(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W1_read Fz_W3_iface Fz_W2_rep Fz_W3_defs Fz_W3_end Fz_W3_tail Fz_W3_dec
     Fz_W3_endl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Ltac hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_core; cbv zeta;
  split; [exact ER|]; split; [exact BLEN|]; split; [exact SA|]; split; [exact SB|]; split; [exact SBIG|];
  split; [exact MAXT|]; split; [exact MAXO|]; split; [exact DNT|]; split; [exact DNO|]; split; [exact GOT|]; split; [exact ROLE|];
  split; [exact OWNN|]; split; [exact NN|]; split; [exact LBN|]; split; [exact NMC|]; split; [exact NONUL|]; split; [exact OWNL|]; split; [exact LBS|];
  split; [exact LBC|]; split; [exact MBT|]; split; [exact MBO|]; split; [exact ELB|]; split; [exact CFRESH|]; split; [exact EL|];
  split; [exact NDT| exact OUT].
Ltac hd_inv_by ER REM BLEN SA SB SBIG LSUM MAXT MAXO DNT DNO GOT ROLE LEN OWNN NN LBN NMC NONUL OWNL LBS LBC NULk MBT MBO ELB CFRESH EL NDT OUT :=
  unfold hd_inv; split; [hd_core_by ER BLEN SA SB SBIG MAXT MAXO DNT DNO GOT ROLE OWNN NN LBN NMC NONUL OWNL LBS LBC MBT MBO ELB CFRESH EL NDT OUT|];
  split; [exact REM|]; split; [exact LSUM|]; split; [exact LEN| exact NULk].

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
  Local Notation er0_callI := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation libenv_cfrI := (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma com_callK : forall en s LBc Lc f m off rem rA rB rBig (T1 : bptr -> Prop) SPc s1 m1 (f1 EV1 rem' : nat) off',
    pem_com libenv en s LBc Lc f m off rem rA rB rBig ->
    cstate s1 LBc (e_LB0 en) Lc m1 (wz (e_PL en + -208)) (e_tp en) (e_lo en) (e_B en) -> cframe T1 [] SPc s LBc Lc m s1 LBc Lc m1 -> SPc <= e_PL en + -104 ->
    (f - EV1 <= f1)%nat -> (rem' + EV1 <= rem)%nat ->
    (forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ T1 q) -> ~ T1 (e_pe en) ->
    mbio_rep m1 LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off' -> e_boff en <= off' <= e_blen en ->
    pem_com libenv en s1 LBc Lc f1 m1 off' rem' rA rB rBig.
  Proof.
    intros en s LBc Lc f m off rem rA rB rBig T1 SPc s1 m1 f1 EV1 rem' off'
           (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & REST) CST1 FRM1 HSP FU1 REM HT HE MB1 OFF1.
    pose proof FRM1 as (CFR1 & KP1 & _).
    assert (NT1 : forall b, In b (e_LBL en) -> ~ T1 (blk_id b)) by (intros b Hb; apply HT; [left; apply in_map; exact (INCL0 _ Hb)| exact (NTL _ Hb)]).
    split; [exact CST1|]. split; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| exact HT]|].
    split; [eapply libenv_cfrI; [exact LE| exact CFR1| exact INCL| exact NT1]|]. split; [exact INCL0|]. split; [exact INCL|]. split; [exact NTL|].
    split; [exact OWNE|]. split; [exact MB1|]. split; [exact OFF1|]. split; [exact EVF|]. split; [lia|].
    split; [exact ROOM|]. split; [exact CG|]. split; [exact RA0|]. split; [exact RB0|]. split; [exact RBIG0|]. split; [exact PLB|]. split; [exact PLC|].
    split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(lia))| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma ow_bounds : forall K mx, 0 <= mx -> 0 <= owA K mx <= 1 /\ 0 <= owB K mx <= 1 /\ 0 <= owBig K mx <= mx + 8192.
  Proof. intros K mx H. unfold owA, owB, owBig. destruct (k_d K); [pose proof (w_bounds mx H); lia| lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem GETS1_proof : forall N, bio_gets_stmt -> RAISE2_stmt libenv errst_at_rest errst_live -> HD_at libenv errst_at_rest errst_live (N - 1) ->
    GETS1_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N BG RAISEP HDP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s10 s11 t3 t4 t5 t6 l0 l8 l11 ta tb
           qn ql namev nn LB2 hBv dBv tmpv ov got endv partv str bn2 bs KT KO methT methO lenT maxT lenO maxO.
    intros MEAS COM PRE LOC ENDV PARTV. unfold RAISE2_stmt, J_RAISE2 in RAISEP. unfold HD_at, J_HD in HDP. unfold bio_gets_stmt in BG.
    pose proof PRE as ((ER0 & BLEN & SA & SB & SBIG & MAXT & MAXO & DNT & DNO & GOT & ROLE & OWNN & NN & LBN & NMC & NONUL & OWNL & LBS & LBC
                      & MBT & MBO & ELB & CFRESH & EL & NDT & OUT) & REM & LSUM).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_GETS1, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2, RN2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 ND4]; subst. cbn [In] in NQ1.
    (* [comment removed for export] *)
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq NT [X| <-]; [apply NT; left; exact X|]. destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). right; left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). right; left; reflexivity. }
    assert (HE1 : ~ (mbio_T (e_K en) (e_pe en) \/ e_pe en = ql)).
    { intros [X|X]; [apply mbio_T_blocks in X; inversion NDR as [|z k NP _]; subst; exact (NP X)|].
      apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| left; exact X]. }
    assert (HKL : ~ mbio_T (e_K en) ql) by (intros X; apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| right; apply mbio_T_blocks; exact X]).
    assert (HT1T : forall q, mbio_T KT q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; right; left; reflexivity]. }
    assert (HT1O : forall q, mbio_T KO q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJY ql); [apply mbio_T_blocks; exact Hq| right; left; reflexivity]. }
    assert (HT1N : ~ (mbio_T (e_K en) qn \/ qn = ql)).
    { intros [X|X]; [apply (DJC qn); [do 2 (apply in_or_app; right); left; reflexivity| right; apply mbio_T_blocks; exact X]| clear - X NQ1; intuition]. }
    hide ROLE. hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BG with (K := e_K en) (pl := ql) (BI := e_BI en) (meth := e_meth en) (len := e_blen en) (max := e_bmax en) (off := off) (LB := LB2) (lo := e_lo en) (B := e_B en) (bs := bs);
        [exact CST| rewrite unsigned_lit by lia; unfold BGETS_STACK; clear - SLO; lia| exact MB| exact OWNL| exact HKL| exact LBS| exact LBC| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (k & bs' & -> & -> & -> & LBS1 & LBC1 & ARMS)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    (* [comment removed for export] *)
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HT1N ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT FRM1 HT1T) as MBT1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO FRM1 HT1O) as MBO1.
    pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    assert (LTO : 0 <= lenT <= maxT /\ 0 <= lenO <= maxO).
    { destruct MBT as (BMt & BBt & RPt & flt & rrwt & padwt & nrt & nwt & _ & _ & _ & _ & _ & _ & _ & (rmaxwt & _ & _ & _ & _ & X1 & X2 & X3 & _)).
      destruct MBO as (BMo & BBo & RPo & flo & rrwo & padwo & nro & nwo & _ & _ & _ & _ & _ & _ & _ & (rmaxwo & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)). clear - X1 X2 X3 Y1 Y2 Y3. lia. }
    pose proof (ow_bounds KT maxT ltac:(clear - LTO; lia)) as OWT. pose proof (ow_bounds KO maxO ltac:(clear - LTO; lia)) as OWO.
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (COMK : forall off', mbio_rep m1 LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off' -> e_boff en <= off' <= e_blen en ->
                   pem_com libenv en st1 LBc Lc f1 m1 off' rem rA rB rBig).
    { intros off' MBk OFFk. eapply (com_callK en s LBc Lc f m off rem rA rB rBig _ _ st1 m1 f1 0%nat rem off');
        [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact HT1| exact HE1| exact MBk| exact OFFk]. }
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG FRM1 CFR1 LOC OUT NMC MBT MBO.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold hideP in ROLE, ELB.
    (* [comment removed for export] *)
    destruct ARMS as [(KZ & OFFE & MBk)|(KR & NULk & MBk)].
    2: { (* [comment removed for export] *)
      pose proof (COMK (off + k) MBk ltac:(clear - KR OFF; lia)) as COM1. clear COMK.
      cprefix. ths. ths. ths. ths. if_cases KK; zify_cond KK. 2: { exfalso. rewrite ?unsigned_lit in KK by (clear - KR; lia). clear - KK KR. lia. }
      chere. unfold hideP in ROLE, ELB.
      eapply (HDP en st1 LBc Lc f1 m1 (off + k) rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                qn ql namev nn LB2 hBv dBv tmpv ov got partv endv k str bn2 bs' KT KO methT methO lenT maxT lenO maxO);
        [clear - MEAS KR; lia| exact COM1| | unfold pem_loc; exact LOC1| exact ENDV| exact PARTV].
      assert (REM1 : (Z.to_nat (2 * (e_blen en - (off + k)) + 18) <= rem)%nat) by (clear - REM KR; lia).
      assert (LSUM1 : lenT + lenO <= 2 * (off + k - e_boff en - k)) by (clear - LSUM; lia).
      assert (LEN1 : 1 <= k <= 254) by (clear - KR; lia).
      hd_inv_by ER1 REM1 BLEN SA SB SBIG LSUM1 MAXT MAXO DNT DNO GOT ROLE LEN1 OWNN NN LBN NMC1 NONUL OWNL LBS1 LBC1 NULk MBT1 MBO1 ELB CFRESH EL NDT OUT1. }
    (* [comment removed for export] *)
    subst k. pose proof (COMK off MBk OFF) as COM1. clear COMK.
    cprefix. ths. ths. ths. ths. try th_if_lit. ths. ths. ths. ths. chere. unfold hideP in ROLE, ELB.
    destruct ROLE as [(RG & -> & ->)|(RG & -> & ->)].
      + eapply (RAISEP en st1 LBc Lc f1 m1 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  qn ql namev nn LB2 hBv dBv 854 (str ++ Z_to_bv 8 0 :: bn2) bs' KT KO methT methO lenT maxT lenO maxO);
          [exact COM1| exact ER1| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOC1| exact OWNN| clear - NN; lia| exact LBN| exact NMC1| exact NUL
          | exact OWNL| exact LBS1| exact LBC1| exact MBT1| exact MBO1| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT1].
      + eapply (RAISEP en st1 LBc Lc f1 m1 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  qn ql namev nn LB2 hBv dBv 854 (str ++ Z_to_bv 8 0 :: bn2) bs' KO KT methO methT lenO maxO lenT maxT);
          [exact COM1| exact ER1| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOC1| exact OWNN| clear - NN; lia| exact LBN| exact NMC1| exact NUL
          | exact OWNL| exact LBS1| exact LBC1| exact MBO1| exact MBT1| | | | | exact OUT1].
        * intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
          apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem GETS2_proof : forall N, bio_gets_stmt -> RAISE2_stmt libenv errst_at_rest errst_live -> HD_at libenv errst_at_rest errst_live (N - 1) ->
    GETS2_at libenv errst_at_rest errst_live N.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros N BG RAISEP HDP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s11 t3 t4 t5 t6 l0 l3 l8 l11 ta tb
           qn ql namev nn LB2 hBv dBv tmpv ov got endv partv str bn2 bs KT KO methT methO lenT maxT lenO maxO.
    intros MEAS COM PRE LOC ENDV PARTV. unfold RAISE2_stmt, J_RAISE2 in RAISEP. unfold HD_at, J_HD in HDP. unfold bio_gets_stmt in BG.
    pose proof PRE as ((ER0 & BLEN & SA & SB & SBIG & MAXT & MAXO & DNT & DNO & GOT & ROLE & OWNN & NN & LBN & NMC & NONUL & OWNL & LBS & LBC
                      & MBT & MBO & ELB & CFRESH & EL & NDT & OUT) & REM & LSUM).
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_GETS2, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNN)) as (RN1 & _ & _ & RN2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2, RN2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    inversion NDC3 as [|z1 k1 NQ1 ND4]; subst. cbn [In] in NQ1.
    (* [comment removed for export] *)
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq NT [X| <-]; [apply NT; left; exact X|]. destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). right; left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). right; left; reflexivity. }
    assert (HE1 : ~ (mbio_T (e_K en) (e_pe en) \/ e_pe en = ql)).
    { intros [X|X]; [apply mbio_T_blocks in X; inversion NDR as [|z k NP _]; subst; exact (NP X)|].
      apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| left; exact X]. }
    assert (HKL : ~ mbio_T (e_K en) ql) by (intros X; apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| right; apply mbio_T_blocks; exact X]).
    assert (HT1T : forall q, mbio_T KT q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; right; left; reflexivity]. }
    assert (HT1O : forall q, mbio_T KO q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJY ql); [apply mbio_T_blocks; exact Hq| right; left; reflexivity]. }
    assert (HT1N : ~ (mbio_T (e_K en) qn \/ qn = ql)).
    { intros [X|X]; [apply (DJC qn); [do 2 (apply in_or_app; right); left; reflexivity| right; apply mbio_T_blocks; exact X]| clear - X NQ1; intuition]. }
    hide ROLE. hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BG with (K := e_K en) (pl := ql) (BI := e_BI en) (meth := e_meth en) (len := e_blen en) (max := e_bmax en) (off := off) (LB := LB2) (lo := e_lo en) (B := e_B en) (bs := bs);
        [exact CST| rewrite unsigned_lit by lia; unfold BGETS_STACK; clear - SLO; lia| exact MB| exact OWNL| exact HKL| exact LBS| exact LBC| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (k & bs' & -> & -> & -> & LBS1 & LBC1 & ARMS)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    (* [comment removed for export] *)
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HT1N ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT FRM1 HT1T) as MBT1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO FRM1 HT1O) as MBO1.
    pose proof (er0_callI en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    assert (LTO : 0 <= lenT <= maxT /\ 0 <= lenO <= maxO).
    { destruct MBT as (BMt & BBt & RPt & flt & rrwt & padwt & nrt & nwt & _ & _ & _ & _ & _ & _ & _ & (rmaxwt & _ & _ & _ & _ & X1 & X2 & X3 & _)).
      destruct MBO as (BMo & BBo & RPo & flo & rrwo & padwo & nro & nwo & _ & _ & _ & _ & _ & _ & _ & (rmaxwo & _ & _ & _ & _ & Y1 & Y2 & Y3 & _)). clear - X1 X2 X3 Y1 Y2 Y3. lia. }
    pose proof (ow_bounds KT maxT ltac:(clear - LTO; lia)) as OWT. pose proof (ow_bounds KO maxO ltac:(clear - LTO; lia)) as OWO.
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (COMK : forall off', mbio_rep m1 LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off' -> e_boff en <= off' <= e_blen en ->
                   pem_com libenv en st1 LBc Lc f1 m1 off' rem rA rB rBig).
    { intros off' MBk OFFk. eapply (com_callK en s LBc Lc f m off rem rA rB rBig _ _ st1 m1 f1 0%nat rem off');
        [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact HT1| exact HE1| exact MBk| exact OFFk]. }
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG FRM1 CFR1 LOC OUT NMC MBT MBO.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold hideP in ROLE, ELB.
    (* [comment removed for export] *)
    destruct ARMS as [(KZ & OFFE & MBk)|(KR & NULk & MBk)].
    2: { (* [comment removed for export] *)
      pose proof (COMK (off + k) MBk ltac:(clear - KR OFF; lia)) as COM1. clear COMK.
      cprefix. ths. ths. if_cases KK; zify_cond KK. 2: { exfalso. rewrite ?unsigned_lit in KK by (clear - KR; lia). clear - KK KR. lia. }
      ths. ths. chere. unfold hideP in ROLE, ELB.
      eapply (HDP en st1 LBc Lc f1 m1 (off + k) rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                qn ql namev nn LB2 hBv dBv tmpv ov got partv endv k str bn2 bs' KT KO methT methO lenT maxT lenO maxO);
        [clear - MEAS KR; lia| exact COM1| | unfold pem_loc; exact LOC1| exact ENDV| exact PARTV].
      assert (REM1 : (Z.to_nat (2 * (e_blen en - (off + k)) + 18) <= rem)%nat) by (clear - REM KR; lia).
      assert (LSUM1 : lenT + lenO <= 2 * (off + k - e_boff en - k)) by (clear - LSUM; lia).
      assert (LEN1 : 1 <= k <= 254) by (clear - KR; lia).
      hd_inv_by ER1 REM1 BLEN SA SB SBIG LSUM1 MAXT MAXO DNT DNO GOT ROLE LEN1 OWNN NN LBN NMC1 NONUL OWNL LBS1 LBC1 NULk MBT1 MBO1 ELB CFRESH EL NDT OUT1. }
    (* [comment removed for export] *)
    subst k. pose proof (COMK off MBk OFF) as COM1. clear COMK.
    cprefix. ths. ths. try th_if_lit. ths. ths. ths. chere. unfold hideP in ROLE, ELB.
    destruct ROLE as [(RG & -> & ->)|(RG & -> & ->)].
      + eapply (RAISEP en st1 LBc Lc f1 m1 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  qn ql namev nn LB2 hBv dBv 854 (str ++ Z_to_bv 8 0 :: bn2) bs' KT KO methT methO lenT maxT lenO maxO);
          [exact COM1| exact ER1| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOC1| exact OWNN| clear - NN; lia| exact LBN| exact NMC1| exact NUL
          | exact OWNL| exact LBS1| exact LBC1| exact MBT1| exact MBO1| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT1].
      + eapply (RAISEP en st1 LBc Lc f1 m1 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  qn ql namev nn LB2 hBv dBv 854 (str ++ Z_to_bv 8 0 :: bn2) bs' KO KT methO methT lenO maxO lenT maxT);
          [exact COM1| exact ER1| clear - REM OFF; lia| clear - SA OWT OWO; lia| clear; lia| unfold pem_loc; exact LOC1| exact OWNN| clear - NN; lia| exact LBN| exact NMC1| exact NUL
          | exact OWNL| exact LBS1| exact LBC1| exact MBO1| exact MBT1| | | | | exact OUT1].
        * intros b Hb. destruct (ELB _ Hb) as [X|X]; [left; exact X| right]. rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros b Hb X. apply (CFRESH _ Hb). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * intros q nm Hq X. apply (EL _ _ Hq). rewrite !in_app_iff in X |- *. clear - X. tauto.
        * eapply Permutation_NoDup; [| exact NDT]. apply Permutation_app_tail. rewrite (app_assoc (mbio_blocks KT)), (app_assoc (mbio_blocks KO)).
          apply Permutation_app; [apply Permutation_app_comm| apply Permutation_refl].
  Qed.
End W3.
