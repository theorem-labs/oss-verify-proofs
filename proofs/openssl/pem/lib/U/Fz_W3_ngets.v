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
     Fz_W3_endl Fz_W3_hdg.
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

  Local Notation er0_callI' := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).
  Local Notation com_segI := (com_seg libenv libenv_fp libenv_agree libenv_fp_where).
  Local Notation er0_segI := (er0_seg errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  Theorem NGETS_proof : bio_gets_stmt -> RAISE2_stmt libenv errst_at_rest errst_live -> (forall N, HD_at libenv errst_at_rest errst_live N) ->
    NGETS_stmt libenv errst_at_rest errst_live.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BG RAISEP HDP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s11 t3 t4 t5 t6 l0 l1 l3 l4 l5 l11 ta tb
           qn ql namev nn LB2 hBv dBv str bn2 bs KX KY methX methY.
    cbv zeta. intros COM ER0 REM BOFF BLEN RA5 RB4 RBIG6 LOC OWNN NN LBN NMC NONUL OWNL LBS LBC MBT KXN MBO KYN ELB CFRESH EL NDT OUT.
    unfold RAISE2_stmt, J_RAISE2 in RAISEP. unfold bio_gets_stmt in BG.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_NGETS, GLOBALS_TOP in *.
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
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq NT [X| <-]; [apply NT; left; exact X|]. destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). right; left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). right; left; reflexivity. }
    assert (HE1 : ~ (mbio_T (e_K en) (e_pe en) \/ e_pe en = ql)).
    { intros [X|X]; [apply mbio_T_blocks in X; inversion NDR as [|z k NP _]; subst; exact (NP X)|].
      apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| left; exact X]. }
    assert (HKL : ~ mbio_T (e_K en) ql) by (intros X; apply (DJC ql); [do 2 (apply in_or_app; right); right; left; reflexivity| right; apply mbio_T_blocks; exact X]).
    assert (HT1T : forall q, mbio_T KX q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; right; left; reflexivity]. }
    assert (HT1O : forall q, mbio_T KY q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJY ql); [apply mbio_T_blocks; exact Hq| right; left; reflexivity]. }
    assert (HT1N : ~ (mbio_T (e_K en) qn \/ qn = ql)).
    { intros [X|X]; [apply (DJC qn); [do 2 (apply in_or_app; right); left; reflexivity| right; apply mbio_T_blocks; exact X]| clear - X NQ1; intuition]. }
    assert (NUL : In (Z_to_bv 8 0) (str ++ Z_to_bv 8 0 :: bn2)) by (apply in_or_app; right; left; reflexivity).
    hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BG with (K := e_K en) (pl := ql) (BI := e_BI en) (meth := e_meth en) (len := e_blen en) (max := e_bmax en) (off := off) (LB := LB2) (lo := e_lo en) (B := e_B en) (bs := bs);
        [exact CST| rewrite unsigned_lit by lia; unfold BGETS_STACK; clear - SLO; lia| exact MB| exact OWNL| exact HKL| exact LBS| exact LBC| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & (k & bs' & -> & -> & -> & LBS1 & LBC1 & ARMS)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (qn, namev, nn) CFR1 NMC (proj1 OWNN) HT1N ltac:(cbn; clear; lia) ltac:(cbn; clear - NN; lia)) as NMC1.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT FRM1 HT1T) as MBT1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO FRM1 HT1O) as MBO1.
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    assert (COMK : forall off', mbio_rep m1 LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off' -> e_boff en <= off' <= e_blen en ->
                   pem_com libenv en st1 LBc Lc f1 m1 off' rem rA rB rBig).
    { intros off' MBk OFFk. eapply (com_callK libenv libenv_fp libenv_agree libenv_fp_where en s LBc Lc f m off rem rA rB rBig _ _ st1 m1 f1 0%nat rem off');
        [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact HT1| exact HE1| exact MBk| exact OFFk]. }
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG FRM1 CFR1 LOC OUT NMC MBT MBO.
    pose proof (munch_refl [(bv_unsigned (e_sp en) + -208, bv_unsigned (e_sp en) + -192); (bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -160)]%Z m1) as MU.
    pose proof (wmono_refl usegs m1) as WM.
    unfold hideP in ELB.
    destruct ARMS as [(KZ & OFFE & MBk)|(KR & NULk & MBk)].
    - (* [comment removed for export] *)
      subst k. pose proof (COMK off MBk OFF) as COM1. clear COMK.
      cprefix. ths. ths. ths. try th_if_lit. ths. ths. ths. chere.
      lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ => rename mx into m2 end.
      lazymatch goal with H1 : mem_inv usegs m2, H2 : stk usegs m2 _ _, H3 : rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H1 into MI2; rename H2 into ST2; rename H3 into LOC2 end.
      assert (HW2 : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ : bptr => True))
                      [(bv_unsigned (e_sp en) + -208, bv_unsigned (e_sp en) + -192); (bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -160)]%Z).
      { apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|]. apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]. }
      assert (COM2 : pem_com libenv en st1 LBc Lc f1 m2 off rem rA rB rBig).
      { eapply (com_segI en st1 LBc Lc f1 m1 off rem rA rB rBig _ m2 (fun _ => True));
          [exact COM1| exact MU| exact WM| exact MI2| exact ST2| exact HW2| intros; exact I| unfold e_PL; cbn [disjoint_from fst snd]; clear; lia]. }
      assert (ER2 : errst_at_rest (e_E en) [] m2).
      { eapply (er0_segI _ en m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact ER1| exact MU| exact WM| exact CST1| exact INE| exact HW2| exact I]. }
      assert (MBT2 : mbio_rep m2 LBc Lc KX hBv methX 0 0 0).
      { eapply (mb_seg _ m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBT1| exact CST1| exact MU| exact WM| exact HW2| intros; exact I]. }
      assert (MBO2 : mbio_rep m2 LBc Lc KY dBv methY 0 0 0).
      { eapply (mb_seg _ m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBO1| exact CST1| exact MU| exact WM| exact HW2| intros; exact I]. }
      lazymatch goal with H1 : rw_cells usegs m2 (bv_unsigned (e_sp en)) _, H2 : rw_cells usegs m2 namev _, H3 : rw_cells usegs m2 LB2 _ |- _ =>
        rename H1 into OUT2; rename H2 into NMC2; rename H3 into LBC2 end.
      eapply (RAISEP en st1 LBc Lc f1 m2 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                qn ql namev nn LB2 hBv dBv 854 (str ++ Z_to_bv 8 0 :: bn2) bs' KX KY methX methY 0 0 0 0);
        [exact COM2| exact ER2| clear - REM OFF; lia| clear - RA5; lia| clear; lia| unfold pem_loc; exact LOC2| exact OWNN| clear - NN; lia| exact LBN| exact NMC2| exact NUL
        | exact OWNL| exact LBS1| exact LBC2| exact MBT2| exact MBO2| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT2].
    - (* [comment removed for export] *)
      pose proof (COMK (off + k) MBk ltac:(clear - KR OFF; lia)) as COM1. clear COMK.
      cprefix. ths. ths. ths. if_cases KK; zify_cond KK. { exfalso. rewrite ?unsigned_lit in KK by (clear - KR; lia). clear - KK KR. lia. }
      ths. ths. ths. ths. ths. ths. ths. ths. ths. chere.
      lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mx _) _ => rename mx into m2 end.
      lazymatch goal with H1 : mem_inv usegs m2, H2 : stk usegs m2 _ _, H3 : rw_cells usegs m2 (bv_unsigned (e_sp en) + -208) _ |- _ => rename H1 into MI2; rename H2 into ST2; rename H3 into LOC2 end.
      assert (HW2 : Forall (wfree LBc (e_lo en) (bv_unsigned (e_sp en) + 32) (fun _ : bptr => True))
                      [(bv_unsigned (e_sp en) + -208, bv_unsigned (e_sp en) + -192); (bv_unsigned (e_sp en) + -176, bv_unsigned (e_sp en) + -160)]%Z).
      { apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia|]. apply Forall_cons; [left; cbn [fst snd]; clear - SLO; lia| apply Forall_nil]. }
      assert (COM2 : pem_com libenv en st1 LBc Lc f1 m2 (off + k) rem rA rB rBig).
      { eapply (com_segI en st1 LBc Lc f1 m1 (off + k) rem rA rB rBig _ m2 (fun _ => True));
          [exact COM1| exact MU| exact WM| exact MI2| exact ST2| exact HW2| intros; exact I| unfold e_PL; cbn [disjoint_from fst snd]; clear; lia]. }
      assert (ER2 : errst_at_rest (e_E en) [] m2).
      { eapply (er0_segI _ en m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact ER1| exact MU| exact WM| exact CST1| exact INE| exact HW2| exact I]. }
      assert (MBT2 : mbio_rep m2 LBc Lc KX hBv methX 0 0 0).
      { eapply (mb_seg _ m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBT1| exact CST1| exact MU| exact WM| exact HW2| intros; exact I]. }
      assert (MBO2 : mbio_rep m2 LBc Lc KY dBv methY 0 0 0).
      { eapply (mb_seg _ m1 m2) with (EX := fun _ => True) (hi := bv_unsigned (e_sp en) + 32); [exact MBO1| exact CST1| exact MU| exact WM| exact HW2| intros; exact I]. }
      lazymatch goal with H1 : rw_cells usegs m2 (bv_unsigned (e_sp en)) _, H2 : rw_cells usegs m2 namev _, H3 : rw_cells usegs m2 LB2 _ |- _ =>
        rename H1 into OUT2; rename H2 into NMC2; rename H3 into LBC2 end.
      assert (BL : 0 <= e_boff en /\ e_blen en < 2 ^ 26) by (clear - BOFF BLEN; lia).
      assert (SA : 5 <= rA + owA KX 0 + owA KY 0) by (unfold owA; rewrite KXN, KYN; clear - RA5; lia).
      assert (SB : 4 <= rB + owB KX 0 + owB KY 0) by (unfold owB; rewrite KXN, KYN; clear - RB4; lia).
      assert (SBIG : 6 * (e_blen en - e_boff en) + 32778 <= rBig + owBig KX 0 + owBig KY 0) by (unfold owBig; rewrite KXN, KYN; clear - RBIG6; lia).
      assert (MX0 : 3 * 0 <= 4 * 0 + 12) by (clear; lia).
      assert (DNT : forall d, k_d KX = Some d -> In (d, 0) Lc) by (rewrite KXN; intros d E; discriminate).
      assert (DNO : forall d, k_d KY = Some d -> In (d, 0) Lc) by (rewrite KYN; intros d E; discriminate).
      assert (GOT : 0 <= 0 <= 2) by (clear; lia).
      assert (ROLE : (0 <> 2 /\ hBv = hBv /\ dBv = dBv) \/ (0 = 2 /\ hBv = dBv /\ dBv = hBv)) by (left; split; [clear; lia| split; reflexivity]).
      assert (REM2 : (Z.to_nat (2 * (e_blen en - (off + k)) + 18) <= rem)%nat) by (clear - REM KR OFF; lia).
      assert (LSUM : 0 + 0 <= 2 * (off + k - e_boff en - k)) by (clear - OFF; lia).
      assert (LEN : 1 <= k <= 254) by (clear - KR; lia).
      assert (Z01 : 0 = 0 \/ 0 = 1) by (left; reflexivity).
      eapply (HDP (e_blen en - (off + k)) en st1 LBc Lc f1 m2 (off + k) rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                qn ql namev nn LB2 hBv dBv hBv dBv 0 0 0 k str bn2 bs' KX KY methX methY 0 0 0 0);
        [clear; lia| exact COM2| | unfold pem_loc, PEM_ENDSTR; exact LOC2| exact Z01| exact Z01].
      hd_inv_by ER2 REM2 BL SA SB SBIG LSUM MX0 MX0 DNT DNO GOT ROLE LEN OWNN NN LBN NMC2 NONUL OWNL LBS1 LBC2 NULk MBT2 MBO2 ELB CFRESH EL NDT OUT2.
  Qed.
End W3.
