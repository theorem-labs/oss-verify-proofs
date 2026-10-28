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

Definition J_J0G : Z := 0x18809c.

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
  Local Notation er0_callI' := (er0_call errst_at_rest errst_fp errst_rest_agree errst_fp_where).

  (* [comment removed for export] *)
  Definition J0G_stmt : Prop :=
    forall (en : pem_entry) s LBc Lc f m off rem rA rB rBig
           (xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb : word)
           (ql : bptr) (LB1 hBv dBv : Z) (bs : list byte) (KX KY : mbk) (methX methY : Z),
    let curids := mbio_blocks KX ++ mbio_blocks KY ++ [ql] in
    pem_com libenv en s LBc Lc f m off rem rA rB rBig -> errst_at_rest (e_E en) [] m ->
    (Z.to_nat (2 * (e_blen en - off) + 19) <= rem)%nat -> 0 <= e_boff en -> e_blen en < 2 ^ 26 ->
    6 <= rA -> 5 <= rB -> 6 * (e_blen en - e_boff en) + 32778 + 8448 <= rBig ->
    rw_cells usegs m (e_PL en + -208) (pem_loc l0 l1 l2 l3 l4 l5 (wz (e_PL en + 8)) (wz (e_PL en + 16)) (wz hBv) (wz dBv) (wz (e_flags en)) l11 ta tb) ->
    cown LBc Lc ql LB1 256 256 -> length bs = 256%nat -> rw_cells usegs m LB1 [CB 256 bs] ->
    mbio_rep m LBc Lc KX hBv methX 0 0 0 -> k_d KX = None -> mbio_rep m LBc Lc KY dBv methY 0 0 0 -> k_d KY = None ->
    (forall b, In b LBc -> In b (e_LBall en) \/ In (blk_id b) curids) ->
    (forall b, In b (e_LBall en) -> ~ In (blk_id b) curids) -> (forall q nm, In (q, nm) (e_L en) -> ~ In q curids) ->
    List.NoDup (curids ++ e_pe en :: mbio_blocks (e_K en)) ->
    rw_cells usegs m (e_PL en) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
    climpl f Lc s (MS (mkR xra (wz (e_PL en + -208)) (e_gp en) (e_tp en) t0 t1 t2 (e_sp en) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (e_sp en) (wz (e_PL en + 24)) (wz (e_BI en)) (wz LB1) s11 t3 t4 t5 t6)
                 (e_F en) (wz J_J0G) (e_fc en) None m (seg_rom usegs))
      (pem_post libenv errst_live en).

  Theorem J0G_proof : bio_gets_stmt -> RAISE1_stmt libenv errst_at_rest errst_live -> (forall N, GN_at libenv errst_at_rest errst_live N) -> J0G_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros BG RAISEP GNP en s LBc Lc f m off rem rA rB rBig xra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s11 t3 t4 t5 t6 l0 l1 l2 l3 l4 l5 l11 ta tb
           ql LB1 hBv dBv bs KX KY methX methY.
    cbv zeta. intros COM ER0 REM BOFF BLEN RA6 RB5 RBIG6 LOC OWNL LBS LBC MBT KXN MBO KYN ELB CFRESH EL NDT OUT.
    unfold RAISE1_stmt, J_RAISE1 in RAISEP. unfold GN_at, J_GN in GNP. unfold bio_gets_stmt in BG.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold BPUTS_STACK, WRITE_STACK, GROW_STACK, J_J0G, GLOBALS_TOP in *.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP.
    pose proof (bv_unsigned_in_range _ (e_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold e_PL in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia). rewrite unsigned_lit in SPB by (clear - SPR SLO LO GLO; lia).
    pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNL)) as (RL1 & _ & _ & RL2 & _).
    unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RL2.
    assert (INE : In (e_pe en, e_E en, 904) LBc) by exact (proj1 OWNE).
    pose proof (nd_split _ _ NDT) as (NDC & NDR & DJC). pose proof (nd_split _ _ NDC) as (_ & NDC2 & DJX). pose proof (nd_split _ _ NDC2) as (_ & NDC3 & DJY).
    assert (HT1 : forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq NT [X| <-]; [apply NT; left; exact X|]. destruct Hq as [Hq|Hq]; apply in_map_iff in Hq.
      - destruct Hq as (b & E & Hb). apply (CFRESH _ Hb). rewrite E. do 2 (apply in_or_app; right). left; reflexivity.
      - destruct Hq as ([q' nm] & E & Hq). cbn in E. subst q'. apply (EL _ _ Hq). do 2 (apply in_or_app; right). left; reflexivity. }
    assert (HE1 : ~ (mbio_T (e_K en) (e_pe en) \/ e_pe en = ql)).
    { intros [X|X]; [apply mbio_T_blocks in X; inversion NDR as [|z k NP _]; subst; exact (NP X)|].
      apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| left; exact X]. }
    assert (HKL : ~ mbio_T (e_K en) ql) by (intros X; apply (DJC ql); [do 2 (apply in_or_app; right); left; reflexivity| right; apply mbio_T_blocks; exact X]).
    assert (HT1T : forall q, mbio_T KX q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJX ql); [apply mbio_T_blocks; exact Hq| apply in_or_app; right; left; reflexivity]. }
    assert (HT1O : forall q, mbio_T KY q -> ~ (mbio_T (e_K en) q \/ q = ql)).
    { intros q Hq [X|X]; [apply (DJC q); [apply in_or_app; right; apply in_or_app; left; apply mbio_T_blocks; exact Hq| right; apply mbio_T_blocks; exact X]|].
      subst q. apply (DJY ql); [apply mbio_T_blocks; exact Hq| left; reflexivity]. }
    hide ELB. hide ROOM. hide CG.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold pem_loc in LOC.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply BG with (K := e_K en) (pl := ql) (BI := e_BI en) (meth := e_meth en) (len := e_blen en) (max := e_bmax en) (off := off) (LB := LB1) (lo := e_lo en) (B := e_B en) (bs := bs);
        [exact CST| rewrite unsigned_lit by lia; unfold BGETS_STACK; clear - SLO; lia| exact MB| exact OWNL| exact HKL| exact LBS| exact LBC| reflexivity| reflexivity| reflexivity]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1' & RET & FU1 & GR1 & CST1 & FRM1 & (k & bs' & -> & -> & -> & LBS1 & LBC1 & ARMS)).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof FRM1 as (CFR1 & KP1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 LOC ltac:(clear; lia)) as LOC1. pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 OUT ltac:(clear; lia)) as OUT1.
    pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBT FRM1 HT1T) as MBT1. pose proof (mb_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MBO FRM1 HT1O) as MBO1.
    pose proof (er0_callI' en _ _ _ _ _ _ _ _ _ _ ER0 FRM1 INE HE1) as ER1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
    assert (COMK : forall off', mbio_rep m1 LBc Lc (e_K en) (e_BI en) (e_meth en) (e_blen en) (e_bmax en) off' -> e_boff en <= off' <= e_blen en ->
                   pem_com libenv en st1 LBc Lc f1 m1 off' rem rA rB rBig).
    { intros off' MBk OFFk. eapply (com_callK libenv libenv_fp libenv_agree libenv_fp_where en s LBc Lc f m off rem rA rB rBig _ _ st1 m1 f1 0%nat rem off');
        [exact COM| exact CST1| exact FRM1| unfold e_PL; clear; lia| exact FU1| clear; lia| exact HT1| exact HE1| exact MBk| exact OFFk]. }
    clear MU WM CST HP MI ST ERR LATCH LXS CIMG FRM1 CFR1 LOC OUT MBT MBO.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    unfold hideP in ELB.
    destruct ARMS as [(KZ & OFFE & MBk)|(KR & NULk & MBk)].
    - (* [comment removed for export] *)
      subst k. pose proof (COMK off MBk OFF) as COM1. clear COMK.
      cprefix. ths. try th_if_lit. chere.
      eapply (RAISEP en st1 LBc Lc f1 m1 off rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l2 l3 l4 l5 _ _ l11 ta tb ql LB1 hBv dBv bs' KX KY methX methY 0 0 0 0);
        [exact COM1| exact ER1| clear - REM OFF; lia| clear - RA6; lia| unfold pem_loc; exact LOC1| exact OWNL| exact LBS1| exact LBC1| exact MBT1| exact MBO1
        | exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT1].
    - (* [comment removed for export] *)
      pose proof (COMK (off + k) MBk ltac:(clear - KR OFF; lia)) as COM1. clear COMK.
      cprefix. ths. if_cases KK; zify_cond KK. { exfalso. rewrite ?unsigned_lit in KK by (clear - KR; lia). clear - KK KR. lia. }
      ths. ths. ths. ths. ths. ths. ths. ths. ths. ths. ths. chere.
      assert (REM1 : (Z.to_nat (2 * (e_blen en - (off + k)) + 19) <= rem)%nat) by (clear - REM KR OFF; lia).
      assert (LEN1 : 1 <= k <= 254) by (clear - KR; lia). assert (Z11 : 0 <= 1 < 2 ^ 32) by (clear; lia).
      rewrite (unsigned_lit LB1), zb_lxor_ones by (clear - RL1 RL2; pose proof alloc_ceiling_lt_2p47; lia).
      eapply (GNP (e_blen en - (off + k)) en st1 LBc Lc f1 m1 (off + k) rem rA rB rBig _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l2 l3 l4 l5 l11 ta tb ql LB1 hBv dBv k 1 _ bs' KX KY methX methY);
        [clear; lia| exact COM1| exact ER1| exact REM1| exact BOFF| exact BLEN| exact RA6| exact RB5| exact RBIG6| unfold pem_loc; exact LOC1| exact OWNL| exact LBS1| exact LBC1
        | exact LEN1| exact NULk| exact Z11| | exact MBT1| exact KXN| exact MBO1| exact KYN| exact ELB| exact CFRESH| exact EL| exact NDT| exact OUT1].
      (* [comment removed for export] *)
      clear - FLR. rewrite unsigned_lit by (clear - FLR; lia).
      lazymatch goal with |- 0 <= Z.land ?a ?b < _ =>
        pose proof (OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Bytes.land_lt_pow2 a b 8 ltac:(clear - FLR; lia) ltac:(clear; lia)); lia end.
  Qed.
End W3.
