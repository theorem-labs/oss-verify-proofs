(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I3_base Fz_I3_kit Fz_W3_iface Fz_T_ekit Fz_M_malloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sa Fz_I3_fxi Fz_W2_exd Fz_W5_defs Fz_W5_env Fz_W5_gsi Fz_W5_vset Fz_W5_new Fz_W5_debug Fz_W5_debug2 Fz_W5_debug3.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation nulls := (repeat (Z_to_bv 64 0) 16) (only parsing).

(* [comment removed for export] *)
Lemma errst_live_nil : forall m E top bot, errst_live E top bot [] m -> exists fl mk buf ls, es_rep m E top bot fl mk buf nulls ls nulls.
Proof.
  intros m E top bot (fl & mk & buf & fs & ls & fn & ks & H & (ND & LEN & RNG & SL & NUL & NDS)).
  destruct ks; [| discriminate LEN].
  destruct H as (A1 & L1 & A2 & L2 & A3 & L3 & Z1 & Z2 & Z3 & A4 & L4 & A5 & L5 & A6 & L6 & TB & HT & HB).
  assert (FS0 : forall (l : list word), length l = 16%nat -> (forall i w, 0 <= i < 16 -> nth_error l (Z.to_nat i) = Some w -> w = Z_to_bv 64 0) ->
                l = repeat (Z_to_bv 64 0) 16).
  { intros l Hl Hz. apply nth_ext with (d := Z_to_bv 64 0) (d' := Z_to_bv 64 0); [rewrite repeat_length; exact Hl|].
    intros n Hn. rewrite nth_repeat. destruct (nth_error l n) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
    rewrite (nth_error_nth l n (Z_to_bv 64 0) Hw). apply (Hz (Z.of_nat n) w); [lia|]. rewrite Nat2Z.id. exact Hw. }
  assert (EFS : fs = repeat (Z_to_bv 64 0) 16).
  { apply (FS0 fs L4). intros i w Hi Hw. apply (NUL (i, false) w); [cbn; lia| unfold slot_word; cbn [fst snd]; exact Hw| intros []]. }
  assert (EFN : fn = repeat (Z_to_bv 64 0) 16).
  { apply (FS0 fn L6). intros i w Hi Hw. apply (NUL (i, true) w); [cbn; lia| unfold slot_word; cbn [fst snd]; exact Hw| intros []]. }
  subst fs fn. exists fl, mk, buf, ls.
  exact (conj A1 (conj L1 (conj A2 (conj L2 (conj A3 (conj L3 (conj Z1 (conj Z2 (conj Z3 (conj A4 (conj L4 (conj A5 (conj L5 (conj A6 (conj L6 (conj TB (conj HT HB))))))))))))))))).
Qed.

(* [comment removed for export] *)
Lemma slots_ok_debug : forall (qf qn : bptr) (QF QN nf nn : Z) (ls : list word),
  0 < QF -> 0 < QN -> 0 < nf -> 0 < nn -> qf <> qn ->
  slots_ok (upd nulls 1%nat (Z_to_bv 64 QF)) (upd nulls 1%nat (Z_to_bv 64 QN)) [(1, true); (1, false)] [(qn, QN, nn); (qf, QF, nf)].
Proof.
  intros qf qn QF QN nf nn ls HQF HQN HNF HNN HNE.
  split. { apply NoDup_cons_2; [intros Hin; apply list_elem_of_singleton in Hin; discriminate Hin|]. apply NoDup_cons_2; [apply not_elem_of_nil| apply NoDup_nil_2]. }
  split; [reflexivity|]. split; [intros ik [<-|[<-|[]]]; cbn; lia|].
  split.
  { intros j ik b Hj Hb. destruct j as [|[|j]]; cbn in Hj, Hb; [injection Hj as <-; injection Hb as <-| injection Hj as <-; injection Hb as <-| destruct j; discriminate Hj];
      unfold slot_word; cbn; (split; [reflexivity| lia]). }
  split.
  2:{ cbn [map blk_id fst]. constructor; [| constructor; [intros []| constructor]]. intros [E1|[]]. exact (HNE E1). }
  intros [i isf] w Hi Hw NI. unfold slot_word in Hw. cbn [fst snd] in Hi, Hw.
  assert (NE1 : Z.to_nat i <> 1%nat). { intros E1. apply NI. assert (i = 1) as -> by lia. destruct isf; [left| right; left]; reflexivity. }
  assert (X : forall x, nth_error (upd (repeat (Z_to_bv 64 0) 16) 1%nat x) (Z.to_nat i) = Some w -> w = Z_to_bv 64 0).
  { intros x Hn. rewrite nth_error_upd_other in Hn by (intros E1; apply NE1; symmetry; exact E1). apply nth_error_In in Hn. apply repeat_spec in Hn. exact Hn. }
  destruct isf; eapply X; exact Hw.
Qed.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?P => change P with (boxed P) in H end.
Ltac unbox H := unfold boxed in H.

Theorem err_set_debug_proof : crypto_malloc_stmt -> err_set_debug_stmt libenv errst_live.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. unfold err_set_debug_stmt. intros until nslack.
  intros Hf ROOM CST SLO ENV INCL OWN LIVE -> -> -> ROB ROBN NONUL NONULN PAD PADN SLOW SHIGH SLOWN SHIGHN ENF ENN NF NN.
  unfold crypto_malloc_stmt in CM.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as ND.
  destruct (libenv_cells _ _ _ ENV) as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & LK & ELBL & STOP & ONCE & OD & OC & KC & HK & TS & SLOT & HMK & P3 & HSA & HDR & HNO & NE & LEAF).
  destruct (errst_live_nil _ _ _ _ LIVE) as (fl & mk & buf & ls & ES).
  destruct OWN as [INE INL].
  assert (INM : In (pm, MK, 72) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INS : In (psa, SA, 32) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INN : In (pn, NODES, 128) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INK : In (pk, LK, 40) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INE) as (E0 & E16 & _ & ECL & EIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (_ & M16 & _ & MCL & MIMG). assert (M8 : MK mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & S16 & _ & SCL & SIMG). assert (S8 : SA mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INN) as (_ & N16 & _ & NCL & NIMG). assert (N8 : NODES mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (_ & _ & _ & KCL & KIMG).
  assert (DJ : forall p X n, In (p, X, n) LBall -> n <> 904 -> X + n <= E \/ E + 904 <= X).
  { intros p X n Hin Hn. destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, X, n) (pe, E, 904) HP Hin INE) as [D|D]; [| cbn [blk_addr blk_size blk_id fst snd] in D; lia| cbn [blk_addr blk_size blk_id fst snd] in D; lia].
    cbn [blk_addr blk_size blk_id fst snd]. intros Heq. subst p. destruct (cown_block_eq LBall pe X n E 904 ND Hin INE) as [_ Hn']. lia. }
  pose proof (DJ _ _ _ INM ltac:(lia)) as DM. pose proof (DJ _ _ _ INS ltac:(lia)) as DS. pose proof (DJ _ _ _ INN ltac:(lia)) as DN. pose proof (DJ _ _ _ INK ltac:(lia)) as DK. clear DJ.
  assert (E8 : E mod 8 = 0) by (Z.div_mod_to_equations; lia). clear E16.
  box DM. box DS. box DN. box DK. box EIMG. box MIMG. box SIMG. box NIMG. box KIMG. box E8.
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia).
  unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
  rewrite <- TPV in TS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  subst nf nn. set (lf := Z.of_nat (length fstr)) in *. set (ln := Z.of_nat (length nstr)) in *.
  replace (- (SF + (lf + 1))) with (- (SF + lf + 1)) in PAD by lia. replace (- (SN + (ln + 1))) with (- (SN + ln + 1)) in PADN by lia.
  destruct (wA_small (lf + 1) ltac:(unfold TIER_A_MAX; lia)) as (WA1 & WB1 & WC1).
  destruct (wA_small (ln + 1) ltac:(unfold TIER_A_MAX; lia)) as (WA2 & WB2 & WC2).
  (* [comment removed for export] *)
  cprefix. eapply evt_cut.
  { pose proof dbg_s1_walk as X. unfold FZ_ERRDBG, DBG_STACK, CM_STACK, RMALLOC_STACK in X. unfold wz, FZ_ERR_SET_DEBUG.
    eapply (X ra sp gp tp t0 t1 t2 s0 s1 _ (Z_to_bv 64 line) _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo TSD_MAIN k MK SA NODES E SF SN errv od pad tw ne fl mk buf ls fstr fslack);
      first [reflexivity | eassumption | subst lf ln; unfold TSD_MAIN, IC_S, RMallocRep.RATP in *; lia]. }
  intros ms1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & jx1 & m1 & -> & MU1 & WM1 & MI1 & ERR1 & ST1 & FR1 & ES1).
  unfold SITE_dbg_m1 in *. chere.
  assert (CST1 : cstate s LBall LB L m1 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg_e _ s LBall LB L m m1 sp _ tp lo B (bv_unsigned sp) (sx32 errv));
      [exact CST| exact MU1| exact WM1| exact MI1| | lia| exact SPB| | exact ERR1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [left; apply cwin_stack; lia|]. apply Forall_cons; [right; cbn [fst snd]; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS, RMallocRep.RATP in *. lia. }
  assert (FRA : cframe (eq pe) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg_e; [apply cframe_refl| exact MU1| exact WM1| exact HP| lia|].
    apply Forall_cons; [left; apply cseg_ok_stack; lia|]. apply Forall_cons; [right; unfold RMallocRep.RERRNO, RMallocRep.RATP in *; cbn [fst snd]; lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply CM with (n := lf + 1) (lo := lo) (B := B);
      [lia| rewrite WA1, WB1, WC1; unfold croom in *; lia| lia| exact CST1| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1' (v1 & m2 & LBall1 & RET1 & FU1 & GR1 & CST2 & FRM1 & (qf & QF & junk1 & -> & -> & -> & RNG1 & BLK1)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  rewrite WA1, WB1, WC1 in GR1.
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR1 ltac:(lia)) as FR2.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & LO2 & ERR2 & MI2 & _) & LXS2 & _).
  rewrite unsigned_lit in ST2 by lia.
  pose proof RNG1 as (QF0 & _ & _ & QFCL & QFIMG).
  assert (ES2 : es_rep m2 E 1 0 fl mk buf nulls ls nulls).
  { eapply (es_rep_agree _ m1 m2); [exact CFR1| exact ES1|]. intros a Ha. right; left. exists (pe, E, 904). split; [exact INE|]. split; [intros X0; exact X0| cbn; lia]. }
  assert (INE1 : In (pe, E, 904) ((qf, QF, lf + 1) :: LBall)) by (right; exact INE).
  assert (INQ1 : In (qf, QF, lf + 1) ((qf, QF, lf + 1) :: LBall)) by (left; reflexivity).
  assert (QFE : QF + (lf + 1) <= E \/ E + 904 <= QF).
  { destruct (RHEAP_blocks_disjoint_proof _ _ _ (qf, QF, lf + 1) (pe, E, 904) HP2 INQ1 INE1) as [D|D]; [| cbn [blk_addr blk_size blk_id fst snd] in D; lia| cbn [blk_addr blk_size blk_id fst snd] in D; lia].
    cbn [blk_addr blk_size blk_id fst snd]. intros Heq. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 INE (eq_sym Heq)). }
  box QFE. box QFIMG.
  replace (Z.to_nat (lf + 1)) with (S (length fstr)) in BLK1 by lia.
  (* [comment removed for export] *)
  cprefix. eapply evt_cut.
  { pose proof dbg_s2_walk as X. unfold DBG_STACK, CM_STACK, RMALLOC_STACK, SITE_dbg_m1 in X.
    eapply (X sp gp tp _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 (Z_to_bv 64 line) F fc m2 lo E SF SN QF fl mk buf ls fstr fslack nstr nslack junk1 jx1);
      first [reflexivity | eassumption | subst lf ln; unfold RMallocRep.RATP in *; lia]. }
  intros ms2 (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & jx2 & m3 & -> & MU2 & WM2 & MI3 & ST3 & FR3 & ES3 & BLK3).
  unfold SITE_dbg_m2 in *. chere.
  assert (CST3 : cstate st1 ((qf, QF, lf + 1) :: LBall) LB ((qf, lf + 1) :: L) m3 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { unbox EIMG. unbox QFIMG. eapply (cstate_seg _ _ _ _ _ m2 m3 _ _ tp lo B (bv_unsigned sp));
      [exact CST2| exact MU2| exact WM2| exact MI3| | lia| exact SPB| | rewrite unsigned_lit by lia; exact ST3| rewrite unsigned_lit by lia; lia].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply (cwin_block _ _ _ (qf, QF, lf + 1)); [exact INQ1| cbn; lia| cbn; lia]|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE1| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS in *. lia. }
  assert (FRB : cframe (eq pe) [] (bv_unsigned sp) s LBall L m st1 ((qf, QF, lf + 1) :: LBall) ((qf, lf + 1) :: L) m3).
  { eapply cframe_seg; [eapply cframe_call; [exact FRA| exact FRM1| lia| intros a X0; exact X0| intros q _ _; tauto]| exact MU2| exact WM2| exact HP2| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (qf, QF, lf + 1)); [exact INQ1| | cbn; lia| cbn; lia].
      intros [[q A'] n'] Hb0 _ E1. cbn [blk_id fst] in E1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 Hb0 E1). }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE1| intros b0 _ Hx; cbn; intros Ex; apply Hx; symmetry; exact Ex| cbn; lia| cbn; lia]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply CM with (n := ln + 1) (lo := lo) (B := B);
      [lia| rewrite WA2, WB2, WC2; unfold croom, cgrow in *; lia| lia| exact CST3| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f2 L2 st2 ms2' (v2 & m4 & LBall2 & RET2 & FU2 & GR2 & CST4 & FRM2 & (qn & QN & junk2 & -> & -> & -> & RNG2 & BLK2)).
  destruct RET2 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. repeat (rewrite unsigned_lit in FRM2 by lia).
  rewrite WA2, WB2, WC2 in GR2.
  pose proof FRM2 as (CFR2 & KP2 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FR3 ltac:(lia)) as FR4.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & ERR4 & MI4 & _) & LXS4 & _).
  rewrite unsigned_lit in ST4 by lia.
  pose proof RNG2 as (QN0 & _ & _ & QNCL & QNIMG).
  assert (ES4 : es_rep m4 E 1 0 fl mk buf (upd nulls 1%nat (Z_to_bv 64 QF)) (upd ls 1%nat (Z_to_bv 64 line)) nulls).
  { eapply (es_rep_agree _ m3 m4); [exact CFR2| exact ES3|]. intros a Ha. right; left. exists (pe, E, 904). split; [exact INE1|]. split; [intros X0; exact X0| cbn; lia]. }
  assert (INE2 : In (pe, E, 904) ((qn, QN, ln + 1) :: (qf, QF, lf + 1) :: LBall)) by (right; right; exact INE).
  assert (INQ2 : In (qn, QN, ln + 1) ((qn, QN, ln + 1) :: (qf, QF, lf + 1) :: LBall)) by (left; reflexivity).
  assert (QNE : QN + (ln + 1) <= E \/ E + 904 <= QN).
  { destruct (RHEAP_blocks_disjoint_proof _ _ _ (qn, QN, ln + 1) (pe, E, 904) HP4 INQ2 INE2) as [D|D]; [| cbn [blk_addr blk_size blk_id fst snd] in D; lia| cbn [blk_addr blk_size blk_id fst snd] in D; lia].
    cbn [blk_addr blk_size blk_id fst snd]. intros Heq. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (or_intror INE) (eq_sym Heq)). }
  box QNE. box QNIMG.
  replace (Z.to_nat (ln + 1)) with (S (length nstr)) in BLK2 by lia.
  (* [comment removed for export] *)
  cprefix. eapply evt_cut.
  { pose proof dbg_s3_walk as X. unfold DBG_STACK, CM_STACK, RMALLOC_STACK, SITE_dbg_m2 in X.
    eapply (X ra sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ (Z_to_bv 64 line) F fc m4 lo E SF SN QN fl mk buf (upd nulls 1%nat (Z_to_bv 64 QF)) (upd ls 1%nat (Z_to_bv 64 line)) nstr nslack junk2 jx2);
      first [reflexivity | eassumption | subst lf ln; lia]. }
  intros ms3 (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m5 & -> & MU3 & WM3 & MI5 & ST5 & ES5 & BLK5).
  chere. apply climpl_done.
  exists a0x, m5, ((qn, QN, ln + 1) :: (qf, QF, lf + 1) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|].
  split; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)|].
  split. { unbox EIMG. unbox QNIMG. eapply (cstate_seg _ _ _ _ _ m4 m5 _ sp tp lo B (bv_unsigned sp));
      [exact CST4| exact MU3| exact WM3| exact MI5| | lia| exact SPB| | exact ST5| exact SPB].
    - apply Forall_cons; [apply cwin_stack; lia|]. apply Forall_cons; [apply (cwin_block _ _ _ (qn, QN, ln + 1)); [exact INQ2| cbn; lia| cbn; lia]|].
      apply Forall_cons; [apply (cwin_block _ _ _ (pe, E, 904)); [exact INE2| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS in *. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRB| exact FRM2| lia| intros a X0; exact X0| intros q _ _; tauto]| exact MU3| exact WM3| exact HP4| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia|].
    apply Forall_cons. { apply (cseg_ok_block _ _ _ _ _ (qn, QN, ln + 1)); [exact INQ2| | cbn; lia| cbn; lia].
      intros [[q A'] n'] Hb0 _ E1. cbn [blk_id fst] in E1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (or_intror Hb0) E1). }
    apply Forall_cons; [| apply Forall_nil]. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE2| intros b0 _ Hx; cbn; intros Ex; apply Hx; symmetry; exact Ex| cbn; lia| cbn; lia]. }
  exists qf, qn, QF, QN. split; [reflexivity|]. split; [reflexivity|].
  split.
  - (* [comment removed for export] *)
    assert (LBLout : forall b a, In b LBL -> blk_addr b <= a < blk_addr b + blk_size b ->
              a < alloc_ceiling /\ (a + 1 <= E \/ E + 904 <= a) /\ (a < QF \/ QF + (lf + 1) <= a) /\ (a < QN \/ QN + (ln + 1) <= a) /\ (a < 0x10000 \/ 0x353000 <= a)).
    { unbox DM. unbox DS. unbox DN. unbox DK. unbox MIMG. unbox SIMG. unbox NIMG. unbox KIMG.
      intros b a Hb Hr. assert (HbA : In b LBall) by (apply INCL; exact Hb).
      assert (D1 : blk_addr b + blk_size b <= QF \/ QF + (lf + 1) <= blk_addr b).
      { destruct (RHEAP_blocks_disjoint_proof _ _ _ b (qf, QF, lf + 1) HP2 (or_intror HbA) INQ1) as [D|D]; [| left; exact D| right; exact D].
        destruct b as [[q A'] n']. cbn. intros E1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST2 HbA E1). }
      assert (D2 : blk_addr b + blk_size b <= QN \/ QN + (ln + 1) <= blk_addr b).
      { destruct (RHEAP_blocks_disjoint_proof _ _ _ b (qn, QN, ln + 1) HP4 (or_intror (or_intror HbA)) INQ2) as [D|D]; [| left; exact D| right; exact D].
        destruct b as [[q A'] n']. cbn. intros E1. exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (or_intror HbA) E1). }
      rewrite ELBL in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]].
      - clear - Hr D1 D2 DM MIMG MCL. cbn [blk_addr blk_size fst snd] in *. lia.
      - clear - Hr D1 D2 DS SIMG SCL. cbn [blk_addr blk_size fst snd] in *. lia.
      - clear - Hr D1 D2 DN NIMG NCL. cbn [blk_addr blk_size fst snd] in *. lia.
      - clear - Hr D1 D2 DK KIMG KCL. cbn [blk_addr blk_size fst snd] in *. lia. }
    assert (STout : forall a, libenv_static a -> 0x2c0000 <= a < 0x3520d0 /\ ~ ralloc_static a /\ a <> LX_FLAGS /\ (a < bv_unsigned tp + -164 \/ bv_unsigned tp + -160 <= a)).
    { intros a Ha. destruct (libenv_fp_where LBL a (or_introl Ha)) as [X0|(b & Hb & b0)].
      - destruct X0 as (X1 & X2 & X3). clear - Ha X1 X2 X3 TPV. unfold libenv_static, IC_S, TH_ONCE, TH_KEY, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12, RMallocRep.RATP in Ha, TPV. split; [lia|]. split; [exact X2|]. split; [exact X3| lia].
      - exfalso. destruct b as [[q A'] n']. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (INCL _ Hb)) as (_ & _ & _ & _ & BIMG).
        clear - Ha BIMG b0. unfold libenv_static, IC_S, TH_ONCE, TH_KEY, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12, RMallocRep.RATP in Ha.
        cbn [blk_addr blk_size fst snd] in *. lia. }
    eapply libenv_agree; [exact ENV|].
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU1 WM1)|]. intros a [Hs|(b & Hb & Hr)]; cbv beta; cbn [outside].
      - destruct (STout a Hs) as (R1 & R2 & R3 & R4). clear - R1 R4 SLO GLO RSP. repeat split; try exact I; lia.
      - destruct (LBLout b a Hb Hr) as (R1 & R2 & R3 & R4 & R5). clear - R1 R5 SLO GLO LO RSP TPV. unfold RMallocRep.RATP in *. repeat split; try exact I; lia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact CFR1|]. intros a [Hs|(b & Hb & Hr)].
      - destruct (STout a Hs) as (R1 & R2 & R3 & R4). right; right. split; [lia|]. split; [exact R2|]. split; [exact R3|]. cbn. tauto.
      - right; left. exists b. split; [exact (INCL b Hb)|]. split; [intros X0; exact X0| exact Hr]. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU2 WM2)|]. intros a [Hs|(b & Hb & Hr)]; cbv beta; cbn [outside].
      - destruct (STout a Hs) as (R1 & R2 & R3 & R4). unbox QFIMG. unbox EIMG. clear - R1 SLO GLO RSP QFIMG EIMG. repeat split; try exact I; lia.
      - destruct (LBLout b a Hb Hr) as (R1 & R2 & R3 & R4 & R5). clear - R1 R2 R3 SLO GLO LO RSP. repeat split; try exact I; lia. }
    eapply agree_on_trans.
    { eapply agree_on_mono; [exact CFR2|]. intros a [Hs|(b & Hb & Hr)].
      - destruct (STout a Hs) as (R1 & R2 & R3 & R4). right; right. split; [lia|]. split; [exact R2|]. split; [exact R3|]. cbn. tauto.
      - right; left. exists b. split; [right; exact (INCL b Hb)|]. split; [intros X0; exact X0| exact Hr]. }
    eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU3 WM3)|]. intros a [Hs|(b & Hb & Hr)]; cbv beta; cbn [outside].
    + destruct (STout a Hs) as (R1 & R2 & R3 & R4). unbox QNIMG. unbox EIMG. clear - R1 SLO GLO RSP QNIMG EIMG. repeat split; try exact I; lia.
    + destruct (LBLout b a Hb Hr) as (R1 & R2 & R3 & R4 & R5). clear - R1 R2 R4 SLO GLO LO RSP. repeat split; try exact I; lia.
  - exists fl, mk, buf, (upd nulls 1%nat (Z_to_bv 64 QF)), (upd ls 1%nat (Z_to_bv 64 line)), (upd nulls 1%nat (Z_to_bv 64 QN)), [(1, true); (1, false)].
    split; [exact ES5|]. apply (slots_ok_debug qf qn QF QN (lf + 1) (ln + 1) ls); [lia| lia| lia| lia|].
    exact (cstate_head_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST4 (or_introl eq_refl)).
Qed.

End WithCeiling0.
