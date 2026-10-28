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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I3_base Fz_I3_kit Fz_W3_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_sa Fz_I3_fxi Fz_W2_exd Fz_W5_defs Fz_W5_env Fz_W5_gsi Fz_W5_vset Fz_W5_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma slots_ok_nulls : slots_ok (repeat (Z_to_bv 64 0) 16) (repeat (Z_to_bv 64 0) 16) [] [].
Proof.
  split; [constructor|]. split; [reflexivity|]. split; [intros ik []|].
  split; [intros j ik b Hj; destruct j; discriminate Hj|].
  split; [| constructor].
  intros [i isf] w Hi Hw _. unfold slot_word in Hw. cbn [fst snd] in *.
  assert (X : forall l : list word, l = repeat (Z_to_bv 64 0) 16 -> nth_error l (Z.to_nat i) = Some w -> w = Z_to_bv 64 0).
  { intros l -> Hn. apply nth_error_In in Hn. apply repeat_spec in Hn. exact Hn. }
  destruct isf; eapply X; eauto.
Qed.

Theorem err_new_rest_proof : err_new_rest_stmt libenv errst_at_rest errst_live.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold err_new_rest_stmt. intros until B. intros CST SLO ENV INCL OWN REST.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  pose proof (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST)) as ND.
  destruct (libenv_cells _ _ _ ENV) as (od & pad & tw & ne & k & MK & SA & NODES & pm & psa & pn & pk & LK & ELBL & STOP & ONCE & OD & OC & KC & HK & TS & SLOT & HMK & P3 & HSA & HDR & HNO & NE & LEAF).
  destruct REST as (_ & fl & mk & buf & ls & ES).
  destruct OWN as [INE INL].
  assert (INM : In (pm, MK, 72) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INS : In (psa, SA, 32) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INN : In (pn, NODES, 128) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  assert (INK : In (pk, LK, 40) LBall) by (apply INCL; rewrite ELBL; cbn; tauto).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INE) as (E0 & E16 & _ & ECL & EIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INM) as (_ & M16 & _ & MCL & MIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INS) as (_ & S16 & _ & SCL & SIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INN) as (_ & N16 & _ & NCL & NIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST INK) as (_ & _ & _ & KCL & KIMG).
  assert (DJ : forall p X n, In (p, X, n) LBall -> n <> 904 -> X + n <= E \/ E + 904 <= X).
  { intros p X n Hin Hn. destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, X, n) (pe, E, 904) HP Hin INE) as [D|D]; cbn [blk_addr blk_size blk_id fst snd] in *; [| lia| lia].
    intros Heq. subst p. destruct (cown_block_eq LBall pe X n E 904 ND Hin INE) as [_ Hn']. lia. }
  pose proof (DJ _ _ _ INM ltac:(lia)) as DM. pose proof (DJ _ _ _ INS ltac:(lia)) as DS. pose proof (DJ _ _ _ INN ltac:(lia)) as DN. pose proof (DJ _ _ _ INK ltac:(lia)) as DK.
  wbox DM. wbox DS. wbox DN. wbox DK. wbox MIMG. wbox SIMG. wbox NIMG. wbox KIMG.
  assert (TPV : bv_unsigned tp = RATP) by (rewrite TP; apply unsigned_lit; unfold RATP; lia).
  unfold ERRN_STACK, GLOBALS_TOP, ceil_window in *.
  rewrite <- TPV in TS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply climpl_evt.
  { pose proof T_err_new_rest_proof as X. unfold T_err_new_rest_stmt, ERRNEW_STACK, GSI_STACK, FZ_ERRNEW in X. unfold wz, FZ_ERR_NEW.
    eapply (X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo TSD_MAIN k MK SA NODES E errv od pad tw ne fl mk buf ls);
      first [reflexivity | eassumption | unfold TSD_MAIN, IC_S, RMallocRep.RATP in *; lia | Z.div_mod_to_equations; lia]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fl' & mk' & buf' & ls' & m' & -> & MU & WM & MI' & ERR' & ST' & ES').
  unfold ERRNEW_STACK, GSI_STACK in MU. apply climpl_done. exists a0', m', LBall.
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [apply cgrow_refl|].
  split. { eapply (cstate_seg_e _ s LBall LB L m m' sp sp tp lo B (bv_unsigned sp) (sx32 errv));
      [exact CST| exact MU| exact WM| exact MI'| | lia| exact SPB| | exact ERR'| exact ST'| exact SPB].
    - apply Forall_cons; [left; apply cwin_stack; lia|]. apply Forall_cons; [right; cbn [fst snd]; lia|].
      apply Forall_cons; [left; apply (cwin_block _ _ _ (pe, E, 904)); [exact INE| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS, RMallocRep.RATP in *. lia. }
  split. { eapply cframe_seg_e; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [left; apply cseg_ok_stack; lia|]. apply Forall_cons; [right; unfold RMallocRep.RERRNO, RMallocRep.RATP in *; cbn [fst snd]; lia|].
    apply Forall_cons; [| apply Forall_nil]. left. apply (cseg_ok_block _ _ _ _ _ (pe, E, 904)); [exact INE| intros b0 _ Hx; cbn; intros Ex; apply Hx; symmetry; exact Ex| cbn; lia| cbn; lia]. }
  split; [reflexivity|]. split; [reflexivity|].
  split; [| exists fl', mk', buf', (repeat (Z_to_bv 64 0) 16), ls', (repeat (Z_to_bv 64 0) 16), []; split; [exact ES'| exact slots_ok_nulls]].
  eapply libenv_agree; [exact ENV|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|].
  intros a [Hs|(b & Hb & Hr)]; cbv beta; cbn [outside].
  - clear - Hs SLO GLO LO RSP TPV EIMG E0 ECL. unfold libenv_static, IC_S, TH_ONCE, TH_KEY, TSD_MAIN, DC_S, DC_GLOBAL_LOCK, DC_IP12, RMallocRep.RATP in *. repeat split; try exact I; lia.
  - rewrite ELBL in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; cbn [blk_addr blk_size fst snd] in Hr; unfold RMallocRep.RATP in *;
      [ wunbox DM; wunbox MIMG; clear - Hr MCL MIMG DM LO SLO GLO RSP TPV
      | wunbox DS; wunbox SIMG; clear - Hr SCL SIMG DS LO SLO GLO RSP TPV
      | wunbox DN; wunbox NIMG; clear - Hr NCL NIMG DN LO SLO GLO RSP TPV
      | wunbox DK; wunbox KIMG; clear - Hr KCL KIMG DK LO SLO GLO RSP TPV ]; repeat split; try exact I; lia.
Qed.

End WithCeiling0.
