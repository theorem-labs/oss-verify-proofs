(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: kit companion of YA0n.v (target-independent; copy with the module path changed).
   A footprint run whose footprint avoids the world's hidden memory is a silent prefix of a world walk: YK04R's
   fsteps_restrict turns it into a run of the restricted state, and YA0n.SRr_msteps lifts that run.
   The run also keeps every hidden byte (fsteps_keeps_hidden; SRr_fevt_hid hands that fact to the continuation,
   in the form YCbq.ajournal_exec takes). And a world walk does not tell apart two register maps that agree on
   every register but x0 (SRr_xregs_eqv, from srealizes_cfg_eqv: lib/Lib/Regs6ss.v's step transport). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0i YK11 YK04 YK04R YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.

(* The model may materialize pages on the way (same_but_materialized), as in YA0n.SRr_msteps. *)
Theorem SRr_fsteps : forall (W : world segs) ms ms' model RNG (Q : world segs -> config -> Prop),
  fsteps segs RNG ms ms' ->
  fp_avoids (w_H W) RNG ->
  (forall model', same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W ms ms' model RNG Q Hrun Hfp Hk.
  destruct (fsteps_restrict segs (w_H W) (w_Hoff W) Hwx RNG ms ms' Hrun Hfp) as [Hms Heq].
  apply (SRr_msteps segs Hwx W ms (restrict (w_H W) ms') model Q Hms).
  intros model' Hsame _. rewrite <- Heq. exact (Hk model' Hsame).
Qed.

(* Eventually-form, for contracts stated as `exists ms', run ms ms' /\ P ms'` (Lib/ExecF.v evtF RNG P ms). *)
Corollary SRr_fevt : forall (W : world segs) ms model RNG (P : machine_state -> Prop)
    (Q : world segs -> config -> Prop),
  (exists ms', fsteps segs RNG ms ms' /\ P ms') ->
  fp_avoids (w_H W) RNG ->
  (forall ms' model', P ms' -> same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (SRr_fsteps W ms ms' model RNG Q Hrun Hfp (fun model' Hs => Hk ms' model' HP Hs)).
Qed.

(* The run changes no byte that H hides (YK04R.fsteps_restrict: the end state is the start state's hidden bytes
   over the restricted run's end state). *)
Lemma fsteps_keeps_hidden : forall (H : word -> bool) RNG ms ms',
  H_off_segments segs H ->
  fsteps segs RNG ms ms' ->
  fp_avoids H RNG ->
  forall x : word, H x = true -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros H RNG ms ms' HH Hrun Hfp x Hx.
  destruct (fsteps_restrict segs H HH Hwx RNG ms ms' Hrun Hfp) as [_ Heq].
  rewrite Heq at 1. cbn [ms_mem unrestrict]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.

(* SRr_fevt whose continuation also gets the hidden bytes of the start state: the premise
   `forall x : word, w_H Wc x = true -> memc' x = memc x` of YCbq.ajournal_exec, for a run that writes memory. *)
Corollary SRr_fevt_hid : forall (W : world segs) ms model RNG (P : machine_state -> Prop)
    (Q : world segs -> config -> Prop),
  (exists ms', fsteps segs RNG ms ms' /\ P ms') ->
  fp_avoids (w_H W) RNG ->
  (forall ms' model', P ms' -> (forall x : word, w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     same_but_materialized model model' -> SRr segs W (mkCfg ms' model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W ms model RNG P Q (ms' & Hrun & HP) Hfp Hk.
  exact (SRr_fsteps W ms ms' model RNG Q Hrun Hfp
    (fun model' Hs => Hk ms' model' HP (fsteps_keeps_hidden (w_H W) RNG ms ms' (w_Hoff W) Hrun Hfp) Hs)).
Qed.
End e.

Section g.
Variable segs : list Segment.

(* srealizes (YK18.v) cannot tell apart two configurations that are Regs6ss.cfg_eqv (same registers but x0, the
   rest equal): Regs6ss.sstep_xport moves each step to the other configuration, xport_round_trip moves it back. *)
Lemma srealizes_cfg_eqv : forall c T, YK18.srealizes segs c T ->
  forall c', Regs6ss.cfg_eqv c c' -> YK18.srealizes segs c' T.
Proof.
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hsp Hh | c T T' H IH Heq]; intros c' Heqv.
  - destruct c as [ms mo], c' as [ms' mo'], Heqv as [Hms Hmo].
    cbn [cfg_ms cfg_model] in Hms, Hmo. subst mo'.
    destruct Hnode as [Hfwd Hexact].
    apply (YK18.srz_node segs (mkCfg ms' mo) I evs (fun i => Regs6ss.xport_cfg segs ms ms' (nx i)) T i0).
    + split.
      * intros i. exact (proj1 (Regs6ss.sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hfwd i))).
      * intros e st Hst.
        destruct (Regs6ss.sstep_xport segs ms' ms mo e st (Regs6ss.ms_eqv_sym ms ms' Hms) Hst) as [Hst0 _].
        destruct (Hexact e _ Hst0) as (j & -> & Hj).
        exists j. split; [reflexivity|].
        rewrite <- (Regs6ss.xport_round_trip segs ms ms' mo (evs j) st Hms Hst), Hj. reflexivity.
    + intros i. apply (IH i).
      exact (proj2 (Regs6ss.sstep_xport segs ms ms' mo (evs i) (SNext (nx i)) Hms (Hfwd i))).
  - apply YK18.srz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - destruct Hsp as [[] _].
  - exact (YK18.srz_conseq segs c' T T' (IH c' Heqv) Heq).
Qed.

Lemma SRr_cfg_eqv : forall (W : world segs) c c' (Q : world segs -> config -> Prop),
  SRr segs W c Q -> Regs6ss.cfg_eqv c c' -> SRr segs W c' Q.
Proof.
  intros W c c' Q H Heqv HI T HK.
  pose proof Heqv as [_ Hmo]. rewrite <- Hmo in HI.
  exact (srealizes_cfg_eqv c T (H HI T HK) c' Heqv).
Qed.

(* A cut's state (YG0d.cfg_at = mkCfg of lib/Lib's MS, A/ProgBridge.v cfg_at_MS) carries the actual register map,
   a footprint contract's start state the canonical one (Regs6ss.mkR_of regs); the two are Regs6ss.xregs_eqv
   (Regs6ss.mkR_of_eqv), so a walk from the canonical state is a walk from the cut's state:
     SRr_xregs_eqv W (Regs6ss.mkR_of regs) regs ... H (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs)).
   MS's fifth argument rv is the reservation (MS has no pending service call). *)
Lemma SRr_xregs_eqv : forall (W : world segs) (R R' F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (m ro : word -> option byte) (md : Model) (Q : world segs -> config -> Prop),
  SRr segs W (mkCfg (MState.MS R F pc fc rv m ro) md) Q ->
  Regs6ss.xregs_eqv R R' ->
  SRr segs W (mkCfg (MState.MS R' F pc fc rv m ro) md) Q.
Proof.
  intros W R R' F pc fc rv m ro md Q H HR. apply (SRr_cfg_eqv W _ _ Q H).
  split; [|reflexivity]. split; [exact HR|]. repeat split; reflexivity.
Qed.

(* Both directions (xregs_eqv is symmetric). *)
Corollary SRr_xregs_iff : forall (W : world segs) (R R' F : bvmap 5 word) (pc : word) (fc : bv 32)
    (rv : option word) (m ro : word -> option byte) (md : Model) (Q : world segs -> config -> Prop),
  Regs6ss.xregs_eqv R R' ->
  (SRr segs W (mkCfg (MState.MS R F pc fc rv m ro) md) Q <->
   SRr segs W (mkCfg (MState.MS R' F pc fc rv m ro) md) Q).
Proof.
  intros W R R' F pc fc rv m ro md Q HR. split; intros H.
  - exact (SRr_xregs_eqv W R R' F pc fc rv m ro md Q H HR).
  - exact (SRr_xregs_eqv W R' R F pc fc rv m ro md Q H (Regs6ss.xregs_eqv_sym R R' HR)).
Qed.
End g.
End d.
