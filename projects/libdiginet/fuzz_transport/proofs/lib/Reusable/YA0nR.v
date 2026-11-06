(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: kit companion of YA0n.v (target-independent; copy with the module path changed).
   A footprint run whose footprint avoids the world's hidden memory is a silent prefix of a world walk: YK04R's
   fsteps_restrict turns it into a run of the restricted state, and YA0n.SRr_msteps lifts that run. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0i YK11 YK04 YK04R YA0n.
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
End e.
End d.
