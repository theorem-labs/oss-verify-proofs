(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrRegsEqvW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Theorem realizes_eqv : forall c T, realizes segs c T -> forall c', cfg_eqv c c' -> realizes segs c' T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 [Hfw Hbw] Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
  -
    pose (I' := { p : I * config | sstep segs c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
    assert (Hsucc : forall i, exists c2', sstep segs c' (evs i) (SNext c2') /\ cfg_eqv (nx i) c2').
    { intros i. destruct (sstep_cfg_eqv segs c c' (evs i) (SNext (nx i)) Heqv (Hfw i)) as (X' & Hst' & HX).
      destruct X' as [c2'|]; cbn in HX; [|contradiction]. exists c2'. split; assumption. }
    destruct (Hsucc i0) as (c0' & Hst0 & He0).
    pose (i0' := (exist _ (i0, c0') (conj Hst0 He0) : I')).
    eapply rz_conseq.
    + apply (rz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
               (fun p => T (fst (proj1_sig p))) i0').
      * split.
        -- intros [[i c2'] [Hst He]]. cbn. exact Hst.
        -- intros e st Hst.
           destruct (sstep_cfg_eqv segs c' c e st (cfg_eqv_sym _ _ Heqv) Hst) as (X & HstX & HX).
           destruct (Hbw e X HstX) as (i & -> & ->).
           destruct st as [c2'|]; cbn in HX; [|contradiction].
           exists (exist _ (i, c2') (conj Hst (cfg_eqv_sym _ _ HX))). split; reflexivity.
      * intros [[i c2'] [Hst He]]. cbn. apply (IH i). exact He.
    + intros tr. unfold t_alt. split.
      * intros [[[i c2'] [Hst He]] Htr]. cbn in Htr. exists i. exact Htr.
      * intros [i Htr]. destruct (Hsucc i) as (c2' & Hst & He).
        exists (exist _ (i, c2') (conj Hst He)). cbn. exact Htr.
  - apply rz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - eapply rz_conseq; [apply IH; exact Heqv | exact Heq].
Qed.

End WithSegs.
