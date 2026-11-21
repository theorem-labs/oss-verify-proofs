(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Monad CMonad CMonadX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import StartupM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section StartupMC.
  Variable segs : list Segment.

  Lemma startup_implMC_of : forall {St B : Type} (s : St) (k : unit -> MC St B)
      (Q : B -> St -> machine_state -> Prop) (P : machine_state -> Prop) ms0,
    impl segs (at_node segs) (enode NSetTid dec_set_tid) (epost (fun _ => P)) ms0 ->
    (forall ms', P ms' -> implMC segs (k tt) s Q ms') ->
    implMC segs (cmbind (clift (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt))) k) s Q ms0.
  Proof.
    intros St B s k Q P ms0 H K.
    eapply implMC_lift_bind with (Q1 := fun _ s' ms' => P ms' /\ s' = s).
    - eapply implM_bind with (Q1 := fun _ s' ms' => P ms' /\ s' = s).
      + unfold implM, msys. eapply impl_epost_mono; [eapply (impl_enode_state segs NSetTid dec_set_tid s (fun _ => P)); exact H|].
        intros [t s'] ms' [HP Hs]; cbn in *. split; assumption.
      + intros t s' ms' [HP ->]. apply implM_ret. apply evt_done. split; [exact HP | reflexivity].
    - intros [] s' ms' [HP ->]. apply K. exact HP.
  Qed.
End StartupMC.
