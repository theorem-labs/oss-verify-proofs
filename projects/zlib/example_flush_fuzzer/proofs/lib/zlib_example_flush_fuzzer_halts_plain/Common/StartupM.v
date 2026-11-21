(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section StartupM.
  Variable segs : list Segment.

  Lemma impl_enode_state : forall {A St : Type} (n : node) (pl : resp -> option A) (s : St)
      (P : A -> machine_state -> Prop) ms,
    impl segs (at_node segs) (enode n pl) (epost P) ms ->
    impl segs (at_node segs) (enode n (fun r => match pl r with Some a => Some (a, s) | None => None end))
         (epost (fun p ms' => P (fst p) ms' /\ snd p = s)) ms.
  Proof.
    intros A St n pl s P ms H. cbn in *.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *.
    - eapply evt_mono; [exact Hk|]. intros ms' HP. split; [exact HP | reflexivity].
    - exact Hk.
  Qed.

End StartupM.
