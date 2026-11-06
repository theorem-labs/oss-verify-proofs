(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Monad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section StartupM.
  Variable segs : list Segment.

  (* [comment removed for export] *)
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

  Lemma startup_implM_of : forall {St B : Type} (s : St) (k : unit -> @M St B)
      (Q : B -> St -> machine_state -> Prop) (P : machine_state -> Prop) ms0,
    impl segs (at_node segs) (enode NSetTid dec_set_tid) (epost (fun _ => P)) ms0 ->
    (forall ms', P ms' -> implM segs (k tt) s Q ms') ->
    implM segs (mbind (mbind (msys NSetTid dec_set_tid) (fun _ => mret tt)) k) s Q ms0.
  Proof.
    intros St B s k Q P ms0 H K.
    eapply implM_bind with (Q1 := fun _ s' ms' => P ms' /\ s' = s).
    - eapply implM_bind with (Q1 := fun _ s' ms' => P ms' /\ s' = s).
      + unfold implM, msys. eapply impl_epost_mono; [eapply (impl_enode_state NSetTid dec_set_tid s (fun _ => P)); exact H|].
        intros [t s'] ms' [HP Hs]; cbn in *. split; assumption.
      + intros t s' ms' [HP ->]. apply implM_ret. apply evt_done. split; [exact HP | reflexivity].
    - intros [] s' ms' [HP ->]. apply K. exact HP.
  Qed.
End StartupM.
