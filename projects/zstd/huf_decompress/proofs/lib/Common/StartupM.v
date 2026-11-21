(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (impl_enode_state, startup_implM_of)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_StartupM () := "C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI47Corelib4Init5Logic2eq00I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8StartupM@impl_enode_stateC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4msysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~".
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
