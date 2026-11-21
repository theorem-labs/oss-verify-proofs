(* The dead-arm check ([DeadArm.dead_ok]) of the main trees whose data needs no
   regeneration, computed once per tree and per r.  Hole 26 is the only hole at the flag [false] ([DeadArm.hf26]):
   [ArgR4Asan.TREE4] fills it with [ArgleafPlansAsan.argda1o_tospin1], a plan with spins, which the check does not
   ask; the check asks instead that every [PHandoff 26] of [argda1otr] sit under a refused arm. *)
From Stdlib Require Import Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import DeadArm.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.MainGlue.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.MainGlueB.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR2Asan.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR3Asan.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR4Asan.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR2Both.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR3Both.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR4Both.

Module MA := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.MainGlue.
Module MB := OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.MainGlueB.

Lemma TREE2_asan_dead : forall rsb, MA.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR2Asan.TREE2 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma TREE3_asan_dead : forall rsb, MA.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR3Asan.TREE3 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma TREE4_asan_dead : forall rsb, MA.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR4Asan.TREE4 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.

Lemma TREE2_both_dead : forall rsb, MB.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR2Both.TREE2 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma TREE3_both_dead : forall rsb, MB.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR3Both.TREE3 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma TREE4_both_dead : forall rsb, MB.mtree_dead hf26 (OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.ArgR4Both.TREE4 rsb) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
