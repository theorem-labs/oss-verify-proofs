(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA NodesA CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Monad CMonad CMonadX.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AProto CProto.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMACX.
Context {St : Type}.
Local Notation postA A := (A -> St -> footprint -> machine_state -> Prop).

Lemma implMAC_from_evtF : forall {A} RNG (mc : MC St A) s (Q : postA A) ms,
  evtF bsegs RNG (fun ms' => implMAC RNG mc s Q ms') ms -> implMAC RNG mc s Q ms.
Proof. intros A RNG mc s Q ms H. eapply implMAC_evtF; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implMAC_lift_bind : forall {A B} RNG (m : Monad.M St A) (f : A -> MC St B) s (Q1 : postA A) (Q : postA B) ms,
  implS bsegs RNG (m s) (epostF (fun p => Q1 (fst p) (snd p))) ms ->
  (forall a s' RNG' ms', Q1 a s' RNG' ms' -> implMAC RNG' (f a) s' Q ms') ->
  implMAC RNG (cmbind (clift m) f) s Q ms.
Proof. intros A B RNG m f s Q1 Q ms Hm Hf. eapply implMAC_bind; [apply implMAC_lift; exact Hm| exact Hf]. Qed.

Lemma implMAC_retb : forall {A B} RNG (a : A) (f : A -> MC St B) s (Q : postA B) ms,
  implMAC RNG (f a) s Q ms -> implMAC RNG (cmbind (cmret a) f) s Q ms.
Proof. intros A B RNG a f s Q ms H. exact H. Qed.

Lemma implMAC_liftretb : forall {A B} RNG (a : A) (f : A -> MC St B) s (Q : postA B) ms,
  implMAC RNG (f a) s Q ms -> implMAC RNG (cmbind (clift (mret a)) f) s Q ms.
Proof. intros A B RNG a f s Q ms H. exact H. Qed.

Lemma implMAC_bind_assoc : forall {A B C} RNG (m : MC St A) (g : A -> MC St B) (f : B -> MC St C) s (Q : postA C) ms,
  implMAC RNG (cmbind m (fun a => cmbind (g a) f)) s Q ms ->
  implMAC RNG (cmbind (cmbind m g) f) s Q ms.
Proof.
  intros A B C RNG m g f s Q ms H. unfold implMAC, cmbind, cebind in *.
  apply implFC_bind_assoc. eapply implFC_bind_cong; [| exact H].
  intros [|[a s']] RNG' ms'; cbn [cbind fst snd]; intros H'; exact H'.
Qed.

Lemma implMAC_lift_bind_assoc : forall {A B C} RNG (m : Monad.M St A) (g : A -> Monad.M St B) (f : B -> MC St C) s (Q : postA C) ms,
  implMAC RNG (cmbind (clift m) (fun a => cmbind (clift (g a)) f)) s Q ms ->
  implMAC RNG (cmbind (clift (mbind m g)) f) s Q ms.
Proof. intros A B C RNG m g f s Q ms H. rewrite clift_mbind. apply implMAC_bind_assoc. exact H. Qed.

Lemma implMAC_of_implMA : forall {A} RNG (c : MC St A) (m : Monad.M St A) s (Q : postA A) ms,
  c = clift m -> implS bsegs RNG (m s) (epostF (fun p => Q (fst p) (snd p))) ms -> implMAC RNG c s Q ms.
Proof. intros A RNG c m s Q ms -> H. apply implMAC_lift. exact H. Qed.

End ImplMACX.
End CANSEC1.
