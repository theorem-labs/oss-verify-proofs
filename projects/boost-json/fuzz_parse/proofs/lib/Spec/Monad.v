(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree3Exc~~~~~~he3exc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~m45itree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~q84node89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad5Monad~~~~~~ub1M04pairhe2Okm43Ret04unit02tt3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshkddmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~hp53evt99OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad5Monad7Machine~~~~~~ht75implMub4mgetub4mupd04list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeijf7Segment" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.

Section Monad.
Context {St : Type}.

Definition M : ltac2:(zQ "00>1ATT") := ltac2:(zQ "40!h8!le!q0!u4\1AT>0?2St@2$2$3@1$1@2$0^2?2St").

Definition mret {A} (a : A) : M A := fun s => Ret (Ok (a, s)).
Definition mbind {A B} (m : M A) (f : A -> M B) : M B :=
  fun s => ebind (m s) (fun p => f (fst p) (snd p)).
Definition munr {A} : M A := fun _ => Ret Unr.
Definition mget : ltac2:(zQ "10!hie@1$0?2St") := ltac2:(zQ "60!h8!hj2!hj8!le!hjd!u4\1s?2St@3$4$5@1$3@2$0?2St?2St@2$2@2$0?2St?2St@4$1?2St?2St^1^1").
Definition mupd : ltac2:(zQ "20!hk3!hie>1f>0?2St?2St@1$1$0") := ltac2:(zQ "80!hk3!h8!hj2!hk9!hj8!le!hjd!u4\1f>0?2St?2St\1s?2St@3$6$7@1$5@2$1$0?2St@2$4@2$1$0?2St@4$2$0?2St$3@1^2^1").
Definition msys {A} (n : node) (dec : resp -> option A) : M A :=
  fun s => enode n (fun r => match dec r with Some a => Some (a, s) | None => None end).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Machine.
Variable segs : ltac2:(zQ "20!ij9!in4@1$0$1").

Definition implM {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
  impl segs (at_node segs) (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implM_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implM (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implM, mret. apply impl_ret_ok. exact H. Qed.

Lemma implM_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implM munr s Q ms.
Proof. intros. unfold implM, munr. apply impl_ret_unr. Qed.

Lemma implM_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
  implM m s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM (f a) s' Q ms') ->
  implM (mbind m f) s Q ms.
Proof.
  intros A B m f s Q1 Q ms Hm Hf. unfold implM, mbind in *.
  eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implM_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  implM m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implM m s Q' ms.
Proof.
  intros A m s Q Q' ms H HQ. unfold implM in *. eapply impl_epost_mono; [exact H|].
  intros [a s'] ms'; cbn; auto.
Qed.

Lemma implM_get : ltac2:(zQ "40!ho4!ht0!ii2!iib>1s?2St>1Q>1x?2St>2x0?2St>0$0P>2ms$0>0@3$1?4segs@2^2^3^3^1@5$2?2St$3^4^3^2").
Proof. intros. unfold implM, mget. apply impl_ret_ok. exact H. Qed.
Lemma implM_upd : ltac2:(zQ "60!hk3!ho4!hk9!ht0!ii2!ij2>1f>1x?2St?2St>1s?2St>1Q>1x$0>2x0?2St>0$1P>2ms$1>0@3$3?4segs@2^2$2@1^4^3^1@5$4$0@1$5^5^4^3^2").
Proof. intros. unfold implM, mupd. apply impl_ret_ok. exact H. Qed.

(* [comment removed for export] *)
Lemma implM_evt : forall {A} (c : M A) s Q P ms,
  evt segs P ms -> (forall ms', P ms' -> implM c s Q ms') -> implM c s Q ms.
Proof. intros A c s Q P ms H K. unfold implM in *. eapply impl_evt; eauto. Qed.

End Machine.
End Monad.

Arguments M St A : clear implicits.

Declare Scope mspec_scope.
Notation "x <- m ;; k" := (mbind m (fun x => k)) (at level 100, m at next level, right associativity) : mspec_scope.
Notation "m ;;; k" := (mbind m (fun _ => k)) (at level 100, right associativity) : mspec_scope.
Notation "' p <- m ;; k" := (mbind m (fun x => let 'p := x in k)) (at level 100, p pattern, m at next level, right associativity) : mspec_scope.
(* [comment removed for export] *)
