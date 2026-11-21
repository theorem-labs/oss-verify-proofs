(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KInv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KLink. Import SM01.KStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import KEv. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM06. Import SM06. Import SM06.MI_Contracts.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrBridge MrFeasNull MrFeasSome1 MrFeasNull44 MrKRefuse.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Lift.
Context {rc : runConstT}.

Definition refusable (e : ev) : Prop :=
  match e with
  | EBrk _ | EMprotect _ _ _ => True
  | EMmap _ _ _ flags => (Z.land flags MAP_FIXED =? 0) = true
  | _ => False
  end.

Definition refuses (e : ev) (z : Z) : Prop :=
  match e with
  | EBrk req => req = 0 \/ z <> req
  | EMmap _ _ _ _ => is_err z = true
  | EMprotect _ _ _ => ((z =? 0) || (z =? TWO64 - ENOSYS)) = false
  | _ => False
  end.

Lemma tpath_msys_ok : forall {A} n (dec : resp -> option A) (s : PState) mo rsp mo' a,
  nstep n mo rsp mo' [] -> dec rsp = Some a ->
  tpath nstep (Monad.msys n dec s) mo [] (Ok (a, s)) mo'.
Proof.
  intros A n dec s mo rsp mo' a Hst Hd. unfold Monad.msys. apply tpath_enode. exists rsp. split; [exact Hst|]. rewrite Hd. reflexivity.
Qed.

Lemma tpath_mbind_ok : forall {A C} (m : Monad.M PState A) (f : A -> Monad.M PState C) s mo a s1 mo1 r mo',
  tpath nstep (m s) mo [] (Ok (a, s1)) mo1 -> tpath nstep (f a s1) mo1 [] r mo' ->
  tpath nstep (Monad.mbind m f s) mo [] r mo'.
Proof.
  intros A C m f s mo a s1 mo1 r mo' H1 H2. unfold Monad.mbind. apply tpath_ebind. right.
  exists [], (a, s1), mo1, []. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.

Lemma tpath_ret_ok : forall {A} (a : A) (s : PState) mo, tpath nstep (Monad.mret a s) mo [] (Ok (a, s)) mo.
Proof. intros. cbn. repeat split. Qed.



Lemma tfeas_of_tpath : forall {R} (t : itree node R) mo tr r mo' (S : R -> Prop),
  tpath nstep t mo tr r mo' -> S r -> B.tfeas node nstep t mo S.
Proof.
  intros R t. induction t as [r0|n k IH]; intros mo tr r mo' S Hp HS; cbn in *.
  - destruct Hp as (-> & _ & _). exact HS.
  - destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _). exists rsp, mo1, evs. split; [exact Hst|]. eapply IH; eauto.
Qed.

Definition is_null (r : exc (option bptr * PState)) : bool :=
  match r with Ok (None, _) => true | _ => false end.




End Lift.
