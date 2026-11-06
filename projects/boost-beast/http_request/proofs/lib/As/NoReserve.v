(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_syscall_effect_nil :
  forall (m : Model) (r : word) (zs us : list (word * word)),
  materialize_model_accesses m
    (syscall_effect_accesses (mkEffectU r [] zs us [] []))
  = Some m.
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.

(* [comment removed for export] *)
Lemma materialize_syscall_effect_copyin_disjoint :
  forall (m : Model) (r : word) (a : word) (n : nat),
  accesses_outside_lazy [(a, n)] (m_vm_lazy m) ->
  materialize_model_accesses m
    (syscall_effect_accesses (with_copyins [(a, n)] (mkEffect r [] [])))
  = Some m.
Proof.
  intros m r a n Hout.
  exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.

(* [comment removed for export] *)
Lemma materialize_munmap_eff_nil : forall (m : Model) (ms : machine_state),
  materialize_model_accesses m (syscall_effect_accesses (munmap_eff ms))
  = Some m.
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma access_outside_range_mono : forall (a : word) (n n' : nat) (lo sz : word),
  (n' <= n)%nat ->
  access_outside_range a n lo sz ->
  access_outside_range a n' lo sz.
Proof.
  intros a n n' lo sz Hle [Hnw Hd].
  split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.

(* [comment removed for export] *)
Lemma accesses_outside_lazy_incl :
  forall (accs accs' : list (word * nat)) (lazy : list (word * word)),
  (forall x, In x accs' -> In x accs) ->
  accesses_outside_lazy accs lazy ->
  accesses_outside_lazy accs' lazy.
Proof.
  intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
  exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.

Lemma accesses_outside_lazy_app_l :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs1 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. left. exact Hx.
Qed.

Lemma accesses_outside_lazy_app_r :
  forall accs1 accs2 lazy,
  accesses_outside_lazy (accs1 ++ accs2) lazy ->
  accesses_outside_lazy accs2 lazy.
Proof.
  intros accs1 accs2 lazy Hout.
  apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
  intros x Hx. apply in_or_app. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma accesses_outside_lazy_shrink :
  forall (a : word) (len n : nat) (lazy : list (word * word)),
  (n <= len)%nat ->
  accesses_outside_lazy [(a, len)] lazy ->
  accesses_outside_lazy [(a, n)] lazy.
Proof.
  intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
  destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
  apply (access_outside_range_mono a len n lo sz Hle).
  apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
  vm_add_lazy a n (mmap_model a n m).

Lemma mmap_model_noreserve_halted : forall a n m,
  m_halted (mmap_model_noreserve a n m) = m_halted m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fs : forall a n m,
  m_fs (mmap_model_noreserve a n m) = m_fs m.
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fd1chan : forall a n m,
  fd1chan m -> fd1chan (mmap_model_noreserve a n m).
Proof. intros a n m H. exact H. Qed.
(* [comment removed for export] *)
Lemma mmap_model_noreserve_lazy : forall a n m,
  m_vm_lazy (mmap_model_noreserve a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof. reflexivity. Qed.

