(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable Dispatch.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimDefs LimFrame LimInv.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition arm_frame_ok (a : SpecArm) : Prop :=
  forall L i m o, bv_unsigned (in_sysno i) = sa_no a -> Inv m -> sa_spec a i m o ->
    alloc_budget_refused_b i m = false -> alloc_budget_refused_b i (m_relim L m) = false ->
    sa_spec a i (m_relim L m) (o_relim L o).
Definition arm_lpres_ok (a : SpecArm) : Prop := lpres (sa_spec a).
Definition arm_inv_ok (a : SpecArm) : Prop := forall i m x m' evs, sa_spec a i m (Ok x m' evs) -> Inv m -> Inv m'.

Lemma lookup_arm_sound : forall t n a, lookup_arm t n = Some a -> In a t /\ sa_no a = n.
Proof.
  induction t as [| b t IH]; intros n a H; [discriminate H |].
  cbn [lookup_arm] in H. destruct (Z.eqb (sa_no b) n) eqn:E.
  - injection H as <-. apply Z.eqb_eq in E. split; [left; reflexivity | exact E].
  - destruct (IH n a H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.

Lemma gate_214 : forall i m, bv_unsigned (in_sysno i) = 214%Z -> alloc_budget_refused_b i m = brk_budget_refused_b m (in_arg i 0).
Proof. intros i m H. unfold alloc_budget_refused_b. cbv zeta. rewrite H. reflexivity. Qed.
Lemma gate_216 : forall i m, bv_unsigned (in_sysno i) = 216%Z ->
  alloc_budget_refused_b i m = mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros i m H. unfold alloc_budget_refused_b. cbv zeta. rewrite H. reflexivity. Qed.
Lemma gate_222 : forall i m, bv_unsigned (in_sysno i) = 222%Z ->
  alloc_budget_refused_b i m = mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros i m H. unfold alloc_budget_refused_b. cbv zeta. rewrite H. reflexivity. Qed.
Lemma gate_226 : forall i m, bv_unsigned (in_sysno i) = 226%Z ->
  alloc_budget_refused_b i m = mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m H. unfold alloc_budget_refused_b. cbv zeta. rewrite H. reflexivity. Qed.
