(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Class StepCfg := { the_scfg : Run.SpuriousCfg }.

Global Instance hunspell_scfg : StepCfg :=
  {| the_scfg := Run.mkSpuriousCfg false true true true true true |}.

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
Import ListNotations.

(* [comment removed for export] *)
Lemma injected_arm_none_29 : Run.injected_arm 29 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_57 : Run.injected_arm 57 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_63 : Run.injected_arm 63 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_64 : Run.injected_arm 64 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_66 : Run.injected_arm 66 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_93 : Run.injected_arm 93 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_94 : Run.injected_arm 94 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_96 : Run.injected_arm 96 = None.   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_215 : Run.injected_arm 215 = None. Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_openat : Run.injected_arm 56 = Some (Run.mkInjectedArm 56 Run.FamFs openat_errnos).
Proof. reflexivity. Qed.
Lemma injected_arm_brk : Run.injected_arm 214 = Some (Run.mkInjectedArm 214 Run.FamAlloc []).
Proof. reflexivity. Qed.
Lemma injected_arm_mmap : Run.injected_arm 222 = Some (Run.mkInjectedArm 222 Run.FamAlloc mmap_errnos).
Proof. reflexivity. Qed.
Lemma injected_arm_mprotect : Run.injected_arm 226 = Some (Run.mkInjectedArm 226 Run.FamAlloc mprotect_errnos).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma injected_family_off_none : forall cfg i,
  Run.injected_arm (bv_unsigned (in_sysno i)) = None ->
  Run.injected_family_off cfg i = false.
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma not_spurious_none : forall cfg i m eff,
  Run.injected_arm (bv_unsigned (in_sysno i)) = None ->
  ~ Run.spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff H. apply Run.spurious_refusal_family_on.
  apply injected_family_off_none. exact H.
Qed.

(* [comment removed for export] *)
Lemma injected_family_off_openat : forall cfg i,
  bv_unsigned (in_sysno i) = 56%Z ->
  Run.injected_family_off cfg i = negb (Run.sc_fs cfg).
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_brk : forall cfg i,
  bv_unsigned (in_sysno i) = 214%Z ->
  Run.injected_family_off cfg i = negb (Run.sc_alloc cfg).
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_mmap : forall cfg i,
  bv_unsigned (in_sysno i) = 222%Z ->
  Run.injected_family_off cfg i = negb (Run.sc_alloc cfg).
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_mprotect : forall cfg i,
  bv_unsigned (in_sysno i) = 226%Z ->
  Run.injected_family_off cfg i = negb (Run.sc_alloc cfg).
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap : forall i m ret,
  bv_unsigned (in_sysno i) = 222%Z ->
  Run.refusal_b i m ret = bv_eqb ret (errno_ret ENOMEM).
Proof.
  intros i m ret H. unfold Run.refusal_b. rewrite H. cbn. rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma refusal_b_mprotect : forall i m ret,
  bv_unsigned (in_sysno i) = 226%Z ->
  Run.refusal_b i m ret = bv_eqb ret (errno_ret ENOMEM).
Proof.
  intros i m ret H. unfold Run.refusal_b. rewrite H. cbn. rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma refusal_b_brk : forall i m ret,
  bv_unsigned (in_sysno i) = 214%Z ->
  Run.refusal_b i m ret = Run.brk_refusal_b m (in_arg i 0) ret.
Proof. intros i m ret H. unfold Run.refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_openat : forall i m ret,
  bv_unsigned (in_sysno i) = 56%Z ->
  Run.refusal_b i m ret = Run.ret_in_errnos openat_errnos ret.
Proof. intros i m ret H. unfold Run.refusal_b. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)

Class AllocForced (SC : StepCfg) : Prop := alloc_forced : Run.sc_alloc the_scfg = false.
Class FsMayFail (SC : StepCfg) : Prop := fs_may_fail : Run.sc_fs the_scfg = true.

Global Instance hunspell_alloc_forced : AllocForced hunspell_scfg := eq_refl.
Global Instance hunspell_fs_may_fail : FsMayFail hunspell_scfg := eq_refl.

Section ScfgFacts.
  Context {SC : StepCfg}.

  Lemma family_off_openat_false {FM : FsMayFail SC} : forall i,
    bv_unsigned (in_sysno i) = 56%Z -> Run.injected_family_off the_scfg i = false.
  Proof. intros i H. rewrite (injected_family_off_openat _ _ H), fs_may_fail. reflexivity. Qed.

  Lemma not_spurious_openat {FM : FsMayFail SC} : forall i m eff,
    bv_unsigned (in_sysno i) = 56%Z -> ~ Run.spurious_refusal_cfg the_scfg i m eff.
  Proof.
    intros i m eff H. apply Run.spurious_refusal_family_on. apply family_off_openat_false. exact H.
  Qed.

  Lemma family_off_brk_true {AF : AllocForced SC} : forall i,
    bv_unsigned (in_sysno i) = 214%Z -> Run.injected_family_off the_scfg i = true.
  Proof. intros i H. rewrite (injected_family_off_brk _ _ H), alloc_forced. reflexivity. Qed.

  Lemma family_off_mmap_true {AF : AllocForced SC} : forall i,
    bv_unsigned (in_sysno i) = 222%Z -> Run.injected_family_off the_scfg i = true.
  Proof. intros i H. rewrite (injected_family_off_mmap _ _ H), alloc_forced. reflexivity. Qed.

  Lemma family_off_mprotect_true {AF : AllocForced SC} : forall i,
    bv_unsigned (in_sysno i) = 226%Z -> Run.injected_family_off the_scfg i = true.
  Proof. intros i H. rewrite (injected_family_off_mprotect _ _ H), alloc_forced. reflexivity. Qed.
End ScfgFacts.
