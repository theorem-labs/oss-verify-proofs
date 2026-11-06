(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Class StepCfg := { the_scfg : Run.SpuriousCfg }.

Global Instance hunspell_scfg : StepCfg :=
  {| the_scfg := Run.mkSpuriousCfg false true true true true true |}.

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run0bInjectedArm37Corelib4Init9Datatypesj94Nonej96option37Corelib4Init5Logicm12eq0cinjected_armj94boolj95false37Corelib7Numbers7BinNumsp74Npos0bSpuriousCfg0h3injected_family_off3h5LinuxProcessSemanticsfLinuxProcessSem5StatetacSyscallInputta8in_sysno35stdpp9bitvectorbdefinitionshi2bbv_unsignedm13not0h4spurious_refusal_cfgta5ModeltadSyscallEffectj94negbp71Z05sc_fs08sc_alloc09refusal_bta6ENOMEMta9errno_ret3h5LinuxProcessSemantics5Riscv7Preludehrf6bv_eqbhi22bv0dbrk_refusal_bta6in_arg" s.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma injected_arm_none_66 : ltac2:(zQ "50!ic!l1!l8!n5!na@3$3@1$2$0@1$4+k2@1$1$0").   Proof. reflexivity. Qed. (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma injected_arm_none_96 : ltac2:(zQ "50!ic!l1!l8!n5!na@3$3@1$2$0@1$4+m0@1$1$0").   Proof. reflexivity. Qed. (* [comment removed for export] *)
Lemma injected_arm_none_215 : ltac2:(zQ "50!ic!l1!l8!n5!na@3$3@1$2$0@1$4+t7@1$1$0"). Proof. reflexivity. Qed. (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma injected_family_off_none : ltac2:(zQ "d0!n5!ic!l1!o8!of!l8!r0!r7!na!s4!hg8!hh7!hjf>3cfg$7>1i$a>0@3$0@1$5$1@1$8@2$c@1$6#k0@1$b^1@1$2$1@3$0$3@2$9^3^2$4").
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma not_spurious_none : ltac2:(zQ "e0!ic!l1!l8!n5!hke!r0!r7!na!hl4!hmb!hn3!hg8!hh7!hjf>3cfg$6>1i$b>1m$9>3eff$a>0@3$3@1$2$0@1$7@2$d@1$5#k0@1$c^3@1$1$0@1$4@4$8^5^4^3^2").
Proof.
  intros cfg i m eff H. apply Run.spurious_refusal_family_on.
  apply injected_family_off_none. exact H.
Qed.

(* [comment removed for export] *)
Lemma injected_family_off_openat : ltac2:(zQ "b0!n5!o8!ho3!r0!hoa!r7!s4!hoe!hg8!hh7!hjf>3cfg$5>1i$8>0@3$0$4@2$a@1$3#k0@1$9^1+j8@3$0$1@2$6^3^2@1$2@1$7^3").
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_brk : ltac2:(zQ "b0!n5!o8!ho3!r0!hoa!r7!s4!hp5!hg8!hh7!hjf>3cfg$5>1i$8>0@3$0$4@2$a@1$3#k0@1$9^1+t6@3$0$1@2$6^3^2@1$2@1$7^3").
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_mmap : ltac2:(zQ "b0!n5!o8!ho3!r0!hoa!r7!s4!hp5!hg8!hh7!hjf>3cfg$5>1i$8>0@3$0$4@2$a@1$3#k0@1$9^1+te@3$0$1@2$6^3^2@1$2@1$7^3").
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_mprotect : ltac2:(zQ "b0!n5!o8!ho3!r0!hoa!r7!s4!hp5!hg8!hh7!hjf>3cfg$5>1i$8>0@3$0$4@2$a@1$3#k0@1$9^1+u2@3$0$1@2$6^3^2@1$2@1$7^3").
Proof. intros cfg i H. unfold Run.injected_family_off. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma refusal_b_mmap : ltac2:(zQ "d0!r0!n5!o8!hoa!hpf!hqa!hmb!hg8!hr3!hh7!hu5!huf!hjf>1i$7>1m$6>3ret@1$b@1$0#k0>0@3$1$3@2$c@1$0#k0@1$9^3+te@3$1$2@3$4^4^3^2@3$a@1$0#k0^2@1$8$5").
Proof.
  intros i m ret H. unfold Run.refusal_b. rewrite H. cbn. rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma refusal_b_mprotect : ltac2:(zQ "d0!r0!n5!o8!hoa!hpf!hqa!hmb!hg8!hr3!hh7!hu5!huf!hjf>1i$7>1m$6>3ret@1$b@1$0#k0>0@3$1$3@2$c@1$0#k0@1$9^3+u2@3$1$2@3$4^4^3^2@3$a@1$0#k0^2@1$8$5").
Proof.
  intros i m ret H. unfold Run.refusal_b. rewrite H. cbn. rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma refusal_b_brk : ltac2:(zQ "c0!n5!r0!o8!hoa!hv5!hpf!hmb!hg8!ig4!hh7!huf!hjf>1i$7>1m$6>3ret@1$a@1$1#k0>0@3$0$3@2$b@1$1#k0@1$9^3+t6@3$0$2@3$5^4^3^2@3$4^3@2$8^4N0^2").
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
(* [comment removed for export] *)
