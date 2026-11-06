(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK
  SymExec3 SymPlan UbSymPlanSoundA UbTargetEntry_defs UbTargetEntryK_defs
  UbTargetShape UbTargetShapeTop UbTargetAssembly UbTargetCover.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbTargetAssemblyTop UbTPBc_g08.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma cso_k0_0_0 : class_shape_ok false s_k0_0_0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_0_0 : TP0 0 0.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound 20000 400 0 0 p_k0_0_0 s_k0_0_0 chk_k0_0_0 cso_k0_0_0); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_36845_37436 : class_shape_ok1 true s_k1_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_36845_37436 : TPK 1 36845 37436.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 36845 37436 p_k1_36845_37436 s_k1_36845_37436 chk_k1_36845_37436 cso_k1_36845_37436); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_52413_53228 : class_shape_ok1 true s_k1_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_52413_53228 : TPK 1 52413 53228.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 1 20000 400 52413 53228 p_k1_52413_53228 s_k1_52413_53228 chk_k1_52413_53228 cso_k1_52413_53228); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_104829_106476 : class_shape_ok1 true s_k2_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_104829_106476 : TPK 2 104829 106476.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k 2 20000 400 104829 106476 p_k2_104829_106476 s_k2_104829_106476 chk_k2_104829_106476 cso_k2_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

