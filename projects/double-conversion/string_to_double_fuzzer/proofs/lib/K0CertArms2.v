(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms K0Defs K0TailDefs K0TailAll K0Arm_a00417 K0Arm_a00449 K0Arm_a00641 K0Arm_a00889 K0Arm_a00897 K0Arm_a01409 K0Arm_a01913 K0Arm_a01921.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a00417_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a00417 K0_C_W K0_HT_big 2 armf_a00417 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00449_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a00449 K0_C_W K0_HT_big 2 armf_a00449 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00641_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a00641 K0_C_W K0_HT_big 2 armf_a00641 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00889_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a00889 K0_C_W K0_HT_big 2 armf_a00889 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00897_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a00897 K0_C_W K0_HT_big 2 armf_a00897 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a01409_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a01409 K0_C_W K0_HT_big 2 armf_a01409 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a01913_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a01913 K0_C_W K0_HT_big 2 armf_a01913 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a01921_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a01921 K0_C_W K0_HT_big 2 armf_a01921 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
