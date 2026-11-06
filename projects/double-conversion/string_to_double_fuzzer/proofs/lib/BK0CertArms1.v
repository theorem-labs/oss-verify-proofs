(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0Defs BK0TailDefs BK0TailAll BK0Arm_a00193 BK0Arm_a00225 BK0Arm_a00257 BK0Arm_a00289 BK0Arm_a00321 BK0Arm_a00353 BK0Arm_a00385 BK0Arm_a00417 BK0Arm_a00449.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a00193_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00193 K0_C_W K0_HT_big 2 armf_a00193 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00225_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00225 K0_C_W K0_HT_big 2 armf_a00225 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00257_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00257 K0_C_W K0_HT_big 2 armf_a00257 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00289_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00289 K0_C_W K0_HT_big 2 armf_a00289 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00321_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00321 K0_C_W K0_HT_big 2 armf_a00321 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00353_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00353 K0_C_W K0_HT_big 2 armf_a00353 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00385_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00385 K0_C_W K0_HT_big 2 armf_a00385 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00417_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00417 K0_C_W K0_HT_big 2 armf_a00417 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00449_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00449 K0_C_W K0_HT_big 2 armf_a00449 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
