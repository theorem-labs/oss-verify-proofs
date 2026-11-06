(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0Defs BK0TailDefs BK0TailAll BK0Arm_a00001 BK0Arm_a00008 BK0Arm_a00009 BK0Arm_a00017 BK0Arm_a00049 BK0Arm_a00065 BK0Arm_a00097 BK0Arm_a00129 BK0Arm_a00161.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a00001_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00001 K0_C_W K0_HT_quick 2 armf_a00001 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00008_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00008 K0_C_W K0_HT_quick 2 armf_a00008 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00009_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00009 K0_C_W K0_HT_quick 2 armf_a00009 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00017_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00017 K0_C_W K0_HT_quick 2 armf_a00017 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00049_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00049 K0_C_W K0_HT_quick 2 armf_a00049 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00065_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00065 K0_C_W K0_HT_big 2 armf_a00065 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00097_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00097 K0_C_W K0_HT_big 2 armf_a00097 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00129_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00129 K0_C_W K0_HT_big 2 armf_a00129 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a00161_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a00161 K0_C_W K0_HT_big 2 armf_a00161 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
