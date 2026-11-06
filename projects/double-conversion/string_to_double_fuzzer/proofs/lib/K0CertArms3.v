(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms K0Defs K0TailDefs K0TailAll K0Arm_a02945 K0Arm_a03961 K0Arm_a03969 K0Arm_a04096 K0Arm_a04097 K0Arm_a07937 K0Arm_a12033 K0Arm_a16121.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a02945_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a02945 K0_C_W K0_HT_big 2 armf_a02945 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a03961_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a03961 K0_C_W K0_HT_big 2 armf_a03961 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a03969_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a03969 K0_C_W K0_HT_big 2 armf_a03969 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a04096_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a04096 K0_C_W K0_HT_big 2 armf_a04096 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a04097_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a04097 K0_C_W K0_HT_big 2 armf_a04097 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a07937_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a07937 K0_C_W K0_HT_big 2 armf_a07937 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a12033_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a12033 K0_C_W K0_HT_big 2 armf_a12033 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a16121_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a16121 K0_C_W K0_HT_big 2 armf_a16121 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
