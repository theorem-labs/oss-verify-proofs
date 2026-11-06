(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs AsanMain MainItab PlanForms K0Defs K0TailDefs K0TailAll K0Arm_a16129 K0Arm_a24065 K0Arm_a32249 K0Arm_a32257 K0Arm_a48129 K0Arm_a64505.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a16129_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a16129 K0_C_W K0_HT_big 2 armf_a16129 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a24065_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a24065 K0_C_W K0_HT_big 2 armf_a24065 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a32249_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a32249 K0_C_W K0_HT_big 2 armf_a32249 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a32257_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a32257 K0_C_W K0_HT_big 2 armf_a32257 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a48129_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a48129 K0_C_W K0_HT_big 2 armf_a48129 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a64505_ok : segb KCm BFUELm FUELm ITm TT_r5 K0_ST_a64505 K0_C_W K0_HT_big 2 armf_a64505 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
