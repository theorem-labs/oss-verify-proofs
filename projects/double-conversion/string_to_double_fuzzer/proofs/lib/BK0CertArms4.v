(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0Defs BK0TailDefs BK0TailAll BK0Arm_a48129 BK0Arm_a64505.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma armf_a48129_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a48129 K0_C_W K0_HT_big 2 armf_a48129 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma armf_a64505_ok : segb KCm BFUELm FUELm BITm TT_r5 K0_ST_a64505 K0_C_W K0_HT_big 2 armf_a64505 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
