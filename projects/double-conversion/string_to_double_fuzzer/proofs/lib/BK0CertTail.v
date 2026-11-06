(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0HS_jt BK0HS_jt2 BK0Defs BK0SegMc BK0TailP BK0JS_tail_pj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition K0_TAILP : plan := (tail_p JSraw_tail_pj_11).
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma seg_mcbf_ok : segb KCm BFUELm FUELm BITm TT HS_jt K0_C_W K0_HT_mc 3 seg_mcbf = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma tail_p_ok : payb KCm BFUELm FUELm BITm TT HS_jt2 K0_C_W 3 K0_TAILP = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
End TTS.
