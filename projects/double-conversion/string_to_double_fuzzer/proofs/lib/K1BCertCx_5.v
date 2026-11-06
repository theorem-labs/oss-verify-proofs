(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth K1BTpl K1BDx_1 K1BDx_2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Section TTS.
Variable TT : nat -> option (acs * plan * shape).
Lemma k1r1x_ok : segb KCm BFUELm FUELm BITm TT HS_hr1x (root_class 5 ++ [(QFlen, 131072, QMAX)]) [(108%nat, (1%nat, HS_hg2x))] 1%nat (k1r1x) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End TTS.
