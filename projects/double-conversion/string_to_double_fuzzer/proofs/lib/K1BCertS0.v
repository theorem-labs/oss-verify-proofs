(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the segment into hand-off 105 is checked as K1BD0F.k1s0x_f, its forget lists recomputed in the build). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainHSBoth MainItabBoth PlanFormsBoth BK0TailAll K1BD0 K1BD0F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Lemma k1s0_ok : preb HS_main_both KCm BFUELm FUELm BITm TT_r5 0%nat (root_class 5 ++ [(QFlen, 65536, QMAX)]) [(105%nat, (1%nat, HS_hg1x))] 0%nat k1s0x_f = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
