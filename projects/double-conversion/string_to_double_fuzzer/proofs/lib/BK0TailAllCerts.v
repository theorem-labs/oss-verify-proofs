(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth AsanTailAlist BothTailTab BK0TailDefs BK0BTailDefs BK1TailDefs BR4TailDefs BK0ETailDefs BK0TailAll BK0TailCerts BK0BTailCerts BK1TailCerts BR4TailCerts BK0ETailCerts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Lemma TT_r5_ok : tails_all_ok KCm BFUELm FUELm BITm TT_r5.
Proof. unfold TT_r5, AL_r5. apply tails_all_ok_alist_app; [exact AL_k0_ok | apply tails_all_ok_alist_app; [exact AL_k0b_ok | apply tails_all_ok_alist_app; [exact AL_k1_ok | apply tails_all_ok_alist_app; [exact AL_r4_ok | exact AL_k0e_ok]]]]. Qed.
