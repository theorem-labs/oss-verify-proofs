(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from HS2Both.v as in the LPS 727298f3 update: the S2 hand-off table S2T_1a, from S1 hand-off 0 at CONFIG_RSEQ value 1, computed in the build in one run of the check, in a file of its own so the four tables build in parallel. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import HS2BothD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the hand-off table from S1 hand-off 0 (a) at CONFIG_RSEQ value 1 *)
Definition S2T_1a : list (nat * acs) := Eval vm_compute in collect_handoffs1 10 (s2_coll 1 0) [].
