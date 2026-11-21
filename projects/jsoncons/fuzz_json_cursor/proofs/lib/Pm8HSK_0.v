(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed HS_0. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Pm8DefsK Pm8PlanK Pm8HSK_201 Pm8HSK_202 Pm8HSK_1.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* REGENERATED at 75d69e00, per CONFIG_RSEQ flag (_f: rz 0, _t: rz 1).  Computed by
   Rocq from Pm8PlanK's plans and solver, not pasted: the stored body is the normal
   form [Eval vm_compute] produced.  OLD: one literal per state, read off the
   pre-revision run. *)
Definition HS_0 (b : bool) : acs := if b then tget TM_t 0 else tget TM_f 0.
