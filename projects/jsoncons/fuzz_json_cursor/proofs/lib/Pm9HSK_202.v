(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed HS_202; added T202_f, T202_t. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Pm9DefsK Pm9PlanK Pm9HSK_201.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* REGENERATED at 75d69e00, per CONFIG_RSEQ flag (_f: rz 0, _t: rz 1).  Computed by
   Rocq from Pm9PlanK's plans and solver, not pasted: the stored body is the normal
   form [Eval vm_compute] produced.  OLD: one literal per state, read off the
   pre-revision run. *)
Definition T202_f : list (nat * acs) := Eval vm_compute in solve 6 0 (HS_201 false) planK_201 [].
Definition T202_t : list (nat * acs) := Eval vm_compute in solve 6 1 (HS_201 true) planK_201 [].
Definition HS_202 (b : bool) : acs := if b then tget T202_t 202 else tget T202_f 202.
