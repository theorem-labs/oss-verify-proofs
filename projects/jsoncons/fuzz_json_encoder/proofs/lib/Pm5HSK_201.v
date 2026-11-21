(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed HS_201; added T201_f, T201_t; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm9HSK_201.v, lines 5-8, 13-19. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK Pm5DefsK Pm5PlanK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* REGENERATED at 75d69e00, per CONFIG_RSEQ flag (_f: rz 0, _t: rz 1).  Computed by
   Rocq from Pm5PlanK's plans and solver, not pasted: the stored body is the normal
   form [Eval vm_compute] produced.  OLD: one literal per state, read off the
   pre-revision run. *)
Definition T201_f : list (nat * acs) := Eval vm_compute in solve 6 0 (asan0_init 0) planK_root [].
Definition T201_t : list (nat * acs) := Eval vm_compute in solve 6 1 (asan0_init 1) planK_root [].
Definition HS_201 (b : bool) : acs := if b then tget T201_t 201 else tget T201_f 201.
