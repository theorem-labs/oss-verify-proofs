(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac nlstep :=
  zstep; nnorm;
  match goal with |- context [Z_to_le_bytes 8 ?lit] => change (Z_to_le_bytes 8 lit) with (le8 (Z_to_bv 64 lit)) end;
  mem_after_store_fast.
Ltac ngstep_l := first [ gguard | nstep | nlstep ].
