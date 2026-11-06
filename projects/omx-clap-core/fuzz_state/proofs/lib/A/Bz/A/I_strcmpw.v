(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/simdjson/fuzz_element/lib/BA/R_strncasecmp.v, with its module paths and addresses changed; 4 of its 22 lines of code are new or changed and 651 lines of the source are left out. *)
(* copied by path from a working branch 51f06361767: its first 25 lines (to icells_sc); the 289 lines after them, definitions and lemmas nothing here uses, are removed *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition icells_sc (m : mem) : Prop :=
  ro_cells asegs m 0x9f6e0 [C8 (Z_to_bv 64 0x139a68)]
  /\ ro_cells asegs m 0x9f6f0 [C8 (Z_to_bv 64 0xa7f38)]
  /\ ro_cells asegs m 0xa7f38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xa8c18 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x139b5d [C1 (Z_to_bv 8 0)].
