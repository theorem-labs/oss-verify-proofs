(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_memsetw.v, with its module paths, module names and addresses changed; 560 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg.asan by symbol + offset pairing (port_addr_check 5033540ba83b predict mode; boxreg's interceptor and runtime code is instruction-for-instruction fuzz_reply's modulo numerals): 8 address numeral(s) rewritten, module paths changed. *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/I_memsetw.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; 8 fuzz_state.asan address numerals moved to
   fuzz_reply.asan (1 code, 7 data cell), each paired by code (instruction by instruction, pc-relative
   fields masked) or, for a data cell, by the auipc pair that loads it (table: lib/A/RT_gxa_mem_Tbl.v); 1 geometry
   constants kept. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.Lib Require Import Tac ImageA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz.A Require Import R_small.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition icells_ms (m : mem) : Prop :=
  ro_cells asegs m 0x98eb8 [C8 (Z_to_bv 64 0xa0f78)]            (* [comment removed for export] *)
  /\ ro_cells asegs m 0x99a20 [C8 (Z_to_bv 64 0xa1c59)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0x9ad28 [C8 (Z_to_bv 64 0x92588)]         (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa0f78 [C8 (Z_to_bv 64 0x7fff8000)]      (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa1c59 [C1 (Z_to_bv 8 1)].              (* [comment removed for export] *)
