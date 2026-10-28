(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0x16f508%Z (only parsing).
Notation RGUARD := 0x6cbe28%Z (only parsing).
Notation RLIBC := 0x6cc078%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x157594);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x1576d8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x173420%Z (only parsing).
Notation RSTDOUT_BUF := 0x6cc608%Z (only parsing).
Notation RSTDERR := 0x173330%Z (only parsing).
Notation F_STDOUT_WRITE := 0x1583cc%Z (only parsing).
Notation F_STDIO_WRITE := 0x1576e0%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x6ce000.
Definition STATIC_SPLIT : Z := 0x168000.

Definition got_ssp := 0x16f508%Z.
Definition ssp_guard := 0x6cbe28%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells bsegs m ssp_guard [C8 canary].
