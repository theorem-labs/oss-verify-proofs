(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x10ec78%Z (only parsing).
Notation RTLL := 0x10e9f0%Z (only parsing).
Notation RTD := 0xee920%Z (only parsing).
Notation RTP := 0xee9e8%Z (only parsing).
Notation RSYSINFO := 0x10ec60%Z (only parsing).
Notation RDEFSTACK := 0xdce90%Z (only parsing).
Notation RGOT_DYNAMIC := 0xdb730%Z (only parsing).
Notation RGOT_SSP := 0xdb8b0%Z (only parsing).
Notation RGUARD := 0x10ec58%Z (only parsing).
Notation RENVIRON := 0xee918%Z (only parsing).
Notation RPROGNAME := 0x10ec68%Z (only parsing).
Notation RHWCAP := 0x10ece0%Z (only parsing).
Notation RGOT3 := 0xdb888%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xc4aec);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xc4ae0); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xdcda0%Z (only parsing).
Notation RSTDOUT_BUF := 0x10f1d8%Z (only parsing).
Notation RSTDERR := 0xdccb0%Z (only parsing).
Notation F_STDOUT_WRITE := 0xc5318%Z (only parsing).
Notation F_STDIO_WRITE := 0xc4950%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x110000.
Definition STATIC_SPLIT : Z := 0xd5000.

Definition got_ssp := 0xdb8b0%Z.
Definition ssp_guard := 0x10ec58%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
