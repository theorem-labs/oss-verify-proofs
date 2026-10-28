(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x10f818%Z (only parsing).
Notation RTLL := 0x10f590%Z (only parsing).
Notation RTD := 0xef4c0%Z (only parsing).
Notation RTP := 0xef588%Z (only parsing).
Notation RSYSINFO := 0x10f800%Z (only parsing).
Notation RDEFSTACK := 0xdda30%Z (only parsing).
Notation RGOT_DYNAMIC := 0xdc2b0%Z (only parsing).
Notation RGOT_SSP := 0xdc448%Z (only parsing).
Notation RGUARD := 0x10f7f8%Z (only parsing).
Notation RENVIRON := 0xef4b8%Z (only parsing).
Notation RPROGNAME := 0x10f808%Z (only parsing).
Notation RHWCAP := 0x10f880%Z (only parsing).
Notation RGOT3 := 0xdc420%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xc535c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xc5350); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xdd940%Z (only parsing).
Notation RSTDOUT_BUF := 0x10fd78%Z (only parsing).
Notation RSTDERR := 0xdd850%Z (only parsing).
Notation F_STDOUT_WRITE := 0xc5b88%Z (only parsing).
Notation F_STDIO_WRITE := 0xc51c0%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x111000.
Definition STATIC_SPLIT : Z := 0xd6000.

Definition got_ssp := 0xdc448%Z.
Definition ssp_guard := 0x10f7f8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
