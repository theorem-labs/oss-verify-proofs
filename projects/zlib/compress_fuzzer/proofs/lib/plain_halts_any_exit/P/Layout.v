(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := Image.psegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x5ab90%Z (only parsing).
Notation RTLL := 0x5a908%Z (only parsing).
Notation RTD := 0x3a838%Z (only parsing).
Notation RTP := 0x3a900%Z (only parsing).
Notation RSYSINFO := 0x5ab78%Z (only parsing).
Notation RDEFSTACK := 0x2a790%Z (only parsing).
Notation RGOT_DYNAMIC := 0x294f0%Z (only parsing).
Notation RGOT_SSP := 0x29570%Z (only parsing).
Notation RGUARD := 0x5ab70%Z (only parsing).
Notation RENVIRON := 0x3a830%Z (only parsing).
Notation RPROGNAME := 0x5ab80%Z (only parsing).
Notation RHWCAP := 0x5abf8%Z (only parsing).
Notation RGOT3 := 0x29548%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x22d40);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x22efc); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2a6a0%Z (only parsing).
Notation RSTDOUT_BUF := 0x5afd8%Z (only parsing).
Notation RSTDERR := 0x2a5b0%Z (only parsing).
Notation F_STDOUT_WRITE := 0x22f04%Z (only parsing).
Notation F_STDIO_WRITE := 0x22d6c%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x5c000.
Definition STATIC_SPLIT : Z := 0x29000.

Definition got_ssp := 0x29570%Z.
Definition ssp_guard := 0x5ab70%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
