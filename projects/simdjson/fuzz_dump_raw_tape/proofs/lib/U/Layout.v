(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x10a648%Z (only parsing).
Notation RTLL := 0x10a3c0%Z (only parsing).
Notation RTD := 0xea2f0%Z (only parsing).
Notation RTP := 0xea3b8%Z (only parsing).
Notation RSYSINFO := 0x10a630%Z (only parsing).
Notation RDEFSTACK := 0xd8858%Z (only parsing).
Notation RGOT_DYNAMIC := 0xd70f0%Z (only parsing).
Notation RGOT_SSP := 0xd7278%Z (only parsing).
Notation RGUARD := 0x10a628%Z (only parsing).
Notation RENVIRON := 0xea2e8%Z (only parsing).
Notation RPROGNAME := 0x10a638%Z (only parsing).
Notation RHWCAP := 0x10a6b0%Z (only parsing).
Notation RGOT3 := 0xd7250%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xc04ac);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xc04a0); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xd8768%Z (only parsing).
Notation RSTDOUT_BUF := 0x10aba8%Z (only parsing).
Notation RSTDERR := 0xd8678%Z (only parsing).
Notation F_STDOUT_WRITE := 0xc0cd8%Z (only parsing).
Notation F_STDIO_WRITE := 0xc0310%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x10c000.
Definition STATIC_SPLIT : Z := 0xd1000.

Definition got_ssp := 0xd7278%Z.
Definition ssp_guard := 0x10a628%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
