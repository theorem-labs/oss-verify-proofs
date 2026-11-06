(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0xb4fb0%Z (only parsing).
Notation RTLL := 0xb4d28%Z (only parsing).
Notation RTD := 0x94c58%Z (only parsing).
Notation RTP := 0x94d20%Z (only parsing).
Notation RSYSINFO := 0xb4f98%Z (only parsing).
Notation RDEFSTACK := 0x84088%Z (only parsing).
Notation RGOT_DYNAMIC := 0x829c8%Z (only parsing).
Notation RGOT_SSP := 0x82b28%Z (only parsing).
Notation RGUARD := 0xb4f90%Z (only parsing).
Notation RENVIRON := 0x94c50%Z (only parsing).
Notation RPROGNAME := 0xb4fa0%Z (only parsing).
Notation RHWCAP := 0xb5018%Z (only parsing).
Notation RGOT3 := 0x82b00%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x72bdc);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x72d98); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x83f98%Z (only parsing).
Notation RSTDOUT_BUF := 0xb53f8%Z (only parsing).
Notation RSTDERR := 0x83ea8%Z (only parsing).
Notation F_STDOUT_WRITE := 0x72da0%Z (only parsing).
Notation F_STDIO_WRITE := 0x72c08%Z (only parsing).

Definition GLOBALS_TOP : Z := 0xb6000.
Definition STATIC_SPLIT : Z := 0x7f000.

Definition got_ssp := 0x82b28%Z.
Definition ssp_guard := 0xb4f90%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
