(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cr.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := X1cr.psegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x661c8%Z (only parsing).
Notation RTLL := 0x65f48%Z (only parsing).
Notation RTD := 0x2e78c%Z (only parsing).
Notation RTP := 0x2e854%Z (only parsing).
Notation RSYSINFO := 0x661b0%Z (only parsing).
Notation RDEFSTACK := 0x35de0%Z (only parsing).
Notation RGOT_DYNAMIC := 0x34ad8%Z (only parsing).
Notation RGOT_SSP := 0x34bc0%Z (only parsing).
Notation RGUARD := 0x661a8%Z (only parsing).
Notation RENVIRON := 0x45e70%Z (only parsing).
Notation RPROGNAME := 0x661b8%Z (only parsing).
Notation RHWCAP := 0x66230%Z (only parsing).
Notation RGOT3 := 0x34b98%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
[C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2da28);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2dbe4); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
CB 80 tail].

Notation RSTDOUT := 0x35cf0%Z (only parsing).
Notation RSTDOUT_BUF := 0x66610%Z (only parsing).
Notation RSTDERR := 0x35c00%Z (only parsing).
Notation F_STDOUT_WRITE := 0x2dbec%Z (only parsing).
Notation F_STDIO_WRITE := 0x2da54%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x67000.
Definition STATIC_SPLIT : Z := 0x34000.

Definition got_ssp := 0x34bc0%Z.
Definition ssp_guard := 0x661a8%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
