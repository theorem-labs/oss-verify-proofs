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

Notation psegs := Image.psegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0xa9a40%Z (only parsing).
Notation RTLL := 0xa97b8%Z (only parsing).
Notation RTD := 0x896e8%Z (only parsing).
Notation RTP := 0x897b0%Z (only parsing).
Notation RSYSINFO := 0xa9a28%Z (only parsing).
Notation RDEFSTACK := 0x78b18%Z (only parsing).
Notation RGOT_DYNAMIC := 0x77760%Z (only parsing).
Notation RGOT_SSP := 0x778b8%Z (only parsing).
Notation RGUARD := 0xa9a20%Z (only parsing).
Notation RENVIRON := 0x896e0%Z (only parsing).
Notation RPROGNAME := 0xa9a30%Z (only parsing).
Notation RHWCAP := 0xa9aa8%Z (only parsing).
Notation RGOT3 := 0x77890%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x67974);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x67b30); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x78a28%Z (only parsing).
Notation RSTDOUT_BUF := 0xa9e88%Z (only parsing).
Notation RSTDERR := 0x78938%Z (only parsing).
Notation F_STDOUT_WRITE := 0x67b38%Z (only parsing).
Notation F_STDIO_WRITE := 0x679a0%Z (only parsing).

Definition GLOBALS_TOP : Z := 0xab000.
Definition STATIC_SPLIT : Z := 0x74000.

Definition got_ssp := 0x778b8%Z.
Definition ssp_guard := 0xa9a20%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
