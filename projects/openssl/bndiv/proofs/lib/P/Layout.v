(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := Image.psegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x30c148%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x30bec0%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x2ebdf0%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x2ebeb8%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x30c130%Z (only parsing).
Notation RDEFSTACK := 0x2d92a8%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x2d7558%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x2d7b38%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x30bef8%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x2ebde8%Z (only parsing).
Notation RPROGNAME := 0x30c138%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x30c1b0%Z (only parsing).
Notation RGOT3 := 0x2d7b40%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x26e924);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x26ea68); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2d91b8%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x30c9a0%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x2d8fd8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x27047c%Z (only parsing).
Notation F_STDIO_WRITE := 0x26f710%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x30e000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x27b000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x2d7b38%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x30bef8%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
