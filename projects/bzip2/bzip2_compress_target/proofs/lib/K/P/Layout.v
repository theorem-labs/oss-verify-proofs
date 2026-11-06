(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation psegs := Image.psegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x5a970%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x39f48%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x79808%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x798d0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x5a958%Z (only parsing).
Notation RDEFSTACK := 0x2a588%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x285f0%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x28678%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x5a950%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x3a610%Z (only parsing).
Notation RPROGNAME := 0x5a960%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x5a9d8%Z (only parsing).
Notation RGOT3 := 0x28650%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x21504);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x21648); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2a498%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x5b1b8%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x2a2b8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x22154%Z (only parsing).
Notation F_STDIO_WRITE := 0x21650%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x5c000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x28000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x28678%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x5a950%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells psegs m ssp_guard [C8 canary].
