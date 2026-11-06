(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x2ec188%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x2ebdb0%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x2ebde8%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x2ebeb0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x2ec170%Z (only parsing).
Notation RDEFSTACK := 0x2d9260%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x2d7510%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x2d7af0%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x2ebf38%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x2ebda8%Z (only parsing).
Notation RPROGNAME := 0x2ec178%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x2ec1f0%Z (only parsing).
Notation RGOT3 := 0x2d7af8%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x26e8d8);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x26ea1c); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2d9170%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x2ec9e0%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x2d8f90%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x270430%Z (only parsing).
Notation F_STDIO_WRITE := 0x26f6c4%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x2ee000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x27b000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x2d7af0%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x2ebf38%Z. (* [comment removed for export] *)

