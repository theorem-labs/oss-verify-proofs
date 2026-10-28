(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x350bf8%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x350970%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x3308a0%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x330968%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x350be0%Z (only parsing).
Notation RDEFSTACK := 0x31dd80%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x31be98%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x31c468%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x3509a8%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x330898%Z (only parsing).
Notation RPROGNAME := 0x350be8%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x350c60%Z (only parsing).
Notation RGOT3 := 0x31c470%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2b36cc);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2b3810); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x31dc90%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x351450%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x31dab0%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x2b4f68%Z (only parsing).
Notation F_STDIO_WRITE := 0x2b44b8%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x353000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x2c0000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x31c468%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x3509a8%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
