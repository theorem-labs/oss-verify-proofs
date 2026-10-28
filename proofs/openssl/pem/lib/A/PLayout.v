(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation asegs := ImageA.asegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0xbc4180%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0xbc3ef8%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0xba3e28%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0xba3ef0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0xbc4168%Z (only parsing).
Notation RDEFSTACK := 0x5aaa38%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x5a4560%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x5a6518%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0xbc3f30%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0xba3e20%Z (only parsing).
Notation RPROGNAME := 0xbc4170%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0xbc41e8%Z (only parsing).
Notation RGOT3 := 0x5a6520%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x520a34);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x520b78); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x5aa948%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0xbc4a08%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x5aa768%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x5220d8%Z (only parsing).
Notation F_STDIO_WRITE := 0x520b80%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0xbc6000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x52e000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x5a6518%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xbc3f30%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].
