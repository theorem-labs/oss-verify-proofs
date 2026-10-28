(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation ctusegs := ImageCt.ctusegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x3534b8%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x353230%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x333160%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x333228%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x3534a0%Z (only parsing).
Notation RDEFSTACK := 0x320640%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x31e750%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x31ed28%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x353268%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x333158%Z (only parsing).
Notation RPROGNAME := 0x3534a8%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x353520%Z (only parsing).
Notation RGOT3 := 0x31ed30%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2b5f18);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2b605c); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x320550%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x353d10%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x320370%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x2b77b4%Z (only parsing).
Notation F_STDIO_WRITE := 0x2b6d04%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x355000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x2c2000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x31ed28%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x353268%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells ctusegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells ctusegs m ssp_guard [C8 canary].
