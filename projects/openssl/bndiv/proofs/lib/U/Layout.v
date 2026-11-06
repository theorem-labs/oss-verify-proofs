(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x352d28%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x352aa0%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x3329d0%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x332a98%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x352d10%Z (only parsing).
Notation RDEFSTACK := 0x31fe80%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x31df98%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x31e568%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x352ad8%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x3329c8%Z (only parsing).
Notation RPROGNAME := 0x352d18%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x352d90%Z (only parsing).
Notation RGOT3 := 0x31e570%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2b5514);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2b5658); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x31fd90%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x353580%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x31fbb0%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x2b706c%Z (only parsing).
Notation F_STDIO_WRITE := 0x2b6300%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x355000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x2c2000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x31e568%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x352ad8%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
