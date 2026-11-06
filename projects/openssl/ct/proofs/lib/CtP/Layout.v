(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation ctpsegs := ImageCt.ctpsegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x30d978%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x30d6f0%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x2ed620%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x2ed6e8%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x30d960%Z (only parsing).
Notation RDEFSTACK := 0x2dab00%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x2d8da8%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x2d9390%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x30d728%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x2ed618%Z (only parsing).
Notation RPROGNAME := 0x30d968%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x30d9e0%Z (only parsing).
Notation RGOT3 := 0x2d9398%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2703bc);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x270500); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2daa10%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x30e1d0%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x2da830%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x271c58%Z (only parsing).
Notation F_STDIO_WRITE := 0x2711a8%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x30f000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x27d000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x2d9390%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x30d728%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells ctpsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells ctpsegs m ssp_guard [C8 canary].
