(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0x3525a8%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0x352320%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0x332250%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0x332318%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0x352590%Z (only parsing).
Notation RDEFSTACK := 0x31f738%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x31d850%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x31de20%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x352358%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0x332248%Z (only parsing).
Notation RPROGNAME := 0x352598%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0x352610%Z (only parsing).
Notation RGOT3 := 0x31de28%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x2b5088);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x2b51cc); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x31f648%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x352e00%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x31f468%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x2b6924%Z (only parsing).
Notation F_STDIO_WRITE := 0x2b5e74%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0x354000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x2c1000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x31de20%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x352358%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
