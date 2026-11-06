(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation bsegs := ImageA.bsegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation RGP := 0x10800%Z (only parsing).        (* [comment removed for export] *)
Notation RLIBC := 0xbf6980%Z (only parsing).      (* [comment removed for export] *)
Notation RTLL := 0xbf66f8%Z (only parsing).       (* [comment removed for export] *)
Notation RTD := 0xbd6628%Z (only parsing).        (* [comment removed for export] *)
Notation RTP := 0xbd66f0%Z (only parsing).        (* [comment removed for export] *)
Notation RSYSINFO := 0xbf6968%Z (only parsing).
Notation RDEFSTACK := 0x5e2f78%Z (only parsing).  (* [comment removed for export] *)
Notation RGOT_DYNAMIC := 0x5dc7e0%Z (only parsing). (* [comment removed for export] *)
Notation RGOT_SSP := 0x5de7a0%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0xbf6730%Z (only parsing).     (* [comment removed for export] *)
Notation RENVIRON := 0xbd6620%Z (only parsing).
Notation RPROGNAME := 0xbf6970%Z (only parsing).   (* [comment removed for export] *)
Notation RHWCAP := 0xbf69e8%Z (only parsing).
Notation RGOT3 := 0x5de7a8%Z (only parsing).       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x559130);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x559274); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x5e2e88%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0xbf7208%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x5e2ca8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x55a7d4%Z (only parsing).
Notation F_STDIO_WRITE := 0x55927c%Z (only parsing).

(* [comment removed for export] *)
Definition GLOBALS_TOP : Z := 0xbf8000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x566000.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x5de7a0%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xbf6730%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m ssp_guard [C8 canary].
