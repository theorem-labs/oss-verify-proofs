(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import ImageA.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0xcd4a8%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x629b08%Z (only parsing).    (* [comment removed for export] *)
Notation RLIBC := 0x629d58%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xbe43c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0xbe580); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0xd0f98%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x62a1d8%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0xd0ea8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0xbf208%Z (only parsing).
Notation F_STDIO_WRITE := 0xbe588%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x62c000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0xc9000.   (* [comment removed for export] *)

Definition got_ssp := 0xcd4a8%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x629b08%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells asegs m ssp_guard [C8 canary].
