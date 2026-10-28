(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0x5e2c40%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0xbfae90%Z (only parsing).    (* [comment removed for export] *)
Notation RLIBC := 0xbfb0e0%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x55d37c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x55d4c0); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x5e7348%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0xbfb968%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0x5e7168%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x55ec68%Z (only parsing).
Notation F_STDIO_WRITE := 0x55d4c8%Z (only parsing).

Definition GLOBALS_TOP : Z := 0xbfd000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x56b000.   (* [comment removed for export] *)

Definition got_ssp := 0x5e2c40%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xbfae90%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells bsegs m ssp_guard [C8 canary].
