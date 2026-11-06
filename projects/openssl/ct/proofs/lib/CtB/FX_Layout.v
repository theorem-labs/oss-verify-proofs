(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac. 
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0x5e3ae8%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0xbfc270%Z (only parsing).    (* [comment removed for export] *)
Notation RLIBC := 0xbfc4c0%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x55e384);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x55e4c8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x5e81c8%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0xbfcd48%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0x5e7fe8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x55fa28%Z (only parsing).
Notation F_STDIO_WRITE := 0x55e4d0%Z (only parsing).

Definition GLOBALS_TOP : Z := 0xbfe000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x56c000.   (* [comment removed for export] *)

Definition got_ssp := 0x5e3ae8%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xbfc270%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells ctbsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells ctbsegs m ssp_guard [C8 canary].
