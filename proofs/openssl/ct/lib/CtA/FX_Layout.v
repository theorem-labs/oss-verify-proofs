(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac. 
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0x5ab1e0%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0xbc9430%Z (only parsing).    (* [comment removed for export] *)
Notation RLIBC := 0xbc9680%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x525600);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x525744); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x5af608%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0xbc9f08%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0x5af428%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x526ca4%Z (only parsing).
Notation F_STDIO_WRITE := 0x52574c%Z (only parsing).

Definition GLOBALS_TOP : Z := 0xbcb000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x533000.   (* [comment removed for export] *)

Definition got_ssp := 0x5ab1e0%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0xbc9430%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells ctasegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells ctasegs m ssp_guard [C8 canary].
