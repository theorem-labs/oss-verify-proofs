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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
Import ListNotations.
Open Scope bv_scope.

Notation RGOT_SSP := 0x1c4a18%Z (only parsing).   (* [comment removed for export] *)
Notation RGUARD := 0x72c478%Z (only parsing).    (* [comment removed for export] *)
Notation RLIBC := 0x72c6c8%Z (only parsing).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x1ad258);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x1ad39c); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x1c8668%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x72cb48%Z (only parsing).  (* [comment removed for export] *)
Notation RSTDERR := 0x1c8578%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x1ae81c%Z (only parsing).
Notation F_STDIO_WRITE := 0x1ad3a4%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x72e000.   (* [comment removed for export] *)
Definition STATIC_SPLIT : Z := 0x1bd000.   (* [comment removed for export] *)

Definition got_ssp := 0x1c4a18%Z.     (* [comment removed for export] *)
Definition ssp_guard := 0x72c478%Z.   (* [comment removed for export] *)
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  ro_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ ro_cells asegs m ssp_guard [C8 canary].
