(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Bytes.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import ITree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Monad.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Stdio.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_memset_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Notation z64 := (Z_to_bv 64 0).   (* [comment removed for export] *)

Notation rsegs := F_memset_u5.rsegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x1786c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x17a28); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 z64;
   CB 80 tail].

Notation RSTDOUT := 0x234e8%Z (only parsing).       (* [comment removed for export] *)
Notation RSTDOUT_BUF := 0x23c40%Z (only parsing).   (* [comment removed for export] *)
Notation RSTDERR := 0x233f8%Z (only parsing).       (* [comment removed for export] *)
Notation F_STDOUT_WRITE := 0x1c4b0%Z (only parsing).
Notation F_STDIO_WRITE := 0x17898%Z (only parsing).

(* [comment removed for export] *)
Definition stdout_file (m : word -> option byte) (so : stdout_st) : Prop :=
  exists (flags mode : word) (tail bufbytes : list byte),
    rw_cells rsegs m RSTDOUT
      (file_cells flags
         (if so_active so then RSTDOUT_BUF + 1024 else 0)%Z
         (if so_active so then RSTDOUT_BUF + zlength (so_buf so) else 0)%Z
         (if so_active so then RSTDOUT_BUF else 0)%Z
         (if so_first so then F_STDOUT_WRITE else F_STDIO_WRITE)
         RSTDOUT_BUF 1024 1 mode
         (if so_lbf_nl so then 10 else 0xffffffff)%Z tail)
    /\ Z.land (bv_unsigned flags) 72 = 0%Z
    /\ rw_cells rsegs m RSTDOUT_BUF [CB 1024 bufbytes]
    /\ firstn (length (so_buf so)) bufbytes = to_bytes (so_buf so)
    /\ (zlength (so_buf so) <= 1024)%Z
    /\ (so_active so = false -> so_buf so = []).

(* [comment removed for export] *)
Definition stderr_file (m : word -> option byte) : Prop :=
  exists (flags mode : word) (e wend : Z) (tail : list byte),
    rw_cells rsegs m RSTDERR (file_cells flags wend e e F_STDIO_WRITE 0x23c38 0 2 mode 0xffffffff tail).

