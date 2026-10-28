(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqs_at_err (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= v_CAP P ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c6fc) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition seqs_at_lexit (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP <= OEND ->
  LLO <= LP <= LEND ->
  0 <= bc < 2^31 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c664) (v_fc P) None m1 (seg_rom usegs)).

