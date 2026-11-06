(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqs_at_err (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= v_CAP P ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 r) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a5ec) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition seqs_at_lexit (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP <= OEND ->
  LLO <= LP <= LEND ->
  0 <= bc < 2^31 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 18446744073709551596) x21 x22 (Z_to_bv 64 OEND) x24 (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a598) (v_fc P) None m1 (seg_rom psegs)).

