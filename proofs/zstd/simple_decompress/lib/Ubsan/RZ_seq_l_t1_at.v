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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition t1_brk (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  LEND < LP + llv ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) x7 x8 x9 x10 (Z_to_bv 64 LEND) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 raddr) (Z_to_bv 64 (24 * cidx)) (Z_to_bv 64 LP) (Z_to_bv 64 llv) x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18928) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition t1_sw0 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (OP : Z) (llv mlv ofs : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 : word),
  seql_linv P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0 m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro (y_DCTX P + 30372) ->
  seql_lfacts P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) (100 + 100 * (y_nbSeq P - K) + 90) OP (y_DCTX P + 30372) bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 < llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 raddr) (Z_to_bv 64 (24 * cidx)) x21 (Z_to_bv 64 llv) x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18b34) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition t1_sw (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs lft : Z) (sn cidx dll dml dof raddr : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  OP + lft <= OEND ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  llv = rl cidx ->
  mlv = rm cidx ->
  ofs = ro cidx ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 lft) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 raddr) (Z_to_bv 64 (24 * cidx)) x21 x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18950) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
