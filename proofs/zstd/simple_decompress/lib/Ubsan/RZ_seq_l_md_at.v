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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition md_head (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c216 c224 c232 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (sn : Z) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) c216 c224 c232 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x18464) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition md_dec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c224 c232 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (sn : Z) (x1 x5 x7 x12 x13 x14 x15 x24 x28 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) ofs c224 c232 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) x7 (Z_to_bv 64 nOF) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) x12 x13 x14 x15 (Z_to_bv 64 mlv) (Z_to_bv 64 vLL) (Z_to_bv 64 sn) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x185f0) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition md_rl1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c232 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (sn : Z) (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) ofs (Z_to_bv 64 mlv) c232 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) x7 (Z_to_bv 64 nOF) (Z_to_bv 64 bLL) x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 vLL) (Z_to_bv 64 sn) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x18608) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition md_upd (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c232 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x1 x5 x7 x8 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) c232 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) x7 x8 x9 (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 llv) (Z_to_bv 64 sn) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x186f0) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition md_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 c232 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 ofs) (Z_to_bv 64 mlv) c232 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 llv) (Z_to_bv 64 sn) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x188c8) (y_fc P) None m1 (seg_rom usegs)).

