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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition md_head (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c152 c160 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (sn : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 sn) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 (Z_to_bv 64 2)) (y_F P) (Z_to_bv 64 0x17d58) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition md_dec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c152 c160 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (sn : Z) (x1 x6 x7 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) (Z_to_bv 64 aOF) x6 x7 (Z_to_bv 64 mlv) ofs (Z_to_bv 64 nML) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bML) (Z_to_bv 64 bOF) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) (Z_to_bv 64 aML) (Z_to_bv 64 vLL) x19 (Z_to_bv 64 sn) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 (Z_to_bv 64 2)) (y_F P) (Z_to_bv 64 0x17e14) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition md_rl1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c152 c160 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (sn : Z) (x1 x5 x6 x7 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 mlv) ofs (Z_to_bv 64 nML) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bML) (Z_to_bv 64 bOF) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) x17 (Z_to_bv 64 vLL) x19 (Z_to_bv 64 sn) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 (Z_to_bv 64 2)) (y_F P) (Z_to_bv 64 0x17e28) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition md_upd (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c152 c160 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x1 x5 x6 x7 x10 x11 x12 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 (Z_to_bv 64 bc) x14 x15 x16 x17 (Z_to_bv 64 llv) x19 (Z_to_bv 64 sn) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 (Z_to_bv 64 2)) (y_F P) (Z_to_bv 64 0x17ed0) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition md_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c152 c160 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs : Z) (sn : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  sn = y_nbSeq P - K ->
  seql_ring_ok 8 rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 llv) x19 (Z_to_bv 64 sn) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 (Z_to_bv 64 2)) (y_F P) (Z_to_bv 64 0x17fbc) (y_fc P) None m1 (seg_rom psegs)).

