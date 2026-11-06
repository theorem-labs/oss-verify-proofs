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
Definition la_head (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (cnt sn raddr rend : Z) (x1 x7 x8 x9 x12 x16 x18 x21 x22 x23 x24 x25 x26 x27 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_SEQ P + 8)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) (Z_to_bv 64 (y_OFT P + 8)) (Z_to_bv 64 (y_LLT P + 8)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 x8 x9 p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) x18 (Z_to_bv 64 cnt) (Z_to_bv 64 rend) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P + 8)) (Z_to_bv 64 raddr) x31) (y_F P) (Z_to_bv 64 0x179dc) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition la_dec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (cnt sn raddr rend : Z) (x7 x16 x21 x23 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_SEQ P + 8)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) (Z_to_bv 64 (y_OFT P + 8)) (Z_to_bv 64 (y_LLT P + 8)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt psegs (seql_post P) (MS (mkR (Z_to_bv 64 nOF) (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 (Z_to_bv 64 aOF) (Z_to_bv 64 bLL) p0 p1 (Z_to_bv 64 aLL) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) (Z_to_bv 64 bOF) (Z_to_bv 64 cnt) (Z_to_bv 64 rend) x21 (Z_to_bv 64 bML) x23 (Z_to_bv 64 mlv) (Z_to_bv 64 vLL) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P + 8)) (Z_to_bv 64 raddr) (Z_to_bv 64 aML)) (y_F P) (Z_to_bv 64 0x17a78) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition la_rl1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (cnt sn raddr rend : Z) (x7 x8 x16 x21 x23 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_SEQ P + 8)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) (Z_to_bv 64 (y_OFT P + 8)) (Z_to_bv 64 (y_LLT P + 8)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seql_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt psegs (seql_post P) (MS (mkR (Z_to_bv 64 nOF) (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 x8 (Z_to_bv 64 bLL) p0 p1 (Z_to_bv 64 aLL) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) (Z_to_bv 64 bOF) (Z_to_bv 64 cnt) (Z_to_bv 64 rend) x21 (Z_to_bv 64 bML) x23 (Z_to_bv 64 mlv) (Z_to_bv 64 vLL) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P + 8)) (Z_to_bv 64 raddr) x31) (y_F P) (Z_to_bv 64 0x17a8c) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition la_upd (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv : Z) (cnt sn raddr rend : Z) (x1 x7 x8 x9 x12 x16 x18 x21 x22 x23 x26 x27 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_SEQ P + 8)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) (Z_to_bv 64 (y_OFT P + 8)) (Z_to_bv 64 (y_LLT P + 8)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 x8 x9 p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) x18 (Z_to_bv 64 cnt) (Z_to_bv 64 rend) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 llv) x26 x27 (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P + 8)) (Z_to_bv 64 raddr) x31) (y_F P) (Z_to_bv 64 0x17b20) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition la_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv : Z) (cnt sn raddr rend : Z) (x1 x7 x8 x9 x12 x16 x18 x21 x22 x23 x26 x27 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_SEQ P + 8)) (Z_to_bv 64 LEND) (Z_to_bv 64 BITMASK) (Z_to_bv 64 (y_OFT P + 8)) (Z_to_bv 64 (y_LLT P + 8)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 x8 x9 p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) x18 (Z_to_bv 64 cnt) (Z_to_bv 64 rend) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 llv) x26 x27 (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P + 8)) (Z_to_bv 64 raddr) x31) (y_F P) (Z_to_bv 64 0x179bc) (y_fc P) None m1 (seg_rom psegs)).

