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
Definition la_head (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (cnt sn raddr rend : Z) (x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 c184 c216 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  cnt = K - 1 ->
  sn = y_nbSeq P - K ->
  0 <= sn < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 312 + 24 * sn ->
  rend = y_SPV P - 312 + 24 * Z.min (y_nbSeq P) 8 ->
  seql_ring_ok sn rl rm ro ->
  OP = y_DST P ->
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 raddr) x19 (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.min (y_nbSeq P) 8 - sn)) x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_SPV P - 344)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x17d38) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition la_dec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (cnt sn raddr rend : Z) (x5 x12 x13 x14 x15 x17 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 c184 c216 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
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
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 raddr) (Z_to_bv 64 mlv) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.min (y_nbSeq P) 8 - sn)) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) p0 (Z_to_bv 64 bOF) (Z_to_bv 64 vLL) (Z_to_bv 64 nLL) (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_SPV P - 344)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x17ec4) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition la_rl1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (cnt sn raddr rend : Z) (x5 x10 x11 x12 x13 x14 x15 x17 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 c184 c216 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
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
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 raddr) (Z_to_bv 64 mlv) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.min (y_nbSeq P) 8 - sn)) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) p0 (Z_to_bv 64 bOF) (Z_to_bv 64 vLL) (Z_to_bv 64 nLL) (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_SPV P - 344)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x17ed8) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition la_upd (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv : Z) (cnt sn raddr rend : Z) (x5 x8 x9 x11 x12 x13 x14 x15 x16 x17 x22 x23 x25 x27 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 c184 c216 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
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
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) x8 x9 (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 raddr) (Z_to_bv 64 mlv) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.min (y_nbSeq P) 8 - sn)) x22 x23 p0 x25 (Z_to_bv 64 llv) x27 (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_SPV P - 344)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x17fb8) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition la_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c176 c184 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv : Z) (cnt sn raddr rend : Z) (x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x25 x27 x29 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 c184 c216 (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
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
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 raddr) (Z_to_bv 64 mlv) (Z_to_bv 64 cnt) (Z_to_bv 64 (Z.min (y_nbSeq P) 8 - sn)) x22 x23 p0 x25 (Z_to_bv 64 llv) x27 (Z_to_bv 64 (2^60)) x29 (Z_to_bv 64 (y_SPV P - 344)) (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x17d14) (y_fc P) None m1 (seg_rom usegs)).

