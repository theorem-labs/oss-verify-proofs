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
Definition s2_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (idx : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x22 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 idx) x10 x11 (Z_to_bv 64 (ile - 32)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) (Z_to_bv 64 ile) (Z_to_bv 64 LP) x22 (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) x26 (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x19f48) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_slow (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ow : Z) (idx : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x20 x21 x22 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ow = LP + llv - 32 ->
  LP + llv <= LEND ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 idx) x10 x11 (Z_to_bv 64 ow) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) x20 x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) x26 (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a238) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_lit1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (idx : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) (Z_to_bv 64 ile) (Z_to_bv 64 LP) (Z_to_bv 64 ole) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x19f70) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_litloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (idx : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 cur) (Z_to_bv 64 (-17)) (Z_to_bv 64 ile) x21 (Z_to_bv 64 ole) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a450) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_match (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) (Z_to_bv 64 ile) x21 (Z_to_bv 64 ole) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x19f78) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_tail (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) x20 x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 r) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a1a4) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_stail (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) x20 x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 r) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a1a4) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_tail2 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) x20 x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 r) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a1a4) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_matloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (idx : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - y_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 cur) (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ome) (Z_to_bv 64 (-17)) (Z_to_bv 64 src) x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a010) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_close (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs mtc q : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - y_PFX P ->
  mtc = ole - ofs ->
  0 <= q -> Z.max q ofs = ole - y_PFX P ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 q) (Z_to_bv 64 (-17)) x20 (Z_to_bv 64 mtc) (Z_to_bv 64 ole) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a614) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_close8 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl rip8 ofs q : Z) (idx : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  y_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs < 16 -> 0 <= q -> Z.max q ofs = ole - y_PFX P ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 q) (Z_to_bv 64 (-17)) x20 (Z_to_bv 64 rip8) (Z_to_bv 64 ole) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 ofs) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mlv) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a814) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s2_closeloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (idx : Z) (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  y_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 idx) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (-17)) (Z_to_bv 64 rsrc) x21 x22 (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 cur) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 ome) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1a86c) (y_fc P) None m1 (seg_rom usegs)).

