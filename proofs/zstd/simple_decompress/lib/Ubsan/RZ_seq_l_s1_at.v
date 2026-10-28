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
Definition s1_exec (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 (Z_to_bv 64 (ile - 32)) x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 LP) (Z_to_bv 64 llv) (Z_to_bv 64 ile) (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x189d8) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_slow (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ow : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x13 x14 x15 x16 x17 x19 x21 x23 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ow = LP + llv - 32 ->
  LP + llv <= LEND ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 (Z_to_bv 64 ow) x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 (Z_to_bv 64 mlv) x21 (Z_to_bv 64 llv) x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x190d8) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_lit1 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 LP) (Z_to_bv 64 llv) (Z_to_bv 64 ile) (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18a04) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_litloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 cur) (Z_to_bv 64 mlv) (Z_to_bv 64 src) x22 (Z_to_bv 64 ile) (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1943c) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_match (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seql_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 (Z_to_bv 64 mlv) x21 x22 (Z_to_bv 64 ile) (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18a0c) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_tail (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 c176 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (sn cidx dll dml dof : Z) (x1 x5 x8 x9 x10 x11 x13 x14 x15 x19 x20 x21 x22 x23 x29 x30 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) c176 (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= r < 2^64 ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 (y_DCTX P + 29896)) (Z_to_bv 64 (y_SPV P - 352)) x8 x9 x10 x11 (Z_to_bv 64 r) x13 x14 x15 (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 sn) x19 x20 x21 x22 x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 2) (Z_to_bv 64 (2^60)) x29 x30 (Z_to_bv 64 BITMASK)) (y_F P) (Z_to_bv 64 0x19038) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_matloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - y_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ome) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 (Z_to_bv 64 src) x21 x22 x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 cur) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18abc) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_close (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl ofs mtc q : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - y_PFX P ->
  mtc = ole - ofs ->
  0 <= q -> Z.max q ofs = ole - y_PFX P ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 q) (Z_to_bv 64 mlv) (Z_to_bv 64 mtc) x22 x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1966c) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_close8 (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl rip8 ofs q : Z) (sn cidx dll dml dof : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  y_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs < 16 -> 0 <= q -> Z.max q ofs = ole - y_PFX P ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) (Z_to_bv 64 q) (Z_to_bv 64 mlv) (Z_to_bv 64 rip8) x22 x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x198e8) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition s1_closeloop (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (sn cidx dll dml dof : Z) (x1 x5 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x27 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 (y_PFX P + 8)) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (-65537)) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) c128 (Z_to_bv 64 (y_nbSeq P - 1)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 sl) (Z_to_bv 64 (- (y_SPV P - 328) - 1)) (Z_to_bv 64 dof) (Z_to_bv 64 dml) (Z_to_bv 64 dll) (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seql_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  y_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  sn = y_nbSeq P - K ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  seql_ring_ok 8 rl rm ro ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 (Z_to_bv 64 rsrc) x7 x8 (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 sn) x19 x20 x21 (Z_to_bv 64 ome) x23 (Z_to_bv 64 cidx) (Z_to_bv 64 OP) (Z_to_bv 64 (-17)) x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x19948) (y_fc P) None m1 (seg_rom usegs)).

