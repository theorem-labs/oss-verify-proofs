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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition et_exec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs oe32 : Z) (x1 x5 x6 x7 x10 x13 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  oe32 = OEND - 32 ->
  LP = LLO ->
  LEND = LLO + 65536 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 (Z_to_bv 64 LP) (Z_to_bv 64 65536) x13 (Z_to_bv 64 OEND) x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 (Z_to_bv 64 30372) (Z_to_bv 64 K) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 oe32) (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bacc) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_slow (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 (Z_to_bv 64 OEND) x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 x23 (Z_to_bv 64 K) x25 x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c744) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_lit1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ole) (Z_to_bv 64 OP) (Z_to_bv 64 16) x21 x22 (Z_to_bv 64 30372) x24 (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1baf4) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_litloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ole) (Z_to_bv 64 OP) x20 (Z_to_bv 64 src) (Z_to_bv 64 cur) (Z_to_bv 64 30372) (Z_to_bv 64 (-17)) (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c7e0) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_match (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ole) (Z_to_bv 64 OP) x20 x21 x22 (Z_to_bv 64 30372) x24 (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1baf8) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_tail (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 r) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 x23 (Z_to_bv 64 K) x25 x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bc00) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_stail (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 x23 (Z_to_bv 64 K) x25 x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c774) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_tail2 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= r ->
  OP + r <= OEND ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bc14) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_matloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x25 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - v_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ome) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 OP) x20 (Z_to_bv 64 src) x22 x23 (Z_to_bv 64 K) x25 x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bba8) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_close (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc dpx : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - v_PFX P ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ole) (Z_to_bv 64 OP) (Z_to_bv 64 dpx) x21 x22 x23 x24 x25 (Z_to_bv 64 mtc) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c828) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_close8 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs dpx rip8 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs <= dpx ->
  dpx = ole - v_PFX P ->
  v_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ole) (Z_to_bv 64 OP) (Z_to_bv 64 dpx) x21 x22 x23 x24 x25 (Z_to_bv 64 rip8) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c93c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition et_closeloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 sl) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  v_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 cur) (Z_to_bv 64 9) (Z_to_bv 64 rsrc) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 (Z_to_bv 64 rsrc) x22 (Z_to_bv 64 ome) x24 x25 x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c990) (v_fc P) None m1 (seg_rom usegs)).

