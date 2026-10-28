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
Definition a2_head (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z)  (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) x21 x22 x23 x24 (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bc38) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_dec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 vLL) ofs (Z_to_bv 64 aML) (Z_to_bv 64 aOF) x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 aLL) (Z_to_bv 64 K) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 bML) (Z_to_bv 64 nLL) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bd80) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_rl1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 vLL) ofs x10 x11 x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 aLL) (Z_to_bv 64 K) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 bML) (Z_to_bv 64 nLL) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1bd94) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_upd (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 ofs) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1be70) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_exec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c018) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_execb (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) (Z_to_bv 64 LP) x22 (Z_to_bv 64 ile) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c028) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_slow (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 OP) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c430) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_lit1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 llv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 K) (Z_to_bv 64 LP) x22 (Z_to_bv 64 ile) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c04c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_litloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 K) (Z_to_bv 64 src) (Z_to_bv 64 cur) (Z_to_bv 64 ile) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c298) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_match (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 K) x21 x22 (Z_to_bv 64 ile) (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c054) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_tail (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) x21 x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 r) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c148) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_matloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - v_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ome) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 src) (Z_to_bv 64 K) (Z_to_bv 64 cur) x22 x23 x24 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c0ec) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_close (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (ole - v_PFX P)) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 K) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 mtc) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c2e0) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_close8 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs rip8 : Z) (x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  v_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs <= ole - v_PFX P ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 (ole - v_PFX P)) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 K) x21 x22 x23 (Z_to_bv 64 mlv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 rip8) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c4c4) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a2_closeloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x8 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  v_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 K) (Z_to_bv 64 rsrc) x22 x23 (Z_to_bv 64 ome) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1c514) (v_fc P) None m1 (seg_rom usegs)).

