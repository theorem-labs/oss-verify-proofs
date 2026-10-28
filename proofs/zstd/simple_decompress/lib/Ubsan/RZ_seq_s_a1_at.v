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
Definition a1_head (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z)  (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x27 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 K) x20 x21 x22 x23 x24 x25 (Z_to_bv 64 OP) x27 (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1ada8) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_dec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) ofs (Z_to_bv 64 aML) (Z_to_bv 64 aOF) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 OP) (Z_to_bv 64 vLL) (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1af38) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_rl1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) ofs x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bOF) (Z_to_bv 64 nML) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 OP) (Z_to_bv 64 vLL) (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1af4c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_upd (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 x20 x21 x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 llv) (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b038) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_exec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x25 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 (Z_to_bv 64 ile) (Z_to_bv 64 LP) x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 llv) (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b23c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_slow (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ow : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ow = LP + llv - 32 ->
  LP + llv <= LEND ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 (Z_to_bv 64 ow) x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 x20 x21 x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b3f0) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_brk (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  LEND < LP + llv ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 (Z_to_bv 64 LEND) x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 LP) x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1ba28) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_lit1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) (Z_to_bv 64 LP) x22 x23 (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b280) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_litloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) x21 (Z_to_bv 64 cur) (Z_to_bv 64 (v_PFX P)) (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) (Z_to_bv 64 src) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b564) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_match (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) x21 x22 (Z_to_bv 64 (v_PFX P)) (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b28c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_tail (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x27 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 x20 x21 x22 x23 (Z_to_bv 64 K) (Z_to_bv 64 r) (Z_to_bv 64 OP) x27 (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b3a8) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_matloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - v_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ome) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 src) x20 x21 (Z_to_bv 64 cur) x23 (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b338) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_close (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 (ole - v_PFX P)) (Z_to_bv 64 mtc) x22 x23 (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b5bc) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_close8 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs rip8 : Z) (x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x27 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  v_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs <= ole - v_PFX P ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 ole) (Z_to_bv 64 (ole - v_PFX P)) (Z_to_bv 64 rip8) x22 x23 (Z_to_bv 64 K) (Z_to_bv 64 sl) (Z_to_bv 64 OP) x27 (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b7a0) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition a1_closeloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x27 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  v_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 (Z_to_bv 64 (v_SPV P + -160)) (Z_to_bv 64 (2^60)) x8 (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (-17)) x19 x20 x21 (Z_to_bv 64 rsrc) (Z_to_bv 64 ome) x24 (Z_to_bv 64 sl) (Z_to_bv 64 OP) x27 (Z_to_bv 64 32) x29 x30 x31) (v_F P) (Z_to_bv 64 0x1b7fc) (v_fc P) None m1 (seg_rom usegs)).

