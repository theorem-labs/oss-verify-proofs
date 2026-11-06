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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition a1_head (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z)  (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x19e94) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_dec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (x1 x6 x7 x8 x9 x19 x21 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) (Z_to_bv 64 aOF) x6 x7 x8 x9 (Z_to_bv 64 nML) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bML) (Z_to_bv 64 bOF) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) (Z_to_bv 64 aML) (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 ofs (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 vLL) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x19f54) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_rl1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x8 x9 x17 x19 x21 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqs_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 nML) (Z_to_bv 64 nOF) (Z_to_bv 64 nLL) (Z_to_bv 64 bML) (Z_to_bv 64 bOF) (Z_to_bv 64 bLL) (Z_to_bv 64 aLL) x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 ofs (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 vLL) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x19f68) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_upd (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x19 x21 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 bc) x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a05c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_exec (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 LP) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a120) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_slow (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ow : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x19 x21 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ow = LP + llv - 32 ->
  LP + llv <= LEND ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 ow) x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a218) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_brk (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  LEND < LP + llv ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 LP) x9 (Z_to_bv 64 LEND) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a638) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_lit1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 LP) (Z_to_bv 64 ole) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a14c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_litloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 ole) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) (Z_to_bv 64 cur) (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a2bc) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_match (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ole) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a150) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_tail (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 r) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a200) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_matloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - v_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 cur) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) (Z_to_bv 64 src) (Z_to_bv 64 ome) x21 x22 (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a1c4) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_close (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ole) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 mtc) (Z_to_bv 64 ofs) (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a2ec) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_close8 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl rip8 : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  v_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 ole) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 rip8) x22 (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a47c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition a1_closeloop (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 (Z_to_bv 64 LEND) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqs_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  v_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 ome) x9 (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 16) (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a49c) (v_fc P) None m1 (seg_rom psegs)).

