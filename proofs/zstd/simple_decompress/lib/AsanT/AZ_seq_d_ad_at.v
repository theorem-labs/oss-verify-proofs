(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_xat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

(* [comment removed for export] *)
Definition ad_head (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z)  (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x27 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 (Z_to_bv 64 AG_blk_BIT_mask) x21 x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93970) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_dec (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (x1 x10 x12 x22 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  sqd_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) (Z_to_bv 64 bLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 (w_SHF P)) ofs (Z_to_bv 64 AG_blk_BIT_mask) (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 vLL) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93b4c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_rl1 (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (x1 x6 x7 x10 x12 x22 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  sqd_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) (Z_to_bv 64 bLL) x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 (Z_to_bv 64 bOF) x12 (Z_to_bv 64 nOF) (Z_to_bv 64 nML) (Z_to_bv 64 nLL) (Z_to_bv 64 aLL) (Z_to_bv 64 bML) (Z_to_bv 64 (w_SHF P)) ofs (Z_to_bv 64 AG_blk_BIT_mask) (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 vLL) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93b60) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_upd (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ofs) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93c34) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_exec (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ofs) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93d44) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_execb (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ofs) (Z_to_bv 64 ile) (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 LP) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x93d50) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_slow (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ofs) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 (Z_to_bv 64 LEND)) (w_F P) (Z_to_bv 64 0x9414c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_lit1 (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 LP) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93d7c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_litloop (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) (Z_to_bv 64 mlv) (Z_to_bv 64 cur) (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 src) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93f14) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_match (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) (Z_to_bv 64 ile) (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 llv) x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93d84) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_tail (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 r) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 x20 x21 x22 (Z_to_bv 64 (w_FF P + 32)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93e4c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_ctail (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 r) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 x20 x21 x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93e54) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_tail2 (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x27 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= r ->
  OP + r <= OEND ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 x20 x21 x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 K) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93e5c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_matloop (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x27 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqd_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - w_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) x19 (Z_to_bv 64 ome) (Z_to_bv 64 cur) (Z_to_bv 64 src) (Z_to_bv 64 (w_FF P + 32)) x24 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x93e10) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_close (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x27 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqd_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - w_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - w_PFX P ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR (Z_to_bv 64 ofs) (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 mtc) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 (Z_to_bv 64 dpx) x29 x30 x31) (w_F P) (Z_to_bv 64 0x93f44) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_close_sel (sel : Z -> Prop) (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x27 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqd_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - w_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - w_PFX P ->
  sel ofs ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR (Z_to_bv 64 ofs) (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 mtc) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 (Z_to_bv 64 dpx) x29 x30 x31) (w_F P) (Z_to_bv 64 0x93f44) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_close8 (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c32 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl rip8 : Z) (ofs dpx : Z) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x27 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) c32 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqd_mfast P OEND OP ole mlv sl ->
  w_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs <= ole - w_PFX P ->
  dpx = ole - w_PFX P ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR (Z_to_bv 64 ofs) (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ole) x20 (Z_to_bv 64 mlv) x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 rip8) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 (Z_to_bv 64 dpx) x29 x30 x31) (w_F P) (Z_to_bv 64 0x94304) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ad_closeloop (P : sqp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c24 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (j va0 va1 va4 vr8 sh5 sh6 : Z) (x5 x6 x7 x12 x17 x20 x21 x22 x27 x28 x29 x30 x31 : word),
  sqd_linv P OEND LLO LEND LOCV m1 (Z_to_bv 64 sl) (Z_to_bv 64 va4) (Z_to_bv 64 ome) (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND (100 + 100 * (w_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqd_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  w_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  va0 = ole + 8 ->
  va1 = rsrc - j ->
  va4 = ole ->
  vr8 = rsrc - j - 8 ->
  cur = ole + 8 + j ->
  sh5 = 2147450880 + cur / 8 ->
  sh6 = 2147450880 + rsrc / 8 ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR c216 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) (Z_to_bv 64 va0) (Z_to_bv 64 va1) x12 (Z_to_bv 64 j) (Z_to_bv 64 va4) (Z_to_bv 64 sh5) (Z_to_bv 64 sh6) x17 (Z_to_bv 64 (w_SHF P)) (Z_to_bv 64 ome) x20 x21 x22 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 vr8) (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x94350) (w_fc P) None m1 (seg_rom bsegs)).

End CANSEC1.
