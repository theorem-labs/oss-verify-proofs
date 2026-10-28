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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_xat.
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
Definition et_execb (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile : Z) (sl : Z) (x1 x5 x6 x7 x10 x12 x13 x14 x15 x17 x18 x19 x23 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  ile = LP + llv ->
  ile <= LEND ->
  LP = LLO ->
  OP + llv + mlv + 32 <= OEND ->
  sl = llv + mlv ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 (Z_to_bv 64 LLO) x12 x13 x14 x15 (Z_to_bv 64 OP) x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 30372) x23 (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 mlv) (Z_to_bv 64 llv) (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x90ff8) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_slow (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 c168 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x18 x19 x22 x23 x24 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) c168 (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 OP) x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 x23 x24 (Z_to_bv 64 mlv) (Z_to_bv 64 llv) (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x920f8) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_lit1 (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 16) x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ile) (Z_to_bv 64 ole) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 mlv) (Z_to_bv 64 llv) (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x91014) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_litloop (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 src) (Z_to_bv 64 cur) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ile) (Z_to_bv 64 ole) x24 (Z_to_bv 64 mlv) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x92170) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_match (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  sqs_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  LP = LLO ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ile) (Z_to_bv 64 ole) x24 (Z_to_bv 64 mlv) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x9101c) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_tail (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 r) (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x910dc) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_ctail (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 r) (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x92634) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_tail2 (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c168 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x22 x24 x26 x28 x29 x30 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= r ->
  OP + r <= OEND ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 (v_DCTX P + 26684)) x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 0x22180) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 OP) x24 (Z_to_bv 64 K) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896))) (v_F P) (Z_to_bv 64 0x910fc) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_matloop (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqs_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - v_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 src) x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ome) (Z_to_bv 64 cur) x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x910a0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_close (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x24 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - v_PFX P ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 (Z_to_bv 64 ofs) x13 x14 x15 x16 x17 (Z_to_bv 64 dpx) (Z_to_bv 64 mtc) (Z_to_bv 64 (v_FF P + 32)) x21 x22 (Z_to_bv 64 ole) x24 (Z_to_bv 64 mlv) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x921a0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_close_sel (sel : Z -> Prop) (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (dpx : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x21 x22 x24 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqs_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - v_PFX P ->
  mtc = ole - ofs ->
  dpx = ole - v_PFX P ->
  sel ofs ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 (Z_to_bv 64 ofs) x13 x14 x15 x16 x17 (Z_to_bv 64 dpx) (Z_to_bv 64 mtc) (Z_to_bv 64 (v_FF P + 32)) x21 x22 (Z_to_bv 64 ole) x24 (Z_to_bv 64 mlv) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x921a0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_close8 (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl rip8 : Z) (ofs dpx : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) (Z_to_bv 64 ofs) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqs_mfast P OEND OP ole mlv sl ->
  v_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs <= ole - v_PFX P ->
  dpx = ole - v_PFX P ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 dpx) (Z_to_bv 64 rip8) (Z_to_bv 64 (v_FF P + 32)) x21 x22 (Z_to_bv 64 ole) x24 (Z_to_bv 64 mlv) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x92460) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition et_closeloop (P : ssq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c0 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (j va0 va1 va4 vr8 sh5 sh6 : Z) (x1 x5 x6 x7 x12 x17 x18 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 (Z_to_bv 64 OP) (Z_to_bv 64 2147450880) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 sl) (Z_to_bv 64 LEND) (Z_to_bv 64 K) c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  sqs_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  v_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  va0 = ole + 8 ->
  va1 = rsrc - j ->
  va4 = ole ->
  vr8 = rsrc - j - 8 ->
  cur = ole + 8 + j ->
  sh5 = 2147450880 + cur / 8 ->
  sh6 = 2147450880 + rsrc / 8 ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 va0) (Z_to_bv 64 va1) x12 (Z_to_bv 64 j) (Z_to_bv 64 va4) (Z_to_bv 64 sh5) (Z_to_bv 64 sh6) x17 x18 (Z_to_bv 64 vr8) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ome) x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x924b4) (v_fc P) None m1 (seg_rom bsegs)).

End CANSEC1.
