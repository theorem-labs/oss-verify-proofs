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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit .
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
Definition sqs_at_err (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (r : Z) (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= v_CAP P ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 (Z_to_bv 64 r) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x91f9c) (v_fc P) None m1 (seg_rom bsegs)).

Definition sqs_at_err19 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= v_CAP P ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x90c94) (v_fc P) None m1 (seg_rom bsegs)).

Definition sqs_at_err10 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= v_CAP P ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x90dec) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition sqs_at_err20 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x91fa0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition sqs_at_lexit (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (c0 c8 c152 c160 c168 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x28 x29 x30 : word),
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DST P <= OP <= OEND ->
  LLO <= LP <= LEND ->
  0 <= bc < 2^31 ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) (Z_to_bv 64 (v_DCTX P + 26684)) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 OP) x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896))) (v_F P) (Z_to_bv 64 0x90ca0) (v_fc P) None m1 (seg_rom bsegs)).

End CANSEC1.
