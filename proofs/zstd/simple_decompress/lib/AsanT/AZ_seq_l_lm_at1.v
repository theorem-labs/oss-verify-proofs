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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_xat.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition lm_latch1 (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c128 c232 c248 c304 c320 c352 c376 cw: word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (r : Z) (sn cidx dll dml dof raddr : Z) (x5 x6 x7 x10 x11 x13 x15 x16 x17 x22 x26 x28 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 dml) (Z_to_bv 64 (l_DCTX P + 30372)) c128 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (l_nbSeq P - 1)) c232 c248 (Z_to_bv 64 raddr) c304 (Z_to_bv 64 dof) c320 (Z_to_bv 64 sn) (Z_to_bv 64 139648) c352 (Z_to_bv 64 dll) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= r ->
  OP + r <= OEND ->
  sn = l_nbSeq P - K ->
  8 <= sn ->
  0 <= cidx <= 7 ->
  0 <= dll < 2^18 ->
  0 <= dml < 2^18 ->
  0 <= dof < 2^64 ->
  sql_ring_ok 8 rl rm ro ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  LLO = l_DCTX P + 30372 ->
  LEND = l_DCTX P + 95908 ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR (Z_to_bv 64 sn) (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 (Z_to_bv 64 raddr) x13 (Z_to_bv 64 r) x15 x16 x17 (Z_to_bv 64 2147450880) c376 (Z_to_bv 64 OP) (Z_to_bv 64 (l_FF P + 32)) x22 (Z_to_bv 64 (l_DCTX P)) (Z_to_bv 64 (l_nbSeq P)) (Z_to_bv 64 (l_FF P)) x26 (Z_to_bv 64 dml) x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8b828) (l_fc P) None m1 (seg_rom bsegs)).


End CANSEC1.
