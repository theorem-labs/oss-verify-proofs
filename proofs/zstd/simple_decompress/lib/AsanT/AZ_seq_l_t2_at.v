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
Definition t2_brk (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c232 c304 c320 c328 c352 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv ile : Z) (cidx raddr : Z) (sn : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) c232 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) c304 (Z_to_bv 64 (l_DCTX P + 95908)) c320 c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  ile = LP + llv ->
  LEND < ile ->
  LOCV = 2 ->
  cidx = Z.land sn 7 ->
  raddr = l_FRB P + 344 + 24 * cidx ->
  llv = rl cidx ->
  sn = l_nbSeq P - K ->
  l_nbSeq P - Z.min (l_nbSeq P) 8 <= sn ->
  sql_ring_ok (Z.min (l_nbSeq P) 8) rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) (Z_to_bv 64 LEND) (Z_to_bv 64 (l_FF P)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 OP) (Z_to_bv 64 ile) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 llv) x24 (Z_to_bv 64 LP) (Z_to_bv 64 LEND) (Z_to_bv 64 raddr) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8ce94) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition t2_pre (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c232 c304 c320 c328 c352 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (raddr : Z) (sn : Z) (llv : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x19 x20 x24 x26 x28 x29 x30 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 3) c232 (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) c304 (Z_to_bv 64 (l_DCTX P + 95908)) c320 c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 sn) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  LOCV = 2 ->
  0 <= llv < 2^18 ->
  raddr = l_FRB P + 344 + 24 * Z.land sn 7 ->
  sn = l_nbSeq P - K ->
  l_nbSeq P - Z.min (l_nbSeq P) 8 <= sn ->
  sql_ring_ok (Z.min (l_nbSeq P) 8) rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 OP) x17 (Z_to_bv 64 2147450880) x19 x20 (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P)) (Z_to_bv 64 llv) x24 (Z_to_bv 64 LEND) x26 (Z_to_bv 64 raddr) x28 x29 x30 (Z_to_bv 64 (l_DCTX P + 30368))) (l_F P) (Z_to_bv 64 0x8d29c) (l_fc P) None m1 (seg_rom bsegs)).


End CANSEC1.
