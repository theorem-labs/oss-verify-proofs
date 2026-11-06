(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_xat.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c328 c352 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (llv ile : Z) (cidx raddr : Z) (sn : Z) (x1 x5 x7 x10 x12 x13 x14 x15 x16 x17 x18 x25 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 LEND) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (l_DCTX P + 30372)) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  ile = LP + llv ->
  LEND < ile ->
  LOCV = 2 ->
  cidx = Z.land sn 7 ->
  raddr = l_FRB P + 408 + 24 * cidx ->
  llv = rl cidx ->
  sn = l_nbSeq P - K ->
  l_nbSeq P - Z.min (l_nbSeq P) 8 <= sn ->
  sql_ring_ok (Z.min (l_nbSeq P) 8) rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 (Z_to_bv 64 OP) x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 (Z_to_bv 64 LEND) x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 llv) (Z_to_bv 64 raddr) (Z_to_bv 64 ile) (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 sn) x25 (Z_to_bv 64 LP) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 (l_DCTX P + 30368)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_FF P + 120)) x31) (l_F P) (Z_to_bv 64 0x8dd68) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition t2_pre (P : slq) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : amem) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c328 c352 c376 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (raddr : Z) (sn : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x25 x26 x29 x30 x31 : word),
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 (Z_to_bv 64 3) (Z_to_bv 64 (l_DCTX P + 30420)) (Z_to_bv 64 (l_DCTX P + 30388)) (Z_to_bv 64 LEND) (Z_to_bv 64 (l_DCTX P + 95908)) (Z_to_bv 64 (-65537)) c328 (Z_to_bv 64 (OEND - 32)) c352 (Z_to_bv 64 (l_DCTX P + 30372)) c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  LOCV = 2 ->
  raddr = l_FRB P + 408 + 24 * Z.land sn 7 ->
  sn = l_nbSeq P - K ->
  l_nbSeq P - Z.min (l_nbSeq P) 8 <= sn ->
  sql_ring_ok (Z.min (l_nbSeq P) 8) rl rm ro ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 OP) x19 (Z_to_bv 64 raddr) x21 (Z_to_bv 64 (l_DCTX P + 30372)) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 sn) x25 x26 (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 (l_DCTX P + 30368)) x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e0c4) (l_fc P) None m1 (seg_rom bsegs)).


End CANSEC1.
