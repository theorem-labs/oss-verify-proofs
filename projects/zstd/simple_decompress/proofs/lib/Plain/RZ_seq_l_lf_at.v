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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma land7_min : forall idx n, 0 <= idx < n -> 0 <= Z.land idx 7 < Z.min n 8.
Proof.
  intros idx n H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
  pose proof (Z.mod_pos_bound idx 8 ltac:(lia)) as HB. destruct (Z_lt_le_dec idx 8) as [L|L]; [rewrite Z.mod_small by lia; lia | lia].
Qed.

(* [comment removed for export] *)
Definition lf_head (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (idx : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x19 x22 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) x22 (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (y_nbSeq P)) x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18cc8) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition lf_fnorm (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  cidx < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  LOCV <> 2 ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (y_nbSeq P)) x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18db8) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition lf_fsplit (P : slp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z)  (idx cidx raddr : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x19 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  seql_lfacts P OEND LLO LEND (100 + 100 * (y_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  idx = y_nbSeq P - K ->
  seql_ring_ok (Z.min (y_nbSeq P) 8) rl rm ro ->
  0 <= cidx <= 7 ->
  cidx < Z.min (y_nbSeq P) 8 ->
  raddr = y_SPV P - 328 + 24 * cidx ->
  LOCV = 2 ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 (Z_to_bv 64 idx) x19 (Z_to_bv 64 OEND) (Z_to_bv 64 16) (Z_to_bv 64 raddr) (Z_to_bv 64 (y_DCTX P + 30372)) (Z_to_bv 64 (y_nbSeq P)) x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18cec) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition lf_end (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (w0 c8 c16 c48 c56 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (OP : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 (Z_to_bv 64 (y_DCTX P + 30420)) (Z_to_bv 64 LEND) (Z_to_bv 64 (y_DCTX P + 30388)) (Z_to_bv 64 (y_DCTX P + 95908)) (Z_to_bv 64 (OEND - 32)) cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  y_DST P <= OP <= OEND -> LLO <= LP <= LEND ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (y_DCTX P + 29896)) x14 x15 x16 x17 x18 x19 (Z_to_bv 64 OEND) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x19740) (y_fc P) None m1 (seg_rom psegs)).
