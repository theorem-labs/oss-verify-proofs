(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqd_fast (OEND LEND OP LP llv mlv : Z) : Prop :=
  0 <= llv < 2^18 /\ 0 <= mlv < 2^18 /\ LP + llv <= LEND /\ OP + llv + mlv <= OEND - 32.

(* [comment removed for export] *)
Definition at_b93c (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv : Z) (ofs : word) (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 ofs x9 (Z_to_bv 64 bc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 mlv) x22 x23 (Z_to_bv 64 OP) x25 (Z_to_bv 64 llv) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1ce4c) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bb64 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ (seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML /\ OP + r <= OEND) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 1152921504606846976) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 x21 x22 x23 (Z_to_bv 64 OP) (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d124) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_exit (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  q_DST P <= OP <= OEND ->
  q_LITP P <= LP <= LEND ->
  0 <= bc < 2^31 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d65c) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bb80 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 ofs) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 mlv) x22 x23 (Z_to_bv 64 OP) x25 (Z_to_bv 64 llv) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d410) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_baac (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 ofs) (Z_to_bv 64 LP) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 mlv) (Z_to_bv 64 ile) x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 llv) (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d028) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bc74 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole cur src : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  OP + 32 <= cur < ole ->
  src = LP + (cur - OP) + 16 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 ofs) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 cur) (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 sl) (Z_to_bv 64 src) (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d278) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bab4 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs ile sl ole : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  seqd_fast OEND LEND OP LP llv mlv ->
  ile = LP + llv ->
  sl = llv + mlv ->
  ole = OP + llv ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 ofs) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 mlv) (Z_to_bv 64 ile) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d034) (q_fc P) None m1 (seg_rom usegs)).

