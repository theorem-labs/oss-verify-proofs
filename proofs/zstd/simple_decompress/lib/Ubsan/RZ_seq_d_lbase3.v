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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lbase2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqd_mfast (P : sdp) (OEND OP ole mlv sl : Z) : Prop :=
  q_DST P <= OP <= ole /\ 0 <= mlv < 2^18 /\ ole + mlv <= OEND - 32 /\ sl = ole - OP + mlv.

(* [comment removed for export] *)
Definition at_bfa4 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= q_CAP P ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d6e4) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bb28 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x26 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - q_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 x21 (Z_to_bv 64 ome) x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d0c8) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_bca4 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc q : Z) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - q_PFX P ->
  mtc = ole - ofs ->
  0 <= q ->
  Z.max q ofs = ole - q_PFX P ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 ofs) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 mtc) (Z_to_bv 64 mlv) (Z_to_bv 64 q) x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d2c0) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_be28 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl rip8 ofs q : Z) (x1 x5 x9 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  q_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  0 <= ofs < 16 ->
  0 <= q ->
  Z.max q ofs = ole - q_PFX P ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 ofs) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 rip8) (Z_to_bv 64 mlv) (Z_to_bv 64 q) x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d4a4) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_be48 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x26 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  q_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) (Z_to_bv 64 rsrc) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 ome) x22 x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d4f4) (q_fc P) None m1 (seg_rom usegs)).

