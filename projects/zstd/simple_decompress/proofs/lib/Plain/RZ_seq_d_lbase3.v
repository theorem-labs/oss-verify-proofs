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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lbase2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqd_mfast (P : sdp) (OEND OP ole mlv sl : Z) : Prop :=
  q_DST P <= OP <= ole /\ 0 <= mlv < 2^18 /\ ole + mlv <= OEND - 32 /\ sl = ole - OP + mlv.

(* [comment removed for export] *)
Definition at_bfa4 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (r : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= r < 2^64 ->
  zd_is_error r = true \/ r <= q_CAP P ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1c070) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition at_bb28 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  16 <= ofs <= ole - q_PFX P ->
  ome = ole + mlv ->
  ole + 16 <= cur < ome ->
  src = cur - ofs + 16 ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) x19 (Z_to_bv 64 src) x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 OP) (Z_to_bv 64 ome) (Z_to_bv 64 sl) (Z_to_bv 64 cur) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bbf4) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition at_bca4 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs mtc : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  0 <= ofs < 16 ->
  ofs <= ole - q_PFX P ->
  mtc = ole - ofs ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 ofs) x20 (Z_to_bv 64 mtc) (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 OP) (Z_to_bv 64 mlv) (Z_to_bv 64 sl) (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bd70) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition at_be28 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl rip8 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  q_PFX P <= rip8 + 8 ->
  ole - 7 <= rip8 + 8 <= ole ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) x19 x20 (Z_to_bv 64 rip8) (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 OP) (Z_to_bv 64 mlv) (Z_to_bv 64 sl) (Z_to_bv 64 ole) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bef4) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition at_be48 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl cur rsrc ome : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x21 x23 x25 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl ->
  ome = ole + mlv ->
  ole + 8 <= cur < ome ->
  q_PFX P <= rsrc ->
  8 <= cur - rsrc <= 15 ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 cur) (Z_to_bv 64 rsrc) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 ome) x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 OP) x25 (Z_to_bv 64 sl) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1bf14) (q_fc P) None m1 (seg_rom psegs)).

