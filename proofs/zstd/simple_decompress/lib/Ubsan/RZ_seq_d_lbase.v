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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base huf411_kit_rs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqd_static (P : sdp) (OEND LEND : Z) : Prop := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  4096 <= B0 /\ B0 <= PFX /\ PFX <= DST /\ DST <= OEND /\ OEND <= DST + CAP /\ DST + CAP <= B1 /\ B1 < 2^47 /\
  LEND = LITP + LITSZ /\ 4096 <= LITP /\ 0 <= LITSZ < 2^32 /\ LEND + 32 < 2^47 /\
  ((OEND <= LITP /\ LEND + 32 <= B1) \/ LEND + 32 <= B0 \/ B1 <= LITP) /\
  4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 1 <= zlen sq /\ 1 <= nbSeq <= 98047 /\
  544 <= SPV < 2^47 /\ 4096 <= lo <= SPV - 544 /\
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  (B1 <= lo \/ SPV <= B0) /\ (SEQ + zlen sq <= lo \/ SPV <= SEQ) /\ (LEND + 32 <= lo \/ SPV <= LITP) /\
  (DCTX + 95992 <= lo \/ SPV <= DCTX) /\
  (LLT + 4104 <= lo \/ SPV <= LLT) /\ (OFT + 2056 <= lo \/ SPV <= OFT) /\ (MLT + 4104 <= lo \/ SPV <= MLT) /\
  (B1 <= SEQ \/ SEQ + zlen sq <= B0) /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\
  (B1 <= LLT \/ LLT + 4104 <= B0) /\ (B1 <= OFT \/ OFT + 2056 <= B0) /\ (B1 <= MLT \/ MLT + 4104 <= B0) /\
  seq_table_ok K_LL tLL /\ seq_table_ok K_OF tOF /\ seq_table_ok K_ML tML /\
  (rsk_al SPV 16 /\ rsk_al LLT 4 /\ rsk_al OFT 4 /\ rsk_al MLT 4).

(* [comment removed for export] *)
Definition seqd_frame (P : sdp) (OEND LEND : Z) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (j0 jpad jseq : list byte) : list cell := let '(mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [CB 8 j0; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 DST);
   C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 PFX);
   C8 (Z_to_bv 64 1152921504606846976); C8 (Z_to_bv 64 LEND);
   C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML);
   C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 LP); CB 24 jseq;
   CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].

(* [comment removed for export] *)
Definition seqd_linv (P : sdp) (OEND LEND : Z) (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) : Prop :=
  (exists j0 jpad jseq, rw_cells usegs m1 (q_SPV P + -352) (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq)) /\
  bytes_at usegs m1 (q_LLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tLL P))) /\
  bytes_at usegs m1 (q_OFT P) (map (Z_to_bv 8) (seq_table_bytes (q_tOF P))) /\
  bytes_at usegs m1 (q_MLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tML P))) /\
  bytes_at usegs m1 (q_SEQ P) (map (Z_to_bv 8) (q_sq P)) /\
  rdbl usegs m1 (q_LITP P) (LEND + 32) /\
  seqd_xinv P m1 (seqd_fe P).

(* [comment removed for export] *)
Definition bit_ok (SEQ n bc ptr : Z) : Prop := bc <= 64 -> ptr = SEQ \/ (8 <= n /\ SEQ <= ptr <= SEQ + n - 8).

(* [comment removed for export] *)
Definition seqd_lfacts (P : sdp) (OEND LEND BND OP LP bc ptr sLL sOF sML : Z) : Prop :=
  q_DST P <= OP <= OEND /\ q_LITP P <= LP <= LEND /\
  0 <= sLL < 2^(st_log (q_tLL P)) /\ 0 <= sOF < 2^(st_log (q_tOF P)) /\ 0 <= sML < 2^(st_log (q_tML P)) /\
  0 <= bc <= BND /\ bit_ok (q_SEQ P) (zlen (q_sq P)) bc ptr.

(* [comment removed for export] *)
Definition seqd_next (P : sdp) (nLL bLL nOF bOF nML bML : Z) : Prop :=
  0 <= bLL <= 9 /\ 0 <= nLL /\ nLL + 2^bLL <= 2^(st_log (q_tLL P)) /\
  0 <= bOF <= 9 /\ 0 <= nOF /\ nOF + 2^bOF <= 2^(st_log (q_tOF P)) /\
  0 <= bML <= 9 /\ 0 <= nML /\ nML + 2^bML <= 2^(st_log (q_tML P)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_head (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z)  (x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 0) OP LP bc ptr sLL sOF sML ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 (Z_to_bv 64 (q_SPV P + -160)) (Z_to_bv 64 1152921504606846976) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 x21 x22 x23 (Z_to_bv 64 OP) x25 x26 x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cc14) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_b884 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqd_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= aML <= 16 ->
  0 <= aOF <= 31 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 ofs (Z_to_bv 64 aLL) (Z_to_bv 64 aML) (Z_to_bv 64 aOF) x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 bOF) (Z_to_bv 64 mlv) (Z_to_bv 64 nLL) (Z_to_bv 64 bLL) (Z_to_bv 64 OP) (Z_to_bv 64 nML) (Z_to_bv 64 vLL) (Z_to_bv 64 bML) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cd5c) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_b898 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (nLL aLL bLL vLL nOF bOF nML bML mlv : Z) (ofs : word) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 47) OP LP bc ptr sLL sOF sML ->
  seqd_next P nLL bLL nOF bOF nML bML ->
  0 <= aLL <= 16 ->
  0 <= vLL < 2^17 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 ofs (Z_to_bv 64 aLL) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 nOF) x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 bOF) (Z_to_bv 64 mlv) (Z_to_bv 64 nLL) (Z_to_bv 64 bLL) (Z_to_bv 64 OP) (Z_to_bv 64 nML) (Z_to_bv 64 vLL) (Z_to_bv 64 bML) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1cd70) (q_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition at_ba80 (P : sdp) (OEND LEND K : Z) : Prop :=
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv : Z) (ofs : word) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x25 x27 x28 x29 x30 x31 : word) (pcb : Z),
  (pcb = 0x1cff4 \/ pcb = 0x1d400) ->
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 ofs x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 (Z_to_bv 64 mlv) x22 x23 (Z_to_bv 64 OP) x25 (Z_to_bv 64 llv) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 pcb) (q_fc P) None m1 (seg_rom usegs)).

