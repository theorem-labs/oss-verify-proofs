(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seql_static (P : slp) (OEND LLO LEND LOCV : Z) : Prop := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  4096 <= B0 /\ B0 <= PFX /\ PFX <= DST /\ DST <= OEND /\ OEND <= DST + CAP /\ DST + CAP <= B1 /\ B1 < 2^47 /\
  LLO <= LEND /\ 4096 <= LLO /\ 0 <= LEND - LLO < 2^47 /\ LEND + 32 < 2^47 /\
  ((B0 <= LLO /\ LEND + 32 <= B1) \/ LEND + 32 <= B0 \/ B1 <= LLO) /\
  4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 1 <= zlen sq /\ 1 <= nbSeq <= 98047 /\
  896 <= SPV < 2^47 /\ 4096 <= lo <= SPV - 896 /\
  4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= LLT < 2^47 /\ 4096 <= OFT < 2^47 /\ 4096 <= MLT < 2^47 /\
  (B1 <= lo \/ SPV <= B0) /\ (SEQ + zlen sq <= lo \/ SPV <= SEQ) /\ (LEND + 32 <= lo \/ SPV <= LLO) /\
  (DCTX + 95992 <= lo \/ SPV <= DCTX) /\
  (LLT + 4104 <= lo \/ SPV <= LLT) /\ (OFT + 2056 <= lo \/ SPV <= OFT) /\ (MLT + 4104 <= lo \/ SPV <= MLT) /\
  (B1 <= SEQ \/ SEQ + zlen sq <= B0) /\ (B1 <= DCTX \/ DCTX + 95992 <= B0) /\
  (B1 <= LLT \/ LLT + 4104 <= B0) /\ (B1 <= OFT \/ OFT + 2056 <= B0) /\ (B1 <= MLT \/ MLT + 4104 <= B0) /\
  (LEND + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LLO) /\
  (LLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= LLT) /\ (OFT + 2056 <= DCTX + 26684 \/ DCTX + 95992 <= OFT) /\
  (MLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= MLT) /\ (SEQ + zlen sq <= DCTX + 26684 \/ DCTX + 95992 <= SEQ) /\
  0 <= LOCV <= 2 /\
  ((LOCV = 2 /\ B0 <= LLO /\ LEND + 32 <= OEND) \/ (LOCV <> 2 /\ ((OEND <= LLO /\ LEND + 32 <= B1) \/ LEND + 32 <= B0 \/ B1 <= LLO))) /\
  (LLT mod 4 = 0 /\ OFT mod 4 = 0 /\ MLT mod 4 = 0 /\ SPV mod 16 = 0) /\ seq_table_ok K_LL tLL /\ seq_table_ok K_OF tOF /\ seq_table_ok K_ML tML.

(* [comment removed for export] *)
Definition seql_ring_bytes (rl rm ro : Z -> Z) : list byte :=
  le8 (Z_to_bv 64 (rl 0)) ++ le8 (Z_to_bv 64 (rm 0)) ++ le8 (Z_to_bv 64 (ro 0)) ++
  le8 (Z_to_bv 64 (rl 1)) ++ le8 (Z_to_bv 64 (rm 1)) ++ le8 (Z_to_bv 64 (ro 1)) ++
  le8 (Z_to_bv 64 (rl 2)) ++ le8 (Z_to_bv 64 (rm 2)) ++ le8 (Z_to_bv 64 (ro 2)) ++
  le8 (Z_to_bv 64 (rl 3)) ++ le8 (Z_to_bv 64 (rm 3)) ++ le8 (Z_to_bv 64 (ro 3)) ++
  le8 (Z_to_bv 64 (rl 4)) ++ le8 (Z_to_bv 64 (rm 4)) ++ le8 (Z_to_bv 64 (ro 4)) ++
  le8 (Z_to_bv 64 (rl 5)) ++ le8 (Z_to_bv 64 (rm 5)) ++ le8 (Z_to_bv 64 (ro 5)) ++
  le8 (Z_to_bv 64 (rl 6)) ++ le8 (Z_to_bv 64 (rm 6)) ++ le8 (Z_to_bv 64 (ro 6)) ++
  le8 (Z_to_bv 64 (rl 7)) ++ le8 (Z_to_bv 64 (rm 7)) ++ le8 (Z_to_bv 64 (ro 7)).

(* [comment removed for export] *)
Definition seql_frame (P : slp) (OEND : Z) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (jpad jseq : list byte) : list cell := let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 (Z_to_bv 64 (- (SPV - 352) - 1)); C8 c40; C8 c48; C8 (Z_to_bv 64 DCTX); C8 c64; C8 c72; C8 (Z_to_bv 64 (Z.min nbSeq 8)); C8 (Z_to_bv 64 (SPV - 344)); C8 (Z_to_bv 64 DST); C8 c104; C8 dend; C8 (Z_to_bv 64 PFX); C8 c128; C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 BITMASK); C8 c152; C8 (Z_to_bv 64 OEND); C8 c168; C8 c176; C8 c184; C8 (Z_to_bv 64 nbSeq); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (DCTX + 29896)); C8 c216; C8 c224; C8 c232; C8 c240; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 LP); CB 24 jseq;
   CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].

(* [comment removed for export] *)
Definition seql_linv (P : slp) (OEND LLO LEND LOCV : Z) (m1 : fmem) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) : Prop :=
  (exists jpad jseq, rw_cells usegs m1 (y_SPV P + -688) (seql_frame P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq)) /\
  bytes_at usegs m1 (y_LLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tLL P))) /\
  bytes_at usegs m1 (y_OFT P) (map (Z_to_bv 8) (seq_table_bytes (y_tOF P))) /\
  bytes_at usegs m1 (y_MLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tML P))) /\
  bytes_at usegs m1 (y_SEQ P) (map (Z_to_bv 8) (y_sq P)) /\
  rdbl usegs m1 LLO (LEND + 32) /\
  (LOCV = 2 -> rdbl usegs m1 (y_DCTX P + 30372) (y_DCTX P + 95940)) /\
  h5_viewed m1 (y_DCTX P) (y_ws P) (Z_to_bv 64 LOCV) /\
  seql_xinv P m1 (seql_fe P).

(* [comment removed for export] *)
Definition seql_lfacts (P : slp) (OEND LLO LEND BND OP LP bc ptr sLL sOF sML : Z) : Prop :=
  y_DST P <= OP <= OEND /\ LLO <= LP <= LEND /\
  0 <= sLL < 2^(st_log (y_tLL P)) /\ 0 <= sOF < 2^(st_log (y_tOF P)) /\ 0 <= sML < 2^(st_log (y_tML P)) /\
  0 <= bc <= BND /\ bit_ok (y_SEQ P) (zlen (y_sq P)) bc ptr.

(* [comment removed for export] *)
Definition seql_next (P : slp) (nLL bLL nOF bOF nML bML : Z) : Prop :=
  0 <= bLL <= 9 /\ 0 <= nLL /\ nLL + 2^bLL <= 2^(st_log (y_tLL P)) /\
  0 <= bOF <= 9 /\ 0 <= nOF /\ nOF + 2^bOF <= 2^(st_log (y_tOF P)) /\
  0 <= bML <= 9 /\ 0 <= nML /\ nML + 2^bML <= 2^(st_log (y_tML P)).

(* [comment removed for export] *)
Definition seql_fast (OEND LEND OP LP llv mlv : Z) : Prop :=
  0 <= llv < 2^18 /\ 0 <= mlv < 2^18 /\ LP + llv <= LEND /\ OP + llv + mlv <= OEND - 32.

(* [comment removed for export] *)
Definition seql_mfast (P : slp) (OEND OP ole mlv sl : Z) : Prop :=
  y_DST P <= OP <= ole /\ 0 <= mlv < 2^18 /\ ole + mlv <= OEND - 32 /\ sl = ole - OP + mlv.

Lemma land7 : forall x, 0 <= Z.land x 7 <= 7.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^3) ltac:(lia)). change (Z.ones 3) with 7. change (2^3) with 8 in *. lia. Qed.

(* [comment removed for export] *)
Definition seql_ring_ok (v : Z) (rl rm ro : Z -> Z) : Prop :=
  forall j, 0 <= j < v -> 0 <= rl j < 2^18 /\ 0 <= rm j < 2^18 /\ 0 <= ro j < 2^64.
