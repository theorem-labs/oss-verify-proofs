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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sd_static_open ST := destruct ST as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 S18 S19 S20
  S21 S22 S23 S24 S25 S26 S27 S28 S29 S30 S31 S32 S33 S34 S35 S36 S37 S38 S39 S40
  S41 S42 S43 S44 S45 S46 S47 S48 S49 S50 S51 S52 S53 S54 S55 S56 S57 S58 S59 S60
  S61 S62 S63 S64 S65 S66 S67 S68 S69 OKLL OKOF OKML];
  cbv beta iota zeta in S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20,
  S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40,
  S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60,
  S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML;
  repeat match goal with H : _ \/ _ |- _ => hold H end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqd_linv_mi : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP -> mem_inv bsegs m1.
Proof.
  intros until LP. intros (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. cbn [sqd_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma sqd_linv_frame : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(w_FRB P, w_FRB P + 216); (w_FF P, w_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (w_FRB P) (sqd_frame P OEND c24' c32' c40' c200' c208' c216' LP' jseq) ->
  rw_cells bsegs m2 (w_FF P) (sqd_ffr P cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  sqd_linv P OEND LLO LEND LOCV m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV
         m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MUL WML MI2 FR FRF.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_xinv w_FRB w_FF w_LLT w_OFT w_MLT w_SEQ w_sq w_tLL w_tOF w_tML w_DCTX w_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 S47 LLL; lia| split; [clear - S58 LLL; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 S47 LOF; lia| split; [clear - S59 LOF; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 S47 LML; lia| split; [clear - S60 LML; lia|exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18 S47; lia| split; [clear - S56; lia|exact I]]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 S47 Hx; lia| split; [clear - S57 Hx; lia|exact I]]]|].
  split; [intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S27 S18 S47 Hx; lia| split; [clear - S54 Hx; lia|exact I]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18 S47; lia| split; [clear - S55; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S47; lia| split; [clear - S50 S18 S47; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MUL | exact WML | cbn [disjoint_from]; split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact SHS | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S53 S18 S47; lia| split; [clear - S49 S52 S53; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx S47; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Definition sqd_cellfacts (P : sqp) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) : Prop :=
  sqd_next P nLL bLL nOF bOF nML bML /\
  nLL < 512 /\ nOF < 512 /\ nML < 512 /\
  0 <= aLL <= 16 /\ 0 <= aOF <= 31 /\ 0 <= aML <= 16 /\
  0 <= vLL /\ vLL + 2^aLL <= 2^17 /\ 0 <= vML /\ vML + 2^aML <= 2^17 + 3 /\ 0 <= vOF /\ vOF + 2^aOF <= 2^32 - 2 /\
  (aOF = 0 -> vOF = 0) /\ (aOF = 1 -> vOF = 1).

Lemma sqd_linv_cells : forall P OEND LLO LEND LOCV BND m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML ->
  exists nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
    (rdn bsegs m1 (wa (w_LLT P + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) /\
     rdn bsegs m1 (wa (w_LLT P + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) /\
     rdn bsegs m1 (wa (w_LLT P + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) /\
     rdn bsegs m1 (wa (w_LLT P + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL))) /\
    (rdn bsegs m1 (wa (w_OFT P + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) /\
     rdn bsegs m1 (wa (w_OFT P + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) /\
     rdn bsegs m1 (wa (w_OFT P + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) /\
     rdn bsegs m1 (wa (w_OFT P + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF))) /\
    (rdn bsegs m1 (wa (w_MLT P + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) /\
     rdn bsegs m1 (wa (w_MLT P + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) /\
     rdn bsegs m1 (wa (w_MLT P + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) /\
     rdn bsegs m1 (wa (w_MLT P + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML))) /\
    sqd_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML.
Proof.
  intros P OEND LLO LEND LOCV BND m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ST INV LF.
  destruct INV as (_ & TLL & TOF & TML & _). destruct LF as (_ & _ & L3 & L4 & L5 & _).
  assert (OKS : seq_table_ok K_LL (w_tLL P) /\ seq_table_ok K_OF (w_tOF P) /\ seq_table_ok K_ML (w_tML P)).
  { destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. cbn [w_tLL w_tOF w_tML] in *. sd_static_open ST. auto. }
  destruct OKS as (OKLL & OKOF & OKML). clear ST.
  destruct (seq_cell_know bsegs m1 _ K_LL _ TLL OKLL sLL L3) as (A0 & A1 & A2 & A3 & (CA1 & CA2 & CA3 & SYA)).
  destruct (seq_cell_know bsegs m1 _ K_OF _ TOF OKOF sOF L4) as (B0 & B1 & B2 & B3 & (CB1 & CB2 & CB3 & SYB)).
  destruct (seq_cell_know bsegs m1 _ K_ML _ TML OKML sML L5) as (C0 & C1 & C2 & C3 & (CC1 & CC2 & CC3 & SYC)).
  pose proof (sym_ok_kind_bounds K_LL _ SYA) as (YA1 & YA2 & YA3 & _).
  pose proof (sym_ok_kind_bounds K_OF _ SYB) as (YB1 & YB2 & YB3 & YB4 & YB5 & _).
  pose proof (sym_ok_kind_bounds K_ML _ SYC) as (YC1 & YC2 & YC3 & _).
  pose proof (seq_tl_range K_LL _ OKLL) as TA. pose proof (seq_tl_range K_OF _ OKOF) as TB. pose proof (seq_tl_range K_ML _ OKML) as TC.
  assert (PA : 2^(st_log (w_tLL P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PB : 2^(st_log (w_tOF P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PC : 2^(st_log (w_tML P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (QA : 0 < 2^(ss_nbBits (st_cell (w_tLL P) sLL))) by (apply Z.pow_pos_nonneg; lia).
  assert (QB : 0 < 2^(ss_nbBits (st_cell (w_tOF P) sOF))) by (apply Z.pow_pos_nonneg; lia).
  assert (QC : 0 < 2^(ss_nbBits (st_cell (w_tML P) sML))) by (apply Z.pow_pos_nonneg; lia).
  do 12 eexists. split; [repeat split; eassumption|]. split; [repeat split; eassumption|]. split; [repeat split; eassumption|].
  unfold sqd_cellfacts, sqd_next. repeat split; try eassumption; try lia.
Qed.

Lemma sqd_lfacts_bc : forall P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML,
  sqd_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> bc <= bc' <= B' ->
  sqd_lfacts P OEND LLO LEND B' OP LP bc' ptr sLL sOF sML.
Proof.
  intros P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) H.
  repeat (split; [assumption|]). split; [lia|]. eapply bit_ok_mono; [exact L7| lia].
Qed.

Lemma sqd_lfacts_lp : forall P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML,
  sqd_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> LLO <= LP' <= LEND ->
  sqd_lfacts P OEND LLO LEND B OP LP' bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML (L1 & L2 & L) H. split; [exact L1|]. split; [exact H| exact L]. Qed.

(* [comment removed for export] *)
Definition sqd_fr_k1 (P : sqp) (OEND : Z) : list cell :=
  [C8 (Z_to_bv 64 (2147450880 + w_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + w_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + w_D8 P + 3335));
   C8 (Z_to_bv 64 (w_DCTX P + 26692)); C8 (Z_to_bv 64 (w_DCTX P + 26688)); C8 (Z_to_bv 64 (w_DCTX P + 26684))].
Definition sqd_fr_k2 (P : sqp) (OEND : Z) : list cell :=
  [C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (w_FF P)); C8 (w_dend P); C8 (Z_to_bv 64 (w_PFX P)); C8 (Z_to_bv 64 (w_FF P + 120)); C8 (Z_to_bv 64 (w_FF P));
   C8 (Z_to_bv 64 (w_DST P))].
Definition sqd_fr_k3 (P : sqp) (OEND : Z) (c200 : word) : list cell := [C8 c200; C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 (w_PFX P))].
Definition sqd_fr_k4 (P : sqp) (LP : Z) (jseq : list byte) : list cell := [CB 16 (w_j224 P); C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 LP); CB 24 jseq].
Lemma sqd_frame_split : forall P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq =
  sqd_fr_k1 P OEND ++ sqd_fr_k2 P OEND ++ [C8 (Z_to_bv 64 0x22180)] ++ sqd_fr_k3 P OEND c200 ++ [C8 c24; C8 c208; C8 c216] ++ sqd_fr_k4 P LP jseq.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.
Lemma length_le8' : forall w, length (le8 w) = 8%nat. Proof. intros w. reflexivity. Qed.
Lemma sqd_fr_k1_len : forall P OEND, length (cells_bytes (sqd_fr_k1 P OEND)) = 48%nat.
Proof. intros. reflexivity. Qed.
Lemma sqd_fr_k2_len : forall P OEND, length (cells_bytes (sqd_fr_k2 P OEND)) = 56%nat.
Proof. intros. reflexivity. Qed.
Lemma sqd_fr_k3_len : forall P OEND c200, length (cells_bytes (sqd_fr_k3 P OEND c200)) = 24%nat.
Proof. intros. reflexivity. Qed.
Lemma sqd_fr_k4_len : forall P LP jseq, length (w_j224 P) = 16%nat -> length jseq = 24%nat -> length (cells_bytes (sqd_fr_k4 P LP jseq)) = 56%nat.
Proof. intros P LP jseq L16 LJ. unfold sqd_fr_k4. cbn [cells_bytes cbytes]. rewrite !length_app, L16, LJ. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sqd_fr_wf : forall (mm : amem) A P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  rw_cells bsegs mm A (sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq) ->
  length (w_j224 P) = 16%nat /\ length jseq = 24%nat.
Proof.
  intros mm A P OEND c24 c32 c40 c200 c208 c216 LP jseq [(WF & _) _]. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_frame cells_wf cell_wf w_j224] in *.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L16 & _ & _ & L24 & _).
  split; assumption.
Qed.
(* [comment removed for export] *)
Definition sqd_fr_view (P : sqp) (OEND : Z) (c24 c32 c40 c200 c208 c216 : word) (LP : Z) (jseq : list byte) : list cell :=
  [CB 48 (cells_bytes (sqd_fr_k1 P OEND)); CB 56 (cells_bytes (sqd_fr_k2 P OEND)); C8 (Z_to_bv 64 0x22180);
   CB 24 (cells_bytes (sqd_fr_k3 P OEND c200)); C8 c24; C8 c208; C8 c216; CB 56 (cells_bytes (sqd_fr_k4 P LP jseq))].
Lemma sqd_fr_v128 : forall (mm : amem) P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  rw_cells bsegs mm (w_FRB P) (sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq) ->
  rw_cells bsegs mm (w_FRB P) (sqd_fr_view P OEND c24 c32 c40 c200 c208 c216 LP jseq).
Proof.
  intros mm P OEND c24 c32 c40 c200 c208 c216 LP jseq H. destruct (sqd_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ H) as (L16 & LJ).
  rewrite sqd_frame_split in H. unfold sqd_fr_view. eapply rw_cells_recell; [exact H| |].
  - cbn [cells_wf cell_wf]. rewrite (sqd_fr_k1_len P OEND), (sqd_fr_k2_len P OEND), (sqd_fr_k3_len P OEND c200), (sqd_fr_k4_len _ _ _ L16 LJ). repeat split; assumption.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r, ?app_assoc. reflexivity.
Qed.
Lemma sqd_fr_u128 : forall (mm : amem) P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  rw_cells bsegs mm (w_FRB P) (sqd_fr_view P OEND c24 c32 c40 c200 c208 c216 LP jseq) ->
  length (w_j224 P) = 16%nat -> length jseq = 24%nat ->
  rw_cells bsegs mm (w_FRB P) (sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq).
Proof.
  intros mm P OEND c24 c32 c40 c200 c208 c216 LP jseq H L16 LJ. rewrite sqd_frame_split. unfold sqd_fr_view in H. eapply rw_cells_recell; [exact H| |].
  - rewrite !cells_wf_app. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [sqd_fr_k1 sqd_fr_k2 sqd_fr_k3 sqd_fr_k4 cells_wf cell_wf w_j224 app] in *. repeat split; assumption.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r, ?app_assoc. reflexivity.
Qed.

End CANSEC1.
