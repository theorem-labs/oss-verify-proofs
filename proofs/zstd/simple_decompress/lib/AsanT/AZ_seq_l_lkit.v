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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac sd_static_open ST := destruct ST as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 S18 S19 S20
  S21 S22 S23 S24 S25 S26 S27 S28 S29 S30 S31 S32 S33 S34 S35 S36 S37 S38 S39 S40
  S41 S42 S43 S44 S45 S46 S47 S48 S49 S50 S51 S52 S53 S54 S55 S56 S57 S58 S59 S60
  S61 S62 S63 S64 S65 S66 S67 S68 S69 OKLL OKOF OKML S70 S71];
  cbv beta iota zeta in S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, S20,
  S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40,
  S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60,
  S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML, S70, S71;
  repeat match goal with H : _ \/ _ |- _ => hold H end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_linv_mi : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP -> mem_inv bsegs m1.
Proof.
  intros until LP. intros (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma sql_linv_frame : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq,
  munch [(l_FRB P, l_FRB P + 568); (l_FF P, l_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (l_FRB P) (sql_frame P OEND c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' rl' rm' ro' LP' jseq) ->
  rw_cells bsegs m2 (l_FF P) (sql_ffr P cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  sql_linv P OEND LLO LEND LOCV m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV
         m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq MUL WML MI2 FR FRF.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_xinv l_FRB l_FF l_LLT l_OFT l_MLT l_SEQ l_sq l_tLL l_tOF l_tML l_DCTX l_ws] in *.
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
Definition sql_cellfacts (P : slq) (nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML : Z) : Prop :=
  sql_next P nLL bLL nOF bOF nML bML /\
  nLL < 512 /\ nOF < 512 /\ nML < 512 /\
  0 <= aLL <= 16 /\ 0 <= aOF <= 31 /\ 0 <= aML <= 16 /\
  0 <= vLL /\ vLL + 2^aLL <= 2^17 /\ 0 <= vML /\ vML + 2^aML <= 2^17 + 3 /\ 0 <= vOF /\ vOF + 2^aOF <= 2^32 - 2 /\
  (aOF = 0 -> vOF = 0) /\ (aOF = 1 -> vOF = 1).

Lemma sql_linv_cells : forall P OEND LLO LEND LOCV BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML ->
  exists nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
    (rdn bsegs m1 (wa (l_LLT P + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) /\
     rdn bsegs m1 (wa (l_LLT P + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) /\
     rdn bsegs m1 (wa (l_LLT P + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) /\
     rdn bsegs m1 (wa (l_LLT P + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL))) /\
    (rdn bsegs m1 (wa (l_OFT P + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) /\
     rdn bsegs m1 (wa (l_OFT P + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) /\
     rdn bsegs m1 (wa (l_OFT P + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) /\
     rdn bsegs m1 (wa (l_OFT P + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF))) /\
    (rdn bsegs m1 (wa (l_MLT P + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) /\
     rdn bsegs m1 (wa (l_MLT P + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) /\
     rdn bsegs m1 (wa (l_MLT P + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) /\
     rdn bsegs m1 (wa (l_MLT P + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML))) /\
    sql_cellfacts P nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML.
Proof.
  intros P OEND LLO LEND LOCV BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ST INV LF.
  destruct INV as (_ & TLL & TOF & TML & _). destruct LF as (_ & _ & L3 & L4 & L5 & _).
  assert (OKS : seq_table_ok K_LL (l_tLL P) /\ seq_table_ok K_OF (l_tOF P) /\ seq_table_ok K_ML (l_tML P)).
  { destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [l_tLL l_tOF l_tML] in *. sd_static_open ST. auto. }
  destruct OKS as (OKLL & OKOF & OKML). clear ST.
  destruct (seq_cell_know bsegs m1 _ K_LL _ TLL OKLL sLL L3) as (A0 & A1 & A2 & A3 & (CA1 & CA2 & CA3 & SYA)).
  destruct (seq_cell_know bsegs m1 _ K_OF _ TOF OKOF sOF L4) as (B0 & B1 & B2 & B3 & (CB1 & CB2 & CB3 & SYB)).
  destruct (seq_cell_know bsegs m1 _ K_ML _ TML OKML sML L5) as (C0 & C1 & C2 & C3 & (CC1 & CC2 & CC3 & SYC)).
  pose proof (sym_ok_kind_bounds K_LL _ SYA) as (YA1 & YA2 & YA3 & _).
  pose proof (sym_ok_kind_bounds K_OF _ SYB) as (YB1 & YB2 & YB3 & YB4 & YB5 & _).
  pose proof (sym_ok_kind_bounds K_ML _ SYC) as (YC1 & YC2 & YC3 & _).
  pose proof (seq_tl_range K_LL _ OKLL) as TA. pose proof (seq_tl_range K_OF _ OKOF) as TB. pose proof (seq_tl_range K_ML _ OKML) as TC.
  assert (PA : 2^(st_log (l_tLL P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PB : 2^(st_log (l_tOF P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (PC : 2^(st_log (l_tML P)) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
  assert (QA : 0 < 2^(ss_nbBits (st_cell (l_tLL P) sLL))) by (apply Z.pow_pos_nonneg; lia).
  assert (QB : 0 < 2^(ss_nbBits (st_cell (l_tOF P) sOF))) by (apply Z.pow_pos_nonneg; lia).
  assert (QC : 0 < 2^(ss_nbBits (st_cell (l_tML P) sML))) by (apply Z.pow_pos_nonneg; lia).
  do 12 eexists. split; [repeat split; eassumption|]. split; [repeat split; eassumption|]. split; [repeat split; eassumption|].
  unfold sql_cellfacts, sql_next. repeat split; try eassumption; try lia.
Qed.

Lemma sql_lfacts_bc : forall P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML,
  sql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> bc <= bc' <= B' ->
  sql_lfacts P OEND LLO LEND B' OP LP bc' ptr sLL sOF sML.
Proof.
  intros P OEND LLO LEND B B' OP LP bc bc' ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) H.
  repeat (split; [assumption|]). split; [lia|]. eapply bit_ok_mono; [exact L7| lia].
Qed.

Lemma sql_lfacts_lp : forall P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML,
  sql_lfacts P OEND LLO LEND B OP LP bc ptr sLL sOF sML -> LLO <= LP' <= LEND ->
  sql_lfacts P OEND LLO LEND B OP LP' bc ptr sLL sOF sML.
Proof. intros P OEND LLO LEND B OP LP LP' bc ptr sLL sOF sML (L1 & L2 & L) H. split; [exact L1|]. split; [exact H| exact L]. Qed.

(* [comment removed for export] *)
Lemma sql_ring_len : forall rl rm ro, length (sql_ring_bytes rl rm ro) = 192%nat.
Proof. intros. reflexivity. Qed.
Lemma sql_fr_wf : forall (mm : amem) A P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq,
  rw_cells bsegs mm A (sql_frame P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq) ->
  length (l_j0 P) = 8%nat /\ length (l_j384 P) = 24%nat /\ length jseq = 24%nat.
Proof.
  intros until jseq. intros [(WF & _) _]. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_frame cells_wf cell_wf l_j0 l_j384] in *.
  destruct WF as (L0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L384 & _ & _ & L24 & _).
  repeat split; assumption.
Qed.

End CANSEC1.
