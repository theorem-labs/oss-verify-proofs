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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_iinv (P : ssq) (OEND LLO LEND LOCV : Z) (m1 : amem) (fr ff : list cell) : Prop :=
  rw_cells bsegs m1 (v_FRB P) fr /\ rw_cells bsegs m1 (v_FF P) ff /\
  dctx_ptrs bsegs m1 (v_DCTX P) (Z_to_bv 64 (v_LLT P)) (Z_to_bv 64 (v_MLT P)) (Z_to_bv 64 (v_OFT P)) (v_huf P) /\
  bytes_at bsegs m1 (v_LLT P) (map (Z_to_bv 8) (seq_table_bytes (v_tLL P))) /\
  bytes_at bsegs m1 (v_OFT P) (map (Z_to_bv 8) (seq_table_bytes (v_tOF P))) /\
  bytes_at bsegs m1 (v_MLT P) (map (Z_to_bv 8) (seq_table_bytes (v_tML P))) /\
  bytes_at bsegs m1 (v_SEQ P) (map (Z_to_bv 8) (v_sq P)) /\
  rdbl bsegs m1 LLO (LEND + 32) /\
  (LOCV = 2 -> rdbl bsegs m1 (v_DCTX P + 30372) (v_DCTX P + 95940)) /\
  h5_viewed m1 (v_DCTX P) (v_ws P) (Z_to_bv 64 LOCV) /\
  sqs_xinv P m1 (sqs_fe P).

Lemma sqs_iinv_mi : forall P OEND LLO LEND LOCV m1 fr ff, sqs_iinv P OEND LLO LEND LOCV m1 fr ff -> mem_inv bsegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. cbn [sqs_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma sqs_iinv_frame : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  forall m2 fr2 ff2,
  munch [(v_FRB P, v_FRB P + 280); (v_FF P, v_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (v_FRB P) fr2 -> rw_cells bsegs m2 (v_FF P) ff2 ->
  sqs_iinv P OEND LLO LEND LOCV m2 fr2 ff2.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV m2 fr2 ff2 MUL WML MI2 FR FRF.
  destruct INV as (_ & _ & PT & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exact FR|]. split; [exact FRF|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_FRB v_FF v_LLT v_OFT v_MLT v_SEQ v_sq v_tLL v_tOF v_tML v_DCTX v_ws v_huf] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]|].
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
Lemma sqs_iinv_step : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  forall m2 fr2 ff2 CS, 0 <= CS <= 4304 ->
  munch [(v_FRB P - CS, v_FRB P); (v_FRB P, v_FRB P + 280); (v_FF P, v_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  stk bsegs m2 (v_lo P) (v_FRB P) ->
  rw_cells bsegs m2 (v_FRB P) fr2 -> rw_cells bsegs m2 (v_FF P) ff2 ->
  sqs_iinv P OEND LLO LEND LOCV m2 fr2 ff2.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV m2 fr2 ff2 CS HCS MUL WML MI2 STK2 FR FRF.
  destruct INV as (_ & _ & PT & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exact FR|]. split; [exact FRF|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_FRB v_FF v_LLT v_OFT v_MLT v_SEQ v_sq v_tLL v_tOF v_tML v_DCTX v_ws v_huf v_lo] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 S47 HCS LLL; lia| split; [clear - S28 S18 S47 LLL; lia| split; [clear - S58 LLL; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 S47 HCS LOF; lia| split; [clear - S29 S18 S47 LOF; lia| split; [clear - S59 LOF; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 S47 HCS LML; lia| split; [clear - S30 S18 S47 LML; lia| split; [clear - S60 LML; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18 S47 HCS; lia| split; [clear - S25 S18 S47; lia| split; [clear - S56; lia|exact I]]]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 S47 HCS Hx; lia| split; [clear - S26 S18 S47 Hx; lia| split; [clear - S57 Hx; lia|exact I]]]]|].
  split; [intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S27 S18 S47 HCS Hx; lia| split; [clear - S27 S18 S47 Hx; lia| split; [clear - S54 Hx; lia|exact I]]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18 S47 HCS; lia| split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18 S47 HCS; lia| split; [clear - S24 S18 S47; lia| split; [clear - S55; lia|exact I]]]]|].
  split; [exact STK2|].
  split; [eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S47 HCS; lia| split; [clear - S47; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - HCS; lia| split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact SHS | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S53 S18 S47 HCS; lia| split; [clear - S53 S18 S47; lia| split; [clear - S49 S52 S53; lia|exact I]]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx S47 S18 HCS; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma sqs_iopen_k : forall P OEND LLO LEND LOCV m1 fr ff,
  sqs_static P OEND LLO LEND LOCV -> sqs_iinv P OEND LLO LEND LOCV m1 fr ff ->
  forall Q : Prop,
  (rw_cells bsegs m1 (v_FRB P) fr ->
   rw_cells bsegs m1 (v_FF P) ff ->
   dctx_ptrs bsegs m1 (v_DCTX P) (Z_to_bv 64 (v_LLT P)) (Z_to_bv 64 (v_MLT P)) (Z_to_bv 64 (v_OFT P)) (v_huf P) ->
   bytes_at bsegs m1 (v_SEQ P) (map (Z_to_bv 8) (v_sq P)) ->
   mem_inv bsegs m1 ->
   unpoisoned m1 (v_FF P + 32) (v_FF P + 32 + 112) ->
   unpoisoned m1 (v_SEQ P) (v_SEQ P + zlen (v_sq P)) -> rng (v_RNG P) (v_SEQ P) (zlen (v_sq P)) ->
   rng (v_RNG P) (shad (v_SEQ P)) (shspan (v_SEQ P) (zlen (v_sq P))) ->
   unpoisoned m1 (v_DCTX P) (v_DCTX P + DCTX_SIZEOF) -> rng (v_RNG P) (v_DCTX P) DCTX_SIZEOF ->
   rng (v_RNG P) (shad (v_DCTX P)) (shspan (v_DCTX P) DCTX_SIZEOF) -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ff ST INV Q K.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  destruct INV as (FR & FRF & PT & _ & _ & _ & SQB & _ & _ & _ & XI).
  assert (AS : sqs_asan P m1).
  { eapply (sqs_asan_transport P OEND LLO LEND LOCV m1 ST);
      destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1];
      cbn [sqs_xinv sqs_Wb v_m] in *; destruct XI as (_ & _ & _ & _ & _ & _ & _ & MU & WM & _); [exact MU | exact WM]. }
  assert (UFL : unpoisoned m1 (v_FF P + 32) (v_FF P + 32 + 112)).
  { destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [sqs_xinv sqs_astat v_FF] in *. pose proof ST as ST1. sd_static_open ST. destruct XI as (_ & _ & _ & _ & _ & _ & SHS & _).
    destruct S61 as (_ & _ & _ & _ & _ & _ & _ & FFa & FFb & FFc & ESHF & _). unfold AIMG_HI in FFa. unfold held in S49.
    eapply sqs_fsh_unp; [exact SHS | rewrite ESHF, shad_div; reflexivity | clear - FFc; Z.div_mod_to_equations; lia | lia | clear - S49 S50 S18 S17; lia]. }
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan v_FRB v_FF v_DCTX v_LLT v_MLT v_OFT v_huf v_SEQ v_sq v_RNG] in *.
  pose proof ST as ST1. sd_static_open ST.
  destruct AS as (ARD & _ & ARS & _).
  destruct (ARS ltac:(clear - S15; lia)) as (_ & USQ & RSQ & RSQS).
  destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (_ & UD & RD & RDS).
  exact (K FR FRF PT SQB MI UFL USQ RSQ RSQS UD RD RDS).
Qed.

(* [comment removed for export] *)
Lemma sqs_iinv_linv : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_frame P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP jseq) (sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq (FR & FRF & _ & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|].
  split; [exact TLL|]. split; [exact TOF|]. split; [exact TML|]. split; [exact SQB|]. split; [exact LIT|]. split; [exact XLIT|]. split; [exact H5 | exact XI].
Qed.

End CANSEC1.
