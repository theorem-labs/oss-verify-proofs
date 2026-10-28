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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2 AZ_seq_s_tkit2 AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_last AZ_seq_s_xat AZ_seq_s_exit AZ_seq_s_xkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqs_fr_vlast : forall (mm : amem) A (j0 j224 jseq : list byte) (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : word),
  length j224 = 16%nat ->
  rw_cells bsegs mm A [CB 16 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13;
                      C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19; C8 w20; C8 w21; C8 w22; C8 w23; C8 w24; C8 w25; C8 w26; CB 16 j224; C8 w27; C8 w28; CB 24 jseq] ->
  rw_cells bsegs mm A [CB 72 (cells_bytes [CB 16 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7]); C8 w8; C8 w9; CB 48 (cells_bytes [C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15]); C8 w16; C8 w17;
                      CB 40 (cells_bytes [C8 w18; C8 w19; C8 w20; C8 w21; C8 w22]); C8 w23; CB 48 (cells_bytes [C8 w24; C8 w25; C8 w26; CB 16 j224; C8 w27]); C8 w28; CB 24 jseq].
Proof.
  intros until w28. intros L224 H.
  eapply rw_cells_recell; [exact H| |].
  - pose proof H as [(WF & _) _]. cbn [cells_wf cell_wf] in WF |- *.
    destruct WF as (L0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L24 & _).
    cbn [cells_bytes cbytes]. rewrite !length_app, L224, L0. cbn. repeat split; try reflexivity. exact L24.
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqs_rep_asan : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DCTX P = 8 * v_D8 P /\
  rdn bsegs m1 (wa (2147450880 + v_D8 P + 3335)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rdn bsegs m1 (wa (2147450880 + v_D8 P + 3336)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng (v_RNG P) (2147450880 + v_D8 P + 3335) 2 /\ rng (v_RNG P) (v_DCTX P + 26684) 12 /\
  ((6443008 <= v_DCTX P /\ v_DCTX P + 95992 <= 2147446784) \/ (17594333495296 <= v_DCTX P /\ v_DCTX P + 95992 <= ATOP)) /\
  ((6443008 <= LLO /\ LEND + 32 <= 2147446784) \/ (17594333495296 <= LLO /\ LEND + 32 <= ATOP)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  pose proof (sqs_asan_now P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan sqs_astat v_DCTX v_D8 v_RNG] in *. AZ_seq_s_lkit.sd_static_open ST.
  destruct AS as (ARD & _ & _ & _ & _ & AOUT & ARL & _).
  destruct S61 as (_ & _ & _ & _ & ED8 & _).
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in *.
  destruct (ARD ltac:(clear; lia)) as (BD & UD & RD1 & RD2). pose proof (ablk_lits _ _ BD) as BDL.
  assert (Z0 : m1 (wa (shad (DCTX + 26684))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m1 DCTX 95992); [exact UD | clear; lia | clear - ED8; Z.div_mod_to_equations; lia]).
  assert (Z1 : m1 (wa (shad (DCTX + 26688))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m1 DCTX 95992); [exact UD | clear; lia | clear - ED8; Z.div_mod_to_equations; lia]).
  rewrite shad_div in Z0, Z1. unfold ASHOFF in Z0, Z1.
  replace ((DCTX + 26684) / 8) with (D8 + 3335) in Z0 by (clear - ED8; Z.div_mod_to_equations; lia).
  replace ((DCTX + 26688) / 8) with (D8 + 3336) in Z1 by (clear - ED8; Z.div_mod_to_equations; lia).
  split; [exact ED8|].
  split; [cbn [rdn]; replace (2147450880 + D8 + 3335) with (2147450880 + (D8 + 3335)) by lia; rewrite Z0; reflexivity|].
  split; [cbn [rdn]; replace (2147450880 + D8 + 3336) with (2147450880 + (D8 + 3336)) by lia; rewrite Z1; reflexivity|].
  split; [eapply rng_sub'; [exact RD2 |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - ED8; Z.div_mod_to_equations; lia|].
  split; [eapply rng_sub'; [exact RD1 | clear; lia]|].
  split; [exact BDL |].
  (* [comment removed for export] *)
  unfold held in S42. unfold held in S73. unfold held in S4. unfold held in S5. unfold held in S6. unfold held in S1. unfold held in S2. unfold held in S3.
  destruct (Z.eq_dec LOCV 2) as [E2|N2].
  - assert (BB : B0 < B1) by (clear - S42 E2 S1 S2 S3 S4 S5 S6 S8 S10; lia).
    destruct (AOUT BB) as (AO & _). destruct (AO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
    clear - BOL S42 E2 S4 S5 S6. lia.
  - destruct (S73 N2) as (_ & EL1 & EL2). subst LLO LEND. clear - BDL. lia.
Qed.

Lemma sqs_lexit_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV -> sqs_at_err P OEND LLO LEND LOCV -> sqs_at_err4 P OEND LLO LEND LOCV -> sqs_at_last P -> sqs_at_lexit P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST ERRK ERRK4 LASTK.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold sqs_at_lexit. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1].
  intros m1 c0 c8 c152 c160 c168 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x24 x25 x26 x28 x29 x30 INV HOP HLP HBC.
  unfold sqs_at_err in ERRK. unfold sqs_at_err4 in ERRK4. unfold sqs_at_last, sqs_fe in LASTK. cbn [sqs_saved sqs_Wb v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in ERRK, ERRK4, LASTK. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, DCTX_SIZEOF, dctx_h3 in LASTK.
  pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sqs_linv_frame _ _ _ _ _ m1 c0 c8 c152 c160 c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in TRANS.
  pose proof (sqs_rep_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as RA. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in RA. destruct RA as (ED8 & RZ0 & RZ1 & RSR & RRP & BDL & BLL).
  pose proof (sqs_dctx_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (UD & RD & RSD & _). cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in UD, RD, RSD.
  pose proof (sqs_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS1. cbn [sqs_asan v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in AS1. destruct AS1 as (ARD1 & _). unfold DCTX_SIZEOF in ARD1.
  pose proof (sqs_loc_shadow RNG m1 DCTX D8 ARD1 ED8) as RZ2. clear ARD1.
  apply (sqs_lopen_k _ _ _ _ _ m1 c0 c8 c152 c160 c168 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqs_frame sqs_ffr v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqs_frame sqs_ffr] in FR, FRF. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in FR, FRF.
  apply (sqs_rg_k _ _ _ _ _ ST); cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & LIT & XLIT & (H5V & H5L) & XI). cbn [sqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in XI, LIT, XLIT, H5V, H5L. unfold sqs_fe in XI. cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in XI.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3, h5_vcells in REP, HH3, MU, H5V |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  AZ_seq_s_lkit.sd_static_open ST. unfold held in RGB.
  unfold held in S61. destruct S61 as (AST & _). destruct AST as (AST1 & _).
  assert (MUL : munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (MUX : munch [(SHF, SHF + 32); (DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sqs_blob_all SHS.
  assert (RG : 512 <= D8 /\ D8 + 11999 < 2^44 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= bc <= 2147483647 /\ 4096 <= SEQ < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47)
    by (clear - ED8 S19 S20 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S13 S14 S15 HOP HLP HBC; lia).
  destruct RG as (RG1 & RG1b & RG2 & RG2b & RG3 & RG4 & RG5 & RG6 & RG7 & RG8).
  pose proof (bytes_at_sh2 m1 _ _ _ _ _ _ eq_refl eq_refl RZ0 RZ1 ltac:(clear; lia) ltac:(clear - RG1; lia) ltac:(clear - RG1b; lia)) as RDS.
  lazymatch type of RDS with bytes_at _ _ _ (?b0 :: ?b1 :: nil) =>
    assert (RDC : ro_cells bsegs m1 (2147450880 + D8 + 3335) [C1 b0; C1 b1]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS]) end.
  clear RDS.
  pose proof (bytes_at_sh1 m1 _ _ _ eq_refl RZ2 ltac:(clear - RG1; lia) ltac:(clear - RG1b; lia)) as RDS.
  lazymatch type of RDS with bytes_at _ _ _ (?b :: nil) =>
    assert (RDC1 : ro_cells bsegs m1 (2147450880 + D8 + 3796) [C1 b]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS]) end.
  clear RDS.
  assert (RT1 : rng RNG (2147450880 + D8 + 3796) 1) by (eapply rng_sub'; [exact RSD |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - ED8; Z.div_mod_to_equations; lia).
  pose proof atop_range as ATR.
  (* [comment removed for export] *)
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 ptr)) in FRF. pose proof (kx_u64_range (Z_to_bv 64 ptr)) as HPT.
  remember (bv_unsigned (Z_to_bv 64 ptr)) as ptz eqn:Eptz. clear Eptz.
  (* [comment removed for export] *)
  assert (KD1 : DCTX + 26684 + 12 <= FRB \/ FRB + 280 <= DCTX + 26684) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (KD2 : DCTX + 26684 + 12 <= FF \/ FF + 256 <= DCTX + 26684) by (unfold held in S54; clear - S54; lia).
  assert (KD3 : DCTX + 26684 + 12 <= SHF \/ SHF + 32 <= DCTX + 26684) by (unfold held in BDL; clear - BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia).
  assert (KD4 : DCTX + 26684 + 12 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 2 <= DCTX + 26684) by (unfold held in BDL; clear - BDL ED8 ATR; lia).
  assert (KD5 : SHF + 32 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 2 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (KD6 : SHF + 32 <= FF \/ FF + 256 <= SHF) by (clear - RGB RGC1 RGA2; lia).
  assert (KD7 : SHF + 32 <= FRB \/ FRB + 280 <= SHF) by (clear - RGC1 RGA2 RGA1 RGA7 RGA8; lia).
  assert (KD8 : DCTX + 26684 + 12 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= DCTX + 26684) by (unfold held in BDL; clear - BDL ED8 ATR; lia).
  assert (KD9 : SHF + 32 <= 2147450880 + D8 + 3796 \/ 2147450880 + D8 + 3796 + 1 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (KD10 : FRB + 280 <= DCTX + 30096 \/ DCTX + 30096 + 276 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (KD11 : FF + 256 <= DCTX + 30096 \/ DCTX + 30096 + 276 <= FF) by (unfold held in S54; clear - S54; lia).
  (* [comment removed for export] *)
  assert (RSH1 : 2147450880 <= SHF) by (clear - RGC1 RGA2; lia). assert (RSH2 : SHF + 32 <= 17594333495296) by (unfold held in S53; clear - S53; lia).
  (* [comment removed for export] *)
  subst DCTX.
  try hold ERRK. try hold ERRK4. try hold LASTK. try hold TRANS. try hold MUL. try hold HH3. try hold LIT. try hold XLIT. try hold H5V. try hold MU. try hold WM. try hold BDL. try hold BLL. try hold L16F. try hold LJF. try hold HOP. try hold HLP. try hold ST0. try hold INV0. try hold BUF. try hold STK. try hold GAP. try hold SAV. try hold AST1. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold S72. try hold S73.
  (* [comment removed for export] *)
  all: (revert RG1 RG1b RG2 RG2b RG3 RG4 RG5 RG6 RG7 RG8 RSH1 RSH2 HPT S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB; rhold_arith; intros RG1 RG1b RG2 RG2b RG3 RG4 RG5 RG6 RG7 RG8 RSH1 RSH2 HPT S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB).
  kx_autoFLA (FR, FRF, REP, RDC, RDC1) [] [0x91fa0; 0x8f668] 140%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 384);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 (17594333495296 - 32);
     KZRange D8 512 (2^44 - 11999);
     KZRange OP 4096 (2^47);
     KZRange OEND 4096 (2^47);
     KZRange LEND 4096 (2^47);
     KZRange LP 4096 (2^47);
     KZRange bc 0 2147483647;
     KZRange SEQ 4096 (2^47);
     KZRange ptz 0 (2^64 - 1);
     KZWord (2147450880 + D8 + 3335) 1 0;
     KZWord (2147450880 + D8 + 3336) 1 0;
     KZWord (2147450880 + D8 + 3796) 1 0;
     KZWr FRB 280;
     KZWr FF 256;
     KZDisj FF 256 FRB 280;
     KZWr SHF 32;
     KZWr (8 * D8 + 26684) 12;
     KZDisj SHF 32 FRB 280;
     KZDisj SHF 32 FF 256;
     KZDisj (8 * D8 + 26684) 12 FRB 280;
     KZDisj (8 * D8 + 26684) 12 FF 256;
     KZDisj (8 * D8 + 26684) 12 SHF 32;
     KZDisj (8 * D8 + 26684) 12 (2147450880 + D8 + 3335) 2;
     KZDisj SHF 32 (2147450880 + D8 + 3335) 2;
     KZDisj (8 * D8 + 26684) 12 (2147450880 + D8 + 3796) 1;
     KZDisj SHF 32 (2147450880 + D8 + 3796) 1]
    [(FRB, 280); (FF, 256); (2147450880 + D8 + 3335, 2); (2147450880 + D8 + 3796, 1)]
    [(FRB, 280); (FF, 256); (SHF, 32); (8 * D8 + 26684, 12)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try sqs_aclose.
  all: kx_mem.
  all: runhold_off.
  all: (try unfold held in ERRK; try unfold held in ERRK4; try unfold held in LASTK; try unfold held in TRANS; try unfold held in MUL; try unfold held in HH3; try unfold held in LIT; try unfold held in XLIT; try unfold held in H5V; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in BLL; try unfold held in L16F; try unfold held in LJF; try unfold held in HOP; try unfold held in HLP; try unfold held in ST0; try unfold held in INV0; try unfold held in BUF; try unfold held in STK; try unfold held in GAP; try unfold held in SAV; try unfold held in AST1; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in S72; try unfold held in S73; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x91fa0) _ _ _ _) =>
         eapply ERRK4; eapply TRANS; [exact MUL | exact WMl | assumption | exact FR | exact FRF]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8f668) _ _ ?mx _) =>
         (* [comment removed for export] *)
         assert (MU2 : munch [(DST, DST + CAP); (8 * D8 + 26684, 8 * D8 + 26684 + 12); (8 * D8 + 30004, 8 * D8 + 30004 + 4); (8 * D8 + 30368, 8 * D8 + 30368 + 4); (SPV - SEQ_SPLIT_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
           by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]);
         assert (WM2 : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WMX]);
         pose proof (sqs_asan_transport (mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo (8 * D8) DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) _ _ _ _ mx ST0 MU2 WM2) as AS2; cbn [sqs_asan v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in AS2;
         destruct AS2 as (ARD & AHD & _ & _ & _ & AOUT & _ & _ & _ & ART2);
         (* [comment removed for export] *)
         assert (BUF' : stk bsegs mx B0 B1) by (eapply stk_transport_disjoint; [exact BUF | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S69; unfold held in S32; clear - S69 S32 S52 RSH2 S68; lia]);
         assert (STK' : stk bsegs mx lo FRB) by (eapply stk_transport_disjoint; [exact STK | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         assert (GAP' : stk bsegs mx (FRB + 280) (SPV + -104)) by (eapply stk_transport_disjoint; [exact GAP | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         assert (SAV' : rw_cells bsegs mx (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (eapply rw_cells_transport; [exact SAV | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; simpl_sizes; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         assert (HH3' : rw_cells bsegs mx (8 * D8 + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 (if nbSeq =? 0 then fe else Z_to_bv 64 1)])
           by (eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; split; [unfold held in BDL; clear - BDL RGC1 RGA1 RGA2 RGA8 RGB; lia|]; split; [clear; lia| exact I]]);
         assert (H5V' : rw_cells bsegs mx (8 * D8 + 30096) [CB 24 (h5_j1 ws); C8 (wnth ws H5_litPtr); CB 24 (h5_j2 ws); C8 (wnth ws H5_litSize); CB 192 (h5_j3 ws); C8 (wnth ws H5_litBuffer); C8 (wnth ws H5_litBufferEnd); C4 (Z_to_bv 64 LOCV)])
           by (eapply rw_cells_transport; [exact H5V | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add]; split; [unfold held in BDL; clear - BDL RGC1 RGA1 RGA2 RGA8 RGB; lia|]; split; [clear; lia| exact I]]);
         assert (LIT' : rdbl bsegs mx LP (LEND + 32))
           by (unfold held in S36; eapply rdbl_transport; [eapply rdbl_sub; [exact LIT | clear - HLP; lia | clear; lia] | exact MUX |];
               intros x Hx; left; cbn [outside]; split; [unfold held in BLL; clear - Hx BLL RGC1 RGA1 RGA2 RGA8 RGB HLP; lia|]; split; [clear - Hx S36 HLP; lia| exact I]);
         assert (XLIT' : LOCV = 2 -> rdbl bsegs mx (8 * D8 + 30372) (8 * D8 + 95940))
           by (intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUX |];
               intros x Hx; left; cbn [outside]; split; [unfold held in BDL; clear - Hx BDL RGC1 RGA1 RGA2 RGA8 RGB; lia|]; split; [clear - Hx; lia| exact I]);
         apply (sqs_fr_vlast mx FRB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L16F) in FR; sqs_blob_last FRF; sqs_blob_all SHS;
         eapply LASTK;
         [ exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | exact HH3' | split; [exact H5V' | exact H5L] | exact BUF' | exact STK' | exact GAP' | exact SAV'
         | exact MU2 | exact WM2 | assumption | exact LIT' | exact XLIT'
         | clear - HOP; lia | clear - HOP; lia | clear - S4 S5; lia
         | (* [comment removed for export] *) unfold held in S71; unfold held in S73; destruct (Z.eq_dec LOCV 2) as [E2|N2];
             [ right; destruct (S71 E2) as (EL1 & EL2 & _); clear - E2 EL1 EL2 HLP; lia | left; destruct (S73 N2) as (EL0 & EL1 & EL2); clear - EL0 EL1 EL2 HLP; lia ]
         | exact ART2 | exact ARD | exact AHD
         | intros BB; destruct (AOUT BB) as (A1 & A2); split; [exact (A1 ltac:(clear - BB; lia)) | exact A2]
         | (* [comment removed for export] *) clear; lia
         | (* [comment removed for export] *) first [reflexivity | (clear; lia) | (clear; Z.div_mod_to_equations; lia)] ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF after the run, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal after the run:" UNEXPECTED
    end.
Qed.

End CANSEC1.
(* [comment removed for export] *)
