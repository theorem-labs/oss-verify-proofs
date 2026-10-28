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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2 AZ_seq_d_fin AZ_seq_d_last AZ_seq_d_xat.
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

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma bytes_at_sh2 : forall (m : amem) A A1 (l0 l1 : list byte) b0 b1,
  l0 = [b0] -> l1 = [b1] -> rdn bsegs m (wa A) 1 = Some l0 -> rdn bsegs m (wa A1) 1 = Some l1 ->
  A1 = A + 1 -> 0 <= A -> A + 2 <= 2^64 -> bytes_at bsegs m A [b0; b1].
Proof.
  intros m A A1 l0 l1 b0 b1 -> -> H0 H1 -> HA HB. split; [exact HA|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|i]]; [ | | lia].
  - rewrite Z.add_0_r. unfold mrd. cbn [rdn] in H0. cbn [nth_error].
    destruct (m (wa A)) as [b|]; [congruence|]. destruct (seg_rom bsegs (wa A)) as [b|]; congruence.
  - change (A + Z.of_nat 1) with (A + 1). unfold mrd. cbn [rdn] in H1. cbn [nth_error].
    destruct (m (wa (A + 1))) as [b|]; [congruence|]. destruct (seg_rom bsegs (wa (A + 1))) as [b|]; congruence.
Qed.

(* [comment removed for export] *)
Definition sqd_fr_l1 (P : sqp) (OEND : Z) : list cell :=
  sqd_fr_k1 P OEND ++ [C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (w_FF P)); C8 (w_dend P); C8 (Z_to_bv 64 (w_PFX P)); C8 (Z_to_bv 64 (w_FF P + 120))].
Definition sqd_fr_l2 (P : sqp) (OEND : Z) (c200 c24 c208 c216 : word) : list cell :=
  [C8 (Z_to_bv 64 0x22180); C8 c200; C8 (Z_to_bv 64 (OEND - 32)); C8 (Z_to_bv 64 (w_PFX P)); C8 c24; C8 c208; C8 c216; CB 16 (w_j224 P); C8 (Z_to_bv 64 (w_FF P))].
Lemma sqd_frame_split3 : forall P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq =
  sqd_fr_l1 P OEND ++ [C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 (w_DST P))] ++ sqd_fr_l2 P OEND c200 c24 c208 c216 ++ [C8 (Z_to_bv 64 LP); CB 24 jseq].
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.
Lemma sqd_fr_l1_len : forall P OEND, length (cells_bytes (sqd_fr_l1 P OEND)) = 88%nat.
Proof. intros. reflexivity. Qed.
Lemma sqd_fr_l2_len : forall P OEND c200 c24 c208 c216, length (w_j224 P) = 16%nat -> length (cells_bytes (sqd_fr_l2 P OEND c200 c24 c208 c216)) = 80%nat.
Proof. intros P OEND c200 c24 c208 c216 L16. unfold sqd_fr_l2. cbn [cells_bytes cbytes]. rewrite !length_app, L16. reflexivity. Qed.
Lemma sqd_fr_vlast : forall (mm : amem) P OEND c24 c32 c40 c200 c208 c216 LP jseq,
  rw_cells bsegs mm (w_FRB P) (sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq) ->
  rw_cells bsegs mm (w_FRB P) [CB 88 (cells_bytes (sqd_fr_l1 P OEND)); C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 (w_DST P));
                               CB 80 (cells_bytes (sqd_fr_l2 P OEND c200 c24 c208 c216)); C8 (Z_to_bv 64 LP); CB 24 jseq].
Proof.
  intros mm P OEND c24 c32 c40 c200 c208 c216 LP jseq H. destruct (sqd_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ H) as (L16 & LJ).
  rewrite sqd_frame_split3 in H. eapply rw_cells_recell; [exact H| |].
  - cbn [cells_wf cell_wf]. rewrite (sqd_fr_l1_len P OEND), (sqd_fr_l2_len _ _ _ _ _ _ L16). repeat split. exact LJ.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqd_rep_asan : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  w_DCTX P = 8 * w_D8 P /\
  rdn bsegs m1 (wa (2147450880 + w_D8 P + 3335)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rdn bsegs m1 (wa (2147450880 + w_D8 P + 3336)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng (w_RNG P) (2147450880 + w_D8 P + 3335) 2 /\ rng (w_RNG P) (w_DCTX P + 26684) 12 /\
  ((6443008 <= w_DCTX P /\ w_DCTX P + 95992 <= 2147446784) \/ (17594333495296 <= w_DCTX P /\ w_DCTX P + 95992 <= ATOP)) /\
  ((6443008 <= LLO /\ LEND + 32 <= 2147446784) \/ (17594333495296 <= LLO /\ LEND + 32 <= ATOP)).
Proof.
  intros P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  pose proof (sqd_asan_now P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_asan sqd_astat w_DCTX w_D8 w_RNG] in *. sd_static_open ST. unfold held in S67. destruct S67 as (ELLO & ELEND).
  destruct AS as (ARD & _ & _ & _ & _ & _ & ARL & _).
  destruct S61 as (_ & _ & _ & _ & ED8 & _).
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in *.
  destruct (ARD ltac:(clear; lia)) as (BD & UD & RD1 & RD2). pose proof (ablk_lits _ _ BD) as BDL.
  destruct (ARL ltac:(clear - S10 ELLO ELEND; lia)) as (BL & _). pose proof (ablk_lits _ _ BL) as BLL.
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
  split; [exact BDL | subst LLO LEND; clear - BLL; lia].
Qed.

Lemma sqd_lexit_ok : forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> LOCV <> 2 -> sqd_at_err P OEND LLO LEND LOCV -> sqd_at_last P -> sqd_at_lexit P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLOC ERRK LASTK.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold sqd_at_lexit. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 INV HOP HLP HBC.
  unfold sqd_at_err in ERRK. unfold sqd_at_last, sqd_fe in LASTK. cbn [sqd_saved sqd_Wb w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in ERRK, LASTK. unfold DCTX_entropy_rep, DCTX_fseEntropy, dctx_h3 in LASTK.
  pose proof ST as ST0. pose proof INV as INV0.
  pose proof (sqd_linv_frame _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS.
  pose proof (sqd_rep_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as RA. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in RA. destruct RA as (ED8 & RZ0 & RZ1 & RSR & RRP & BDL & BLL).
  apply (sqd_lopen_k _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqd_frame sqd_ffr] in FR, FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR, FRF.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof INV as (_ & _ & _ & _ & _ & LIT & _ & _ & XI). cbn [sqd_xinv w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in XI. unfold sqd_fe in XI. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in XI.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & _).
  unfold DCTX_entropy_rep, DCTX_fseEntropy, dctx_h3 in REP, HH3, MU |- *.
  clear INV SQB UFL USEQ RSQ RSQS.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (MUX : munch [(SHF, SHF + 32); (DCTX + 26684, DCTX + 26684 + 12)] m1 m1) by apply munch_refl. assert (WMX : wmono bsegs m1 m1) by apply wmono_refl.
  sqd_blob_all SHS.
  assert (RG : 512 <= D8 < 2^44 /\ 4096 <= DCTX < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= bc <= 2147483647 /\ 4096 <= SEQ < 2^47)
    by (clear - ED8 S19 S20 S1 S2 S3 S4 S5 S6 S7 S8 S9 S11 S13 S14 S15 HOP HBC; lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6).
  pose proof (bytes_at_sh2 m1 _ _ _ _ _ _ eq_refl eq_refl RZ0 RZ1 ltac:(clear; lia) ltac:(clear - RG1; lia) ltac:(clear - RG1; lia)) as RDS.
  (* [comment removed for export] *)
  lazymatch type of RDS with bytes_at _ _ _ (?b0 :: ?b1 :: nil) =>
    assert (RDC : ro_cells bsegs m1 (2147450880 + D8 + 3335) [C1 b0; C1 b1]) by (split; [cbn [cells_wf cell_wf]; repeat first [exact I | split] | cbn [cells_bytes cbytes app]; exact RDS]) end.
  clear RDS.
  pose proof atop_range as ATR.
  (* [comment removed for export] *)
  rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 ptr)) in FRF. pose proof (kx_u64_range (Z_to_bv 64 ptr)) as HPT.
  remember (bv_unsigned (Z_to_bv 64 ptr)) as ptz eqn:Eptz. clear Eptz.
  (* [comment removed for export] *)
  assert (KD1 : DCTX + 26684 + 12 <= FRB \/ FRB + 216 <= DCTX + 26684) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (KD2 : DCTX + 26684 + 12 <= FF \/ FF + 256 <= DCTX + 26684) by (unfold held in S54; clear - S54; lia).
  assert (KD3 : DCTX + 26684 + 12 <= SHF \/ SHF + 32 <= DCTX + 26684) by (unfold held in BDL; clear - BDL RGC1 RGA1 RGA2 RGA8 RGB ATR; lia).
  assert (KD4 : DCTX + 26684 + 12 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 2 <= DCTX + 26684) by (unfold held in BDL; clear - BDL ED8 ATR; lia).
  assert (KD5 : SHF + 32 <= 2147450880 + D8 + 3335 \/ 2147450880 + D8 + 3335 + 2 <= SHF) by (unfold held in S54; clear - S54 RGC1 RGC2 ED8 RG1; Z.div_mod_to_equations; lia).
  assert (KD6 : SHF + 32 <= FF \/ FF + 256 <= SHF) by (clear - RGB RGC1 RGA2; lia).
  assert (KD7 : SHF + 32 <= FRB \/ FRB + 216 <= SHF) by (clear - RGC1 RGA2 RGA1 RGA7 RGA8; lia).
  (* [comment removed for export] *)
  assert (RSH1 : 2147450880 <= SHF) by (clear - RGC1 RGA2; lia). assert (RSH2 : SHF + 32 <= 17594333495296) by (unfold held in S53; clear - S53; lia).
  try hold ERRK; try hold LASTK; try hold TRANS; try hold MUL; try hold HH3; try hold LIT; try hold MU; try hold WM; try hold BDL; try hold BLL; try hold L16F; try hold LJF; try hold HOP; try hold HLP; try hold ST0; try hold INV0; try hold BUF; try hold STK; try hold GAP; try hold SAV; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold S36; try hold S37; try hold S38; try hold S39; try hold S40; try hold S41; try hold S42; try hold S43; try hold S44; try hold S45; try hold S46; try hold S47; try hold S48; try hold S49; try hold S50; try hold S51; try hold S52; try hold S53; try hold S54; try hold S55; try hold S56; try hold S57; try hold S58; try hold S59; try hold S60; try hold S61; try hold S62; try hold S63; try hold S64; try hold S65; try hold S66; try hold S67; try hold S68; try hold S69; try hold S70; try hold OKLL; try hold OKOF; try hold OKML.
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_cases KEQ.
  all: kx_mkR_fold.
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94744) _ _ _ _) =>
        (* [comment removed for export] *)
        zstep; kx_mkR_fold; replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply Z_to_bv_eqm; reflexivity);
        unfold held in ERRK; unfold held in INV0; eapply ERRK with (c32 := c32) (c40 := c40); [exact INV0 | clear; lia | left; reflexivity]
    | |- _ => idtac
    end.
  (* [comment removed for export] *)
  all: (revert RG1 RG2 RG3 RG4 RG5 RG6 RSH1 RSH2 HPT S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB; rhold_arith; intros RG1 RG2 RG3 RG4 RG5 RG6 RSH1 RSH2 HPT S17 RGA1 RGA2 RGA4 RGA5 RGA6 RGA7 RGA8 RGB).
  kx_autoFLA (FR, FRF, REP) [] [0x94748; 0x94840] 120%nat
    [KZRange SPV 17594333495296 (2^47);
     KZRange FRB 17594333495296 (2^47 - 320);
     KZRange FF 6443008 (2^47 - 576);
     KZAlign SPV 16;
     KZRange SHF 2147450880 (17594333495296 - 32);
     KZRange D8 512 (2^44);
     KZRange DCTX 4096 (2^47);
     KZRange OP 4096 (2^47);
     KZRange LEND 4096 (2^47);
     KZRange bc 0 2147483647;
     KZRange SEQ 4096 (2^47);
     KZRange ptz 0 (2^64 - 1);
     KZWord (2147450880 + D8 + 3335) 1 0;
     KZWord (2147450880 + D8 + 3336) 1 0;
     KZWr FRB 216;
     KZWr FF 256;
     KZDisj FF 256 FRB 216;
     KZWr SHF 32;
     KZWr (DCTX + 26684) 12;
     KZDisj SHF 32 FRB 216;
     KZDisj SHF 32 FF 256;
     KZDisj (DCTX + 26684) 12 FRB 216;
     KZDisj (DCTX + 26684) 12 FF 256;
     KZDisj (DCTX + 26684) 12 SHF 32;
     KZDisj (DCTX + 26684) 12 (2147450880 + D8 + 3335) 2;
     KZDisj SHF 32 (2147450880 + D8 + 3335) 2]
    [(FRB, 216); (FF, 256); (2147450880 + D8 + 3335, 2)]
    [(FRB, 216); (FF, 256); (SHF, 32); (DCTX + 26684, 12); (2147450880 + D8 + 3335, 2)].
  all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]); try (lazymatch goal with |- _ /\ _ => split; [lia | split; [lia | split; [lia | assumption]]] end).
  all: try sqd_aclose.
  all: kx_mem.
  all: runhold_off.
  all: (try unfold held in ERRK; try unfold held in LASTK; try unfold held in TRANS; try unfold held in MUL; try unfold held in HH3; try unfold held in LIT; try unfold held in MU; try unfold held in WM; try unfold held in BDL; try unfold held in BLL; try unfold held in L16F; try unfold held in LJF; try unfold held in HOP; try unfold held in HLP; try unfold held in ST0; try unfold held in INV0; try unfold held in BUF; try unfold held in STK; try unfold held in GAP; try unfold held in SAV; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94748) _ _ _ _) => eapply ERRK with (c32 := c32) (c40 := c40) (r := 18446744073709551596); [eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | clear; lia | left; reflexivity]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x94840) _ _ ?mx _) =>
         (* [comment removed for export] *)
         assert (MU2 : munch [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (SPV - SEQ_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)] m mx)
           by (eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp, DCTX_entropy_rep; cbn [outside]; intros x Hx; clear - Hx; lia]);
         assert (WM2 : wmono bsegs m mx) by (eapply wmono_trans; [exact WM | exact WMX]);
         pose proof (sqd_asan_transport (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) _ _ _ _ mx ST0 MU2 WM2) as AS2; cbn [sqd_asan w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in AS2;
         destruct AS2 as (_ & _ & _ & _ & _ & AOUT & ARL & AHL & _ & ART2);
         (* [comment removed for export] *)
         assert (BUF' : stk bsegs mx B0 B1) by (eapply stk_transport_disjoint; [exact BUF | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S69; unfold held in S32; clear - S69 S32 S52 RSH2 S68; lia]);
         assert (STK' : stk bsegs mx lo FRB) by (eapply stk_transport_disjoint; [exact STK | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         assert (GAP' : stk bsegs mx (FRB + 216) (SPV + -104)) by (eapply stk_transport_disjoint; [exact GAP | exact MUX | exact WMX | cbn [disjoint_from]; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         assert (SAV' : rw_cells bsegs mx (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
           by (eapply rw_cells_transport; [exact SAV | exact MUX | exact WMX | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; simpl_sizes; unfold held in S27; clear - S27 S53 S47 S18; lia]);
         apply (sqd_fr_vlast mx (mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 LP jseq) in FR; cbn [sqd_fr_l1 sqd_fr_l2 w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR; sqd_blob_last FRF; sqd_blob_all SHS;
         eapply LASTK; [exact FR | exact FRF | exact SHS | eexists; eexists; eexists; exact REP | | exact BUF' | exact STK' | exact GAP' | exact SAV' | | | exact KXMI | | | | | | | | | | | | | ]
    end.
  - (* [comment removed for export] *)
    eapply rw_cells_transport; [exact HH3 | exact MUX | exact WMX |].
    cbn [disjoint_from cells_size csize Nat.add]. split; [unfold held in BDL; clear - BDL RGC1 RGA1 RGA2 RGA8 RGB; lia|]. split; [clear; lia| exact I].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MUX]; unfold sub_fp, DCTX_entropy_rep; cbn [outside]; intros x Hx; clear - Hx; lia].
  - eapply wmono_trans; [exact WM | exact WMX].
  - (* [comment removed for export] *)
    unfold held in S36; unfold held in S67. destruct S67 as (ELLO & ELEND).
    eapply rdbl_transport; [eapply rdbl_sub; [exact LIT | clear - HLP; lia | clear; lia] | exact MUX |].
    intros x Hx; left; cbn [outside]. split; [unfold held in BLL; clear - Hx BLL RGC1 RGA1 RGA2 RGA8 RGB HLP; lia|]. split; [clear - Hx S36 HLP; lia| exact I].
  - clear - HOP; lia.
  - clear - HOP; lia.
  - clear - S4 S5; lia.
  - unfold held in S67. clear - S67 HLP; lia.
  - clear - HLP; lia.
  - unfold held in S67. clear - S67 HLP; lia.
  - unfold held in S42. clear - S42 HLOC HLP; lia.     (* [comment removed for export] *)
  - clear - S1 S2 S3; lia.
  - exact ART2.
  - unfold held in S67. destruct S67 as (ELLO & ELEND). unfold WILDCOPY_OVERLENGTH in *.
    eapply aregU_sub; [exact ARL | clear - S10 ELLO ELEND; lia | clear - ELLO HLP; lia | clear - HLP; lia | clear - ELEND HLP; lia].
  - unfold held in S67. destruct S67 as (ELLO & ELEND). unfold WILDCOPY_OVERLENGTH in *.
    eapply ahull_sub; [exact AHL | clear - ELLO HLP; lia | clear - ELEND HLP; lia].
  - intros HBB. destruct (AOUT HBB) as (AO & AH). split; [exact (AO ltac:(clear - HBB; lia)) | exact AH].
Qed.

End CANSEC1.
