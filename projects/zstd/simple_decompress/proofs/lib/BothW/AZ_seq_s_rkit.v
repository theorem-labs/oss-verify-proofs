(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sqs_ediv8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r.
Proof. intros q r H. split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_ffr_rest (P : ssq) (sLL sOF sML : Z) (p0 p1 p2 : word) : list cell :=
  [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (v_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (v_MLT P + 8));
   C8 p0; C8 p1; C8 p2; CB 104 (v_j144 P); C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))].
Lemma sqs_ffr_app : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad,
  sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad = [CB 32 (v_jfh P)] ++ sbd_cells cw bc jpad ptr (v_SEQ P) ++ sqs_ffr_rest P sLL sOF sML p0 p1 p2.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.

(* [comment removed for export] *)
Definition sqs_rl_post (P : ssq) (OEND LLO LEND LOCV : Z) (c0 c8 c152 c160 c168 c200 c208 c216 : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (cw2 : word),
    (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
       ms' = MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m2 (seg_rom bsegs)) /\
    sqs_linv P OEND LLO LEND LOCV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw2 (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP.

Lemma sqs_rl_spec : forall P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP
    ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  sqs_static P OEND LLO LEND LOCV ->
  sqs_linv P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  0 <= bc <= 64 -> v_SEQ P + 8 <= ptr -> ptr <= v_SEQ P + zlen (v_sq P) - 8 ->
  evtF bsegs (v_RNG P) (sqs_rl_post P OEND LLO LEND LOCV c0 c8 c152 c160 c168 c200 c208 c216 bc ptr sLL sOF sML p0 p1 p2 LP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (v_FF P + 32)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x967a8) fc None m0 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         ST INV HBC HP1 HP2.
  pose proof (sqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_linv_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as UFL.
  pose proof (sqs_linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof INV as ((jpad & jseq & FR & FRF) & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  (* [comment removed for export] *)
  rewrite sqs_ffr_app in FRF. apply rw_cells_app in FRF. destruct FRF as (F0 & FRF). apply rw_cells_app in FRF. destruct FRF as (BDC & F2).
  cbn [cells_size csize Nat.add length] in BDC. cbn [cells_size csize Nat.add length sbd_cells] in F2.
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv sqs_asan sqs_astat sqs_pro v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (_ & _ & ARS & _ & _ & _ & _ & _ & AZS & ART).
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  unfold zd_reload_int_stmtA in S74.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 40 < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ (FF + 32) mod 8 = 0 /\
                (FF + 32 + 40 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ lo <= FRB - 16 /\ FRB < 2^47 /\
                (FF + 32 + 40 <= lo \/ FRB <= FF + 32) /\ (SEQ + zlen sq <= lo \/ FRB <= SEQ) /\ 0 <= FRB - 16).
  { clear - S13 S14 S15 S17 S18 S47 S49 S50 S51 S56 S25. Z.div_mod_to_equations. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  (* [comment removed for export] *)
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOBD : aro RNG m0 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOSQ : aro RNG m0 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LSQ. apply aregU_aro. apply ARS. clear - S15; lia. }
  eapply evtF_mono.
  - eapply (S74 RNG ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 FRB lo (FF + 32) SEQ bc ptr cw jpad (map (Z_to_bv 8) sq));
      [ exact BDC | exact SQB | exact G1 | exact G2 | exact G3 | rewrite LSQ; exact G4 | exact G5 | rewrite LSQ; exact G6
      | exact HBC | exact HP1 | rewrite LSQ; exact HP2
      | exact STK | exact G7 | exact G8 | exact G9 | rewrite LSQ; exact G10
      | exact ABD | exact AOBD | exact AOSQ | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact MI ].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & cw' & -> & MU & WM & MI' & STK' & BDC').
    exists m', cw'. split; [do 15 eexists; reflexivity|].
    assert (MU4 : munch [(DST, DST); (FRB - 16, FRB); (FRB, FRB + 280); (FF, FF + 256)] m0 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply (STEP m' c0 c8 c152 c160 c168 c200 c208 c216 cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP jpad jseq DST DST 16);
      [ clear; lia | exact MU4 | exact WM | exact MI' | | exact STK' | clear; lia | clear - S4; lia | | ].
    + (* [comment removed for export] *)
      eapply stk_transport_disjoint; [exact BUF | exact MU | exact WM |].
      cbn [disjoint_from]. split; [clear - S55 S68; lia|]. split; [clear - S24 S18 S47 S68; lia| exact I].
    + eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from sqs_frame cells_size csize Nat.add v_FRB].
      split; [clear - S50 S18 S47; lia|]. split; [clear; lia| exact I].
    + rewrite sqs_ffr_app. cbn [v_jfh v_SEQ sqs_ffr_rest v_LLT v_OFT v_MLT v_j144 v_fflag v_L v_FF]. apply rw_cells_app. split.
      * eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add length]. split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I].
      * apply rw_cells_app. cbn [cells_size csize Nat.add length]. split; [exact BDC'|].
        eapply rw_cells_transport; [exact F2 | exact MU | exact WM |].
        cbn [disjoint_from cells_size csize Nat.add length sbd_cells sqs_ffr_rest].
        split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma sqs_fr0_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 0)) 8 = Some (word_to_le_bytes 8 c0).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 0%nat (C8 c0) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 0) with (FRB + 0) in R by lia. exact R.
Qed.
Lemma sqs_fr8_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 8)) 8 = Some (word_to_le_bytes 8 c8).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 8%nat (C8 c8) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 8) with (FRB + 8) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr176_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1152921504606846976)).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 176%nat (C8 (Z_to_bv 64 1152921504606846976)) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 176) with (FRB + 176) in R by lia. exact R.
Qed.
Lemma sqs_fr208_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 208)) 8 = Some (word_to_le_bytes 8 c208).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 208%nat (C8 c208) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 208) with (FRB + 208) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr168_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 168)) 8 = Some (word_to_le_bytes 8 c168).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 168%nat (C8 c168) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 168) with (FRB + 168) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr152_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 152)) 8 = Some (word_to_le_bytes 8 c152).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 152%nat (C8 c152) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 152) with (FRB + 152) in R by lia. exact R.
Qed.

End CANSEC1.
