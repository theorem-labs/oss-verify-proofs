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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit
     AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_bit_init_stmtG (ENTRY : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  (1 <= n -> BD + 40 <= SRC \/ SRC + n <= BD) ->
  stk bsegs m lo SPV -> lo <= SPV - BITINIT_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> (1 <= n -> aro RNG m SRC n) ->
  art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqs_bitd_ptr_ok : forall SEQ n bc, bit_ok SEQ n bc (bitd_ptr SEQ n).
Proof.
  intros SEQ n bc _. unfold bitd_ptr. destruct (8 <=? n) eqn:E; [apply Z.leb_le in E; right; lia | left; reflexivity].
Qed.

(* [comment removed for export] *)
Definition sqs_bitinit_ipost (P : ssq) (OEND LLO LEND LOCV : Z) (fr : list cell) (j72 : list byte) (p0 p1 p2 : word) (A6 T32 : Z) (x1 s2 s9 s11 : word)
    : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (sqs_iregs P A6 T32 x1 t0 t1 t2 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6) (v_F P) (ret_pc x1) (v_fc P) None m2 (seg_rom bsegs) /\
    ((r = zlen (v_sq P) /\
      exists cw bc jpad, 1 <= bc <= 64 /\
        sqs_iinv P OEND LLO LEND LOCV m2 fr (sqs_iffB P cw bc jpad (bitd_ptr (v_SEQ P) (zlen (v_sq P))) j72 p0 p1 p2))
     \/ (zd_is_error r = true /\ 0 <= r < 2^64 /\
         exists jbd, sqs_iinv P OEND LLO LEND LOCV m2 fr (sqs_iffA P jbd j72 p0 p1 p2))).

Lemma sqs_bitinit_ispec : forall P OEND LLO LEND LOCV m1 fr jbd j72 p0 p1 p2 A6 T32 (x1 t0 t1 t2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 : word),
  sqs_static P OEND LLO LEND LOCV -> sqs_bit_init_stmtG APZD_BITINIT ->
  sqs_iinv P OEND LLO LEND LOCV m1 fr (sqs_iffA P jbd j72 p0 p1 p2) ->
  evtF bsegs (v_RNG P) (sqs_bitinit_ipost P OEND LLO LEND LOCV fr j72 p0 p1 p2 A6 T32 x1 s2 s9 s11)
    (MS (sqs_iregs P A6 T32 x1 t0 t1 t2 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (zlen (v_sq P))) a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6)
        (v_F P) (Z_to_bv 64 APZD_BITINIT) (v_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 fr jbd j72 p0 p1 p2 A6 T32 x1 t0 t1 t2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 ST BI INV.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_iff_ahull _ _ _ _ _ _ _ _ ST INV) as AHB.
  pose proof (sqs_iinv_step _ _ _ _ _ _ _ _ ST INV) as STEP.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF _ SQB _ UFL _ _ _ _ _ _.
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  (* [comment removed for export] *)
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_iregs sqs_bitinit_ipost sqs_iffA sqs_iffB] in *.
  cbn [sqs_xinv sqs_asan sqs_astat sqs_pro v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ [CB 40 jbd] ++ [CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])) in FRF.
  apply rw_cells_app in FRF. destruct FRF as (F0 & FRF). apply rw_cells_app in FRF. destruct FRF as (BDC & F2).
  cbn [cells_size csize Nat.add length] in BDC, F2.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (_ & _ & ARS & _ & _ & _ & _ & _ & AZS & ART).
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  unfold sqs_bit_init_stmtG in BI.
  assert (LSQ : zlen (map (Z_to_bv 8) sq) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 40 < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ (FF + 32) mod 8 = 0 /\
                (FF + 32 + 40 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ lo <= FRB - 2224 /\ FRB < 2^47 /\
                (FF + 32 + 40 <= lo \/ FRB <= FF + 32) /\ (SEQ + zlen sq <= lo \/ FRB <= SEQ)).
  { clear - S13 S14 S15 S17 S18 S47 S49 S50 S51 S56 S25. Z.div_mod_to_equations. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  (* [comment removed for export] *)
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOBD : aro RNG m1 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOSQ : aro RNG m1 SEQ (zlen sq)).
  { apply aregU_aro. apply ARS. clear - S15; lia. }
  eapply evtF_mono.
  - eapply (BI RNG x1 gp' tp' t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 FRB) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (zlen sq)) (Z_to_bv 64 SEQ) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 A6) (Z_to_bv 64 T32) (Z_to_bv 64 nbSeq) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6
               F' fc' m1 FRB (FF + 32) SEQ (zlen sq) lo (map (Z_to_bv 8) sq) jbd);
      [ exact MI | exact BDC | exact G5 | exact SQB | exact LSQ | exact G1 | exact G2 | exact G3 | exact G4 | intros _; exact G6
      | exact STK | exact G7 | exact G8 | exact G9 | exact G10
      | exact ABD | exact AOBD | exact AHB | intros _; exact AOSQ | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia] ].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & -> & MU & WM & MI' & STK' & RES).
    exists m', r. do 14 eexists. split; [reflexivity|].
    assert (MU3 : munch [(FRB - 2224, FRB); (FRB, FRB + 280); (FF, FF + 256)] m1 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    assert (FR' : rw_cells bsegs m' FRB fr).
    { eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from]. split; [clear - S50 S18 S47; right; lia|]. split; [clear; lia| exact I]. }
    assert (F0' : rw_cells bsegs m' FF [CB 32 jfh]).
    { eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add length]. split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I]. }
    assert (F2' : rw_cells bsegs m' (FF + 32 + 40) [CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))]).
    { eapply rw_cells_transport; [exact F2 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add length]. split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I]. }
    destruct RES as [(-> & N1 & cw & bc & pad & HBC & HBC8 & BDC') | (ER & HR & bs & BDC')].
    + left. split; [reflexivity|]. exists cw, bc, pad. split; [exact HBC|].
      eapply (STEP m' fr _ 2224); [clear; lia | exact MU3 | exact WM | exact MI' | exact STK' | exact FR' |].
      change (rw_cells bsegs m' FF ([CB 32 jfh] ++ bitd_cells cw (Z_to_bv 64 bc) pad (bitd_ptr SEQ (zlen sq)) SEQ ++ [CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])).
      apply rw_cells_app. split; [exact F0'|]. apply rw_cells_app. cbn [cells_size csize Nat.add length bitd_cells]. split; [exact BDC' | exact F2'].
    + right. apply zd_is_error_true_iff in ER as ER'. split; [exact ER|]. split; [clear - ER' HR; unfold ZE_maxCode in *; lia|]. exists bs.
      eapply (STEP m' fr _ 2224); [clear; lia | exact MU3 | exact WM | exact MI' | exact STK' | exact FR' |].
      change (rw_cells bsegs m' FF ([CB 32 jfh] ++ [CB 40 bs] ++ [CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])).
      apply rw_cells_app. split; [exact F0'|]. apply rw_cells_app. cbn [cells_size csize Nat.add length]. split; [exact BDC' | exact F2'].
Qed.

(* [comment removed for export] *)
Definition sqs_initfse_ipost (P : ssq) (OEND LLO LEND LOCV : Z) (fr mid post : list cell) (T : Z) (t : seq_table) (B A6 T32 : Z) (x1 s2 s9 s11 : word)
    : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (cw' : word) (bc' : Z) (jpad' : list byte) (ptr' st : Z) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (sqs_iregs P A6 T32 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6) (v_F P) (ret_pc x1) (v_fc P) None m2 (seg_rom bsegs) /\
    sqs_iinv P OEND LLO LEND LOCV m2 fr ([CB 32 (v_jfh P)] ++ sbd_cells cw' bc' jpad' ptr' (v_SEQ P) ++ mid ++ C8 (Z_to_bv 64 st) :: C8 (Z_to_bv 64 (T + 8)) :: post) /\
    0 <= st < 2^(st_log t) /\ 0 <= bc' <= B + 9 /\ bit_ok (v_SEQ P) (zlen (v_sq P)) bc' ptr'.

Lemma sqs_initfse_ispec : forall P OEND LLO LEND LOCV m1 fr cw bc jpad ptr mid (u1 u2 : word) post T t K B STP A6 T32
    (x1 t0 t1 t2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 : word),
  sqs_static P OEND LLO LEND LOCV -> zd_initfse_stmtA ->
  sqs_iinv P OEND LLO LEND LOCV m1 fr ([CB 32 (v_jfh P)] ++ sbd_cells cw bc jpad ptr (v_SEQ P) ++ mid ++ C8 u1 :: C8 u2 :: post) ->
  ((T = v_LLT P /\ t = v_tLL P /\ K = K_LL) \/ (T = v_OFT P /\ t = v_tOF P /\ K = K_OF) \/ (T = v_MLT P /\ t = v_tML P /\ K = K_ML)) ->
  (v_LLT P + 4104 < 2^47 /\ v_OFT P + 2056 < 2^47 /\ v_MLT P + 4104 < 2^47) ->
  STP = v_FF P + 72 + Z.of_nat (cells_size mid) ->
  (Z.of_nat (cells_size mid) = 0 \/ Z.of_nat (cells_size mid) = 16 \/ Z.of_nat (cells_size mid) = 32) ->
  Z.of_nat (cells_size mid) + Z.of_nat (cells_size post) = 168 ->
  0 <= bc <= B -> B <= 82 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr ->
  evtF bsegs (v_RNG P) (sqs_initfse_ipost P OEND LLO LEND LOCV fr mid post T t B A6 T32 x1 s2 s9 s11)
    (MS (sqs_iregs P A6 T32 x1 t0 t1 t2 (Z_to_bv 64 STP) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 T) a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6)
        (v_F P) (Z_to_bv 64 APZD_INITFSE) (v_fc P) None m1 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 fr cw bc jpad ptr mid u1 u2 post T t K B STP A6 T32 x1 t0 t1 t2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 ST IFS INV TSEL TST ESTP HMID HPOST HBC HB HBOK.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_itbl_asan _ _ _ _ _ _ _ _ ST INV) as ATB3.
  pose proof (sqs_iinv_step _ _ _ _ _ _ _ _ ST INV) as STEP.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF _ SQB _ UFL _ _ _ _ _ _.
  pose proof INV as (_ & _ & _ & TLL & TOF & TML & _ & _ & _ & _ & XI).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st0 LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_iregs sqs_initfse_ipost] in *.
  cbn [sqs_xinv sqs_asan sqs_astat sqs_pro v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  (* [comment removed for export] *)
  apply rw_cells_app in FRF. destruct FRF as (F0 & FRF). apply rw_cells_app in FRF. destruct FRF as (BDC & FRF).
  apply rw_cells_app in FRF. destruct FRF as (FM & FRF).
  change (C8 u1 :: C8 u2 :: post) with ([C8 u1; C8 u2] ++ post) in FRF. apply rw_cells_app in FRF. destruct FRF as (STC & F2).
  cbn [cells_size csize Nat.add length sbd_cells] in BDC, FM, STC, F2.
  lazymatch type of STC with rw_cells _ _ ?A _ => replace A with STP in STC by (clear - ESTP; lia) end.
  lazymatch type of F2 with rw_cells _ _ ?A _ => replace A with (STP + 16) in F2 by (clear - ESTP; lia) end.
  lazymatch type of FM with rw_cells _ _ ?A _ => replace A with (FF + 72) in FM by (clear; lia) end.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (_ & _ & ARS & _ & ACL & _ & _ & _ & AZS & ART).
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ATB3 as (ATLL & ATOF & ATML). destruct TST as (TS1 & TS2 & TS3).
  (* [comment removed for export] *)
  assert (TF : bytes_at bsegs m1 T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok K t /\ aro RNG m1 T (8 * (1 + 2 ^ st_log t)) /\ 1 <= 2 ^ st_log t /\
               4096 <= T /\ T + 8 * (1 + 2 ^ st_log t) < 2^47 /\ T mod 8 = 0 /\
               (FF + 256 <= T \/ T + 8 * (1 + 2 ^ st_log t) <= FF) /\ (T + 8 * (1 + 2 ^ st_log t) <= lo \/ SPV <= T)).
  { destruct TSEL as [(ET & Et & EK) | [(ET & Et & EK) | (ET & Et & EK)]]; rewrite ET, Et, EK.
    - pose proof (proj1 OKLL) as TRK. cbn [kind_maxLog] in TRK. pose proof (Z.pow_le_mono_r 2 (st_log tLL) 9) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tLL)) as PP.
      split; [exact TLL|]. split; [exact OKLL|]. split; [exact ATLL|].
      set (EE := 2 ^ st_log tLL) in *. clearbody EE. change (2 ^ 9) with 512 in PM. clear - S21 S44 S58 S28 TS1 TRK PM PP. lia.
    - pose proof (proj1 OKOF) as TRK. cbn [kind_maxLog] in TRK. pose proof (Z.pow_le_mono_r 2 (st_log tOF) 8) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tOF)) as PP.
      split; [exact TOF|]. split; [exact OKOF|]. split; [exact ATOF|].
      set (EE := 2 ^ st_log tOF) in *. clearbody EE. change (2 ^ 8) with 256 in PM. clear - S22 S45 S59 S29 TS2 TRK PM PP. lia.
    - pose proof (proj1 OKML) as TRK. cbn [kind_maxLog] in TRK. pose proof (Z.pow_le_mono_r 2 (st_log tML) 9) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tML)) as PP.
      split; [exact TML|]. split; [exact OKML|]. split; [exact ATML|].
      set (EE := 2 ^ st_log tML) in *. clearbody EE. change (2 ^ 9) with 512 in PM. clear - S23 S46 S60 S30 TS3 TRK PM PP. lia. }
  clear TLL TOF TML ATLL ATOF ATML OKLL OKOF OKML TSEL TS1 TS2 TS3.
  destruct TF as (TB & TOK & ATB & PP & RT1 & RT2 & RT8 & DJTF & DJTL).
  set (TSZ := 8 * (1 + 2 ^ st_log t)) in *. assert (ETSZ : TSZ = 8 * (1 + 2 ^ st_log t)) by reflexivity. clearbody TSZ.
  unfold zd_initfse_stmtA, zd_initfse_stmtA_if in IFS.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 40 < 2^47 /\ 4096 <= STP /\ STP + 16 < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 1 <= zlen sq /\
                (FF + 32) mod 8 = 0 /\ STP mod 8 = 0 /\ T mod 4 = 0 /\
                (FF + 32 + 40 <= STP \/ STP + 16 <= FF + 32) /\ (FF + 32 + 40 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ (STP + 16 <= SEQ \/ SEQ + zlen sq <= STP) /\
                (FF + 32 + 40 <= T \/ T + TSZ <= FF + 32) /\ (STP + 16 <= T \/ T + TSZ <= STP) /\
                lo <= FRB - 16 /\ FRB < 2^47 /\
                (FF + 32 + 40 <= lo \/ FRB <= FF + 32) /\ (STP + 16 <= lo \/ FRB <= STP) /\ (SEQ + zlen sq <= lo \/ FRB <= SEQ) /\
                (T + TSZ <= lo \/ FRB <= T)).
  { clear - S13 S14 S15 S17 S18 S47 S49 S50 S51 S56 S25 RT1 RT2 RT8 DJTF DJTL ESTP HMID PP. Z.div_mod_to_equations. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  (* [comment removed for export] *)
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (ABS : app_blk STP (STP + 16)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear - ESTP HMID; lia | clear; lia | clear - ESTP HMID; lia]. }
  assert (AOBD : aro RNG m1 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOST : aro RNG m1 STP 16).
  { split; [eapply unpoisoned_sub; [exact UFL | clear - ESTP HMID; lia | clear - ESTP HMID; lia]|].
    split; [eapply rng_sub; [exact RFF | clear - ESTP HMID; lia | clear - ESTP HMID; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51 ESTP HMID; Z.div_mod_to_equations; lia. }
  assert (AOSQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LSQ. apply aregU_aro. apply ARS. clear - S15; lia. }
  eapply evtF_mono.
  - eapply (IFS RNG x1 gp' tp' t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 FRB) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (zlen sq)) (Z_to_bv 64 SEQ) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 A6) (Z_to_bv 64 T32) (Z_to_bv 64 nbSeq) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6
               F' fc' m1 FRB lo (FF + 32) STP T SEQ B bc ptr cw u1 u2 jpad (map (Z_to_bv 8) sq) K t);
      [ exact BDC | exact STC | exact TB | exact TOK | exact SQB
      | exact G1 | exact G2 | exact G3 | exact G4 | exact RT1 | rewrite <- ETSZ; exact RT2 | exact G5 | rewrite LSQ; exact G6 | rewrite LSQ; exact G7
      | exact G8 | exact G9 | exact G10
      | exact G11 | rewrite LSQ; exact G12 | rewrite LSQ; exact G13 | rewrite <- ETSZ; exact G14 | rewrite <- ETSZ; exact G15
      | exact HBC | exact HB | rewrite LSQ; exact HBOK
      | exact STK | exact G16 | exact G17 | exact G18 | exact G19 | rewrite LSQ; exact G20 | rewrite <- ETSZ; exact G21
      | exact ABD | exact AOBD | exact ABS | exact AOST | exact AOSQ | rewrite <- ETSZ; exact ATB | exact ACL | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact MI | exact I ].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & cw' & bc' & jpad' & ptr' & st & -> & MU & WM & MI' & STK' & BDC' & STC' & HST & HBC' & HBOK').
    exists m', cw', bc', jpad', ptr', st. do 15 eexists. split; [reflexivity|].
    rewrite LSQ in HBOK'.
    split; [| split; [exact HST | split; [exact HBC' | exact HBOK']]].
    assert (MU3 : munch [(FRB - 16, FRB); (FRB, FRB + 280); (FF, FF + 256)] m1 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx ESTP HMID. lia. }
    eapply (STEP m' fr _ 16); [clear; lia | exact MU3 | exact WM | exact MI' | exact STK' | |].
    + eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from]. split; [clear - S50 S18 S47; right; lia|]. split; [clear - S50 S18 S47 ESTP HMID; right; lia|]. split; [clear; lia| exact I].
    + apply rw_cells_app. split.
      { eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add length].
        split; [clear; lia|]. split; [clear - ESTP HMID; lia|]. split; [clear - S50 S18 S47; lia| exact I]. }
      apply rw_cells_app. cbn [cells_size csize Nat.add length sbd_cells]. split; [exact BDC'|].
      apply rw_cells_app.
      lazymatch goal with |- rw_cells _ _ ?A _ /\ _ => replace A with (FF + 72) by (clear; lia) end.
      split.
      { eapply rw_cells_transport; [exact FM | exact MU | exact WM |]. cbn [disjoint_from].
        split; [clear - HMID; lia|]. split; [clear - ESTP HMID; lia|]. split; [clear - S50 S18 S47 HMID; lia| exact I]. }
      change (C8 (Z_to_bv 64 st) :: C8 (Z_to_bv 64 (T + 8)) :: post) with ([C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))] ++ post).
      apply rw_cells_app. cbn [cells_size csize Nat.add length].
      lazymatch goal with |- rw_cells _ _ ?A _ /\ _ => replace A with STP by (clear - ESTP; lia) end. split; [exact STC'|].
      lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (STP + 16) by (clear - ESTP; lia) end.
      eapply rw_cells_transport; [exact F2 | exact MU | exact WM |]. cbn [disjoint_from].
      split; [clear - ESTP HMID; lia|]. split; [clear; lia|]. split; [clear - S50 S18 S47 ESTP HMID HPOST; lia| exact I].
Qed.

End CANSEC1.
