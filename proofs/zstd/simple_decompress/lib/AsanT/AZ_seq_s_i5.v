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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AZ_seq_inl_initfse_S3.
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

Local Ltac sqs_i5_hat H X := lazymatch type of H with rw_cells _ _ ?A _ => replace A with X in H by (cbn [cells_size csize Nat.add sbd_cells]; clear; lia) end.
Local Ltac sqs_i5_at X := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with X by (cbn [cells_size csize Nat.add sbd_cells]; clear; lia) end.
Local Ltac sqs_i5_tr H MU WM DJ := eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add sbd_cells]; clear - DJ; lia].

Lemma sqs_i5_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV ->
  (v_LLT P + 4104 < 2^47 /\ v_OFT P + 2056 < 2^47 /\ v_MLT P + 4104 < 2^47) ->
  ai_I7 P OEND LLO LEND LOCV -> ai_I5 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST TST CONT.
  unfold ai_I5.
  intros m1 jseq jpad j104 w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw bc ptr sLL sOF x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 INV HBC BOK HS1 HS2.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_itbl_asan _ _ _ _ _ _ _ _ ST INV) as ATB3.
  pose proof (sqs_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF _ SQB _ UFL _ _ _ _ _ _.
  pose proof INV as (_ & _ & _ & _ & _ & TML & _ & _ & _ & _ & _).
  clear INV. unfold ai_I7 in CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  (* [comment removed for export] *)
  AZ_seq_s_lkit.sd_static_open ST. unfold held in *.
  cbn [sqs_astat sqs_pro] in S61, S63.
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ASTK as (_ & RSTK & _).
  destruct AS as (_ & _ & ARS & _ & ACL & _ & _ & _ & AZS & ART).
  destruct ATB3 as (_ & _ & ATB).
  destruct TST as (_ & _ & TS3).
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (TS : 8 * (1 + 2 ^ st_log tML) <= 4104 /\ 1 <= 2 ^ st_log tML).
  { pose proof (proj1 OKML) as TRK. cbn [kind_maxLog] in TRK.
    pose proof (Z.pow_le_mono_r 2 (st_log tML) 9) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tML)) as PP.
    set (EE := 2 ^ st_log tML) in *. clearbody EE. change (2 ^ 9) with 512 in PM. clear - TRK PM PP. lia. }
  assert (DJF : FF + 256 <= FRB) by (clear - S18 S47 S50; lia).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 88 < 2^47 /\ 4096 <= MLT /\ MLT + 8 * (1 + 2 ^ st_log tML) < 2^47 /\
                4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 1 <= zlen sq /\ 4096 <= FRB /\ FRB + 168 < 2^47 /\
                (FF + 32) mod 8 = 0 /\ MLT mod 4 = 0 /\ FRB mod 8 = 0 /\
                (FF + 32 + 88 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ (FF + 32 + 88 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FF + 32) /\
                (FRB + 168 <= SEQ \/ SEQ + zlen sq <= FRB + 72) /\ (FRB + 168 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FRB + 72)).
  { clear - S13 S14 S15 S17 S18 S23 S25 S30 S46 S47 S48 S49 S50 S51 S56 S60 TS TS3.
    set (EE := 2 ^ st_log tML) in *. clearbody EE. Z.div_mod_to_equations. lia. }
  destruct RGS as (G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G29 & G30).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (ABS : app_blk (FF + 32 + 72) (FF + 32 + 88)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOFF : aro RNG m1 (FF + 32) 112).
  { split; [exact UFL|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOBD : aro RNG m1 (FF + 32) 40) by (eapply aro_sub; [exact AOFF | clear; lia | clear; lia | clear; lia]).
  assert (AOST : aro RNG m1 (FF + 32 + 72) 16) by (eapply aro_sub; [exact AOFF | clear; lia | clear; lia | clear; lia]).
  assert (AFS : app_blk FRB (FRB + 280)) by (eapply azstk_app; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia]).
  assert (AF1 : app_blk (FRB + 72) (FRB + 88)) by (eapply app_blk_sub; [exact AFS | clear; lia | clear; lia | clear; lia]).
  assert (AF2 : app_blk (FRB + 96) (FRB + 104)) by (eapply app_blk_sub; [exact AFS | clear; lia | clear; lia | clear; lia]).
  assert (AF3 : app_blk (FRB + 152) (FRB + 168)) by (eapply app_blk_sub; [exact AFS | clear; lia | clear; lia | clear; lia]).
  assert (RF1 : rng RNG (FRB + 72) 16) by (eapply rng_sub; [exact RSTK | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RF2 : rng RNG (FRB + 96) 8) by (eapply rng_sub; [exact RSTK | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RF3 : rng RNG (FRB + 152) 16) by (eapply rng_sub; [exact RSTK | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (AOSQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LSQ. apply aregU_aro. apply ARS. clear - S15; lia. }
  destruct (sqs_cb16_words m1 FF [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))] j104 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FRF) as (u1 & u2 & FRF1).
  clear FRF.
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ sbd_cells cw bc jpad ptr SEQ ++ [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8))] ++
                                 [C8 u1; C8 u2] ++ [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])) in FRF1.
  apply rw_cells_app in FRF1. destruct FRF1 as (F0 & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (BDC & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (FM & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (STC & F2).
  sqs_i5_hat BDC (FF + 32). sqs_i5_hat FM (FF + 72). sqs_i5_hat STC (FF + 32 + 72). sqs_i5_hat F2 (FF + 120).
  change (rw_cells bsegs m1 FRB (
    [CB 16 j0; C8 w16; C8 (Z_to_bv 64 (DCTX + 26692)); C8 (Z_to_bv 64 (DCTX + 26688)); C8 (Z_to_bv 64 (DCTX + 26684));
     C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (2147450880 + D8 + 3335))] ++
    [C8 w72; C8 w80] ++ [C8 (Z_to_bv 64 OEND)] ++ [C8 w96] ++
    [C8 (Z_to_bv 64 (-20)); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF)] ++
    [C8 w152; C8 w160] ++
    [C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (2147450880 + D8 + 3795)); C8 (Z_to_bv 64 (DCTX + 30360)); C8 (Z_to_bv 64 LEND);
     C8 w200; C8 w208; C8 w216; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LLO); CB 24 jseq])) in FR.
  apply rw_cells_app in FR. destruct FR as (K1 & FR).
  apply rw_cells_app in FR. destruct FR as (FA & FR).
  apply rw_cells_app in FR. destruct FR as (K2 & FR).
  apply rw_cells_app in FR. destruct FR as (FB & FR).
  apply rw_cells_app in FR. destruct FR as (K3 & FR).
  apply rw_cells_app in FR. destruct FR as (FC & K4).
  sqs_i5_hat FA (FRB + 72). sqs_i5_hat K2 (FRB + 88). sqs_i5_hat FB (FRB + 96). sqs_i5_hat K3 (FRB + 104).
  sqs_i5_hat FC (FRB + 152). sqs_i5_hat K4 (FRB + 168).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (sq_inl_initfse_S3_proof RNG (Z_to_bv 64 nbSeq) (Z_to_bv 64 FRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) x12 x14 x15 x16 x17 x22 x23
              (Z_to_bv 64 DST) (Z_to_bv 64 DCTX) x26 (Z_to_bv 64 SHF) x28 x29 x30 (Z_to_bv 64 (DCTX + 29896))
              F fc m1 FRB (FF + 32) MLT SEQ 82 bc ptr cw u1 u2 w72 w80 w96 w152 w160 jpad (map (Z_to_bv 8) sq) K_ML tML);
      [ exact BDC | exact STC | exact FA | exact FB | exact FC | exact TML | exact OKML | exact SQB
      | exact G9 | exact G10 | exact G11 | exact G12 | exact G13 | rewrite LSQ; exact G14 | rewrite LSQ; exact G15
      | exact G16 | exact G17 | exact G18 | exact G19 | exact G20
      | rewrite LSQ; exact G21 | exact G22
      | clear - DJF; lia | clear - DJF; lia | clear - DJF; lia | clear - DJF; lia | clear - DJF; lia | clear - DJF; lia
      | rewrite LSQ; exact G29 | exact G30
      | exact HBC | clear; lia | unfold bit_okS; rewrite LSQ; exact BOK
      | exact ABD | exact AOBD | exact ABS | exact AOST
      | exact AF1 | exact RF1 | exact AF2 | exact RF2 | exact AF3 | exact RF3
      | exact AOSQ | exact ATB | exact ACL | exact ART | exact MI | exact I ]. }
  intros ms' HQ. unfold sq_inl_initfse_S3_post in HQ.
  destruct HQ as (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x7' & m' & cw' & bc' & jpad' & ptr' & stv & -> & MU & WM & MI' & BDC' & STC' & FA' & FB' & FC' & EX7 & HST & HBC' & BOK').
  subst x7'.
  (* [comment removed for export] *)
  apply (CONT m' jseq jpad' w16 w200 w208 w216 p0 p1 p2 cw' bc' ptr' sLL sOF stv x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SEQ) x22 (Z_to_bv 64 DST) (Z_to_bv 64 DCTX) x26 x28 x29 x30).
  - apply TRANS.
    + eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia.
    + exact WM.
    + exact MI'.
    + lazymatch type of K1 with rw_cells _ _ _ ?L1 => lazymatch type of K2 with rw_cells _ _ _ ?L2 =>
      lazymatch type of K3 with rw_cells _ _ _ ?L3 => lazymatch type of K4 with rw_cells _ _ _ ?L4 =>
        change (rw_cells bsegs m' FRB (L1 ++ [C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 DST)] ++ L2 ++ [C8 (Z_to_bv 64 ASHOFF)] ++ L3 ++
                                       [C8 (Z_to_bv 64 SBITMASK); C8 (Z_to_bv 64 (DCTX + 29896))] ++ L4)) end end end end.
      apply rw_cells_app; split; [sqs_i5_tr K1 MU WM DJF |].
      sqs_i5_at (FRB + 72). apply rw_cells_app; split; [exact FA' |].
      sqs_i5_at (FRB + 88). apply rw_cells_app; split; [sqs_i5_tr K2 MU WM DJF |].
      sqs_i5_at (FRB + 96). apply rw_cells_app; split; [exact FB' |].
      sqs_i5_at (FRB + 104). apply rw_cells_app; split; [sqs_i5_tr K3 MU WM DJF |].
      sqs_i5_at (FRB + 152). apply rw_cells_app; split; [exact FC' |].
      sqs_i5_at (FRB + 168). sqs_i5_tr K4 MU WM DJF.
    + lazymatch type of FM with rw_cells _ _ _ ?LM => lazymatch type of F2 with rw_cells _ _ _ ?LQ =>
        change (rw_cells bsegs m' FF ([CB 32 jfh] ++ sbd_cells cw' bc' jpad' ptr' SEQ ++ LM ++ [C8 (Z_to_bv 64 stv); C8 (Z_to_bv 64 (MLT + 8))] ++ LQ)) end end.
      apply rw_cells_app; split; [sqs_i5_tr F0 MU WM DJF |].
      sqs_i5_at (FF + 32). apply rw_cells_app; split; [exact BDC' |].
      sqs_i5_at (FF + 72). apply rw_cells_app; split; [sqs_i5_tr FM MU WM DJF |].
      sqs_i5_at (FF + 32 + 72). apply rw_cells_app; split; [exact STC' |].
      sqs_i5_at (FF + 120). sqs_i5_tr F2 MU WM DJF.
  - clear - HBC'. lia.
  - rewrite LSQ in BOK'. exact BOK'.
  - exact HS1.
  - exact HS2.
  - exact HST.
Qed.

End CANSEC1.
