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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AZ_seq_inl_initfse_S2.
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

Local Ltac sqs_i3_hat H X := lazymatch type of H with rw_cells _ _ ?A _ => replace A with X in H by (cbn [cells_size csize Nat.add sbd_cells]; clear; lia) end.
Local Ltac sqs_i3_at X := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with X by (cbn [cells_size csize Nat.add sbd_cells]; clear; lia) end.
Local Ltac sqs_i3_tr H MU WM DJ := eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add sbd_cells]; clear - DJ; lia].

Lemma sqs_i3_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV ->
  (v_LLT P + 4104 < 2^47 /\ v_OFT P + 2056 < 2^47 /\ v_MLT P + 4104 < 2^47) ->
  ai_I5 P OEND LLO LEND LOCV -> ai_I3 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST TST CONT.
  unfold ai_I3.
  intros m1 jseq jpad j88 w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw bc ptr sLL x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 INV HBC BOK HS1.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_itbl_asan _ _ _ _ _ _ _ _ ST INV) as ATB3.
  pose proof (sqs_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF PT SQB _ UFL _ _ _ _ _ _.
  pose proof INV as (_ & _ & _ & _ & TOF & TML & _ & _ & _ & _ & _).
  clear INV. unfold ai_I5 in CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  (* [comment removed for export] *)
  AZ_seq_s_lkit.sd_static_open ST. unfold held in *.
  cbn [sqs_astat sqs_pro] in S61, S63.
  destruct S61 as (ASTK & _ & _ & _ & ED8 & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct AS as (ARD & _ & ARS & _ & ACL & _ & _ & _ & _ & ART).
  destruct ATB3 as (_ & ATBO & ATBM).
  destruct TST as (_ & TS2 & TS3).
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (TSO : 8 * (1 + 2 ^ st_log tOF) <= 2056 /\ 1 <= 2 ^ st_log tOF).
  { pose proof (proj1 OKOF) as TRK. cbn [kind_maxLog] in TRK.
    pose proof (Z.pow_le_mono_r 2 (st_log tOF) 8) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tOF)) as PP.
    set (EE := 2 ^ st_log tOF) in *. clearbody EE. change (2 ^ 8) with 256 in PM. clear - TRK PM PP. lia. }
  assert (TSM : 8 * (1 + 2 ^ st_log tML) <= 4104 /\ 1 <= 2 ^ st_log tML).
  { pose proof (proj1 OKML) as TRK. cbn [kind_maxLog] in TRK.
    pose proof (Z.pow_le_mono_r 2 (st_log tML) 9) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tML)) as PP.
    set (EE := 2 ^ st_log tML) in *. clearbody EE. change (2 ^ 9) with 512 in PM. clear - TRK PM PP. lia. }
  assert (DJF : FF + 256 <= FRB) by (clear - S18 S47 S50; lia).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 72 < 2^47 /\ 4096 <= OFT /\ OFT + 8 * (1 + 2 ^ st_log tOF) < 2^47 /\
                4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ 1 <= zlen sq /\
                4096 <= DCTX /\ DCTX + 24 < 2^47 /\ 4096 <= MLT /\ MLT + 8 * (1 + 2 ^ st_log tML) < 2^47 /\
                (FF + 32) mod 8 = 0 /\ OFT mod 4 = 0 /\ DCTX mod 8 = 0 /\ MLT mod 4 = 0 /\
                (FF + 32 + 72 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ (FF + 32 + 72 <= OFT \/ OFT + 8 * (1 + 2 ^ st_log tOF) <= FF + 32) /\
                (FF + 32 + 72 <= DCTX + 8 \/ DCTX + 16 <= FF + 32) /\ (FF + 32 + 72 <= MLT \/ MLT + 8 <= FF + 32)).
  { clear - S13 S14 S15 S17 S18 S19 S20 S22 S23 S45 S46 S47 S49 S50 S51 S54 S56 S59 S60 ED8 TSO TSM TS2 TS3.
    set (EO := 2 ^ st_log tOF) in *. set (EM := 2 ^ st_log tML) in *. clearbody EO EM. Z.div_mod_to_equations. lia. }
  destruct RGS as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (ABS : app_blk (FF + 32 + 56) (FF + 32 + 72)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOFF : aro RNG m1 (FF + 32) 112).
  { split; [exact UFL|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOBD : aro RNG m1 (FF + 32) 40) by (eapply aro_sub; [exact AOFF | clear; lia | clear; lia | clear; lia]).
  assert (AOST : aro RNG m1 (FF + 32 + 56) 16) by (eapply aro_sub; [exact AOFF | clear; lia | clear; lia | clear; lia]).
  assert (AOPT : aro RNG m1 (DCTX + 8) 8).
  { apply aregU_aro. eapply aregU_sub; [exact ARD | unfold DCTX_SIZEOF; clear; lia | clear; lia | clear; lia | unfold DCTX_SIZEOF; clear; lia]. }
  assert (AONT : aro RNG m1 MLT 8).
  { eapply aro_sub; [exact ATBM | clear; lia | clear; lia | clear - TSM; set (EM := 2 ^ st_log tML) in *; lia]. }
  assert (AOSQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LSQ. apply aregU_aro. apply ARS. clear - S15; lia. }
  unfold dctx_ptrs in PT.
  change (rw_cells bsegs m1 DCTX ([C8 (Z_to_bv 64 LLT)] ++ [C8 (Z_to_bv 64 MLT)] ++ [C8 (Z_to_bv 64 OFT); C8 huf])) in PT.
  apply rw_cells_app in PT. destruct PT as (_ & PT). apply rw_cells_app in PT. destruct PT as (PTM & _).
  sqs_i3_hat PTM (DCTX + 8).
  destruct (sqs_cbst32 m1 FF [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] j88 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FRF) as (u1 & u2 & j104 & FRF1).
  clear FRF.
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ sbd_cells cw bc jpad ptr SEQ ++ [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] ++
                                 [C8 u1; C8 u2] ++ [CB 16 j104; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])) in FRF1.
  apply rw_cells_app in FRF1. destruct FRF1 as (F0 & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (BDC & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (FM & FRF1).
  apply rw_cells_app in FRF1. destruct FRF1 as (STC & F2).
  sqs_i3_hat BDC (FF + 32). sqs_i3_hat FM (FF + 72). sqs_i3_hat STC (FF + 32 + 56). sqs_i3_hat F2 (FF + 104).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (sq_inl_initfse_S2_proof RNG (Z_to_bv 64 nbSeq) (Z_to_bv 64 FRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 FRB) x12 x14 x15 x16 x17 x22 x23
              (Z_to_bv 64 DST) x26 (Z_to_bv 64 SHF) x28 x29 x30 (Z_to_bv 64 (DCTX + 29896))
              F fc m1 (FF + 32) OFT SEQ 73 bc ptr DCTX MLT cw u1 u2 jpad (map (Z_to_bv 8) sq) K_OF tOF K_ML tML);
      [ exact BDC | exact STC | exact PTM | exact TML | exact OKML | exact TOF | exact OKOF | exact SQB
      | exact R1 | exact R2 | exact R3 | exact R4 | exact R5 | rewrite LSQ; exact R6 | rewrite LSQ; exact R7
      | exact R8 | exact R9 | exact R10 | exact R11
      | exact R12 | exact R13 | exact R14 | exact R15
      | rewrite LSQ; exact R16 | exact R17 | exact R18 | exact R19
      | exact HBC | clear; lia | unfold bit_okS; rewrite LSQ; exact BOK
      | exact ABD | exact AOBD | exact ABS | exact AOST
      | exact AOPT | exact AONT
      | exact AOSQ | exact ATBO | exact ACL | exact ART | exact MI | exact I ]. }
  intros ms' HQ. unfold sq_inl_initfse_S2_post in HQ.
  destruct HQ as (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x2' & m' & cw' & bc' & jpad' & ptr' & stv & -> & MU & WM & MI' & BDC' & STC' & EA0 & EA1 & EA3 & EX2 & HST & HBC' & BOK').
  subst a0 a1 a3 x2'.
  apply (CONT m' jseq jpad' j104 w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw' bc' ptr' sLL stv x5 x6 x7 a2 a4 a5 a6 a7 x22 x23 x26 x28 x29 x30).
  - apply TRANS.
    + eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia.
    + exact WM.
    + exact MI'.
    + sqs_i3_tr FR MU WM DJF.
    + lazymatch type of FM with rw_cells _ _ _ ?LM => lazymatch type of F2 with rw_cells _ _ _ ?LQ =>
        change (rw_cells bsegs m' FF ([CB 32 jfh] ++ sbd_cells cw' bc' jpad' ptr' SEQ ++ LM ++ [C8 (Z_to_bv 64 stv); C8 (Z_to_bv 64 (OFT + 8))] ++ LQ)) end end.
      apply rw_cells_app; split; [sqs_i3_tr F0 MU WM DJF |].
      sqs_i3_at (FF + 32). apply rw_cells_app; split; [exact BDC' |].
      sqs_i3_at (FF + 72). apply rw_cells_app; split; [sqs_i3_tr FM MU WM DJF |].
      sqs_i3_at (FF + 32 + 56). apply rw_cells_app; split; [exact STC' |].
      sqs_i3_at (FF + 104). sqs_i3_tr F2 MU WM DJF.
  - clear - HBC'. lia.
  - rewrite LSQ in BOK'. exact BOK'.
  - exact HS1.
  - exact HST.
Qed.

End CANSEC1.
