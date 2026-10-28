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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_fin AZ_seq_inl_bitinit_S1.
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

Lemma sqs_i0_cut : forall (m1 : amem) A cs i, rw_cells bsegs m1 A cs ->
  rw_cells bsegs m1 A (firstn i cs) /\ rw_cells bsegs m1 (A + Z.of_nat (cells_size (firstn i cs))) (skipn i cs).
Proof. intros m1 A cs i H. apply rw_cells_app. rewrite firstn_skipn. exact H. Qed.

Lemma sqs_i0_join : forall (m1 : amem) A B c1 c2, rw_cells bsegs m1 A c1 -> rw_cells bsegs m1 B c2 ->
  B = A + Z.of_nat (cells_size c1) -> rw_cells bsegs m1 A (c1 ++ c2).
Proof. intros m1 A B c1 c2 H1 H2 E. subst B. apply rw_cells_app. split; [exact H1 | exact H2]. Qed.

Local Ltac sqs_pp H k :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let post := eval cbn [skipn] in (skipn k cs) in
    change (rw_cells sg mm A (pre ++ post)) in H
  end.
Local Ltac sqs_w8 H k a := sqs_pp H k; let H' := fresh in destruct (cb8_as_c8 _ _ _ _ _ _ H) as (a & H'); clear H; rename H' into H; cbn [app] in H.
Local Ltac sqs_w16 H k a b := sqs_pp H k; let H' := fresh in destruct (sqs_cb16_words _ _ _ _ _ H) as (a & b & H'); clear H; rename H' into H; cbn [app] in H.
Local Ltac sqs_w24 H k a b c := sqs_pp H k; let H' := fresh in destruct (sqs_cb24_words _ _ _ _ _ H) as (a & b & c & H'); clear H; rename H' into H; cbn [app] in H.
Local Ltac sqs_cut H k X H1 H2 :=
  destruct (sqs_i0_cut _ _ _ k H) as (H1 & H2); clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  lazymatch type of H2 with rw_cells _ _ ?A _ => replace A with X in H2 by (clear; lia) end.
Local Ltac sqs_tr H MU WM GF :=
  eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - GF; lia].
Local Ltac sqs_aeq := cbn [cells_size csize Nat.add length sbd_cells]; clear; lia.

Lemma sqs_i0_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV ->
  sqs_at_ierr P OEND LLO LEND LOCV -> ai_I1 P OEND LLO LEND LOCV -> ai_I0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST IERR CONT. unfold ai_I0.
  intros m1 ja jb jc jd je jseq jbd j72 p0 p1 p2 T48 T56 T64 T128 T176 T184 A2 A4 A5 x5 x6 x7 x10 x11 x22 x26 x28 x29 x30
         INV E48 E56 E64 E128 E176 E184 EA2 EA4 EA5 HN.
  subst T48 T56 T64 T128 T176 T184 A2 A4 A5.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_itbl_asan _ _ _ _ _ _ _ _ ST INV) as ATB3.
  pose proof (sqs_iff_ahull _ _ _ _ _ _ _ _ ST INV) as AHB.
  pose proof (sqs_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF PT SQB _ UFL _ _ _ UD RD RDS. clear INV.
  pose proof sq_inl_bitinit_S1_proof as BIS. unfold sq_inl_bitinit_S1_stmt in BIS.
  unfold ai_I1 in CONT. unfold sqs_at_ierr in IERR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_iffA sqs_iffB] in *.
  cbn [sqs_asan sqs_astat sqs_pro v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  AZ_seq_s_lkit.sd_static_open ST. unfold held in *.
  destruct AS as (_ & _ & ARS & _ & _ & _ & _ & _ & AZS & ART).
  destruct S61 as (ASTK & _ & _ & _ & ED8 & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ATB3 as (ATLL & _ & _). destruct ASTK as (_ & RLO & RAI).
  sqs_w24 FR 18%nat w200 w208 w216.
  sqs_w24 FR 14%nat w152 w160 y168.
  sqs_w8 FR 7%nat w96.
  sqs_w16 FR 5%nat w72 w80.
  sqs_pp FR 1%nat. apply (rw_cells_split_CB _ _ _ _ 32%nat ja _ [8; 24]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  sqs_w8 FR 1%nat w16.
  sqs_w24 FR 2%nat y24 y32 y40.
  sqs_cut FR 2%nat (FRB + 24) FA FR1. sqs_cut FR1 3%nat (FRB + 48) FB FR2. sqs_cut FR2 15%nat (FRB + 168) FC FR3. sqs_cut FR3 1%nat (FRB + 176) FD FE.
  sqs_cut FRF 1%nat (FF + 32) F0 FRF1. sqs_cut FRF1 1%nat (FF + 32 + 40) BDC F2.
  unfold dctx_ptrs in PT. sqs_cut PT 1%nat (DCTX + 8) PT0 PT1. clear PT1.
  assert (GS : (FF + 32) mod 8 = 0 /\ 4096 <= FF + 32 /\ FF + 32 + 40 < 2^47 /\ 4096 <= FRB /\ FRB + 176 < 2^47 /\ FRB mod 8 = 0 /\
               (FF + 32 + 40 <= FRB + 24 \/ FRB + 48 <= FF + 32) /\ (FF + 32 + 40 <= FRB + 168 \/ FRB + 176 <= FF + 32) /\
               FF + 256 <= FRB /\ lo <= FRB /\ FRB + 280 <= SPV).
  { clear - S17 S18 S47 S48 S49 S50 S51. Z.div_mod_to_equations. lia. }
  destruct GS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GF & GLO & GSP).
  assert (GQ : (FF + 32 + 40 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ (FRB + 176 <= SEQ \/ SEQ + zlen sq <= FRB + 24)).
  { clear - S17 S18 S47 S25 S56. lia. }
  destruct GQ as (G9 & G10).
  assert (GD : DCTX + 8 < 2^47 /\ DCTX mod 8 = 0 /\ (FF + 32 + 40 <= DCTX \/ DCTX + 8 <= FF + 32) /\ (FRB + 176 <= DCTX \/ DCTX + 8 <= FRB + 24)).
  { clear - S17 S18 S20 S27 S47 S54 ED8. Z.div_mod_to_equations. lia. }
  destruct GD as (G11 & G12 & G13 & G14).
  assert (GL : 4096 <= LLT /\ LLT + 8 < 2^47 /\ LLT mod 4 = 0).
  { clear - S21 S44. Z.div_mod_to_equations. lia. }
  destruct GL as (G15 & G16 & G17).
  assert (LSQ : zlen (map (Z_to_bv 8) sq) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  assert (AFF : aro RNG m1 (FF + 32) 112).
  { split; [exact UFL|]. split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOBD : aro RNG m1 (FF + 32) 40) by (eapply aro_sub; [exact AFF | clear; lia | clear; lia | clear; lia]).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOSQ : aro RNG m1 SEQ (zlen sq)) by (apply aregU_aro; apply ARS; clear - S15; lia).
  assert (ABF1 : app_blk (FRB + 24) (FRB + 48)).
  { replace (FRB + 48) with (FRB + 24 + 24) by (clear; lia). eapply azstk_app; [exact AZS | clear - GLO; lia | clear; lia | clear - GSP; lia]. }
  assert (ABF2 : app_blk (FRB + 168) (FRB + 176)).
  { replace (FRB + 176) with (FRB + 168 + 8) by (clear; lia). eapply azstk_app; [exact AZS | clear - GLO; lia | clear; lia | clear - GSP; lia]. }
  assert (RF1 : rng RNG (FRB + 24) 24) by (eapply rng_sub; [exact RLO | clear - GLO; lia | clear - GSP; lia]).
  assert (RF2 : rng RNG (FRB + 168) 8) by (eapply rng_sub; [exact RLO | clear - GLO; lia | clear - GSP; lia]).
  assert (ADC : aro RNG m1 DCTX DCTX_SIZEOF) by (split; [exact UD | split; [exact RD | exact RDS]]).
  assert (AOD : aro RNG m1 DCTX 8) by (eapply aro_sub; [exact ADC | clear; lia | clear; lia | unfold DCTX_SIZEOF; clear; lia]).
  assert (PPL : 0 <= 2 ^ st_log tLL) by (apply Z.pow_nonneg; lia).
  assert (AOL : aro RNG m1 LLT 8) by (eapply aro_sub; [exact ATLL | clear; lia | clear; lia | clear - PPL; lia]).
  assert (MUW : forall m2, munch [(FF + 32, FF + 32 + 40); (FRB + 24, FRB + 48); (FRB + 168, FRB + 176)] m1 m2 ->
                           munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m2).
  { intros m2 MU. eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (BIS RNG (Z_to_bv 64 nbSeq) (Z_to_bv 64 FRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) x10 x11
                (Z_to_bv 64 (DCTX + 26688)) (Z_to_bv 64 PFX) (Z_to_bv 64 (DCTX + 26684)) (Z_to_bv 64 (DCTX + 26692)) (Z_to_bv 64 FF) (Z_to_bv 64 (FF + 120))
                (Z_to_bv 64 28672) x22 (Z_to_bv 64 DST) x26 (Z_to_bv 64 SHF) x28 x29 x30 (Z_to_bv 64 (DCTX + 29896))
                F fc m1 FRB (FF + 32) SEQ (zlen sq) DCTX LLT y24 y32 y40 y168 (map (Z_to_bv 8) sq) jbd);
      assumption. }
  intros ms' POST. unfold sq_inl_bitinit_S1_post in POST.
  destruct POST as [(a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x7' & m' & cw & bc & jpad & -> & MU & WM & MI' & BDC' & FB' & FD' & EA0 & EA1 & EA3 & HBC & _)
                   |(a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x7' & m' & bs & z24 & z32 & z40 & z168 & -> & MU & WM & MI' & BDC' & FB' & FD')].
  - (* [comment removed for export] *)
    subst a0' a1' a3'. pose proof (MUW m' MU) as MU2.
    eapply CONT.
    + eapply sqs_iinv_eq2.
      * eapply TRANS; [exact MU2 | exact WM | exact MI' | |].
        -- eapply (sqs_i0_join _ _ (FRB + 24)); [sqs_tr FA MU WM GF | | sqs_aeq].
           eapply (sqs_i0_join _ _ (FRB + 48)); [exact FB' | | sqs_aeq].
           eapply (sqs_i0_join _ _ (FRB + 168)); [sqs_tr FC MU WM GF | | sqs_aeq].
           eapply (sqs_i0_join _ _ (FRB + 176)); [exact FD' | sqs_tr FE MU WM GF | sqs_aeq].
        -- eapply (sqs_i0_join _ _ (FF + 32)); [sqs_tr F0 MU WM GF | | sqs_aeq].
           eapply (sqs_i0_join _ _ (FF + 32 + 40)); [exact BDC' | sqs_tr F2 MU WM GF | sqs_aeq].
      * cbn [app]. reflexivity.
      * cbn [app sbd_cells]. reflexivity.
    + exact HBC.
    + apply sqs_bitd_ptr_ok.

  - (* [comment removed for export] *)
    pose proof (MUW m' MU) as MU2.
    eassert (FR' : rw_cells bsegs m' FRB (_ ++ _ ++ _ ++ _ ++ _)).
    { eapply (sqs_i0_join _ _ (FRB + 24)); [sqs_tr FA MU WM GF | | sqs_aeq].
      eapply (sqs_i0_join _ _ (FRB + 48)); [exact FB' | | sqs_aeq].
      eapply (sqs_i0_join _ _ (FRB + 168)); [sqs_tr FC MU WM GF | | sqs_aeq].
      eapply (sqs_i0_join _ _ (FRB + 176)); [exact FD' | sqs_tr FE MU WM GF | sqs_aeq]. }
    eassert (FRF' : rw_cells bsegs m' FF (_ ++ _ ++ _)).
    { eapply (sqs_i0_join _ _ (FF + 32)); [sqs_tr F0 MU WM GF | | sqs_aeq].
      eapply (sqs_i0_join _ _ (FF + 32 + 40)); [exact BDC' | sqs_tr F2 MU WM GF | sqs_aeq]. }
    cbn [app] in FR', FRF'.
    sqs_blob_seg FR' 18%nat 31%nat. sqs_blob_seg FR' 13%nat 16%nat. sqs_blob_seg FR' 0%nat 12%nat. sqs_blob_seg FRF' 0%nat 7%nat.
    eapply IERR. eapply TRANS; [exact MU2 | exact WM | exact MI' | exact FR' | exact FRF'].
Qed.

End CANSEC1.
