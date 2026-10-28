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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_inl_initfse_S1.
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

Lemma sqs_i1_cut : forall (m1 : amem) A cs i, rw_cells bsegs m1 A cs ->
  rw_cells bsegs m1 A (firstn i cs) /\ rw_cells bsegs m1 (A + Z.of_nat (cells_size (firstn i cs))) (skipn i cs).
Proof. intros m1 A cs i H. apply rw_cells_app. rewrite firstn_skipn. exact H. Qed.

Lemma sqs_i1_join : forall (m1 : amem) A B c1 c2, rw_cells bsegs m1 A c1 -> rw_cells bsegs m1 B c2 ->
  B = A + Z.of_nat (cells_size c1) -> rw_cells bsegs m1 A (c1 ++ c2).
Proof. intros m1 A B c1 c2 H1 H2 E. subst B. apply rw_cells_app. split; [exact H1 | exact H2]. Qed.

Local Ltac sqs_pp H k :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let post := eval cbn [skipn] in (skipn k cs) in
    change (rw_cells sg mm A (pre ++ post)) in H
  end.
Local Ltac sqs_cut H k X H1 H2 :=
  destruct (sqs_i1_cut _ _ _ k H) as (H1 & H2); clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  lazymatch type of H2 with rw_cells _ _ ?A _ => replace A with X in H2 by (clear; lia) end.
Local Ltac sqs_tr H MU WM GF :=
  eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - GF; lia].
Local Ltac sqs_aeq := cbn [cells_size csize Nat.add length sbd_cells]; clear; lia.

Lemma sqs_i1_ok : forall P OEND LLO LEND LOCV, sqs_static P OEND LLO LEND LOCV ->
  (v_LLT P + 4104 < 2^47 /\ v_OFT P + 2056 < 2^47 /\ v_MLT P + 4104 < 2^47) ->
  ai_I3 P OEND LLO LEND LOCV -> ai_I1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST TST CONT. unfold ai_I1.
  intros m1 jseq jpad j72 w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw bc ptr x5 x6 x7 x12 x14 x15 x16 x17 x18 x22 x23 x26 x28 x29 x30 INV HBC BOK.
  pose proof (sqs_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_itbl_asan _ _ _ _ _ _ _ _ ST INV) as ATB3.
  pose proof (sqs_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof INV as (_ & _ & _ & TLL & TOF & _).
  apply (sqs_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF PT SQB _ UFL _ _ _ UD RD RDS. clear INV.
  pose proof sq_inl_initfse_S1_proof as IFS. unfold sq_inl_initfse_S1_stmt, sq_inl_initfse_S1_stmt_if in IFS.
  unfold ai_I3 in CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv delta [sqs_iffB sqs_iffC] in *.
  cbn [sqs_asan sqs_astat sqs_pro v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  AZ_seq_s_lkit.sd_static_open ST. unfold held in *.
  destruct AS as (_ & _ & ARS & _ & ACL & _ & _ & _ & _ & ART).
  destruct S61 as (_ & _ & _ & _ & ED8 & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ATB3 as (ATLL & ATOF & _). destruct TST as (TS1 & TS2 & _).
  (* [comment removed for export] *)
  sqs_pp FRF 7%nat. destruct (sqs_cbst48 _ _ _ _ _ FRF) as (u1 & u2 & j88 & FRF1). clear FRF. cbn [app] in FRF1.
  sqs_cut FRF1 1%nat (FF + 32) F0 FRF2. sqs_cut FRF2 6%nat (FF + 32 + 40) BDC FRF3. sqs_cut FRF3 2%nat (FF + 32 + 56) STC F2.
  unfold dctx_ptrs in PT. sqs_cut PT 2%nat (DCTX + 16) PT0 PT1. sqs_cut PT1 1%nat (DCTX + 24) PT2 PT3. clear PT0 PT3.
  assert (GS : (FF + 32) mod 8 = 0 /\ 4096 <= FF + 32 /\ FF + 32 + 56 < 2^47 /\ FF + 256 <= FRB).
  { clear - S17 S18 S47 S49 S50 S51. Z.div_mod_to_equations. lia. }
  destruct GS as (G1 & G2 & G3 & GF).
  assert (GD : DCTX + 24 < 2^47 /\ DCTX mod 8 = 0 /\ (FF + 32 + 56 <= DCTX + 16 \/ DCTX + 24 <= FF + 32)).
  { clear - S20 S54 ED8. Z.div_mod_to_equations. lia. }
  destruct GD as (G4 & G5 & G6).
  pose proof (proj1 OKLL) as TRL. pose proof (proj1 OKOF) as TRO. cbn [kind_maxLog] in TRL, TRO.
  assert (GT : 4096 <= LLT /\ LLT + 8 * (1 + 2 ^ st_log tLL) < 2^47 /\ LLT mod 4 = 0 /\ (FF + 32 + 56 <= LLT \/ LLT + 8 * (1 + 2 ^ st_log tLL) <= FF + 32) /\
               4096 <= OFT /\ OFT + 8 * (1 + 2 ^ st_log tOF) < 2^47 /\ OFT mod 4 = 0 /\ (FF + 32 + 56 <= OFT \/ OFT + 8 <= FF + 32)).
  { pose proof (Z.pow_le_mono_r 2 (st_log tLL) 9) as PML. pose proof (Z.pow_le_mono_r 2 (st_log tOF) 8) as PMO.
    pose proof (Z.pow_nonneg 2 (st_log tLL)) as PPL. pose proof (Z.pow_nonneg 2 (st_log tOF)) as PPO.
    set (EL := 2 ^ st_log tLL) in *. set (EO := 2 ^ st_log tOF) in *. clearbody EL EO.
    change (2 ^ 9) with 512 in PML. change (2 ^ 8) with 256 in PMO.
    clear - S21 S22 S44 S45 S58 S59 TS1 TS2 TRL TRO PML PMO PPL PPO. Z.div_mod_to_equations. lia. }
  destruct GT as (G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (GQ : SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) < 2^47 /\ 1 <= Z.of_nat (length (map (Z_to_bv 8) sq)) /\
               (FF + 32 + 56 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32)).
  { rewrite LSQ. clear - S14 S15 S56. lia. }
  destruct GQ as (G15 & G16 & G17).
  assert (HB1 : 0 <= bc <= 64) by (clear - HBC; lia).
  assert (HB2 : 64 <= 82) by (clear; lia).
  assert (BOKS : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (rewrite LSQ; exact BOK).
  assert (AFF : aro RNG m1 (FF + 32) 112).
  { split; [exact UFL|]. split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOBD : aro RNG m1 (FF + 32) 40) by (eapply aro_sub; [exact AFF | clear; lia | clear; lia | clear; lia]).
  assert (AOST : aro RNG m1 (FF + 32 + 40) 16) by (eapply aro_sub; [exact AFF | clear; lia | clear; lia | clear; lia]).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (ABS : app_blk (FF + 32 + 40) (FF + 32 + 56)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOSQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))) by (rewrite LSQ; apply aregU_aro; apply ARS; clear - S15; lia).
  assert (ADC : aro RNG m1 DCTX DCTX_SIZEOF) by (split; [exact UD | split; [exact RD | exact RDS]]).
  assert (AOD : aro RNG m1 (DCTX + 16) 8) by (eapply aro_sub; [exact ADC | clear; lia | clear; lia | unfold DCTX_SIZEOF; clear; lia]).
  assert (PPO : 0 <= 2 ^ st_log tOF) by (apply Z.pow_nonneg; lia).
  assert (AOO : aro RNG m1 OFT 8) by (eapply aro_sub; [exact ATOF | clear; lia | clear; lia | clear - PPO; lia]).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (IFS RNG (Z_to_bv 64 nbSeq) (Z_to_bv 64 FRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 FRB) x12 x14 x15 x16 x17
                x18 x22 x23 (Z_to_bv 64 DST) x26 (Z_to_bv 64 SHF) x28 x29 x30 (Z_to_bv 64 (DCTX + 29896))
                F fc m1 (FF + 32) LLT SEQ 64 bc ptr DCTX OFT cw u1 u2 jpad (map (Z_to_bv 8) sq) K_LL tLL K_OF tOF);
      first [ assumption | exact I ]. }
  intros ms' POST. unfold sq_inl_initfse_S1_post in POST.
  destruct POST as (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x2' & m' & cw' & bc' & jpad' & ptr' & sv & -> & MU & WM & MI' & BDC' & STC' & EA0 & EA1 & EA3 & EX2 & HST & HBC' & BOK').
  subst a0' a1' a3' x2'. rewrite LSQ in BOK'.
  assert (MU2 : munch [(FRB, FRB + 280); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
  eapply CONT.
  - eapply sqs_iinv_eq2.
    + eapply TRANS; [exact MU2 | exact WM | exact MI' | sqs_tr FR MU WM GF |].
      eapply (sqs_i1_join _ _ (FF + 32)); [sqs_tr F0 MU WM GF | | sqs_aeq].
      eapply (sqs_i1_join _ _ (FF + 32 + 40)); [exact BDC' | | sqs_aeq].
      eapply (sqs_i1_join _ _ (FF + 32 + 56)); [exact STC' | sqs_tr F2 MU WM GF | sqs_aeq].
    + reflexivity.
    + cbn [app sbd_cells]. reflexivity.
  - clear - HBC'; lia.
  - exact BOK'.
  - exact HST.
Qed.

End CANSEC1.
