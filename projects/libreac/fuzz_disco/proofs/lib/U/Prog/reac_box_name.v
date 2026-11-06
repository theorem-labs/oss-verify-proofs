From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model box_name_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c memcpy_c strlen_c
  box_name_ucall box_name_ubase box_name_useg_end box_name_useg_dp box_name_useg_tkz box_name_useg_tok box_name_useg_cmp box_name_useg_stem.
Import ListNotations.
Open Scope Z_scope.

Section BoxName.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
          (sd : list Z).
Hypothesis SBCH : sb_ch_contract.
Hypothesis DEC : sb_dec_contract.
Hypothesis MC : memcpy_contract.
Hypothesis SL : strlen_contract.

Notation S := (bv_unsigned sp).
Notation SVC := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation ACC := (bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                   (bv_unsigned display) (bv_unsigned display_len)).
Notation NM := (bn_NM f sd i o).
Notation LN := (firstn 23 NM).
Notation NOV := (if 23 <? Z.of_nat (length NM) then 1 else 0).
Hypothesis HIM : bn_image m (S - BN_K) S.

Notation W4 := (bn_w4 i o).
Notation STM := (bn_stem f sd).
Notation Q0 := (QQ ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo f i o display display_len sd).

Lemma seg_go : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (jds jrd jbd jrt jbt jrn jbn jrw jg3 jbw : list byte) (P : Z),
  lo + BN_K <= S -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  bn_cstr m (S - BN_K) S P STM ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 16 jds] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] -> rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] -> rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  rw_cells rsegs m2 (S + -200) [CB 32 jrn] -> rw_cells rsegs m2 (S + -168) [CB 24 jbn] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jrw] -> rw_cells rsegs m2 (S + -112) [CB 3 jg3] ->
  rw_cells rsegs m2 (S + -109) [CB 5 jbw] ->
  0 < P ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 x11 x12 x13 display x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) (Z_to_bv 64 P) display_len x25 x26 x27
                        x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14f00) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jds jrd jbd jrt jbt jrn jbn jrw
    jg3 jbw P HLO S16 AOK BUFS CS ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 RN2 BN2 RW2 G32 BW2 P0.
  destruct CS as (STC & sl & STB & SLK & PD). cbn [disjoint_from] in PD. destruct PD as [PD _].
  eapply seg_stem; try eassumption; try apply stem_ne; unfold BN_K in *; lia.
Qed.

Lemma seg_sel : forall (m2 : word -> option byte)
    (x1 x5 x6 x7 x9 x10 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 : word)
    (jds jrd jbd jrt jbt jrn jbn jrw jg3 jbw : list byte),
  lo + BN_K <= S -> -2^31 <= f < 2^31 -> S mod 16 = 0 ->
  bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len) i o = true ->
  bn_said m (S - BN_K) S (bv_unsigned a1) sd ->
  bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
          (bv_unsigned display) (bv_unsigned display_len) ->
  stk rsegs m2 lo (S + -352) -> munch [(S - BN_K, S)] m m2 -> wmono rsegs m m2 -> mem_inv rsegs m2 ->
  rw_cells rsegs m2 (S + -104) SVC ->
  rw_cells rsegs m2 (S + -352) [CB 16 jds] ->
  rw_cells rsegs m2 (S + -336) [CB 32 jrd] -> rw_cells rsegs m2 (S + -304) [CB 48 jbd] ->
  rw_cells rsegs m2 (S + -256) [CB 32 jrt] -> rw_cells rsegs m2 (S + -224) [CB 24 jbt] ->
  rw_cells rsegs m2 (S + -200) [CB 32 jrn] -> rw_cells rsegs m2 (S + -168) [CB 24 jbn] ->
  rw_cells rsegs m2 (S + -144) [CB 32 jrw] -> rw_cells rsegs m2 (S + -112) [CB 3 jg3] ->
  rw_cells rsegs m2 (S + -109) [CB 5 jbw] ->
  evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 x10 (Z_to_bv 64 f)
                        x12 x13 display x15 x16 x17
                        a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                        display_len x25 x26 x27 x28 x29 x30 x31)
                   F (Z_to_bv 64 0x14ec8) fc None m2 (seg_rom rsegs)).
Proof.
  intros m2 x1 x5 x6 x7 x9 x10 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 jds jrd jbd jrt jbt jrn jbn jrw jg3
    jbw HLO Hf S16 AOK SAID BUFS ST2 MU2 WM2 MI2 SV2 DS2 RD2 BD2 RT2 BT2 RN2 BN2 RW2 G32 BW2.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof HIM as (TB & TD & C1 & C2 & C3 & C0 & _).
  assert (TBL : sd = [] -> forall y10 : word,
    evt rsegs Q0 (MS (mkR x1 (Z_to_bv 64 (S + -352)) gp tp x5 x6 x7 a6 x9 y10 (Z_to_bv 64 f)
                          x12 x13 display x15 x16 x17
                          a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x14ed4) fc None m2 (seg_rom rsegs))).
  { intros Hsd y10. set (QL := Q0).
    assert (ESTM : bn_stem f sd = bn_STEM f) by (rewrite Hsd; reflexivity).
    pose proof (bytes_at_transport rsegs _ _ _ _ _ TB MU2 TD) as TB2.
    apply bytes_at_app in TB2. destruct TB2 as [T1 T23]. rewrite length_le8 in T23.
    apply bytes_at_app in T23. destruct T23 as [T2 T3]. rewrite length_le8 in T3.
    unfold BN_K in *.
    step. step. step.
    rewrite tbl_chk by lia.
    destruct (Z.leb_spec 1 f) as [F1|F1]; destruct (Z.leb_spec f 3) as [F3|F3]; cbn [andb negb]; cbv iota.
    - assert (EF : f = 1 \/ f = 2 \/ f = 3) by lia.
      destruct EF as [EF|[EF|EF]]; rewrite EF; do 4 step; fold_tbl.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T1 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + 0)) with (Z_to_bv 64 132600) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S1); try eassumption; try (unfold BN_S1, BN_S2, BN_S3, BN_REAC; lia). rewrite ESTM, EF. exact C1.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T2 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + Z.of_nat 8 + 0)) with (Z_to_bv 64 132608) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S2); try eassumption; try (unfold BN_S1, BN_S2, BN_S3, BN_REAC; lia). rewrite ESTM, EF. exact C2.
      + pose proof (bytes_at_read rsegs m2 _ _ 0 8 T3 ltac:(lia) ltac:(rewrite length_le8; lia)) as HR.
        change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
        rewrite firstn_all2 in HR by (rewrite length_le8; lia).
        replace (wa (BN_TS + Z.of_nat 8 + Z.of_nat 8 + 0)) with (Z_to_bv 64 132616) in HR by reflexivity.
        step. step.
        eapply seg_go with (P := BN_S3); try eassumption; try (unfold BN_S1, BN_S2, BN_S3, BN_REAC; lia). rewrite ESTM, EF. exact C3.
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption; [rewrite ESTM, (STEM_other f) by lia; exact C0 | unfold BN_REAC; lia].
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption; [rewrite ESTM, (STEM_other f) by lia; exact C0 | unfold BN_REAC; lia].
    - step. step.
      eapply seg_go with (P := BN_REAC); try eassumption; [rewrite ESTM, (STEM_other f) by lia; exact C0 | unfold BN_REAC; lia]. }
  step.
  rewrite bl_eqb0.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [Hz|Hz]; cbv iota.
  - destruct SAID as [(_ & Hsd)|(Hne & _)]; [|contradiction]. exact (TBL Hsd x10).
  - destruct SAID as [(E & _)|(_ & CS)]; [lia|].
    pose proof CS as (SC & sl & SB & SLK & SPD). cbn [disjoint_from] in SPD. destruct SPD as [SPD _].
    unfold BN_K in *.
    pose proof (bytes_at_transport rsegs _ _ _ _ _ SB MU2
                  ltac:(cbn [disjoint_from]; rewrite length_app, bn_bytes_length; cbn [length]; split; [lia|exact I]))
      as SB2.
    destruct (list_eq_dec Z.eq_dec sd []) as [Hsd|Hsd].
    + pose proof (bytes_at_read rsegs m2 _ _ 0 1 SB2 ltac:(lia)
                    ltac:(rewrite length_app, bn_bytes_length; cbn [length]; lia)) as HR.
      rewrite Hsd in HR. change (Z.to_nat 0) with 0%nat in HR. rewrite skipn0 in HR.
      change (firstn 1 (bn_bytes [] ++ Z_to_bv 8 0 :: sl)) with [Z_to_bv 8 0] in HR.
      replace (wa (bv_unsigned a1 + 0)) with a1 in HR
        by (symmetry; unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      step. step.
      try (rewrite bl_zxb by lia). try (rewrite (bl_eqb 0 0) by lia). cbn [negb Z.eqb]. cbv iota.
      exact (TBL Hsd _).
    + pose proof (proj1 (proj1 (bytes_at_app rsegs _ _ _ _) SB2)) as SB3.
      assert (L1 : (0 < length sd)%nat)
        by (apply Nat.neq_0_lt_0; intro E0; apply length_zero_iff_nil in E0; contradiction).
      assert (R0 : 0 < nth 0 sd 0 < 256) by (rewrite Forall_forall in SC; apply SC; apply nth_In; lia).
      pose proof (rd_nth m2 _ sd 0 SB3 L1) as HR.
      replace (Z_to_bv 64 (bv_unsigned a1 + Z.of_nat 0)) with a1 in HR
        by (symmetry; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      step. rewrite bl_zxb by lia.
      step.
      rewrite bl_eqb by lia. replace (nth 0 sd 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace a1 with (Z_to_bv 64 (bv_unsigned a1)) by (apply Z_to_bv_bv_unsigned).
      eapply seg_go with (P := bv_unsigned a1); try eassumption; try (unfold BN_S1, BN_S2, BN_S3, BN_REAC; lia). rewrite (stem_sd f sd Hsd). exact CS.
Qed.

Lemma bn_main : forall (a0 a2 a3 : word),
  a0 = Z_to_bv 64 f -> -2^31 <= f < 2^31 ->
  a2 = Z_to_bv 64 i -> -2^31 <= i < 2^31 ->
  a3 = Z_to_bv 64 o -> -2^31 <= o < 2^31 ->
  bytes_at rsegs m S (le8 display ++ le8 display_len) ->
  stk rsegs m lo S -> lo + BN_K <= S -> S mod 16 = 0 ->
  (bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
              (bv_unsigned display) (bv_unsigned display_len) i o = true ->
     bn_said m (S - BN_K) S (bv_unsigned a1) sd /\
     bn_bufs m (S - BN_K) S (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
             (bv_unsigned display) (bv_unsigned display_len)) ->
  mem_inv rsegs m ->
  evt rsegs Q0 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 REAC_BOX_NAME) fc None m (seg_rom rsegs)).
Proof.
  intros a0 a2 a3 -> Hf -> Hi -> Ho DSB ST HLO S16 PRE MI.
  unfold REAC_BOX_NAME. unfold BN_K in HLO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (Hlo0 : 0 <= lo) by (destruct ST as (Q & _); exact Q).
  pose proof (bytes_at_bound rsegs m _ _ DSB) as DSR. rewrite length_app, !length_le8 in DSR.
  apply bytes_at_app in DSB. destruct DSB as [DSa DSb]. rewrite length_le8 in DSb.
  assert (DSH : bytes_at rsegs m S (le8 display) /\ bytes_at rsegs m (S + 8) (le8 display_len)).
  { split; [exact DSa|]. replace (S + 8) with (S + Z.of_nat 8) by lia. exact DSb. }
  clear DSa DSb.
  carve_frame 104%nat ST. rename FR into FRS.
  carve_frame 5%nat ST. rename FR into FBW.
  carve_frame 3%nat ST. rename FR into FG3.
  carve_frame 32%nat ST. rename FR into FRW.
  carve_frame 24%nat ST. rename FR into FBN.
  carve_frame 32%nat ST. rename FR into FRN.
  carve_frame 24%nat ST. rename FR into FBT.
  carve_frame 32%nat ST. rename FR into FRT.
  carve_frame 48%nat ST. rename FR into FBD.
  carve_frame 32%nat ST. rename FR into FRD.
  carve_frame 16%nat ST. rename FR into FDS.
  pose proof (munch_refl [(S - 416, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  do 13 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => first [is_var mm; rename mm into m1 | set (m1 := mm) in *] end.
  destruct DSH as [DSa0 DSb0].
  pose proof (bytes_at_transport rsegs _ _ _ _ _ DSa0 MU
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia|exact I])) as DSa.
  pose proof (bytes_at_transport rsegs _ _ _ _ _ DSb0 MU
                ltac:(cbn [disjoint_from]; rewrite length_le8; split; [lia|exact I])) as DSb.
  clear DSa0 DSb0.
  pose proof (bytes_at_read rsegs m1 _ _ 0 8 DSa ltac:(lia) ltac:(rewrite length_le8; lia)) as RDa.
  pose proof (bytes_at_read rsegs m1 _ _ 0 8 DSb ltac:(lia) ltac:(rewrite length_le8; lia)) as RDb.
  change (Z.to_nat 0) with 0%nat in RDa, RDb. rewrite skipn0 in RDa, RDb.
  rewrite firstn_all2 in RDa by (rewrite length_le8; lia).
  rewrite firstn_all2 in RDb by (rewrite length_le8; lia).
  replace (wa (S + 0)) with sp in RDa by (symmetry; unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
  replace (wa (S + 8 + 0)) with (Z_to_bv 64 (S + 8)) in RDb by (unfold wa; f_equal; lia).
  clear DSa DSb.
  lazymatch goal with H : rw_cells rsegs m1 (S + -104) _ |- _ => rename H into SV1 end.
  assert (SV2 : rw_cells rsegs m1 (S + -104) SVC)
    by (first [exact SV1 | eapply rw_cells_conv; [exact SV1 | cbn; tauto | reflexivity]]).
  clear SV1.
  assert (STF : stk rsegs m1 lo (S + -104)).
  { pose proof (stk_of_rw_cells rsegs _ _ _ FDS) as K1. pose proof (stk_of_rw_cells rsegs _ _ _ FRD) as K2.
    pose proof (stk_of_rw_cells rsegs _ _ _ FBD) as K3. pose proof (stk_of_rw_cells rsegs _ _ _ FRT) as K4.
    pose proof (stk_of_rw_cells rsegs _ _ _ FBT) as K5. pose proof (stk_of_rw_cells rsegs _ _ _ FRN) as K6.
    pose proof (stk_of_rw_cells rsegs _ _ _ FBN) as K7. pose proof (stk_of_rw_cells rsegs _ _ _ FRW) as K8.
    pose proof (stk_of_rw_cells rsegs _ _ _ FG3) as K9. pose proof (stk_of_rw_cells rsegs _ _ _ FBW) as K10.
    cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5, K6, K7, K8, K9, K10.
    pose proof (stk_glue _ _ _ _ _ ST K1 ltac:(lia) ltac:(lia)) as G1.
    pose proof (stk_glue _ _ _ _ _ G1 K2 ltac:(lia) ltac:(lia)) as G2.
    pose proof (stk_glue _ _ _ _ _ G2 K3 ltac:(lia) ltac:(lia)) as G3.
    pose proof (stk_glue _ _ _ _ _ G3 K4 ltac:(lia) ltac:(lia)) as G4.
    pose proof (stk_glue _ _ _ _ _ G4 K5 ltac:(lia) ltac:(lia)) as G5.
    pose proof (stk_glue _ _ _ _ _ G5 K6 ltac:(lia) ltac:(lia)) as G6.
    pose proof (stk_glue _ _ _ _ _ G6 K7 ltac:(lia) ltac:(lia)) as G7.
    pose proof (stk_glue _ _ _ _ _ G7 K8 ltac:(lia) ltac:(lia)) as G8.
    pose proof (stk_glue _ _ _ _ _ G8 K9 ltac:(lia) ltac:(lia)) as G9.
    pose proof (stk_glue _ _ _ _ _ G9 K10 ltac:(lia) ltac:(lia)) as G10.
    eapply stk_ext; [exact G10|lia]. }
  assert (REF : forall (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
                        y29 y30 y31 : word),
    bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
               (bv_unsigned display) (bv_unsigned display_len) i o = false ->
    evt rsegs Q0 (MS (mkR y1 (Z_to_bv 64 (S + -352)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (-1)) y11 y12 y13 y14 y15
                          y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                     F (Z_to_bv 64 0x15254) fc None m1 (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 AF.
    eapply seg_epi; [unfold BN_K; lia | exact STF | exact SV2 | exact WM | exact MI |].
    unfold bn_res, bn_accept. rewrite AF. cbn [andb]. unfold BN_K. split; [reflexivity|exact MU]. }
  step. step. step. step.
  step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned display_len) 0) as [D0|D0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a7) 0) as [T0|T0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a5) 0) as [N0|N0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a4) 0) as [M0|M0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned a6) 0) as [K0|K0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  step. step.
  rewrite bl_eqb0. destruct (Z.eqb_spec (bv_unsigned display) 0) as [P0|P0]; cbv iota.
  { apply REF. apply args_ok_false. tauto. }
  assert (SEL : bn_ok i = true -> bn_ok o = true -> ~ (i = 0 /\ o = 0) -> forall y10 y12 y13 : word,
    evt rsegs Q0 (MS (mkR ra (Z_to_bv 64 (S + -352)) gp tp t0 t1 t2 a6 s1 y10 (Z_to_bv 64 f)
                          y12 y13 display a5 a6 a7 a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14ec8) fc None m1 (seg_rom rsegs))).
  { intros OKI OKO NZ y10 y12 y13.
    assert (AOK : bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                             (bv_unsigned display) (bv_unsigned display_len) i o = true)
      by (apply args_ok_true; assumption).
    destruct (PRE AOK) as [SAID BUFS].
    eapply seg_sel; try eassumption; unfold BN_K; lia. }
  assert (OK2 : forall y12 y13 : word, bn_ok i = true -> o <> 0 ->
    evt rsegs Q0 (MS (mkR ra (Z_to_bv 64 (S + -352)) gp tp t0 t1 t2 a6 s1 (Z_to_bv 64 (-1)) (Z_to_bv 64 f)
                          y12 y13 display a5 a6 a7 a4 a7 a5 (Z_to_bv 64 o) (Z_to_bv 64 i) a1
                          display_len s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x14eb4) fc None m1 (seg_rom rsegs))).
  { intros y12 y13 OKI O0.
    step. step. step.
    rewrite addiw_chk by lia.
    destruct (Z.leb_spec 2 o); destruct (Z.leb_spec o 40); cbn [andb negb]; cbv iota;
      [| apply REF; apply args_ok_false; right; right; right; right; right; right; right; left;
         apply bn_ok_out; lia ..].
    step. step.
    rewrite land_chk by lia.
    destruct (Z.even o) eqn:EV; cbn [negb]; cbv iota.
    - apply SEL; [exact OKI | apply bn_ok_in; [lia | exact EV] | lia].
    - apply REF. apply args_ok_false. right; right; right; right; right; right; right; left.
      apply bn_ok_odd; assumption. }
  step. step. step.
  rewrite bl_eqb0s by lia.
  destruct (Z.eqb_spec i 0) as [I0|I0]; cbv iota.
  - step.
    rewrite bl_eqb0s by lia.
    destruct (Z.eqb_spec o 0) as [O0|O0]; cbv iota.
    + apply REF. apply args_ok_false. tauto.
    + apply OK2; [apply bn_ok_0; exact I0 | exact O0].
  - step. step. step.
    rewrite addiw_chk by lia.
    destruct (Z.leb_spec 2 i); destruct (Z.leb_spec i 40); cbn [andb negb]; cbv iota;
      [| apply REF; apply args_ok_false; right; right; right; right; right; right; left;
         apply bn_ok_out; lia ..].
    step. step.
    rewrite land_chk by lia.
    destruct (Z.even i) eqn:EV; cbn [negb]; cbv iota.
    + assert (OKI : bn_ok i = true) by (apply bn_ok_in; [lia | exact EV]).
      step.
      rewrite bl_eqb0s by lia.
      destruct (Z.eqb_spec o 0) as [O0|O0]; cbn [negb]; cbv iota.
      * step. apply SEL; [exact OKI | apply bn_ok_0; exact O0 | lia].
      * apply OK2; [exact OKI | exact O0].
    + apply REF. apply args_ok_false. right; right; right; right; right; right; left.
      apply bn_ok_odd; assumption.
Qed.

End BoxName.

Theorem reac_box_name_holds :
  sb_dec_contract -> sb_ch_contract -> memcpy_contract -> strlen_contract -> reac_box_name_contract.
Proof.
  intros DEC SBCH MC SL. unfold reac_box_name_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo f i o
    display display_len sd E0 Hf E2 Hi E3 Ho DSB ST HLO S16 HIM PRE MI.
  eapply bn_main; eassumption.
Qed.
