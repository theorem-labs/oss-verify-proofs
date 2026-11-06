(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2
  Zpo Z4a Z4e Z4c Z4l Z4m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition chars (bs : list byte) : list Z := map bv_unsigned bs.
Lemma to_bytes_chars : forall bs, to_bytes (chars bs) = bs.
Proof.
  intros bs. unfold to_bytes, chars. rewrite map_map. rewrite <- (map_id bs) at 2. apply map_ext. intros b.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma chars_range : forall bs, Forall (fun c => 0 <= c < 256) (chars bs).
Proof.
  intros bs. unfold chars. induction bs as [|b bs IH]; cbn [map]; constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.
Lemma chars_length : forall bs, zlength (chars bs) = Z.of_nat (length bs).
Proof. intros bs. unfold chars, zlength. rewrite length_map. reflexivity. Qed.

Definition fa_locals2 (j0 j1 j2 : list byte) (f : Z) (jo jr : list byte) (dn : Z) (j13 jn : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 f); CB 24 jo; CB 24 jr; C8 (Z_to_bv 64 dn); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j13; CB 16 jn].

Section Top1.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc_contract_f RT 2.
Hypothesis SPL : splitinto_cpsA RT.
Hypothesis EMP : empl_cpsA RT.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma LIB_agree' : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma vblockA_length : forall A c sz, (length (vblockA A c sz) <= 3)%nat.
Proof. intros A c sz. unfold vblockA. destruct (c =? 0); [cbn; lia| apply ann_block_length]. Qed.

Definition lh_inv (Σ Σx : rts RT) (m mx : mem) (usp sp' f lo d : Z) (bs : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (h3 t jp : list byte) (szN : nat) (A : Z) (els : list (Z * Z)) : Prop :=
  ART RT Σx mx /\ mem_inv asegs mx /\ stk asegs mx lo sp'
  /\ (exists j0 j1 j2 jo jr j13 jn, rw_cells asegs mx sp' (fa_locals2 j0 j1 j2 f jo jr (d + Z.of_nat (length bs)) j13 jn))
  /\ stk asegs mx (sp' + 120) (usp - 104)
  /\ rw_cells asegs mx (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells asegs mx f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e899)) (C8 (Z_to_bv 64 0x969b0)) h3)
  /\ rw_cells asegs mx (f / 8 + 2147450880) (fa_shadow1 t)
  /\ rw_cells asegs mx (f + 96) [CB 80 jp]
  /\ vrepA mx (f + 32) A (vcap_iter szN 0 0) (Z.of_nat szN) els
  /\ bytes_at asegs mx d bs /\ LIB mx
  /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp LIB_FP m mx
  /\ vliveA (rt_live RT Σx) A (vcap_iter szN 0 0) (Z.of_nat szN) (rt_live RT Σ)
  /\ rt_frames RT Σx = [(f, 2%nat)] /\ rt_sp0 RT Σx = rt_sp0 RT Σ
  /\ rt_credit RT Σ - 2 - vcost_pushes szN 0 0 <= rt_credit RT Σx.

Definition vec_postA (Σ : rts RT) (PMc : Model -> Prop) (usp lo d : Z) (bs : list byte)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : config -> Prop :=
  fun c => exists (Σ1 : rts RT) (sp' f A : Z),
    ASTA RT Σ1 PMc (fun ms => exists (m1 : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (h3 t jp : list byte),
        ms = MS (mkR x1 (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 16) (Z_to_bv 64 A) s7 s8
                     (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
                F (Z_to_bv 64 0x96b50) fc None m1 (seg_rom asegs)
        /\ frm0 fc
        /\ lh_inv Σ Σ1 m m1 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t jp (atp_P (chars bs)) A (atp_elsA d (chars bs))) c
    /\ usp - 240 <= sp' <= usp - 224 /\ sp' mod 32 = 0 /\ 0 < f /\ f mod 64 = 0 /\ f + 256 <= rt_sp0 RT Σ - STACK_WIN
    /\ (f + 256 <= 0x10000 \/ SEGTOP_A <= f) /\ (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f)
    /\ SHB <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN.

Theorem lftoi_vec : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x646eb0 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_fuzz m)))
    (vec_postA Σ PMc (bv_unsigned sp) lo d bs ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF SM2 SPL EMP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST -> -> -> D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0.
  set (usp := bv_unsigned sp) in *. set (n := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N0 : 0 <= n < 2^64) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - D0 P1 P2 R1 SP0R N0. ul. }
  assert (VC0 : forall k, 0 <= vcost_pushes k 0 0).
  { assert (G : forall k c s, 0 <= c -> 0 <= s -> 0 <= vcost_pushes k c s).
    { induction k as [|k IH]; intros c0 s0' Hc0 Hs0; cbn [vcost_pushes]; [lia|].
      assert (0 <= vcost_push c0 s0').
      { unfold vcost_push. destruct (s0' <? c0); [lia|]. apply mcost_nonneg. unfold vcap_next. lia. }
      assert (0 <= (if s0' <? c0 then c0 else vcap_next c0 s0')) by (destruct (s0' <? c0); [lia| unfold vcap_next; lia]).
      specialize (IH (if s0' <? c0 then c0 else vcap_next c0 s0') (s0' + 1) H0 ltac:(lia)). lia. }
    intros k. apply G; lia. }

  destruct (fa_prologue usp lo d n ra gp (Z_to_bv 64 0x646eb0) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
              ST0 ltac:(ul) ltac:(ul) ltac:(ul) SPA CC0 MI0) as (sp' & SPR & SPA' & W0).
  rewrite <- ESP in W0.
  lazymatch type of W0 with evt asegs _ ?X =>
    assert (W0' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W0) end.
  clear W0.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W0') Hc). clear W0'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a1' & a2' & j0 & j1 & j2 & j3 & jo & jr & j10 & j11 & j12 & j13 & jn
                                             & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & STp1 & FRs1) & Hc1').
  clear Hc1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (LIB1 : LIB m1).
  { apply (LIB_agree' m m1 LIB0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. pose proof (proj2 (lib_fp_static x Hx)).
    cbn [outside]. split; [ul| exact I]. }
  assert (BS1 : bytes_at asegs m1 d bs).
  { apply (bytes_at_agree asegs m m1 _ _ BS). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbv beta in Hx. cbn [outside]. split; [| exact I].
    destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (R0 & R1 & R2). clear - Hx P1 P2 R1 SPR LOW LOR. subst n. ul. }
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).

  apply (SM2 Σ PMc (Z_to_bv 64 0x96a24) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 224)
           a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m1 lo FDO MST);
    try reflexivity; try assumption; [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - left; reflexivity.
  - rewrite FRS0. cbn. unfold FRAMES_MAX. lia.
  - unfold FUZZ_COST in *. pose proof (VC0 0%nat). lia.
  - unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia].
  - intros c2 ((Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU1 in ST2, PRES2.
    rewrite (ret_pc_even 0x96a24) in Hc2' by lia.
    change (fs_size 2) with 256 in *. change (256 / 8) with 32 in WRS.
    assert (INF1 : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
    pose proof (fframe_ranges RT AF Σ1 m2 f 2 ART2 INF1) as (_ & FR1' & _ & SHB0 & SHT).
    pose proof (af_fshadow_apart RT AF Σ1 m2 f 2 ART2 INF1) as (FSL & FSF).
    pose proof (FSF f 2%nat INF1) as FSELF.
    pose proof (af_frames_align RT AF Σ1 m2 f 2 ART2 INF1) as (_ & FSEG).
    change (fs_size 2) with 256 in *. rewrite SP1 in FR1', SHT.
    assert (SHF : shad (f + 256) = shad f + 32) by (unfold shad; Z.div_mod_to_equations; lia).
    rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, WRS.
    assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).

    assert (FRl2 : rw_cells asegs m2 sp' (fa_locals0 j0 j1 j2 j3 jo jr j10 j11 j12 j13 jn)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRl1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold fa_locals0. pres_tac. }
    assert (FRs2 : rw_cells asegs m2 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FRs1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold fa_saved. pres_tac. }
    assert (STp2 : stk asegs m2 (sp' + 120) (usp - 104)).
    { apply (stk_agree asegs m1 m2 _ _ STp1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. left. ul. }
    assert (LIB2 : LIB m2).
    { apply (LIB_agree' m1 m2 LIB1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. right; left. exact (proj1 (lib_fp_static x Hx)). }
    assert (BS2 : bytes_at asegs m2 d bs).
    { apply (bytes_at_agree asegs m1 m2 _ _ BS1). apply (agree_of_pres _ _ _ _ _ _ PRES2). intros x Hx. cbv beta in Hx.
      destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
      right; right; left. exists p, k. split; [exact Hin| lia]. }

    destruct (wr_at_rw_CB m2 f 32 (wr_at_sub m2 f 248 f 32 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
    change (Z.to_nat 32) with 32%nat in FH2.
    apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2.
    destruct (wr_at_rw_CB m2 (f + 32) 24 (wr_at_sub m2 f 248 (f + 32) 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jV & FV2).
    change (Z.to_nat 24) with 24%nat in FV2.
    destruct (wr_at_rw_CB m2 (f + 96) 80 (wr_at_sub m2 f 248 (f + 96) 80 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jP & FP2).
    change (Z.to_nat 80) with 80%nat in FP2.
    destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 32 WRS ltac:(lia)) as (jS & FS2).
    change (Z.to_nat 32) with 32%nat in FS2.
    apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 4]%nat) in FS2; [| reflexivity].
    cbn [mk_CB_cells app] in FS2.
    lazymatch type of FS2 with rw_cells _ _ _ [CB 1 ?l0; CB 1 ?l1; CB 1 ?l2; CB 1 ?l3; CB 1 ?l4; CB 1 ?l5; CB 1 ?l6; CB 1 ?l7; CB 1 ?l8; CB 1 ?l9;
                                               CB 1 ?l10; CB 1 ?l11; CB 1 ?l12; CB 1 ?l13; CB 1 ?l14; CB 1 ?l15; CB 1 ?l16; CB 1 ?l17; CB 1 ?l18; CB 1 ?l19;
                                               CB 1 ?l20; CB 1 ?l21; CB 1 ?l22; CB 1 ?l23; CB 1 ?l24; CB 1 ?l25; CB 1 ?l26; CB 1 ?l27; CB 4 ?t] =>
      change (rw_cells asegs m2 (f / 8 + 2147450880)
                (fa_shadow0 [l0; l1; l2; l3; l4; l5; l6; l7; l8; l9; l10; l11; l12; l13; l14; l15; l16; l17; l18; l19; l20; l21; l22; l23; l24; l25; l26; l27] t)) in FS2;
      set (tS := t) in FS2; clearbody tS
    end.

    lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2; CB 8 ?h3] =>
    lazymatch type of FS2 with rw_cells _ _ _ (fa_shadow0 ?LS _) =>
      pose proof (fa_walk1 usp sp' f lo d n gp (Z_to_bv 64 0x646eb0) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s7 s8 s9 s10 v3 v4 v5 v6
                    j0 j1 j2 j3 jo jr j10 j11 j12 j13 jn h0 h1 h2 h3 tS LS F2 fc2 m2 eq_refl FPOS ltac:(ul) ltac:(ul) FD0
                    ltac:(lia) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) DR N0 FRl2 FH2 FS2 MI2) as W1;
      set (H3 := h3) in *
    end end.
    clearbody H3.
    lazymatch type of W1 with evt asegs _ ?X =>
      assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
    clear W1.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W1') Hc2'). clear W1'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a2x & a3x & a4x & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FS3) & Hc3').
    clear Hc3. unfold fa_W1 in MU3.
    set (S := f / 8 + 2147450880) in *.
    assert (SHS : shad f = S) by reflexivity.
    assert (ART3 : ART RT Σ1 m3).
    { apply (art_client_write RT AF Σ1 m2 m3 sp' ART2 ltac:(rewrite SP1; ul)); [| exact WM3].
      intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
      - left. ul.
      - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
      - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INF1| lia]. }
    assert (AG23 : agree_on (fun x => ~ (sp' <= x < sp' + 120) /\ ~ (f <= x < f + 24) /\ ~ (S <= x < S + 28)) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x (H1 & H2 & H3'). cbn [outside]. repeat split; assumption. }
    assert (ST3 : stk asegs m3 lo sp').
    { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
    assert (STp3 : stk asegs m3 (sp' + 120) (usp - 104)).
    { apply (stk_agree asegs m2 m3 _ _ STp2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
    assert (FRs3 : rw_cells asegs m3 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree asegs m2 m3 _ _ FRs2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. unfold fa_saved in Hx.
      cbn [cells_size csize Nat.add] in Hx. cbv beta in *. ul. }
    assert (LIB3 : LIB m3).
    { apply (LIB_agree' m2 m3 LIB2). eapply agree_sub; [exact AG23|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)). cbv beta. ul. }
    pose proof (af_frames_range RT AF Σ1 m2 f 2%nat ART2 INF1) as (_ & _ & _ & FLV). change (fs_size 2) with 256 in FLV.
    assert (BS3 : bytes_at asegs m3 d bs).
    { apply (bytes_at_agree asegs m2 m3 _ _ BS2). eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in Hx.
      destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
      rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as X1. pose proof (FSL p k Hin) as X2. pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hin) as (R0 & R1 & R2).
      rewrite ?SHF, ?SHS in X2. cbv beta. clear - Hx P1 P2 X1 X2 R1 SPR SP1 LOW LOR N0. subst n. ul. }
    assert (FV3 : rw_cells asegs m3 (f + 32) [CB 24 jV]).
    { apply (rw_cells_agree asegs m2 m3 _ _ FV2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
    assert (FP3 : rw_cells asegs m3 (f + 96) [CB 80 jP]).
    { apply (rw_cells_agree asegs m2 m3 _ _ FP2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }

    assert (FOBJV : fobj RT Σ1 m3 (f + 32) 24).
    { split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
      split; [exists f, 2%nat; change (fs_size 2) with 256; split; [exact INF1| lia]|].
      replace (shad (f + 32)) with (S + 4) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
      pose proof FS3 as X. unfold fa_shadow1 in X. cbn [map app repeat] in X.
      lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
        change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in X end.
      apply Zvw.rw_cells_app in X. destruct X as [_ X]. apply Zvw.rw_cells_app in X. destruct X as [X _].
      cbn [cells_size csize Nat.add] in X. destruct X as [[_ HB] _]. exact HB. }

    pose proof FRl3 as FD3. unfold fa_locals1 in FD3.
    lazymatch type of FD3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7] ++ rest) in FD3 end.
    apply Zvw.rw_cells_app in FD3. destruct FD3 as [_ FD3]. apply Zvw.rw_cells_app in FD3. destruct FD3 as [FD3 _].
    cbn [cells_size csize Nat.add] in FD3. replace (sp' + Z.of_nat 80) with (sp' + 80) in FD3 by lia.
    assert (En : zlength (chars bs) = n) by (subst n; apply chars_length). rewrite <- En in FD3.
    assert (BSc : bytes_at asegs m3 d (to_bytes (chars bs))) by (rewrite to_bytes_chars; exact BS3).
    assert (LENc : zlength (chars bs) < 2^26) by (rewrite chars_length; exact BSL).
    assert (INLVc : (exists p k, In (p, k) (rt_live RT Σ1) /\ p <= d /\ d + zlength (chars bs) <= p + k) \/ (chars bs = [] /\ d < SEGTOP_A)).
    { rewrite chars_length, LV1. fold n. destruct INLV as [L|(E & DL)]; [left; exact L| right]. split; [| exact DL]. rewrite E. reflexivity. }
    assert (ST3' : stk asegs m3 lo (bv_unsigned (Z_to_bv 64 sp'))) by (rewrite EU1; exact ST3).
    assert (SPFD : bv_unsigned (Z_to_bv 64 sp') <= sp' + 80) by (rewrite EU1; lia).
    assert (FDT : sp' + 80 + 24 <= USTACK_TOP) by ul.
    assert (FD8 : (sp' + 80) mod 8 = 0) by (clear - SPA'; Z.div_mod_to_equations; lia).
    assert (LVB1 : Z.of_nat (length (rt_live RT Σ1)) + 4 <= LIVE_MAX) by (rewrite LV1; unfold FUZZ_LIVE in LVB; lia).
    assert (LVPOS1 : forall p k, In (p, k) (rt_live RT Σ1) -> 0 < k) by (rewrite LV1; exact LVPOS).
    pose proof (vcb_ok (chars bs) LENc) as VCB0.
    assert (PLE : (length (poffs (chars bs)) <= atp_P (chars bs))%nat) by (unfold atp_P; rewrite poffs_length; lia).
    assert (VCM : vcost_pushes (length (poffs (chars bs))) 0 0 <= vcost_pushes (atp_P (chars bs)) 0 0).
    { assert (G : forall a b, vcost_pushes a 0 0 <= vcost_pushes (a + b) 0 0).
      { intros a b. induction b as [|b IH]; [rewrite Nat.add_0_r; lia|].
        rewrite Nat.add_succ_r, vcost_pushes_snoc.
        pose proof (vcap_iter_inv (a + b) 0 0 ltac:(lia) ltac:(lia)) as VI.
        pose proof (vcost_push_nonneg (vcap_iter (a + b) 0 0) (0 + Z.of_nat (a + b)) ltac:(lia)). lia. }
      replace (atp_P (chars bs)) with (length (poffs (chars bs)) + (atp_P (chars bs) - length (poffs (chars bs))))%nat by lia. apply G. }
    assert (CRB1 : 1 + vcost_pushes (length (poffs (chars bs))) 0 0 <= rt_credit RT Σ1) by (rewrite CR1; unfold FUZZ_COST in CR0; lia).
    assert (FRB1 : (length (rt_frames RT Σ1) + 1 < FRAMES_MAX2)%nat) by (rewrite FRS1, FRS0; cbn; unfold FRAMES_MAX2; lia).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (LOR1 : lo + ATPA_SPLITINTO_STACK <= bv_unsigned (Z_to_bv 64 sp')) by (rewrite EU1; ul).
    assert (SPT1 : bv_unsigned (Z_to_bv 64 sp') + 16 <= USTACK_TOP) by (rewrite EU1; ul).
    assert (SPA1 : bv_unsigned (Z_to_bv 64 sp') mod 16 = 0) by (rewrite EU1; clear - SPA'; Z.div_mod_to_equations; lia).

    apply (SPL Σ1 PMc (Z_to_bv 64 0x96b30) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) v0 v1 v2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (sp' + 80)) a2x a3x a4x e5 e6 e7
             (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8
             (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) v3 v4 v5 v6 F2 fc2 m3 (f + 32) (sp' + 80) d (chars bs) jV lo
             FDO MST eq_refl eq_refl eq_refl BSc (chars_range bs) LENc D0 INLVc LVPOS1 FOBJV FV3 SPFD FDT FD8 FD3 LVB1 CRB1 FRB1 ART3 MI3 ST3' LOW1 LOR1 SPT1 SPA1 FRM2);
      [split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    intros c4 ((Σ2 & A & Hc4 & VL2 & FRS2 & SP2 & CR2) & FC4).
    destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (rv4 & m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & VR4 & FD4) & FRM4 & Hc4'). clear Hc4.
    destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
    cbn [ms_fcsr] in FRM4. rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even 0x96b30) in Hc4' by lia.
    set (P0 := length (poffs (chars bs))) in *.

    assert (ACL : forall x, (sp' <= x < sp' + 80) \/ (sp' + 96 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 176) \/ (S <= x < S + 32) ->
                    aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x /\ outside [(f + 32, f + 32 + 24); (sp' + 80, sp' + 80 + 16)] x).
    { intros x Hx. assert (OUT : outside [(f + 32, f + 32 + 24); (sp' + 80, sp' + 80 + 16)] x).
      { cbn [outside]. destruct Hx as [H|[H|[H|[H|H]]]]; (split; [| split; [| exact I]]); clear - H FR1' SPR LOW LOR SHT SHB0 FSELF FPOS; ul. }
      split; [| exact OUT]. destruct Hx as [H|[H|[H|[H|H]]]].
      - left. ul. - left. ul.
      - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
      - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
      - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INF1| lia]. }
    assert (AG34 : agree_on (fun x => (sp' <= x < sp' + 80) \/ (sp' + 96 <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 176) \/ (S <= x < S + 32)) m3 m4).
    { intros a Ha. destruct (ACL _ Ha) as [H1 H2]. exact (PRES4 a H1 H2). }
    pose proof (af_frames_range RT AF Σ1 m2 f 2%nat ART2 INF1) as (_ & _ & FSEG2 & _). change (fs_size 2) with 256 in FSEG2.

    assert (EP0 : zlength (poffs (chars bs)) = Z.of_nat P0) by reflexivity.
    assert (INV4 : lh_inv Σ Σ2 m m4 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H3 tS jP P0 A (map (pview d) (poffs (chars bs)))).
    { unfold lh_inv. split; [exact ART4|]. split; [exact MI4|]. split; [exact ST4|].
      split. { exists j0, j1, j2, jo, jr, j13, jn. unfold fa_locals2.
               pose proof FRl3 as X. unfold fa_locals1 in X.
               lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
                 change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7] ++ rest) in X end.
               apply Zvw.rw_cells_app in X. destruct X as [X1 X]. apply Zvw.rw_cells_app in X. destruct X as [_ X3].
               cbn [cells_size csize Nat.add] in X1, X3. replace (sp' + Z.of_nat 80 + Z.of_nat 16) with (sp' + 96) in X3 by lia.
               lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
                 change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest) with ([c0; c1; c2; c3; c4; c5] ++ [c6; c7] ++ rest) end.
               apply Zvw.rw_cells_app. split.
               { apply (rw_cells_agree_nw asegs m3 m4 _ _ X1). eapply agree_sub; [exact AG34|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
               apply Zvw.rw_cells_app. split.
               { cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 80) with (sp' + 80) by lia. rewrite chars_length in FD4. fold n in FD4. subst n. exact FD4. }
               cbn [cells_size csize Nat.add]. replace (sp' + Z.of_nat 80 + Z.of_nat 16) with (sp' + 96) by lia.
               apply (rw_cells_agree_nw asegs m3 m4 _ _ X3). eapply agree_sub; [exact AG34|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      split. { apply (stk_agree_nw asegs m3 m4 _ _ STp3). eapply agree_sub; [exact AG34|]. intros x Hx. cbv beta in *. ul. }
      split. { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRs3). eapply agree_sub; [exact AG34|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      split. { apply (rw_cells_agree_nw asegs m3 m4 _ _ FH3). eapply agree_sub; [exact AG34|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { apply (rw_cells_agree_nw asegs m3 m4 _ _ FS3). eapply agree_sub; [exact AG34|]. intros x Hx. unfold fa_shadow1 in Hx.
               cbn [map app repeat cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { apply (rw_cells_agree_nw asegs m3 m4 _ _ FP3). eapply agree_sub; [exact AG34|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { rewrite <- EP0. exact VR4. }
      split. { apply (bytes_at_agree asegs m3 m4 _ _ BS3). intros a Ha. cbv beta in Ha.
               destruct INLV as [(p & k & Hin & P1 & P2)| (E & DL)]; [| subst n; rewrite E in Ha; cbn [length] in Ha; lia].
               apply PRES4.
               - right; right; left. exists p, k. split; [rewrite LV1; exact Hin| subst n; lia].
               - rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as X1. pose proof (af_live_range RT AF Σ1 m2 p k ART2 Hin) as (_ & R1 & _). cbn [outside].
                 split; [clear - Ha P1 P2 X1; lia|]. split; [| exact I]. rewrite SP1 in R1. clear - Ha P2 R1 LOW LOR SPR. subst n usp. unfold FUZZ_STACK, STACK_WIN in *. lia. }
      split. { apply (LIB_agree' m3 m4 LIB3). intros a Ha. destruct (lib_fp_static _ Ha) as [CS R]. apply PRES4; [right; left; exact CS|].
               cbn [outside]. clear - R FSEG2 SPR LOW LOR SP0R. unfold SEGTOP_A in *. split; [lia|]. split; [ul| exact I]. }
      split. { intros a Ha Hout. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL0.
               assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' (bv_unsigned a)).
               { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; exact He| intros e He; rewrite FRS0 in He; destruct He| lia]. }
               assert (NF : ~ (f <= bv_unsigned a < f + 256) /\ ~ (S <= bv_unsigned a < S + 32)).
               { destruct Ha as [H|[H|[H|[H|H]]]].
                 - clear - H FR1' SHT SP0R LOW LOR SPR. split; ul.
                 - pose proof (client_static_range _ H) as R. clear - R FSEG2 SHB0. unfold SEGTOP_A, SHB in *. split; lia.
                 - destruct H as (p & k & Hin & Hr). rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as X1. pose proof (FSL p k Hin) as X2. rewrite ?SHF, ?SHS in X2.
                   clear - Hr X1 X2. split; lia.
                 - destruct H as (f0 & k0 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
                 - destruct H as (f0 & k0 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
               destruct NF as [NF1 NF2].
               rewrite (PRES4 a Ha1), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
               - cbn [outside]. split; [clear - SPL0 SPR LOW LOR; ul| exact I].
               - apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; rewrite FRS0 in He; destruct He| lia].
               - cbn [outside]. split; [clear - SPL0 SPR LOW LOR; ul|]. split; [clear - NF1; lia|]. split; [clear - NF2; lia| exact I].
               - cbn [outside]. split; [clear - NF1; lia|]. split; [clear - SPL0 SPR LOW LOR; ul| exact I]. }
      split; [rewrite <- EP0, <- LV1; exact VL2|]. split; [rewrite FRS2, FRS1, FRS0; reflexivity|]. split; [rewrite SP2; exact SP1|].
      rewrite CR1 in CR2. clear - CR2 VCM VCB0 CR0. lia. }

    assert (FIN : forall (Σx : rts RT) (mx : mem) (cx : config) (pc : Z) (rax q0 q1 q2 q3 q4 q5 q6 q7 u0 u1 u2 u3 u4 u5 u6 s5y s6y : word)
                     Fx fcx (h3x tx jpx : list byte) (szN : nat) (Ax : Z) (els : list (Z * Z)),
              lh_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3x tx jpx szN Ax els ->
              (2 <= szN)%nat -> szN = atp_P (chars bs) -> els = atp_elsA d (chars bs) -> frm0 fcx ->
              (pc = 0x96b30 \/ (pc = 0x96b4c /\ s5y = Z_to_bv 64 16)) ->
              ASTA RT Σx PMc (eq (eh_regs pc rax sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp q0 q1 q2 q3 q4 q5 q6 q7 f s5y s6y s7 s8 u3 u4 u5 u6 Fx fcx mx)) cx ->
              realizes asegs cx T).
    { intros Σx mx cx pc rax q0 q1 q2 q3 q4 q5 q6 q7 u0 u1 u2 u3 u4 u5 u6 s5y s6y Fx fcx h3x tx jpx szN Ax els INV SZ2 ESZ EELS FRMx PC Hcx.
      pose proof INV as (ARTx & MIx & STx & _ & _ & _ & _ & _ & _ & VRx & _).
      pose proof VRx as (ELS & SZC & CAPB & A0 & AH & SVx & _).
      pose proof (eh_exit pc rax sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp q0 q1 q2 q3 q4 q5 q6 q7 f Ax (vcap_iter szN 0 0) (Z.of_nat szN)
                    s5y s6y s7 s8 u3 u4 u5 u6 Fx fcx mx PC FPOS ltac:(clear - FR1' SP0R; ul) A0 AH ltac:(lia) SVx MIx) as WX.
      lazymatch type of WX with evt asegs _ ?X =>
        assert (WX' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WX) end.
      clear WX.
      apply (cps_realizes asegs _ _ _ cx (asta_evt_c RT AF Σx PMc _ _ MST WX') Hcx). clear WX'. intros cy Hcy.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σx PMc _ cy Hcy); intros ms0 <-; exact FRMx].
      unfold vec_postA. exists Σx, sp', f, Ax. split.
      - eapply ASTA_conseq; [exact Hcy|]. intros ms <-. unfold eh_regs.
        exists mx, rax, u0, u1, u2, (Z_to_bv 64 (16 * Z.of_nat szN)), q1, q2, q3, q4, q5, q6, q7, u3, u4, u5, u6, Fx, fcx, h3x, tx, jpx.
        split; [subst S; reflexivity|]. split; [exact FRMx|]. rewrite <- ESZ, <- EELS. exact INV.
      - split; [exact SPR|]. split; [exact SPA'|]. split; [exact FPOS|]. split; [exact F64|]. split; [exact FR1'|]. split; [exact FSEG2|].
        split; [subst S; exact FSELF|]. subst S. split; [exact SHB0| exact SHT]. }

    assert (VMONO : forall a b, vcost_pushes a 0 0 <= vcost_pushes (a + b) 0 0).
    { intros a b. induction b as [|b IH]; [rewrite Nat.add_0_r; lia|].
      rewrite Nat.add_succ_r, vcost_pushes_snoc.
      pose proof (vcap_iter_inv (a + b) 0 0 ltac:(lia) ltac:(lia)) as VI.
      pose proof (vcost_push_nonneg (vcap_iter (a + b) 0 0) (0 + Z.of_nat (a + b)) ltac:(lia)). lia. }
    assert (P2 : (2 <= atp_P (chars bs))%nat) by (unfold atp_P; lia).
    assert (ROUND : forall (Σx : rts RT) (mx : mem) (cx : config) (pc : Z) (rax q0 q1 q2 q3 q4 q5 q6 q7 u0 u1 u2 u3 u4 u5 u6 s5y s6y : word)
                     Fx fcx (h3x tx jpx : list byte) (szN : nat) (Ax : Z) (els : list (Z * Z)),
              lh_inv Σ Σx m mx usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3x tx jpx szN Ax els ->
              (szN < 2)%nat -> frm0 fcx -> (pc = 0x96b30 \/ (pc = 0x96b4c /\ s5y = Z_to_bv 64 16)) ->
              ASTA RT Σx PMc (eq (eh_regs pc rax sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp q0 q1 q2 q3 q4 q5 q6 q7 f s5y s6y s7 s8 u3 u4 u5 u6 Fx fcx mx)) cx ->
              (forall (Σy : rts RT) (my : mem) (cy : config) (r0 r1 r2 r3 r4 r5 r6 r7 v0' v1' v2' v3' v4' v5' v6' : word) Fy fcy (Ay : Z),
                  lh_inv Σ Σy m my usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3x tx jpx (Datatypes.S szN) Ay (els ++ [(0, 0)]) -> frm0 fcy ->
                  ASTA RT Σy PMc (eq (eh_regs 0x96b4c (Z_to_bv 64 0x96b4c) sp' gp (Z_to_bv 64 0x646eb0) v0' v1' v2' usp r0 r1 r2 r3 r4 r5 r6 r7 f
                                         (Z_to_bv 64 16) (Z_to_bv 64 Ax) s7 s8 v3' v4' v5' v6' Fy fcy my)) cy ->
                  realizes asegs cy T) ->
              realizes asegs cx T).
    { intros Σx mx cx pc rax q0 q1 q2 q3 q4 q5 q6 q7 u0 u1 u2 u3 u4 u5 u6 s5y s6y Fx fcx h3x tx jpx szN Ax els INV SZ2 FRMx PC Hcx K.
      pose proof INV as (ARTx & MIx & STx & (k0 & k1 & k2 & ko & kr & k13 & kn & FRlx) & STpx & FRsx & FHx & FSx & FPx & VRx & BSx & LIBx & PRESx & VLx & FRSx & SPx & CRx).
      pose proof VRx as (ELS & SZC & CAPB & A0 & AH & SVx & _).
      pose proof (eh_call pc rax sp' gp (Z_to_bv 64 0x646eb0) u0 u1 u2 usp q0 q1 q2 q3 q4 q5 q6 q7 f Ax (vcap_iter szN 0 0) (Z.of_nat szN)
                    s5y s6y s7 s8 u3 u4 u5 u6 Fx fcx mx PC FPOS ltac:(clear - FR1' SP0R; ul) A0 AH ltac:(lia) ltac:(lia) SVx MIx) as WX.
      lazymatch type of WX with evt asegs _ ?X =>
        assert (WX' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WX) end.
      clear WX.
      apply (cps_realizes asegs _ _ _ cx (asta_evt_c RT AF Σx PMc _ _ MST WX') Hcx). clear WX'. intros cz Hcz.
      assert (INFx : In (f, 2%nat) (rt_frames RT Σx)) by (rewrite FRSx; left; reflexivity).
      assert (FOBJx : fobj RT Σx mx (f + 32) 24).
      { split; [Z.div_mod_to_equations; lia|]. split; [lia|]. change ((24 + 7) / 8) with 3.
        split; [exists f, 2%nat; change (fs_size 2) with 256; split; [exact INFx| lia]|].
        replace (shad (f + 32)) with (S + 4) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
        pose proof FSx as X. unfold fa_shadow1 in X. cbn [map app repeat] in X.
        lazymatch type of X with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?d0 :: ?d1 :: ?d2 :: ?rest) =>
          change (c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: rest) with ([c0; c1; c2; c3] ++ [d0; d1; d2] ++ rest) in X end.
        apply Zvw.rw_cells_app in X. destruct X as [_ X]. apply Zvw.rw_cells_app in X. destruct X as [X _].
        cbn [cells_size csize Nat.add] in X. subst S. destruct X as [[_ HB] _]. exact HB. }
      assert (LVBx : Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX) by (unfold FUZZ_LIVE in LVB; lia).
      assert (CRBx : vcost_push (vcap_iter szN 0 0) (Z.of_nat szN) <= rt_credit RT Σx).
      { pose proof (VMONO (Datatypes.S szN) (atp_P (chars bs) - Datatypes.S szN)%nat) as M1. replace (Datatypes.S szN + (atp_P (chars bs) - Datatypes.S szN))%nat with (atp_P (chars bs)) in M1 by lia.
        rewrite vcost_pushes_snoc, Z.add_0_l in M1. clear - M1 CRx VCB0 CR0. unfold FUZZ_COST in CR0. lia. }
      assert (STx' : stk asegs mx lo (bv_unsigned (Z_to_bv 64 sp'))) by (rewrite EU1; exact STx).
      assert (LOWx : rt_sp0 RT Σx - STACK_WIN <= lo) by (rewrite SPx; exact LOW).
      assert (LORx : lo + ATPA_PUSH_STACK <= bv_unsigned (Z_to_bv 64 sp')) by (rewrite EU1; ul).
      apply (EMP Σx PMc (Z_to_bv 64 0x96b4c) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x646eb0) u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
               (Z_to_bv 64 (f + 32)) q1 q2 q3 q4 q5 q6 q7
               (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 16) (Z_to_bv 64 Ax) s7 s8
               (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) u3 u4 u5 u6 Fx fcx mx (f + 32) Ax (vcap_iter szN 0 0) (Z.of_nat szN) els (rt_live RT Σ) lo
               FDO MST eq_refl eq_refl VRx VLx LVPOS ltac:(lia) FOBJx LVBx CRBx ARTx MIx STx' LOWx LORx SPT1 SPA1 FRMx);
        [split; [subst S; exact Hcz| apply (cfrm0_of_asta RT Σx PMc (eq _) cz Hcz); intros ms0 <-; exact FRMx] |].
      intros cw ((Σy & Ay & Hcw & VLy & FRSy & SPy & CRy) & FCw).
      destruct (ASTA_unpack_f RT Σy _ _ cw Hcw FCw) as (msw & (rvw & my & RSw & (ARTy & MIy & STy) & PRESy & VRy) & FRMy & Hcw'). clear Hcw.
      destruct RSw as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fy & fcy & ->).
      cbn [ms_fcsr] in FRMy. rewrite EU1 in STy, PRESy. rewrite (ret_pc_even 0x96b4c) in Hcw' by lia.

      assert (ACLx : forall x, (sp' <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 176) \/ (S <= x < S + 32) ->
                      aclient (rt_live RT Σ) (rt_frames RT Σx) sp' x /\ outside [(f + 32, f + 32 + 24)] x).
      { intros x Hx. split.
        - destruct Hx as [H|[H|[H|H]]].
          + left. ul.
          + right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INFx| lia].
          + right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INFx| lia].
          + right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INFx| lia].
        - cbn [outside]. split; [| exact I]. destruct Hx as [H|[H|[H|H]]]; clear - H FR1' SPR LOW LOR SHT SHB0 FSELF FPOS; ul. }
      assert (AGxy : agree_on (fun x => (sp' <= x < usp) \/ (f <= x < f + 32) \/ (f + 96 <= x < f + 176) \/ (S <= x < S + 32)) mx my).
      { intros a Ha. destruct (ACLx _ Ha) as [H1 H2]. exact (PRESy a H1 H2). }
      apply (K Σy my cw rvw z1 z2 z3 z4 z5 z6 z7 y0 y1 y2 y3 y4 y5 y6 Fy fcy Ay); [| exact FRMy| subst S; exact Hcw'].
      unfold lh_inv. split; [exact ARTy|]. split; [exact MIy|]. split; [exact STy|].
      split. { exists k0, k1, k2, ko, kr, k13, kn. apply (rw_cells_agree_nw asegs mx my _ _ FRlx). eapply agree_sub; [exact AGxy|].
               intros x Hx. unfold fa_locals2 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      split. { apply (stk_agree_nw asegs mx my _ _ STpx). eapply agree_sub; [exact AGxy|]. intros x Hx. cbv beta in *. ul. }
      split. { apply (rw_cells_agree_nw asegs mx my _ _ FRsx). eapply agree_sub; [exact AGxy|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
      split. { apply (rw_cells_agree_nw asegs mx my _ _ FHx). eapply agree_sub; [exact AGxy|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { apply (rw_cells_agree_nw asegs mx my _ _ FSx). eapply agree_sub; [exact AGxy|]. intros x Hx. unfold fa_shadow1 in Hx.
               cbn [map app repeat cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { apply (rw_cells_agree_nw asegs mx my _ _ FPx). eapply agree_sub; [exact AGxy|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia. }
      split. { rewrite vcap_iter_S, Z.add_0_l. replace (Z.of_nat (Datatypes.S szN)) with (Z.of_nat szN + 1) by lia. exact VRy. }
      split. { apply (bytes_at_agree asegs mx my _ _ BSx). intros a Ha. cbv beta in Ha.
               destruct INLV as [(p & k & Hin & Q1 & Q2)| (E & DL)]; [| subst n; rewrite E in Ha; cbn [length] in Ha; lia].
               apply PRESy.
               - right; right; left. exists p, k. split; [exact Hin| subst n; lia].
               - rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as X1. cbn [outside]. split; [clear - Ha Q1 Q2 X1; lia| exact I]. }
      split. { apply (LIB_agree' mx my LIBx). intros a Ha. destruct (lib_fp_static _ Ha) as [CS R]. apply PRESy; [right; left; exact CS|].
               cbn [outside]. clear - R FSEG2. unfold SEGTOP_A in *. split; [lia| exact I]. }
      split. { intros a Ha Hout. rewrite <- (PRESx a Ha Hout). apply PRESy.
               - apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros e He; rewrite FRS0 in He; destruct He| lia].
               - cbn [outside]. split; [| exact I]. destruct Ha as [H|[H|[H|[H|H]]]].
                 + clear - H FR1' SP0R LOW LOR SPR. ul.
                 + pose proof (client_static_range _ H) as R. clear - R FSEG2. unfold SEGTOP_A in *. lia.
                 + destruct H as (p & k & Hin & Hr). rewrite <- LV1 in Hin. pose proof (FLV p k Hin) as X1. clear - Hr X1. lia.
                 + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
                 + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
      split. { rewrite vcap_iter_S, Z.add_0_l. replace (Z.of_nat (Datatypes.S szN)) with (Z.of_nat szN + 1) by lia. exact VLy. }
      split; [rewrite FRSy; exact FRSx|]. split; [rewrite SPy; exact SPx|].
      rewrite vcost_pushes_snoc, Z.add_0_l. clear - CRx CRy. lia. }

    assert (PL : length (poffs (chars bs)) = length (atp_parts (chars bs))) by apply poffs_length.
    destruct (le_lt_dec 2 P0) as [GE|LT].
    + apply (FIN Σ2 m4 c4 0x96b30 (Z_to_bv 64 0x96b30) rv4 g1 g2 g3 g4 g5 g6 g7 w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 n) (Z_to_bv 64 d) F4 fc4 H3 tS jP
               P0 A (map (pview d) (poffs (chars bs))) INV4 GE); [| | exact FRM4| left; reflexivity| subst S; exact Hc4'].
      * subst P0. unfold atp_P. rewrite <- PL. lia.
      * subst P0. unfold atp_elsA, atp_P. rewrite <- PL. replace (Nat.max (length (poffs (chars bs))) 2 - length (poffs (chars bs)))%nat with 0%nat by lia.
        cbn [repeat]. rewrite app_nil_r. reflexivity.
    + apply (ROUND Σ2 m4 c4 0x96b30 (Z_to_bv 64 0x96b30) rv4 g1 g2 g3 g4 g5 g6 g7 w0 w1 w2 w3 w4 w5 w6 (Z_to_bv 64 n) (Z_to_bv 64 d) F4 fc4 H3 tS jP
               P0 A (map (pview d) (poffs (chars bs))) INV4 LT FRM4 ltac:(left; reflexivity) ltac:(subst S; exact Hc4')).
      intros Σy my cy r0 r1 r2 r3 r4 r5 r6 r7 x0 x1' x2 x3 x4 x5 x6 Fy fcy Ay INVy FRMy Hcy.
      destruct (le_lt_dec 2 (Datatypes.S P0)) as [GE1|LT1].
      * apply (FIN Σy my cy 0x96b4c (Z_to_bv 64 0x96b4c) r0 r1 r2 r3 r4 r5 r6 r7 x0 x1' x2 x3 x4 x5 x6 (Z_to_bv 64 16) (Z_to_bv 64 A) Fy fcy H3 tS jP
                 (Datatypes.S P0) Ay (map (pview d) (poffs (chars bs)) ++ [(0, 0)]) INVy GE1); [| | exact FRMy| right; split; reflexivity| exact Hcy].
        -- subst P0. unfold atp_P. rewrite <- PL. lia.
        -- subst P0. unfold atp_elsA, atp_P. rewrite <- PL. replace (Nat.max (length (poffs (chars bs))) 2 - length (poffs (chars bs)))%nat with 1%nat by lia.
          reflexivity.
      * apply (ROUND Σy my cy 0x96b4c (Z_to_bv 64 0x96b4c) r0 r1 r2 r3 r4 r5 r6 r7 x0 x1' x2 x3 x4 x5 x6 (Z_to_bv 64 16) (Z_to_bv 64 A) Fy fcy H3 tS jP
                 (Datatypes.S P0) Ay (map (pview d) (poffs (chars bs)) ++ [(0, 0)]) INVy LT1 FRMy ltac:(right; split; reflexivity) Hcy).
        intros Σz mz cz r0' r1' r2' r3' r4' r5' r6' r7' x0' x1'' x2' x3' x4' x5' x6' Fz fcz Az INVz FRMz Hcz.
        apply (FIN Σz mz cz 0x96b4c (Z_to_bv 64 0x96b4c) r0' r1' r2' r3' r4' r5' r6' r7' x0' x1'' x2' x3' x4' x5' x6' (Z_to_bv 64 16) (Z_to_bv 64 Ay) Fz fcz H3 tS jP
                 (Datatypes.S (Datatypes.S P0)) Az ((map (pview d) (poffs (chars bs)) ++ [(0, 0)]) ++ [(0, 0)]) INVz ltac:(lia));
          [| | exact FRMz| right; split; reflexivity| exact Hcz].
        -- subst P0. unfold atp_P. rewrite <- PL. lia.
        -- subst P0. unfold atp_elsA, atp_P. rewrite <- PL. destruct (poffs (chars bs)) as [|e l] eqn:EPF; [reflexivity|]. cbn [length] in LT1. lia.
Qed.
End Top1.
