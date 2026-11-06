(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3 Sj_new Zpo Zwn Z4a Z73 Z6m Z6y Z6p Z4e Z4l Z4m Z4n Z52 Z57.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Top2a.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.

Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem lftoi_par1 : forall (Σ Σ1 : rts RT) PMc (m m1 : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) F fc (h3 t jp : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  0 < d -> Z.of_nat (length bs) < 2^26 ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lh_inv RT LIB Σ Σ1 m m1 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t jp (atp_P (chars bs)) A (atp_elsA d (chars bs)) ->
  usp - 304 <= sp' <= usp - 288 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN -> frm0 fc ->
  cps_f (ASTA RT Σ1 PMc (eq (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
                                     s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 17) (Z_to_bv 64 A) (Z_to_bv 64 (-16)) (Z_to_bv 64 16)
                                     (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
                                F (Z_to_bv 64 0x96c90) fc None m1 (seg_rom bsegs))))
    (par_postA RT LIB Σ PMc usp lo d bs ra gp (Z_to_bv 64 0x653c30) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF MSET.
  intros Σ Σ1 PMc m m1 usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x t3 t4 t5 t6 F fc h3 t jp
    FDO MST D0 BSL INLV FRS0 LOW LOR SPT SPA INV SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM.
  intros T c (Hc & FC0) Hk.
  destruct INV as (ART1 & MI1 & ST1 & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & FRl1) & STp1 & FRs1 & FH1 & FS1 & FP1 & VR1 & BS1 & LIB1 & PRES1 & VL1 & FRS1 & SP1 & CR1).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SP0R. rewrite SP1 in SP0R.
  set (n := Z.of_nat (length bs)) in *. set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *.
  assert (INF1 : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (SHF : shad (f + 256) = S + 32) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (SHS : shad f = S) by reflexivity.
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  pose proof (af_frames_range RT AF Σ1 m1 f 2%nat ART1 INF1) as (_ & _ & _ & FLV). change (fs_size 2) with 256 in FLV.
  pose proof (af_fshadow_apart RT AF Σ1 m1 f 2 ART1 INF1) as (FSL & _). change (fs_size 2) with 256 in FSL. rewrite SHF, SHS in FSL.
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI.
  assert (INCL1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)).
  { intros e He. unfold vliveA in VL1. rewrite VL1. apply in_or_app. right. exact He. }
  assert (INA : In (A, 16 * Z.of_nat P) (rt_live RT Σ1)).
  { unfold vliveA, vblockA in VL1. rewrite VL1. apply in_or_app. left. destruct (Z.eqb_spec (vcap_iter P 0 0) 0); [lia|]. apply ann_block_vis. }
  pose proof (FLV A _ INA) as AFL. pose proof (FSL A _ INA) as ASL. pose proof (af_live_range RT AF Σ1 m1 A _ ART1 INA) as (AR0 & AR1 & AR2). rewrite SP1 in AR1.

  assert (CLI : forall mx, ART RT Σ1 mx -> forall x, lp_dom RT Σ usp sp' f A d bs x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros mx ARTx. exact (lp_client RT AF Σ Σ1 mx usp sp' f lo d A bs ARTx FRS1 FRS0 INCL1 INA INLV FPOS F64 ltac:(lia) SPT). }
  assert (APF : forall mx lo' hi', ART RT Σ1 mx -> f + 56 <= lo' -> hi' <= f + 256 -> forall x, lp_dom RT Σ usp sp' f A d bs x -> ~ (lo' <= x < hi')).
  { intros mx lo' hi' ARTx HLO HHI. exact (lp_apart_frame RT AF Σ Σ1 mx usp sp' f lo d A lo' hi' bs ARTx FRS1 FRS0 SP1 INCL1 INA INLV LOW LOR ltac:(lia) FSELF HLO HHI). }

  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [1; 7; 8; 1; 3; 4; 24; 8; 1; 7; 16]%nat) in FP1; [| reflexivity]. cbn [mk_CB_cells app] in FP1.

  lazymatch type of FP1 with rw_cells _ _ _ [CB 1 ?p0; CB 7 ?p1; CB 8 ?p8; CB 1 ?p16; CB 3 ?p17; CB 4 ?p20; CB 24 ?p24; CB 8 ?p48; CB 1 ?p56; CB 7 ?p57; CB 16 ?p64] =>
    pose proof (fa_walk3 usp sp' f x1 gp (Z_to_bv 64 0x653c30) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 17) (Z_to_bv 64 A) (Z_to_bv 64 (-16)) (Z_to_bv 64 16) t3 t4 t5 t6 t p1 p8 p16 p17 p20 p24 p48 p56 p57 p64 p0 F fc m1
                  FPOS ltac:(ul) ltac:(apply Z.div_pos; lia) ltac:(subst S; ul) ltac:(subst S; exact FSELF) FS1 FP1 MI1) as W3;
    set (P1 := p1) in *; set (P17 := p17) in *; set (P24 := p24) in *; set (P48 := p48) in *; set (P56 := p56) in *; set (P57 := p57) in *; set (P64 := p64) in *
  end.
  clearbody P1 P17 P24 P48 P56 P57 P64.
  lazymatch type of W3 with evt bsegs _ ?X =>
    assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc). clear W3'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & FS3 & FP3) & Hc3'). clear Hc3. fold S in MU3, FS3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m1 m3 sp' ART1 ltac:(rewrite SP1; ul)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
    - right; right; right; right. exists f, 2%nat. change (fs_size 2) with 256. rewrite SHF, SHS. split; [exact INF1| lia]. }
  assert (AG13 : agree_on (fun x => ~ (f + 96 <= x < f + 120) /\ ~ (S + 12 <= x < S + 22)) m1 m3).
  { apply (agree_of_munch _ _ _ _ MU3). intros x (H1 & H2). cbn [outside]. repeat split; assumption. }
  assert (INV3 : lp_inv RT LIB Σ Σ1 m m3 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A).
  { unfold lp_inv. split; [exact ART3|]. split; [exact MI3|].
    split. { apply (stk_agree bsegs m1 m3 _ _ ST1); [| exact WM3]. eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx FR1' LOW LOR SPR SHT. split; ul. }
    split. { exists j0, j1, j2, j4, jq, je, jo, jn, jr, j13. apply (rw_cells_agree_nw bsegs m1 m3 _ _ FRl1). eapply agree_sub; [exact AG13|]. intros x Hx.
             unfold fa_locals2 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FR1' LOW LOR SPR SHT. split; ul. }
    split. { apply (stk_agree_nw bsegs m1 m3 _ _ STp1). eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in *. clear - Hx FR1' LOW LOR SPR SHT. split; ul. }
    split. { apply (rw_cells_agree_nw bsegs m1 m3 _ _ FRs1). eapply agree_sub; [exact AG13|]. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx.
             cbv beta. clear - Hx FR1' LOW LOR SPR SHT. split; ul. }
    split. { apply (rw_cells_agree_nw bsegs m1 m3 _ _ FH1). eapply agree_sub; [exact AG13|]. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx.
             cbv beta. clear - Hx FSELF. split; lia. }
    split; [exact FS3|].
    split. { destruct VR1 as (E & R & C & A0 & AH & SV & BLK). unfold vrepA. split; [exact E|]. split; [exact R|]. split; [exact C|]. split; [exact A0|]. split; [exact AH|].
             split. { apply (rw_cells_agree_nw bsegs m1 m3 _ _ SV). eapply agree_sub; [exact AG13|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. clear - Hx FSELF. split; lia. }
             destruct BLK as [B|(C1 & A16 & ASG & EL)]; [left; exact B| right]. split; [exact C1|]. split; [exact A16|]. split; [exact ASG|].
             apply (rw_cells_agree_nw bsegs m1 m3 _ _ EL). eapply agree_sub; [exact AG13|]. intros x Hx. rewrite velts_size, atp_elsA_length in Hx. fold P in Hx.
             cbv beta. clear - Hx AFL ASL. split; lia. }
    split. { apply (bytes_at_agree bsegs m1 m3 _ _ BS1). eapply agree_sub; [exact AG13|]. intros x Hx. cbv beta in Hx. cbv beta.
             destruct INLV as [(p & k & Hin & Q1 & Q2)| (E & DL)]; [| subst n; rewrite E in Hx; cbn [length] in Hx; lia].
             pose proof (FLV p k (INCL1 _ Hin)) as X1. pose proof (FSL p k (INCL1 _ Hin)) as X2. clear - Hx Q1 Q2 X1 X2. subst n. split; lia. }
    split. { apply (LIB_agree2 LIB LIB_loc m1 m3 LIB1). eapply agree_sub; [exact AG13|]. intros x Hx. pose proof (proj2 (lib_fp_static x Hx)) as R. cbv beta.
             clear - R FSEG2 SHB0. unfold SEGTOP_A, SHB in *. split; lia. }
    split. { intros a Ha Hout. rewrite <- (PRES1 a Ha Hout). apply MU3. cbn [outside]. split; [| split; [| exact I]].
             - exact (APF m1 (f + 96) (f + 120) ART1 ltac:(lia) ltac:(lia) (bv_unsigned a) (or_intror (conj Ha Hout))).
             - destruct Ha as [H|[H|[H|[H|H]]]].
               + clear - H SHT SP0R LOW LOR SPR. ul.
               + pose proof (client_static_range _ H) as R. clear - R SHB0. unfold SEGTOP_A, SHB in *. lia.
               + destruct H as (p & k & Hin & Hr). pose proof (FSL p k (INCL1 _ Hin)) as X2. clear - Hr X2. lia.
               + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin.
               + destruct H as (f9 & k9 & Hin & _). rewrite FRS0 in Hin. destruct Hin. }
    split; [exact FRS1| exact SP1]. }
  clear AG13 FS3.

  pose proof INV3 as (_ & _ & ST3 & _).
  pose proof (fobj_shz RT AF Σ1 m3 (f + 96) 80 ART3 (lp_fobjP RT LIB Σ Σ1 m m3 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV3 FPOS F64)) as SHZ3.
  assert (ACCP : acc bsegs m3 (f + 96) 80).
  { destruct (lp_fobjP RT LIB Σ Σ1 m m3 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV3 FPOS F64) as (A8 & _ & _ & HB).
    change (Z.to_nat ((80 + 7) / 8)) with 10%nat in HB. exact (acc_zero_run bsegs m3 (f + 96) 10 A8 ltac:(lia) HB). }
  assert (WRP : wr_at bsegs m3 (f + 96) 80)
    by (apply (rw_cells_wr_at bsegs m3 _ _ 80 FP3); unfold fz_parser; cbn [cells_size csize Nat.add]; lia).
  assert (INP : forall x, f + 96 <= x < f + 176 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x)
    by (intros x Hx; right; right; right; left; exists f, 2%nat; change (fs_size 2) with 256; split; [exact INF1| lia]).
  apply (MSET Σ1 PMc (Z_to_bv 64 0x96ce0) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
           (Z_to_bv 64 (f + 120)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
           (Z_to_bv 64 A) (Z_to_bv 64 (-16)) (Z_to_bv 64 16) (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m3 (f + 120) 24 z8 lo FDO MST);
    try reflexivity; try assumption; [.. | split; [subst S; exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM] |].
  - ul.
  - lia.
  - unfold checked_dst. rewrite EU1. split; [| split].
    + intros _. split; [apply (acc_sub bsegs m3 (f + 96) 80); [exact ACCP| lia| lia]|].
      right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
    + intros i Hi. apply INP. lia.
    + apply (wr_at_sub m3 (f + 96) 80); [exact WRP| lia| lia| lia].
  - unfold call_ok. rewrite EU1, SP1. split; [exact ST3|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia].
  - intros c4 (Hc4 & FC4). unfold icpt_post in Hc4.
    destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BS4) & FRM4 & Hc4'). clear Hc4.
    destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
    cbn [ms_fcsr] in FRM4. rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even 0x96ce0) in Hc4' by lia. change (Z.to_nat 24) with 24%nat in BS4.
    assert (EQ4 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m4 a = m3 a).
    { intros a Ha. apply PRES4; [exact (CLI m3 ART3 _ Ha)| exact (APF m3 (f + 120) (f + 120 + 24) ART3 ltac:(lia) ltac:(lia) _ Ha)]. }
    pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σ1 Σ1 m m3 m4 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV3 ltac:(lia) eq_refl eq_refl ART4 MI4 ST4 EQ4) as INV4.
    assert (FP4 : rw_cells bsegs m4 (f + 96) (fz_parser (C1 (Z_to_bv 8 0)) P1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) P17 (C4 (Z_to_bv 64 12))
                                                        (CB 24 (repeat z8 24)) (CB 8 P48) (CB 1 P56) P57 (CB 16 P64))).
    { unfold fz_parser in *.
      apply (cells_mid_update m3 m4 (f + 96) [C1 (Z_to_bv 8 0); CB 7 P1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 P17; C4 (Z_to_bv 64 12)]
               24 P24 (repeat z8 24) [CB 8 P48; CB 1 P56; CB 7 P57; CB 16 P64] FP3); [| exact WM4| | reflexivity].
      - apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4). intros x (Hx & Hn). cbn [app cells_size csize Nat.add] in Hx, Hn.
        split; [apply INP; lia| lia].
      - cbn [cells_size csize Nat.add]. replace (f + 96 + Z.of_nat 24) with (f + 120) by lia. exact BS4. }
    clear FP3 INV3 ACCP WRP ST3 SHZ3 EQ4 PRES4 BS4 Hc3' MU3 WM3 MI3 WM4.

    pose proof (fa_walk4 usp sp' f (Z_to_bv 64 0x96ce0) gp (Z_to_bv 64 0x653c30) w0 w1 w2 (Z_to_bv 64 (f + 120)) g1 g2 g3 g4 g5 g6 g7 s2x (Z_to_bv 64 A) (Z_to_bv 64 (-16)) (Z_to_bv 64 16) w3 w4 w5 w6
                  P1 P17 (repeat z8 24) P48 P56 P57 P64 F4 fc4 m4 FPOS ltac:(ul) FP4 MI4) as W4.
    fold S in W4.
    lazymatch type of W4 with evt bsegs _ ?X =>
      assert (W4' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W4) end.
    clear W4.
    apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W4') Hc4'). clear W4'. intros c5 Hc5.
    destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & FP5) & Hc5'). clear Hc5.
    assert (ART5 : ART RT Σ1 m5).
    { apply (art_fp_client RT AF Σ1 m4 m5 lo [(f + 144, f + 153)] ART4 ltac:(rewrite SP1; exact LOW)); [| exact MU5| exact WM5].
      constructor; [| constructor]. right; right. exists f, 2%nat. change (fs_size 2) with 256. cbn [fst snd]. split; [exact INF1| lia]. }
    assert (EQ5 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m5 a = m4 a).
    { intros a Ha. apply MU5. cbn [outside]. split; [exact (APF m4 (f + 144) (f + 153) ART4 ltac:(lia) ltac:(lia) _ Ha)| exact I]. }
    pose proof INV4 as (_ & _ & ST4' & _).
    assert (ST5 : stk bsegs m5 lo sp').
    { apply (stk_agree bsegs m4 m5 _ _ ST4'); [| exact WM5]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbv beta in Hx. cbn [outside].
      clear - Hx FR1' LOW LOR SPR. split; [ul| exact I]. }
    pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σ1 Σ1 m m4 m5 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV4 ltac:(lia) eq_refl eq_refl ART5 MI5 ST5 EQ5) as INV5.
    clear INV4 ST4' EQ5 FP4 MU5 WM5 MI4 ST4 Hc4'.

    assert (ACCP : acc bsegs m5 (f + 96) 80).
    { destruct (lp_fobjP RT LIB Σ Σ1 m m5 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV5 FPOS F64) as (A8 & _ & _ & HB).
      change (Z.to_nat ((80 + 7) / 8)) with 10%nat in HB. exact (acc_zero_run bsegs m5 (f + 96) 10 A8 ltac:(lia) HB). }
    assert (WRP : wr_at bsegs m5 (f + 96) 80)
      by (apply (rw_cells_wr_at bsegs m5 _ _ 80 FP5); unfold fz_parser; cbn [cells_size csize Nat.add]; lia).
    apply (MSET Σ1 PMc (Z_to_bv 64 0x96d00) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) w0 w1 w2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (f + 160)) (Z_to_bv 64 0) (Z_to_bv 64 16) g3 g4 g5 g6 g7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
             (Z_to_bv 64 A) (Z_to_bv 64 (-16)) (Z_to_bv 64 16) (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) w3 w4 w5 w6 F4 fc4 m5 (f + 160) 16 z8 lo FDO MST);
      try reflexivity; try assumption; [.. | split; [exact Hc5'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM4] |].
    + ul.
    + lia.
    + unfold checked_dst. rewrite EU1. split; [| split].
      * intros _. split; [apply (acc_sub bsegs m5 (f + 96) 80); [exact ACCP| lia| lia]|].
        right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia].
      * intros i Hi. apply INP. lia.
      * apply (wr_at_sub m5 (f + 96) 80); [exact WRP| lia| lia| lia].
    + unfold call_ok. rewrite EU1, SP1. split; [exact ST5|]. split; [ul|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia].
    + intros c6 (Hc6 & FC6). unfold icpt_post in Hc6.
      destruct (ASTA_unpack_f RT Σ1 _ _ c6 Hc6 FC6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BS6) & FRM6 & Hc6'). clear Hc6.
      destruct RS6 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F6 & fc6 & ->).
      cbn [ms_fcsr] in FRM6. rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even 0x96d00) in Hc6' by lia. change (Z.to_nat 16) with 16%nat in BS6.
      assert (EQ6 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m6 a = m5 a).
      { intros a Ha. apply PRES6; [exact (CLI m5 ART5 _ Ha)| exact (APF m5 (f + 160) (f + 160 + 16) ART5 ltac:(lia) ltac:(lia) _ Ha)]. }
      pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σ1 Σ1 m m5 m6 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV5 ltac:(lia) eq_refl eq_refl ART6 MI6 ST6 EQ6) as INV6.
      assert (FP6 : rw_cells bsegs m6 (f + 96) (parser_init P1 P17 P57)).
      { unfold parser_init, fz_parser in *.
        apply (cells_mid_update m5 m6 (f + 96) [C1 (Z_to_bv 8 0); CB 7 P1; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 P17; C4 (Z_to_bv 64 12);
                                                 CB 24 (repeat z8 24); C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0); CB 7 P57]
                 16 P64 (repeat z8 16) [] FP5); [| exact WM6| | reflexivity].
        - apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES6). intros x (Hx & Hn). cbn [app cells_size csize Nat.add] in Hx, Hn.
          split; [apply INP; lia| lia].
        - cbn [cells_size csize Nat.add]. replace (f + 96 + Z.of_nat 64) with (f + 160) by lia. exact BS6. }

      apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c6 Hc6'); intros ms0 <-; exact FRM6].
      exists Σ1, sp', f, A. split.
      * eapply ASTA_conseq; [exact Hc6'|]. intros ms <-. exists m6, (Z_to_bv 64 0x96d00), y0, y1, y2, (Z_to_bv 64 (f + 160)), k1, k2, k3, k4, k5, k6, k7, s2x, (Z_to_bv 64 (-16)), (Z_to_bv 64 16), y3, y4, y5, y6, F6, fc6, h3, t, P1, P17, P57.
        split; [subst S; reflexivity|]. split; [exact FRM6|]. split; [exact INV6| exact FP6].
      * split; [exact VL1|]. split; [exact CR1|]. repeat split; try assumption; lia.
Qed.
End Top2a.
