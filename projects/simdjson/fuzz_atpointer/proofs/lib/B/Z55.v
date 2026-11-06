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
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3 Sj_new Zpo Zwn Z4a Z73 Z5g Z6m Z71 Z5h Z5i Z5j Z6q Z6y Z6p Z4e Z4l Z4m Z4n Z52 Z57 Z56.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Top2b.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis MCPY : memcpy_icontract_f RT e_asan_memcpy.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis PID : pid_cps RT LIB.
Hypothesis PID0 : pid0_cps RT LIB.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac ul := unfold FUZZ_STACK, ATPA_SPLITINTO_STACK, ATPA_SPLIT_STACK, ATPA_PUSH_STACK, PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem lftoi_par2 : forall (Σ Σ1 : rts RT) PMc (m m1 : mem) (usp sp' f A lo d : Z) (bs : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x s8x t3 t4 t5 t6 : word) F fc (h3 t p1 p17 p57 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  0 < d -> Z.of_nat (length bs) < 2^26 ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ -> 8 + vcost_pushes (atp_P (chars bs)) 0 0 <= 2^32 ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
  lp_inv RT LIB Σ Σ1 m m1 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A ->
  rw_cells bsegs m1 (f + 96) (parser_init p1 p17 p57) ->
  vliveA (rt_live RT Σ1) A (vcap_iter (atp_P (chars bs)) 0 0) (Z.of_nat (atp_P (chars bs))) (rt_live RT Σ) ->
  rt_credit RT Σ - 2 - vcost_pushes (atp_P (chars bs)) 0 0 <= rt_credit RT Σ1 ->
  usp - 304 <= sp' <= usp - 288 -> sp' mod 32 = 0 -> 0 < f -> f mod 64 = 0 -> f + 256 <= rt_sp0 RT Σ - STACK_WIN ->
  (f + 256 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) ->
  SHB <= f / 8 + 2147450880 -> f / 8 + 2147450880 + 32 + 1 <= rt_sp0 RT Σ - STACK_WIN -> frm0 fc ->
  cps_f (ASTA RT Σ1 PMc (eq (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
                                     s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) s7x s8x
                                     (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
                                F (Z_to_bv 64 0x96d00) fc None m1 (seg_rom bsegs))))
    (gate_postA RT LIB Σ PMc usp lo d bs ra gp (Z_to_bv 64 0x653c30) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using LIB_loc AF MSET MCPY NEWA DELA PID PID0 AFC.
  intros Σ Σ1 PMc m m1 usp sp' f A lo d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x s8x t3 t4 t5 t6 F fc h3 t p1 p17 p57
    FDO MST D0 BSL INLV FRS0 LVPOS LVB CR0 VCB LOW LOR SPT SPA INV1 FP1 VL1 CR1 SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof INV1 as (ART1 & MI1 & ST1 & (j0 & j1 & j2 & j4 & jq & je & jo & jn & jr & j13 & FRl1) & STp1 & FRs1 & FH1 & FS1 & VR1 & BS1 & LIB1 & PRES1 & FRS1 & SP1).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SP0R. rewrite SP1 in SP0R.
  set (n := Z.of_nat (length bs)) in *. set (P := atp_P (chars bs)) in *. set (S := f / 8 + 2147450880) in *. set (capv := vcap_iter P 0 0) in *.
  assert (INF1 : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (SHF : shad (f + 256) = S + 32) by (subst S; unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (SHS : shad f = S) by reflexivity.
  assert (EU1 : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; ul).
  assert (EUSP : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; ul).
  pose proof (af_frames_range RT AF Σ1 m1 f 2%nat ART1 INF1) as (_ & _ & _ & FLV). change (fs_size 2) with 256 in FLV.
  assert (P2 : (2 <= P)%nat) by (subst P; unfold atp_P; lia).
  pose proof (vcap_iter_inv P 0 0 ltac:(lia) ltac:(lia)) as CAPI. rewrite Z.add_0_l in CAPI. fold capv in CAPI.
  assert (INCL1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)).
  { intros e He. unfold vliveA in VL1. rewrite VL1. apply in_or_app. right. exact He. }
  assert (INA : In (A, 16 * Z.of_nat P) (rt_live RT Σ1)).
  { unfold vliveA, vblockA in VL1. rewrite VL1. apply in_or_app. left. destruct (Z.eqb_spec capv 0); [lia|]. apply ann_block_vis. }
  pose proof (FLV A _ INA) as AFL. pose proof (af_live_range RT AF Σ1 m1 A _ ART1 INA) as (AR0 & AR1 & AR2). rewrite SP1 in AR1.
  assert (LVL1 : Z.of_nat (length (rt_live RT Σ1)) <= 3 + Z.of_nat (length (rt_live RT Σ))).
  { unfold vliveA in VL1. rewrite VL1, length_app. pose proof (vblockA_length A capv (Z.of_nat P)). lia. }
  assert (LPX1 : lposx (rt_live RT Σ1)).
  { unfold vliveA in VL1. rewrite VL1. apply lposx_app; [| exact (lposx_of_pos _ LVPOS)].
    unfold vblockA. destruct (capv =? 0); [intros p k []| apply lposx_ann_block; lia]. }

  destruct (atp_elsA_shape d (chars bs)) as (P0 & e1 & rest & EELS & P0Z & ES0).
  destruct (atp_s0_bytes bs) as (bs0 & ES0B & EBS0 & LBS0).
  set (l0 := Z.of_nat (length bs0)) in *.
  assert (EL0 : zlength (atp_s0 (chars bs)) = l0) by (rewrite ES0B, chars_length; reflexivity).
  rewrite EL0 in EELS.
  assert (L0R : 0 <= l0 <= n) by (subst l0 n; lia).
  pose proof VR1 as (_ & _ & CAPB & A0 & AH & SV1 & BLK1).
  destruct BLK1 as [(C0 & _)|(C1 & A16 & APOS & EL1)]; [exfalso; lia|].
  rewrite EELS in EL1. cbn [velts fst snd] in EL1.
  assert (P0R : 0 <= P0 < 2^64).
  { destruct P0Z as [(-> & _)| ->]; [lia|]. destruct INLV as [(p & k & Hin & Q1 & Q2)|(_ & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ1 m1 p k ART1 (INCL1 _ Hin)) as (_ & R1 & _). rewrite SP1 in R1. clear - D0 Q1 Q2 R1 SP0R L0R. ul. }
  assert (SHZA : shz m1 A 16).
  { pose proof (shz_live RT AF Σ1 m1 A _ ART1 INA ltac:(clear - A16; Z.div_mod_to_equations; lia)) as X.
    eapply shz_sub; [exact X| lia|]. clear - P2. Z.div_mod_to_equations. nia. }

  assert (CLI1 : forall mx, ART RT Σ1 mx -> forall x, lp_dom RT Σ usp sp' f A d bs x -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros mx ARTx. exact (lp_client RT AF Σ Σ1 mx usp sp' f lo d A bs ARTx FRS1 FRS0 INCL1 INA INLV FPOS F64 ltac:(lia) SPT). }

  pose proof FRl1 as RES1. unfold fa_locals2 in RES1.
  lazymatch type of RES1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] ++ [c10] ++ rest) in RES1 end.
  apply Zvw.rw_cells_app in RES1. destruct RES1 as [_ RES1]. apply Zvw.rw_cells_app in RES1. destruct RES1 as [RES1 _].
  cbn [cells_size csize Nat.add] in RES1. replace (sp' + Z.of_nat 136) with (sp' + 136) in RES1 by lia.
  pose proof (lp_fobjP RT LIB Σ Σ1 m m1 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV1 FPOS F64) as FOBJ1.

  pose proof (pid_costA_bound 0 ltac:(lia)) as PC0B. pose proof (mcost_le 64 ltac:(lia)) as MC64.
  assert (VC0 : 0 <= vcost_pushes P 0 0) by (apply vcost_pushes_nonneg; lia).
  destruct (Z.lt_ge_cases 1048512 l0) as [BIG|SMALL].
  -
    assert (EDOC : atp_doc (chars bs) = []).
    { unfold atp_doc. rewrite EL0. replace (l0 <=? SJ_PADMAX) with false by (symmetry; apply Z.leb_gt; unfold SJ_PADMAX; lia). reflexivity. }
    assert (EDL : doc_len bs = 0) by (unfold doc_len; rewrite EDOC; reflexivity).
    assert (EDC : doc_cap bs = 32) by (unfold doc_cap; rewrite EDL; reflexivity).
    pose proof (fa_walk5_big usp sp' f A P0 l0 (velts (e1 :: rest)) x1 gp (Z_to_bv 64 0x653c30) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x s8x t3 t4 t5 t6 F fc m1
                  FPOS ltac:(ul) ltac:(ul) ltac:(ul) APOS ltac:(clear - A16; Z.div_mod_to_equations; lia) ltac:(lia) P0R ltac:(subst l0 n; lia) SHZA EL1 MI1) as W5.
    fold S in W5.
    lazymatch type of W5 with evt bsegs _ ?X =>
      assert (W5' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W5) end.
    clear W5.
    apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ1 PMc _ _ MST W5') Hc). clear W5'. intros c6 Hc6.
    destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & <- & Hc6'). clear Hc6.
    apply (PID0 Σ1 PMc (Z_to_bv 64 0x96dcc) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (sp' + 136)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) a6 a7
             s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) (Z_to_bv 64 l0) s8x
             (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m1 (f + 96) (sp' + 136) p1 p17 p57 jr lo FDO MST);
      try reflexivity; try assumption; [.. | split; [exact Hc6'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c6 Hc6'); intros ms0 <-; exact FRM] |].
    + f_equal. lia.
    + rewrite EU1. lia.
    + ul.
    + clear - LVL1 LVB. unfold FUZZ_LIVE in *. lia.
    + clear - CR1 CR0 VCB PC0B VC0. unfold FUZZ_COST in *. lia.
    + rewrite EU1. exact ST1.
    + rewrite SP1. exact LOW.
    + rewrite EU1. ul.
    + rewrite EU1. ul.
    + rewrite EU1. clear - SPA'. Z.div_mod_to_equations. lia.
    + intros c8 ((Σp & impl & idx & oc & ia & tape & sbuf & Hc8 & LVp & MODS & FRSp & SPp & CRp) & FC8).
      destruct (ASTA_unpack_f RT Σp _ _ c8 Hc8 FC8) as (ms8 & (v8 & m8 & RS8 & (ART8 & MI8 & ST8) & PRES8 & (r & j20 & RC8 & R64 & OKR8) & LIB8 & PD8 & PST8) & FRM8 & Hc8').
      clear Hc8. destruct RS8 as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & F8 & fc8 & ->).
      cbn [ms_fcsr] in FRM8. rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even 0x96dcc) in Hc8' by lia.
      destruct (rw_cells_forget bsegs m8 (sp' + 136) _ RC8) as (jr' & RES8).
      assert (RSZ : cells_size (res_cellsA (f + 96 + 24) r j20) = 24%nat) by (unfold res_cellsA; destruct (bv_eqb _ _); reflexivity). rewrite RSZ in RES8.
      assert (EQ8 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> ~ (sp' + 136 <= bv_unsigned a < sp' + 160) ->
                      ~ in_ranges LIB_FP (bv_unsigned a) -> m8 a = m1 a).
      { intros a Ha H1 H2. apply PRES8; [exact (CLI1 m1 ART1 _ Ha)|]. cbn [outside]. split; [| split; [clear - H1; lia| exact (outside_of_nin _ _ H2)]].
        exact (lp_apart_frame RT AF Σ Σ1 m1 usp sp' f lo d A (f + 96) (f + 96 + 80) bs ART1 FRS1 FRS0 SP1 INCL1 INA INLV LOW LOR ltac:(lia) FSELF ltac:(lia) ltac:(lia) _ Ha). }
      pose proof (lp_inv_xfer_pid RT LIB LIB_loc AF Σ Σ1 Σp m m1 m8 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A jr'
                    INV1 FRS0 INCL1 INA INLV LOW LOR SPR FSEG2 SHB0 FRSp SPp ART8 MI8 ST8 EQ8 LIB8 RES8) as INV8.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σp PMc (eq _) c8 Hc8'); intros ms0 <-; exact FRM8].
      assert (RCC : res_cellsA (f + 96 + 24) r j20 = res_cellsA (f + 120) r j20) by (f_equal; lia). rewrite RCC in RC8.
      apply (gate_intro RT LIB Σ Σp PMc c8 m m8 usp sp' f A lo d bs ra gp (Z_to_bv 64 0x653c30) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 0x96dcc) z0 z1 z2 v8 q1 q2 q3 q4 q5 q6 q7 s2x (Z_to_bv 64 A) (Z_to_bv 64 l0) s8x z3 z4 z5 z6 F8 fc8 h3 t j20 impl idx oc ia tape sbuf r);
        [ unfold sa_regs; subst S; exact Hc8' | exact FRM8 | exact INV8 | exact RC8 | exact R64 | rewrite EDC; exact OKR8
        | unfold vliveA in VL1; rewrite <- VL1; exact PD8 | rewrite EDC; exact PST8
        | exact SPR | exact SPA' | exact FPOS | exact F64 | exact FR1' | exact FSEG2 | exact FSELF | exact SHB0 | exact SHT
        | rewrite EDC, LVp; unfold vliveA in VL1; rewrite VL1; reflexivity | exact MODS
        | idtac ].
      rewrite EDL. subst P. clear - CRp CR1 VC0. change (0 + 64) with 64. pose proof (mcost_nonneg 64 ltac:(lia)). lia.
  -
    assert (EDOC : atp_doc (chars bs) = atp_s0 (chars bs)).
    { unfold atp_doc. rewrite EL0. replace (l0 <=? SJ_PADMAX) with true by (symmetry; apply Z.leb_le; unfold SJ_PADMAX; lia). reflexivity. }
    assert (EDL : doc_len bs = l0) by (unfold doc_len; rewrite EDOC; exact EL0).
    assert (EDC : doc_cap bs = Z.max l0 32) by (unfold doc_cap; rewrite EDL; reflexivity).
    set (cap := Z.max l0 32) in *.
    pose proof (sc_idx_bounds cap ltac:(lia)) as IXB. pose proof (al_tape_bounds cap ltac:(lia)) as TPB. pose proof (al_sbuf_bounds cap ltac:(lia)) as SBB.
    pose proof (pid_costA_bound l0 ltac:(lia)) as PCB. pose proof (mcost_le (l0 + 64) ltac:(lia)) as MCB. pose proof (mcost_nonneg (l0 + 64) ltac:(lia)) as MC0.
    pose proof (AFC Σ1 m1 ART1) as GOT1.
    pose proof (fa_walk5_small usp sp' f A P0 l0 (velts (e1 :: rest)) x1 gp (Z_to_bv 64 0x653c30) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x s8x t3 t4 t5 t6 F fc m1
                  FPOS ltac:(ul) APOS ltac:(clear - A16; Z.div_mod_to_equations; lia) ltac:(lia) P0R ltac:(lia) SHZA EL1 GOT1 MI1) as W5.
    fold S in W5.
    lazymatch type of W5 with evt bsegs _ ?X =>
      assert (W5' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W5) end.
    clear W5.
    apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ1 PMc _ _ MST W5') Hc). clear W5'. intros c6 Hc6.
    destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & <- & Hc6'). clear Hc6.

    apply (NEWA Σ1 PMc (Z_to_bv 64 0x96d54) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
             (Z_to_bv 64 (l0 + 64)) (Z_to_bv 64 0x2ca50) a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) (Z_to_bv 64 A) (Z_to_bv 64 l0) (Z_to_bv 64 P0)
             (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m1 (l0 + 64) lo FDO MST);
      try reflexivity; try assumption; [.. | split; [subst S; exact Hc6'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c6 Hc6'); intros ms0 <-; exact FRM] |].
    + lia.
    + clear - LVL1 LVB. unfold FUZZ_LIVE, LIVE_MAX in *. lia.
    + clear - CR1 CR0 VCB MCB VC0 L0R SMALL. unfold FUZZ_COST in *. lia.
    + rewrite EU1. exact ST1.
    + rewrite SP1. exact LOW.
    + rewrite EU1. ul.
    + rewrite EU1. ul.
    + rewrite EU1. clear - SPA'. Z.div_mod_to_equations. lia.
    + intros c7 ((Σn & buf & Hc7 & LVn & FRSn & SPn & CRn & BPOS & B16 & BTOP) & FC7).
      destruct (ASTA_unpack_f RT Σn _ _ c7 Hc7 FC7) as (ms7 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & WRB & ACB) & FRM7 & Hc7'). clear Hc7.
      destruct RS7 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F7 & fc7 & ->).
      cbn [ms_fcsr] in FRM7. rewrite EU1 in ST7, PRES7. rewrite (ret_pc_even 0x96d54) in Hc7' by lia.
      assert (EQ7 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m7 a = m1 a) by (intros a Ha; exact (PRES7 a (CLI1 m1 ART1 _ Ha))).
      pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σ1 Σn m m1 m7 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV1 ltac:(lia) FRSn SPn ART7 MI7 ST7 EQ7) as INV7.
      assert (FP7 : rw_cells bsegs m7 (f + 96) (parser_init p1 p17 p57)).
      { apply (rw_cells_agree_nw bsegs m1 m7 _ _ FP1). apply (agree_of_pres _ _ _ _ _ _ PRES7). intros x Hx. unfold parser_init, fz_parser in Hx.
        cbn [cells_size csize Nat.add] in Hx. right; right; right; left. exists f, 2%nat. change (fs_size 2) with 256. split; [exact INF1| lia]. }

      assert (FRSn' : rt_frames RT Σn = [(f, 2%nat)]) by (rewrite FRSn; exact FRS1).
      assert (SPn' : rt_sp0 RT Σn = rt_sp0 RT Σ) by (rewrite SPn; exact SP1).
      assert (INFn : In (f, 2%nat) (rt_frames RT Σn)) by (rewrite FRSn'; left; reflexivity).
      assert (INCLn : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σn)) by (intros e He; rewrite LVn; right; exact (INCL1 e He)).
      assert (INAn : In (A, 16 * Z.of_nat P) (rt_live RT Σn)) by (rewrite LVn; right; exact INA).
      assert (INBn : In (buf, l0 + 64) (rt_live RT Σn)) by (rewrite LVn; left; reflexivity).
      assert (CLIn : forall mx, ART RT Σn mx -> forall x, lp_dom RT Σ usp sp' f A d bs x -> aclient (rt_live RT Σn) (rt_frames RT Σn) sp' x).
      { intros mx ARTx. exact (lp_client RT AF Σ Σn mx usp sp' f lo d A bs ARTx FRSn' FRS0 INCLn INAn INLV FPOS F64 ltac:(lia) SPT). }
      assert (APBn : forall mx, ART RT Σn mx -> forall x, lp_dom RT Σ usp sp' f A d bs x -> ~ (buf <= x < buf + (l0 + 64))).
      { intros mx ARTx. exact (lp_apart_chunk RT AF Σ Σn mx usp sp' f lo d A buf (l0 + 64) [] (rt_live RT Σ1) bs ARTx FRSn' FRS0 SPn' LVn INCL1 INA INLV LOW LOR ltac:(lia) F64). }
      pose proof (af_frames_range RT AF Σn m7 f 2%nat ART7 INFn) as (_ & _ & _ & FLVn). change (fs_size 2) with 256 in FLVn. pose proof (FLVn buf _ INBn) as BFL.
      assert (LPXn : lposx (rt_live RT Σn)) by (rewrite LVn; apply lposx_cons; [lia| exact LPX1]).

      pose proof (fa_walk6 usp sp' f A buf l0 P0 gp (Z_to_bv 64 0x653c30) w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s2x w3 w4 w5 w6 F7 fc7 m7 FPOS ltac:(ul) BPOS ltac:(ul) ltac:(lia)) as W6.
      unfold sa_regs in W6. fold S in W6.
      lazymatch type of W6 with evt bsegs _ ?X =>
        assert (W6' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W6) end.
      clear W6.
      apply (cps_realizes bsegs _ _ _ c7 (asta_evt_c RT AF Σn PMc _ _ MST W6') Hc7'). clear W6'. intros c8 Hc8.
      destruct (ASTA_unpack RT Σn _ _ c8 Hc8) as (ms8 & <- & Hc8'). clear Hc8.
      apply (MSET Σn PMc (Z_to_bv 64 0x96d74) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) w0 w1 w2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
               (Z_to_bv 64 (buf + l0)) (Z_to_bv 64 0) (Z_to_bv 64 64) g3 g4 g5 g6 g7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
               (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0) (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) w3 w4 w5 w6 F7 fc7 m7 (buf + l0) 64 z8 lo FDO MST);
        try reflexivity; try assumption; [.. | split; [subst S; exact Hc8'| apply (cfrm0_of_asta RT Σn PMc (eq _) c8 Hc8'); intros ms0 <-; exact FRM7] |].
      * clear - BPOS BTOP L0R. ul.
      * lia.
      * unfold checked_dst. rewrite EU1. split; [| split].
        -- intros _. split; [apply (acc_sub bsegs m7 buf (l0 + 64)); [exact ACB| lia| lia]|]. left. exists buf, (l0 + 64). split; [exact INBn| lia].
        -- intros i Hi. right; right; left. exists buf, (l0 + 64). split; [exact INBn| lia].
        -- apply (wr_at_sub m7 buf (l0 + 64)); [exact WRB| lia| lia| lia].
      * unfold call_ok. rewrite EU1, SPn'. split; [exact ST7|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia].
      * intros c9 (Hc9 & FC9). unfold icpt_post in Hc9.
        destruct (ASTA_unpack_f RT Σn _ _ c9 Hc9 FC9) as (ms9 & (m9 & RS9 & (ART9 & MI9 & WM9 & ST9) & PRES9 & BS9) & FRM9 & Hc9'). clear Hc9.
        destruct RS9 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F9 & fc9 & ->).
        cbn [ms_fcsr] in FRM9. rewrite EU1 in ST9, PRES9. rewrite (ret_pc_even 0x96d74) in Hc9' by lia. change (Z.to_nat 64) with 64%nat in BS9.
        assert (EQ9 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m9 a = m7 a).
        { intros a Ha. apply PRES9; [exact (CLIn m7 ART7 _ Ha)|]. pose proof (APBn m7 ART7 _ Ha). lia. }
        pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σn Σn m m7 m9 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV7 ltac:(lia) eq_refl eq_refl ART9 MI9 ST9 EQ9) as INV9.
        assert (FP9 : rw_cells bsegs m9 (f + 96) (parser_init p1 p17 p57)).
        { apply (rw_cells_agree_nw bsegs m7 m9 _ _ FP7). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES9). intros x Hx. unfold parser_init, fz_parser in Hx.
          cbn [cells_size csize Nat.add] in Hx. split; [right; right; right; left; exists f, 2%nat; change (fs_size 2) with 256; split; [exact INFn| lia]| clear - Hx BFL; lia]. }
        clear EQ7 PRES7 Hc7' Hc8' WM7 EQ9.
        destruct (Z.eq_dec l0 0) as [LZ|LNZ].
        --
           assert (B0 : bs0 = []) by (destruct bs0; [reflexivity| exfalso; subst l0; cbn [length] in LZ; lia]).
           rewrite LZ in Hc9'.
           pose proof (fa_walk7z usp sp' f buf P0 (Z_to_bv 64 0x96d74) gp (Z_to_bv 64 0x653c30) y0 y1 y2 (Z_to_bv 64 (buf + 0)) k1 k2 k3 k4 k5 k6 k7 s2x y3 y4 y5 y6 F9 fc9 m9
                         FPOS ltac:(ul) ltac:(ul) ltac:(ul)) as W7.
           unfold sa_regs in W7. fold S in W7.
           lazymatch type of W7 with evt bsegs _ ?X =>
             assert (W7' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W7) end.
           clear W7.
           apply (cps_realizes bsegs _ _ _ c9 (asta_evt_c RT AF Σn PMc _ _ MST W7') Hc9'). clear W7'. intros c10 Hc10.
           destruct (ASTA_unpack RT Σn _ _ c10 Hc10) as (ms10 & <- & Hc10'). clear Hc10.
           rewrite LZ, Z.add_0_r in BS9. subst bs0.
           exact (lftoi_ptail RT LIB LIB_loc AF DELA PID Σ Σ1 Σn PMc m m9 usp sp' f A lo d buf P0 bs [] ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y0 y1 y2 k6 k7 s2x y3 y4 y5 y6 F9 fc9 h3 t p1 p17 p57
                    FDO MST INLV FRS0 LVB CR0 VCB LOW LOR SPT VL1 CR1 LVL1 LPX1 LVn FRSn' SPn' CRn B16 SMALL L0R EDL EDC SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT
                    INV9 FP9 BS9 FRM9 T c10 (conj ltac:(unfold sa_regs; subst S; exact Hc10') (cfrm0_of_asta RT Σn PMc (eq _) c10 Hc10' ltac:(intros ms0 <-; exact FRM9))) Hk).
        --
           assert (LPOS : 0 < l0) by lia.

           assert (NE0 : atp_s0 (chars bs) <> []) by (rewrite ES0B; destruct bs0; [subst l0; cbn [length] in LPOS; lia| discriminate]).
           assert (EP0 : P0 = d) by (destruct P0Z as [(_ & E)| E]; [exact (False_ind _ (NE0 E))| rewrite E; lia]).
           pose proof INLV as INLV0. destruct INLV0 as [(pB & kB & INPB & PB1 & PB2)|(E0 & _)]; [| exfalso; subst bs; rewrite firstn_nil in EBS0; subst bs0 l0; cbn [length] in LPOS; lia].
           pose proof (af_live_range RT AF Σn m9 pB kB ART9 (INCLn _ INPB)) as (PBR0 & PBR1 & PBR2). rewrite SPn' in PBR1.
           pose proof (af_live_disj RT AF Σn m9 buf (l0 + 64) pB kB [] (rt_live RT Σ1) ART9 LVn (INCL1 _ INPB)) as DJB.
           pose proof (fa_walk7c usp sp' f buf l0 P0 (Z_to_bv 64 0x96d74) gp (Z_to_bv 64 0x653c30) y0 y1 y2 (Z_to_bv 64 (buf + l0)) k1 k2 k3 k4 k5 k6 k7 s2x y3 y4 y5 y6 F9 fc9 m9
                         FPOS ltac:(ul) ltac:(subst l0 n; lia)) as W7.
           unfold sa_regs in W7. fold S in W7.
           lazymatch type of W7 with evt bsegs _ ?X =>
             assert (W7' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W7) end.
           clear W7.
           apply (cps_realizes bsegs _ _ _ c9 (asta_evt_c RT AF Σn PMc _ _ MST W7') Hc9'). clear W7'. intros c10 Hc10.
           destruct (ASTA_unpack RT Σn _ _ c10 Hc10) as (ms10 & <- & Hc10'). clear Hc10.
           pose proof INV9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BS9d & _).
           assert (BS0 : bytes_at bsegs m9 P0 bs0) by (rewrite EP0, EBS0; exact (bytes_at_firstn' m9 d bs _ BS9d)).
           apply (MCPY Σn PMc (Z_to_bv 64 0x96d88) (Z_to_bv 64 sp') gp (Z_to_bv 64 0x653c30) y0 y1 y2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                    (Z_to_bv 64 buf) (Z_to_bv 64 P0) (Z_to_bv 64 l0) k3 k4 k5 k6 k7 s2x (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120))
                    (Z_to_bv 64 buf) (Z_to_bv 64 l0) (Z_to_bv 64 P0) (Z_to_bv 64 S) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) y3 y4 y5 y6 F9 fc9 m9 buf P0 bs0 lo FDO MST);
             try reflexivity; try assumption; [.. | split; [subst S; exact Hc10'| apply (cfrm0_of_asta RT Σn PMc (eq _) c10 Hc10'); intros ms0 <-; exact FRM9] |].
           ++ clear - BPOS BTOP L0R. ul.
           ++ rewrite EP0. clear - D0 PB1 PB2 PBR1 SP0R L0R. subst n l0. ul.
           ++ subst l0. lia.
           ++ unfold checked_src. rewrite EU1, EP0. split.
              ** intros _. split; [| left; exists pB, kB; split; [exact (INCLn _ INPB)| subst n l0; lia]].
                 apply (acc_sub bsegs m9 pB kB); [exact (proj2 (af_acc_live RT AF Σn m9 pB kB ART9 (INCLn _ INPB)))| lia| subst n l0; lia].
              ** left. clear - PB1 PB2 PBR1 LOW L0R. subst n l0. lia.
           ++ unfold checked_dst. rewrite EU1. split; [| split].
              ** intros _. split; [| left; exists buf, (l0 + 64); split; [exact INBn| subst l0; lia]].
                 apply (acc_sub bsegs m9 buf (l0 + 64)); [exact (proj2 (af_acc_live RT AF Σn m9 buf (l0 + 64) ART9 INBn))| lia| subst l0; lia].
              ** intros i Hi. right; right; left. exists buf, (l0 + 64). split; [exact INBn| subst l0; lia].
              ** apply (wr_at_sub m9 buf (l0 + 64)); [exact (proj1 (af_acc_live RT AF Σn m9 buf (l0 + 64) ART9 INBn))| lia| subst l0; lia| subst l0; lia].
           ++ rewrite EP0. clear - DJB PB1 PB2 L0R LPOS. subst n l0. lia.
           ++ unfold call_ok. rewrite EU1, SPn'. split; [exact ST9|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA'; Z.div_mod_to_equations; lia].
           ++ intros c10b (Hc10b & FC10b). unfold icpt_post in Hc10b.
              destruct (ASTA_unpack_f RT Σn _ _ c10b Hc10b FC10b) as (ms10b & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & BS10) & FRM10 & Hc10b'). clear Hc10b.
              destruct RS10 as (x0' & x1' & x2' & r1 & r2 & r3 & r4 & r5 & r6 & r7 & x3' & x4' & x5' & x6' & F10 & fc10 & ->).
              cbn [ms_fcsr] in FRM10. rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even 0x96d88) in Hc10b' by lia.
              assert (EQ10 : forall a : word, lp_dom RT Σ usp sp' f A d bs (bv_unsigned a) -> m10 a = m9 a).
              { intros a Ha. apply PRES10; [exact (CLIn m9 ART9 _ Ha)|]. pose proof (APBn m9 ART9 _ Ha). subst l0. lia. }
              pose proof (lp_inv_xfer' RT LIB LIB_loc Σ Σn Σn m m9 m10 usp sp' f lo d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 t A INV9 ltac:(lia) eq_refl eq_refl ART10 MI10 ST10 EQ10) as INV10.
              assert (FP10 : rw_cells bsegs m10 (f + 96) (parser_init p1 p17 p57)).
              { apply (rw_cells_agree_nw bsegs m9 m10 _ _ FP9). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES10). intros x Hx. unfold parser_init, fz_parser in Hx.
                cbn [cells_size csize Nat.add] in Hx. split; [right; right; right; left; exists f, 2%nat; change (fs_size 2) with 256; split; [exact INFn| lia]| clear - Hx BFL L0R; subst l0; lia]. }
              assert (BUF10 : bytes_at bsegs m10 buf (bs0 ++ repeat z8 64)).
              { apply bytes_at_app. split; [exact BS10|]. apply (bytes_at_agree bsegs m9 m10 _ _ BS9). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES10).
                intros x Hx. rewrite repeat_length in Hx. split; [right; right; left; exists buf, (l0 + 64); split; [exact INBn| subst l0; lia]| subst l0; lia]. }

              pose proof (fa_walk8 usp sp' f buf l0 P0 (Z_to_bv 64 0x96d88) gp (Z_to_bv 64 0x653c30) x0' x1' x2' (Z_to_bv 64 buf) r1 r2 r3 r4 r5 r6 r7 s2x x3' x4' x5' x6' F10 fc10 m10
                            FPOS ltac:(ul) ltac:(ul) ltac:(ul)) as W8.
              unfold sa_regs in W8. fold S in W8.
              lazymatch type of W8 with evt bsegs _ ?X =>
                assert (W8' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W8) end.
              clear W8.
              apply (cps_realizes bsegs _ _ _ c10b (asta_evt_c RT AF Σn PMc _ _ MST W8') Hc10b'). clear W8'. intros c10c Hc10c.
              destruct (ASTA_unpack RT Σn _ _ c10c Hc10c) as (ms10c & <- & Hc10c'). clear Hc10c.
              exact (lftoi_ptail RT LIB LIB_loc AF DELA PID Σ Σ1 Σn PMc m m10 usp sp' f A lo d buf P0 bs bs0 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x0' x1' x2' r6 r7 s2x x3' x4' x5' x6' F10 fc10 h3 t p1 p17 p57
                       FDO MST INLV FRS0 LVB CR0 VCB LOW LOR SPT VL1 CR1 LVL1 LPX1 LVn FRSn' SPn' CRn B16 SMALL L0R EDL EDC SPR SPA' FPOS F64 FR1' FSEG2 FSELF SHB0 SHT
                       INV10 FP10 BUF10 FRM10 T c10c (conj ltac:(unfold sa_regs; subst S; exact Hc10c') (cfrm0_of_asta RT Σn PMc (eq _) c10c Hc10c' ltac:(intros ms0 <-; exact FRM10))) Hk).
Qed.
End Top2b.
