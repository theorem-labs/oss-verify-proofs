(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_h_dtor Sj_h_alloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition e_setmd : Z := 0xf5cb8.

Definition impl_cells2 (pre40 : list byte) (md : word) (p48 : list byte) (oc ia : word) (p72 : list byte) : list cell :=
  [CB 40 pre40; C8 md; CB 8 p48; C8 oc; C8 ia; CB 24 p72].

Definition sm_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sm_walk1 : forall (usp THIS md lo : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 64 -> 0x6e0000 <= lo -> usp < 2^63 -> 0 < THIS < 2^63 -> 0 <= md < 2^31 ->
  shb_consts m -> cli_got_nothrow m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xf5d10) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 md)
             (Z_to_bv 64 (8 * md)) (Z_to_bv 64 0x31890) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc e_newarr_nt m1
      /\ munch [(usp - 64, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -64)
      /\ rw_cells bsegs m1 (usp + -64) (sm_frame ra s0 s1 s2 s3 s4 s5 s6))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 md) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_setmd m).
Proof.
  intros until m. intros ST LO GLO SPH T0 M0 (G1 & G2) GN MI.
  unfold entry_st, e_setmd, e_newarr_nt, sm_frame, cli_got_nothrow in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  do 8 zstep. zstep. zstep.
  assert (SH : Z.shiftr md 31 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite SH. zstep. if_true.
  do 5 zstep.
  zstep. zstep. zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. replace (md * 8) with (8 * md) by lia.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma sm_walk2 : forall (THIS md oc sp' : Z) (pre40 p48 p72 : list byte) (md0 : word)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < THIS < 2^63 -> (THIS + 96 <= 0x10000 \/ 0x6e0000 <= THIS) -> 0 <= md < 2^31 -> 0 <= oc < 2^64 -> oc mod 16 = 0 ->
  shz m THIS 96 -> cli_got_nothrow m ->
  rw_cells bsegs m THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 0) (Z_to_bv 64 0) p72) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = entry_st (Z_to_bv 64 0xf5d54) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 md)
             (Z_to_bv 64 md) (Z_to_bv 64 0x31890) a2' a3 a4 a5 a6 a7 (Z_to_bv 64 (THIS + 56)) (Z_to_bv 64 (THIS + 64)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((THIS + 56) / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_newarr_nt m1
      /\ munch [(THIS, THIS + 96)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 oc) (Z_to_bv 64 0) p72))
    (MS (mkR (Z_to_bv 64 0xf5d10) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 md) (Z_to_bv 64 oc) a1 a2 a3 a4 a5 a6 a7
             s2x s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf5d10) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros T0 TX M0 OC OC16 SHZ GN TH MI.
  unfold entry_st, e_newarr_nt, impl_cells2, cli_got_nothrow in *.
  pose proof (munch_refl [(THIS, THIS + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHZ (THIS + 56) ltac:(lia)) as RD0.
  zstep. rewrite (land7_aligned oc) by (first [lia| exact OC16]). zstep. if_false.
  zstep.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; eassumption.
Qed.

Definition this_shz (W : list ivl) (m0 : mem) (THIS : Z) : Prop :=
  forall m' : mem, munch W m0 m' -> wmono bsegs m0 m' -> shz m' THIS 96.

Lemma sm_walk3 : forall (usp THIS md oc ia lo : Z) (pre40 p48 p72 : list byte) (md0 : word)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6x s7 s8 s9 s10 s11 t3 t4 t5 t6 rac s0c s1c s2c s3c s4c s5c s6c : word) F fc (m : mem),
  stk bsegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6e0000 <= lo -> usp < 2^63 ->
  0 < THIS -> THIS + 96 <= lo -> 0 <= md < 2^31 -> 0 < oc < 2^64 -> 0 < ia < 2^64 ->
  this_shz [(usp - 64, usp); (THIS, THIS + 96)] m THIS ->
  rw_cells bsegs m (usp + -64) (sm_frame rac s0c s1c s2c s3c s4c s5c s6c) ->
  rw_cells bsegs m THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 oc) (Z_to_bv 64 0) p72) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(usp - 64, usp); (THIS, THIS + 96)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' THIS (impl_cells2 pre40 (Z_to_bv 64 md) p48 (Z_to_bv 64 oc) (Z_to_bv 64 ia) p72))
    (MS (mkR (Z_to_bv 64 0xf5d54) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 md) (Z_to_bv 64 ia) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (THIS + 56)) (Z_to_bv 64 (THIS + 64)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((THIS + 56) / 8 + 2147450880)) s6x s7 s8 s9 s10 s11
             t3 t4 t5 t6) F (Z_to_bv 64 0xf5d54) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH T0 TLO M0 OC IA SHZ FR TH MI.
  unfold sm_frame, impl_cells2 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp); (THIS, THIS + 96)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EUI : bv_unsigned (Z_to_bv 64 ia) = ia) by (apply unsigned_lit; lia).
  assert (EUO : bv_unsigned (Z_to_bv 64 oc) = oc) by (apply unsigned_lit; lia).
  pose proof (SHZ m MU WM (THIS + 64) ltac:(lia)) as RD0.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. if_true.
  zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' (THIS + 56) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (THIS + 40) ltac:(lia)) as RD2 end.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  replace (Z.b2z (oc <? 1)) with 0 by (destruct (Z.ltb_spec oc 1); [lia| reflexivity]).
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  do 8 zstep. zstep.
  release_frame FR ST usp.
  zstep.
  assert (EL : Z.land 18446744073709551615 md = md) by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite EL in *.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.

Section SetmdCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition setmd_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (THIS md : Z) (md0 : word) (pre40 p48 p72 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 md -> tp = Z_to_bv 64 0x6be3e8 ->
  1 <= md <= 4096 ->
  In (THIS, 96) (rt_live RT Σ) -> THIS mod 8 = 0 ->
  rw_cells bsegs m THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 0) (Z_to_bv 64 0) p72) ->
  Z.of_nat (length (rt_live RT Σ)) + 2 <= LIVE_MAX -> mcost (8 * md) + mcost md <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 96 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_setmd m)))
    (fun c => exists (Σ' : rts RT) (oc ia : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(THIS, THIS + 96)] m m'
         /\ rw_cells bsegs m' THIS (impl_cells2 pre40 (Z_to_bv 64 md) p48 (Z_to_bv 64 oc) (Z_to_bv 64 ia) p72)
         /\ wr_at bsegs m' oc (8 * md) /\ wr_at bsegs m' ia md) c
       /\ rt_live RT Σ' = (ia, md) :: (oc, 8 * md) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (8 * md) - mcost md
       /\ 0 < oc /\ oc mod 16 = 0 /\ 0 < ia /\ ia mod 16 = 0).

Theorem setmd_ok : setmd_cps.
Proof using AF NEWA AFC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m THIS md md0 pre40 p48 p72 lo
    FDO MST -> -> -> MD INT T8 TH0 LVB CR0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_live_range RT AF Σ m THIS 96 ART0 INT) as (TP0 & TP1 & TPX).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FP1 : fp_client RT Σ lo [(usp - 64, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (FPT : forall Σx, In (THIS, 96) (rt_live RT Σx) -> fp_client RT Σx lo [(THIS, THIS + 96)]).
  { intros Σx Hin. constructor; [| constructor]. right; left. exists THIS, 96. cbn [fst snd]. split; [exact Hin| lia]. }
  assert (FPW : forall Σx, In (THIS, 96) (rt_live RT Σx) -> fp_client RT Σx lo [(usp - 64, usp); (THIS, THIS + 96)]).
  { intros Σx Hin. constructor; [left; cbn [fst snd]; ul|]. exact (FPT Σx Hin). }
  pose proof (sm_walk1 usp THIS md lo ra gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) (conj G1 G2) (AFC Σ m ART0) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  assert (TH1 : rw_cells bsegs m1 THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 0) (Z_to_bv 64 0) p72)).
  { apply (rw_cells_agree bsegs m m1 _ _ TH0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
    intros x Hx. unfold impl_cells2 in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -64) mod 16 = 0) by (replace (usp + -64) with (usp + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  apply (NEWA Σ PMc (Z_to_bv 64 0xf5d10) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 THIS) (Z_to_bv 64 md)
           (Z_to_bv 64 (8 * md)) (Z_to_bv 64 0x31890) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m1 (8 * md) lo FDO MST); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - lia.
  - lia.
  - pose proof (mcost_nonneg md ltac:(lia)). lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c2 ((Σ1 & oc & Hc2 & LV1 & FRS1 & SP1 & CR1 & OC0 & OC16 & OCTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRO & _) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xf5d10) in Hc2' by lia.
    assert (INT1 : In (THIS, 96) (rt_live RT Σ1)) by (rewrite LV1; right; exact INT).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (FR2 : rw_cells bsegs m2 (usp + -64) (sm_frame ra s0 s1 s2 s3 s4 s5 s6)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold sm_frame. pres_tac. }
    assert (TH2 : rw_cells bsegs m2 THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 0) (Z_to_bv 64 0) p72)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ TH1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold impl_cells2. pres_tac. }
    pose proof (sm_walk2 THIS md oc (usp + -64) pre40 p48 p72 md0 gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 F2 fc2 m2 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) OC16 (shz_live RT AF Σ1 m2 THIS 96 ART2 INT1 T8) (AFC Σ1 m2 ART2) TH2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a2' & -> & MU3 & WM3 & MI3 & TH3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 (FPT Σ1 INT1) MU3 WM3) as ART3.
    assert (AG23 : agree_on (fun x => ~ (THIS <= x < THIS + 96)) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
    assert (FR3 : rw_cells bsegs m3 (usp + -64) (sm_frame ra s0 s1 s2 s3 s4 s5 s6)).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. unfold sm_frame in Hx.
      cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
    assert (ST3 : stk bsegs m3 lo (usp + -64)).
    { apply (stk_agree bsegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
    apply (NEWA Σ1 PMc (Z_to_bv 64 0xf5d54) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 (Z_to_bv 64 THIS) (Z_to_bv 64 md)
             (Z_to_bv 64 md) (Z_to_bv 64 0x31890) a2' b3 b4 b5 b6 b7 (Z_to_bv 64 (THIS + 56)) (Z_to_bv 64 (THIS + 64)) (Z_to_bv 64 2147450880)
             (Z_to_bv 64 ((THIS + 56) / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m3 md lo FDO MST); try reflexivity; try assumption;
      [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + lia.
    + rewrite LV1. cbn [length]. lia.
    + rewrite CR1. lia.
    + rewrite EU2. exact ST3.
    + rewrite EU2. ul.
    + rewrite EU2. ul.
    + rewrite EU2. exact SPA2.
    + intros c4 ((Σ2 & ia & Hc4 & LV2 & FRS2 & SP2 & CR2 & IA0 & IA16 & IATOP) & FC4).
      destruct (ASTA_unpack_f RT Σ2 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & WRI & _) & FRM4 & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xf5d54) in Hc4' by lia.
      assert (INT2 : In (THIS, 96) (rt_live RT Σ2)) by (rewrite LV2; right; exact INT1).
      assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
      assert (FR4 : rw_cells bsegs m4 (usp + -64) (sm_frame ra s0 s1 s2 s3 s4 s5 s6)).
      { apply (rw_cells_agree bsegs m3 m4 _ _ FR3); [| exact WM4]. apply (agree_of_pres _ _ _ _ _ _ PRES4). unfold sm_frame. pres_tac. }
      assert (TH4 : rw_cells bsegs m4 THIS (impl_cells2 pre40 md0 p48 (Z_to_bv 64 oc) (Z_to_bv 64 0) p72)).
      { apply (rw_cells_agree bsegs m3 m4 _ _ TH3); [| exact WM4]. apply (agree_of_pres _ _ _ _ _ _ PRES4). unfold impl_cells2. pres_tac. }
      assert (SHZ4 : this_shz [(usp - 64, usp); (THIS, THIS + 96)] m4 THIS).
      { intros m' MU WM. exact (shz_live RT AF Σ2 m' THIS 96 (art_fp_client RT AF Σ2 m4 m' lo _ ART4 LOW2 (FPW Σ2 INT2) MU WM) INT2 T8). }
      pose proof (sm_walk3 usp THIS md oc ia lo pre40 p48 p72 md0 gp (Z_to_bv 64 0x6be3e8) w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6
                    ra s0 s1 s2 s3 s4 s5 s6 F4 fc4 m4 ST4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul) SHZ4 FR4 TH4 MI4) as W3.
      lazymatch type of W3 with evt bsegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ2 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ2 PMc _ c5 Hc5); intros ms (m5 & _ & E5 & _); rewrite E5; exact FRM4].
      exists Σ2, oc, ia.
      split; [| split; [rewrite LV2, LV1; reflexivity| split; [rewrite FRS2; exact FRS1| split; [rewrite SP2; exact SP1|
                  split; [rewrite CR2, CR1; lia| repeat split; assumption]]]]].
      eapply ASTA_conseq; [exact Hc5|]. intros ms (m5 & RS5 & _ & MU5 & WM5 & MI5 & ST5 & TH5). exists m5.
      split; [rewrite ESP; exact RS5|].
      split; [split; [exact (art_fp_client RT AF Σ2 m4 m5 lo _ ART4 LOW2 (FPW Σ2 INT2) MU5 WM5)| split; [exact MI5| split; [| exact ST5]]]|].
      { exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 WM5)))). }
      split; [| split; [exact TH5| split; [exact (wr_at_transport bsegs _ _ _ _ (wr_at_transport bsegs _ _ _ _ (wr_at_transport bsegs m2 m3 _ _ WRO WM3) WM4) WM5)|
                                             exact (wr_at_transport bsegs m4 m5 _ _ WRI WM5)]]].
      intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -64) (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; right; exact He| rewrite FRS1; auto| lia]. }
      rewrite (MU5 a), (PRES4 a Ha1), (MU3 a), (PRES2 a), (MU1 a); [reflexivity| | | |].
      * cbn [outside]. split; [ul| exact I].
      * apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
      * cbn [outside]. split; [exact HO| exact I].
      * cbn [outside]. split; [ul|]. split; [exact HO| exact I].
Qed.

End SetmdCPS.
