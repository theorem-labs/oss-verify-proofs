(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintTally.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma prev_st_eq2 s : prev_st s = set_match_length (set_prev_length (set_prev_match s (ds_match_start s)) (ds_match_length s)) 2.
Proof. destruct s; reflexivity. Qed.

Lemma prev_st_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms ms (prev_st s1) (prev_st s2).
Proof.
  intros R. rewrite !prev_st_eq2. rewrite (rel_match_length _ _ _ _ _ _ _ _ R).
  eapply rel_set_match_length; [|unfold MIN_MATCH; lia].
  eapply rel_set_prev_length; [|dsr; exact (r_g1 _ _ _ _ _ _ _ _ R)].
  eapply rel_set_prev_match; [exact R|exact (r_ms _ _ _ _ _ _ _ _ R)| |auto].
  intros Hp. exact (r_g3 _ _ _ _ _ _ _ _ R (r_g2 _ _ _ _ _ _ _ _ R Hp)).
Qed.
Lemma INV_prev_st s : INV s -> INV (prev_st s).
Proof. intros I. pose proof (iv_ml s I). rewrite prev_st_eq2. apply INV_set_match_length; [lia|]. apply INV_set_prev_length; [dsr; lia|]. apply INV_set_prev_match. exact I. Qed.
Lemma prev_st_frame s : lz5 (prev_st s) = lz5 s /\ fwk (prev_st s) = fwk s /\ ds_prev_length (prev_st s) = ds_match_length s
  /\ ds_match_length (prev_st s) = 2 /\ ds_match_available (prev_st s) = ds_match_available s /\ ds_insert (prev_st s) = ds_insert s
  /\ ds_window (prev_st s) = ds_window s.
Proof. unfold prev_st. dsr. repeat split; reflexivity. Qed.

Lemma HFREL_prev_st s1 s2 hh : HFREL s1 s2 hh -> HFREL (prev_st s1) (prev_st s2) hh.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH & Hcv). exists W, C, B, bnd, ms, ms.
  split; [eapply prev_st_rel; exact R|]. unfold prev_st, WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact Hcv.
Qed.

Lemma st_lm_rel s1 s2 hh :
  HFREL s1 s2 hh -> INV s1 -> INV s2 -> ds_level s1 <> 0 -> 1 <= ds_lookahead s1 ->
  ds_strstart s1 + MIN_LOOKAHEAD <= 65536 -> 1 <= ds_prev_length s1 ->
  FREL (st_lm s1 hh) (st_lm s2 hh)
  /\ INV (st_lm s1 hh) /\ INV (st_lm s2 hh)
  /\ lz5 (st_lm s1 hh) = lz5 s1 /\ fwk (st_lm s1 hh) = fwk s1.
Proof.
  intros HF I1 I2 Hlv Hlk Hss Hpl. pose proof HF as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH & Hcv).
  pose proof (iv_ss s1 I1). pose proof (iv_sl s1 I1).
  unfold st_lm, sl_lm_cond. rel_fields R. unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hss.
  match goal with |- context [if ?c then _ else s1] => destruct c eqn:Ec end.
  2:{ split; [exists W, C, B, bnd, ms, pm; repeat (split; [assumption|]); exact HH|].
      split; [exact I1|]. split; [exact I2|]. split; reflexivity. }
  apply andb_prop in Ec. destruct Ec as [Ec _]. apply andb_prop in Ec. destruct Ec as [Ec _].
  destruct (Z.eqb_spec hh 0) as [|Hh0]; [discriminate Ec|].
  assert (HW2 : forall i, 0 <= i <= ds_strstart s1 + 258 -> W i).
  { intros i Hi. apply HW. unfold WHI. eapply HWI4_use; [exact HH|exact Hlv|lia|lia|lia]. }
  pose proof (longest_match_rel _ _ _ _ _ _ _ _ hh R I1 I2 HW2 ltac:(lia) Hb (Hcv Hh0) Hh0 Hpl) as LM.
  cbv zeta in LM. destruct LM as (Er & ms' & Hms & R' & J1 & J2 & L5 & CL & Hrng & Hg & Hle).
  rewrite <- Er.
  set (t1 := fst (longest_match s1 hh)) in *. set (t2 := fst (longest_match s2 hh)) in *. set (ml := snd (longest_match s1 hh)) in *.
  clearbody t1 t2 ml.
  pose proof (lz5_eq _ _ L5) as (Ess & Elk & Ehw & Elv & Ebs). pose proof (fwk_of_clean _ _ CL) as FK.
  pose proof (rel_set_match_length _ _ _ _ _ _ _ _ ml R' Hg) as R2.

  assert (EF : sl_filter (set_match_length t2 ml) = sl_filter (set_match_length t1 ml)).
  { unfold sl_filter. dsr. rel_fields R'.
    destruct (Z.eqb_spec ml 3) as [M3|M3]; cbn [andb]; [|reflexivity].
    rewrite (r_ms _ _ _ _ _ _ _ _ R' ltac:(apply Hg; unfold MIN_MATCH; lia)). reflexivity. }
  rewrite EF.
  assert (K1 : INV (set_match_length t1 ml)) by (apply INV_set_match_length; [lia|exact J1]).
  assert (K2 : INV (set_match_length t2 ml)) by (apply INV_set_match_length; [lia|exact J2]).
  destruct (sl_filter (set_match_length t1 ml)).
  - pose proof (rel_set_match_length _ _ _ _ _ _ _ _ 2 R2 ltac:(unfold MIN_MATCH; lia)) as R3.
    split.
    { exists W, C, B, bnd, ms', pm. split; [exact R3|]. unfold WHI, PBC, SYMB, HWI in *. dsr. rewrite Ess, Elk, Ehw, Elv.
      pose proof (fwk_fields _ _ FK) as (F1 & F2 & F3 & F4 & F5 & F6). rewrite F1, F2, F3, F4, F5.
      repeat (split; [assumption|]). exact HH. }
    split; [apply INV_set_match_length; [lia|exact K1]|]. split; [apply INV_set_match_length; [lia|exact K2]|].
    dsr. split; [exact L5|exact FK].
  - split.
    { exists W, C, B, bnd, ms', pm. split; [exact R2|]. unfold WHI, PBC, SYMB, HWI in *. dsr. rewrite Ess, Elk, Ehw, Elv.
      pose proof (fwk_fields _ _ FK) as (F1 & F2 & F3 & F4 & F5 & F6). rewrite F1, F2, F3, F4, F5.
      repeat (split; [assumption|]). exact HH. }
    split; [exact K1|]. split; [exact K2|].
    dsr. split; [exact L5|exact FK].
Qed.

Lemma deflate_slow_insert_rel f : forall W C B bnd ms pm s1 s2 mi,
  REL W C B bnd ms pm s1 s2 -> INV s1 -> INV s2 ->
  bnd <= ds_strstart s1 -> pm = true ->
  (forall i, 0 <= i <= mi + 2 -> W i) -> 0 <= mi -> mi + 2 <= ds_strstart s1 + ds_prev_length s1 + ds_lookahead s1 ->
  ds_strstart s1 + ds_prev_length s1 + ds_lookahead s1 + 1 <= 65536 ->
  1 <= ds_prev_length s1 <= Z.of_nat f ->
  let t1 := deflate_slow_insert f s1 mi in let t2 := deflate_slow_insert f s2 mi in
  exists C', (forall p, C p -> C' p)
    /\ REL W C' B (ds_strstart t1) ms pm t1 t2
    /\ INV t1 /\ INV t2
    /\ ds_strstart t1 = ds_strstart s1 + ds_prev_length s1 /\ ds_prev_length t1 = 0
    /\ fwk t1 = fwk s1 /\ ds_lookahead t1 = ds_lookahead s1 /\ ds_high_water t1 = ds_high_water s1 /\ ds_block_start t1 = ds_block_start s1
    /\ ds_match_length t1 = ds_match_length s1 /\ ds_match_available t1 = ds_match_available s1.
Proof.
  induction f as [|f IH]; intros W C B bnd ms pm s1 s2 mi R I1 I2 Hb Hpm HW Hmi Hmi2 Hsl Hpl; [cbn in Hpl; lia|].
  rewrite !slow_insert_step. rel_fields R.
  pose proof (iv_ss s1 I1). pose proof (iv_ins s1 I1). pose proof (iv_look s1 I1). pose proof (iv_pvl s1 I1).
  pose proof (rel_set_strstart _ _ _ _ _ _ _ _ (ds_strstart s1 + 1) R) as R1.
  pose proof (INV_set_strstart s1 (ds_strstart s1 + 1) ltac:(lia) ltac:(lia) ltac:(lia) I1) as I11.
  pose proof (INV_set_strstart s2 (ds_strstart s1 + 1) ltac:(lia) ltac:(rel_fields R; lia) ltac:(rel_fields R; lia) I2) as I21.
  pose proof (rel_bnd_up _ _ _ bnd (ds_strstart s1 + 1) _ _ _ _ R1 ltac:(lia)) as R1'.
  dsr.

  assert (STEP : exists C' u1 u2, (forall p, C p -> C' p)
            /\ (if ds_strstart s1 + 1 <=? mi then fst (insert_string (set_strstart s1 (ds_strstart s1 + 1)) (ds_strstart s1 + 1)) else set_strstart s1 (ds_strstart s1 + 1)) = u1
            /\ (if ds_strstart s1 + 1 <=? mi then fst (insert_string (set_strstart s2 (ds_strstart s1 + 1)) (ds_strstart s1 + 1)) else set_strstart s2 (ds_strstart s1 + 1)) = u2
            /\ REL W C' B (ds_strstart s1 + 1) ms pm u1 u2 /\ INV u1 /\ INV u2
            /\ ds_strstart u1 = ds_strstart s1 + 1 /\ ds_prev_length u1 = ds_prev_length s1 /\ ds_lookahead u1 = ds_lookahead s1
            /\ fwk u1 = fwk s1 /\ ds_high_water u1 = ds_high_water s1 /\ ds_block_start u1 = ds_block_start s1
            /\ ds_match_length u1 = ds_match_length s1 /\ ds_match_available u1 = ds_match_available s1).
  { destruct (Z.leb_spec (ds_strstart s1 + 1) mi).
    - pose proof (insert_string_rel _ _ _ _ _ _ _ _ (ds_strstart s1 + 1) R1' I11 I21 ltac:(lia) ltac:(lia) ltac:(apply HW; lia) ltac:(lia)) as (Eh & R2 & _).
      eexists _, _, _. split; [|split; [reflexivity|]; split; [reflexivity|]; split; [exact R2|]].
      + intros p Cp. left. exact Cp.
      + split; [apply INV_insert_string; exact I11|]. split; [apply INV_insert_string; exact I21|]. unfold insert_string. dsr. repeat split; reflexivity.
    - exists C, (set_strstart s1 (ds_strstart s1 + 1)), (set_strstart s2 (ds_strstart s1 + 1)).
      split; [auto|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact R1'|]. split; [exact I11|]. split; [exact I21|]. dsr. repeat split; reflexivity. }
  destruct STEP as (C1 & u1 & u2 & HC1 & E1 & E2 & R2 & J1 & J2 & Ess & Epl & Elk & Efw & Ehw & Ebs & Eml & Ema).
  rewrite E1, E2. clear E1 E2.
  pose proof (rel_set_prev_length _ _ _ _ _ _ _ _ (ds_prev_length u1 - 1) R2 ltac:(intros _; exact Hpm)) as R3.
  pose proof (INV_set_prev_length u1 (ds_prev_length u1 - 1) ltac:(lia) J1) as K1.
  pose proof (INV_set_prev_length u2 (ds_prev_length u1 - 1) ltac:(lia) J2) as K2.
  rel_fields R2. dsr. rewrite Epl.
  destruct (Z.eqb_spec (ds_prev_length s1 - 1) 0) as [Z0|Z0]; cbn [negb].
  - exists C1. split; [exact HC1|]. dsr. rewrite Ess.
    split; [rewrite <- Epl; exact R3|]. split; [rewrite <- Epl; exact K1|]. split; [rewrite <- Epl; exact K2|].
    rewrite Elk, Ehw, Ebs, Eml, Ema. repeat split; try lia. unfold fwk in *. dsr. exact Efw.
  - destruct (IH _ _ _ _ _ _ _ _ mi R3 K1 K2 ltac:(dsr; lia) Hpm HW Hmi ltac:(dsr; lia) ltac:(dsr; lia) ltac:(dsr; lia))
      as (C' & HC' & R4 & L1 & L2 & Ess' & Epl' & Efw' & Elk' & Ehw' & Ebs' & Eml' & Ema').
    cbv zeta. rewrite <- Epl. exists C'. split; [intros p Cp; apply HC', HC1, Cp|].
    split; [exact R4|]. split; [exact L1|]. split; [exact L2|].
    revert Ess' Epl' Efw' Elk' Ehw' Ebs' Eml' Ema'. dsr. rewrite Ess, Epl, Elk, Ehw, Ebs, Eml, Ema. unfold fwk in *. dsr. rewrite Efw. intros. repeat split; try assumption; lia.
Qed.

Lemma swap_look_ss s a b : set_lookahead (set_strstart s a) b = set_strstart (set_lookahead s b) a.
Proof. destruct s; reflexivity. Qed.

Section SDist.
  Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
  Hypothesis R : REL W C B bnd ms pm s1 s2.
  Hypothesis I1 : INV s1.
Hypothesis I2 : INV s2.
  Hypothesis HW : forall i, i < WHI s1 -> W i.
  Hypothesis Hb : bnd <= ds_strstart s1.
  Hypothesis HP : PBC B s1.
  Hypothesis HS : SYMB B s1.
  Hypothesis HH : HWI s1.
  Hypothesis Hlv : ds_level s1 <> 0.
  Hypothesis Hsn : 0 <= ds_sym_next s1.

  Lemma st_sdist_rel :
    dist_cond s1 = true -> ds_prev_length s1 - 1 <= ds_lookahead s1 -> 1 <= ds_strstart s1 ->
    snd (st_sdist s1) = snd (st_sdist s2)
    /\ FREL (fst (st_sdist s1)) (fst (st_sdist s2)) /\ INV (fst (st_sdist s1)) /\ INV (fst (st_sdist s2)).
  Proof.
    intros Hdc Hpll Hss1.
    pose proof (iv_ss s1 I1). pose proof (iv_sl s1 I1). pose proof (iv_wl s1 I1). pose proof (iv_ins s1 I1). pose proof (iv_look s1 I1). pose proof (iv_pvl s1 I1). pose proof (iv_ml s1 I1).
    unfold dist_cond in Hdc. apply andb_prop in Hdc. destruct Hdc as [Hdc1 Hdc2]. apply Z.leb_le in Hdc1. apply Z.leb_le in Hdc2.
    pose proof (r_g2 _ _ _ _ _ _ _ _ R ltac:(unfold MIN_MATCH; lia)) as Hpm.
    unfold st_sdist. rel_fields R.
    rewrite <- (r_pm _ _ _ _ _ _ _ _ R Hpm).
    set (d := wrap32 (ds_strstart s1 - 1 - ds_prev_match s1)). set (l := ds_prev_length s1 - 3).
    set (mi := wrap32 (ds_strstart s1 + ds_lookahead s1 - 3)).
    assert (Hmi : mi = ds_strstart s1 + ds_lookahead s1 - 3) by (subst mi; apply wrap32_id; lia).
    pose proof (tr_tally_dist_rel _ _ _ _ _ _ _ _ d l R I1 I2) as [Eb R1].
    pose proof (INV_tr_tally_dist s1 d l I1) as J1. pose proof (INV_tr_tally_dist s2 d l I2) as J2.
    pose proof (tr_tally_dist_shape s1 d l) as [Sh1 Sb1]. pose proof (tr_tally_dist_shape s2 d l) as [Sh2 Sb2].
    destruct (tr_tally_dist s1 d l) as [t1 b1]. destruct (tr_tally_dist s2 d l) as [t2 b2]. cbn [fst snd] in *. subst t1 t2 b1 b2.
    split; [rel_fields R; reflexivity|].
    set (B' := Bx B _ _) in R1.

    dsr. rel_fields R. rewrite (wrap32_id (ds_lookahead s1 - (ds_prev_length s1 - 1))) by lia.
    pose proof (rel_set_lookahead _ _ _ _ _ _ _ _ (ds_lookahead s1 - (ds_prev_length s1 - 1)) R1) as R2.
    pose proof (rel_set_prev_length _ _ _ _ _ _ _ _ (ds_prev_length s1 - 2) R2 ltac:(intros _; exact Hpm)) as R3.
    match type of R1 with REL _ _ _ _ _ _ ?x _ =>
      pose proof (INV_set_lookahead x (ds_lookahead s1 - (ds_prev_length s1 - 1)) ltac:(lia) ltac:(dsr; lia) J1) as K1 end.
    match type of R3 with REL _ _ _ _ _ _ ?x ?y => set (u1 := x) in *; set (u2 := y) in * end.
    assert (K1' : INV u1) by (subst u1; apply INV_set_prev_length; [dsr; lia|exact K1]).
    assert (K2' : INV u2).
    { subst u2. pose proof (rel_strstart _ _ _ _ _ _ _ _ R). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R). pose proof (rel_prev_length _ _ _ _ _ _ _ _ R).
      apply INV_set_prev_length; [dsr; lia|]. apply INV_set_lookahead; dsr; try lia. exact J2. }

    pose proof (deflate_slow_insert_rel (Z.to_nat (ds_prev_length u1)) _ _ _ _ _ _ _ _ mi R3 K1' K2') as IR.
    subst u1 u2. revert IR. dsr. intros IR.
    specialize (IR ltac:(lia) Hpm ltac:(rewrite Hmi; intros i Hi; apply HW; unfold WHI; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id; lia)).
    destruct IR as (C' & HC' & R4 & L1 & L2 & Ess & Epl & Efw & Elk & Ehw & Ebs & Eml & Ema).
    revert R4 L1 L2 Ess Epl Efw Elk Ehw Ebs Eml Ema. rel_fields R.
    set (v1 := deflate_slow_insert _ _ mi). set (v2 := deflate_slow_insert _ _ mi). clearbody v1 v2. intros.
    pose proof (fwk_fields _ _ Efw) as (Fp & Fpo & Fsn & Flb & Fao & Flv). revert Fp Fpo Fsn Flb Fao Flv. dsr. intros.
    split; [|split].
    - exists W, C', B', (ds_strstart v1), ms, pm.
      split; [rewrite (rel_strstart _ _ _ _ _ _ _ _ R4); apply rel_set_strstart; apply rel_set_match_length; [apply rel_set_match_available; exact R4|unfold MIN_MATCH; lia]|].
      unfold WHI, PBC, SYMB, HWI, B', Bx in *. dsr. rewrite Ess, Elk, Ehw, Fp, Fpo, Fsn, Flb, Fao, Flv.
      split; [intros i Hi; apply HW; lia|]. split; [lia|].
      split; [destruct HP as [[P1 P2]|[P1 P2]]; [left|right]; split; auto|].
      split; [intros i Hi; destruct (Z_lt_le_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; apply HS; lia|right; lia]|].
      eapply HWI4_shift; [exact HH|lia|lia|lia].
    - apply INV_set_strstart; dsr; rewrite ?Ess, ?Elk; try lia; [pose proof (iv_ins v1 L1); lia|].
      apply INV_set_match_length; [lia|]. apply INV_set_match_available. exact L1.
    - pose proof (iv_ins v2 L2). pose proof (rel_strstart _ _ _ _ _ _ _ _ R4). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R4). pose proof (rel_insert _ _ _ _ _ _ _ _ R4).
      apply INV_set_strstart; dsr; try lia. apply INV_set_match_length; [lia|]. apply INV_set_match_available. exact L2.
  Qed.
End SDist.

Section SLit.
  Hypothesis HFB : FB_CALL.
  Hypothesis HFBR : FLUSH_BLOCK_REL.
  Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
  Hypothesis R : REL W C B bnd ms pm s1 s2.
  Hypothesis I1 : INV s1.
Hypothesis I2 : INV s2.
  Hypothesis HW : forall i, i < WHI s1 -> W i.
  Hypothesis Hb : bnd <= ds_strstart s1.
  Hypothesis HP : PBC B s1.
  Hypothesis HS : SYMB B s1.
  Hypothesis HH : HWI s1.
  Hypothesis Hsn : 0 <= ds_sym_next s1.
  Hypothesis Hlk : 1 <= ds_lookahead s1.

  Lemma st_slit_rel :
    1 <= ds_strstart s1 ->
    let c := arr_get (ds_window s1) (ds_strstart s1 - 1) in
    fb_entry (fst (tr_tally_lit s1 c)) 0 -> fb_entry (fst (tr_tally_lit s2 c)) 0 ->
    snd (st_slit s1) = snd (st_slit s2)
    /\ FREL (fst (st_slit s1)) (fst (st_slit s2)) /\ INV (fst (st_slit s1)) /\ INV (fst (st_slit s2)).
  Proof.
    intros Hss1 c FE1 FE2.
    pose proof (iv_ss s1 I1). pose proof (iv_sl s1 I1). pose proof (iv_wl s1 I1). pose proof (iv_ins s1 I1). pose proof (iv_look s1 I1).
    unfold st_slit.
    assert (EW : arr_get (ds_window s2) (ds_strstart s1 - 1) = c).
    { subst c. symmetry. apply (aeq_get _ _ _ _ (r_win _ _ _ _ _ _ _ _ R)); [lia|apply HW; unfold WHI; lia]. }
    rel_fields R. rewrite EW. fold c.
    pose proof (tr_tally_lit_rel _ _ _ _ _ _ _ _ c R I1 I2) as [Eb R1].
    pose proof (INV_tr_tally_lit s1 c I1) as J1. pose proof (INV_tr_tally_lit s2 c I2) as J2.
    pose proof (tr_tally_lit_shape s1 c) as [Sh1 Sb1]. pose proof (tr_tally_lit_shape s2 c) as [Sh2 Sb2].
    revert FE1 FE2.
    destruct (tr_tally_lit s1 c) as [t1 b1]. destruct (tr_tally_lit s2 c) as [t2 b2]. cbn [fst snd] in *. subst b1 b2. intros FE1 FE2.
    rel_fields R.
    set (B' := Bx B _ _) in R1.
    assert (FRt : FREL t1 t2).
    { exists W, C, B', bnd, ms, pm. split; [exact R1|]. subst t1 t2 B'. unfold WHI, PBC, SYMB, HWI, Bx in *. dsr.
      split; [exact HW|]. split; [exact Hb|].
      split; [destruct HP as [[P1 P2]|[P1 P2]]; [left|right]; split; auto|].
      split; [intros i Hi; destruct (Z_lt_le_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; apply HS; lia|right; lia]|].
      exact HH. }
    assert (Lt : lzm t1 = lzm s1) by (subst t1; reflexivity).

    assert (MID : forall u1 u2, FREL u1 u2 -> INV u1 -> INV u2 -> lzm u1 = lzm (set_block_start s1 (ds_block_start u1)) ->
      let v1 := set_lookahead (set_strstart u1 (ds_strstart u1 + 1)) (ds_lookahead u1 - 1) in
      let v2 := set_lookahead (set_strstart u2 (ds_strstart u2 + 1)) (ds_lookahead u2 - 1) in
      (if cs_avail_out (ds_strm v1) =? 0 then LRet need_more else LCont) = (if cs_avail_out (ds_strm v2) =? 0 then LRet need_more else LCont)
      /\ FREL v1 v2 /\ INV v1 /\ INV v2).
    { intros u1 u2 FRu K1 K2 Lu. cbv zeta. pose proof FRu as (W' & C' & B'' & bnd' & ms' & pm' & Ru & HWu & Hbu & HPu & HSu & HHu).
      rel_fields Ru. dsr. rel_fields Ru. split; [reflexivity|].
      pose proof (iv_ins u1 K1). pose proof (iv_ins u2 K2). pose proof (iv_sl u2 K2).
      pose proof (rel_strstart _ _ _ _ _ _ _ _ Ru). pose proof (rel_lookahead _ _ _ _ _ _ _ _ Ru). pose proof (rel_insert _ _ _ _ _ _ _ _ Ru).
      unfold FREL, WHI, PBC, SYMB, HWI in *. dsr. lzm_rw Lu.
      split.
      - exists W', C', B'', bnd', ms', pm'. split; [apply rel_set_lookahead, rel_set_strstart; exact Ru|].
        split; [intros i Hi; apply HWu; lia|]. split; [lia|]. split; [exact HPu|]. split; [exact HSu|].
        eapply HWI4_shift; [exact HHu|lia|lia|lia].
      - split.
        + rewrite swap_look_ss. apply INV_set_strstart; dsr; try lia. apply INV_set_lookahead; dsr; try lia. exact K1.
        + rewrite swap_look_ss. apply INV_set_strstart; dsr; try lia. apply INV_set_lookahead; dsr; try lia. exact K2. }
    destruct (ds_sym_next s1 + 1 + 1 + 1 =? ds_sym_end s1).
    - pose proof (fe_diff _ _ FE1).
      pose proof (flush_block_only_rel HFB HFBR t1 t2 0 FRt J1 J2 FE1 FE2 ltac:(lia)) as (FRf & L1 & L2 & Lf & _).
      apply (MID _ _ FRf L1 L2).
      pose proof (lzm_fields _ _ Lf) as G.

      remember (flush_block_only t1 0) as u1 eqn:Eu1.
      lzm_rw Lt.
      repeat match type of G with _ /\ _ => let G1 := fresh in destruct G as [G1 G]; rewrite ?G1 in * end. rewrite ?G in *. reflexivity.
    - apply (MID _ _ FRt J1 J2). lzm_rw Lt. reflexivity.
  Qed.

  Lemma st_avail_rel :
    snd (st_avail s1) = snd (st_avail s2)
    /\ FREL (fst (st_avail s1)) (fst (st_avail s2)) /\ INV (fst (st_avail s1)) /\ INV (fst (st_avail s2)).
  Proof.
    pose proof (iv_ss s1 I1). pose proof (iv_sl s1 I1). pose proof (iv_ins s1 I1). pose proof (iv_look s1 I1).
    unfold st_avail. cbn [fst snd]. split; [reflexivity|]. rel_fields R.
    split.
    - exists W, C, B, bnd, ms, pm. split; [apply rel_set_lookahead, rel_set_strstart, rel_set_match_available; exact R|].
      unfold WHI, PBC, SYMB, HWI in *. dsr.
      split; [intros i Hi; apply HW; lia|]. split; [lia|]. split; [exact HP|]. split; [exact HS|].
      eapply HWI4_shift; [exact HH|lia|lia|lia].
    - split.
      + rewrite swap_look_ss. apply INV_set_strstart; dsr; try lia. apply INV_set_lookahead; dsr; try lia. apply INV_set_match_available. exact I1.
      + rewrite swap_look_ss. pose proof (iv_ins s2 I2). pose proof (iv_sl s2 I2).
        pose proof (rel_strstart _ _ _ _ _ _ _ _ R). pose proof (rel_lookahead _ _ _ _ _ _ _ _ R). pose proof (rel_insert _ _ _ _ _ _ _ _ R).
        apply INV_set_strstart; dsr; try lia. apply INV_set_lookahead; dsr; try lia. apply INV_set_match_available. exact I2.
  Qed.
End SLit.

Section SlowRel.
  Variable c0 : cstrm.
Variable s01 : deflate_state.
Variable s02 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Hypothesis HFBR : FLUSH_BLOCK_REL.

  Lemma dmode4_level s : dmode s = 4 -> ds_level s <> 0.
  Proof. unfold dmode. destruct (Z.eqb_spec (ds_level s) 0); [intros X; discriminate X|intros _; assumption]. Qed.

  Lemma slow_step_rel s1 s2 :
    STI c0 s01 s1 -> STI c0 s02 s2 -> FREL s1 s2 -> INV s1 -> INV s2 ->
    snd (st_sbody s1 flush) = snd (st_sbody s2 flush)
    /\ FREL (fst (st_sbody s1 flush)) (fst (st_sbody s2 flush))
    /\ INV (fst (st_sbody s1 flush)) /\ INV (fst (st_sbody s2 flush)).
  Proof.
    intros F1 F2 FR I1 I2.
    pose proof F1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1). pose proof F2 as (HDC2 & HK2 & Hp2 & Hm2 & Hst2 & Ho2).
    pose proof (dmode4_level _ Hm1) as Hlv.
    unfold st_sbody.

    pose proof (st_fill_rel s1 s2 flush FR I1 I2 Hlv) as (Ee & FRa & Ia1 & Ia2 & _).
    pose proof (sfill_stage c0 s01 flush HC0 s1 F1) as FS1. cbv zeta in FS1. destruct FS1 as (Fa1 & _ & _ & _ & _ & Ews1 & Hnone1 & _ & _ & Hss1 & _).
    pose proof (sfill_stage c0 s02 flush HC0 s2 F2) as FS2. cbv zeta in FS2. destruct FS2 as (Fa2 & _ & _ & _ & _ & Ews2 & Hnone2 & _).
    rewrite (iv_wsize s1 I1) in Hss1.
    rewrite <- Ee in Hnone2 |- *.
    set (a1 := fst (st_fill s1 flush)) in *. set (a2 := fst (st_fill s2 flush)) in *.
    destruct (snd (st_fill s1 flush)) as [o|]; clearbody a1 a2.
    { cbn [fst snd]. split; [reflexivity|]. split; [exact FRa|]. split; [exact Ia1|exact Ia2]. }
    pose proof (Hnone1 eq_refl) as Hlk1. pose proof (Hnone2 eq_refl) as Hlk2.
    pose proof (STI_facts _ _ _ Fa1) as (Da1 & Xa1 & Va1 & _ & _ & _ & _ & Hml1 & Hpl1 & Hn1 & Hsn1 & _).
    assert (Hlva : ds_level a1 <> 0) by (apply dmode4_level; exact (proj1 (proj2 (proj2 (proj2 Fa1))))).
    unfold st_srest.

    pose proof (st_hash_rel a1 a2 FRa Ia1 Ia2) as (Eh & HFR & Ib1 & Ib2 & L5b & Kb & CLb).
    pose proof (shash_stage c0 s01 a1 Fa1 Hlk1) as HS1. cbv zeta in HS1. destruct HS1 as [HR1 Hlm1].
    pose proof (shash_stage c0 s02 a2 Fa2 Hlk2) as HS2. cbv zeta in HS2. destruct HS2 as [HR2 Hlm2].
    rewrite <- Eh in Hlm2 |- *.
    set (b1 := fst (st_hash a1)) in *. set (b2 := fst (st_hash a2)) in *. set (hh := snd (st_hash a1)) in *. clearbody b1 b2 hh.
    pose proof (lz5_eq _ _ L5b) as (Ess_b & Elk_b & Ehw_b & Elv_b & Ebs_b).
    assert (Eml_b : ds_match_length b1 = ds_match_length a1) by (apply (f_equal ds_match_length) in CLb; exact CLb).

    pose proof (HFREL_prev_st _ _ _ HFR) as HFRp. pose proof (INV_prev_st _ Ib1) as Ip1. pose proof (INV_prev_st _ Ib2) as Ip2.
    pose proof (prev_st_frame b1) as (L5p & Kp & Eplp & Emlp & _).
    pose proof (lz5_eq _ _ L5p) as (Ess_p & Elk_p & Ehw_p & Elv_p & Ebs_p).
    pose proof (st_lm_rel (prev_st b1) (prev_st b2) hh HFRp Ip1 Ip2 ltac:(rewrite Elv_p, Elv_b; exact Hlva) ltac:(rewrite Elk_p, Elk_b; exact Hlk1)
                  ltac:(rewrite Ess_p, Ess_b; exact Hss1) ltac:(rewrite Eplp, Eml_b; lia)) as (FRc & Ic1 & Ic2 & L5c & Kc).
    pose proof (slm_stage c0 s01 a1 b1 hh Fa1 Hlk1 ltac:(rewrite Ews1, (iv_wsize s1 I1); exact Hss1) HR1 Hlm1) as LM1. cbv zeta in LM1. destruct LM1 as [MR1 _].
    pose proof (slm_stage c0 s02 a2 b2 hh Fa2 Hlk2 ltac:(rewrite Ews2, (iv_wsize s2 I2); rewrite <- (clean_eq_fieldT ds_strstart _ _ (FREL_clean _ _ FRa) ltac:(reflexivity)); exact Hss1) HR2 Hlm2) as LM2.
    cbv zeta in LM2. destruct LM2 as [MR2 _]. clear Hlm1 Hlm2.
    set (d1 := st_lm (prev_st b1) hh) in *. set (d2 := st_lm (prev_st b2) hh) in *. clearbody d1 d2.
    pose proof (lz5_eq _ _ L5c) as (Ess_c & Elk_c & Ehw_c & Elv_c & Ebs_c).
    pose proof MR1 as (_ & Estr4 & Elook4 & Esn4 & _ & _ & _ & _ & _ & _ & Epl4 & Epm4 & Ema4 & Hml4 & Hms4 & Hlz4).
    pose proof (fwk_fields _ _ Kc) as (_ & _ & Esn_c & _). pose proof (fwk_fields _ _ Kp) as (_ & _ & Esn_p & _). pose proof (fwk_fields _ _ Kb) as (_ & _ & Esn_b & _).
    pose proof FRc as (W & C & B & bnd & ms & pm & Rc & HWc & Hbc & HPc & HSc & HHc).
    assert (Hsnc : 0 <= ds_sym_next d1) by (rewrite Esn_c, Esn_p, Esn_b; lia).

    unfold st_decide. rel_fields Rc.
    replace (dist_cond d2) with (dist_cond d1) by (unfold dist_cond; rel_fields Rc; reflexivity).
    destruct (dist_cond d1) eqn:Edc.
    -
      pose proof (sdist_stage c0 s01 a1 b1 d1 Fa1 Hlk1 HR1 MR1 Edc) as SD1. cbv zeta in SD1. destruct SD1 as (SDR1 & _ & Hml3 & Hmll & Hss1' & _).
      pose proof (sdist_stage c0 s02 a2 b2 d2 Fa2 Hlk2 HR2 MR2 ltac:(unfold dist_cond in Edc |- *; rel_fields Rc; exact Edc)) as SD2. cbv zeta in SD2. destruct SD2 as (SDR2 & _ & Hml3' & Hmll' & _ & _).
      pose proof (st_sdist_rel W C B bnd ms pm d1 d2 Rc Ic1 Ic2 HWc Hbc HPc HSc HHc Edc
                    ltac:(rewrite Epl4, Elk_c, Elk_p, Elk_b; exact Hmll) ltac:(rewrite Ess_c, Ess_p, Ess_b; exact Hss1')) as (Eb & FRe & Ie1 & Ie2).
      pose proof (send_facts c0 s01 HC0 a1 _ _ _ Fa1 (sdist_send c0 s01 a1 _ Fa1 SDR1 Hml3 Hmll)) as SF1.
      pose proof (send_facts c0 s02 HC0 a2 _ _ _ Fa2 (sdist_send c0 s02 a2 _ Fa2 SDR2 Hml3' Hmll')) as SF2.
      destruct SF1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE1 & _).
      destruct SF2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE2 & _).
      destruct (st_sdist d1) as [e1 bf]. destruct (st_sdist d2) as [e2 bf2]. cbn [fst snd] in *. subst bf2.
      unfold st_bflush. destruct bf.
      2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact FRe|]. split; [exact Ie1|exact Ie2]. }
      pose proof (fe_diff _ _ FE1) as Hdiff.
      assert (Hbs : ds_block_start e1 <= ds_strstart e1) by (clear - Hdiff; lia).
      pose proof (flush_block_rel HFB HFBR e1 e2 0 FRe Ie1 Ie2 FE1 FE2 Hbs) as (Er & Ef1 & Ef2 & _).
      pose proof (flush_block_only_rel HFB HFBR e1 e2 0 FRe Ie1 Ie2 FE1 FE2 Hbs) as (FRf & If1 & If2 & _).
      destruct (flush_block e1 0) as [f1 r1]. destruct (flush_block e2 0) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
      destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); (split; [exact If1|exact If2]).
    - destruct (Z.eqb_spec (ds_match_available d1) 0) as [Hma|Hma]; cbn [negb].
      +   pose proof (st_avail_rel W C B bnd ms pm d1 d2 Rc Ic1 Ic2 HWc Hbc HPc HSc HHc ltac:(rewrite Elk_c, Elk_p, Elk_b; exact Hlk1)) as XX. exact XX.
      +
        assert (Hma1 : ds_match_available d1 = 1) by (rewrite Ema4 in Hma |- *; pose proof (STI_facts _ _ _ Fa1) as (_ & _ & _ & _ & _ & _ & Hmaa & _); lia).
        pose proof (smid_facts c0 s01 HC0 a1 b1 d1 Fa1 Hlk1 HR1 MR1 Edc Hma1) as SM1. cbv zeta in SM1.
        destruct SM1 as (_ & _ & _ & _ & FE1 & _ & _ & _ & _ & _ & _ & _ & Hss1' & _).
        pose proof (smid_facts c0 s02 HC0 a2 b2 d2 Fa2 Hlk2 HR2 MR2 ltac:(unfold dist_cond in Edc |- *; rel_fields Rc; exact Edc) ltac:(rewrite (rel_match_available _ _ _ _ _ _ _ _ Rc); exact Hma1)) as SM2.
        cbv zeta in SM2. destruct SM2 as (_ & _ & _ & _ & FE2 & _).
        clear HR1 HR2 MR1 MR2.
        rewrite (rel_strstart _ _ _ _ _ _ _ _ Rc) in FE2.
        rewrite (window_eq_upto _ _ _ _ _ _ _ _ (ds_strstart d1 - 1) Rc Ic1 ltac:(intros i Hi; apply HWc; unfold WHI; pose proof (iv_look d1 Ic1); lia)
                   ltac:(pose proof (iv_sl d1 Ic1); pose proof (iv_look d1 Ic1); lia) (ds_strstart d1 - 1) ltac:(rewrite Ess_c, Ess_p, Ess_b; lia)) in FE2.
        pose proof (st_slit_rel HFB HFBR W C B bnd ms pm d1 d2 Rc Ic1 Ic2 HWc Hbc HPc HSc HHc ltac:(rewrite Elk_c, Elk_p, Elk_b; exact Hlk1)
                 ltac:(rewrite Ess_c, Ess_p, Ess_b; exact Hss1') FE1 FE2) as XX.
        exact XX.
  Qed.

  Lemma slow_loop_rel fuel : forall s1 s2,
    STI c0 s01 s1 -> STI c0 s02 s2 -> FREL s1 s2 -> INV s1 -> INV s2 -> lz_meas s1 < Z.of_nat fuel ->
    let r1 := deflate_slow_loop fuel s1 flush in let r2 := deflate_slow_loop fuel s2 flush in
    snd r1 = snd r2 /\ FREL (fst r1) (fst r2) /\ INV (fst r1) /\ INV (fst r2)
    /\ (snd r1 = None -> STI c0 s01 (fst r1) /\ STI c0 s02 (fst r2) /\ ds_lookahead (fst r1) = 0).
  Proof.
    induction fuel as [|f IH]; intros s1 s2 F1 F2 FR I1 I2 Hmz.
    { exfalso. pose proof (STI_facts _ _ _ F1) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite (sloop_step' f s1 flush), (sloop_step' f s2 flush).
    pose proof (slow_step_rel s1 s2 F1 F2 FR I1 I2) as (Eo & FR' & I1' & I2').
    pose proof (sstep c0 s01 flush HC0 HFB s1 F1) as [_ M1]. pose proof (sstep c0 s02 flush HC0 HFB s2 F2) as [_ M2].
    destruct (st_sbody s1 flush) as [t1 o1]. destruct (st_sbody s2 flush) as [t2 o2]. cbn [fst snd] in *. subst o2.
    destruct o1 as [| |bs].
    - destruct M1 as [F1' Hm']. destruct M2 as [F2' _]. exact (IH t1 t2 F1' F2' FR' I1' I2' ltac:(lia)).
    - cbn [fst snd]. split; [reflexivity|]. split; [exact FR'|]. split; [exact I1'|]. split; [exact I2'|].
      intros _. split; [exact (proj1 M1)|]. split; [exact (proj1 M2)|exact (proj2 M1)].
    - cbn [fst snd]. split; [reflexivity|]. split; [exact FR'|]. split; [exact I1'|]. split; [exact I2'|]. intros X; discriminate X.
  Qed.

  Lemma deflate_tail_rel u1 u2 :
    FREL u1 u2 -> INV u1 -> INV u2 ->
    (forall last, 0 <= last <= 1 -> fb_entry u1 last /\ fb_entry u2 last) ->
    snd (deflate_tail u1 flush) = snd (deflate_tail u2 flush)
    /\ FREL (fst (deflate_tail u1 flush)) (fst (deflate_tail u2 flush))
    /\ INV (fst (deflate_tail u1 flush)) /\ INV (fst (deflate_tail u2 flush)).
  Proof.
    intros FRu K1 K2 FE. unfold deflate_tail. pose proof (FREL_clean _ _ FRu) as ECu.
    destruct (Z.eqb_spec flush Z_FINISH).
    - destruct (FE 1 ltac:(lia)) as [FE1 FE2]. pose proof (fe_diff _ _ FE1) as Hd.
      pose proof (flush_block_rel HFB HFBR u1 u2 1 FRu K1 K2 FE1 FE2 ltac:(clear -Hd; lia)) as (Eb & Ef1 & Ef2 & _).
      pose proof (flush_block_only_rel HFB HFBR u1 u2 1 FRu K1 K2 FE1 FE2 ltac:(clear -Hd; lia)) as (FRf & L1 & L2 & _).
      destruct (flush_block u1 1) as [f1 r1]. destruct (flush_block u2 1) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
      destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); (split; [exact L1|exact L2]).
    - rewrite <- (clean_eq_fieldT ds_sym_next _ _ ECu ltac:(reflexivity)).
      destruct (Z.eqb_spec (ds_sym_next u1) 0); cbn [negb].
      + cbn [fst snd]. split; [reflexivity|]. split; [exact FRu|]. split; [exact K1|exact K2].
      + destruct (FE 0 ltac:(lia)) as [FE1 FE2]. pose proof (fe_diff _ _ FE1) as Hd.
        pose proof (flush_block_rel HFB HFBR u1 u2 0 FRu K1 K2 FE1 FE2 ltac:(clear -Hd; lia)) as (Eb & Ef1 & Ef2 & _).
        pose proof (flush_block_only_rel HFB HFBR u1 u2 0 FRu K1 K2 FE1 FE2 ltac:(clear -Hd; lia)) as (FRf & L1 & L2 & _).
        destruct (flush_block u1 0) as [f1 r1]. destruct (flush_block u2 0) as [f2 r2]. cbn [fst snd] in *. subst r2 f1 f2.
        destruct r1; cbn [fst snd]; (split; [reflexivity|]); (split; [exact FRf|]); (split; [exact L1|exact L2]).
  Qed.

  Lemma deflate_slow_rel :
    let s1 := s01 in let s2 := s02 in
    STI c0 s1 s1 -> STI c0 s2 s2 -> FREL s1 s2 -> INV s1 -> INV s2 -> 0 <= flush <= 5 ->
    let r1 := deflate_slow s1 flush in let r2 := deflate_slow s2 flush in
    snd r1 = snd r2 /\ FREL (fst r1) (fst r2) /\ INV (fst r1) /\ INV (fst r2).
  Proof.
    cbv zeta. set (s1 := s01). set (s2 := s02). intros F1 F2 FR I1 I2 Hfl. unfold deflate_slow.
    pose proof (FREL_clean _ _ FR) as EC.
    assert (Efuel : lz_fuel s2 = lz_fuel s1).
    { unfold lz_fuel. rewrite <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_lookahead _ _ EC ltac:(reflexivity)). reflexivity. }
    rewrite Efuel.
    pose proof (STI_facts _ _ _ F1) as (D1 & X1 & V1 & _).
    assert (Hmz : lz_meas s1 < Z.of_nat (lz_fuel s1)).
    { apply lz_fuel_meas. unfold lz_meas. pose proof (df_look _ D1). pose proof (sv_ain _ _ V1). lia. }
    pose proof (slow_loop_rel (lz_fuel s1) s1 s2 F1 F2 FR I1 I2 Hmz) as (Er & FRr & J1 & J2 & Hn).
    destruct (deflate_slow_loop _ s1 flush) as [t1 r1]. destruct (deflate_slow_loop _ s2 flush) as [t2 r2]. cbn [fst snd] in *. subst r2.
    destruct r1 as [bs|].
    { cbn [fst snd]. split; [reflexivity|]. split; [exact FRr|]. split; [exact J1|exact J2]. }
    destruct (Hn eq_refl) as (G1 & G2 & Hl0). clear Hn.
    pose proof (FREL_clean _ _ FRr) as ECt.
    pose proof (STI_facts _ _ _ G1) as (Dt1 & Xt1 & Vt1 & Sw1 & _ & _ & Hma & _ & _ & _ & Hsn1 & _ & Hss1 & _ & _ & _ & Hma11 & _).
    rewrite <- (clean_eq_fieldT ds_match_available _ _ ECt ltac:(reflexivity)).

    assert (TAILREL : forall u1 u2, FREL u1 u2 -> INV u1 -> INV u2 -> TAILOK c0 s01 u1 -> TAILOK c0 s02 u2 -> clean u1 = clean u2 ->
      let v := (if ds_strstart u1 <? MIN_MATCH - 1 then ds_strstart u1 else MIN_MATCH - 1) in
      snd (deflate_tail (set_insert u1 v) flush) = snd (deflate_tail (set_insert u2 v) flush)
      /\ FREL (fst (deflate_tail (set_insert u1 v) flush)) (fst (deflate_tail (set_insert u2 v) flush))
      /\ INV (fst (deflate_tail (set_insert u1 v) flush)) /\ INV (fst (deflate_tail (set_insert u2 v) flush))).
    { intros u1 u2 FRu K1 K2 T1 T2 ECu vv.
      destruct T1 as (Du1 & Vu1 & XXu1 & Bu1 & _ & _ & _ & _ & _ & _ & _ & _ & Hss0 & FE1 & XD1 & _).
      destruct T2 as (Du2 & Vu2 & XXu2 & Bu2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & FE2 & XD2 & _).
      assert (Hv : 0 <= vv <= ds_strstart u1 /\ vv <= 2) by (subst vv; unfold MIN_MATCH; destruct (Z.ltb_spec (ds_strstart u1) (3 - 1)); lia).
      pose proof (dwf_sizes u1 Du1) as (Swu & _). pose proof (dwf_sizes u2 Du2) as (Swu2 & _).
      pose proof (clean_eq_fieldT ds_strstart _ _ ECu ltac:(reflexivity)) as Ess.
      pose proof (tail_insert_facts u1 vv ltac:(lia) ltac:(lia) Du1 XXu1 Bu1 FE1 XD1) as TI1. cbv zeta in TI1. destruct TI1 as (_ & _ & _ & FE1' & _).
      pose proof (tail_insert_facts u2 vv ltac:(rewrite <- Ess; lia) ltac:(lia) Du2 XXu2 Bu2 FE2 XD2) as TI2. cbv zeta in TI2. destruct TI2 as (_ & _ & _ & FE2' & _).
      apply deflate_tail_rel; [apply FREL_set_insert; exact FRu | apply INV_set_insert; [lia|exact K1] | apply INV_set_insert; [rewrite <- Ess; lia|exact K2] | intros last Hl; split; [apply FE1'; exact Hl|apply FE2'; exact Hl]]. }
    cbv zeta.
    destruct (Z.eqb_spec (ds_match_available t1) 0) as [Hma0|Hma0]; cbn [negb].
    - rewrite <- (clean_eq_fieldT ds_strstart _ _ ECt ltac:(reflexivity)).
      apply (TAILREL t1 t2 FRr J1 J2 (TAILOK_STI c0 s01 HC0 t1 G1 Hl0 Hma0)); [|exact ECt].
      apply (TAILOK_STI c0 s02 HC0 t2 G2); [rewrite <- (clean_eq_fieldT ds_lookahead _ _ ECt ltac:(reflexivity)); exact Hl0|rewrite <- (clean_eq_fieldT ds_match_available _ _ ECt ltac:(reflexivity)); exact Hma0].
    - assert (Hma1 : ds_match_available t1 = 1) by lia.
      pose proof FRr as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
      pose proof (iv_ss t1 J1). pose proof (iv_sl t1 J1). pose proof (iv_wl t1 J1).
      rewrite (rel_strstart _ _ _ _ _ _ _ _ R).
      rewrite (window_eq_upto _ _ _ _ _ _ _ _ (ds_strstart t1 - 1) R J1 ltac:(intros i Hi; apply HW; unfold WHI; lia) ltac:(lia) (ds_strstart t1 - 1) ltac:(specialize (Hma11 Hma1); lia)).
      set (c := arr_get (ds_window t1) (ds_strstart t1 - 1)) in *.
      pose proof (tr_tally_lit_rel _ _ _ _ _ _ _ _ c R J1 J2) as [Eb R1].
      pose proof (INV_tr_tally_lit t1 c J1) as L1. pose proof (INV_tr_tally_lit t2 c J2) as L2.
      pose proof (TAILOK_lit c0 s01 HC0 t1 G1 Hl0 Hma1) as T1.
      pose proof (TAILOK_lit c0 s02 HC0 t2 G2 ltac:(rewrite <- (clean_eq_fieldT ds_lookahead _ _ ECt ltac:(reflexivity)); exact Hl0)
                    ltac:(rewrite <- (clean_eq_fieldT ds_match_available _ _ ECt ltac:(reflexivity)); exact Hma1)) as T2.
      rewrite (rel_strstart _ _ _ _ _ _ _ _ R) in T2.
      rewrite (window_eq_upto _ _ _ _ _ _ _ _ (ds_strstart t1 - 1) R J1 ltac:(intros i Hi; apply HW; unfold WHI; lia) ltac:(lia) (ds_strstart t1 - 1) ltac:(specialize (Hma11 Hma1); lia)) in T2.
      fold c in T1, T2.
      pose proof (tr_tally_lit_shape t1 c) as [Sh1 _]. pose proof (tr_tally_lit_shape t2 c) as [Sh2 _].
      destruct (tr_tally_lit t1 c) as [v1 b1]. destruct (tr_tally_lit t2 c) as [v2 b2]. cbn [fst snd] in *.
      assert (FRv : FREL (set_match_available v1 0) (set_match_available v2 0)).
      { exists W, C, (Bx B (ds_lit_bufsize t1 + ds_sym_next t1) (ds_lit_bufsize t1 + ds_sym_next t1 + 3)), bnd, ms, pm.
        split; [apply rel_set_match_available; exact R1|]. subst v1 v2. unfold WHI, PBC, SYMB, HWI, Bx in *. dsr.
        split; [exact HW|]. split; [exact Hb|].
        split; [destruct HP as [[P1 P2]|[P1 P2]]; [left|right]; split; auto|].
        split; [intros i Hi; destruct (Z_lt_le_dec i (ds_lit_bufsize t1 + ds_sym_next t1)); [left; apply HS; lia|right; lia]|].
        exact HH. }
      pose proof (r_clean _ _ _ _ _ _ _ _ (rel_set_match_available _ _ _ _ _ _ _ _ 0 R1)) as ECv.
      dsr. replace (ds_strstart v2) with (ds_strstart v1) by (exact (clean_eq_fieldT ds_strstart _ _ ECv ltac:(reflexivity))).
      replace (ds_strstart v1) with (ds_strstart (set_match_available v1 0)) by reflexivity.
      apply (TAILREL _ _ FRv (INV_set_match_available _ 0 L1) (INV_set_match_available _ 0 L2) T1 T2 ECv).
  Qed.
End SlowRel.
