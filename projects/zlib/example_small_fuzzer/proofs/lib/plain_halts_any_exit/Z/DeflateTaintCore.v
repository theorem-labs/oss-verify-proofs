(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL5.RefDeflSafeL3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeL4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintTrees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintBits.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintBits.DeflateTaintLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintBlk.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintBlk.DeflateTaintTally.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.

Module DeflateTaintSlow.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintBits.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintBits.DeflateTaintLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateTaintBlk.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintBlk.DeflateTaintTally.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.
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
      + pose proof (st_avail_rel W C B bnd ms pm d1 d2 Rc Ic1 Ic2 HWc Hbc HPc HSc HHc ltac:(rewrite Elk_c, Elk_p, Elk_b; exact Hlk1)) as XX. exact XX.
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
End DeflateTaintSlow.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateTaintCore.DeflateTaintSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintStored.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintCall.

Module DeflateTaintInit.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeI6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateTaintCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac krefl := lazymatch goal with |- ?a = _ => exact_no_check (@eq_refl _ a) end.

Section Shape.
  Context {St : Type}.
  Variable H : zhooks St.

  Definition dinit_tail (ml lv st me : Z) (s : deflate_state) : SM St (option deflate_state * ZRet) :=
    do rw <- zalloc H (ds_w_size s) 2 ;
    let s := s_win s rw in
    do rp <- zalloc H (ds_w_size s) 2 ;
    let s := s_prv s rp in
    do rh <- zalloc H (ds_hash_size s) 2 ;
    let s := s_hd s rh in
    let s := s_lbs s ml in
    do rb <- zalloc H (ds_lit_bufsize s) LIT_BUFS ;
    let s := s_pb s rb in
    match ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s with
    | Some _, Some _, Some _, Some _ =>
        let '(s, rc) := deflateReset (s_fin s lv st me) in
        sret (Some s, zret_of_cs (ds_strm s) rc)
    | _, _, _, _ =>
        let s := s_fail s in
        do _ <- deflateEnd_core H s ;
        sret (None, zret_of_cs (ds_strm s) Z_MEM_ERROR)
    end.

  Definition dinit_prog (zc : ZCall) (level method windowBits memLevel strategy : Z)
    : SM St (option deflate_state * ZRet) :=
    let cs := cset_msg (cstrm_of_call zc) MSG_NULL in
    let level := if Z.eqb level Z_DEFAULT_COMPRESSION then 6 else level in
    let '(wrap, windowBits, bad) :=
      if Z.ltb windowBits 0 then (0, - windowBits, Z.ltb windowBits (-15))
      else if Z.ltb 15 windowBits then (2, windowBits - 16, false)
      else (1, windowBits, false) in
    if bad then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else if (memLevel <? 1) || (MAX_MEM_LEVEL <? memLevel) || negb (method =? Z_DEFLATED)
            || (windowBits <? 8) || (15 <? windowBits) || (level <? 0) || (9 <? level)
            || (strategy <? 0) || (Z_FIXED <? strategy) || ((windowBits =? 8) && negb (wrap =? 1))
    then sret (None, zret_of_cs cs Z_STREAM_ERROR)
    else
      let windowBits := if Z.eqb windowBits 8 then 9 else windowBits in
      do r0 <- zalloc H 1 SIZEOF_deflate_state ;
      match r0 with
      | None => sret (None, zret_of_cs cs Z_MEM_ERROR)
      | Some (b0, g0) => dinit_tail memLevel level strategy method (s_setup g0 b0 cs wrap windowBits memLevel)
      end.

  Lemma deflateInit2_m_prog : forall zc level method windowBits memLevel strategy,
    deflateInit2_m H zc level method windowBits memLevel strategy = dinit_prog zc level method windowBits memLevel strategy.
  Proof. intros. krefl. Qed.
End Shape.


Lemma dFg_strm b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 meml lv strat method :
  ds_strm (dFg b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 meml lv strat method)
  = cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
               (if wrap =? 2 then crc32_init else adler32_init).
Proof. reflexivity. Qed.

Lemma s_fail_proj' : forall s,
  ds_pending_buf_blk (s_fail s) = ds_pending_buf_blk s /\ ds_head_blk (s_fail s) = ds_head_blk s
  /\ ds_prev_blk (s_fail s) = ds_prev_blk s /\ ds_window_blk (s_fail s) = ds_window_blk s
  /\ ds_self_blk (s_fail s) = ds_self_blk s /\ ds_status (s_fail s) = FINISH_STATE
  /\ ds_strm (s_fail s) = cset_msg (ds_strm s) (MSG_ERR Z_MEM_ERROR).
Proof. intros s. destruct s. repeat split; reflexivity. Qed.

Definition IRAW (cs : cstrm) (wrap wb9 ml lv st me : Z) (s1 s2 : deflate_state) : Prop :=
  exists b0 bw bp bh bb g0 gw gp gh gb g0' gw' gp' gh' gb',
    s1 = dFg b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 ml lv st me
    /\ s2 = dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs wrap wb9 ml lv st me.

Definition init_cs (cs : cstrm) (wrap : Z) : cstrm :=
  cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
             (if wrap =? 2 then crc32_init else adler32_init).

Definition IQ (OK : Prop) (cs : cstrm) (wrap wb9 ml lv st me : Z) (p1 p2 : option deflate_state * ZRet) : Prop :=
  snd p1 = snd p2
  /\ match fst p1, fst p2 with
     | Some s1, Some s2 => OK /\ IRAW cs wrap wb9 ml lv st me s1 s2 /\ snd p1 = zret_of_cs (init_cs cs wrap) Z_OK
     | None, None => True
     | _, _ => False
     end.

Section TwoHooks.
  Context {St : Type}.
  Variable H1 : zhooks St.
Variable H2 : zhooks St.
  Hypothesis HZ : forall a b, srel (fun r1 r2 => option_map fst r1 = option_map fst r2) (zalloc H1 a b) (zalloc H2 a b).
  Hypothesis HF : forall b, srel eq (zfree H1 b) (zfree H2 b).

  Lemma try_free_rel b : srel eq (try_free H1 b) (try_free H2 b).
  Proof. destruct b as [b|]; [apply HF | apply srel_eq_refl]. Qed.

  Lemma deflateEnd_core_rel s1 s2 :
    ds_pending_buf_blk s2 = ds_pending_buf_blk s1 -> ds_head_blk s2 = ds_head_blk s1 -> ds_prev_blk s2 = ds_prev_blk s1 ->
    ds_window_blk s2 = ds_window_blk s1 -> ds_self_blk s2 = ds_self_blk s1 -> ds_status s2 = ds_status s1 ->
    srel eq (deflateEnd_core H1 s1) (deflateEnd_core H2 s2).
  Proof.
    intros E1 E2 E3 E4 E5 E6. unfold deflateEnd_core. rewrite E1, E2, E3, E4, E5, E6.
    eapply srel_bind; [apply try_free_rel | intros [] [] _].
    eapply srel_bind; [apply try_free_rel | intros [] [] _].
    eapply srel_bind; [apply try_free_rel | intros [] [] _].
    eapply srel_bind; [apply try_free_rel | intros [] [] _].
    eapply srel_bind; [apply HF | intros [] [] _].
    apply srel_ret. reflexivity.
  Qed.

  Lemma dinit_tail_rel (OK : Prop) (HOK : OK) ml lv st me cs wrap wb9 b0 g0 g0' : 0 <= wrap ->
    srel (IQ OK cs wrap wb9 ml lv st me)
         (dinit_tail H1 ml lv st me (s_setup g0 b0 cs wrap wb9 ml))
         (dinit_tail H2 ml lv st me (s_setup g0' b0 cs wrap wb9 ml)).
  Proof.
    intros Hw. unfold dinit_tail.
    rewrite !s_setup_w_size.
    eapply srel_bind; [apply HZ | intros rw1 rw2 Qw; cbv beta zeta].
    rewrite !s_win_w_size, !s_setup_w_size.
    eapply srel_bind; [apply HZ | intros rp1 rp2 Qp; cbv beta zeta].
    rewrite !s_prv_hash_size, !s_win_hash_size, !s_setup_hash_size.
    eapply srel_bind; [apply HZ | intros rh1 rh2 Qh; cbv beta zeta].
    rewrite !s_lbs_lit_bufsize.
    eapply srel_bind; [apply HZ | intros rb1 rb2 Qb; cbv beta zeta].
    rewrite !s5_window_blk, !s5_prev_blk, !s5_head_blk, !s5_pending_buf_blk.
    assert (FAIL : forall rw1 rw2 rp1 rp2 rh1 rh2 rb1 rb2,
      option_map fst rw1 = option_map fst rw2 -> option_map fst rp1 = option_map fst rp2 ->
      option_map fst rh1 = option_map fst rh2 -> option_map fst rb1 = option_map fst rb2 ->
      let x1 := s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 ml) rw1) rp1) rh1) ml) rb1 in
      let x2 := s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0' b0 cs wrap wb9 ml) rw2) rp2) rh2) ml) rb2 in
      srel (IQ OK cs wrap wb9 ml lv st me)
           (let s := s_fail x1 in do _ <- deflateEnd_core H1 s ; sret (None, zret_of_cs (ds_strm s) Z_MEM_ERROR))
           (let s := s_fail x2 in do _ <- deflateEnd_core H2 s ; sret (None, zret_of_cs (ds_strm s) Z_MEM_ERROR))).
    { intros w1 w2 p1 p2 h1 h2 q1 q2 Ew Ep Eh Eb x1 x2. cbv zeta.
      pose proof (s_fail_proj' x1) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      pose proof (s_fail_proj' x2) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      eapply srel_bind.
      - apply deflateEnd_core_rel; rewrite ?A1, ?A2, ?A3, ?A4, ?A5, ?A6, ?B1, ?B2, ?B3, ?B4, ?B5, ?B6; subst x1 x2;
          rewrite ?s5_window_blk, ?s5_prev_blk, ?s5_head_blk, ?s5_pending_buf_blk, ?s5_self_blk, ?s5_status;
          first [exact (eq_sym Eb) | exact (eq_sym Eh) | exact (eq_sym Ep) | exact (eq_sym Ew) | rewrite !s_setup_self; reflexivity | reflexivity].
      - intros u1 u2 _. apply srel_ret. split; [| exact I]. cbn [fst snd]. rewrite A7, B7. subst x1 x2. rewrite !s5_strm, !s_setup_strm. reflexivity. }
    destruct rw1 as [[bw gw]|], rw2 as [[bw' gw']|]; cbn [option_map fst] in Qw; try discriminate Qw;
      [injection Qw as <- | apply (FAIL None None rp1 rp2 rh1 rh2 rb1 rb2); [reflexivity | exact Qp | exact Qh | exact Qb]].
    destruct rp1 as [[bp gp]|], rp2 as [[bp' gp']|]; cbn [option_map fst] in Qp; try discriminate Qp;
      [injection Qp as <- | apply (FAIL (Some (bw, gw)) (Some (bw, gw')) None None rh1 rh2 rb1 rb2); [reflexivity | reflexivity | exact Qh | exact Qb]].
    destruct rh1 as [[bh gh]|], rh2 as [[bh' gh']|]; cbn [option_map fst] in Qh; try discriminate Qh;
      [injection Qh as <- | apply (FAIL (Some (bw, gw)) (Some (bw, gw')) (Some (bp, gp)) (Some (bp, gp')) None None rb1 rb2); [reflexivity | reflexivity | reflexivity | exact Qb]].
    destruct rb1 as [[bb gb]|], rb2 as [[bb' gb']|]; cbn [option_map fst] in Qb; try discriminate Qb;
      [injection Qb as <- | apply (FAIL (Some (bw, gw)) (Some (bw, gw')) (Some (bp, gp)) (Some (bp, gp')) (Some (bh, gh)) (Some (bh, gh')) None None); reflexivity].
    cbn [option_map fst].
    change (s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 ml) (Some (bw, gw))) (Some (bp, gp))) (Some (bh, gh))) ml) (Some (bb, gb)))
      with (S5g b0 bw bp bh bb g0 gw gp gh gb cs wrap wb9 ml).
    change (s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0' b0 cs wrap wb9 ml) (Some (bw, gw'))) (Some (bp, gp'))) (Some (bh, gh'))) ml) (Some (bb, gb')))
      with (S5g b0 bw bp bh bb g0' gw' gp' gh' gb' cs wrap wb9 ml).
    rewrite !(reset_S5g _ _ _ _ _ _ _ _ _ _ cs wrap wb9 ml lv st me Hw).
    apply srel_ret. split.
    - cbn [fst snd]. rewrite !dFg_strm. reflexivity.
    - cbn [fst snd]. split; [exact HOK|]. split; [| rewrite dFg_strm; reflexivity].
      exists b0, bw, bp, bh, bb, g0, gw, gp, gh, gb. exists g0', gw', gp', gh', gb'. split; reflexivity.
  Qed.

  Theorem deflateInit2_hooks_rel zc level method wb meml strategy :
    srel (IQ (di_bad level method wb meml strategy = false) (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method)
         (deflateInit2_m H1 zc level method wb meml strategy)
         (deflateInit2_m H2 zc level method wb meml strategy).
  Proof.
    rewrite (deflateInit2_m_prog H1), (deflateInit2_m_prog H2). unfold dinit_prog.
    rewrite di_triple. cbv beta iota.
    change (cset_msg (cstrm_of_call zc) MSG_NULL) with (cs_init zc).
    change (if level =? Z_DEFAULT_COMPRESSION then 6 else level) with (di_level level).
    destruct ((wb <? 0) && (wb <? -15)) eqn:Hb0.
    { apply srel_ret. split; [reflexivity | exact I]. }
    lazymatch goal with |- srel _ (if ?c then _ else _) _ => replace c with (di_chk level method wb meml strategy) by reflexivity end.
    destruct (di_chk level method wb meml strategy) eqn:Hchk.
    { apply srel_ret. split; [reflexivity | exact I]. }
    change (if di_wb wb =? 8 then 9 else di_wb wb) with (di_wb9 wb).
    eapply srel_bind; [apply HZ | intros r1 r2 Q0; cbv beta].
    destruct r1 as [[b0 g0]|], r2 as [[b0' g0']|]; cbn [option_map fst] in Q0; try discriminate Q0.
    - injection Q0 as <-. apply dinit_tail_rel; [| exact (proj1 (di_wrap_range wb))].
      unfold di_bad. rewrite Hb0, Hchk. reflexivity.
    - apply srel_ret. split; [reflexivity | exact I].
  Qed.
End TwoHooks.


Section ZcHooks.
  Context {MM : MallocModel}.
End ZcHooks.


Lemma dFg_dreach zc level method wb meml strategy b0 bw bp bh bb g0 gw gp gh gb :
  di_bad level method wb meml strategy = false -> 5 <= meml ->
  dreach (dFg b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method).
Proof.
  intros Hbad HML5.
  apply (DR_init zc level method wb meml strategy [Some (b0, g0); Some (bw, gw); Some (bp, gp); Some (bh, gh); Some (bb, gb)] _
           (zret_of_cs (ds_strm (dFg b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method)) Z_OK)); [exact HML5|].
  rewrite (dinit_run zc level method wb meml strategy _ Hbad). cbn [ohd otl].
  pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb))) as PJ.
  cbv zeta in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
  unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb. cbn [option_map fst].
  change (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb)))
    with (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml).
  rewrite (reset_S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method (proj1 (di_wrap_range wb))).
  reflexivity.
Qed.

Section Facts.
  Variable b0 : blk.
Variable bw : blk.
Variable bp : blk.
Variable bh : blk.
Variable bb : blk.
Variable cs : cstrm.
Variable lv : Z.
  Hypothesis Hlv : 0 <= lv <= 9.
  Hypothesis Hain : 0 <= cs_avail_in cs.
  Hypothesis Haout : 0 <= cs_avail_out cs.

  Section One.
    Variable g0 : Z -> Z.
Variable gw : Z -> Z.
Variable gp : Z -> Z.
Variable gh : Z -> Z.
Variable gb : Z -> Z.
    Let F := dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8.

    Lemma dFg_lens :
      arr_len (ds_window F) = 65536 /\ arr_len (ds_prev F) = 32768 /\ arr_len (ds_head F) = 32768 /\ arr_len (ds_pending_buf F) = 65536
      /\ arr_len (ds_dyn_ltree_fc F) = 573 /\ arr_len (ds_dyn_dtree_fc F) = 61 /\ arr_len (ds_bl_tree_fc F) = 39.
    Proof.
      unfold F, dFg. cbn [ds_window ds_prev ds_head ds_pending_buf ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc].
      unfold blk_bytes, blk_ush, arr_u16_of. rewrite ?arr_len_fill, ?arr_len_set, ?arr_len_fill, !arr_len_init. repeat split; reflexivity.
    Qed.

    Lemma dFg_head0' h : 0 <= h < 32768 -> arr_get (ds_head F) h = 0.
    Proof.
      intros Hh. unfold F, dFg. cbn [ds_head]. apply (cleared_get (blk_ush gh (Z.shiftl 1 (8 + 7)))); [| exact Hh].
      unfold blk_ush. rewrite arr_len_init. reflexivity.
    Qed.

    Lemma dFg_INV : INV F.
    Proof.
      pose proof dFg_lens as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
      pose proof (dFg_dwf b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8 ltac:(lia) ltac:(lia) Hlv ltac:(lia) ltac:(lia) eq_refl) as D.
      pose proof (df_tl _ D) as TL. clear D. revert L1 L2 L3 L4 L5 L6 L7 TL.
      unfold F, dFg, tree_lens.
      cbn [ds_w_size ds_w_mask ds_w_bits ds_window_size ds_hash_size ds_hash_mask ds_hash_bits ds_hash_shift ds_lit_bufsize
           ds_pending_buf_size ds_sym_end ds_window ds_prev ds_head ds_pending_buf ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc
           ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth ds_strstart ds_lookahead ds_insert ds_high_water
           ds_strm ds_opt_len ds_static_len ds_match_length ds_prev_length ds_strategy ds_pending ds_pending_out
           cs_avail_in cs_avail_out cset_adler cset_data_type cset_msg cset_total_out cset_total_in].
      intros L1 L2 L3 L4 L5 L6 L7 TL.
      constructor;
        [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity
        | exact L1 | exact L2 | exact L3 | exact L4 | exact TL
        | cbn [ds_strstart]; lia | cbn [ds_lookahead]; lia | cbn [ds_insert ds_strstart]; lia | cbn [ds_strstart ds_lookahead]; lia
        | cbn [ds_high_water]; lia
        | cbn [ds_strm cs_avail_in cset_adler cset_data_type cset_msg cset_total_out cset_total_in]; destruct cs; cbn in Hain |- *; exact Hain
        | cbn [ds_opt_len]; lia | cbn [ds_static_len]; lia
        | cbn [ds_match_length]; unfold MIN_MATCH; lia | cbn [ds_prev_length]; unfold MIN_MATCH; lia
        | reflexivity | cbn [ds_pending]; lia | cbn [ds_pending ds_pending_out]; intros _; reflexivity
        | cbn [ds_strm cs_avail_out cset_adler cset_data_type cset_msg cset_total_out cset_total_in]; destruct cs; cbn in Haout |- *; exact Haout ].
    Qed.
  End One.

  Local Ltac proj_cbn :=
    cbn [ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush
         ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift
         ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length
         ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl
         ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap
         ds_heap_len ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf
         ds_bi_valid ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm].

  Lemma dFg_REL g0 gw gp gh gb g0' gw' gp' gh' gb' :
    REL (fun i => i < 0) (fun _ => False) (fun _ => False) 0 false false
        (dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8) (dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs 1 15 8 lv 0 8).
  Proof.
    pose proof (dFg_lens g0 gw gp gh gb) as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    pose proof (dFg_lens g0' gw' gp' gh' gb') as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
    pose proof (dFg_head0' g0 gw gp gh gb) as Z1. pose proof (dFg_head0' g0' gw' gp' gh' gb') as Z2.
    revert L1 L2 L3 L4 L5 L6 L7 M1 M2 M3 M4 M5 M6 M7 Z1 Z2.
    unfold dFg. proj_cbn. intros L1 L2 L3 L4 L5 L6 L7 M1 M2 M3 M4 M5 M6 M7 Z1 Z2.
    constructor; proj_cbn.
    - unfold clean. proj_cbn. reflexivity.
    - split; [rewrite L1, M1; reflexivity | intros i Hi Hlt; exfalso; lia].
    - split; [rewrite L3, M3; reflexivity | intros i Hi _]. rewrite L3 in Hi. rewrite Z1, Z2 by exact Hi. reflexivity.
    - split; [rewrite L2, M2; reflexivity | intros i _ Hf; destruct Hf].
    - split; [| intros p Hf; destruct Hf]. intros h Hh. unfold cv. proj_cbn. rewrite Z1 by exact Hh. split; [lia | left; reflexivity].
    - split; [rewrite L4, M4; reflexivity | intros i _ Hf; destruct Hf].
    - split; [rewrite L5, M5; reflexivity | intros i Hi Hlt]. rewrite L5 in Hi.
      rewrite !arr_get_set, !arr_get_fill. unfold arr_inb. rewrite !arr_len_fill. unfold arr_u16_of. rewrite !arr_len_init.
      unfold L_CODES, END_BLOCK in *.
      destruct (Z.eqb_spec 256 i); cbn [andb].
      + replace ((0 <=? 256) && (256 <? 573)) with true by reflexivity. reflexivity.
      + replace ((0 <=? i) && (i <? 0 + Z.max 0 286) && ((0 <=? i) && (i <? 573))) with true
          by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - split; [rewrite L6, M6; reflexivity | intros i Hi Hlt]. rewrite L6 in Hi.
      rewrite !arr_get_fill. unfold arr_inb. unfold arr_u16_of. rewrite !arr_len_init. unfold D_CODES in *.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 30) && ((0 <=? i) && (i <? 61))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - split; [rewrite L7, M7; reflexivity | intros i Hi Hlt]. rewrite L7 in Hi.
      rewrite !arr_get_fill. unfold arr_inb. unfold arr_u16_of. rewrite !arr_len_init. unfold BL_CODES in *.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 19) && ((0 <=? i) && (i <? 39))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - intros E; discriminate E.
    - intros E; discriminate E.
    - unfold MIN_MATCH. intros; exfalso; lia.
    - unfold MIN_MATCH. intros; exfalso; lia.
    - intros E; discriminate E.
  Qed.

  Lemma dFg_DQ g0 gw gp gh gb g0' gw' gp' gh' gb' :
    DQ (dFg b0 bw bp bh bb g0 gw gp gh gb cs 1 15 8 lv 0 8) (dFg b0 bw bp bh bb g0' gw' gp' gh' gb' cs 1 15 8 lv 0 8).
  Proof.
    exists (fun i => i < 0), (fun _ => False), (fun _ => False), 0, false, false.
    split; [apply dFg_REL|]. unfold WHI, SYMB, HWI, dFg. proj_cbn.
    split; [intros i Hi; lia|]. split; [intros _; lia|]. split; [intros; lia|]. split; [intros; lia | apply HWI4_look0].
  Qed.
End Facts.

Lemma di_bad_level level method wb meml strategy :
  di_bad level method wb meml strategy = false -> 0 <= di_level level <= 9.
Proof.
  unfold di_bad, di_chk. intros Hb. apply Bool.orb_false_iff in Hb as [_ Hc].
  repeat (apply Bool.orb_false_iff in Hc as [Hc ?]).
  repeat match goal with K : (_ <? _) = false |- _ => apply Z.ltb_ge in K end. lia.
Qed.


Definition ISTRM (z : zstrm) : Prop := zstrm_okP z /\ zs_total_out z = 0 /\ zs_total_in z = 0.
End DeflateTaintInit.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma DREL_clean s1 s2 : DREL s1 s2 -> clean s1 = clean s2.
Proof. intros (W & C & B & bnd & ms & pm & R & _). exact (r_clean _ _ _ _ _ _ _ _ R). Qed.

Lemma DQ_set_strm s1 s2 c : DQ s1 s2 -> DQ (set_strm s1 c) (set_strm s2 c).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_strm; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_set_last_flush s1 s2 v : DQ s1 s2 -> DQ (set_last_flush s1 v) (set_last_flush s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_last_flush; exact R|]. unfold WHI, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DQ_err_return s1 s2 e : DQ s1 s2 -> snd (err_return s1 e) = snd (err_return s2 e) /\ DQ (fst (err_return s1 e)) (fst (err_return s2 e)).
Proof.
  intros D. pose proof (DQ_clean _ _ D) as EC. unfold err_return. cbn [fst snd]. split; [reflexivity|].
  rewrite <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)). apply DQ_set_strm. exact D.
Qed.
Lemma DREL_set_status s1 s2 v : DREL s1 s2 -> DREL (set_status s1 v) (set_status s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_status; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DREL_set_last_flush s1 s2 v : DREL s1 s2 -> DREL (set_last_flush s1 v) (set_last_flush s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_last_flush; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma DREL_set_wrap s1 s2 v : DREL s1 s2 -> DREL (set_wrap s1 v) (set_wrap s2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_wrap; exact R|]. unfold WHI, PBC, SYMB, HWI in *. dsr. repeat (split; [assumption|]). exact HH.
Qed.
Lemma INV_err_return s e : INV s -> INV (fst (err_return s e)).
Proof. intros I. unfold err_return. cbn [fst]. apply INV_set_strm; [dsr; exact (iv_ain s I)|dsr; exact (iv_aout s I)|exact I]. Qed.


Lemma bi_flush_noop s : ds_bi_valid s <= 7 -> ds_pending (bi_flush s) = ds_pending s.
Proof.
  intros H. rewrite bi_flush_pending. destruct (Z.eqb_spec (ds_bi_valid s) 16); [lia|]. destruct (Z.leb_spec 8 (ds_bi_valid s)); [lia|reflexivity].
Qed.

Lemma flush_pending_DREL W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INV s1 -> INV s2 ->
  (forall i, i < WHI s1 -> W i) -> (ds_level s1 <> 0 -> bnd <= ds_strstart s1) -> SYMB B s1 -> HWI s1 ->
  0 <= ds_pending_out s1 -> (forall i, ds_pending_out s1 <= i < ds_pending_out s1 + ds_pending s1 -> B i) ->
  (ds_pending_out s1 = 0 \/ ds_pending (bi_flush s1) = ds_pending s1) ->
  ds_pending_out s1 + ds_pending (bi_flush s1) <= 65536 ->
  DREL (flush_pending s1) (flush_pending s2) /\ INV (flush_pending s1) /\ INV (flush_pending s2)
  /\ lzm (flush_pending s1) = lzm s1 /\ ds_sym_next (flush_pending s1) = ds_sym_next s1
  /\ cs_avail_in (ds_strm (flush_pending s1)) = cs_avail_in (ds_strm s1).
Proof.
  intros R I1 I2 HW Hb HS HH PO0 PB PZ HL.
  pose proof (iv_bl s1 I1) as BL1.
  pose proof (flush_pending_rel _ _ _ _ _ _ _ _ R I1 I2 PO0 ltac:(rewrite BL1; exact HL) PB PZ) as (R' & K1 & K2).
  pose proof (bi_flush_pending_le s1) as BFL.
  pose proof (flush_pending_shape s1 (iv_aout s1 I1) (iv_pend s1 I1) ltac:(lia)) as SH.
  cbv zeta in SH. destruct SH as (po & st & E & Ei & En & Ea & Eo & El & Hlen & Hpo & _).
  pose proof (k_bi_flush lzv true true keeps_lzv eq_refl s1) as L3.
  pose proof (k_bi_flush ds_sym_next true false keeps_sym_next eq_refl s1) as SN3.
  pose proof (iv_po _ K1) as PO'.
  revert R' K1 K2 PO'. rewrite E. set (s9 := bi_flush s1) in *. clearbody s9. set (t2 := flush_pending s2). clearbody t2. intros R' K1 K2 PO'.
  assert (LL : lzm s9 = lzm s1) by (apply lzm_of_lzv; exact L3).
  split; [|split; [exact K1|]; split; [exact K2|]; dsr; lzm_rw LL; split; [reflexivity|]; split; [exact SN3|rewrite Ea; reflexivity]].
  exists W, C, (Bx B (ds_pending s1) (ds_pending s9)), bnd, ms, pm. split; [exact R'|].
  revert PO'. unfold WHI, PBC, SYMB, HWI, Bx in *. lzm_rw LL. intros PO'.
  split; [exact HW|]. split; [exact Hb|]. split.
  { rewrite Eo. destruct Hpo as [[A1 A2]|[[A1 [A2 A3]]|[A1 A2]]].
    - left. split; [exact A2|intros; lia].
    - right. split; [lia|]. intros i Hi. destruct PZ as [PZ|PZ]; [|left; apply PB; lia].
      rewrite PZ in *. destruct (Z_lt_le_dec i (ds_pending s1)); [left; apply PB; lia|right; lia].
    - rewrite A1 in *. destruct (Z.eq_dec (ds_pending s9) 0) as [Z0|Z0].
      + left. split; [apply PO'; lia|intros; lia].
      + right. split; [lia|]. intros i Hi. destruct PZ as [PZ|PZ]; [|left; apply PB; lia].
        rewrite PZ in *. destruct (Z_lt_le_dec i (ds_pending s1)); [left; apply PB; lia|right; lia]. }
  rewrite ?SN3. split; [intros i Hi; left; apply HS; exact Hi|exact HH].
Qed.


Lemma CFG_lzv s t : lzv t = lzv s -> CFG s -> CFG t.
Proof.
  intros E (C1 & C2 & C3). pose proof (lzv_fields _ _ E) as F. repeat match type of F with _ /\ _ => destruct F as [? F] end.
  unfold CFG. repeat match goal with H : ?f t = ?f s |- context [?f t] => rewrite H end. repeat split; assumption.
Qed.
Lemma lzv_put_byte s c : lzv (put_byte s c) = lzv s. Proof. reflexivity. Qed.
Lemma lzv_putShortMSB s b : lzv (putShortMSB s b) = lzv s. Proof. reflexivity. Qed.

Definition WRUN (s1 t1 t2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C (Bx B 0 (ds_pending t1)) bnd ms pm t1 t2
    /\ (forall i, i < WHI s1 -> W i) /\ (ds_level s1 <> 0 -> bnd <= ds_strstart s1) /\ SYMB B s1 /\ HWI s1
    /\ lzm t1 = lzm s1 /\ ds_sym_next t1 = ds_sym_next s1 /\ ds_pending_out t1 = 0 /\ 0 <= ds_pending t1
    /\ cs_avail_in (ds_strm t1) = cs_avail_in (ds_strm s1) /\ cs_avail_out (ds_strm t1) = cs_avail_out (ds_strm s1).

Lemma WRUN_start s1 s2 : DREL s1 s2 -> INV s1 -> ds_pending s1 = 0 -> WRUN s1 s1 s2.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) I1 Hp. pose proof (iv_po s1 I1 Hp) as Hpo.
  exists W, C, B, bnd, ms, pm. split; [rewrite Hp; apply rel_Bx_same; exact R|].
  split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hpo|]. split; [lia|]. split; reflexivity.
Qed.

Lemma WRUN_put_byte s1 t1 t2 c : WRUN s1 t1 t2 -> WRUN s1 (put_byte t1 c) (put_byte t2 c).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao). exists W, C, B, bnd, ms, pm.
  split.
  { pose proof (put_byte_rel _ _ _ _ _ _ _ _ c R) as R1. rewrite put_byte_pending in *.
    apply (rel_weaken _ _ _ _ _ _ _ _ _ _ _ R1); [auto| |apply Z.le_refl]. unfold Bx. intros i [X|X]; [left; left; exact X|]. destruct (Z_lt_le_dec i (ds_pending t1)); [left; right; lia|right; lia]. }
  split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. unfold put_byte. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. split; [exact Eai|exact Eao].
Qed.
Lemma WRUN_putShortMSB s1 t1 t2 b : WRUN s1 t1 t2 -> WRUN s1 (putShortMSB t1 b) (putShortMSB t2 b).
Proof. intros H. unfold putShortMSB. apply WRUN_put_byte, WRUN_put_byte, H. Qed.
Lemma WRUN_set_strm s1 t1 t2 st1 st2 :
  WRUN s1 t1 t2 -> st1 = st2 -> cs_avail_in st1 = cs_avail_in (ds_strm t1) -> cs_avail_out st1 = cs_avail_out (ds_strm t1) ->
  WRUN s1 (set_strm t1 st1) (set_strm t2 st2).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao) <- E1 E2. exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_strm; exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. rewrite E1, E2. split; [exact Eai|exact Eao].
Qed.
Lemma WRUN_set_status s1 t1 t2 v : WRUN s1 t1 t2 -> WRUN s1 (set_status t1 v) (set_status t2 v).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao). exists W, C, B, bnd, ms, pm.
  split; [apply rel_set_status; exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
  split; [rewrite <- L; reflexivity|]. dsr. split; [exact Esn|]. split; [exact Hpo|]. split; [lia|]. split; [exact Eai|exact Eao].
Qed.
Lemma WRUN_clean s1 t1 t2 : WRUN s1 t1 t2 -> clean t1 = clean t2.
Proof. intros (W & C & B & bnd & ms & pm & R & _). exact (r_clean _ _ _ _ _ _ _ _ R). Qed.

Lemma WRUN_flush s1 t1 t2 : WRUN s1 t1 t2 -> INV t1 -> INV t2 -> ds_bi_valid t1 <= 7 -> ds_pending t1 <= 65536 ->
  DREL (flush_pending t1) (flush_pending t2) /\ INV (flush_pending t1) /\ INV (flush_pending t2)
  /\ lzm (flush_pending t1) = lzm s1 /\ ds_sym_next (flush_pending t1) = ds_sym_next s1
  /\ cs_avail_in (ds_strm (flush_pending t1)) = cs_avail_in (ds_strm s1).
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HS & HH & L & Esn & Hpo & Hp & Eai & Eao) K1 K2 Hbv Hpl.
  pose proof (bi_flush_noop t1 Hbv) as NB.
  assert (Lf : lzm t1 = lzm s1) by exact L.
  pose proof (lzm_fields _ _ L) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  pose proof (flush_pending_DREL W C (Bx B 0 (ds_pending t1)) bnd ms pm t1 t2 R K1 K2) as X.
  unfold WHI, SYMB, HWI in X, HW, HS, HH. rewrite E1, E2, E3, E4, E10, Esn, Hpo, NB in X.
  specialize (X HW Hb ltac:(intros i Hi; left; apply HS; exact Hi) HH ltac:(lia) ltac:(intros i Hi; right; lia) ltac:(left; reflexivity) ltac:(lia)).
  destruct X as (D & J1 & J2 & L' & Esn' & Eai'). split; [exact D|]. split; [exact J1|]. split; [exact J2|].
  rewrite L', Esn', Eai'. split; [exact Lf|]. split; [reflexivity|exact Eai].
Qed.

Lemma putShortMSB_strstart s b : ds_strstart (putShortMSB s b) = ds_strstart s. Proof. reflexivity. Qed.
Lemma putShortMSB_strm s b : ds_strm (putShortMSB s b) = ds_strm s. Proof. reflexivity. Qed.

Lemma zhdr_WRUN s1 s2 : DREL s1 s2 -> INV s1 -> ds_pending s1 = 0 ->
  WRUN s1 (zhdr_st s1) (zhdr_st s2) /\ ds_pending (zhdr_st s1) <= 6.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold zhdr_st. cbv zeta. rewrite !putShortMSB_strstart, !putShortMSB_strm. eqc_fields EC.
  match goal with |- context [putShortMSB s1 ?h] => set (hdr := h) end.
  pose proof (WRUN_putShortMSB _ _ _ hdr W0) as W1.
  destruct (Z.eqb_spec (ds_strstart s1) 0); cbn [negb]; rewrite !putShortMSB_strm; eqc_fields EC.
  - split; [|unfold putShortMSB, put_byte; dsr; lia].
    apply WRUN_set_status. eapply WRUN_set_strm; [exact W1|reflexivity|dsr; reflexivity|dsr; reflexivity].
  - set (a := cs_adler (ds_strm s1)).
    pose proof (WRUN_putShortMSB _ _ _ (Z.land a 65535) (WRUN_putShortMSB _ _ _ (wrap32 (Z.shiftr a 16)) W1)) as W3.
    split; [|unfold putShortMSB, put_byte; dsr; lia].
    apply WRUN_set_status. eapply WRUN_set_strm; [exact W3|reflexivity|dsr; reflexivity|dsr; reflexivity].
Qed.

Lemma put_byte_level s c : ds_level (put_byte s c) = ds_level s. Proof. reflexivity. Qed.
Lemma put_byte_strategy s c : ds_strategy (put_byte s c) = ds_strategy s. Proof. reflexivity. Qed.
Lemma put_byte_strm s c : ds_strm (put_byte s c) = ds_strm s. Proof. reflexivity. Qed.
Lemma set_strm_level s v : ds_level (set_strm s v) = ds_level s. Proof. reflexivity. Qed.
Lemma set_strm_strategy s v : ds_strategy (set_strm s v) = ds_strategy s. Proof. reflexivity. Qed.
Lemma set_strm_pending s v : ds_pending (set_strm s v) = ds_pending s. Proof. reflexivity. Qed.
Lemma set_status_pending s v : ds_pending (set_status s v) = ds_pending s. Proof. reflexivity. Qed.
Lemma set_strm_strm s v : ds_strm (set_strm s v) = v. Proof. reflexivity. Qed.
Lemma cset_adler_avail_in c v : cs_avail_in (cset_adler c v) = cs_avail_in c. Proof. reflexivity. Qed.
Lemma cset_adler_avail_out c v : cs_avail_out (cset_adler c v) = cs_avail_out c. Proof. reflexivity. Qed.

Lemma gzhdr_WRUN s1 s2 : DREL s1 s2 -> INV s1 -> ds_pending s1 = 0 ->
  WRUN s1 (gzhdr_st s1) (gzhdr_st s2) /\ ds_pending (gzhdr_st s1) <= 10.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold gzhdr_st. cbv zeta. rewrite !put_byte_level, !put_byte_strategy, !set_strm_level, !set_strm_strategy. eqc_fields EC.
  split; [|rewrite set_status_pending, !put_byte_pending, set_strm_pending; lia].
  apply WRUN_set_status. repeat apply WRUN_put_byte.
  eapply WRUN_set_strm; [exact W0|reflexivity|rewrite cset_adler_avail_in; reflexivity|rewrite cset_adler_avail_out; reflexivity].
Qed.

Lemma trailer_WRUN s1 s2 : DREL s1 s2 -> INV s1 -> ds_pending s1 = 0 ->
  WRUN s1 (trailer_st s1) (trailer_st s2) /\ ds_pending (trailer_st s1) <= 8.
Proof.
  intros D I1 Hp. pose proof (WRUN_start s1 s2 D I1 Hp) as W0. pose proof (DREL_clean _ _ D) as EC.
  unfold trailer_st. cbv zeta. eqc_fields EC.
  destruct (ds_wrap s1 =? 2).
  - split; [|rewrite !put_byte_pending; lia]. repeat apply WRUN_put_byte. exact W0.
  - split; [|rewrite !putShortMSB_pending; lia]. apply WRUN_putShortMSB, WRUN_putShortMSB. exact W0.
Qed.

Lemma INV_zhdr s : INV s -> INV (zhdr_st s).
Proof.
  intros I. unfold zhdr_st. cbv zeta. rewrite !putShortMSB_strstart, !putShortMSB_strm. apply INV_set_status.
  destruct (negb _); rewrite ?putShortMSB_strm;
    (apply INV_set_strm; [rewrite cset_adler_avail_in; exact (iv_ain s I) | rewrite cset_adler_avail_out; exact (iv_aout s I) |]);
    repeat apply INV_putShortMSB; exact I.
Qed.
Lemma INV_gzhdr s : INV s -> INV (gzhdr_st s).
Proof.
  intros I. unfold gzhdr_st. cbv zeta. apply INV_set_status. repeat apply INV_put_byte.
  apply INV_set_strm; [rewrite cset_adler_avail_in; exact (iv_ain s I)|rewrite cset_adler_avail_out; exact (iv_aout s I)|exact I].
Qed.
Lemma INV_trailer s : INV s -> INV (trailer_st s).
Proof. intros I. unfold trailer_st. cbv zeta. destruct (_ =? 2); [repeat apply INV_put_byte | repeat apply INV_putShortMSB]; exact I. Qed.


Local Notation Hst := stored_bf_spec.
Local Notation Hhf := (huff_bf_spec FB_CALL_ok).
Local Notation Hrl := (rle_bf_spec FB_CALL_ok).
Local Notation Hfa := (fast_bf_spec FB_CALL_ok).
Local Notation Hsl := (slow_bf_spec FB_CALL_ok).

Ltac eqc_goal EC :=
  lazymatch type of EC with clean ?s1 = clean ?s2 =>
  repeat match goal with
  | |- context [?f s2] =>
        lazymatch f with
        | ds_status => idtac | ds_pending_buf_size => idtac | ds_pending_out => idtac | ds_pending => idtac
        | ds_wrap => idtac | ds_gzhead => idtac | ds_method => idtac | ds_last_flush => idtac
        | ds_w_size => idtac | ds_w_bits => idtac | ds_w_mask => idtac | ds_window_size => idtac
        | ds_ins_h => idtac | ds_hash_size => idtac | ds_hash_bits => idtac | ds_hash_mask => idtac | ds_hash_shift => idtac
        | ds_block_start => idtac | ds_match_length => idtac | ds_match_available => idtac | ds_strstart => idtac
        | ds_lookahead => idtac | ds_prev_length => idtac | ds_max_chain_length => idtac | ds_max_lazy_match => idtac
        | ds_level => idtac | ds_strategy => idtac | ds_good_match => idtac | ds_nice_match => idtac
        | ds_lit_bufsize => idtac | ds_sym_next => idtac | ds_sym_end => idtac | ds_opt_len => idtac | ds_static_len => idtac
        | ds_matches => idtac | ds_insert => idtac | ds_bi_buf => idtac | ds_bi_valid => idtac | ds_high_water => idtac
        | ds_self_blk => idtac | ds_window_blk => idtac | ds_prev_blk => idtac | ds_head_blk => idtac | ds_pending_buf_blk => idtac
        | ds_strm => idtac
        end;
        let H := fresh in
        assert (H : f s2 = f s1) by (symmetry; apply (clean_eq_fieldT f s1 s2 EC); intros; reflexivity);
        rewrite H; clear H
  end end.

Lemma dmode_clean s1 s2 : clean s1 = clean s2 -> dmode s2 = dmode s1.
Proof. intros EC. unfold dmode. eqc_fields EC. reflexivity. Qed.

Section Core.
  Variable c0 : cstrm.
Variable s01 : deflate_state.
Variable s02 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs01 : ds_strm s01 = c0.
  Hypothesis Hs02 : ds_strm s02 = c0.
  Hypothesis D01 : dwf s01.
  Hypothesis D02 : dwf s02.

  Local Notation ST1 := (ST c0 s01).
  Local Notation ST2 := (ST c0 s02).

  Lemma rcf_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> ds_status s1 <> FINISH_STATE -> 0 <= flush <= 5 ->
    snd (run_compress_func s1 flush) = snd (run_compress_func s2 flush)
    /\ DREL (fst (run_compress_func s1 flush)) (fst (run_compress_func s2 flush))
    /\ INV (fst (run_compress_func s1 flush)) /\ INV (fst (run_compress_func s2 flush)).
  Proof.
    intros [H1 K1] [H2 K2] D I1 I2 Hp Hst0 Hfl. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hst2 : ds_status s2 <> FINISH_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact Hst0).
    assert (PRE1 : BFPRE c0 s1 flush) by (split; [exact HC0|]; split; [exact H1|]; split; [exact Hp|]; split; [exact Hst0|exact Hfl]).
    assert (PRE2 : BFPRE c0 s2 flush) by (split; [exact HC0|]; split; [exact H2|]; split; [exact Hp2|]; split; [exact Hst2|exact Hfl]).
    pose proof (dmode_clean _ _ EC) as Em.
    rewrite !run_compress_func_dmode, Em.
    pose proof (dmode_range s1) as Hm. pose proof (iv_strat s1 I1) as Sg.
    assert (NH : dmode s1 <> 1 /\ dmode s1 <> 2).
    { unfold dmode. rewrite Sg. change (0 =? Z_HUFFMAN_ONLY) with false. change (0 =? Z_RLE) with false. cbv iota.
      destruct (ds_level s1 =? 0); [lia|]. destruct (ds_level s1 <=? 3); lia. }
    destruct (Z.eq_dec (dmode s1) 0) as [E0|E0].
    { rewrite E0. pose proof (SI_intro c0 s1 flush PRE1 E0) as G1. pose proof (SI_intro c0 s2 flush PRE2 ltac:(rewrite Em; exact E0)) as G2.
      pose proof (deflate_stored_rel c0 s1 s2 flush HC0 G1 G2 (DREL_FREL0 _ _ D (dmode0_level _ E0)) I1 I2) as (E & R & J1 & J2).
      split; [exact E|]. split; [exact (FREL0_DREL _ _ R)|]. split; [exact J1|exact J2]. }
    destruct (Z.eq_dec (dmode s1) 3) as [E3|E3].
    { rewrite E3.
      assert (G1 : FTI c0 s1 s1) by (split; [exact H1|]; split; [reflexivity|]; split; [exact Hp|]; split; [exact E3|]; split; [exact Hst0|apply OUTLE_refl]).
      assert (G2 : FTI c0 s2 s2) by (split; [exact H2|]; split; [reflexivity|]; split; [exact Hp2|]; split; [rewrite Em; exact E3|]; split; [exact Hst2|apply OUTLE_refl]).
      pose proof (deflate_fast_rel c0 s1 s2 flush HC0 FB_CALL_ok flush_block_rel_blk G1 G2 (DREL_FREL _ _ D (dmode3_level _ E3)) I1 I2 Hfl) as (E & R & J1 & J2).
      split; [exact E|]. split; [exact (FREL_DREL _ _ R)|]. split; [exact J1|exact J2]. }
    assert (E4 : dmode s1 = 4) by lia. rewrite E4.
    assert (G1 : STI c0 s1 s1) by (split; [exact H1|]; split; [reflexivity|]; split; [exact Hp|]; split; [exact E4|]; split; [exact Hst0|apply OUTLE_refl]).
    assert (G2 : STI c0 s2 s2) by (split; [exact H2|]; split; [reflexivity|]; split; [exact Hp2|]; split; [rewrite Em; exact E4|]; split; [exact Hst2|apply OUTLE_refl]).
    pose proof (deflate_slow_rel c0 s1 s2 flush HC0 FB_CALL_ok flush_block_rel_blk G1 G2 (DREL_FREL _ _ D (dmode4_level _ E4)) I1 I2 Hfl) as (E & R & J1 & J2).
    split; [exact E|]. split; [exact (FREL_DREL _ _ R)|]. split; [exact J1|exact J2].
  Qed.

  Lemma bdone_st_0 s : bdone_st s 0 = tr_stored_block s None 0 0.
  Proof. reflexivity. Qed.

  Lemma tsb0_pending_range s : 0 <= ds_pending s -> ds_pending s <= ds_pending (tr_stored_block s None 0 0) <= ds_pending s + 8.
  Proof.
    intros Hp. rewrite tr_stored_block_pending. pose proof (bi_windup_pending_mono (send_bits s (Z.shiftl STORED_BLOCK 1 + 0) 3)) as A.
    pose proof (send_bits_pending_mono s (Z.shiftl STORED_BLOCK 1 + 0) 3) as B0. lia.
  Qed.

  Lemma WRUN_tsb0 s1 s2 : DREL s1 s2 -> INV s1 -> ds_pending s1 = 0 ->
    WRUN s1 (tr_stored_block s1 None 0 0) (tr_stored_block s2 None 0 0).
  Proof.
    intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) I1 Hp. pose proof (iv_po s1 I1 Hp) as Hpo.
    pose proof (tr_stored_block_rel0 W C bnd ms pm B s1 s2 None 0 0 R ltac:(lia) ltac:(intros _; reflexivity) ltac:(intros off HH0; discriminate HH0)) as R1.
    rewrite Hp in R1.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s1 None 0 0) as L.
    pose proof (k_tr_stored_block ds_sym_next true false keeps_sym_next eq_refl s1 None 0 0) as Esn.
    pose proof (k_tr_stored_block ds_strm true true keeps_strm eq_refl s1 None 0 0) as Est.
    pose proof (tsb0_pending_range s1 (iv_pend s1 I1)) as PR.
    pose proof (lzv_fields _ _ L) as F. destruct F as (_ & _ & Epo & _).
    exists W, C, B, bnd, ms, pm. split; [exact R1|].
    split; [exact HW|]. split; [exact Hb|]. split; [exact HS|]. split; [exact HH|].
    split; [exact (lzm_of_lzv _ _ L)|]. split; [exact Esn|]. split; [rewrite Epo; exact Hpo|]. split; [lia|]. rewrite Est. split; reflexivity.
  Qed.

  Lemma bdone0_rel s1 s2 :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> ds_match_available s1 = 0 ->
    let t1 := flush_pending (tr_stored_block s1 None 0 0) in let t2 := flush_pending (tr_stored_block s2 None 0 0) in
    DREL t1 t2 /\ INV t1 /\ INV t2.
  Proof.
    intros [H1 K1] [H2 K2] D I1 I2 Hp Hma. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hma2 : ds_match_available s2 = 0) by (rewrite <- (clean_eq_fieldT ds_match_available _ _ EC ltac:(reflexivity)); exact Hma).
    pose proof (bdone_facts c0 s1 0 H1 Hp Hma) as X1. pose proof (bdone_facts c0 s2 0 H2 Hp2 Hma2) as X2.
    cbv zeta in X1, X2. rewrite !bdone_st_0 in X1, X2.
    destruct X1 as (G1 & _ & _ & P1 & _). destruct X2 as (G2 & _).
    pose proof (WRUN_tsb0 s1 s2 D I1 Hp) as WR.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s1 None 0 0) as L1.
    pose proof (k_tr_stored_block lzv true true keeps_lzv eq_refl s2 None 0 0) as L2.
    assert (J1 : INV (tr_stored_block s1 None 0 0)) by (apply (INV_of_DC c0); [exact G1|apply (CFG_lzv s1); [exact L1|exact (CFG_of_INV _ I1)]]).
    assert (J2 : INV (tr_stored_block s2 None 0 0)) by (apply (INV_of_DC c0); [exact G2|apply (CFG_lzv s2); [exact L2|exact (CFG_of_INV _ I2)]]).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR J1 J2 BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.

  Lemma blocks_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4) ->
    (ds_status s1 = FINISH_STATE -> cs_avail_in (ds_strm s1) = 0) ->
    snd (deflate_blocks s1 flush) = snd (deflate_blocks s2 flush)
    /\ DQ (fst (deflate_blocks s1 flush)) (fst (deflate_blocks s2 flush))
    /\ INV (fst (deflate_blocks s1 flush)) /\ INV (fst (deflate_blocks s2 flush)).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl Hfin. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2]. pose proof H1 as [[DW1 X1] V1].
    pose proof (DREL_clean _ _ D) as EC.
    unfold deflate_blocks. eqc_fields EC.
    match goal with |- context [if ?c then _ else (s1, None)] => destruct c eqn:Hcond end.
    2:{ cbn [fst snd]. split; [reflexivity|]. split; [exact (DREL_DQ _ _ D)|]. split; [exact I1|exact I2]. }
    assert (Hst0 : ds_status s1 <> FINISH_STATE).
    { intros Ef. rewrite (Hfin Ef), (dx_fin _ X1 Ef), Ef in Hcond. cbn in Hcond. rewrite andb_false_r in Hcond. discriminate Hcond. }
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hst2 : ds_status s2 <> FINISH_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact Hst0).
    pose proof (rcf_rel s1 s2 flush HS1 HS2 D I1 I2 Hp Hst0 ltac:(lia)) as (Eb & Dr & J1 & J2).
    destruct (bf_call _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s01 HC0 s1 flush HS1 Hp Hst0 ltac:(lia)) as [_ P1].
    destruct (bf_call _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s02 HC0 s2 flush HS2 Hp2 Hst2 ltac:(lia)) as [_ P2].
    destruct (run_compress_func s1 flush) as [t1 b1]. destruct (run_compress_func s2 flush) as [t2 b2]. cbn [fst snd] in Eb, Dr, J1, J2, P1, P2. subst b2.
    unfold BFPOST in P1, P2. cbn [fst snd] in P1, P2. destruct P1 as (Ht1 & Kt1 & _ & Pbd1 & Pfin1 & Pfd1). destruct P2 as (Ht2 & Kt2 & _ & Pbd2 & Pfin2 & Pfd2).
    cbv zeta.
    set (u1 := if block_state_eqb b1 finish_started || block_state_eqb b1 finish_done then set_status t1 FINISH_STATE else t1).
    set (u2 := if block_state_eqb b1 finish_started || block_state_eqb b1 finish_done then set_status t2 FINISH_STATE else t2).
    assert (HU : DREL u1 u2 /\ INV u1 /\ INV u2 /\ (block_state_eqb b1 finish_started || block_state_eqb b1 finish_done = false -> u1 = t1 /\ u2 = t2)).
    { subst u1 u2. destruct (block_state_eqb b1 finish_started || block_state_eqb b1 finish_done).
      - split; [apply DREL_set_status; exact Dr|]. split; [apply INV_set_status; exact J1|]. split; [apply INV_set_status; exact J2|]. intros X; discriminate X.
      - split; [exact Dr|]. split; [exact J1|]. split; [exact J2|]. intros _; split; reflexivity. }
    clearbody u1 u2. destruct HU as (Du & Ku1 & Ku2 & Eu). pose proof (DREL_clean _ _ Du) as ECu.
    rewrite <- (clean_eq_fieldT ds_strm _ _ ECu ltac:(reflexivity)).
    destruct (block_state_eqb b1 need_more || block_state_eqb b1 finish_started) eqn:Enm.
    { cbn [fst snd]. split; [reflexivity|]. destruct (cs_avail_out (ds_strm u1) =? 0).
      - split; [apply DREL_DQ, DREL_set_last_flush; exact Du|]. split; apply INV_set_last_flush; assumption.
      - split; [apply DREL_DQ; exact Du|]. split; assumption. }
    destruct (block_state_eqb b1 block_done) eqn:Ebd.
    - assert (E1 : b1 = block_done) by (destruct b1; cbn in Ebd; try discriminate Ebd; reflexivity). subst b1.
      destruct (Pbd1 eq_refl) as (Hpt1 & Hnf & Hma1). cbn in Eu. destruct (Eu eq_refl) as [-> ->].
      assert (F0 : flush = 0) by (unfold Z_FINISH in Hnf; lia). subst flush.
      change (0 =? Z_PARTIAL_FLUSH) with false. change (negb (0 =? Z_BLOCK)) with true. change (0 =? Z_FULL_FLUSH) with false. cbv iota.
      assert (St1 : ST1 t1) by (split; [exact Ht1|rewrite Kt1; exact K1]). assert (St2 : ST2 t2) by (split; [exact Ht2|rewrite Kt2; exact K2]).
      pose proof (bdone0_rel t1 t2 St1 St2 Du Ku1 Ku2 Hpt1 Hma1) as (Df & Kf1 & Kf2). cbv zeta in Df, Kf1, Kf2.
      set (f1 := flush_pending (tr_stored_block t1 None 0 0)) in *. set (f2 := flush_pending (tr_stored_block t2 None 0 0)) in *. clearbody f1 f2.
      rewrite <- (clean_eq_fieldT ds_strm _ _ (DREL_clean _ _ Df) ltac:(reflexivity)).
      destruct (cs_avail_out (ds_strm f1) =? 0); cbn [fst snd].
      + split; [reflexivity|]. split; [apply DREL_DQ, DREL_set_last_flush; exact Df|]. split; apply INV_set_last_flush; assumption.
      + split; [reflexivity|]. split; [apply DREL_DQ; exact Df|]. split; assumption.
    - cbn [fst snd]. split; [reflexivity|]. split; [apply DREL_DQ; exact Du|]. split; assumption.
  Qed.

  Lemma zhdr_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> ds_status s1 = INIT_STATE ->
    let t1 := flush_pending (zhdr_st s1) in let t2 := flush_pending (zhdr_st s2) in
    DREL t1 t2 /\ INV t1 /\ INV t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp Hst. pose proof (zhdr_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (zhdr_facts c0 s1 H1 Hp Hst) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INV_zhdr _ I1) (INV_zhdr _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.
  Lemma gzhdr_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> ds_status s1 = GZIP_STATE ->
    let t1 := flush_pending (gzhdr_st s1) in let t2 := flush_pending (gzhdr_st s2) in
    DREL t1 t2 /\ INV t1 /\ INV t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp Hst. pose proof (gzhdr_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (gzhdr_facts c0 s1 H1 Hp Hst) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INV_gzhdr _ I1) (INV_gzhdr _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.
  Lemma trailer_rel0 s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 ->
    let t1 := flush_pending (trailer_st s1) in let t2 := flush_pending (trailer_st s2) in
    DREL t1 t2 /\ INV t1 /\ INV t2.
  Proof.
    intros [H1 K1] D I1 I2 Hp. pose proof (trailer_WRUN s1 s2 D I1 Hp) as [WR PL].
    pose proof (trailer_facts c0 s1 H1 Hp) as X1. cbv zeta in X1. destruct X1 as ((G1 & _ & _) & _).
    pose proof (dx_biv _ (proj2 (proj1 G1))) as BV.
    pose proof (WRUN_flush s1 _ _ WR (INV_trailer _ I1) (INV_trailer _ I2) BV ltac:(lia)) as (DR & Q1 & Q2 & _).
    cbv zeta. split; [exact DR|]. split; [exact Q1|exact Q2].
  Qed.

  Definition RQ {A} (r1 r2 : deflate_state * A) : Prop := snd r1 = snd r2 /\ DQ (fst r1) (fst r2) /\ INV (fst r1) /\ INV (fst r2).
  Lemma RQ_I {A} a1 a2 (x : A) : DQ a1 a2 -> INV a1 -> INV a2 -> RQ (a1, x) (a2, x).
  Proof. intros D I1 I2. split; [reflexivity|]. split; [exact D|]. split; [exact I1|exact I2]. Qed.
  Lemma RQ_err a1 a2 e : DQ a1 a2 -> INV a1 -> INV a2 -> RQ (err_return a1 e) (err_return a2 e).
  Proof.
    intros D I1 I2. destruct (DQ_err_return a1 a2 e D) as [E D']. split; [exact E|]. split; [exact D'|]. split; apply INV_err_return; assumption.
  Qed.

  Lemma trailer_rel s1 s2 :
    ST1 s1 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 ->
    RQ (deflate_trailer s1) (deflate_trailer s2).
  Proof.
    intros HS1 D I1 I2 Hp. rewrite !deflate_trailer_eq. cbv zeta.
    pose proof (trailer_rel0 s1 s2 HS1 D I1 I2 Hp) as (Df & J1 & J2). cbv zeta in Df, J1, J2.
    set (f1 := flush_pending (trailer_st s1)) in *. set (f2 := flush_pending (trailer_st s2)) in *. clearbody f1 f2.
    pose proof (DREL_clean _ _ Df) as EC. eqc_fields EC.
    destruct (0 <? ds_wrap f1).
    - pose proof (DREL_set_wrap _ _ (- ds_wrap f1) Df) as Dw. pose proof (DREL_clean _ _ Dw) as ECw.
      split; [cbn [snd]; dsr; eqc_fields EC; reflexivity|]. cbn [fst]. split; [apply DREL_DQ; exact Dw|]. split; apply INV_set_wrap; assumption.
    - split; [cbn [snd]; eqc_fields EC; reflexivity|]. cbn [fst]. split; [apply DREL_DQ; exact Df|]. split; assumption.
  Qed.

  Definition core_fin (s : deflate_state) (flush : Z) : deflate_state * Z :=
    let '(s, r) := deflate_blocks s flush in
    match r with Some rc => (s, rc) | None =>
    if negb (Z.eqb flush Z_FINISH) then (s, Z_OK)
    else if Z.leb (ds_wrap s) 0 then (s, Z_STREAM_END)
    else deflate_trailer s
    end.

  Lemma fin_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4) ->
    (ds_status s1 = FINISH_STATE -> cs_avail_in (ds_strm s1) = 0) ->
    RQ (core_fin s1 flush) (core_fin s2 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl Hfin. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    assert (Hfin2 : ds_status s2 = FINISH_STATE -> cs_avail_in (ds_strm s2) = 0).
    { rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)), <- (clean_eq_fieldT ds_strm _ _ EC ltac:(reflexivity)). exact Hfin. }
    pose proof (blocks_rel s1 s2 flush HS1 HS2 D I1 I2 Hp Hfl Hfin) as (Eb & Db & Jb1 & Jb2).
    destruct (blocks_stage _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s01 HC0 Hs01 D01 s1 flush HS1 Hp ltac:(lia) Hfin) as (_ & HSr1 & Hr1).
    destruct (blocks_stage _ _ _ _ Hst Hhf Hrl Hfa Hsl c0 s02 HC0 Hs02 D02 s2 flush HS2 Hp2 ltac:(lia) Hfin2) as (_ & HSr2 & Hr2).
    unfold core_fin.
    destruct (deflate_blocks s1 flush) as [b1 r1]. destruct (deflate_blocks s2 flush) as [b2 r2]. cbn [fst snd] in Eb, Db, Jb1, Jb2, HSr1, Hr1, HSr2, Hr2. subst r2.
    destruct r1 as [rc|]; [apply RQ_I; assumption|].
    destruct (Hr1 eq_refl) as [Hpb1 _].
    pose proof (DQ_clean _ _ Db) as ECb. eqc_fields ECb.
    destruct (negb (flush =? Z_FINISH)); [apply RQ_I; assumption|].
    destruct (ds_wrap b1 <=? 0); [apply RQ_I; assumption|].
    pose proof HSr1 as [[[_ Xb1] _] _].
    apply trailer_rel; [exact HSr1|apply DQ_DREL; [exact Db|exact Hpb1|exact (dx_pout0 _ Xb1 Hpb1)]|exact Jb1|exact Jb2|exact Hpb1].
  Qed.

  Definition core_tail (s : deflate_state) (flush : Z) : deflate_state * Z :=
    if Z.eqb (ds_status s) FINISH_STATE && negb (Z.eqb (cs_avail_in (ds_strm s)) 0)
    then err_return s Z_BUF_ERROR
    else
    let s := if Z.eqb (ds_status s) INIT_STATE && Z.eqb (ds_wrap s) 0 then set_status s BUSY_STATE else s in
    let '(s, r) := if Z.eqb (ds_status s) INIT_STATE then deflate_zlib_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    let '(s, r) := if Z.eqb (ds_status s) GZIP_STATE then deflate_gzip_header s else (s, None) in
    match r with Some rc => (s, rc) | None =>
    core_fin s flush
    end end.

  Lemma core_tail_rel s1 s2 flush :
    ST1 s1 -> ST2 s2 -> DREL s1 s2 -> INV s1 -> INV s2 -> ds_pending s1 = 0 -> (flush = 0 \/ flush = 4) ->
    RQ (core_tail s1 flush) (core_tail s2 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hp Hfl. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2]. pose proof (DREL_clean _ _ D) as EC.
    assert (Hp2 : ds_pending s2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ EC ltac:(reflexivity)); exact Hp).
    unfold core_tail. eqc_fields EC.
    destruct ((ds_status s1 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s1) =? 0)) eqn:Efa; [apply RQ_err; [apply DREL_DQ; exact D|exact I1|exact I2]|].
    assert (Hnf : ~ (ds_status s1 = FINISH_STATE /\ cs_avail_in (ds_strm s1) <> 0)).
    { intros [A1 A2]. rewrite A1 in Efa. cbn in Efa. destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0); [exact (A2 ltac:(assumption))|discriminate Efa]. }
    cbv zeta.
    set (v1 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s1 BUSY_STATE else s1).
    set (v2 := if (ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0) then set_status s2 BUSY_STATE else s2).
    assert (HV : ST1 v1 /\ ST2 v2 /\ DREL v1 v2 /\ INV v1 /\ INV v2 /\ ds_pending v1 = 0
                 /\ cs_avail_in (ds_strm v1) = cs_avail_in (ds_strm s1) /\ (ds_status v1 = FINISH_STATE -> ds_status s1 = FINISH_STATE)).
    { subst v1 v2. destruct ((ds_status s1 =? INIT_STATE) && (ds_wrap s1 =? 0)) eqn:E.
      - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
        assert (E1' : ds_status s2 = INIT_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ EC ltac:(reflexivity)); exact E1).
        assert (E2' : ds_wrap s2 = 0) by (rewrite <- (clean_eq_fieldT ds_wrap _ _ EC ltac:(reflexivity)); exact E2).
        destruct (DC_set_status c0 s1 BUSY_STATE H1 ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (G1 & KG1 & _).
        destruct (DC_set_status c0 s2 BUSY_STATE H2 ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (G2 & KG2 & _).
        split; [split; [exact G1|rewrite KG1; exact K1]|]. split; [split; [exact G2|rewrite KG2; exact K2]|].
        split; [apply DREL_set_status; exact D|]. split; [apply INV_set_status; exact I1|]. split; [apply INV_set_status; exact I2|].
        dsr. split; [exact Hp|]. split; [reflexivity|]. unfold BUSY_STATE, FINISH_STATE. intros; lia.
      - split; [exact HS1|]. split; [exact HS2|]. split; [exact D|]. split; [exact I1|]. split; [exact I2|]. split; [exact Hp|]. split; [reflexivity|]. intros X; exact X. }
    clearbody v1 v2. destruct HV as (HSv1 & HSv2 & Dv & Iv1 & Iv2 & Hpv & Aiv & Finv).
    pose proof (DREL_clean _ _ Dv) as ECv. eqc_fields ECv.
    assert (Hpv2 : ds_pending v2 = 0) by (rewrite <- (clean_eq_fieldT ds_pending _ _ ECv ltac:(reflexivity)); exact Hpv).
    destruct (Z.eqb_spec (ds_status v1) INIT_STATE) as [Ei|Ei].
    - assert (Ei2 : ds_status v2 = INIT_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ ECv ltac:(reflexivity)); exact Ei).
      rewrite !deflate_zlib_header_eq. cbv zeta.
      pose proof (zhdr_rel v1 v2 HSv1 Dv Iv1 Iv2 Hpv Ei) as (Dz & Kz1 & Kz2). cbv zeta in Dz, Kz1, Kz2.
      destruct (hdr_zlib c0 s01 HC0 Hs01 D01 v1 HSv1 Hpv Ei) as (_ & HSz1 & Stz1 & Horz1 & Aiz1 & _).
      destruct (hdr_zlib c0 s02 HC0 Hs02 D02 v2 HSv2 Hpv2 Ei2) as (_ & HSz2 & _).
      set (z1 := flush_pending (zhdr_st v1)) in *. set (z2 := flush_pending (zhdr_st v2)) in *. clearbody z1 z2.
      pose proof (DREL_clean _ _ Dz) as ECz. eqc_fields ECz.
      destruct (Z.eqb_spec (ds_pending z1) 0) as [Pz|Pz]; cbn [negb]; eqc_fields ECz.
      + rewrite Stz1. change (BUSY_STATE =? GZIP_STATE) with false. cbn [negb].
        apply fin_rel; [exact HSz1|exact HSz2|exact Dz|exact Kz1|exact Kz2|exact Pz|exact Hfl|].
        rewrite Stz1. unfold BUSY_STATE, FINISH_STATE. intros; lia.
      + apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Dz|apply INV_set_last_flush; exact Kz1|apply INV_set_last_flush; exact Kz2].
    - cbn [negb]. eqc_fields ECv.
      destruct (Z.eqb_spec (ds_status v1) GZIP_STATE) as [Eg|Eg].
      + assert (Eg2 : ds_status v2 = GZIP_STATE) by (rewrite <- (clean_eq_fieldT ds_status _ _ ECv ltac:(reflexivity)); exact Eg).
        rewrite !deflate_gzip_header_eq. cbv zeta.
        pose proof (gzhdr_rel v1 v2 HSv1 Dv Iv1 Iv2 Hpv Eg) as (Dz & Kz1 & Kz2). cbv zeta in Dz, Kz1, Kz2.
        destruct (hdr_gzip c0 s01 HC0 Hs01 D01 v1 HSv1 Hpv Eg) as (_ & HSz1 & Stz1 & Horz1 & Aiz1 & _).
        destruct (hdr_gzip c0 s02 HC0 Hs02 D02 v2 HSv2 Hpv2 Eg2) as (_ & HSz2 & _).
        set (z1 := flush_pending (gzhdr_st v1)) in *. set (z2 := flush_pending (gzhdr_st v2)) in *. clearbody z1 z2.
        pose proof (DREL_clean _ _ Dz) as ECz. eqc_fields ECz.
        destruct (Z.eqb_spec (ds_pending z1) 0) as [Pz|Pz]; cbn [negb]; eqc_fields ECz.
        * apply fin_rel; [exact HSz1|exact HSz2|exact Dz|exact Kz1|exact Kz2|exact Pz|exact Hfl|].
          rewrite Stz1. unfold BUSY_STATE, FINISH_STATE. intros; lia.
        * apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Dz|apply INV_set_last_flush; exact Kz1|apply INV_set_last_flush; exact Kz2].
      + cbn [negb]. apply fin_rel; [exact HSv1|exact HSv2|exact Dv|exact Iv1|exact Iv2|exact Hpv|exact Hfl|].
        intros Ef. rewrite Aiv. destruct (Z.eq_dec (cs_avail_in (ds_strm s1)) 0) as [A|A]; [exact A|]. exfalso. apply Hnf. split; [exact (Finv Ef)|exact A].
  Qed.

  Lemma core_rel flush :
    ST1 s01 -> ST2 s02 -> DQ s01 s02 -> INV s01 -> INV s02 -> (flush = 0 \/ flush = 4) ->
    RQ (deflate_core s01 flush) (deflate_core s02 flush).
  Proof.
    intros HS1 HS2 D I1 I2 Hfl. pose proof HS1 as [H1 K1]. pose proof HS2 as [H2 K2].
    pose proof (DQ_clean _ _ D) as EC.
    unfold deflate_core. rewrite <- (clean_eq_fieldT deflateStateCheck _ _ EC ltac:(intros; reflexivity)). eqc_goal EC.
    destruct (deflateStateCheck s01 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk; [apply RQ_I; assumption|].
    destruct ((ds_status s01 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply RQ_err; assumption|].
    destruct (Z.eqb_spec (cs_avail_out (ds_strm s01)) 0) as [Hao|Hao]; [apply RQ_err; assumption|].
    cbv zeta.
    pose proof (ST_set_last_flush c0 s01 s01 flush HS1 ltac:(lia)) as HSu1.
    pose proof (ST_set_last_flush c0 s02 s02 flush HS2 ltac:(lia)) as HSu2.
    pose proof (DQ_set_last_flush _ _ flush D) as Du. pose proof (INV_set_last_flush s01 flush I1) as Iu1. pose proof (INV_set_last_flush s02 flush I2) as Iu2.
    set (u1 := set_last_flush s01 flush) in *. set (u2 := set_last_flush s02 flush) in *. clearbody u1 u2.
    pose proof HSu1 as [Hu1 Ku1]. pose proof Hu1 as [[DWu1 Xu1] Vu1].
    pose proof (DQ_clean _ _ Du) as ECu. eqc_fields ECu.
    destruct (Z.eqb_spec (ds_pending u1) 0) as [Ep|Ep]; cbn [negb].
    -
      destruct ((cs_avail_in (ds_strm u1) =? 0) && (RANK flush <=? RANK (ds_last_flush s01)) && negb (flush =? Z_FINISH)).
      + unfold err_return. cbn [negb]. apply RQ_err; assumption.
      + apply core_tail_rel; [exact HSu1|exact HSu2|apply DQ_DREL; [exact Du|exact Ep|exact (dx_pout0 _ Xu1 Ep)]|exact Iu1|exact Iu2|exact Ep|exact Hfl].
    -
      destruct Du as (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH).
      pose proof (df_pend _ DWu1) as (PO0 & _ & PLE). rewrite (iv_lbs _ Iu1) in PLE.
      pose proof (bi_flush_noop u1 (dx_biv _ Xu1)) as NB.
      pose proof (flush_pending_DREL W C B bnd ms pm u1 u2 R Iu1 Iu2 HW Hb HS HH PO0 HP (or_intror NB) ltac:(rewrite NB; lia)) as (Df & Jf1 & Jf2 & _).
      destruct (ST_flush_pending c0 s01 HC0 u1 HSu1) as (HSf1 & _ & Hor1 & _).
      destruct (ST_flush_pending c0 s02 HC0 u2 HSu2) as (HSf2 & _).
      set (f1 := flush_pending u1) in *. set (f2 := flush_pending u2) in *. clearbody f1 f2.
      pose proof (DREL_clean _ _ Df) as ECf. eqc_fields ECf.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm f1)) 0) as [Ea|Ea]; cbn [negb].
      + apply RQ_I; [apply DREL_DQ, DREL_set_last_flush; exact Df|apply INV_set_last_flush; exact Jf1|apply INV_set_last_flush; exact Jf2].
      + assert (Hpf : ds_pending f1 = 0) by (destruct Hor1 as [X|X]; [exact X|exfalso; exact (Ea X)]).
        apply core_tail_rel; [exact HSf1|exact HSf2|exact Df|exact Jf1|exact Jf2|exact Hpf|exact Hfl].
  Qed.
End Core.


Lemma cstrm_of_call_avail_in zc : cs_avail_in (cstrm_of_call zc) = zlength (zc_input zc).
Proof. reflexivity. Qed.
Lemma cstrm_of_call_avail_out zc : cs_avail_out (cstrm_of_call zc) = zc_avail_out zc.
Proof. reflexivity. Qed.

Theorem deflate_m_rel : DEFLATE_M_REL.
Proof.
  intros s1 s2 zc flush (D & I1 & I2 & R1 & R2) Hzc Hfl.
  assert (Hfl' : flush = 0 \/ flush = 4) by (unfold Z_NO_FLUSH, Z_FINISH in Hfl; exact Hfl).
  pose proof (DR_deflate s1 zc flush (fst (deflate_m s1 zc flush)) (snd (deflate_m s1 zc flush)) R1 Hzc ltac:(lia) (surjective_pairing _)) as R1'.
  pose proof (DR_deflate s2 zc flush (fst (deflate_m s2 zc flush)) (snd (deflate_m s2 zc flush)) R2 Hzc ltac:(lia) (surjective_pairing _)) as R2'.
  revert R1' R2'. unfold deflate_m.
  set (c0 := cstrm_of_call zc).
  pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
  pose proof (dreach_DD _ R1) as DD1. pose proof (dreach_DD _ R2) as DD2.
  assert (G1 : DC c0 (set_strm s1 c0)) by (split; [apply DD_set_strm; exact DD1 | subst c0; apply SV_entry; exact Hzc]).
  assert (G2 : DC c0 (set_strm s2 c0)) by (split; [apply DD_set_strm; exact DD2 | subst c0; apply SV_entry; exact Hzc]).
  assert (HS1 : ST c0 (set_strm s1 c0) (set_strm s1 c0)) by (split; [exact G1|reflexivity]).
  assert (HS2 : ST c0 (set_strm s2 c0) (set_strm s2 c0)) by (split; [exact G2|reflexivity]).
  pose proof (DQ_set_strm s1 s2 c0 D) as Du.
  assert (Ain : 0 <= cs_avail_in c0) by (subst c0; rewrite cstrm_of_call_avail_in; unfold zlength; lia).
  assert (Aout : 0 <= cs_avail_out c0) by (subst c0; rewrite cstrm_of_call_avail_out; destruct Hzc as (_ & Hao & _); lia).
  pose proof (INV_set_strm s1 c0 Ain Aout I1) as Iu1. pose proof (INV_set_strm s2 c0 Ain Aout I2) as Iu2.
  pose proof (core_rel c0 (set_strm s1 c0) (set_strm s2 c0) HC0 eq_refl eq_refl (proj1 (proj1 G1)) (proj1 (proj1 G2)) flush HS1 HS2 Du Iu1 Iu2 Hfl') as (E & Dq & J1 & J2).
  destruct (deflate_core (set_strm s1 c0) flush) as [t1 rc1]. destruct (deflate_core (set_strm s2 c0) flush) as [t2 rc2].
  cbn [fst snd] in E, Dq, J1, J2 |- *. subst rc2. intros R1' R2'.
  split; [rewrite (clean_eq_fieldT ds_strm _ _ (DQ_clean _ _ Dq) ltac:(reflexivity)); reflexivity|].
  split; [exact Dq|]. split; [exact J1|]. split; [exact J2|]. split; [exact R1'|exact R2'].
Qed.
