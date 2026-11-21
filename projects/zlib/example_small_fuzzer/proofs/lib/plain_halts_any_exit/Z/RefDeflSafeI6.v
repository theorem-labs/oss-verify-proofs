(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayCoreL.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.

Module RefDeflSafeI5.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateDictM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLW0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma setdict_inner_S' : forall k t str m,
  setdict_inner (S k) t str m =
  (if negb (m - 1 =? 0) then setdict_inner k (fst (insert_string t str)) (str + 1) (m - 1)
   else (fst (insert_string t str), str + 1)).
Proof. intros. reflexivity. Qed.

Definition sd_fuel (f : nat) (t : deflate_state) : Prop :=
  cs_avail_in (ds_strm t) + 1 + (if MIN_MATCH <=? ds_lookahead t then 1 else 0) <= Z.of_nat f.

Section Loops.
  Variables ws hs wk : Z.
  Hypothesis Hwk : 0 <= wk /\ ws = 2 ^ wk.

  Lemma insert1_facts : forall (c : bool) u str,
    fw_wf ws hs u -> 0 <= str < 2 ^ 16 ->
    (c = true -> CHAIN u (str - 1) (str - 1)) ->
    let u' := fst (insert_string u str) in
    fw_wf ws hs u' /\ 0 <= ds_ins_h u' < 65536 /\ (c = true -> CHAIN u' str str)
    /\ ds_strm u' = ds_strm u /\ ds_lookahead u' = ds_lookahead u /\ ds_strstart u' = ds_strstart u
    /\ ds_insert u' = ds_insert u /\ ds_high_water u' = ds_high_water u /\ ds_window_size u' = ds_window_size u.
  Proof.
    intros c u str HW Hstr Hc u'. subst u'.
    pose proof (wf_hmask _ _ _ HW) as Vhm. pose proof (wf_hsr _ _ _ HW) as Lhs. pose proof (wf_hs _ _ _ HW) as Vhs.
    pose proof (wf_ws _ _ _ HW) as Vws. pose proof (wf_wmask _ _ _ HW) as Vwm. pose proof (wf_pl _ _ _ HW) as Vpl.
    pose proof (wf_hl _ _ _ HW) as Vhl. pose proof (wf_wsr _ _ _ HW) as Lws.
    assert (Hh : 0 <= update_hash u (ds_ins_h u) (arr_get (ds_window u) (str + (MIN_MATCH - 1))) <= ds_hash_mask u).
    { apply update_hash_range. rewrite Vhm. lia. }
    assert (HC : c = true -> CHAIN (fst (insert_string u str)) str str).
    { intros Ec. destruct (CHAIN_insert_string u str (str - 1) (str - 1) wk (Hc Ec)
                  ltac:(rewrite Vws; lia) ltac:(lia) ltac:(rewrite Vwm, Vws; reflexivity) ltac:(rewrite Vpl, Vws; reflexivity)
                  ltac:(rewrite Vhl, Vhs; reflexivity) ltac:(rewrite Vhm; lia) ltac:(rewrite Vhm, Vhs; reflexivity) ltac:(lia)) as [H _].
      replace (Z.max (str - 1) str) with str in H by lia. replace (Z.max (str - 1) (str - 1)) with (str - 1) in H by lia.
      apply (CHAIN_mono _ str (str - 1)); [lia | lia | exact H]. }
    revert HC. rewrite insert_string_fst. cbv zeta. intros HC.
    split.
    { destruct HW; constructor; dsred; try assumption; try lia.
      - rewrite arr_len_set. assumption.
      - rewrite arr_len_set. assumption.
      - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wf_hb; rewrite Vhm in Hh; lia | apply wf_pb; exact Hi].
      - intros i Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply wf_hb; exact Hi]. }
    split; [dsred; rewrite Vhm in Hh; lia|].
    split; [exact HC|].
    dsred. repeat split; reflexivity.
  Qed.

  Lemma inner_facts : forall (c : bool) k u str m,
    k = Z.to_nat m -> 1 <= m -> 0 <= str -> str + m <= 2 ^ 16 ->
    fw_wf ws hs u -> 0 <= ds_ins_h u < 65536 ->
    (c = true -> CHAIN u (str - 1) (str - 1)) ->
    let r := setdict_inner k u str m in
    fw_wf ws hs (fst r) /\ 0 <= ds_ins_h (fst r) < 65536 /\ (c = true -> CHAIN (fst r) (str + m - 1) (str + m - 1))
    /\ snd r = str + m
    /\ ds_strm (fst r) = ds_strm u /\ ds_lookahead (fst r) = ds_lookahead u /\ ds_strstart (fst r) = ds_strstart u
    /\ ds_insert (fst r) = ds_insert u /\ ds_high_water (fst r) = ds_high_water u /\ ds_window_size (fst r) = ds_window_size u.
  Proof.
    intros c k. induction k as [|k IH]; intros u str m Hk Hm Hstr Hsm HW Hih Hc r; subst r; [lia|].
    rewrite setdict_inner_S'.
    pose proof (insert1_facts c u str HW ltac:(lia) Hc) as F. cbv zeta in F.
    destruct F as (W1 & I1 & C1 & E1 & E2 & E3 & E4 & E5 & E6).
    set (u1 := fst (insert_string u str)) in *.
    destruct (Z.eqb_spec (m - 1) 0) as [M|M]; cbn [negb].
    - cbn [fst snd]. replace (str + m - 1) with str by lia. replace (str + m) with (str + 1) by lia.
      split; [exact W1|]. split; [exact I1|]. split; [exact C1|]. split; [reflexivity|].
      split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5 | exact E6].
    - pose proof (IH u1 (str + 1) (m - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) W1 I1
                    ltac:(intros Ec; replace (str + 1 - 1) with str by lia; exact (C1 Ec))) as R. cbv zeta in R.
      destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
      replace (str + 1 + (m - 1) - 1) with (str + m - 1) in R3 by lia. replace (str + 1 + (m - 1)) with (str + m) in R4 by lia.
      rewrite E1 in R5. rewrite E2 in R6. rewrite E3 in R7. rewrite E4 in R8. rewrite E5 in R9. rewrite E6 in R10.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
      split; [exact R5|]. split; [exact R6|]. split; [exact R7|]. split; [exact R8|]. split; [exact R9 | exact R10].
  Qed.

  Definition sd_trip (t : deflate_state) : deflate_state :=
    let n := ds_lookahead t - (MIN_MATCH - 1) in
    let r := setdict_inner (Z.to_nat n) t (ds_strstart t) n in
    set_lookahead (set_strstart (fst r) (snd r)) (MIN_MATCH - 1).

  Lemma sd_trip_facts : forall (c : bool) t,
    fw_wf ws hs t -> 0 <= ds_ins_h t < 65536 -> MIN_MATCH <= ds_lookahead t ->
    (c = true -> CHAIN t (ds_strstart t - 1) (ds_strstart t - 1)) ->
    let t1 := sd_trip t in
    fw_wf ws hs t1 /\ 0 <= ds_ins_h t1 < 65536 /\ (c = true -> CHAIN t1 (ds_strstart t1 - 1) (ds_strstart t1 - 1))
    /\ ds_strm t1 = ds_strm t /\ ds_lookahead t1 = MIN_MATCH - 1
    /\ ds_insert t1 = ds_insert t /\ ds_high_water t1 = ds_high_water t /\ ds_window_size t1 = ds_window_size t.
  Proof.
    intros c t HW Hih Hl Hc t1. subst t1. unfold sd_trip. cbv zeta.
    pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_wsr _ _ _ HW) as Lws.
    unfold MIN_MATCH in *.
    pose proof (inner_facts c (Z.to_nat (ds_lookahead t - (3 - 1))) t (ds_strstart t) (ds_lookahead t - (3 - 1))
                  eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HW Hih Hc) as R. cbv zeta in R.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
    set (u := fst (setdict_inner _ _ _ _)) in *. rewrite R4.
    split.
    { destruct R1; constructor; dsred; try assumption; try lia. }
    split; [dsred; exact R2|].
    split; [intros Ec; dsred; replace (ds_strstart t + (ds_lookahead t - (3 - 1)) - 1) with (ds_strstart t + (ds_lookahead t - (3 - 1)) - 1) by lia;
            apply (CHAIN_same u); dsred; try reflexivity; exact (R3 Ec)|].
    dsred. rewrite R5, R8, R9, R10. repeat split; reflexivity.
  Qed.

  Lemma setdict_outer_S' : forall f t,
    setdict_outer (S f) t = (if MIN_MATCH <=? ds_lookahead t then setdict_outer f (fill_window (sd_trip t)) else t).
  Proof. intros f t. rewrite setdict_outer_S. reflexivity. Qed.

  Section Outer.
    Variable P : deflate_state -> Prop.
    Hypothesis HPtrip : forall t, fw_wf ws hs t -> P t -> MIN_MATCH <= ds_lookahead t -> fw_wf ws hs (sd_trip t) /\ P (sd_trip t).
    Hypothesis HPfw : forall t, fw_wf ws hs t -> P t -> ds_lookahead t < MIN_LOOKAHEAD -> P (fill_window t).

    Lemma setdict_outer_P : forall f t, fw_wf ws hs t -> P t -> sd_fuel f t ->
      let t' := setdict_outer f t in fw_wf ws hs t' /\ P t' /\ ds_lookahead t' < MIN_MATCH.
    Proof.
      induction f as [|f IH]; intros t HW HP Hf t'; subst t'.
      - exfalso. unfold sd_fuel in Hf. pose proof (wf_ai _ _ _ HW). destruct (_ <=? _); cbn in Hf; lia.
      - rewrite setdict_outer_S'. unfold sd_fuel in Hf.
        destruct (Z.leb_spec MIN_MATCH (ds_lookahead t)) as [GE|LT]; [| split; [exact HW | split; [exact HP | exact LT]]].
        destruct (HPtrip t HW HP GE) as [HW1 HP1].
        assert (L1 : ds_lookahead (sd_trip t) = MIN_MATCH - 1 /\ ds_strm (sd_trip t) = ds_strm t).
        { unfold sd_trip. cbv zeta. dsred.
          pose proof (proj1 (setdict_inner_eq (Z.to_nat (ds_lookahead t - (MIN_MATCH - 1))) t (ds_strstart t) (ds_lookahead t - (MIN_MATCH - 1)))) as E.
          rewrite E. unfold sdput3. dsred. split; reflexivity. }
        destruct L1 as [L1 S1].
        pose proof (fill_window_facts ws hs (sd_trip t) HW1 ltac:(rewrite L1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia)) as F.
        cbv zeta in F. destruct F as (HW2 & _ & _ & HL2 & HA2 & _).
        pose proof (HPfw (sd_trip t) HW1 HP1 ltac:(rewrite L1; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia)) as HP2.
        apply (IH _ HW2 HP2). unfold sd_fuel. rewrite HA2, S1. rewrite L1 in HL2 |- *.
        replace (if MIN_MATCH <=? ds_lookahead t then 1 else 0) with 1 in Hf by (symmetry; destruct (Z.leb_spec MIN_MATCH (ds_lookahead t)); [reflexivity | lia]).
        destruct (Z.leb_spec MIN_MATCH (ds_lookahead (fill_window (sd_trip t)))); unfold MIN_MATCH in *; lia.
    Qed.
  End Outer.

  Lemma sd_trip_FWX : forall t, fw_wf ws hs t -> FWX t -> MIN_MATCH <= ds_lookahead t -> fw_wf ws hs (sd_trip t) /\ FWX (sd_trip t).
  Proof.
    intros t HW X Hl.
    pose proof (sd_trip_facts true t HW (fx_insh _ X) Hl (fun _ => fx_chain _ X)) as R. cbv zeta in R.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    split; [exact R1|]. constructor.
    - exact (R3 eq_refl).
    - exact R2.
    - rewrite R6, (wf_ws _ _ _ R1). rewrite <- (wf_ws _ _ _ HW). exact (fx_ins _ X).
    - rewrite R7, R8. exact (fx_hw _ X).
    - rewrite R4. exact (fx_ad _ X).
  Qed.

  Lemma setdict_outer_FWX : forall f t, fw_wf ws hs t -> FWX t -> sd_fuel f t ->
    let t' := setdict_outer f t in fw_wf ws hs t' /\ FWX t' /\ ds_lookahead t' < MIN_MATCH.
  Proof.
    apply (setdict_outer_P FWX sd_trip_FWX).
    intros t HW X Hl. exact (proj1 (fill_window_FWX ws hs wk Hwk t HW X Hl)).
  Qed.

  Lemma sd_trip_FWX0 : forall t, fw_wf ws hs t -> FWX0 t -> MIN_MATCH <= ds_lookahead t -> fw_wf ws hs (sd_trip t) /\ FWX0 (sd_trip t).
  Proof.
    intros t HW X Hl.
    pose proof (sd_trip_facts false t HW (fx0_insh _ X) Hl ltac:(intros E; discriminate E)) as R. cbv zeta in R.
    destruct R as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    split; [exact R1|]. constructor.
    - exact R2.
    - rewrite R7, R8. exact (fx0_hw _ X).
  Qed.

  Lemma setdict_outer_FWX0 : forall f t, fw_wf ws hs t -> FWX0 t -> sd_fuel f t ->
    let t' := setdict_outer f t in fw_wf ws hs t' /\ FWX0 t' /\ ds_lookahead t' < MIN_MATCH.
  Proof.
    apply (setdict_outer_P FWX0 sd_trip_FWX0).
    intros t HW X Hl. exact (fill_window_FWX0 ws hs t HW X Hl).
  Qed.
End Loops.


Lemma bytes_okP_zskipn : forall k l, bytes_okP l -> bytes_okP (zskipn k l).
Proof.
  intros k l H. unfold zskipn, bytes_okP in *. rewrite Forall_forall in H |- *. intros x Hx. apply H.
  rewrite <- (firstn_skipn (Z.to_nat k) l). apply in_app_iff. right. exact Hx.
Qed.

Lemma zlength_zskipn' : forall (l : list Z) k, 0 <= k <= zlength l -> zlength (zskipn k l) = zlength l - k.
Proof. intros l k Hk. unfold zskipn, zlength in *. rewrite length_skipn. lia. Qed.

Lemma dwf_set_wrap : forall s w, - 2 <= w <= 2 -> dwf s -> dwf (set_wrap s w).
Proof. intros s w Hw D. destruct D; constructor; dsred; try assumption. Qed.

Lemma head_cleared : forall s h, arr_len (ds_head s) = ds_hash_size s -> 0 <= h < ds_hash_size s ->
  arr_get (arr_fill (arr_set (ds_head s) (ds_hash_size s - 1) NIL) 0 (ds_hash_size s - 1) 0) h = 0.
Proof.
  intros s h Hhl Hh. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hhl.
  destruct (Z_lt_le_dec h (ds_hash_size s - 1)).
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with false
      by (symmetry; apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    replace h with (ds_hash_size s - 1) by lia. rewrite arr_get_set_same by (rewrite Hhl; lia). reflexivity.
Qed.

Lemma dwf_sd_clear : forall s, dwf s -> ds_lookahead s = 0 -> dwf (sd_clear s).
Proof.
  intros s D Hl. pose proof (df_hl _ D) as Hhl. pose proof (dwf_sizes s D) as (Sw & Sh & _).
  unfold sd_clear, clear_hash. destruct D; constructor; dsred; try assumption; try lia.
  - rewrite arr_len_fill, arr_len_set. assumption.
  - intros i Hi. rewrite (head_cleared s i Hhl Hi). lia.
Qed.

Lemma sd_split_cases : forall w s2 dict s3 dict',
  sd_split w s2 dict = (s3, dict') ->
  s3 = (if (ds_w_size s2 <=? zlength dict) && (w =? 0) then sd_clear s2 else s2)
  /\ (dict' = dict \/ (ds_w_size s2 <= zlength dict /\ dict' = zskipn (zlength dict - ds_w_size s2) dict)).
Proof.
  intros w s2 dict s3 dict' E. unfold sd_split in E.
  destruct (Z.leb_spec (ds_w_size s2) (zlength dict)) as [Le|Gt]; cbn [andb] in *.
  - destruct (w =? 0); apply pair_equal_spec in E; destruct E as [E1 E2]; subst s3 dict'.
    + split; [reflexivity | right; split; [exact Le | reflexivity]].
    + split; [reflexivity | right; split; [exact Le | reflexivity]].
  - apply pair_equal_spec in E; destruct E as [E1 E2]; subst s3 dict'. split; [reflexivity | left; reflexivity].
Qed.

Lemma sd_s2_facts : forall s zc dict, DD s -> zstrm_okP (zc_strm zc) -> bytes_okP dict ->
  let s2 := sd_s2 (set_strm s (cstrm_of_call zc)) dict in
  dwf s2 /\ SDK s s2 /\ ds_wrap s2 = 0 /\ ds_lookahead s2 = ds_lookahead s /\ ds_ins_h s2 = ds_ins_h s /\ ds_high_water s2 = ds_high_water s
  /\ ds_window_size s2 = ds_window_size s /\ ds_insert s2 = ds_insert s
  /\ ds_head s2 = ds_head s /\ ds_prev s2 = ds_prev s /\ ds_strstart s2 = ds_strstart s /\ ds_hash_size s2 = ds_hash_size s
  /\ ds_w_size s2 = ds_w_size s /\ ds_w_mask s2 = ds_w_mask s
  /\ 0 <= cs_adler (ds_strm s2) < 2 ^ 64 /\ 0 <= cs_total_in (ds_strm s2) < 2 ^ 64.
Proof.
  intros s zc dict [D X] (Ht1 & Ht2 & Had & Hdt) Hb s2. subst s2.
  assert (Hadl : 0 <= adler32_upd (zs_adler (zc_strm zc)) dict < 2 ^ 64).
  { apply adler32_upd_range. intros b Hin. unfold bytes_okP in Hb. rewrite Forall_forall in Hb. exact (Hb b Hin). }
  unfold sd_s2, set_strm. cbn [ds_wrap ds_strm]. destruct (ds_wrap s =? 1); dsred; unfold cstrm_of_call; cbn [cs_adler cs_total_in].
  all: split; [destruct D; constructor; dsred; try assumption; lia|].
  all: split; [unfold SDK, sdput; dsred; destruct s; reflexivity|].
  all: repeat (split; [reflexivity|]).
  all: split; [first [exact Hadl | exact Had] | exact Ht1].
Qed.

Lemma sd_clear_facts : forall t, dwf t -> ds_lookahead t = 0 ->
  let t' := sd_clear t in
  dwf t' /\ SDK t t' /\ ds_wrap t' = ds_wrap t /\ ds_lookahead t' = 0 /\ ds_ins_h t' = ds_ins_h t /\ ds_high_water t' = ds_high_water t
  /\ ds_window_size t' = ds_window_size t /\ ds_insert t' = 0 /\ ds_strstart t' = 0 /\ ds_strm t' = ds_strm t
  /\ (forall BH BP, CHAIN t' BH BP).
Proof.
  intros t D Hl t'. subst t'. pose proof (df_hl _ D) as Hhl. pose proof (dwf_sizes t D) as (Sw & Sh & _).
  unfold sd_clear, clear_hash. dsred.
  split. { destruct D; constructor; dsred; try assumption; try lia.
           - rewrite arr_len_fill, arr_len_set. assumption.
           - intros i Hi. rewrite (head_cleared t i Hhl Hi). lia. }
  split; [unfold SDK, sdput; dsred; destruct t; reflexivity|].
  repeat (split; [first [reflexivity | exact Hl]|]).
  intros BH BP. apply CHAIN_heads0. dsred. intros h Hh. apply head_cleared; [exact Hhl | exact Hh].
Qed.

Section SetDict.
  Variable s : deflate_state.
Variable zc : ZCall.
Variable dict : list Z.
  Hypothesis HDD : DD s.
  Hypothesis Hz : zstrm_okP (zc_strm zc).
  Hypothesis Hb : bytes_okP dict.
  Hypothesis Hlen : 0 < zlength dict < 2 ^ 32.

  Let s0 : deflate_state := set_strm s (cstrm_of_call zc).

  Lemma sd3_facts : forall s3 dict', sd_bad s0 = false ->
    sd_split (ds_wrap s0) (sd_s2 s0 dict) dict = (s3, dict') ->
    dwf s3 /\ SDK s s3 /\ ds_wrap s3 = 0 /\ ds_lookahead s3 = 0
    /\ ds_ins_h s3 = ds_ins_h s /\ ds_high_water s3 = ds_high_water s /\ ds_window_size s3 = ds_window_size s
    /\ ds_insert s3 <= ds_w_size s
    /\ (dmode s <> 0 -> CHAIN s3 (ds_strstart s3 - 1) (ds_strstart s3 - 1))
    /\ 0 <= cs_adler (ds_strm s3) < 2 ^ 64 /\ 0 <= cs_total_in (ds_strm s3) < 2 ^ 64
    /\ bytes_okP dict' /\ 0 <= zlength dict' <= zlength dict
    /\ (ds_wrap s = 1 -> ds_status s = INIT_STATE).
  Proof.
    intros s3 dict' Hbad E. pose proof HDD as [D X]. pose proof (dwf_sizes s D) as (Sw & Sh & _).
    unfold sd_bad in Hbad. change (ds_wrap s0) with (ds_wrap s) in Hbad. change (ds_status s0) with (ds_status s) in Hbad.
    change (ds_lookahead s0) with (ds_lookahead s) in Hbad.
    apply Bool.orb_false_iff in Hbad as [Hbad Hl0]. apply Bool.orb_false_iff in Hbad as [Hw2 Hw1].
    apply Bool.negb_false_iff in Hl0. apply Z.eqb_eq in Hl0. apply Z.eqb_neq in Hw2.
    assert (Hw1' : ds_wrap s = 1 -> ds_status s = INIT_STATE).
    { intros W1. rewrite W1 in Hw1. cbn [Z.eqb Pos.eqb andb] in Hw1. apply Bool.negb_false_iff in Hw1. apply Z.eqb_eq in Hw1. exact Hw1. }
    change (ds_wrap s0) with (ds_wrap s) in E.
    apply sd_split_cases in E. destruct E as [E1 Ed].
    pose proof (sd_s2_facts s zc dict HDD Hz Hb) as F2. cbv zeta in F2. fold s0 in F2.
    set (s2 := sd_s2 s0 dict) in *.
    destruct F2 as (D2 & K2 & W2 & L2 & I2 & H2 & Z2 & N2 & Ehd & Epv & Ess & Ehs & Ews & Ewm & A2 & Ti2).
    rewrite Hl0 in L2.
    assert (Hd' : bytes_okP dict' /\ 0 <= zlength dict' <= zlength dict).
    { rewrite Ews in Ed. destruct Ed as [-> | [Le ->]]; [split; [exact Hb | lia]|].
      split; [apply bytes_okP_zskipn; exact Hb | rewrite zlength_zskipn' by lia; lia]. }
    destruct ((ds_w_size s2 <=? zlength dict) && (ds_wrap s =? 0)); subst s3.
    - pose proof (sd_clear_facts s2 D2 L2) as F3. cbv zeta in F3.
      destruct F3 as (D3 & K3 & W3 & L3 & I3 & H3 & Z3 & N3 & S3 & T3 & C3).
      split; [exact D3|]. split; [exact (SDK_trans _ _ _ K2 K3)|]. split; [rewrite W3; exact W2|]. split; [exact L3|].
      split; [rewrite I3; exact I2|]. split; [rewrite H3; exact H2|]. split; [rewrite Z3; exact Z2|].
      split; [rewrite N3; lia|].
      split; [intros _; apply C3|].
      rewrite T3. split; [exact A2|]. split; [exact Ti2|]. split; [exact (proj1 Hd')|]. split; [exact (proj2 Hd') | exact Hw1'].
    - split; [exact D2|]. split; [exact K2|]. split; [exact W2|]. split; [exact L2|]. split; [exact I2|]. split; [exact H2|]. split; [exact Z2|].
      split; [rewrite N2; exact (dx_ins _ X)|].
      split; [intros Hm; rewrite Ess; apply (CHAIN_same s); try assumption; exact (dx_chain _ X Hm)|].
      split; [exact A2|]. split; [exact Ti2|]. split; [exact (proj1 Hd')|]. split; [exact (proj2 Hd') | exact Hw1'].
  Qed.
End SetDict.


Section Fin.
  Variable s : deflate_state.
Variable T : deflate_state.
Variable wrap : Z.
Variable saved : cstrm.
  Hypothesis HDD : DD s.
  Hypothesis Hk : SDK s T.
  Hypothesis HW : fw_wf (ds_w_size s) (ds_hash_size s) T.
  Hypothesis HX0 : FWX0 T.
  Hypothesis HCT : dmode s <> 0 -> CHAIN T (ds_strstart T - 1) (ds_strstart T - 1).
  Hypothesis HLT : ds_lookahead T < MIN_MATCH.
  Hypothesis Hwrap : wrap = ds_wrap s.

  Lemma fin_dwf : dwf (fst (sd_fin wrap saved T)).
  Proof.
    pose proof HDD as [D X]. pose proof (df_wrap _ D) as Hw. rewrite <- Hwrap in Hw.
    pose proof (wf_wsr _ _ _ HW) as Lws. unfold MIN_MATCH in HLT.
    unfold sd_fin. cbv zeta. cbn [fst]. pose proof Hk as Hk'. unfold SDK in Hk'. rewrite Hk'.
    destruct D; destruct HW; constructor; unfold sdput; dsred; try assumption; try (unfold MIN_MATCH; lia).
  Qed.

  Lemma fin_DX : DX (fst (sd_fin wrap saved T)).
  Proof.
    pose proof HDD as [D X]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_look _ _ _ HW) as Vlook. unfold MIN_MATCH in HLT.
    pose proof Hk as Hk'. unfold SDK in Hk'.
    assert (EwszT : ds_window_size T = ds_window_size s) by (rewrite Hk' at 1; reflexivity).
    assert (EwsT : ds_w_size T = ds_w_size s) by (rewrite Hk' at 1; reflexivity).
    assert (EhsT : ds_hash_size T = ds_hash_size s) by (rewrite Hk' at 1; reflexivity).
    assert (EwmT : ds_w_mask T = ds_w_mask s) by (rewrite Hk' at 1; reflexivity).
    unfold sd_fin. cbv zeta. cbn [fst]. rewrite Hk'. unfold sdput. dsred.
    match goal with |- DX ?f => set (F := f) end.
    assert (Em : dmode F = dmode s) by reflexivity.
    assert (En : nsym F = nsym s) by reflexivity.
    constructor; rewrite ?Em, ?En.
    - exact (dx_cfg _ X).
    - subst F; dsred. exact (fx0_insh _ HX0).
    - subst F; dsred. lia.
    - subst F; dsred. unfold MIN_MATCH, MAX_MATCH. lia.
    - subst F; dsred. unfold MIN_MATCH, MAX_MATCH. lia.
    - subst F; dsred. left; reflexivity.
    - exact (dx_pm _ X).
    - exact (dx_matches _ X).
    - subst F; dsred. rewrite <- EwszT. exact (fx0_hw _ HX0).
    - intros _. subst F; dsred. unfold MIN_MATCH. split; [reflexivity | lia].
    - intros _. subst F; dsred. reflexivity.
    - intros _. subst F; dsred. unfold MIN_MATCH. split; [lia|]. split; [intros H; discriminate H | intros H; exfalso; lia].
    - intros Hm0. subst F; dsred. destruct (dx_st0 _ X Hm0) as (A & B & C & D'). split; [reflexivity|]. split; [lia|]. split; [exact C | exact D'].
    - subst F; dsred. rewrite Hwrap. exact (dx_wrapneg _ X).
    - intros _. subst F; dsred. reflexivity.
    - exact (dx_sn _ X).
    - exact (dx_nsym _ X).
    - exact (dx_syms _ X).
    - exact (dx_hist _ X).
    - exact (dx_opt _ X).
    - exact (dx_stat _ X).
    - intros _. subst F; dsred. pose proof (dx_nsym _ X). lia.
    - exact (dx_tfc _ X).
    - exact (dx_tdl _ X).
    - exact (dx_depth _ X).
    - exact (dx_blc _ X).
    - intros Hm. apply (CHAIN_mono _ (ds_strstart T - 1) (ds_strstart T - 1)); [subst F; dsred; lia | subst F; dsred; lia |].
      apply (CHAIN_same T); [subst F; dsred; reflexivity | subst F; dsred; reflexivity
                            | subst F; dsred; symmetry; exact EhsT | subst F; dsred; symmetry; exact EwsT
                            | subst F; dsred; symmetry; exact EwmT | exact (HCT Hm)].
    - exact (dx_pout0 _ X).
    - exact (dx_biv _ X).
  Qed.

  Lemma fin_DD : DD (fst (sd_fin wrap saved T)).
  Proof. split; [exact fin_dwf | exact fin_DX]. Qed.
End Fin.


Section SetDictMain.
  Variable s : deflate_state.
Variable zc : ZCall.
Variable dict : list Z.
  Hypothesis HDD : DD s.
  Hypothesis Hz : zstrm_okP (zc_strm zc).
  Hypothesis Hb : bytes_okP dict.
  Hypothesis Hlen : 0 < zlength dict < 2 ^ 32.

  Theorem setdict_DD : DD (fst (deflateSetDictionary_m s zc dict)).
  Proof.
    pose proof HDD as [D X]. pose proof (dwf_sizes s D) as (Sw & Sh & _).
    assert (Hwk : 0 <= ds_w_bits s /\ ds_w_size s = 2 ^ ds_w_bits s) by (pose proof (df_wbits _ D); split; [lia | exact (df_wsize _ D)]).
    rewrite sdm_unfold. cbv zeta. set (s0 := set_strm s (cstrm_of_call zc)).
    destruct (deflateStateCheck s0) eqn:Hchk; [cbn [fst]; apply DD_set_strm; exact HDD|].
    destruct (sd_bad s0) eqn:Hbad; [cbn [fst]; apply DD_set_strm; exact HDD|].
    destruct (sd_split (ds_wrap s0) (sd_s2 s0 dict) dict) as [s3 dict'] eqn:E.
    pose proof (sd3_facts s zc dict HDD Hz Hb Hlen s3 dict' Hbad E) as F3. cbv zeta in F3.
    destruct F3 as (D3 & K3 & W3 & L3 & I3 & H3 & Z3 & N3 & C3 & A3 & Ti3 & Bd & Ld & Hw1).
    unfold sd_tail. set (s4 := sd_s4 s3 dict').
    pose proof K3 as K3'. unfold SDK in K3'.
    assert (Ews3 : ds_w_size s3 = ds_w_size s) by (rewrite K3' at 1; reflexivity).
    assert (Ehs3 : ds_hash_size s3 = ds_hash_size s) by (rewrite K3' at 1; reflexivity).
    assert (K4 : SDK s s4) by (eapply SDK_trans; [exact K3 | apply SDK_strm]).
    assert (HW4 : fw_wf (ds_w_size s) (ds_hash_size s) s4).
    { rewrite <- Ews3, <- Ehs3. change (ds_w_size s3) with (ds_w_size s4). change (ds_hash_size s3) with (ds_hash_size s4).
      apply dwf_fw_wf; subst s4; unfold sd_s4; dsred.
      - apply dwf_set_strm. exact D3.
      - rewrite W3. lia.
      - lia.
      - lia.
      - rewrite arr_len_of_list. lia.
      - exact Ti3.
      - exact A3.
      - intros i Hi. rewrite arr_len_of_list in Hi. apply bytes_okP_get; [exact Bd | exact Hi]. }
    assert (X04 : FWX0 s4).
    { constructor; subst s4; unfold sd_s4; dsred.
      - rewrite I3. exact (dx_insh _ X).
      - rewrite H3, Z3. exact (dx_hw _ X). }
    assert (X4 : dmode s <> 0 -> FWX s4).
    { intros Hm. constructor; subst s4; unfold sd_s4; dsred.
      - apply (CHAIN_same s3); try reflexivity. exact (C3 Hm).
      - rewrite I3. exact (dx_insh _ X).
      - rewrite Ews3. exact N3.
      - rewrite H3, Z3. exact (dx_hw _ X).
      - exact A3. }
    assert (L4 : ds_lookahead s4 = 0) by (subst s4; unfold sd_s4; dsred; exact L3).
    assert (Ai4 : cs_avail_in (ds_strm s4) = zlength dict') by (subst s4; unfold sd_s4; dsred; reflexivity).
    assert (L4' : ds_lookahead s4 < MIN_LOOKAHEAD) by (rewrite L4; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH; lia).
    pose proof (fill_window_facts (ds_w_size s) (ds_hash_size s) s4 HW4 L4') as F5. cbv zeta in F5.
    destruct F5 as (HW5 & _ & _ & HL5 & HA5 & _).
    pose proof (fill_window_FWX0 (ds_w_size s) (ds_hash_size s) s4 HW4 X04 L4') as X05.
    assert (X5 : dmode s <> 0 -> FWX (fill_window s4)) by (intros Hm; exact (proj1 (fill_window_FWX (ds_w_size s) (ds_hash_size s) (ds_w_bits s) Hwk s4 HW4 (X4 Hm) L4'))).
    pose proof (fill_window_SDK s4) as K5.
    set (t5 := fill_window s4) in *.
    assert (Hf : sd_fuel (Z.to_nat (zlength dict' + 2)) t5).
    { unfold sd_fuel. rewrite HA5, Ai4, L4. rewrite Z2Nat.id by lia. rewrite L4 in HL5.
      destruct (MIN_MATCH <=? ds_lookahead t5); lia. }
    pose proof (setdict_outer_FWX0 (ds_w_size s) (ds_hash_size s) (ds_w_bits s) Hwk (Z.to_nat (zlength dict' + 2)) t5 HW5 X05 Hf) as R. cbv zeta in R.
    destruct R as (HWT & X0T & HLT).
    assert (HCT : dmode s <> 0 -> CHAIN (setdict_outer (Z.to_nat (zlength dict' + 2)) t5)
                                        (ds_strstart (setdict_outer (Z.to_nat (zlength dict' + 2)) t5) - 1)
                                        (ds_strstart (setdict_outer (Z.to_nat (zlength dict' + 2)) t5) - 1)).
    { intros Hm. pose proof (setdict_outer_FWX (ds_w_size s) (ds_hash_size s) (ds_w_bits s) Hwk (Z.to_nat (zlength dict' + 2)) t5 HW5 (X5 Hm) Hf) as R.
      cbv zeta in R. exact (fx_chain _ (proj1 (proj2 R))). }
    pose proof (setdict_outer_SDK (Z.to_nat (zlength dict' + 2)) t5) as K6.
    set (T := setdict_outer (Z.to_nat (zlength dict' + 2)) t5) in *.
    apply (fin_DD s T (ds_wrap s0) (ds_strm s3) HDD).
    - eapply SDK_trans; [exact K4|]. eapply SDK_trans; [exact K5 | exact K6].
    - exact HWT.
    - exact X0T.
    - exact HCT.
    - exact HLT.
    - reflexivity.
  Qed.
End SetDictMain.
End RefDeflSafeI5.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5.

Module RefDeflSafeI5b.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma wrap8_range' : forall z, 0 <= wrap8 z < 256.
Proof. intros z. pose proof (wrap8_range z). change (2 ^ 8) with 256 in H. lia. Qed.
Lemma init_u8_range : forall g b i, 0 <= init_u8 g b i < 256.
Proof. intros. unfold init_u8. apply wrap8_range'. Qed.
Lemma init_u16_range : forall g b i, 0 <= init_u16 g b i < 65536.
Proof. intros. unfold init_u16. pose proof (wrap8_range' (g (b + 2 * i))). pose proof (wrap8_range' (g (b + 2 * i + 1))). lia. Qed.
Lemma init_u32_range : forall g b i, 0 <= init_u32 g b i < 2 ^ 32.
Proof. intros. unfold init_u32. pose proof (init_u16_range g b (2 * i)). pose proof (init_u16_range g b (2 * i + 1)). lia. Qed.

Lemma cleared_get : forall (a : arr) n h, arr_len a = n -> 0 <= h < n ->
  arr_get (arr_fill (arr_set a (n - 1) NIL) 0 (n - 1) 0) h = 0.
Proof.
  intros a n h Hl Hh. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hl.
  destruct (Z_lt_le_dec h (n - 1)).
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (n - 1)) && ((0 <=? h) && (h <? n))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (n - 1)) && ((0 <=? h) && (h <? n))) with false
      by (symmetry; apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    replace h with (n - 1) by lia. rewrite arr_get_set_same by (rewrite Hl; lia). reflexivity.
Qed.

Section InitState.
  Variable b0 : blk.
Variable bw : blk.
Variable bp : blk.
Variable bh : blk.
Variable bb : blk.
Variable g0 : Z -> Z.
Variable gw : Z -> Z.
Variable gp : Z -> Z.
Variable gh : Z -> Z.
Variable gb : Z -> Z.
Variable cs : cstrm.
Variable wrap : Z.
Variable wb9 : Z.
Variable meml : Z.
Variable lv : Z.
Variable strat : Z.
Variable method : Z.

  Definition S5g : deflate_state :=
    s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 meml) (Some (bw, gw))) (Some (bp, gp))) (Some (bh, gh))) meml) (Some (bb, gb)).

  Definition dFg : deflate_state :=
   {| ds_status := if wrap =? 2 then GZIP_STATE else INIT_STATE;
      ds_pending_buf := blk_bytes gb (Z.shiftl 1 (meml + 6) * 4);
      ds_pending_buf_size := Z.shiftl 1 (meml + 6) * 4;
      ds_pending_out := 0;
      ds_pending := 0;
      ds_wrap := wrap;
      ds_gzhead := 0;
      ds_gzindex := init_u64 g0 64 0;
      ds_method := wrap8 method;
      ds_last_flush := -2;
      ds_w_size := Z.shiftl 1 wb9;
      ds_w_bits := wb9;
      ds_w_mask := Z.shiftl 1 wb9 - 1;
      ds_window := blk_bytes gw (2 * Z.shiftl 1 wb9);
      ds_window_size := 2 * Z.shiftl 1 wb9;
      ds_prev := blk_ush gp (Z.shiftl 1 wb9);
      ds_head := arr_fill (arr_set (blk_ush gh (Z.shiftl 1 (meml + 7))) (Z.shiftl 1 (meml + 7) - 1) 0) 0 (Z.shiftl 1 (meml + 7) - 1) 0;
      ds_ins_h := 0;
      ds_hash_size := Z.shiftl 1 (meml + 7);
      ds_hash_bits := meml + 7;
      ds_hash_mask := Z.shiftl 1 (meml + 7) - 1;
      ds_hash_shift := (meml + 7 + MIN_MATCH - 1) / MIN_MATCH;
      ds_block_start := 0;
      ds_match_length := MIN_MATCH - 1;
      ds_prev_match := init_u32 g0 164 0;
      ds_match_available := 0;
      ds_strstart := 0;
      ds_match_start := init_u32 g0 176 0;
      ds_lookahead := 0;
      ds_prev_length := MIN_MATCH - 1;
      ds_max_chain_length := cfg_chain lv;
      ds_max_lazy_match := cfg_lazy lv;
      ds_level := lv;
      ds_strategy := strat;
      ds_good_match := cfg_good lv;
      ds_nice_match := cfg_nice lv;
      ds_dyn_ltree_fc := arr_set (arr_fill (arr_u16_of g0 212 4 573) 0 L_CODES 0) END_BLOCK (wrap16 1);
      ds_dyn_ltree_dl := arr_u16_of g0 214 4 573;
      ds_dyn_dtree_fc := arr_fill (arr_u16_of g0 2504 4 61) 0 D_CODES 0;
      ds_dyn_dtree_dl := arr_u16_of g0 2506 4 61;
      ds_bl_tree_fc := arr_fill (arr_u16_of g0 2748 4 39) 0 BL_CODES 0;
      ds_bl_tree_dl := arr_u16_of g0 2750 4 39;
      ds_l_max_code := swrap32 (init_u32 g0 2912 0);
      ds_d_max_code := swrap32 (init_u32 g0 2936 0);
      ds_bl_max_code := swrap32 (init_u32 g0 2960 0);
      ds_bl_count := arr_u16_of g0 2976 2 16;
      ds_heap := arr_s32_of g0 3008 4 573;
      ds_heap_len := swrap32 (init_u32 g0 5300 0);
      ds_heap_max := swrap32 (init_u32 g0 5304 0);
      ds_depth := arr_u8_of g0 5308 1 573;
      ds_lit_bufsize := Z.shiftl 1 (meml + 6);
      ds_sym_next := 0;
      ds_sym_end := (Z.shiftl 1 (meml + 6) - 1) * 3;
      ds_opt_len := 0;
      ds_static_len := 0;
      ds_matches := 0;
      ds_insert := 0;
      ds_bi_buf := 0;
      ds_bi_valid := 0;
      ds_high_water := 0;
      ds_self_blk := b0;
      ds_window_blk := Some bw;
      ds_prev_blk := Some bp;
      ds_head_blk := Some bh;
      ds_pending_buf_blk := Some bb;
      ds_strm := cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
                            (if wrap =? 2 then crc32_init else adler32_init) |}.

  Lemma dFg_eq : LM (tr_init (RK0 (s_fin S5g lv strat method))) = dFg.
  Proof. reflexivity. Qed.

  Lemma reset_S5g : 0 <= wrap -> deflateReset (s_fin S5g lv strat method) = (dFg, Z_OK).
  Proof.
    intros Hw. rewrite deflateReset_eq; [| reflexivity | exact Hw].
    rewrite dFg_eq. reflexivity.
  Qed.

  Hypothesis H1 : 9 <= wb9 <= 15.
  Hypothesis H2 : 5 <= meml <= 9.
  Hypothesis H3 : 0 <= lv <= 9.
  Hypothesis H4 : 0 <= strat <= 4.
  Hypothesis H5 : 0 <= wrap <= 2.
  Hypothesis H6 : method = 8.

  Let Ews : Z.shiftl 1 wb9 = 2 ^ wb9 := Z.shiftl_1_l wb9.
  Let Ehs : Z.shiftl 1 (meml + 7) = 2 ^ (meml + 7) := Z.shiftl_1_l (meml + 7).
  Let Elbs : Z.shiftl 1 (meml + 6) = 2 ^ (meml + 6) := Z.shiftl_1_l (meml + 6).

  Lemma dFg_head0 : forall h, 0 <= h < Z.shiftl 1 (meml + 7) -> arr_get (ds_head dFg) h = 0.
  Proof.
    intros h Hh. cbn [ds_head dFg]. apply (cleared_get (blk_ush gh (Z.shiftl 1 (meml + 7)))); [| exact Hh].
    unfold blk_ush. rewrite arr_len_init. reflexivity.
  Qed.

  Lemma dFg_dwf : dwf dFg.
  Proof.
    pose proof (pow2_range_9_15 wb9 H1) as R1. pose proof (pow2_range_8_16 (meml + 7) ltac:(lia)) as R2. pose proof (pow2_range_7_15 (meml + 6) ltac:(lia)) as R3.
    pose proof dFg_head0 as Hh0. cbn [ds_head dFg] in Hh0.
    constructor; cbn [ds_status ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_w_bits ds_w_size ds_w_mask ds_window_size
                      ds_hash_bits ds_hash_size ds_hash_mask ds_hash_shift ds_lit_bufsize ds_pending_buf_size ds_sym_end ds_window ds_prev ds_head
                      ds_pending_buf ds_gzhead ds_method ds_level ds_strategy ds_wrap ds_strstart
                      ds_insert ds_lookahead ds_match_start ds_ins_h ds_high_water
                      ds_last_flush ds_pending ds_pending_out ds_bi_buf ds_bi_valid dFg];
      rewrite ?Ews, ?Ehs, ?Elbs in *;
      try discriminate; try lia;
      first
      [ unfold deflateStateCheck; cbn [ds_status dFg]; destruct (wrap =? 2); reflexivity
      | unfold GZIP_STATE, INIT_STATE; destruct (wrap =? 2); lia
      | replace (meml + 7 - 1) with (meml + 6) by lia; reflexivity
      | unfold blk_bytes; rewrite arr_len_init; lia
      | unfold blk_ush; rewrite arr_len_init; lia
      | rewrite arr_len_fill, arr_len_set; unfold blk_ush; rewrite arr_len_init; lia
      | unfold tree_lens; cbn [ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth dFg];
        rewrite ?arr_len_set, ?arr_len_fill; unfold arr_u16_of, arr_s32_of, arr_u8_of; rewrite !arr_len_init; unfold HEAP_SIZE, L_CODES, D_CODES, BL_CODES, MAX_BITS; lia
      | rewrite H6; reflexivity
      | unfold Z_FIXED; lia
      | pose proof (init_u32_range g0 176 0); lia
      | vm_compute; split; [discriminate | reflexivity]
      | intros i Hi; unfold blk_bytes; rewrite arr_get_init; apply init_u8_range
      | intros i Hi; unfold blk_ush; rewrite arr_get_init; apply init_u16_range
      | intros i Hi; rewrite (Hh0 i Hi); lia
      | match goal with |- ?g => idtac "DWFLEFT" g end ].
  Qed.

  Lemma dFg_BQ : BQ dFg /\ nsym dFg = 0.
  Proof.
    apply BQ_fresh; cbn [ds_sym_next ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc dFg].
    - reflexivity.
    - intros c Hc. unfold L_CODES, LITERALS, LENGTH_CODES in *. rewrite arr_get_set. unfold arr_inb. rewrite arr_len_fill. unfold arr_u16_of. rewrite arr_len_init.
      unfold END_BLOCK. destruct (Z.eqb_spec 256 c) as [<-|Hne].
      + replace ((256 =? 256) && ((0 <=? 256) && (256 <? 573))) with true by reflexivity. reflexivity.
      + replace (256 =? c) with false by (symmetry; apply Z.eqb_neq; exact Hne). cbn [andb].
        rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_init.
        replace ((0 <=? c) && (c <? 0 + Z.max 0 286) && ((0 <=? c) && (c <? 573))) with true
          by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        try replace (c =? 256) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - intros d Hd. unfold D_CODES in *. rewrite arr_get_fill. unfold arr_inb, arr_u16_of. rewrite arr_len_init.
      replace ((0 <=? d) && (d <? 0 + Z.max 0 30) && ((0 <=? d) && (d <? 61))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - intros b Hb. unfold BL_CODES in *. rewrite arr_get_fill. unfold arr_inb, arr_u16_of. rewrite arr_len_init.
      replace ((0 <=? b) && (b <? 0 + Z.max 0 19) && ((0 <=? b) && (b <? 39))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma u16_cells : forall g off st n i, 0 <= arr_get (arr_u16_of g off st n) i < 65536.
  Proof. intros. unfold arr_u16_of. rewrite arr_get_init. apply init_u16_range. Qed.

  Lemma fill_cells : forall (a : arr) ofs n i, (forall j, 0 <= arr_get a j < 65536) -> 0 <= arr_get (arr_fill a ofs n 0) i < 65536.
  Proof. intros a ofs n i Ha. rewrite arr_get_fill. destruct (_ && _); [lia | apply Ha]. Qed.

  Lemma dFg_DX : DX dFg.
  Proof.
    pose proof (pow2_range_9_15 wb9 H1) as R1. pose proof (pow2_range_8_16 (meml + 7) ltac:(lia)) as R2. pose proof (pow2_range_7_15 (meml + 6) ltac:(lia)) as R3.
    destruct dFg_BQ as [(Q1 & Q2 & Q3 & Q4) Qn].
    assert (Hm : 0 <= dmode dFg <= 4) by (apply dmode_range).
    constructor; rewrite ?Qn;
      cbn [ds_good_match ds_max_lazy_match ds_nice_match ds_max_chain_length ds_level ds_ins_h ds_insert ds_w_size ds_match_length ds_prev_length
           ds_match_available ds_prev_match ds_matches ds_high_water ds_window_size ds_lookahead ds_strstart ds_match_start ds_block_start
           ds_sym_next ds_wrap ds_status ds_lit_bufsize ds_opt_len ds_static_len ds_depth ds_bl_count ds_pending ds_pending_out ds_bi_valid dFg];
      rewrite ?Ews, ?Ehs, ?Elbs in *; unfold MIN_MATCH, MAX_MATCH; try lia.
    - symmetry. apply cfg_eta.
    - pose proof (init_u32_range g0 164 0). lia.
    - exact Q4.
    - intros t i. destruct t; cbn [tree_fc ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc dFg].
      + rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range 1) as W; change (2 ^ 16) with 65536 in W; lia | apply fill_cells; intros j; apply u16_cells].
      + apply fill_cells; intros j; apply u16_cells.
      + apply fill_cells; intros j; apply u16_cells.
    - intros t i. destruct t; cbn [tree_dl ds_dyn_ltree_dl ds_dyn_dtree_dl ds_bl_tree_dl dFg]; apply u16_cells.
    - intros i. unfold arr_u8_of. rewrite arr_get_init. apply init_u8_range.
    - intros i Hi. apply u16_cells.
    - intros _. apply CHAIN_heads0. cbn [ds_hash_size dFg]. exact dFg_head0.
  Qed.

  Lemma dFg_DD : DD dFg.
  Proof. split; [exact dFg_dwf | exact dFg_DX]. Qed.
End InitState.


Definition ohd (chs : DCH) : option (blk * (Z -> Z)) := match chs with [] => None | c :: _ => c end.
Definition otl (chs : DCH) : DCH := match chs with [] => [] | _ :: t => t end.

Lemma dhooks_zalloc : forall a b chs, zalloc dhooks a b chs = MRet (ohd chs, otl chs).
Proof. intros a b [|c t]; reflexivity. Qed.

Definition dend_rc (s : deflate_state) : Z := if ds_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK.
Lemma dhooks_end : forall s chs, deflateEnd_core dhooks s chs = MRet (dend_rc s, chs).
Proof.
  intros s chs. unfold deflateEnd_core, try_free.
  destruct (ds_pending_buf_blk s), (ds_head_blk s), (ds_prev_blk s), (ds_window_blk s); reflexivity.
Qed.

Lemma dpure_sbind' : forall A B (m : SM DCH A) (f : A -> SM DCH B) chs a chs',
  m chs = MRet (a, chs') -> dpure (sbind m f) chs = dpure (f a) chs'.
Proof. intros A B m f chs a chs' H. unfold dpure, sbind. rewrite H. reflexivity. Qed.

Ltac dpeel' name :=
  lazymatch goal with
  | |- dpure (let x := ?v in @?b x) ?c = ?r => set (name := v); change (dpure (b name) c = r); cbv beta
  end.

Definition S5og (b0 : blk) (g0 : Z -> Z) (cs : cstrm) (wrap wb9 meml : Z) (rw rp rh rb : option (blk * (Z -> Z))) : deflate_state :=
  s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 meml) rw) rp) rh) meml) rb.

Lemma S5og_proj : forall b0 g0 cs wrap wb9 meml rw rp rh rb,
  let s := S5og b0 g0 cs wrap wb9 meml rw rp rh rb in
  ds_window_blk s = option_map fst rw /\ ds_prev_blk s = option_map fst rp /\ ds_head_blk s = option_map fst rh
  /\ ds_pending_buf_blk s = option_map fst rb.
Proof.
  intros. subst s. unfold S5og.
  split; [apply s5_window_blk|]. split; [apply s5_prev_blk|]. split; [apply s5_head_blk | apply s5_pending_buf_blk].
Qed.

Lemma some_pair_fst : forall {A B} (a : A * B) (x : A) (y : B), Some a = Some (x, y) -> fst a = x.
Proof. intros A B a x y H. injection H as H'. subst a. reflexivity. Qed.
Lemma some_pair_inj1 : forall {A B} (x1 x2 : A) (y1 y2 : B), Some (x1, y1) = Some (x2, y2) -> x1 = x2.
Proof. intros A B x1 x2 y1 y2 H. injection H as H1 H2. exact H1. Qed.

Section Run.
  Variable zc : ZCall.
Variable level : Z.
Variable method : Z.
Variable wb : Z.
Variable meml : Z.
Variable strategy : Z.
  Hypothesis HML5 : 5 <= meml.

  Definition dinit_body (s5 : deflate_state) : option deflate_state * ZRet :=
    if all_some s5
    then (Some (fst (deflateReset (s_fin s5 (di_level level) strategy method))),
          zret_of_cs (ds_strm (fst (deflateReset (s_fin s5 (di_level level) strategy method))))
                     (snd (deflateReset (s_fin s5 (di_level level) strategy method))))
    else (None, zret_of_cs (ds_strm (s_fail s5)) Z_MEM_ERROR).

  Lemma dinit_run_bad : forall chs, di_bad level method wb meml strategy = true ->
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (None, zret_of_cs (cs_init zc) Z_STREAM_ERROR).
  Proof.
    intros chs Hbad. unfold di_bad in Hbad.
    cbv delta [deflateInit2_m]. cbv beta.
    dpeel' csX. dpeel' lvX. rewrite di_triple. cbv beta iota.
    lazymatch goal with |- dpure (if _ then _ else if ?c then _ else _) _ = _ => replace c with (di_chk level method wb meml strategy) by reflexivity end.
    apply Bool.orb_true_iff in Hbad. destruct ((wb <? 0) && (wb <? -15)) eqn:Hb0.
    - cbv beta iota delta [dpure sret fst]. subst csX. reflexivity.
    - destruct Hbad as [Hbad|Hbad]; [discriminate Hbad|]. rewrite Hbad. cbv beta iota delta [dpure sret fst]. subst csX. reflexivity.
  Qed.

  Lemma dinit_run : forall chs, di_bad level method wb meml strategy = false ->
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs =
    Some (match ohd chs with
          | None => (None, zret_of_cs (cs_init zc) Z_MEM_ERROR)
          | Some (b0, g0) =>
            dinit_body (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml
                          (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs))))))
          end).
  Proof.
    intros chs Hbad. unfold di_bad in Hbad. apply Bool.orb_false_iff in Hbad as [Hb0 Hchk].
    cbv delta [deflateInit2_m]. cbv beta.
    dpeel' csX. dpeel' lvX. rewrite di_triple. cbv beta iota. rewrite Hb0.
    lazymatch goal with |- dpure (if ?c then _ else _) _ = _ => replace c with (di_chk level method wb meml strategy) by reflexivity end.
    rewrite Hchk. dpeel' wb9X.
    erewrite dpure_sbind' by apply dhooks_zalloc.
    destruct (ohd chs) as [[b0 g0]|].
    2: { cbv beta iota delta [dpure sret fst]. subst csX. reflexivity. }
    cbv beta iota.
    dpeel' s0'. dpeel' s1'. dpeel' s2'. dpeel' s3'. dpeel' s4'. dpeel' s5'. dpeel' s6'. dpeel' s7'. dpeel' s8'. dpeel' s9'. dpeel' s10'.
    replace s10' with (s_setup g0 b0 csX (di_wrap wb) wb9X meml) by reflexivity. clear s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s11'.
    replace s11' with (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) by reflexivity. clear s11'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s12'.
    replace s12' with (s_prv (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) (ohd (otl (otl chs)))) by reflexivity. clear s12'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s13'. dpeel' s14'. dpeel' s15'.
    replace s15' with (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) (ohd (otl (otl chs)))) (ohd (otl (otl (otl chs))))) meml) by reflexivity.
    clear s15' s14' s13'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s16'. dpeel' s17'.
    replace s17' with (S5og b0 g0 csX (di_wrap wb) wb9X meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) by reflexivity.
    clear s17' s16'.
    subst csX lvX wb9X. change (cset_msg (cstrm_of_call zc) MSG_NULL) with (cs_init zc).
    change (if level =? Z_DEFAULT_COMPRESSION then 6 else level) with (di_level level).
    change (if di_wb wb =? 8 then 9 else di_wb wb) with (di_wb9 wb).
    remember (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as S5 eqn:ES5.
    pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as PJ.
    cbv zeta in PJ. rewrite <- ES5 in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
    unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb.
    destruct (ohd (otl chs)) as [[bw gw]|]; [destruct (ohd (otl (otl chs))) as [[bp gp]|]; [destruct (ohd (otl (otl (otl chs)))) as [[bh gh]|];
      [destruct (ohd (otl (otl (otl (otl chs))))) as [[bb gb]|]|]|]|]; cbv beta iota delta [option_map].
    1: { change (set_method (set_strategy (set_level (set_sym_end S5 ((ds_lit_bufsize S5 - 1) * 3)) (di_level level)) strategy) (wrap8 method))
           with (s_fin S5 (di_level level) strategy method).
         destruct (deflateReset (s_fin S5 (di_level level) strategy method)) as [s' rc'].
         cbv beta iota delta [dpure sret fst snd]. reflexivity. }
    all: change (set_strm (set_status S5 FINISH_STATE) (cset_msg (ds_strm (set_status S5 FINISH_STATE)) (MSG_ERR Z_MEM_ERROR))) with (s_fail S5);
         erewrite dpure_sbind' by apply dhooks_end; cbv beta iota delta [dpure sret fst]; reflexivity.
  Qed.

  Lemma dinit_some : forall chs s zr,
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (Some s, zr) ->
    di_bad level method wb meml strategy = false
    /\ exists b0 g0 bw gw bp gp bh gh bb gb,
         s = fst (deflateReset (s_fin (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml) (di_level level) strategy method)).
  Proof.
    intros chs s zr H.
    destruct (di_bad level method wb meml strategy) eqn:Hbad.
    { rewrite (dinit_run_bad chs Hbad) in H. exfalso. apply some_pair_fst in H. cbn [fst] in H. discriminate H. }
    split; [reflexivity|].
    rewrite (dinit_run chs Hbad) in H.
    destruct (ohd chs) as [[b0 g0]|]; [| exfalso; apply some_pair_fst in H; cbn [fst] in H; discriminate H].
    cbv beta iota in H.
    remember (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as S5 eqn:ES5.
    pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as PJ.
    cbv zeta in PJ. rewrite <- ES5 in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
    unfold dinit_body, all_some in H. rewrite Ew, Ep, Eh, Eb in H.
    destruct (ohd (otl chs)) as [[bw gw]|]; [destruct (ohd (otl (otl chs))) as [[bp gp]|]; [destruct (ohd (otl (otl (otl chs)))) as [[bh gh]|];
      [destruct (ohd (otl (otl (otl (otl chs))))) as [[bb gb]|]|]|]|]; cbv beta iota delta [option_map] in H.
    1: { apply some_pair_inj1 in H. injection H as H1.
         exists b0, g0, bw, gw, bp, gp, bh, gh, bb, gb.
         change (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml)
           with (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb))).
         rewrite <- ES5. symmetry. exact H1. }
    all: exfalso; apply some_pair_inj1 in H; discriminate H.
  Qed.

  Theorem dinit_DD : forall chs s zr,
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (Some s, zr) -> DD s.
  Proof.
    intros chs s zr H. destruct (dinit_some chs s zr H) as [Hbad (b0 & g0 & bw & gw & bp & gp & bh & gh & bb & gb & Es)].
    unfold di_bad in Hbad. apply Bool.orb_false_iff in Hbad as [Hb0 Hc].
    unfold di_chk, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED in Hc.
    apply Bool.orb_false_iff in Hc as [Hc C10].
    apply Bool.orb_false_iff in Hc as [Hc C9]. apply Z.ltb_ge in C9.
    apply Bool.orb_false_iff in Hc as [Hc C8]. apply Z.ltb_ge in C8.
    apply Bool.orb_false_iff in Hc as [Hc C7]. apply Z.ltb_ge in C7.
    apply Bool.orb_false_iff in Hc as [Hc C6]. apply Z.ltb_ge in C6.
    apply Bool.orb_false_iff in Hc as [Hc C5]. apply Z.ltb_ge in C5.
    apply Bool.orb_false_iff in Hc as [Hc C4]. apply Z.ltb_ge in C4.
    apply Bool.orb_false_iff in Hc as [Hc C3]. apply Bool.negb_false_iff in C3. apply Z.eqb_eq in C3.
    apply Bool.orb_false_iff in Hc as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
    pose proof (di_wrap_range wb) as Hwr.
    assert (H9 : 9 <= di_wb9 wb <= 15).
    { unfold di_wb9. destruct (Z.eqb_spec (di_wb wb) 8) as [E8|N8]; lia. }
    rewrite (reset_S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method (proj1 Hwr)) in Es.
    cbn [fst] in Es. subst s.
    apply dFg_DD; try assumption; lia.
  Qed.
End Run.
End RefDeflSafeI5b.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL5.RefDeflSafeL3.

Module RefDeflSafeL4.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
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
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL2.RefDeflSafeLM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeLF.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSafeL5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeL5.RefDeflSafeL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma rle_cmpk_range : forall k w prev scan,
  let r := rle_cmpk k w prev scan in
  scan <= fst r <= scan + Z.of_nat k /\ (snd r = true -> fst r = scan + Z.of_nat k).
Proof.
  induction k as [|k IH]; intros w prev scan r; subst r.
  - cbn [rle_cmpk fst snd]. lia.
  - cbn [rle_cmpk]. destruct (prev =? arr_get w (scan + 1)).
    + specialize (IH w prev (scan + 1)). cbv zeta in IH. destruct (rle_cmpk k w prev (scan + 1)) as [sc ok]. cbn [fst snd] in *.
      rewrite Nat2Z.inj_succ. split; [lia|]. intros Hok. rewrite (proj2 IH Hok). lia.
    + cbn [fst snd]. rewrite Nat2Z.inj_succ. split; [lia|]. intros HH; discriminate HH.
Qed.

Lemma rle_cmp_loop_range : forall f w prev scan strend,
  scan < strend -> (exists q, strend - scan = 8 * q) ->
  scan <= rle_cmp_loop f w prev scan strend <= strend.
Proof.
  induction f as [|f IH]; intros w prev scan strend Hlt [q Hq].
  - cbn [rle_cmp_loop]. lia.
  - cbn [rle_cmp_loop]. pose proof (rle_cmpk_range 8 w prev scan) as R. cbv zeta in R.
    destruct (rle_cmpk 8 w prev scan) as [sc ok]. cbn [fst snd] in R. destruct R as [R1 R2]. change (Z.of_nat 8) with 8 in R1, R2.
    destruct ok; cbn [andb].
    + specialize (R2 eq_refl). destruct (Z.ltb_spec sc strend) as [L|L].
      * pose proof (IH w prev sc strend L ltac:(exists (q - 1); lia)). lia.
      * lia.
    + lia.
Qed.

Lemma rl_run_facts : forall s, 0 <= ds_lookahead s ->
  exists v, rl_run s = set_match_length s v /\ 0 <= v <= ds_lookahead s /\ v <= MAX_MATCH.
Proof.
  intros s Hl. unfold rl_run.
  change (ds_lookahead (set_match_length s 0)) with (ds_lookahead s).
  change (ds_strstart (set_match_length s 0)) with (ds_strstart s).
  change (ds_window (set_match_length s 0)) with (ds_window s).
  destruct ((MIN_MATCH <=? ds_lookahead s) && (0 <? ds_strstart s)) eqn:C.
  - pose proof (rle_cmpk_range 3 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) (ds_strstart s - 1)) as R. cbv zeta in R.
    destruct (rle_cmpk 3 _ _ _) as [sc ok]. cbn [fst snd] in R. destruct R as [R1 R2]. change (Z.of_nat 3) with 3 in R1, R2.
    destruct ok.
    + specialize (R2 eq_refl).
      pose proof (rle_cmp_loop_range 33 (ds_window s) (arr_get (ds_window s) (ds_strstart s - 1)) sc (ds_strstart s + MAX_MATCH)
                    ltac:(unfold MAX_MATCH; lia) ltac:(exists 32; unfold MAX_MATCH; lia)) as L.
      set (sc' := rle_cmp_loop 33 _ _ _ _) in *. clearbody sc'.
      cbv zeta. change (ds_lookahead (set_match_length (set_match_length s 0) ?v)) with (ds_lookahead s).
      change (ds_match_length (set_match_length (set_match_length s 0) ?v)) with v.
      destruct (Z.ltb_spec (ds_lookahead s) (MAX_MATCH - (ds_strstart s + MAX_MATCH - sc'))).
      * exists (ds_lookahead s). split; [destruct s; reflexivity|]. unfold MAX_MATCH in *. lia.
      * exists (MAX_MATCH - (ds_strstart s + MAX_MATCH - sc')). split; [destruct s; reflexivity|]. unfold MAX_MATCH in *. lia.
    + exists 0. split; [reflexivity|]. unfold MAX_MATCH. lia.
  - exists 0. split; [reflexivity|]. unfold MAX_MATCH. lia.
Qed.


Section Rle.
  Variable c0 : cstrm.
Variable s0 : deflate_state.
Variable flush : Z.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis HFB : FB_CALL.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.

  Definition RTI (s : deflate_state) : Prop :=
    DC c0 s /\ KV s = KV s0 /\ ds_pending s = 0 /\ dmode s = 2 /\ ds_status s <> FINISH_STATE /\ OUTLE s0 s.

  Lemma RTI_facts : forall s, RTI s ->
    dwf s /\ DX s /\ SV c0 s
    /\ 512 <= ds_w_size s <= 32768 /\ 256 <= ds_hash_size s <= 65536 /\ 2048 <= ds_lit_bufsize s <= 32768
    /\ ds_match_available s = 0
    /\ 0 <= nsym s <= ds_lit_bufsize s - 2 /\ ds_sym_next s = 3 * nsym s /\ ds_sym_end s = (ds_lit_bufsize s - 1) * 3
    /\ 0 <= ds_strstart s /\ 0 <= ds_lookahead s /\ ds_strstart s + ds_lookahead s <= 2 * ds_w_size s
    /\ 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s.
  Proof.
    intros s (HDC & HK & Hp & Hm & Hst & Ho). pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
    pose proof (dx_notslow _ X ltac:(rewrite Hm; lia)) as Hma.
    pose proof (dx_nsym _ X). pose proof (dx_sn _ X). pose proof (df_symend _ D). pose proof (df_strstart _ D). pose proof (df_look _ D). pose proof (df_sl _ D).
    pose proof (dx_ext _ X ltac:(rewrite Hm; lia)) as He. rewrite Hma in He.
    repeat (split; [assumption|]). lia.
  Qed.

  Lemma rfill_stage : forall s, RTI s ->
    let r := rl_fill s flush in
    RTI (fst r) /\ lz_meas (fst r) = lz_meas s
    /\ (ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s))
    /\ ds_w_size (fst r) = ds_w_size s
    /\ (snd r = None -> 1 <= ds_lookahead (fst r))
    /\ (snd r = Some LBreak -> ds_lookahead (fst r) = 0)
    /\ (forall bs, snd r = Some (LRet bs) -> bs = need_more)
    /\ snd r <> Some LCont
    /\ ds_strstart (fst r) + MAX_MATCH < 2 * ds_w_size s.
  Proof.
    intros s HF r. subst r. pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    assert (Hwr : 0 <= ds_wrap s) by (pose proof (dx_wrapneg _ X); pose proof (df_wrap _ D); destruct (Z_lt_le_dec (ds_wrap s) 0); [exfalso; apply Hst; auto | lia]).
    assert (HW : fw_wf (ds_w_size s) (ds_hash_size s) s).
    { apply (dwf_fw_wf s D Hwr (sv_nin _ _ V) (sv_ain _ _ V) ltac:(rewrite (sv_input _ _ V); pose proof (sv_inlen _ _ V); lia)
             (sv_tin _ _ V) (sv_adler _ _ V) (sv_ib _ _ V)). }
    unfold rl_fill.
    destruct (Z.leb_spec (ds_lookahead s) MAX_MATCH) as [Hl0|Hl0].
    - destruct (DC_fill_window c0 s HC0w HDC ltac:(rewrite Hm; lia) Hst ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia))
        as (HDC' & HK' & Ho' & R' & Eext & HL' & HX' & HW' & SS').
      pose proof (fw_rest_fields _ _ R') as ((Est & _ & _ & _ & Epd & _) & (_ & _ & Elv & Esy & _) & _).
      pose proof (fill_window_keep s) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ksum).
      assert (HF' : RTI (fill_window s)).
      { split; [exact HDC'|]. split; [rewrite HK'; exact HK|]. split; [rewrite Epd; exact Hp|].
        split; [unfold dmode; rewrite Elv, Esy; exact Hm|]. split; [rewrite Est; exact Hst | exact (OUTLE_trans _ _ _ Ho Ho')]. }
      pose proof (wf_ws _ _ _ HW') as Ews'.
      assert (HFW : ds_lookahead s <= MAX_MATCH -> fw_wf (ds_w_size s) (ds_hash_size s) s /\ DOK (fill_window s) /\ lz_keeps s (fill_window s)).
      { intros _. split; [exact HW|]. split; [exact (DC_DOK c0 _ HC0w HDC')|].
        pose proof HDC as [[_ _] V0]. pose proof HDC' as [[D' _] V'].
        exact (lz_keeps_intro c0 s (fill_window s) D D' V0 V' HK' Ho'). }
      assert (SS : ds_strstart (fill_window s) + MAX_MATCH < 2 * ds_w_size s) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; clear - SS'; lia).
      destruct ((ds_lookahead (fill_window s) <=? MAX_MATCH) && (flush =? Z_NO_FLUSH)) eqn:E1.
      + cbn [fst snd]. split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
        split; [intros HH; discriminate HH|]. split; [intros HH; discriminate HH|].
        split; [intros bs Hbs; injection Hbs as <-; reflexivity|]. split; [intros HH; discriminate HH | exact SS].
      + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [E0|E0]; cbn [fst snd].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros HH; discriminate HH|]. split; [intros _; exact E0|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | exact SS].
        * split; [exact HF'|]. split; [unfold lz_meas; exact Ksum|]. split; [exact HFW|]. split; [exact Ews'|].
          split; [intros _; lia|]. split; [intros HH; discriminate HH|].
          split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | exact SS].
    - cbn [fst snd]. split; [exact HF|]. split; [reflexivity|]. split; [intros HH; exfalso; lia|]. split; [reflexivity|].
      split; [intros _; unfold MAX_MATCH in Hl0; lia|]. split; [intros HH; discriminate HH|].
      split; [intros bs Hbs; discriminate Hbs|]. split; [intros HH; discriminate HH | clear - Hl0 Hsl; lia].
  Qed.

  Lemma rtally_lit : forall s1 v, RTI s1 ->
    let s3 := set_match_length s1 v in
    let r := tr_tally_lit s3 (arr_get (ds_window s3) (ds_strstart s3)) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 v HF s3 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    pose proof (tally_lit_facts s3 (arr_get (ds_window s3) (ds_strstart s3))) as (TK & Esn & Ebf & Edt & Ebt & Elt & Rl & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3) by (apply (BQ_same s1); try reflexivity; exact (DX_BQ s1 X)).
    assert (N3 : nsym s3 = nsym s1) by reflexivity.
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    destruct (BQ_tally_lit s3 BQ3 ltac:(change (ds_lit_bufsize s1 + ds_sym_next s1 + 3 <= arr_len (ds_pending_buf s1)); rewrite (df_bl _ D); lia)
                ltac:(change (0 <= ds_lit_bufsize s1); lia) ltac:(rewrite N3; lia) ltac:(change (L_CODES <= arr_len (ds_dyn_ltree_fc s1)); rewrite L1; unfold L_CODES; lia)
                (arr_get (ds_window s3) (ds_strstart s3))) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    split; [| rewrite Ebf; reflexivity].
    eapply tally_common.
    - change (forall j, 0 <= j < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s1) j < 256). exact (df_bb _ D).
    - change (forall i, 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TL).
    - change (forall i, 0 <= arr_get (ds_dyn_dtree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TD).
    - exact TK.
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - left. exact Edt.
    - exact Ebt.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - destruct TK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehmk & _). exact Ehmk.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_lit, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Lemma rtally_dist : forall s1 v, RTI s1 ->
    let s3 := set_match_length s1 v in
    let r := tr_tally_dist s3 1 (v - MIN_MATCH) in
    TALLYF s3 (fst r) /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1).
  Proof.
    intros s1 v HF s3 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    set (len := v - MIN_MATCH).
    pose proof (tally_dist_facts s3 1 len) as (TK & Esn & Ebf & Ebt & Rl & Rd & Rp). cbv zeta in *.
    assert (BQ3 : BQ s3) by (apply (BQ_same s1); try reflexivity; exact (DX_BQ s1 X)).
    assert (N3 : nsym s3 = nsym s1) by reflexivity.
    pose proof (df_tl _ D) as TL. unfold tree_lens in TL. destruct TL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    destruct (BQ_tally_dist s3 BQ3 ltac:(change (ds_lit_bufsize s1 + ds_sym_next s1 + 3 <= arr_len (ds_pending_buf s1)); rewrite (df_bl _ D); lia)
                ltac:(change (0 <= ds_lit_bufsize s1); lia) ltac:(rewrite N3; lia) ltac:(change (L_CODES <= arr_len (ds_dyn_ltree_fc s1)); rewrite L1; unfold L_CODES; lia)
                ltac:(change (D_CODES <= arr_len (ds_dyn_dtree_fc s1)); rewrite L3; unfold D_CODES; lia)
                1 len ltac:(lia)) as (BQ4 & N4 & _).
    cbv zeta in BQ4, N4.
    pose proof (tally_dist_fields s3 1 len) as (_ & _ & _ & Elt & Edt & _). cbv zeta in Elt, Edt.
    split; [| rewrite Ebf; reflexivity].
    eapply tally_common.
    - change (forall j, 0 <= j < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s1) j < 256). exact (df_bb _ D).
    - change (forall i, 0 <= arr_get (ds_dyn_ltree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TL).
    - change (forall i, 0 <= arr_get (ds_dyn_dtree_fc s1) i < 65536). exact (dx_tfc _ X DeflateState.TD).
    - exact TK.
    - exact Esn.
    - exact Rp.
    - eexists. eexists. exact Elt.
    - right. eexists. eexists. exact Edt.
    - exact Ebt.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - destruct TK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehmk & _). exact Ehmk.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - unfold tr_tally_dist, set_Freq, sym_buf_set; cbn [fst tree_fc set_tree_fc]; dsred; reflexivity.
    - exact BQ4.
    - exact N4.
  Qed.

  Definition RTREL (s1 s7 : deflate_state) (adv : Z) : Prop :=
    TF s7 = TF s1 /\ ds_strstart s7 = ds_strstart s1 + adv /\ ds_lookahead s7 = ds_lookahead s1 - adv
    /\ 0 <= ds_match_length s7 < MIN_MATCH /\ ds_match_start s7 = ds_match_start s1
    /\ ds_head s7 = ds_head s1 /\ ds_prev s7 = ds_prev s1 /\ ds_ins_h s7 = ds_ins_h s1
    /\ arr_len (ds_pending_buf s7) = arr_len (ds_pending_buf s1)
    /\ (forall i, 0 <= i < ds_lit_bufsize s1 * 4 -> 0 <= arr_get (ds_pending_buf s7) i < 256)
    /\ arr_len (ds_dyn_ltree_fc s7) = arr_len (ds_dyn_ltree_fc s1) /\ arr_len (ds_dyn_dtree_fc s7) = arr_len (ds_dyn_dtree_fc s1)
    /\ (forall i, 0 <= arr_get (ds_dyn_ltree_fc s7) i < 65536) /\ (forall i, 0 <= arr_get (ds_dyn_dtree_fc s7) i < 65536)
    /\ BQ s7 /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3.

  Lemma rtally_stage : forall s1, RTI s1 -> 1 <= ds_lookahead s1 ->
    let r := rl_tally (rl_run s1) in
    (exists adv, RTREL s1 (fst r) adv /\ 1 <= adv <= ds_lookahead s1 /\ adv <= 258)
    /\ snd r = (ds_sym_next s1 + 3 =? ds_sym_end s1)
    /\ 0 <= ds_match_length (rl_run s1) <= ds_lookahead s1 /\ ds_match_length (rl_run s1) <= MAX_MATCH
    /\ (exists v, rl_run s1 = set_match_length s1 v).
  Proof.
    intros s1 HF Hl1 r. subst r.
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct (rl_run_facts s1 ltac:(lia)) as (v & Erun & Hv & Hv2). rewrite Erun.
    split; [| split; [| split; [dsred; exact Hv | split; [dsred; exact Hv2 | exists v; reflexivity]]]].
    all: unfold rl_tally; change (ds_match_length (set_match_length s1 v)) with v.
    all: destruct (Z.leb_spec MIN_MATCH v) as [H3|H3].
    -
      destruct (rtally_dist s1 v HF) as [TY Ebf]. cbv zeta in TY, Ebf.
      destruct (tr_tally_dist (set_match_length s1 v) 1 (v - MIN_MATCH)) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      change (ds_match_length (set_match_length s1 v)) with v in Eml4.
      exists v. split; [| unfold MAX_MATCH, MIN_MATCH in Hv2, H3; lia].
      unfold RTREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4. dsred.
      split; [etransitivity; [| exact T4]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [unfold MIN_MATCH; lia|]. repeat (split; [reflexivity|]).
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4 | exact Esn4].
    -
      destruct (rtally_lit s1 v HF) as [TY Ebf]. cbv zeta in TY, Ebf.
      destruct (tr_tally_lit (set_match_length s1 v) _) as [s4 bf]. cbn [fst snd] in TY, Ebf |- *.
      destruct TY as (T4 & Estr4 & Elook4 & Eml4 & Ems4 & Ehd4 & Epv4 & Eih4 & Lpb4 & Bpb4 & Llt4 & Ldt4 & Blt4 & Bdt4 & BQ4 & N4 & Esn4).
      change (ds_match_length (set_match_length s1 v)) with v in Eml4.
      exists 1. split; [| lia].
      unfold RTREL. dsred. rewrite Estr4, Elook4, Eml4, Ems4, Ehd4, Epv4, Eih4. dsred.
      split; [etransitivity; [| exact T4]; reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. repeat (split; [reflexivity|]).
      split; [exact Lpb4|]. split; [exact Bpb4|]. split; [exact Llt4|]. split; [exact Ldt4|]. split; [exact Blt4|]. split; [exact Bdt4|].
      split; [apply (BQ_same s4); dsred; try reflexivity; exact BQ4|].
      split; [unfold nsym in *; dsred; exact N4 | exact Esn4].
    - destruct (rtally_dist s1 v HF) as [_ Ebf]. cbv zeta in Ebf.
      destruct (tr_tally_dist (set_match_length s1 v) 1 (v - MIN_MATCH)) as [s4 bf]. cbn [fst snd] in Ebf |- *. exact Ebf.
    - destruct (rtally_lit s1 v HF) as [_ Ebf]. cbv zeta in Ebf.
      destruct (tr_tally_lit (set_match_length s1 v) _) as [s4 bf]. cbn [fst snd] in Ebf |- *. exact Ebf.
  Qed.

  Lemma rtrip_end : forall s1 s7 adv, RTI s1 -> 1 <= ds_lookahead s1 -> RTREL s1 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    dwf s7 /\ SV c0 s7 /\ KV s7 = KV s0 /\ ds_pending s7 = 0 /\ dmode s7 = 2 /\ ds_status s7 <> FINISH_STATE /\ OUTLE s0 s7
    /\ ds_strm s7 = ds_strm s1 /\ lz_meas s7 < lz_meas s1 /\ 0 <= ds_lookahead s7 <= 2 * ds_w_size s1
    /\ nsym s7 = nsym s1 + 1 /\ ds_sym_next s7 = ds_sym_next s1 + 3 /\ ds_sym_end s7 = ds_sym_end s1 /\ ds_lit_bufsize s7 = ds_lit_bufsize s1
    /\ (nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7)
    /\ fb_entry s7 0
    /\ DXX s7 /\ BND s7.
  Proof.
    intros s1 s7 adv HF Hl1 TR Hadv Hadv2.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s1 HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    destruct TR as (T7 & Estr7 & Elook7 & Hml7 & Ems7 & Ehd7 & Epv7 & Eih7 & Lpb7 & Bpb7 & Llt7 & Ldt7 & Blt7 & Bdt7 & BQ7 & N7 & Esn7).
    pose proof (TF_fields _ _ T7) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eins & Ews & Epl & Ema & Epm & Emt & Ehw & Ewsz) & (Ebs & Ewr & Est & Elbs & Ebl & Eldl & Eddl & Ebdl)
                                        & (Edep & Eblc & Eol & Esl & Ehs & Ewm & Ehm & Ehsh) & (Estrm & Epd & Epo & Ebv & Ebb & Elf & Ewin & EKV & Ese) & (Ewb & Ehb & Epbs & Egz & Eme & Ehp)).
    assert (Em7 : dmode s7 = 2) by (unfold dmode; rewrite Elv, Esy; exact Hm).
    pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl. pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc.
    assert (Htfc7 : forall t i, 0 <= arr_get (tree_fc s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_fc]; [apply Blt7 | apply Bdt7 | rewrite Ebl; apply (Xtfc DeflateState.TB i)]. }
    assert (Htdl7 : forall t i, 0 <= arr_get (tree_dl s7 t) i < 65536).
    { intros t i. destruct t; cbn [tree_dl]; rewrite ?Eldl, ?Eddl, ?Ebdl; [apply (Xtdl DeflateState.TL i) | apply (Xtdl DeflateState.TD i) | apply (Xtdl DeflateState.TB i)]. }
    assert (HC7 : CHAIN s7 (ds_strstart s7 - 1) (ds_strstart s7 - 1)).
    { apply (CHAIN_same s1); [exact Ehd7 | exact Epv7 | exact Ehs | exact Ews | exact Ewm |].
      rewrite Estr7. eapply CHAIN_mono; [| | exact (dx_chain _ X ltac:(rewrite Hm; lia))]; clear - Hadv; lia. }
    assert (D7 : dwf s7).
    { apply (dwf_TF_transfer s1 s7 D T7); rewrite ?Estr7, ?Elook7, ?Ems7, ?Eih7, ?Ehd7, ?Epv7; try reflexivity; try assumption.
      - clear - Hstr Hadv. lia.
      - clear - Hadv. lia.
      - clear - Hsl. lia.
      - pose proof (df_ins _ D). clear - H Hadv. lia.
      - exact (df_ms _ D).
      - pose proof (dx_insh _ X). clear - H. lia.
      - exact (df_hb _ D).
      - exact (df_pb _ D). }
    assert (XX7 : DXX s7).
    { apply (DXX_TF_transfer s1 s7 X T7); rewrite ?Eih7, ?Hm; try assumption.
      - exact (dx_insh _ X).
      - unfold MAX_MATCH, MIN_MATCH in *. clear - Hml7. lia.
      - intros HH. discriminate HH.
      - intros HH. discriminate HH.
      - clear. lia. }
    assert (V7 : SV c0 s7) by (apply (SV_strm c0 s1); [exact Estrm | exact V]).
    assert (Hl7 : ds_level s7 <> 0) by (intros E0; unfold dmode in Em7; rewrite E0 in Em7; discriminate Em7).
    assert (X7 : nsym s7 <= ds_lit_bufsize s7 - 2 -> DX s7).
    { intros Hn7. destruct BQ7 as (Q1 & Q2 & Q3 & Q4).
      apply (DXX_DX s7 XX7 (SLOW3_mode s7 ltac:(rewrite Em7; lia))); rewrite ?Em7, ?Emt, ?N7, ?Eol, ?Esl, ?Epd, ?Epo, ?Ebv, ?Ebs, ?Ema; try assumption.
      - pose proof (RefDeflSafeI1.dx_matches _ X) as HM. clear - HM. lia.
      - rewrite <- N7. exact Q1.
      - revert Hn7. rewrite N7, Elbs. clear - Hn. intros Hn7. lia.
      - rewrite <- N7. exact Q3.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros _. rewrite Estr7, Hma. clear - Hext Hn Hadv Hadv2. lia.
      - intros _. exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - intros _. exact HC7. }
    assert (FE7 : fb_entry s7 0).
    { apply (fb_entry_intro c0 s7 0 HC0w D7 V7); rewrite ?Epd, ?Epo, ?Ebv, ?Eol, ?Esl, ?Edep, ?Eblc, ?Elv, ?Estr7, ?Ebs, ?N7, ?Elbs; try assumption.
      - exact (dx_pout0 _ X Hp).
      - exact (dx_biv _ X).
      - clear - Hn. lia.
      - exact (dx_opt _ X).
      - exact (dx_stat _ X).
      - intros E0. apply Hl7. rewrite Elv. exact E0.
      - clear - Hext Hn Hadv Hadv2. lia.
      - clear. lia. }
    split; [exact D7|]. split; [exact V7|]. split; [rewrite EKV; exact HK|]. split; [rewrite Epd; exact Hp|]. split; [exact Em7|].
    split; [rewrite Est; exact Hst|]. split; [apply (OUTLE_trans _ s1); [exact Ho | apply OUTLE_strm; exact Estrm]|].
    split; [exact Estrm|]. split; [unfold lz_meas; rewrite Estrm, Elook7; clear - Hadv; lia|]. split; [rewrite Elook7; clear - Hadv Hlook Hsl Hstr; lia|].
    split; [exact N7|]. split; [exact Esn7|]. split; [exact Ese|]. split; [exact Elbs|]. split; [exact X7|]. split; [exact FE7|].
    split; [exact XX7 | exact (conj (fun _ => HC7) (SLOW3_mode s7 ltac:(rewrite Em7; lia)))].
  Qed.

  Definition RRET (s' : deflate_state) (bs : block_state) : Prop :=
    DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ bs = need_more.

  Lemma rflush : forall s last, dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s = 2 -> BND s ->
    KV s = KV s0 -> OUTLE s0 s ->
    let s' := flush_block_only s last in
    fblk_ok fb_safe s last
    /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ dmode s' = 2 /\ ds_status s' <> FINISH_STATE
    /\ ds_lookahead s' = ds_lookahead s /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
    /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ ds_match_available s' = ds_match_available s.
  Proof.
    intros s last D V XX FE Hst Hm B HK Ho s'.
    pose proof (flush_block_only_facts c0 s last HFB HC0w D V XX FE Hst ltac:(rewrite Hm; lia) B) as FB. cbv zeta in FB.
    destruct FB as (FO & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
    subst s'. pose proof DC' as [[D' X'] V'].
    pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema' & _) & (Est' & _) & _).
    split; [apply (fblk_ok_intro s last FO (SV_aout c0 _ HC0w V') (lz_keeps_intro c0 _ _ D D' V V' HK' Ho'))|].
    split; [exact DC'|]. split; [rewrite HK'; exact HK|]. split; [exact (OUTLE_trans _ _ _ Ho Ho')|].
    split; [rewrite (dmode_PF _ _ EPF); exact Hm|]. split; [rewrite Est'; exact Hst|].
    split; [exact Elook'|]. split; [exact Hpa|]. split; [exact Eain | exact Ema'].
  Qed.

  Lemma rle_outcome : forall s s1 s7 adv (bf : bool),
    RTI s1 -> lz_meas s1 = lz_meas s -> 1 <= ds_lookahead s1 -> RTREL s1 s7 adv -> 1 <= adv <= ds_lookahead s1 -> adv <= 258 ->
    bf = (ds_sym_next s1 + 3 =? ds_sym_end s1) ->
    (bf = true -> fblk_ok fb_safe s7 0)
    /\ match snd (st_bflush0 s7 bf) with
       | LCont => RTI (fst (st_bflush0 s7 bf)) /\ lz_meas (fst (st_bflush0 s7 bf)) < lz_meas s
       | LBreak => RTI (fst (st_bflush0 s7 bf)) /\ ds_lookahead (fst (st_bflush0 s7 bf)) = 0
       | LRet bs => RRET (fst (st_bflush0 s7 bf)) bs
       end.
  Proof.
    intros s s1 s7 adv bf HF1 Emeas Hl1 TR Hadv Hadv2 Ebf.
    pose proof (RTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    pose proof (rtrip_end s1 s7 adv HF1 Hl1 TR Hadv Hadv2) as TE.
    destruct TE as (D7 & V7 & HK7 & Hp7 & Hm7 & Hst7 & Ho7 & Estrm7 & Hmeas7 & Hl7 & N7 & Esn7 & Ese7 & Elbs7 & X7 & FE7 & XX7 & B7).
    split; [intros _; exact (proj1 (rflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7))|].
    unfold st_bflush0. destruct bf.
    - rewrite flush_block_eq'.
      pose proof (rflush s7 0 D7 V7 XX7 FE7 Hst7 Hm7 B7 HK7 Ho7) as FB. cbv zeta in FB.
      destruct FB as (_ & DC' & HK' & Ho' & Hm' & Hst' & Elook' & Hpa & Eain & _).
      set (s' := flush_block_only s7 0) in *. clearbody s'.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [Z.eqb negb fst snd].
      + split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. reflexivity.
      + split.
        * split; [exact DC'|]. split; [exact HK'|]. split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)]|].
          split; [exact Hm'|]. split; [exact Hst'|]. exact Ho'.
        * unfold lz_meas. rewrite Elook', Eain. unfold lz_meas in Hmeas7, Emeas. rewrite <- Emeas. exact Hmeas7.
    - cbn [fst snd].
      assert (Hn7 : nsym s7 <= ds_lit_bufsize s7 - 2).
      { symmetry in Ebf. apply Z.eqb_neq in Ebf. rewrite (df_symend _ D1) in Ebf. rewrite Elbs7, N7. clear - Ebf Hsn1 Hn1. lia. }
      split.
      + split; [split; [split; [exact D7 | exact (X7 Hn7)] | exact V7]|]. split; [exact HK7|]. split; [exact Hp7|].
        split; [exact Hm7|]. split; [exact Hst7|]. exact Ho7.
      + rewrite <- Emeas. exact Hmeas7.
  Qed.

  Lemma rl_body_eq2 : forall s,
    rl_body s flush = match snd (rl_fill s flush) with
                      | Some o => (fst (rl_fill s flush), o)
                      | None => st_bflush0 (fst (rl_tally (rl_run (fst (rl_fill s flush))))) (snd (rl_tally (rl_run (fst (rl_fill s flush)))))
                      end.
  Proof.
    intros s. unfold rl_body. destruct (rl_fill s flush) as [s1 e]. cbn [fst snd]. destruct e; [reflexivity|]. destruct (rl_tally (rl_run s1)); reflexivity.
  Qed.

  Lemma rle_step : forall s, RTI s ->
    rl_trip_ok fb_safe s flush
    /\ match snd (rl_body s flush) with
       | LCont => RTI (fst (rl_body s flush)) /\ lz_meas (fst (rl_body s flush)) < lz_meas s
       | LBreak => RTI (fst (rl_body s flush)) /\ ds_lookahead (fst (rl_body s flush)) = 0
       | LRet bs => RRET (fst (rl_body s flush)) bs
       end.
  Proof.
    intros s HF.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (rfill_stage s HF) as FS. cbv zeta in FS.
    destruct FS as (HF1 & Emeas & Hfw & Ews1 & Hnone & Hbrk & Hret & Hnc & Hss1).
    rewrite rl_body_eq2.
    set (s1 := fst (rl_fill s flush)) in *.
    pose proof HF1 as (HDC1 & HK1 & Hp1 & Hm1 & Hst1 & Ho1).
    pose proof (RTI_facts s1 HF1) as (D1 & X1 & V1 & Sw1 & Sh1 & Sl1 & Hma1 & Hn1 & Hsn1 & Hse1 & Hstr1 & Hlook1 & Hsl1 & Hext1).
    destruct (snd (rl_fill s flush)) as [o|] eqn:Eo.
    - split.
      { split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros HH; rewrite Eo in HH; discriminate HH. }
      cbn [fst snd]. destruct o as [| |bs].
      + exfalso. exact (Hnc eq_refl).
      + split; [exact HF1 | exact (Hbrk eq_refl)].
      + rewrite (Hret bs eq_refl). split; [exact HDC1|]. split; [exact HK1|]. split; [exact Ho1 | reflexivity].
    - pose proof (Hnone eq_refl) as Hl1.
      pose proof (rtally_stage s1 HF1 Hl1) as TS. cbv zeta in TS. destruct TS as ((adv & TR & Hadv & Hadv2) & Ebf & Hml2 & Hml2' & (v & Erun)).
      pose proof (rle_outcome s s1 (fst (rl_tally (rl_run s1))) adv (snd (rl_tally (rl_run s1))) HF1 Emeas Hl1 TR Hadv Hadv2 Ebf) as [FOK OUT].
      split; [| exact OUT].
      split; [exact (DC_DOK c0 s HC0w HDC)|]. split; [exact Hfw|]. intros _.
      change ((DOK s1 /\ 1 <= ds_lookahead s1 /\ ds_strstart s1 + ds_lookahead s1 <= 2 * ds_w_size s1
               /\ (MIN_MATCH <= ds_lookahead s1 -> 0 < ds_strstart s1 -> ds_strstart s1 + MAX_MATCH < 2 * ds_w_size s1)
               /\ (forall j, 0 <= j < 2 * ds_w_size s1 -> 0 <= arr_get (ds_window s1) j < 256))
              /\ (DOK (rl_run s1) /\ 1 <= ds_lookahead (rl_run s1) /\ ds_strstart (rl_run s1) + ds_lookahead (rl_run s1) <= 2 * ds_w_size (rl_run s1)
                  /\ 0 <= ds_match_length (rl_run s1) <= ds_lookahead (rl_run s1) /\ ds_match_length (rl_run s1) <= MAX_MATCH
                  /\ 0 <= ds_sym_next (rl_run s1) /\ ds_sym_next (rl_run s1) + 3 <= 3 * ds_lit_bufsize (rl_run s1) /\ 0 <= ds_sym_end (rl_run s1) < 2 ^ 32
                  /\ (forall j, 0 <= j < 2 * ds_w_size (rl_run s1) -> 0 <= arr_get (ds_window (rl_run s1)) j < 256)
                  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc (rl_run s1)) i < 65536)
                  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (ds_dyn_dtree_fc (rl_run s1)) i < 65536)
                  /\ (snd (rl_tally (rl_run s1)) = true -> fblk_ok fb_safe (fst (rl_tally (rl_run s1))) 0))).
      split.
      + split; [exact (DC_DOK c0 s1 HC0w HDC1)|]. split; [exact Hl1|]. split; [exact Hsl1|].
        split; [intros _ _; rewrite Ews1; exact Hss1|]. exact (df_wb _ D1).
      + rewrite Erun in Hml2, Hml2' |- *. revert Hml2 Hml2' FOK. rewrite Erun. dsred. intros Hml2 Hml2' FOK.
        destruct (DD_set_insert s1 (ds_insert s1) D1 X1 (df_ins _ D1) (dx_ins _ X1)) as [_ _].
        split.
        { pose proof (DC_DOK c0 s1 HC0w HDC1) as OK1. destruct OK1; constructor; dsred; assumption. }
        split; [exact Hl1|]. split; [exact Hsl1|]. split; [exact Hml2|]. split; [exact Hml2'|].
        split; [clear - Hsn1 Hn1; lia|]. split; [clear - Hsn1 Hn1; lia|]. split; [rewrite Hse1; clear - Sl1; lia|].
        split; [exact (df_wb _ D1)|]. split; [intros i _; exact (dx_tfc _ X1 DeflateState.TL i)|].
        split; [intros i _; exact (dx_tfc _ X1 DeflateState.TD i) | exact FOK].
  Qed.

  Lemma rle_loop : forall fuel s, RTI s -> lz_meas s < Z.of_nat fuel ->
    rl_loop_ok fb_safe fuel s flush
    /\ match snd (deflate_rle_loop fuel s flush) with
       | None => RTI (fst (deflate_rle_loop fuel s flush)) /\ ds_lookahead (fst (deflate_rle_loop fuel s flush)) = 0
       | Some bs => RRET (fst (deflate_rle_loop fuel s flush)) bs
       end.
  Proof.
    induction fuel as [|f IH]; intros s HI Hmz.
    { exfalso. pose proof (RTI_facts s HI) as (D & _ & V & _). pose proof (sv_ain _ _ V). pose proof (df_look _ D). unfold lz_meas in Hmz. cbn [Z.of_nat] in Hmz. lia. }
    rewrite rl_loop_ok_S, rloop_step. destruct (rle_step s HI) as [HT HC].
    destruct (snd (rl_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (rl_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
    - cbn [fst snd]. split; [exact (conj HT I) | exact HC].
  Qed.

  Lemma rle_tail : forall s, RTI s -> ds_lookahead s = 0 ->
    tail0_ok fb_safe s flush
    /\ BFPOST c0 s0 flush (tail0 s flush).
  Proof.
    intros s HF Hl0.
    pose proof HF as (HDC & HK & Hp & Hm & Hst & Ho).
    pose proof (RTI_facts s HF) as (D & X & V & Sw & Sh & Sl & Hma & Hn & Hsn & Hse & Hstr & Hlook & Hsl & Hext).
    set (st := set_insert s 0).
    destruct (DD_set_insert s 0 D X ltac:(clear - Hstr; lia) ltac:(clear - Sw; lia)) as [Dst Xst]. fold st in Dst, Xst.
    assert (Vst : SV c0 st) by (apply (SV_strm c0 s st eq_refl V)).
    assert (DCst : DC c0 st) by (exact (conj (conj Dst Xst) Vst)).
    assert (Hpst : ds_pending st = 0) by (exact Hp).
    assert (Hmst : dmode st = 2) by (exact Hm).
    assert (Hstst : ds_status st <> FINISH_STATE) by (exact Hst).
    assert (HKst : KV st = KV s0) by (exact HK).
    assert (Hlst : ds_lookahead st = 0) by (exact Hl0).
    assert (Host : OUTLE s0 st) by (exact Ho).
    assert (Hmast : ds_match_available st = 0) by (exact Hma).
    assert (FB : forall last, 0 <= last <= 1 ->
      let s' := flush_block_only st last in
      fblk_ok fb_safe st last /\ DC c0 s' /\ KV s' = KV s0 /\ OUTLE s0 s' /\ ds_lookahead s' = 0 /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
      /\ ds_match_available s' = 0).
    { intros last Hlast.
      pose proof (rflush st last Dst Vst (DX_DXX _ Xst) (DC_fb_entry c0 st last HC0w DCst Hpst ltac:(rewrite Hmst; lia) Hlast) Hstst Hmst (DX_BND st Xst) HKst Host) as FB. cbv zeta in FB.
      destruct FB as (FO & DC' & HK' & Ho' & _ & _ & Elook' & Hpa & _ & Ema').
      cbv zeta. split; [exact FO|]. split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
      split; [rewrite Elook'; exact Hlst|]. split; [exact Hpa | rewrite Ema'; exact Hmast]. }
    split.
    - unfold tail0_ok. cbv zeta. fold st.
      split; [exact (DC_DOK c0 st HC0w DCst)|].
      split; [intros _; exact (proj1 (FB 1 ltac:(lia))) | intros _ _; exact (proj1 (FB 0 ltac:(lia)))].
    - unfold tail0. fold st. unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4].
      + rewrite flush_block_eq'. destruct (FB 1 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
        set (s' := flush_block_only st 1) in *. clearbody s'.
        destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros HH; discriminate HH.
        * split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
          split; [intros _; exact Hl'|]. intros _. destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)].
      + destruct (Z.eqb_spec (ds_sym_next st) 0) as [N0|N0]; cbn [negb].
        * unfold BFPOST; cbn [fst snd].
          split; [exact DCst|]. split; [exact HKst|]. split; [exact Host|]. split; [intros _; split; [exact Hpst | split; [exact F4 | exact Hmast]]|].
          split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
        * rewrite flush_block_eq'. destruct (FB 0 ltac:(lia)) as (_ & DC' & HK' & Ho' & Hl' & Hpa & Hma').
          set (s' := flush_block_only st 0) in *. clearbody s'.
          destruct (Z.eqb_spec (cs_avail_out (ds_strm s')) 0) as [A0|A0]; cbn [negb Z.eqb]; unfold BFPOST; cbn [fst snd].
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
          -- split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|].
             split; [intros _; split; [destruct Hpa as [P0|A00]; [exact P0 | exfalso; exact (A0 A00)] | split; [exact F4 | exact Hma']]|].
             split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
  Qed.

End Rle.


Theorem rle_bf_spec : FB_CALL -> BF_SPEC 2 (rle_ok fb_safe) deflate_rle.
Proof.
  intros HFB c0 s flush (HC0 & HDC & Hp & Hst & Hfl) Hm.
  assert (HF : RTI c0 s s).
  { split; [exact HDC|]. split; [reflexivity|]. split; [exact Hp|]. split; [exact Hm|]. split; [exact Hst | apply OUTLE_refl]. }
  pose proof HDC as [[D X] V].
  assert (Hmz : 0 <= lz_meas s) by (unfold lz_meas; pose proof (df_look _ D); pose proof (sv_ain _ _ V); lia).
  destruct (rle_loop c0 s flush HC0 HFB (lz_fuel s) s HF (lz_fuel_meas s Hmz)) as [HL HR].
  assert (POST : BFPOST c0 s flush (deflate_rle s flush)).
  { unfold deflate_rle.
    destruct (deflate_rle_loop (lz_fuel s) s flush) as [s' r] eqn:E. cbn [fst snd] in HR.
    destruct r as [bs|].
    + destruct HR as (DC' & HK' & Ho' & ->). unfold BFPOST; cbn [fst snd].
      split; [exact DC'|]. split; [exact HK'|]. split; [exact Ho'|]. split; [intros HH; discriminate HH|].
      split; [intros [HH|HH]; discriminate HH|]. intros HH; discriminate HH.
    + destruct HR as [HF' Hl']. exact (proj2 (rle_tail c0 s flush HC0 HFB _ HF' Hl')). }
  split; [| exact POST].
  unfold rle_ok. split; [exact HL|]. split.
  - destruct (snd (deflate_rle_loop (lz_fuel s) s flush)); [exact I|].
    destruct HR as [HF' Hl']. exact (proj1 (rle_tail c0 s flush HC0 HFB _ HF' Hl')).
  - destruct POST as (DC' & HK' & Ho' & _). pose proof DC' as [[D' X'] V'].
    split; [exact (lz_keeps_intro c0 _ _ D D' V V' HK' Ho') | exact (DC_DOK c0 _ (c0'_ok _ HC0) DC')].
Qed.
End RefDeflSafeL4.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeL4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeL5.

Module RefDeflFast5.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow4.RefDeflFast4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 96).

Local Ltac nf := cbn [dfF].
Lemma sx32_cases : forall a, 0 <= a < 2 ^ 32 ->
  (a < 2 ^ 31 /\ szwrap 32 a mod 2 ^ 64 = a) \/ (2 ^ 31 <= a /\ szwrap 32 a mod 2 ^ 64 = a + 2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  change (2 ^ 31) with 2147483648. change (2 ^ 64) with 18446744073709551616.
  destruct (Z_lt_le_dec a 2147483648).
  - left. split; [lia|]. rewrite (Z.mod_small (a + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
  - right. split; [lia|]. replace ((a + 2147483648) mod 4294967296) with (a + 2147483648 - 4294967296) by (Z.to_euclidean_division_equations; lia).
    Z.to_euclidean_division_equations; lia.
Qed.
Lemma sx32_u64_ge : forall a q, 0 <= a < 2 ^ 32 -> 0 <= q < 2 ^ 31 -> q <= a -> q <= szwrap 32 a mod 2 ^ 64.
Proof. intros a q Ha Hp Hle. destruct (sx32_cases a Ha) as [[? E]|[? E]]; rewrite E; lia. Qed.
Lemma sx32_u64_nz : forall a, 0 < a < 2 ^ 32 -> szwrap 32 a mod 2 ^ 64 <> 0.
Proof. intros a Ha. destruct (sx32_cases a ltac:(lia)) as [[? E]|[? E]]; rewrite E; lia. Qed.
Lemma snez_sx32 : forall a, 0 <= a < 2 ^ 32 -> (if 0 <? szwrap 32 a mod 2 ^ 64 then 1 else 0) = (if 0 <? a then 1 else 0).
Proof.
  intros a Ha. destruct (sx32_cases a Ha) as [[? E]|[? E]]; rewrite E; [reflexivity|].
  destruct (Z.ltb_spec 0 (a + 2 ^ 64 - 2 ^ 32)); destruct (Z.ltb_spec 0 a); first [reflexivity | lia].
Qed.

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P20 := fresh "P20" in
  let P19 := fresh "P19" in let P18 := fresh "P18" in let P22 := fresh "P22" in let P21 := fresh "P21" in
  pose proof HRG as (P8 & P2 & P9 & P20 & P19 & P18 & P22 & P21).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].

Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].

Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.
Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P20 := fresh "P20" in
  let P19 := fresh "P19" in let P22 := fresh "P22" in let P21 := fresh "P21" in
  pose proof HRG as (P8 & P2 & P9 & P20 & P19 & P22 & P21).



Definition fb_bufp (X : deflate_state) : Z :=
  if ds_block_start X <? 0 then 0 else W + wrap32 (ds_block_start X).
Definition fb_len (X : deflate_state) : Z := wrap64 (ds_strstart X - ds_block_start X).

Lemma bs_facts : forall bs, - 2 ^ 63 <= bs < 2 ^ 63 ->
  szwrap 64 (bs mod 2 ^ 64) = bs /\ (bs mod 2 ^ 64) mod 2 ^ 32 = wrap32 bs /\ 0 <= bs mod 2 ^ 64 < 2 ^ 64.
Proof.
  intros bs Hbs. split; [rewrite szwrap_mod by lia; apply szwrap_small; lia|].
  split; [rewrite wrap32_mod; apply mod_pow2_mod_pow2; lia|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma fp_len_eq : forall X, 0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) ->
  fp_len X = (if cs_avail_out (ds_strm X) <? ds_pending X then cs_avail_out (ds_strm X) else ds_pending X)
  /\ 0 <= fp_len X <= ds_pending X /\ fp_len X <= cs_avail_out (ds_strm X).
Proof.
  intros X Hp Ha. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia.
Qed.

Definition break_st (X : deflate_state) : deflate_state :=
  set_insert X (if ds_strstart X <? 2 then ds_strstart X else 2).

End Walk.
End RefDeflFast5.

Module RefDeflFast7.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefLmatch_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFillWin4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefTrFlushBits_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow4.RefDeflFast4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflFast5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 96).



Definition ILI (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2 ^ 31 /\ ds_hash_mask X = hs - 1 /\ ds_w_mask X = ws - 1 /\ 0 <= ds_hash_shift X < 32
  /\ 0 <= ds_sym_next X < 2 ^ 32 /\ 0 <= ds_sym_end X < 2 ^ 32 /\ 0 <= ds_lookahead X <= 2 * ws
  /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536)
  /\ arr_len (ds_head X) = hs.

Lemma tdist1_view : forall X,
  (ds_match_length (tdist1 X), ds_lookahead (tdist1 X), ds_max_lazy_match (tdist1 X), ds_strstart (tdist1 X), ds_hash_shift (tdist1 X),
   ds_hash_mask (tdist1 X), ds_sym_next (tdist1 X), ds_sym_end (tdist1 X), ds_dyn_dtree_fc (tdist1 X), ds_ins_h (tdist1 X), ds_w_mask (tdist1 X),
   ds_window (tdist1 X), ds_head (tdist1 X), ds_w_size (tdist1 X))
  = (ds_match_length X, ds_lookahead X, ds_max_lazy_match X, ds_strstart X, ds_hash_shift X,
     ds_hash_mask X, ds_sym_next X + 3, ds_sym_end X, ds_dyn_dtree_fc X, ds_ins_h X, ds_w_mask X, ds_window X, ds_head X, ds_w_size X).
Proof. intros X. unfold tdist1. dsred. reflexivity. Qed.

Lemma tdist2_view : forall X dc,
  (ds_match_length (tdist2 X dc), ds_lookahead (tdist2 X dc), ds_max_lazy_match (tdist2 X dc), ds_strstart (tdist2 X dc), ds_hash_shift (tdist2 X dc),
   ds_hash_mask (tdist2 X dc), ds_sym_next (tdist2 X dc), ds_sym_end (tdist2 X dc), ds_ins_h (tdist2 X dc), ds_w_mask (tdist2 X dc),
   ds_window (tdist2 X dc), ds_head (tdist2 X dc), ds_w_size (tdist2 X dc))
  = (ds_match_length X, ds_lookahead X - ds_match_length X, ds_max_lazy_match X, ds_strstart X, ds_hash_shift X,
     ds_hash_mask X, ds_sym_next X, ds_sym_end X, ds_ins_h X, ds_w_mask X, ds_window X, ds_head X, ds_w_size X).
Proof. intros X dc. unfold tdist2. dsred. reflexivity. Qed.

Lemma tlit1_view : forall X,
  (ds_lookahead (tlit1 X), ds_strstart (tlit1 X)) = (ds_lookahead X - 1, ds_strstart X + 1).
Proof. intros X. unfold tlit1. dsred. reflexivity. Qed.

Lemma noins_view : forall X,
  (ds_lookahead (noins_st X), ds_strstart (noins_st X), ds_sym_next (noins_st X), ds_sym_end (noins_st X))
  = (ds_lookahead X, ds_strstart X + ds_match_length X, ds_sym_next X, ds_sym_end X).
Proof. intros X. unfold noins_st. dsred. reflexivity. Qed.



Lemma flush_block_snd : forall s last,
  snd (flush_block s last)
  = (if cs_avail_out (ds_strm (fst (flush_block s last))) =? 0
     then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof.
  intros s last. unfold flush_block. cbv zeta.
  destruct (cs_avail_out (ds_strm (flush_block_only s last)) =? 0) eqn:E; cbn [fst snd]; rewrite E; reflexivity.
Qed.

End Walk.
End RefDeflFast7.

Module RefDeflSlow7.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefLmatch_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFillWin4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefTrFlushBits_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFast6.RefDeflFast3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSlow6.RefDeflSlow5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 112).

Lemma fpx_view : forall s len,
  (ds_strstart (fp_tail s len), ds_lookahead (fp_tail s len)) = (ds_strstart s, ds_lookahead s).
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); dsred; reflexivity. Qed.

Lemma flush_block_snd : forall s last,
  snd (flush_block s last)
  = (if cs_avail_out (ds_strm (fst (flush_block s last))) =? 0
     then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof.
  intros s last. unfold flush_block. cbv zeta.
  destruct (cs_avail_out (ds_strm (flush_block_only s last)) =? 0) eqn:E; cbn [fst snd]; rewrite E; reflexivity.
Qed.


Lemma flush_block_fst : forall s last, fst (flush_block s last) = flush_block_only s last.
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.


Definition ILIS (X : deflate_state) : Prop :=
  0 <= ds_strstart X /\ 0 <= ds_ins_h X < 2 ^ 31 /\ ds_hash_mask X = hs - 1 /\ ds_w_mask X = ws - 1 /\ 0 <= ds_hash_shift X < 32
  /\ 0 <= ds_sym_next X < 2 ^ 18 /\ 0 <= ds_sym_end X < 2 ^ 18 /\ 0 <= ds_lookahead X <= 2 * ws
  /\ (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256)
  /\ (forall j, 0 <= j < hs -> 0 <= arr_get (ds_head X) j < 65536)
  /\ arr_len (ds_head X) = hs.


Lemma ltail_avail : forall X, cs_avail_out (ds_strm (ltail_st X)) = cs_avail_out (ds_strm X).
Proof. intros X. unfold ltail_st. dsred. reflexivity. Qed.

End Walk.
End RefDeflSlow7.

Module RefDeflStored9.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefTrFlushBits_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored7.RefDeflStored3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored7.RefDeflStored6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 128).
Local Notation MB := (MBv ds).



Lemma sl_fix_facts : forall s,
  ds_strstart (sl_fix s) = ds_strstart s /\ ds_window (sl_fix s) = ds_window s /\ ds_strm (sl_fix s) = ds_strm s
  /\ ds_insert (sl_fix s) = (if ds_strstart s <? ds_insert s then ds_strstart s else ds_insert s)
  /\ ds_w_size (sl_fix s) = ds_w_size s /\ ds_block_start (sl_fix s) = ds_block_start s
  /\ ds_matches (sl_fix s) = (if ds_matches s <? 2 then ds_matches s + 1 else ds_matches s).
Proof.
  intros s. unfold sl_fix. destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s <? ds_insert s); dsred; repeat split; reflexivity.
Qed.


Lemma tlen_eq : forall have left, tlen have left = MIN left have.
Proof. intros have left. unfold tlen, MIN. destruct (Z.ltb_spec left have); destruct (Z.ltb_spec have left); lia. Qed.

Lemma fin_last_range : forall s f, 0 <= fin_last s f <= 1.
Proof. intros s f. unfold fin_last. destruct ((f =? Z_FINISH) && (cs_avail_in (ds_strm s) =? 0) && (fin_len s =? wrap32 (ds_strstart s - ds_block_start s))); lia. Qed.

Lemma bs_code_last : forall last, 0 <= last <= 1 ->
  last * 2 ^ 1 = bs_code (if negb (last =? 0) then finish_started else need_more).
Proof. intros last H. assert (last = 0 \/ last = 1) as [->| ->] by lia; reflexivity. Qed.


Lemma st_fillw_facts : forall s n, 0 < n <= cs_avail_in (ds_strm s) ->
  ds_strstart (st_fillw s n) = ds_strstart s + n /\ ds_high_water (st_fillw s n) = ds_high_water s.
Proof.
  intros s n Hn. unfold st_fillw, read_buf.
  replace (negb (n =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  cbv zeta. rewrite (rb_len_eq n (cs_avail_in (ds_strm s)) Hn).
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  cbv iota beta. dsred. destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; split; reflexivity.
Qed.

Lemma st_wupd_facts : forall s u,
  ds_high_water (st_wupd s u) = ds_high_water s /\ ds_strm (st_wupd s u) = ds_strm s.
Proof.
  intros s u. unfold st_wupd.
  destruct (negb (u =? 0)); [| split; reflexivity].
  destruct (ds_w_size s <=? u); [dsred; split; reflexivity|].
  destruct (ds_window_size s - ds_strstart s <=? u); cbv zeta; dsred; [| split; reflexivity].
  destruct (ds_matches s <? 2); dsred; destruct (ds_strstart s - ds_w_size s <? ds_insert s); dsred; split; reflexivity.
Qed.

Lemma hw_st_facts : forall s,
  ds_strstart (hw_st s) = ds_strstart s /\ ds_block_start (hw_st s) = ds_block_start s /\ ds_strm (hw_st s) = ds_strm s
  /\ ds_window_size (hw_st s) = ds_window_size s /\ ds_w_size (hw_st s) = ds_w_size s.
Proof. intros s. unfold hw_st. destruct (_ <? _); dsred; repeat split; reflexivity. Qed.

Lemma fmin_range : forall have ai, 0 <= have -> 0 <= ai -> 0 <= fmin have ai <= have /\ fmin have ai <= ai.
Proof. intros have ai Hh Ha. unfold fmin. destruct (Z.ltb_spec ai have); lia. Qed.

End Walk.
End RefDeflStored9.

Module RefDeflate1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma szwrap32_hi : forall a, 2 ^ 31 <= a < 2 ^ 32 -> szwrap 32 a = a - 2 ^ 32.
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod64_nz : forall v, - 2 ^ 64 < v < 2 ^ 64 -> v <> 0 -> v mod 2 ^ 64 <> 0.
Proof.
  intros v Hv Hnz. destruct (Z_lt_le_dec v 0).
  - rewrite <- (Z.mod_add v 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.
Lemma mod64_z : forall v, v = 0 -> v mod 2 ^ 64 = 0.
Proof. intros v ->. reflexivity. Qed.

Lemma szwrap32_cases : forall a, 0 <= a < 2 ^ 32 ->
  (a < 2 ^ 31 /\ szwrap 32 a = a) \/ (2 ^ 31 <= a /\ szwrap 32 a = a - 2 ^ 32).
Proof.
  intros a Ha. destruct (Z_lt_le_dec a (2 ^ 31)).
  - left. split; [lia|]. apply szwrap_small; lia.
  - right. split; [lia|]. apply szwrap32_hi; lia.
Qed.


Definition ERRMSG2 : Z := 0x2dd08.
Definition ERRMSG5 : Z := 0x2dd40.

Definition cfg_func (lv : Z) : Z := if lv =? 0 then 0x136b0 else if lv <=? 3 then 0x141a8 else 0x148a8.

Definition deVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 16); (35%nat, 2 ^ 63)].

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.


Definition st4 (st : Z) : Prop := st = 42 \/ st = 57 \/ st = 113 \/ st = 666.


Definition rank_bad (old : Z) : bool := Z.leb (RANK flush) (RANK old) && negb (flush =? 4).

Local Ltac rb_tac old :=
  unfold rank_bad, RANK;
  destruct (Z.ltb_spec 4 flush); destruct (Z.ltb_spec 4 old); destruct (Z.eqb_spec flush 4);
  match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end; cbn [andb negb]; first [reflexivity | exfalso; lia].
Definition st42_st (X : deflate_state) : deflate_state :=
  if (ds_status X =? 42) && (ds_wrap X =? 0) then set_status X BUSY_STATE else X.

End Walk.
End RefDeflate1.

Module RefDeflate2.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.



Definition zp_msgc (v : Z) : zs_ptrs :=
  ZSP (zp_in zp) (zp_out zp) (zp_zalloc zp) (zp_zfree zp) (zp_opaque zp) (zp_reserved zp) (fun _ => v).

Lemma zsl_vals_msgc : forall st, zsl_vals (zp_msgc (zp_msg zp (cs_msg st))) S st = zsl_vals zp S st.
Proof. intros st. reflexivity. Qed.

Lemma zsl_vals_msg_upd : forall st v e, list_upd (zsl_vals zp S st) 6 v = zsl_vals (zp_msgc v) S (cset_msg st e).
Proof. intros st v e. destruct st; reflexivity. Qed.
Definition XVB : bounds := [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64)].

End Walk.
End RefDeflate2.

Module RefDeflate3.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.

Lemma fp_len_eq : forall X, 0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) ->
  fp_len X = (if cs_avail_out (ds_strm X) <? ds_pending X then cs_avail_out (ds_strm X) else ds_pending X)
  /\ 0 <= fp_len X <= ds_pending X /\ fp_len X <= cs_avail_out (ds_strm X).
Proof.
  intros X Hp Ha. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia.
Qed.

Lemma aout_hi_facts : forall a, 2 ^ 31 <= a < 2 ^ 32 ->
  szwrap 32 a = a - 2 ^ 32 /\ (szwrap 32 a) mod 2 ^ 64 = a - 2 ^ 32 + 2 ^ 64.
Proof.
  intros a Ha. pose proof (szwrap32_hi a Ha) as E. split; [exact E|]. rewrite E.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition FPOK (X : deflate_state) : Prop :=
  BINV PBL X
  /\ (let X1 := tr_flush_bits X in
      0 <= ds_pending X1 < 2 ^ 31 /\ ds_pending X1 <= PBL /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + fp_len X1 <= PBL
      /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64).

Definition FPst (X : deflate_state) : deflate_state :=
  let X1 := tr_flush_bits X in if fp_len X1 =? 0 then X1 else fp_tail X1 (fp_len X1).

Lemma FPst_eq : forall X, flush_pending X = FPst X.
Proof. intros X. rewrite flush_pending_eq. reflexivity. Qed.

Lemma fp_tail_strm : forall X1 len,
  cs_avail_out (ds_strm (fp_tail X1 len)) = cs_avail_out (ds_strm X1) - len
  /\ ds_pending (fp_tail X1 len) = ds_pending X1 - len.
Proof.
  intros X1 len. unfold fp_tail. destruct (ds_pending X1 - len =? 0); dsred; destruct (ds_strm X1); cbn; split; reflexivity.
Qed.

Local Ltac via Hfr := rewrite (Hfr _ eq_refl).
Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).

End Walk.
End RefDeflate3.

Module RefDeflate4.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).

Definition zh2_st (X : deflate_state) : deflate_state :=
  set_status (set_strm X (cset_adler (ds_strm X) adler32_init)) BUSY_STATE.

End Walk.
End RefDeflate4.

Module RefDeflate5.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).


Definition bks_cond (X : deflate_state) : bool :=
  negb (cs_avail_in (ds_strm X) =? 0) || negb (ds_lookahead X =? 0) || (negb (flush =? 0) && negb (ds_status X =? 666)).



Definition bs_st (X : deflate_state) (b : block_state) : deflate_state :=
  if block_state_eqb b finish_started || block_state_eqb b finish_done then set_status X FINISH_STATE else X.


Definition tt_st (X : deflate_state) : deflate_state := if 0 <? ds_wrap X then set_wrap X (- ds_wrap X) else X.
Definition tt_rc (X : deflate_state) : Z := if negb (ds_pending X =? 0) then Z_OK else Z_STREAM_END.

End Walk.
End RefDeflate5.

Module RefDeflate6.


From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).
Definition bdt_st (X : deflate_state) : deflate_state :=
  if flush =? 3 then set_head X (arr_set (ds_head X) (hs - 1) 0) else X.


Definition bdm_st (X : deflate_state) : deflate_state :=
  if ds_lookahead X =? 0 then set_insert (set_block_start (set_strstart X 0) 0) 0 else X.

End Walk.
End RefDeflate6.

Module RefDeflate7.


From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).
Definition abw_st (X : deflate_state) : deflate_state := if ds_wrap X <=? 0 then X else trailer_st X.

Definition tr2_stM (X : deflate_state) : deflate_state :=
  let p := ds_pending X in
  let ad := cs_adler (ds_strm X) in
  let t := cs_total_in (ds_strm X) in
  mput2 (mput2 (mput2 (mput2 (mput2 (mput2 (mput2 (mput2 X
    p ad (p + 1)) (p + 1) (ad / 2 ^ 8) (p + 2)) (p + 2) (ad / 2 ^ 16) (p + 3)) (p + 3) (ad / 2 ^ 24) (p + 4))
    (p + 4) t (p + 5)) (p + 5) (t / 2 ^ 8) (p + 6)) (p + 6) (t / 2 ^ 16) (p + 7)) (p + 7) (t / 2 ^ 24) (p + 8).

Lemma w8_land : forall a, wrap8 a = wrap8 (Z.land a 255).
Proof. intros a. rewrite !wrap8_mod'. symmetry. apply b8_land255. Qed.
Lemma w8_shr_land : forall a k, 0 <= k -> wrap8 (a / 2 ^ k) = wrap8 (Z.land (Z.shiftr a k) 255).
Proof. intros a k Hk. rewrite Z.shiftr_div_pow2 by exact Hk. apply w8_land. Qed.

Lemma tr2_stM_eq : forall X, ds_wrap X = 2 -> tr2_stM X = trailer_st X.
Proof.
  intros X W2. unfold tr2_stM, trailer_st. rewrite (proj2 (Z.eqb_eq _ _) W2). cbv zeta.
  set (pn := ds_pending X). set (ad := cs_adler (ds_strm X)). set (t := cs_total_in (ds_strm X)).
  change (mputl2 X [(pn, ad, pn + 1); (pn + 1, ad / 2 ^ 8, pn + 2); (pn + 2, ad / 2 ^ 16, pn + 3); (pn + 3, ad / 2 ^ 24, pn + 4);
                    (pn + 4, t, pn + 5); (pn + 5, t / 2 ^ 8, pn + 6); (pn + 6, t / 2 ^ 16, pn + 7); (pn + 7, t / 2 ^ 24, pn + 8)]
          = putl X [Z.land ad 255; Z.land (Z.shiftr ad 8) 255; Z.land (Z.shiftr ad 16) 255; Z.land (Z.shiftr ad 24) 255;
                    Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]).
  apply mputl2_putl. subst pn. cbn [MOK].
  repeat split; first [lia | apply w8_land | apply w8_shr_land; lia].
Qed.

Definition tr1_stM (X : deflate_state) : deflate_state :=
  let p := ds_pending X in
  let ad := cs_adler (ds_strm X) in
  mput2 (mput2 (mput2 (mput2 X
    p ((ad / 2 ^ 16) mod 2 ^ 32 / 2 ^ 8) (p + 1)) (p + 1) (ad / 2 ^ 16) (p + 2))
    (p + 2) (ad mod 2 ^ 32 / 2 ^ 8) (p + 3)) (p + 3) ad (p + 4).

Lemma tr1_stM_eq : forall X, ds_wrap X <> 2 -> 0 <= cs_adler (ds_strm X) -> tr1_stM X = trailer_st X.
Proof.
  intros X W2 Had. unfold tr1_stM, trailer_st, putShortMSB. rewrite (proj2 (Z.eqb_neq _ _) W2). cbv zeta.
  set (pn := ds_pending X). revert Had. generalize (cs_adler (ds_strm X)) as ad. intros ad Had.
  change (mputl2 X [(pn, (ad / 2 ^ 16) mod 2 ^ 32 / 2 ^ 8, pn + 1); (pn + 1, ad / 2 ^ 16, pn + 2); (pn + 2, ad mod 2 ^ 32 / 2 ^ 8, pn + 3); (pn + 3, ad, pn + 4)]
          = putl X [Z.shiftr (wrap32 (Z.shiftr ad 16)) 8; Z.land (wrap32 (Z.shiftr ad 16)) 255;
                    Z.shiftr (Z.land ad 65535) 8; Z.land (Z.land ad 65535) 255]).
  apply mputl2_putl. subst pn. cbn [MOK].
  repeat split; try lia.
  - rewrite !wrap8_mod', !Z.shiftr_div_pow2, wrap32_mod by lia. reflexivity.
  - rewrite !wrap8_mod', !Z.shiftr_div_pow2, wrap32_mod by lia. rewrite b8_land255, b8_mod32. reflexivity.
  - rewrite !wrap8_mod', !Z.shiftr_div_pow2 by lia. apply b8_hi32. exact Had.
  - rewrite !wrap8_mod'. apply b8_lo. exact Had.
Qed.

End Walk.
End RefDeflate7.

Module RefDeflateW1.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma pending_set_wrap : forall s v, ds_pending (set_wrap s v) = ds_pending s.
Proof. intros; reflexivity. Qed.
Lemma wrap_set_wrap : forall s v, ds_wrap (set_wrap s v) = v.
Proof. intros; reflexivity. Qed.
Lemma strm_set_last_flush : forall s v, ds_strm (set_last_flush s v) = ds_strm s.
Proof. intros; reflexivity. Qed.
Lemma strm_set_status : forall s v, ds_strm (set_status s v) = ds_strm s.
Proof. intros; reflexivity. Qed.

Definition RES_fin (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if negb (flush =? Z_FINISH) then (X, Z_OK)
  else if ds_wrap X <=? 0 then (X, Z_STREAM_END)
  else deflate_trailer X.

Definition RES_bde (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if cs_avail_out (ds_strm X) =? 0 then (set_last_flush X (-1), Z_OK) else RES_fin flush X.

Definition oka_st (X : deflate_state) : deflate_state :=
  if cs_avail_out (ds_strm X) =? 0 then set_last_flush X (-1) else X.

Definition bs_st2 (X1 : deflate_state) (b : block_state) : deflate_state :=
  if block_state_eqb b finish_started || block_state_eqb b finish_done then set_status X1 FINISH_STATE else X1.

Definition RES_bs (flush : Z) (X2 : deflate_state) (b : block_state) : deflate_state * Z :=
  match b with
  | need_more | finish_started => (oka_st X2, Z_OK)
  | block_done => RES_bde flush (flush_pending (bdone_st X2 flush))
  | finish_done => RES_fin flush X2
  end.

Definition RES_bks (flush : Z) (X : deflate_state) : deflate_state * Z :=
  match deflate_blocks X flush with
  | (s, Some rc) => (s, rc)
  | (s, None) => RES_fin flush s
  end.

Lemma bks_cond_eq : forall flush X,
  negb (cs_avail_in (ds_strm X) =? 0) || negb (ds_lookahead X =? 0) || (negb (flush =? Z_NO_FLUSH) && negb (ds_status X =? FINISH_STATE))
  = bks_cond flush X.
Proof. intros; reflexivity. Qed.

Lemma deflate_blocks_nc : forall flush X, bks_cond flush X = false -> deflate_blocks X flush = (X, None).
Proof. intros flush X Hc. unfold deflate_blocks. rewrite bks_cond_eq, Hc. reflexivity. Qed.

Lemma RES_bks_nc : forall flush X, bks_cond flush X = false -> RES_bks flush X = RES_fin flush X.
Proof. intros flush X Hc. unfold RES_bks. rewrite (deflate_blocks_nc flush X Hc). reflexivity. Qed.

Lemma deflate_blocks_c : forall flush X X1 b, bks_cond flush X = true -> run_compress_func X flush = (X1, b) ->
  deflate_blocks X flush
  = match b with
    | need_more | finish_started => (oka_st (bs_st2 X1 b), Some Z_OK)
    | block_done => let s := flush_pending (bdone_st (bs_st2 X1 b) flush) in
                    if cs_avail_out (ds_strm s) =? 0 then (set_last_flush s (-1), Some Z_OK) else (s, None)
    | finish_done => (bs_st2 X1 b, None)
    end.
Proof.
  intros flush X X1 b Hc E. unfold deflate_blocks. rewrite bks_cond_eq, Hc, E. unfold bs_st2, oka_st, bdone_st.
  destruct b; cbn [block_state_eqb orb andb negb]; reflexivity.
Qed.

Lemma RES_bks_c : forall flush X X1 b, bks_cond flush X = true -> run_compress_func X flush = (X1, b) ->
  RES_bks flush X = RES_bs flush (bs_st2 X1 b) b.
Proof.
  intros flush X X1 b Hc E. unfold RES_bks. rewrite (deflate_blocks_c flush X X1 b Hc E). unfold RES_bs, RES_bde.
  destruct b; try reflexivity. cbv zeta. destruct (cs_avail_out _ =? 0); reflexivity.
Qed.

Lemma RES_fin_nf : forall flush X, flush <> Z_FINISH -> RES_fin flush X = (X, Z_OK).
Proof. intros flush X H. unfold RES_fin. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma bks_cond_false : forall flush X, bks_cond flush X = false -> flush <> 0 -> ds_status X = 666.
Proof.
  intros flush X Hc Hf. unfold bks_cond in Hc.
  destruct (cs_avail_in (ds_strm X) =? 0); [|discriminate]. destruct (ds_lookahead X =? 0); [|discriminate].
  rewrite (proj2 (Z.eqb_neq _ _) Hf) in Hc. cbn in Hc. destruct (Z.eqb_spec (ds_status X) 666); [assumption | discriminate].
Qed.

Lemma gzhdr_st_eq : forall X, gzhdr_st X = gz_st X.
Proof.
  intros X. unfold gzhdr_st, gz_st, gz_xfl. gs.
  lazymatch goal with |- ?a = ?b => constr_eq a b; exact (@eq_refl deflate_state a) end.
Qed.

Lemma zhdr_st_eq : forall X, zhdr_st X = zh2_st (zh_st X).
Proof.
  intros X. unfold zhdr_st, zh2_st, zh_st, zh_hdr, zh_h2, zh_h1, zh_h0, zh_lf. cbv zeta.
  unfold putShortMSB. gs.
  destruct (ds_strstart X =? 0); cbn [negb];
    lazymatch goal with |- ?a = ?b => constr_eq a b; exact (@eq_refl deflate_state a) end.
Qed.

Lemma keeps_status : keeps ds_status true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma status_tr_flush_bits : forall s, ds_status (tr_flush_bits s) = ds_status s.
Proof. intros s. unfold tr_flush_bits. apply (k_bi_flush ds_status true true keeps_status eq_refl). Qed.

Lemma status_fp_tail : forall s len, ds_status (fp_tail s len) = ds_status s.
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); gs; reflexivity. Qed.

Lemma status_flush_pending : forall s, ds_status (flush_pending s) = ds_status s.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  destruct (fp_len (tr_flush_bits s) =? 0); rewrite ?status_fp_tail; apply status_tr_flush_bits.
Qed.

Lemma status_set_status : forall s v, ds_status (set_status s v) = v.
Proof. intros; reflexivity. Qed.
Lemma status_set_last_flush : forall s v, ds_status (set_last_flush s v) = ds_status s.
Proof. intros; reflexivity. Qed.
Lemma pending_set_last_flush : forall s v, ds_pending (set_last_flush s v) = ds_pending s.
Proof. intros; reflexivity. Qed.
Lemma strm_zh2 : forall X, ds_strm (zh2_st X) = cset_adler (ds_strm X) adler32_init.
Proof. intros; reflexivity. Qed.
Lemma status_zh2 : forall X, ds_status (zh2_st X) = BUSY_STATE.
Proof. intros; reflexivity. Qed.
Lemma status_zhdr : forall X, ds_status (zhdr_st X) = BUSY_STATE.
Proof. intros X. rewrite zhdr_st_eq. apply status_zh2. Qed.
Lemma ain_cset_adler : forall c v, cs_avail_in (cset_adler c v) = cs_avail_in c.
Proof. intros [] v; reflexivity. Qed.

Definition RES_gzh (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let s2 := flush_pending (gz_st X) in
  if negb (ds_pending s2 =? 0) then (set_last_flush s2 (-1), Z_OK) else RES_bks flush s2.
Definition RES_dsp (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if ds_status X =? GZIP_STATE then RES_gzh flush X else RES_bks flush X.
Definition RES_zh (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let s2 := flush_pending (zhdr_st X) in
  if negb (ds_pending s2 =? 0) then (set_last_flush s2 (-1), Z_OK) else RES_dsp flush s2.
Definition RES_42 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if ds_status X =? INIT_STATE then (if ds_wrap X =? 0 then RES_bks flush (set_status X BUSY_STATE) else RES_zh flush X)
  else RES_dsp flush X.

Definition RES_996 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if (ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0) then err_return X Z_BUF_ERROR else RES_42 flush X.
Definition RES_974 (flush : Z) (X : deflate_state) : deflate_state * Z :=
  let old := ds_last_flush X in
  let s1 := set_last_flush X flush in
  if negb (ds_pending s1 =? 0) then
    (let s2 := flush_pending s1 in
     if cs_avail_out (ds_strm s2) =? 0 then (set_last_flush s2 (-1), Z_OK) else RES_996 flush s2)
  else if (cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK old) && negb (flush =? Z_FINISH)
       then err_return s1 Z_BUF_ERROR
       else RES_996 flush s1.
Definition RES_entry (flush : Z) (X : deflate_state) : deflate_state * Z :=
  if Z_BLOCK <? flush then (X, Z_STREAM_ERROR)
  else if (ds_status X =? FINISH_STATE) && negb (flush =? Z_FINISH) then err_return X Z_STREAM_ERROR
  else if cs_avail_out (ds_strm X) =? 0 then err_return X Z_BUF_ERROR
  else RES_974 flush X.

Lemma core_996_eq : forall flush s,
  (if (ds_status s =? FINISH_STATE) && negb (cs_avail_in (ds_strm s) =? 0) then err_return s Z_BUF_ERROR
   else
    let s0 := if (ds_status s =? INIT_STATE) && (ds_wrap s =? 0) then set_status s BUSY_STATE else s in
    let '(s1, r) := if ds_status s0 =? INIT_STATE then deflate_zlib_header s0 else (s0, None) in
    match r with
    | Some rc => (s1, rc)
    | None =>
        let '(s2, r0) := if ds_status s1 =? GZIP_STATE then deflate_gzip_header s1 else (s1, None) in
        match r0 with
        | Some rc => (s2, rc)
        | None =>
            let '(s3, r1) := deflate_blocks s2 flush in
            match r1 with
            | Some rc => (s3, rc)
            | None => if negb (flush =? Z_FINISH) then (s3, Z_OK) else if ds_wrap s3 <=? 0 then (s3, Z_STREAM_END) else deflate_trailer s3
            end
        end
    end) = RES_996 flush s.
Proof.
  intros flush s. unfold RES_996. destruct (_ && negb _); [reflexivity|].
  assert (ED : forall s5,
    (let '(s2, r0) := (if ds_status s5 =? GZIP_STATE then deflate_gzip_header s5 else (s5, None)) in
     match r0 with
     | Some rc => (s2, rc)
     | None => let '(s3, r1) := deflate_blocks s2 flush in
               match r1 with Some rc => (s3, rc)
               | None => if negb (flush =? Z_FINISH) then (s3, Z_OK) else if ds_wrap s3 <=? 0 then (s3, Z_STREAM_END) else deflate_trailer s3 end
     end) = RES_dsp flush s5).
  { intros s5. unfold RES_dsp, RES_gzh, RES_bks, RES_fin. destruct (ds_status s5 =? GZIP_STATE).
    - rewrite deflate_gzip_header_eq, gzhdr_st_eq. cbv zeta. destruct (negb (ds_pending _ =? 0)); [reflexivity|].
      destruct (deflate_blocks _ flush) as [s3 [rc|]]; reflexivity.
    - destruct (deflate_blocks _ flush) as [s3 [rc|]]; reflexivity. }
  unfold RES_42. unfold INIT_STATE, BUSY_STATE in *.
  destruct (Z.eqb_spec (ds_status s) 42) as [S42|S42]; [destruct (Z.eqb_spec (ds_wrap s) 0) as [W0|W0]|]; cbn [andb]; cbv zeta.
  - replace (ds_status (set_status s 113) =? 42) with false by reflexivity.
    transitivity (RES_dsp flush (set_status s 113)); [exact (ED (set_status s 113))|].
    unfold RES_dsp. replace (ds_status (set_status s 113) =? GZIP_STATE) with false by reflexivity. reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) S42). unfold RES_zh. rewrite deflate_zlib_header_eq. cbv zeta.
    destruct (negb (ds_pending _ =? 0)); [reflexivity|]. apply ED.
  - rewrite (proj2 (Z.eqb_neq _ _) S42). apply ED.
Qed.

Lemma deflate_core_RES : forall flush X, deflateStateCheck X = false -> 0 <= flush ->
  deflate_core X flush = RES_entry flush X.
Proof.
  intros flush X Hchk Hf0. unfold deflate_core, RES_entry. rewrite Hchk.
  replace (flush <? 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  destruct (Z_BLOCK <? flush); [reflexivity|].
  destruct (_ && negb (flush =? Z_FINISH)); [reflexivity|].
  destruct (cs_avail_out (ds_strm X) =? 0); [reflexivity|].
  unfold RES_974. cbv zeta.
  destruct (negb (ds_pending (set_last_flush X flush) =? 0)).
  - destruct (cs_avail_out _ =? 0); [reflexivity|]. apply core_996_eq.
  - destruct (_ && _ && _); [reflexivity|]. apply core_996_eq.
Qed.


Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 96).
Local Notation FPOK := (RefDeflate3.FPOK ds).
Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
Variable WF : deflate_state -> Prop.
Variable s0 : deflate_state.

Definition RES_abw (X : deflate_state) : deflate_state * Z :=
  if ds_wrap X <=? 0 then (X, Z_STREAM_END) else deflate_trailer X.

Lemma clear_hash_eq : forall X1, ds_hash_size X1 = hs ->
  set_head (set_head X1 (arr_set (ds_head X1) (hs - 1) 0))
           (arr_fill (ds_head (set_head X1 (arr_set (ds_head X1) (hs - 1) 0))) 0 (hs - 1) 0)
  = clear_hash X1.
Proof. intros X1 E. unfold clear_hash, NIL. gs. rewrite E. reflexivity. Qed.

Lemma lookahead_clear_hash : forall s, ds_lookahead (clear_hash s) = ds_lookahead s.
Proof. intros; reflexivity. Qed.
Lemma keeps_lookahead : keeps ds_lookahead true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma lookahead_tsb : forall s buf len last, ds_lookahead (tr_stored_block s buf len last) = ds_lookahead s.
Proof. intros. apply (k_tr_stored_block ds_lookahead true true keeps_lookahead eq_refl). Qed.
Lemma hash_size_tsb : forall s buf len last, ds_hash_size (tr_stored_block s buf len last) = ds_hash_size s.
Proof. intros. apply (k_tr_stored_block ds_hash_size true true keeps_hash_size eq_refl). Qed.


Definition BS_OK (X2 : deflate_state) (b : block_state) : Prop :=
  DOK X2
  /\ (b = block_done -> bdone_ok X2 flush
        /\ (cs_avail_out (ds_strm (flush_pending (bdone_st X2 flush))) <> 0 -> finish_ok WF s0 (flush_pending (bdone_st X2 flush)) flush))
  /\ (b = finish_done -> finish_ok WF s0 X2 flush).


Definition GZ_OK (s5 : deflate_state) : Prop :=
  (ds_status s5 = GZIP_STATE -> hdr_ok WF s0 s5 (gzhdr_st s5) 10)
  /\ let s6 := if Z.eqb (ds_status s5) GZIP_STATE then flush_pending (gzhdr_st s5) else s5 in
     ((ds_status s5 = GZIP_STATE -> ds_pending s6 = 0) ->
      blocks_ok SAFEs SAFEf SAFEw FB WF s0 s6 flush
      /\ (snd (deflate_blocks s6 flush) = None -> finish_ok WF s0 (fst (deflate_blocks s6 flush)) flush)).

Definition ZH_OK (s4 : deflate_state) : Prop :=
  DOK s4
  /\ (ds_status s4 = INIT_STATE -> hdr_ok WF s0 s4 (zhdr_st s4) 6)
  /\ let s5 := if Z.eqb (ds_status s4) INIT_STATE then flush_pending (zhdr_st s4) else s4 in
     ((ds_status s4 = INIT_STATE -> ds_pending s5 = 0) -> GZ_OK s5).


Lemma body_ok_split : forall X,
  body_ok SAFEs SAFEf SAFEw FB WF s0 X flush ->
  DOK X /\ (~ (ds_status X = FINISH_STATE /\ cs_avail_in (ds_strm X) <> 0) -> ZH_OK (st42_st X)).
Proof. intros X (H1 & _ & H3). split; [exact H1 | exact H3]. Qed.

Definition PEND_OK (X : deflate_state) : Prop :=
  let s1 := set_last_flush X flush in
  DOK s1
  /\ (ds_pending s1 <> 0 ->
      fp_ok s1
      /\ let s2 := flush_pending s1 in
         DOK s2
         /\ (cs_avail_out (ds_strm s2) = 0 -> dpost_ok WF s0 (set_last_flush s2 (-1)) Z_OK)
         /\ (cs_avail_out (ds_strm s2) <> 0 -> body_ok SAFEs SAFEf SAFEw FB WF s0 s2 flush))
  /\ (ds_pending s1 = 0 ->
      (rank_err s0 flush -> dpost_ok WF s0 (fst (err_return s1 Z_BUF_ERROR)) Z_BUF_ERROR)
      /\ (~ rank_err s0 flush -> body_ok SAFEs SAFEf SAFEw FB WF s0 s1 flush)).

Lemma st4_lt : forall st, st4 st -> 0 <= st < 2 ^ 31.
Proof. intros st Hs. unfold st4 in Hs. lia. Qed.

End Walk.


Lemma st4_of : forall st, DeflateSafe.st4 st -> RefDeflate1.st4 st.
Proof. intros st H. exact H. Qed.
End RefDeflateW1.

Module RefDeflate8.


From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflFast5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).
Local Ltac open_hregs6 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in let P22 := fresh "P22" in
  pose proof HRG as ((P8 & P2 & P9 & P18) & P22).


Lemma ne_szwrap_mod : forall a s, 0 <= s < 2 ^ 32 -> 0 <= a < 2 ^ 31 -> a <> s -> a <> szwrap 32 s mod 2 ^ 64.
Proof.
  intros a s Hs Ha Hne. destruct (szwrap32_cases s Hs) as [[H1 E]|[H1 E]]; rewrite E.
  - rewrite Z.mod_small by lia. exact Hne.
  - Z.to_euclidean_division_equations; lia.
Qed.

Definition htl (X : deflate_state) : deflate_state :=
  let sn := ds_sym_next X in
  let lb := ds_lit_bufsize X in
  let c := arr_get (ds_window X) (ds_strstart X) in
  let X0 := set_match_length X 0 in
  let X1 := set_sym_next X0 (sn + 1) in
  let X2 := set_pending_buf X1 (arr_set (ds_pending_buf X) (lb + sn) (wrap8 0)) in
  let X3 := set_sym_next X2 (sn + 2) in
  let X4 := set_pending_buf X3 (arr_set (ds_pending_buf X2) (lb + sn + 1) (wrap8 0)) in
  let X5 := set_sym_next X4 (sn + 3) in
  let X6 := set_pending_buf X5 (arr_set (ds_pending_buf X4) (lb + sn + 2) (wrap8 (wrap8 c))) in
  let X7 := set_dyn_ltree_fc X6 (arr_set (ds_dyn_ltree_fc X) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc X) (wrap8 c) + 1))) in
  set_strstart (set_lookahead X7 (ds_lookahead X - 1)) (ds_strstart X + 1).


Definition hfb_bufp (X : deflate_state) : Z :=
  if ds_block_start X <? 0 then 0 else W + wrap32 (ds_block_start X).
Definition hfb_len (X : deflate_state) : Z := wrap64 (ds_strstart X - ds_block_start X).
Definition h28_st (X : deflate_state) : deflate_state := if flush =? 0 then X else set_insert X 0.


Local Ltac aout_prep X Hao :=
  let SZ := fresh "SZ" in pose proof (szwrap32_cases (cs_avail_out (ds_strm X)) Hao) as SZ.

End Walk.
End RefDeflate8.

Module RefDeflate8F.


From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).

Local Ltac nf := cbn [dfF].

Local Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.

Ltac st_leaf extra := first [ reflexivity | lia | progress extra; st_leaf extra | rewrite (szwrap_small 32) by lia; st_leaf extra | progress f_equal; st_leaf extra ].
Ltac st_peel extra :=
  lazymatch goal with
  | |- @eq deflate_state ?a ?a => reflexivity
  | |- @eq deflate_state (?f _ _) (?f _ _) => apply (f_equal2 f); [st_peel extra | st_leaf extra]
  end.
Ltac st_close extra := cbn [set_tree_fc tree_fc]; dsred; st_peel extra.




Local Ltac open_hregs0 HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in
  pose proof HRG as (P8 & P2 & P9).

Local Notation FPOK := (RefDeflate3.FPOK ds).


End Walk.
End RefDeflate8F.

Module RefDeflate8W.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate3.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate8.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate8F.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflateW1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma hf_tally_eq : forall X, hf_tally X = (htl X, Z.eqb (ds_sym_next X + 3) (ds_sym_end X)).
Proof.
  intros X. unfold hf_tally, tr_tally_lit. cbv zeta. unfold set_Freq, Freq, sym_buf_set. cbn [tree_fc set_tree_fc].
  unfold htl. cbv zeta. dsred.
  match goal with |- (?a, ?b) = (?c, ?d) => assert (E1 : a = c); [symmetry; mpeel | rewrite E1; f_equal; f_equal; lia] end.
Qed.

Lemma huff_loop_step : forall n X flush,
  deflate_huff_loop (S n) X flush
  = match snd (hf_body X flush) with
    | LCont => deflate_huff_loop n (fst (hf_body X flush)) flush
    | LBreak => (fst (hf_body X flush), None)
    | LRet bs => (fst (hf_body X flush), Some bs)
    end.
Proof. intros n X flush. cbn [deflate_huff_loop]. rewrite hf_body_eq. destruct (hf_body X flush); reflexivity. Qed.

Lemma flush_block_only_eq : forall s last,
  flush_block_only s last
  = flush_pending (set_block_start (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None)
                                                    (wrap64 (ds_strstart s - ds_block_start s)) last)
                                    (ds_strstart (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None)
                                                    (wrap64 (ds_strstart s - ds_block_start s)) last))).
Proof. intros; reflexivity. Qed.

Lemma flush_block_snd' : forall s last,
  flush_block s last = (flush_block_only s last,
                        if cs_avail_out (ds_strm (flush_block_only s last)) =? 0
                        then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof. intros s last. unfold flush_block. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma strstart_tfb : forall s buf len last, ds_strstart (tr_flush_block s buf len last) = ds_strstart s.
Proof. intros. pose proof (tfb_lz_view s buf len last) as E. unfold lz_view in E. congruence. Qed.
Lemma lookahead_tfb : forall s buf len last, ds_lookahead (tr_flush_block s buf len last) = ds_lookahead s.
Proof. intros. pose proof (tfb_lz_view s buf len last) as E. unfold lz_view in E. congruence. Qed.

Lemma lz_view_flush_pending : forall s,
  (ds_strstart (flush_pending s), ds_lookahead (flush_pending s)) = (ds_strstart s, ds_lookahead s).
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  pose proof (bits_lz_view s) as E1. unfold lz_view in E1.
  destruct (fp_len (tr_flush_bits s) =? 0).
  - congruence.
  - pose proof (fp_tail_view (tr_flush_bits s) (fp_len (tr_flush_bits s))) as E2. congruence.
Qed.
Lemma lookahead_fbo : forall s last, ds_lookahead (flush_block_only s last) = ds_lookahead s.
Proof.
  intros s last. rewrite flush_block_only_eq.
  pose proof (lz_view_flush_pending (set_block_start (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last)
                 (ds_strstart (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last)))) as E.
  pose proof (lookahead_tfb s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last) as E2.
  assert (E3 : forall t v, ds_lookahead (set_block_start t v) = ds_lookahead t) by (intros; reflexivity).
  rewrite E3, E2 in E. congruence.
Qed.
Lemma strstart_fbo : forall s last, ds_strstart (flush_block_only s last) = ds_strstart s.
Proof.
  intros s last. rewrite flush_block_only_eq.
  pose proof (lz_view_flush_pending (set_block_start (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last)
                 (ds_strstart (tr_flush_block s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last)))) as E.
  pose proof (strstart_tfb s (if 0 <=? ds_block_start s then Some (wrap32 (ds_block_start s)) else None) (wrap64 (ds_strstart s - ds_block_start s)) last) as E2.
  assert (E3 : forall t v, ds_strstart (set_block_start t v) = ds_strstart t) by (intros; reflexivity).
  rewrite E3, E2 in E. congruence.
Qed.

Lemma hf_fill_eq : forall s flush,
  hf_fill s flush = if ds_lookahead s =? 0
                    then (if ds_lookahead (fill_window s) =? 0
                          then (if flush =? Z_NO_FLUSH then (fill_window s, Some (LRet need_more)) else (fill_window s, Some LBreak))
                          else (fill_window s, None))
                    else (s, None).
Proof. intros; reflexivity. Qed.


Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation SP := (sp - 96).
Local Notation FPOK := (RefDeflate3.FPOK ds).


Lemma sym_next_set_insert : forall s v, ds_sym_next (set_insert s v) = ds_sym_next s. Proof. intros; reflexivity. Qed.
Lemma strstart_set_insert : forall s v, ds_strstart (set_insert s v) = ds_strstart s. Proof. intros; reflexivity. Qed.
Lemma block_start_set_insert : forall s v, ds_block_start (set_insert s v) = ds_block_start s. Proof. intros; reflexivity. Qed.
Lemma hfb_bufp_set_insert : forall X v, hfb_bufp p (set_insert X v) = hfb_bufp p X. Proof. intros; reflexivity. Qed.
Lemma hfb_len_set_insert : forall X v, hfb_len (set_insert X v) = hfb_len X. Proof. intros; reflexivity. Qed.

Lemma deflate_tail_eq : forall s fl,
  deflate_tail s fl
  = if fl =? Z_FINISH then
      (flush_block_only s 1, if cs_avail_out (ds_strm (flush_block_only s 1)) =? 0 then finish_started else finish_done)
    else if negb (ds_sym_next s =? 0) then
      (flush_block_only s 0, if cs_avail_out (ds_strm (flush_block_only s 0)) =? 0 then need_more else block_done)
    else (s, block_done).
Proof.
  intros s fl. unfold deflate_tail. rewrite !flush_block_snd'.
  destruct (fl =? Z_FINISH); [destruct (_ =? 0); reflexivity|].
  destruct (negb (ds_sym_next s =? 0)); [destruct (_ =? 0); reflexivity | reflexivity].
Qed.

End Walk.
End RefDeflate8W.

Module RefDeflateP.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateSafe.RefDeflateM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflateW1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma snd_err_return : forall s rc, snd (err_return s rc) = rc.
Proof. intros; reflexivity. Qed.

Lemma avail_in_set_last_flush : forall s v, cs_avail_in (ds_strm (set_last_flush s v)) = cs_avail_in (ds_strm s).
Proof. intros; reflexivity. Qed.

Lemma last_flush_set_strm : forall s st, ds_last_flush (set_strm s st) = ds_last_flush s.
Proof. intros; reflexivity. Qed.

Lemma wrap_set_status : forall s v, ds_wrap (set_status s v) = ds_wrap s.
Proof. intros; reflexivity. Qed.

Section Post.
  Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable WF : deflate_state -> Prop.
  Variable s0 : deflate_state.
Variable flush : Z.

  Definition DP (r : deflate_state * Z) : Prop := dpost_ok WF s0 (fst r) (snd r).

  Lemma DP_pair : forall s rc, dpost_ok WF s0 s rc -> DP (s, rc).
  Proof. intros s rc H. exact H. Qed.

  Lemma P_fin : forall X, finish_ok WF s0 X flush -> DP (RES_fin flush X).
  Proof.
    intros X (HOK & Hnf & Hend & Htr). unfold RES_fin.
    destruct (Z.eqb_spec flush Z_FINISH) as [F4|F4]; cbn [negb].
    - destruct (Z.leb_spec (ds_wrap X) 0) as [W0|W0].
      + apply DP_pair. exact (Hend F4 W0).
      + destruct (Htr F4 ltac:(lia)) as (_ & _ & _ & _ & _ & T). cbv zeta in T. destruct T as (_ & _ & Wp & Tp).
        rewrite deflate_trailer_eq. cbv zeta.
        generalize dependent Tp. generalize dependent Wp.
        generalize (flush_pending (trailer_st X)) as s2. intros s2 Wp Tp.
        replace (0 <? ds_wrap s2) with true by (symmetry; apply Z.ltb_lt; exact Wp).
        apply DP_pair. rewrite pending_set_wrap. exact Tp.
    - apply DP_pair. exact (Hnf F4).
  Qed.

  Lemma P_bks : forall Y,
    blocks_ok SAFEs SAFEf SAFEw FB WF s0 Y flush ->
    (snd (deflate_blocks Y flush) = None -> finish_ok WF s0 (fst (deflate_blocks Y flush)) flush) ->
    DP (RES_bks flush Y).
  Proof.
    intros Y (HOK & HB) HF.
    destruct (Sumbool.sumbool_of_bool (bks_cond flush Y)) as [C|C].
    - destruct (run_compress_func Y flush) as [X1 b] eqn:E.
      rewrite (RES_bks_c flush Y X1 b C E).
      rewrite (deflate_blocks_c flush Y X1 b C E) in HF.
      rewrite bks_cond_eq, C in HB. destruct (HB eq_refl) as (_ & HB2). clear HB.
      change (if block_state_eqb b finish_started || block_state_eqb b finish_done then set_status X1 FINISH_STATE else X1)
        with (bs_st2 X1 b) in HB2.
      generalize dependent HB2. generalize dependent HF. generalize (bs_st2 X1 b) as X2. intros X2 HF (HOK2 & Hnm & Hbd).
      destruct b.
      + apply DP_pair. exact (Hnm eq_refl).
      + destruct (Hbd eq_refl) as (_ & Hz). cbn [RES_bs]. unfold RES_bde.
        cbv zeta in HF.
        generalize dependent Hz. generalize dependent HF. generalize (flush_pending (bdone_st X2 flush)) as s. intros s HF Hz.
        destruct (cs_avail_out (ds_strm s) =? 0).
        * apply DP_pair. exact (Hz eq_refl).
        * apply P_fin. exact (HF eq_refl).
      + apply DP_pair. exact (Hnm eq_refl).
      + cbn [RES_bs]. apply P_fin. exact (HF eq_refl).
    - rewrite (RES_bks_nc flush Y C). apply P_fin.
      rewrite (deflate_blocks_nc flush Y C) in HF. exact (HF eq_refl).
  Qed.

  Lemma P_996 : forall X, body_ok SAFEs SAFEf SAFEw FB WF s0 X flush -> DP (RES_996 flush X).
  Proof.
    intros X (HOK & Herr & Hgo). unfold RES_996.
    destruct (Sumbool.sumbool_of_bool ((ds_status X =? FINISH_STATE) && negb (cs_avail_in (ds_strm X) =? 0))) as [C|C]; rewrite C.
    - apply DP_pair. apply Herr. apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1.
      split; [exact C1|]. intros E. rewrite E in C2. discriminate C2.
    - assert (NC : ~ (ds_status X = FINISH_STATE /\ cs_avail_in (ds_strm X) <> 0)).
      { intros [E1 E2]. rewrite (proj2 (Z.eqb_eq _ _) E1) in C. cbn [andb] in C.
        destruct (Z.eqb_spec (cs_avail_in (ds_strm X)) 0); [exact (E2 ltac:(assumption)) | discriminate C]. }
      specialize (Hgo NC). clear Herr NC C. cbv zeta in Hgo. destruct Hgo as (HOK4 & Hzh & Hrest).
      unfold RES_42.
      assert (DSP : forall Y,
        (ds_status Y = GZIP_STATE -> hdr_ok WF s0 Y (gzhdr_st Y) 10) /\
        (let s6 := if ds_status Y =? GZIP_STATE then flush_pending (gzhdr_st Y) else Y in
         (ds_status Y = GZIP_STATE -> ds_pending s6 = 0) ->
         blocks_ok SAFEs SAFEf SAFEw FB WF s0 s6 flush /\
         (snd (deflate_blocks s6 flush) = None -> finish_ok WF s0 (fst (deflate_blocks s6 flush)) flush)) ->
        DP (RES_dsp flush Y)).
      { intros Y (Hgz & Hrest2). unfold RES_dsp.
        destruct (Z.eqb_spec (ds_status Y) GZIP_STATE) as [S57|S57]; cbn [andb negb] in Hrest2 |- *.
        - pose proof (Hgz S57) as (_ & _ & _ & _ & Hh2). cbv zeta in Hh2. destruct Hh2 as (_ & _ & Hpend2).
          unfold RES_gzh. rewrite <- gzhdr_st_eq.
          generalize dependent Hrest2. generalize dependent Hpend2.
          generalize (flush_pending (gzhdr_st Y)) as s6. intros s6 Hpend2 Hrest2.
          destruct (Z.eqb_spec (ds_pending s6) 0) as [Q0|Q0]; cbn [negb].
          + destruct (Hrest2 (fun _ => Q0)) as (HB & HF). exact (P_bks _ HB HF).
          + apply DP_pair. exact (Hpend2 Q0).
        - destruct (Hrest2 ltac:(intros E; exfalso; exact (S57 E))) as (HB & HF). exact (P_bks _ HB HF). }
      destruct (Z.eqb_spec (ds_status X) INIT_STATE) as [S42|S42].
      + destruct (Z.eqb_spec (ds_wrap X) 0) as [W0|W0]; cbn [andb] in HOK4, Hzh, Hrest |- *.
        *
          assert (S4 : ds_status (set_status X BUSY_STATE) =? INIT_STATE = false) by reflexivity.
          rewrite S4 in Hrest. cbn [andb] in Hrest.
          specialize (Hrest ltac:(intros E; discriminate E)).
          change (DP (RES_dsp flush (set_status X BUSY_STATE))). exact (DSP _ Hrest).
        *
          rewrite (proj2 (Z.eqb_eq _ _) S42) in Hrest. cbn [andb] in Hrest.
          pose proof (Hzh S42) as (_ & _ & _ & _ & Hh). cbv zeta in Hh. destruct Hh as (_ & _ & Hpend).
          unfold RES_zh.
          generalize dependent Hrest. generalize dependent Hpend.
          generalize (flush_pending (zhdr_st X)) as s5. intros s5 Hpend Hrest.
          destruct (Z.eqb_spec (ds_pending s5) 0) as [P0|P0]; cbn [negb].
          -- exact (DSP _ (Hrest (fun _ => P0))).
          -- apply DP_pair. exact (Hpend P0).
      +
        cbn [andb] in HOK4, Hzh, Hrest |- *.
        rewrite (proj2 (Z.eqb_neq _ _) S42) in Hrest. cbn [andb] in Hrest.
        exact (DSP _ (Hrest ltac:(intros E; exfalso; exact (S42 E)))).
  Qed.

  Lemma P_974 : PEND_OK flush SAFEs SAFEf SAFEw FB WF s0 s0 -> DP (RES_974 flush s0).
  Proof.
    intros (HOK1 & Hp & Hnp). unfold RES_974. cbv zeta.
    destruct (Z.eqb_spec (ds_pending (set_last_flush s0 flush)) 0) as [P0|P0]; cbn [negb].
    - destruct (Hnp P0) as (Hre & Hgo). rewrite avail_in_set_last_flush.
      destruct (Sumbool.sumbool_of_bool ((cs_avail_in (ds_strm s0) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH))) as [C|C]; rewrite C.
      + apply DP_pair. apply Hre.
        apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
        split; [apply Z.eqb_eq; exact C1|]. split; [apply Z.leb_le; exact C2|].
        intros E. rewrite E in C3. discriminate C3.
      + apply P_996. apply Hgo. intros (R1 & R2 & R3).
        rewrite (proj2 (Z.eqb_eq _ _) R1), (proj2 (Z.leb_le _ _) R2), (proj2 (Z.eqb_neq _ _) R3) in C. discriminate C.
    - destruct (Hp P0) as (_ & Hgo). cbv zeta in Hgo. destruct Hgo as (_ & Hz & Hnz).
      generalize dependent Hnz. generalize dependent Hz. generalize (flush_pending (set_last_flush s0 flush)) as s2. intros s2 Hz Hnz.
      destruct (Z.eqb_spec (cs_avail_out (ds_strm s2)) 0) as [A0|A0].
      + apply DP_pair. exact (Hz A0).
      + apply P_996. exact (Hnz A0).
  Qed.
End Post.

Theorem deflate_safe_post :
  forall SAFEs SAFEf SAFEw FB WF ds zc flush,
    0 <= flush ->
    deflate_safe SAFEs SAFEf SAFEw FB WF ds zc flush ->
    let s0 := set_strm ds (cstrm_of_call zc) in
    dpost_ok WF s0 (fst (deflate_core s0 flush)) (snd (deflate_core s0 flush)).
Proof.
  intros SAFEs SAFEf SAFEw FB WF ds zc flush Hf0 HS. cbv zeta.
  generalize dependent HS. unfold deflate_safe. generalize (set_strm ds (cstrm_of_call zc)) as s0.
  intros s0 (HOK & Hchk & Hlf & E1 & E2 & E3 & HP).
  change (DP WF s0 (deflate_core s0 flush)).
  rewrite (deflate_core_RES flush s0 Hchk Hf0). unfold RES_entry.
  destruct (Z.ltb_spec Z_BLOCK flush) as [F5|F5].
  - apply DP_pair. exact E1.
  - destruct (Sumbool.sumbool_of_bool ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH))) as [C|C]; rewrite C.
    + apply DP_pair. exact E2.
    + destruct (Z.eqb_spec (cs_avail_out (ds_strm s0)) 0) as [A0|A0].
      * apply DP_pair. exact E3.
      * apply (P_974 SAFEs SAFEf SAFEw FB). apply HP; [unfold Z_BLOCK in F5; lia | | exact A0].
        intros [S1 S2]. rewrite (proj2 (Z.eqb_eq _ _) S1), (proj2 (Z.eqb_neq _ _) S2) in C. discriminate C.
Qed.
End RefDeflateP.

Module RefDeflate_run.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZSeqExecP.BvAux.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefZApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateKZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateDict_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflFast7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflSlow7.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflStored9.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateG.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflateW1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate8W.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflateP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma deflate_m_eq : forall ds zc flush Xf rc,
  deflate_core (set_strm ds (cstrm_of_call zc)) flush = (Xf, rc) ->
  deflate_m ds zc flush = (Xf, zret_of_cs (ds_strm Xf) rc).
Proof. intros ds zc flush Xf rc E. unfold deflate_m. cbv zeta. rewrite E. reflexivity. Qed.

Lemma zlength_cs_output : forall st, zlength (cs_output st) = Z.of_nat (length (cs_out_rev st)).
Proof. intros st. unfold zlength, cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.

Lemma znth_nth0 : forall (l : list Z) i, 0 <= i -> ZIface.znth 0 l i = nth (Z.to_nat i) l 0.
Proof. intros l i Hi. unfold ZIface.znth. replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma length_nil_Z : Z.of_nat (@length Z []) = 0.
Proof. reflexivity. Qed.

Definition SAFE_SPEC : Prop :=
  forall ds zc flush, dreach ds -> dwf ds -> dcall_wf zc -> 0 <= flush < 16 ->
    deflate_safe stored_safe fast_safe slow_safe fb_safe dwf ds zc flush.

Section Proofs.
  Hypothesis HSAFE : SAFE_SPEC.

  Section Call.
  Variable sp : Z.
Variable strm : Z.
Variable pin : Z.
Variable pout : Z.
Variable S : Z.
Variable ds : deflate_state.
Variable zc : ZCall.
Variable flush : Z.
Variable ra : Z.
  Hypothesis Hzok : zstrm_ok (zc_strm zc).
  Hypothesis Haout : 0 <= zc_avail_out zc < 2 ^ 32.
  Hypothesis Hilen : zlength (zc_input zc) < 2 ^ 32.
  Hypothesis Hinok : bytes_ok (zc_input zc).
  Hypothesis Hio : pin + zlength (zc_input zc) <= pout \/ pout + zc_avail_out zc <= pin.
  Hypothesis Hsi : strm + ZS_SIZE <= pin \/ pin + zlength (zc_input zc) <= strm.
  Hypothesis Hso : strm + ZS_SIZE <= pout \/ pout + zc_avail_out zc <= strm.
  Hypothesis Hfl : 0 <= flush < 16.
  Local Notation ws := (ds_w_size ds).
  Local Notation hs := (ds_hash_size ds).
  Local Notation lbs := (ds_lit_bufsize ds).
  Local Notation ILEN := (zlength (zc_input zc)).
  Local Notation AOUT := (zc_avail_out zc).
  Definition dsw : deflate_state := set_strm ds (cstrm_of_call zc).

  Section WithMsg.
  Variable vmsg : Z.
Variable vres : Z.

  Definition zp : zs_ptrs := ZSP pin pout pc_zalloc pc_zfree 0 vres (fun _ => vmsg).

  End WithMsg.
  End Call.
End Proofs.


Section Api.
  Hypothesis HSAFE : SAFE_SPEC.
End Api.
End RefDeflate_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeI6.RefDeflate_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma FB_CALL_ok : FB_CALL.
Proof. exact (FB_CALL_intro overlay_core_proof). Qed.

Theorem dreach_DD : forall s, dreach s -> DD s.
Proof.
  intros s Hr.
  induction Hr as [zc level method wb memlevel strategy chs s zr HML5 H | s zc flush s' zr Hr IH Hzc Hfl E | s zc dict s' zr Hr IH Hz Hb Hl E].
  - exact (dinit_DD zc level method wb memlevel strategy HML5 chs s zr H).
  - pose proof (deflate_m_DD _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok)
                  s zc flush IH Hzc Hfl) as D.
    rewrite E in D. exact D.
  - pose proof (setdict_DD s zc dict IH Hz Hb Hl) as D. rewrite E in D. exact D.
Qed.

Theorem deflate_safe_proof : SAFE_SPEC.
Proof.
  intros ds zc flush Hr Hw Hzc Hfl.
  apply (deflate_safe_DD _ _ _ _ stored_bf_spec (huff_bf_spec FB_CALL_ok) (rle_bf_spec FB_CALL_ok) (fast_bf_spec FB_CALL_ok) (slow_bf_spec FB_CALL_ok));
    [| exact Hzc | exact Hfl].
  exact (dreach_DD ds Hr).
Qed.
