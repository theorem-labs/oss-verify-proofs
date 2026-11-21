(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateDictM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLW.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeLW0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
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
