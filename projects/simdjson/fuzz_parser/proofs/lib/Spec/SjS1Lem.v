(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma scan_from_stop : forall f d len i acc err uncl, len <= i -> scan_from f d len i acc err uncl = (acc, err, uncl).
Proof. intros [|f] d len i acc err uncl H; cbn [scan_from]; [reflexivity|]. replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma scan_from_space : forall f d len i acc err uncl, i < len -> is_space (byte_at d i) = true ->
  scan_from (S f) d len i acc err uncl = scan_from f d len (i + 1) acc err uncl.
Proof. intros f d len i acc err uncl H Hs. cbn [scan_from]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hs. reflexivity. Qed.

Lemma scan_from_string : forall f d len i acc err uncl, i < len -> is_space (byte_at d i) = false -> byte_at d i = 34 ->
  scan_from (S f) d len i acc err uncl =
  match vstring (S (Z.to_nat len)) d len (i + 1) err with
  | (Some j, e) => scan_from f d len (j + 1) (i :: acc) e uncl
  | (None, e) => (i :: acc, e, true)
  end.
Proof.
  intros f d len i acc err uncl H Hs Hq. cbn [scan_from]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hs, Hq. reflexivity.
Qed.

Lemma scan_from_op : forall f d len i acc err uncl, i < len -> is_space (byte_at d i) = false -> byte_at d i <> 34 -> is_op (byte_at d i) = true ->
  scan_from (S f) d len i acc err uncl = scan_from f d len (i + 1) (i :: acc) err uncl.
Proof.
  intros f d len i acc err uncl H Hs Hq Ho. cbn [scan_from]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hs. replace (byte_at d i =? 34) with false by (symmetry; apply Z.eqb_neq; exact Hq). rewrite Ho. reflexivity.
Qed.

Lemma scan_from_prim : forall f d len i acc err uncl, i < len -> is_space (byte_at d i) = false -> byte_at d i <> 34 -> is_op (byte_at d i) = false ->
  scan_from (S f) d len i acc err uncl = scan_from f d len (prim_end (Z.to_nat len) d len i + 1) (i :: acc) err uncl.
Proof.
  intros f d len i acc err uncl H Hs Hq Ho. cbn [scan_from]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hs. replace (byte_at d i =? 34) with false by (symmetry; apply Z.eqb_neq; exact Hq). rewrite Ho. reflexivity.
Qed.

(* [comment removed for export] *)
Definition primc (c : Z) : bool := negb (is_space c || is_op c) && negb (c =? 30).

Lemma prim_end_step : forall g d len i, i + 1 < len -> primc (byte_at d (i + 1)) = true ->
  prim_end (S g) d len i = prim_end g d len (i + 1).
Proof.
  intros g d len i H Hp. cbn [prim_end]. unfold primc in Hp.
  replace (i + 1 <? len) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite Hp. reflexivity.
Qed.

Lemma prim_end_here : forall g d len i, (len <= i + 1 \/ primc (byte_at d (i + 1)) = false) -> prim_end g d len i = i.
Proof.
  intros [|g] d len i H; cbn [prim_end]; [reflexivity|]. unfold primc in H.
  destruct H as [H|H].
  - replace (i + 1 <? len) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - destruct (i + 1 <? len); cbn [andb]; [rewrite H|]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vstring_stop : forall g d len i e, len <= i -> vstring g d len i e = (None, e).
Proof. intros [|g] d len i e H; cbn [vstring]; [reflexivity|]. replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

Lemma vstring_plain : forall g d len i e, i < len -> is_ascii_stop (byte_at d i) = false ->
  vstring (S g) d len i e = vstring g d len (i + 1) e.
Proof. intros g d len i e H Hs. cbn [vstring]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia). rewrite Hs. reflexivity. Qed.

Lemma vstring_quote : forall g d len i e, i < len -> byte_at d i = 34 -> vstring (S g) d len i e = (Some i, e).
Proof.
  intros g d len i e H Hq. cbn [vstring]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hq. reflexivity.
Qed.

Lemma vstring_bslash : forall g d len i e, i < len -> byte_at d i = 92 -> vstring (S g) d len i e = vstring g d len (i + 2) e.
Proof.
  intros g d len i e H Hq. cbn [vstring]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite Hq. reflexivity.
Qed.

Lemma vstring_ctrl : forall g d len i e, i < len -> 0 <= byte_at d i < 32 -> vstring (S g) d len i e = vstring g d len (i + 1) true.
Proof.
  intros g d len i e H Hc. cbn [vstring]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  unfold is_ascii_stop. replace (byte_at d i <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb negb].
  replace (byte_at d i =? 34) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at d i =? 92) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (128 <=? byte_at d i) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma vstring_utf8 : forall g d len i e, i < len -> 128 <= byte_at d i ->
  vstring (S g) d len i e = let '(i', e') := utf8_char d len i in vstring g d len i' (e || e').
Proof.
  intros g d len i e H Hc. cbn [vstring]. replace (len <=? i) with false by (symmetry; apply Z.leb_gt; lia).
  unfold is_ascii_stop. replace (128 <=? byte_at d i) with true by (symmetry; apply Z.leb_le; lia). rewrite !orb_true_r. cbn [negb].
  replace (byte_at d i =? 34) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (byte_at d i =? 92) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma prim_end_fuel : forall g1 g2 d len i, Z.of_nat g1 >= len - i - 1 -> Z.of_nat g2 >= len - i - 1 ->
  prim_end g1 d len i = prim_end g2 d len i.
Proof.
  induction g1 as [|g1 IH]; intros [|g2] d len i H1 H2; cbn [prim_end]; try reflexivity.
  - destruct ((i + 1 <? len) && _ && _) eqn:E; [|reflexivity]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
    apply Z.ltb_lt in E. lia.
  - destruct ((i + 1 <? len) && _ && _) eqn:E; [|reflexivity]. apply andb_prop in E as [E _]. apply andb_prop in E as [E _].
    apply Z.ltb_lt in E. lia.
  - destruct ((i + 1 <? len) && _ && _); [apply IH; lia| reflexivity].
Qed.

Lemma vstring_fuel : forall g1 g2 d len i e, Z.of_nat g1 > len - i -> Z.of_nat g2 > len - i ->
  vstring g1 d len i e = vstring g2 d len i e.
Proof.
  induction g1 as [|g1 IH]; intros g2 d len i e H1 H2.
  { destruct g2; cbn [vstring]; [reflexivity|]. replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  destruct g2 as [|g2]; [cbn [vstring]; replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia); reflexivity|].
  cbn [vstring]. destruct (len <=? i) eqn:EL; [reflexivity|]. apply Z.leb_gt in EL.
  destruct (negb (is_ascii_stop (byte_at d i))); [apply IH; lia|].
  destruct (byte_at d i =? 34); [reflexivity|].
  destruct (byte_at d i =? 92); [apply IH; lia|].
  destruct (128 <=? byte_at d i).
  - destruct (utf8_char d len i) as [i' e'] eqn:EU. apply utf8_char_adv in EU. apply IH; lia.
  - apply IH; lia.
Qed.

Lemma scan_from_fuel : forall f1 f2 d len i acc err uncl, Z.of_nat f1 > len - i -> Z.of_nat f2 > len - i ->
  scan_from f1 d len i acc err uncl = scan_from f2 d len i acc err uncl.
Proof.
  induction f1 as [|f1 IH]; intros [|f2] d len i acc err uncl H1 H2.
  - reflexivity.
  - cbn [scan_from]. replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - cbn [scan_from]. replace (len <=? i) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - cbn [scan_from]. destruct (len <=? i) eqn:EL; [reflexivity|]. apply Z.leb_gt in EL.
    destruct (is_space (byte_at d i)); [apply IH; lia|].
    destruct (byte_at d i =? 34).
    + destruct (vstring (S (Z.to_nat len)) d len (i + 1) err) as [[j|] e] eqn:EV; [|reflexivity].
      apply vstring_some_bound in EV. apply IH; lia.
    + destruct (is_op (byte_at d i)); [apply IH; lia|].
      pose proof (prim_end_ge (Z.to_nat len) d len i). apply IH; lia.
Qed.

(* [comment removed for export] *)
Definition fin3 (R : list Z * bool * bool) : bool * list Z :=
  let '(acc, err, uncl) := R in (negb (match acc with [] => true | _ => false end) && negb err && negb uncl, rev acc).

(* [comment removed for export] *)
Definition S1C (d : list Z) (j : Z) (acc : list Z) (err : bool) : bool * list Z :=
  fin3 (scan_from (S (Z.to_nat (zlength d - j))) d (zlength d) j acc err false).
(* [comment removed for export] *)
Definition VSC (d : list Z) (k : Z) (e : bool) : option Z * bool := vstring (S (Z.to_nat (zlength d - k))) d (zlength d) k e.
(* [comment removed for export] *)
Definition SRES (d : list Z) (i : Z) (acc : list Z) (r : option Z * bool) : bool * list Z :=
  match r with (Some j, e) => S1C d (j + 1) (i :: acc) e | (None, e) => fin3 (i :: acc, e, true) end.
(* [comment removed for export] *)
Definition PEC (d : list Z) (k : Z) : Z := prim_end (S (Z.to_nat (zlength d - k))) d (zlength d) k.

Lemma scan_S1C : forall d, scan d = S1C d 0 [] false.
Proof.
  intros d. unfold scan, S1C, fin3. change (Z.of_nat (length d)) with (zlength d). rewrite (scan_from_fuel (S (length d)) (S (Z.to_nat (zlength d - 0))) d (zlength d) 0 [] false false)
    by (unfold zlength; lia).
  destruct (scan_from _ _ _ _ _ _ _) as [[acc err] uncl]. reflexivity.
Qed.

Section Cont.
Variable d : list Z.
Notation len := (zlength d).

Lemma S1C_stop : forall j acc err, len <= j -> S1C d j acc err = fin3 (acc, err, false).
Proof. intros j acc err H. unfold S1C. rewrite scan_from_stop by lia. reflexivity. Qed.

Lemma S1C_space : forall j acc err, 0 <= j < len -> is_space (byte_at d j) = true -> S1C d j acc err = S1C d (j + 1) acc err.
Proof.
  intros j acc err H Hs. unfold S1C. rewrite scan_from_space by (lia || exact Hs). f_equal. apply scan_from_fuel; lia.
Qed.

Lemma S1C_op : forall j acc err, 0 <= j < len -> is_space (byte_at d j) = false -> byte_at d j <> 34 -> is_op (byte_at d j) = true ->
  S1C d j acc err = S1C d (j + 1) (j :: acc) err.
Proof.
  intros j acc err H Hs Hq Ho. unfold S1C. rewrite scan_from_op by assumption || lia. f_equal. apply scan_from_fuel; lia.
Qed.

Lemma S1C_prim : forall j acc err, 0 <= j < len -> is_space (byte_at d j) = false -> byte_at d j <> 34 -> is_op (byte_at d j) = false ->
  S1C d j acc err = S1C d (PEC d j + 1) (j :: acc) err.
Proof.
  intros j acc err H Hs Hq Ho. unfold S1C, PEC. rewrite scan_from_prim by assumption || lia.
  rewrite (prim_end_fuel (Z.to_nat len) (S (Z.to_nat (len - j))) d len j) by lia.
  pose proof (prim_end_ge (S (Z.to_nat (len - j))) d len j). f_equal. apply scan_from_fuel; lia.
Qed.

Lemma S1C_string : forall j acc err, 0 <= j < len -> is_space (byte_at d j) = false -> byte_at d j = 34 ->
  S1C d j acc err = SRES d j acc (VSC d (j + 1) err).
Proof.
  intros j acc err H Hs Hq. unfold S1C at 1. rewrite scan_from_string by assumption || lia. unfold VSC.
  rewrite (vstring_fuel (S (Z.to_nat len)) (S (Z.to_nat (len - (j + 1)))) d len (j + 1) err) by lia.
  destruct (vstring (S (Z.to_nat (len - (j + 1)))) d len (j + 1) err) as [[k|] e] eqn:EV; cbn [SRES].
  - apply vstring_some_bound in EV. unfold S1C. f_equal. apply scan_from_fuel; lia.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma VSC_stop : forall k e, len <= k -> VSC d k e = (None, e).
Proof. intros k e H. unfold VSC. apply vstring_stop. lia. Qed.
Lemma VSC_plain : forall k e, 0 <= k < len -> is_ascii_stop (byte_at d k) = false -> VSC d k e = VSC d (k + 1) e.
Proof. intros k e H Hs. unfold VSC. rewrite vstring_plain by assumption || lia. apply vstring_fuel; lia. Qed.
Lemma VSC_quote : forall k e, 0 <= k < len -> byte_at d k = 34 -> VSC d k e = (Some k, e).
Proof. intros k e H Hq. unfold VSC. apply vstring_quote; lia || exact Hq. Qed.
Lemma VSC_bslash : forall k e, 0 <= k < len -> byte_at d k = 92 -> VSC d k e = VSC d (k + 2) e.
Proof. intros k e H Hq. unfold VSC. rewrite vstring_bslash by assumption || lia. apply vstring_fuel; lia. Qed.
Lemma VSC_ctrl : forall k e, 0 <= k < len -> 0 <= byte_at d k < 32 -> VSC d k e = VSC d (k + 1) true.
Proof. intros k e H Hc. unfold VSC. rewrite vstring_ctrl by assumption || lia. apply vstring_fuel; lia. Qed.
Lemma VSC_utf8 : forall k e, 0 <= k < len -> 128 <= byte_at d k ->
  VSC d k e = let '(k', e') := utf8_char d len k in VSC d k' (e || e').
Proof.
  intros k e H Hc. unfold VSC. rewrite vstring_utf8 by assumption || lia.
  destruct (utf8_char d len k) as [k' e'] eqn:EU. apply utf8_char_adv in EU. apply vstring_fuel; lia.
Qed.

(* [comment removed for export] *)
Lemma PEC_step : forall k, 0 <= k -> k + 1 < len -> primc (byte_at d (k + 1)) = true -> PEC d k = PEC d (k + 1).
Proof. intros k H0 H Hp. unfold PEC. rewrite prim_end_step by assumption. apply prim_end_fuel; lia. Qed.
Lemma PEC_here : forall k, (len <= k + 1 \/ primc (byte_at d (k + 1)) = false) -> PEC d k = k.
Proof. intros k H. unfold PEC. apply prim_end_here. exact H. Qed.
End Cont.
