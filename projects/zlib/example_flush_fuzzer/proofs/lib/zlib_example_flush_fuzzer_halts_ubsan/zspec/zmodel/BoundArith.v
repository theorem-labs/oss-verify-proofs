(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees Deflate
  OverlayFBS OverlayRace OverlayCmp OverlayFlush DeflateInv DeflInvTally.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition cdiv8 (v : Z) : Z := (v + 7) / 8.

Lemma cdiv8_mul : forall k v, cdiv8 (8 * k + v) = k + cdiv8 v.
Proof. intros. unfold cdiv8. replace (8 * k + v + 7) with (v + 7 + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma cdiv8_add_le : forall a b, 0 <= b -> cdiv8 (a + b) <= cdiv8 a + cdiv8 b.
Proof.
  intros a b Hb. unfold cdiv8.
  set (q := (a + 7) / 8). set (p := (b + 7) / 8).
  pose proof (Z.div_mod (a + 7) 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound (a + 7) 8 ltac:(lia)) as B1.
  pose proof (Z.div_mod (b + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (b + 7) 8 ltac:(lia)) as B2.
  fold q in E1. fold p in E2.
  enough ((a + b + 7) / 8 < q + p + 1) by lia. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma cdiv8_mono : forall a b, a <= b -> cdiv8 a <= cdiv8 b.
Proof. intros. unfold cdiv8. apply Z.div_le_mono; lia. Qed.

Lemma cdiv8_0 : cdiv8 0 = 0. Proof. reflexivity. Qed.
Lemma cdiv8_le : forall v, 0 <= v -> 0 <= cdiv8 v /\ 8 * cdiv8 v < v + 8 /\ v <= 8 * cdiv8 v.
Proof.
  intros v Hv. unfold cdiv8. pose proof (Z.div_mod (v + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (v + 7) 8 ltac:(lia)).
  pose proof (Z.div_pos (v + 7) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma cdiv8_small : forall v, 0 <= v <= 8 -> cdiv8 v <= 1.
Proof. intros v Hv. unfold cdiv8. enough ((v + 7) / 8 < 2) by lia. apply Z.div_lt_upper_bound; lia. Qed.
Lemma cdiv8_3 : forall v, 0 <= v -> cdiv8 (v + 3) <= cdiv8 v + 1.
Proof. intros v Hv. pose proof (cdiv8_add_le v 3 ltac:(lia)). change (cdiv8 3) with 1 in H. lia. Qed.

Lemma lenb_cdiv8 : forall x, 0 <= x -> Z.shiftr (x + 3 + 7) 3 = cdiv8 (x + 3).
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. unfold cdiv8. change (2 ^ 3) with 8. f_equal. Qed.


Definition cb_budget (n : Z) : Z := n + 11 + 5 * (n / 16383).

Lemma cb_budget_le : forall n, 0 <= n <= 2 ^ 26 -> cb_budget n <= compressBound_m n.
Proof.
  intros n Hn. unfold cb_budget, compressBound_m.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 12) with 4096. change (2 ^ 14) with 16384. change (2 ^ 25) with 33554432.
  pose proof (Z.div_pos n 33554432 ltac:(lia) ltac:(lia)) as P25.
  assert (U25 : n / 33554432 <= 2) by (enough (n / 33554432 < 3) by lia; apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_mod n 16383 ltac:(lia)) as E. pose proof (Z.mod_pos_bound n 16383 ltac:(lia)) as R.
  set (q := n / 16383) in *. set (r := n mod 16383) in *.
  assert (Q : 0 <= q <= 4097) by (subst q; split; [apply Z.div_pos; lia | enough (n / 16383 < 4098) by lia; apply Z.div_lt_upper_bound; lia]).
  assert (A : 4 * q - 1 <= n / 4096) by (apply Z.div_le_lower_bound; lia).
  assert (B : q - 1 <= n / 16384) by (apply Z.div_le_lower_bound; lia).
  assert (A0 : 0 <= n / 4096) by (apply Z.div_pos; lia).
  assert (B0 : 0 <= n / 16384) by (apply Z.div_pos; lia).
  rewrite wrap64_id by lia. lia.
Qed.


Definition scov (x : Z * Z) : Z := let '(d, lc) := x in if d =? 0 then 1 else lc + MIN_MATCH.

Lemma zcov_csum : forall l, zcov l = csum scov l.
Proof. induction l as [|[d lc] l IH]; [reflexivity|]. unfold zcov in *. cbn [fold_right csum]. rewrite IH. reflexivity. Qed.

Definition too_far_ok (x : Z * Z) : Prop := fst x <> 0 -> snd x = 0 -> fst x <= TOO_FAR.

Lemma dist_code_near : forall k, 0 <= k < 288 -> 0 <= arr_get dist_code_a k <= 23.
Proof. intros k H. exact (table_range dist_code_a 0 23 288 ltac:(vm_compute; reflexivity) k ltac:(lia)). Qed.

Lemma d_code_near : forall d, 0 <= d < 4096 -> 0 <= d_code d <= 23.
Proof.
  intros d Hd. unfold d_code. destruct (Z.ltb_spec d 256).
  - apply dist_code_near. lia.
  - apply dist_code_near. rewrite Z.shiftr_div_pow2 by lia.
    assert (0 <= d / 2 ^ 7) by (apply Z.div_pos; lia).
    assert (d / 2 ^ 7 < 32) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma extra_dbits_near : forall i, 0 <= i <= 23 -> 0 <= arr_get extra_dbits_a i <= 10.
Proof. intros i Hi. exact (table_range extra_dbits_a 0 10 24 ltac:(vm_compute; reflexivity) i ltac:(lia)). Qed.

Lemma length_code_0 : arr_get length_code_a 0 = 0. Proof. reflexivity. Qed.
Lemma length_code_1 : arr_get length_code_a 1 = 1. Proof. reflexivity. Qed.
Lemma extra_lbits_0 : arr_get extra_lbits_a 0 = 0. Proof. reflexivity. Qed.
Lemma extra_lbits_1 : arr_get extra_lbits_a 1 = 0. Proof. reflexivity. Qed.

Lemma scost_match : forall d lc, sym_valid (d, lc) -> d <> 0 -> too_far_ok (d, lc) ->
  scost (d, lc) <= 31 /\ scost (d, lc) <= 7 * lc + 22.
Proof.
  intros d lc V Hd TF. pose proof (scost_bound (d, lc) V) as SB. split; [lia|].
  unfold sym_valid in V. unfold too_far_ok, TOO_FAR in TF. cbn [fst snd] in TF.
  destruct (Z.le_gt_cases 2 lc); [lia|].
  unfold scost. replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hd).
  pose proof (d_code_range (d - 1) ltac:(unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in V; lia)) as DR.
  pose proof (extra_dbits_range _ DR) as XD.
  assert (lc = 0 \/ lc = 1) as [-> | ->] by lia.
  - rewrite length_code_0, extra_lbits_0. unfold LITERALS. replace (arr_get static_ltree_dl (0 + 256 + 1)) with 7 by reflexivity.
    pose proof (d_code_near (d - 1) ltac:(lia)) as DN. pose proof (extra_dbits_near _ DN). lia.
  - rewrite length_code_1, extra_lbits_1. unfold LITERALS. replace (arr_get static_ltree_dl (1 + 256 + 1)) with 7 by reflexivity. lia.
Qed.

Lemma scost_lit : forall lc, sym_valid (0, lc) -> scost (0, lc) <= 9.
Proof.
  intros lc V. unfold sym_valid in V. unfold scost. rewrite Z.eqb_refl. rewrite static_ltree_len by lia.
  destruct (lc <? 144); [lia|]. destruct (Z.ltb_spec lc 256); lia.
Qed.

Definition islit (x : Z * Z) : bool := fst x =? 0.
Definition nlit (l : list (Z * Z)) : Z := csum (fun x => if islit x then 1 else 0) l.
Definition nmatch (l : list (Z * Z)) : Z := csum (fun x => if islit x then 0 else 1) l.
Definition mcov (l : list (Z * Z)) : Z := csum (fun x => if islit x then 0 else scov x) l.
Definition mcost (l : list (Z * Z)) : Z := csum (fun x => if islit x then 0 else scost x) l.

Lemma sums_facts : forall l, Forall sym_valid l -> Forall too_far_ok l ->
  Z.of_nat (length l) = nlit l + nmatch l
  /\ zcov l = nlit l + mcov l
  /\ csum scost l <= 9 * nlit l + mcost l
  /\ mcost l <= 31 * nmatch l
  /\ mcost l <= 7 * mcov l + nmatch l
  /\ 3 * nmatch l <= mcov l
  /\ 0 <= nlit l /\ 0 <= nmatch l.
Proof.
  intros l V T. rewrite zcov_csum. induction l as [|[d lc] l IH].
  - cbn. lia.
  - inversion V as [|x l' Vx Vl]; subst. inversion T as [|x l' Tx Tl]; subst.
    specialize (IH Vl Tl). destruct IH as (A & B & C & D & E & F & G).
    unfold nlit, nmatch, mcov, mcost, islit, scov in *. cbn [csum length fst snd] in *. rewrite Nat2Z.inj_succ.
    destruct (Z.eqb_spec d 0) as [-> | Hd].
    + pose proof (scost_lit lc Vx). lia.
    + pose proof (scost_match d lc Vx Hd Tx) as [M1 M2].
      assert (0 <= lc) by (unfold sym_valid in Vx; lia). unfold MIN_MATCH in *. lia.
Qed.

Theorem Sstat_big_block : forall l L,
  Forall sym_valid l -> Forall too_far_ok l ->
  Z.of_nat (length l) <= 16383 -> L - 1 <= zcov l <= L -> 32507 <= L ->
  Sstat l <= 8 * L + 7.
Proof.
  intros l L V T N C BIG. unfold Sstat.
  destruct (sums_facts l V T) as (A & B & Cs & D & E & F & G).
  destruct (Z.le_gt_cases 260 (nmatch l)); lia.
Qed.
