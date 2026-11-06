(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs BnSpecs2 BnAddSpec BnMulSpec.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BgState BgWords BgLib BgInv BgSpecs BgLibSpec BgAddSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_word_limbs_spec : forall l w, limbs l -> 0 <= w < BW ->
  let '(l', w') := add_word_limbs l w in
  limbs l' /\ length l' = length l /\ 0 <= w' < BW /\ (l <> [] -> w' <= 1) /\ lval l' + Bp (length l) * w' = lval l + w.
Proof.
  induction l as [|x l IH]; intros w Hl Hw.
  - cbn [add_word_limbs lval length]. rewrite Bp_0. repeat split; try lia; try constructor. intros H; contradiction.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. cbn [add_word_limbs].
    destruct (Z.eqb_spec w 0) as [->|Hw0].
    + cbn [lval length]. repeat split; try lia. constructor; [split; assumption|exact Hl].
    + unfold addw. set (s := (x + w) mod BW).
      assert (Hs : 0 <= s < BW) by (apply Z.mod_pos_bound; unfold BW; lia).
      set (c := if s <? w then 1 else 0).
      assert (Hc : (c = 0 \/ c = 1) /\ x + w = s + BW * c).
      { unfold c, s. destruct (Z.lt_ge_cases (x + w) BW) as [Hlt|Hge].
        - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (x + w) w); [lia|]. split; [left; reflexivity|lia].
        - assert (E : (x + w) mod BW = x + w - BW).
          { symmetry. apply (Z.mod_unique (x + w) BW 1 (x + w - BW)); lia. }
          rewrite E. destruct (Z.ltb_spec (x + w - BW) w); [|lia]. split; [right; reflexivity|lia]. }
      destruct Hc as [Hc01 Hcs].
      specialize (IH c Hl ltac:(unfold BW; lia)). destruct (add_word_limbs l c) as [r w'] eqn:Er.
      destruct IH as (I1 & I2 & I3 & I4 & I5). cbn [lval length].
      split; [constructor; [exact Hs|exact I1]|]. split; [lia|]. split; [exact I3|]. split.
      * intros _. destruct l as [|y l']; [cbn [add_word_limbs] in Er; injection Er as <- <-; lia|]. apply I4. discriminate.
      * rewrite Bp_S. nia.
Qed.

Lemma firstn_upd_last : forall buf t v, (t < length buf)%nat -> firstn (t + 1) (upd buf t v) = firstn t buf ++ [v].
Proof.
  intros buf t v H. unfold upd, splice. cbn [length]. rewrite firstn_app, firstn_length_le by lia.
  rewrite (firstn_all2 (firstn t buf)) by (rewrite firstn_length_le; lia).
  replace (t + 1 - t)%nat with 1%nat by lia. reflexivity.
Qed.

Lemma sub_word_limbs_spec : forall l w k, limbs l -> 0 <= w < BW -> w <= lval l ->
  let '(l', i) := sub_word_limbs l w k in
  limbs l' /\ length l' = length l /\ lval l' = lval l - w /\ (k <= i)%nat /\ (l <> [] -> i < k + length l)%nat /\
  (forall j, (i - k < j)%nat -> nth j l' 0 = nth j l 0).
Proof.
  induction l as [|x l IH]; intros w k Hl Hw Hle.
  - cbn [sub_word_limbs lval length] in *. repeat split; try lia; try constructor. intros H; contradiction.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. cbn [sub_word_limbs]. cbn [lval] in Hle.
    pose proof (lval_nonneg l Hl) as Hv.
    destruct (Z.leb_spec w x) as [Hwx|Hwx].
    + cbn [lval length]. split; [constructor; [unfold limb; lia|exact Hl]|]. repeat split; try lia.
      intros j Hj. destruct j; [lia|reflexivity].
    + assert (Hl1 : 1 <= lval l) by nia.
      specialize (IH 1 (S k) Hl ltac:(unfold BW; lia) Hl1). destruct (sub_word_limbs l 1 (S k)) as [r i'] eqn:Er.
      destruct IH as (I1 & I2 & I3 & I4 & I5 & I6). cbn [lval length].
      assert (Es : subw x w = x - w + BW).
      { unfold subw. symmetry. apply (Z.mod_unique (x - w) BW (-1) (x - w + BW)); lia. }
      split; [constructor; [rewrite Es; unfold limb; lia|exact I1]|]. split; [lia|]. split; [rewrite Es, I3; lia|].
      split; [lia|]. split.
      * intros _. assert (l <> []) by (intros ->; cbn in Hl1; lia). specialize (I5 H). lia.
      * intros j Hj. destruct j; [lia|]. cbn [nth]. apply I6. lia.
Qed.

Section WordSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma firstn_top_limbs : forall b : BN, bg_okv b -> limbs (firstn (bn_top b) (bn_buf b)) /\ length (firstn (bn_top b) (bn_buf b)) = bn_top b.
Proof. intros b (H1 & H2). split; [apply limbs_firstn; exact H1|apply firstn_length_le; exact H2]. Qed.

(* [comment removed for export] *)
Lemma norm_of_mag_ge : forall b : BN, bg_okv b -> (bn_top b = 0%nat \/ Bp (bn_top b - 1) <= bn_mag b) -> bn_norm b.
Proof.
  intros b Hb [H|H]; [left; exact H|]. destruct (Nat.eq_dec (bn_top b) 0) as [E|E]; [left; exact E|right].
  destruct (firstn_top_limbs b Hb) as [Hl Hlen].
  pose proof (top_limb_nonzero _ (bn_top b) Hl Hlen ltac:(lia) H) as Hnz.
  rewrite nth_firstn in Hnz. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [exact Hnz|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_add_word_spec : forall r w F s, (r < length (st_bns s))%nat -> r <> ROne -> 0 <= w < BW ->
  bn_norm (getbn r s) -> bn_neg (getbn r s) = false -> Z.of_nat (bn_top (getbn r s)) + 1 <= BG_DMAX ->
  hoare F s (BN_add_word ops r w) (upd1 r s (fun b' =>
     bn_mag b' = bn_mag (getbn r s) + w /\ bn_norm b' /\ bn_neg b' = false /\ (bn_top b' <= bn_top (getbn r s) + 1)%nat)).
Proof.
  intros r w F s Hr Hn Hw Hnorm Hneg Hsz. apply hoare_wf. intros Hs. unfold BN_add_word.
  pose proof (st_wf_ok r s Hs Hr Hn) as Hok. pose proof (bg_ok_okv _ Hok) as Hokv.
  destruct (Z.eqb_spec w 0) as [->|Hw0].
  { apply hoare_ret. exists (getbn r s). split; [rewrite setbn_getbn_id; reflexivity|]. repeat split; try assumption; lia. }
  apply hoare_bind_get. set (a := getbn r s) in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [Et|Et].
  { eapply hoare_mono; [apply BN_set_word_spec; [exact Hr|exact Hn|exact Hw]|].
    intros [] s1 _ (b1 & -> & M1 & [M2 _] & M3 & M4). exists b1. split; [reflexivity|]. rewrite (bn_mag_top0 a Et). repeat split; try assumption; lia. }
  rewrite Hneg.
  destruct (firstn_top_limbs a Hokv) as [Hsl Hslen]. set (src := firstn (bn_top a) (bn_buf a)) in *.
  pose proof (add_word_limbs_spec src w Hsl Hw) as Hp. destruct (add_word_limbs src w) as [l w'] eqn:El.
  destruct Hp as (P1 & P2 & P3 & P4 & P5). rewrite Hslen in P2, P5.
  assert (Hne : src <> []) by (intros E; rewrite E in Hslen; cbn in Hslen; lia). specialize (P4 Hne).
  pose proof Hok as (O1 & O2 & O3 & O4). unfold bn_dmax in *.
  assert (Hlen1 : length (splice (bn_buf a) 0 l) = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) (splice (bn_buf a) 0 l) = l) by (apply firstn_splice_0; [exact P2|lia]).
  assert (Hmag_a : bn_mag a = lval src) by reflexivity.
  apply hoare_bind_set; try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite Hlen1. split; [apply splice_limbs; assumption|]. repeat split; try assumption. }
  set (b1 := bn_with_buf a (splice (bn_buf a) 0 l)).
  destruct (Z.eqb_spec w' 0) as [Ew|Ew].
  - apply hoare_ret. exists b1. split; [reflexivity|]. unfold bn_mag at 1. cbn [b1 bn_with_buf bn_top bn_buf bn_neg]. rewrite Hf1.
    split; [lia|]. split; [|split; [exact Hneg|lia]].
    apply norm_of_mag_ge.
    + unfold b1. split; cbn [bn_with_buf bn_buf bn_top]; [apply splice_limbs; assumption|unfold bn_dmax; cbn [bn_with_buf bn_buf]; rewrite Hlen1; exact O2].
    + right. unfold bn_mag, b1. cbn [bn_with_buf bn_top bn_buf]. rewrite Hf1.
      pose proof (okv_mag_ge a Hokv Hnorm ltac:(lia)). lia.
  - assert (Ew1 : w' = 1) by lia.
    eapply hoare_bind; [apply bn_wexpand_spec; [rewrite length_setbn; exact Hr|exact Hn|lia]|].
    intros [] s2 Hs2 (b2 & -> & Hex). rewrite getbn_setbn_same in Hex by exact Hr. rewrite setbn_setbn_same.
    apply hoare_bind_get. rewrite getbn_setbn_same by exact Hr.
    pose proof (gexpanded_prefix b1 b2 _ ltac:(unfold bg_ok, bn_dmax, b1; cbn [bn_with_buf bn_buf bn_top bn_flags]; rewrite Hlen1; split; [apply splice_limbs; assumption|repeat split; assumption]) Hex) as Hpre.
    destruct Hex as (E1 & E2 & E3 & E4 & Hok2 & Hd2 & Hd3). pose proof Hok2 as (Q1 & Q2 & Q3 & Q4). unfold bn_dmax in *.
    cbn [b1 bn_with_buf bn_top bn_buf bn_neg bn_flags] in E1, E2, E3, Hpre. rewrite Hf1 in Hpre.
    assert (Hlen2 : length (upd (bn_buf b2) (bn_top a) w') = length (bn_buf b2)) by (apply upd_length; lia).
    eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen2. split; [apply upd_limbs; [exact Q1|unfold limb; lia]|]. repeat split; try assumption; lia.
    + rewrite setbn_setbn_same. eexists. split; [reflexivity|].
      assert (Hfst : firstn (bn_top a + 1) (upd (bn_buf b2) (bn_top a) w') = l ++ [w']).
      { rewrite <- Hpre. apply firstn_upd_last. lia. }
      unfold bn_mag at 1, bn_norm. cbn [bn_top bn_buf bn_neg]. rewrite Hfst, lval_app, P2. cbn [lval].
      split; [lia|]. split; [|split; [rewrite E2; exact Hneg|lia]].
      right. replace (bn_top a + 1 - 1)%nat with (bn_top a) by lia. rewrite nth_upd_same by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_sub_word_spec : forall r w F s, (r < length (st_bns s))%nat -> r <> ROne -> 0 <= w < BW ->
  bn_norm (getbn r s) -> bn_neg (getbn r s) = false -> w <= bn_mag (getbn r s) ->
  hoare F s (BN_sub_word ops r w) (upd1 r s (fun b' =>
     bn_mag b' = bn_mag (getbn r s) - w /\ bn_norm b' /\ bn_neg b' = false /\ (bn_top b' <= bn_top (getbn r s))%nat)).
Proof.
  intros r w F s Hr Hn Hw Hnorm Hneg Hle. apply hoare_wf. intros Hs. unfold BN_sub_word.
  pose proof (st_wf_ok r s Hs Hr Hn) as Hok. pose proof (bg_ok_okv _ Hok) as Hokv.
  destruct (Z.eqb_spec w 0) as [->|Hw0].
  { apply hoare_ret. exists (getbn r s). split; [rewrite setbn_getbn_id; reflexivity|]. repeat split; try assumption; lia. }
  apply hoare_bind_get. set (a := getbn r s) in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [Et|Et]; [rewrite (bn_mag_top0 a Et) in Hle; lia|].
  rewrite Hneg.
  destruct (firstn_top_limbs a Hokv) as [Hsl Hslen]. set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hmag_a : bn_mag a = lval src) by reflexivity.
  assert (Hn0 : nth 0 (bn_buf a) 0 = nth 0 src 0).
  { unfold src. rewrite nth_firstn. destruct (Nat.ltb_spec 0 (bn_top a)); [reflexivity|lia]. }
  assert (Hcase : ((bn_top a =? 1)%nat && (nth 0 (bn_buf a) 0 <? w)) = false).
  { destruct (Nat.eqb_spec (bn_top a) 1) as [E1|E1]; [|reflexivity]. cbn [andb]. apply Z.ltb_ge.
    rewrite Hn0. destruct src as [|x [|y t]]; cbn in Hslen; try lia. cbn [nth]. rewrite Hmag_a in Hle. cbn [lval] in Hle. lia. }
  rewrite Hcase.
  pose proof (sub_word_limbs_spec src w 0 Hsl Hw ltac:(lia)) as Hp. destruct (sub_word_limbs src w 0) as [l i] eqn:El.
  destruct Hp as (P1 & P2 & P3 & P4 & P5 & P6). rewrite Hslen in P2, P5.
  assert (Hne : src <> []) by (intros E; rewrite E in Hslen; cbn in Hslen; lia). specialize (P5 Hne).
  pose proof Hok as (O1 & O2 & O3 & O4). unfold bn_dmax in *.
  set (buf := splice (bn_buf a) 0 l).
  assert (Hlen1 : length buf = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) buf = l) by (apply firstn_splice_0; [exact P2|lia]).
  assert (Hnb : forall j, (j < bn_top a)%nat -> nth j buf 0 = nth j l 0).
  { intros j Hj. rewrite <- Hf1. rewrite nth_firstn. destruct (Nat.ltb_spec j (bn_top a)); [reflexivity|lia]. }
  set (top := if (nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat then (bn_top a - 1)%nat else bn_top a).
  assert (Hokv' : bg_okv (mkBN (bn_d a) buf top false (bn_flags a))).
  { split; cbn [bn_buf bn_top]; [apply splice_limbs; assumption|]. unfold bn_dmax. cbn [bn_buf]. rewrite Hlen1.
    unfold top. destruct ((nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat); lia. }
  eapply hoare_set; try assumption; try reflexivity.
  - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen1. split; [apply splice_limbs; assumption|].
    repeat split; try assumption. unfold top. destruct ((nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat); lia.
  - eexists. split; [reflexivity|].
    pose proof (okv_mag_ge a Hokv Hnorm ltac:(lia)) as Hge.
    (* [comment removed for export] *)
    assert (Hmag' : bn_mag (mkBN (bn_d a) buf top false (bn_flags a)) = lval src - w).
    { unfold bn_mag. cbn [bn_top bn_buf]. unfold top.
      destruct ((nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat) eqn:Ec; [|rewrite Hf1; exact P3].
      apply andb_prop in Ec. destruct Ec as [Ez Ei]. apply Z.eqb_eq in Ez. apply Nat.eqb_eq in Ei.
      rewrite (firstn_of_firstn buf (bn_top a - 1) (bn_top a)) by lia. rewrite Hf1.
      rewrite <- P3. pose proof (lval_split_le (bn_top a - 1) l ltac:(lia)) as Hsp.
      assert (Hsk : lval (skipn (bn_top a - 1) l) = 0).
      { assert (Hlk : length (skipn (bn_top a - 1) l) = 1%nat) by (rewrite length_skipn; lia).
        destruct (skipn (bn_top a - 1) l) as [|y [|z t]] eqn:Es; cbn in Hlk; try lia.
        assert (Hy : nth (bn_top a - 1) l 0 = y).
        { rewrite <- (firstn_skipn (bn_top a - 1) l), Es. rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
          rewrite firstn_length_le by lia. rewrite Nat.sub_diag. reflexivity. }
        rewrite <- Hnb, <- Ei, Ez in Hy by lia. subst y. reflexivity. }
      rewrite Hsp, Hsk. lia. }
    split; [exact Hmag'|]. split; [|split; [reflexivity|unfold top; cbn [bn_top]; destruct ((nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat); lia]].
    (* [comment removed for export] *)
    unfold top in *. destruct ((nth i buf 0 =? 0) && (i =? bn_top a - 1)%nat) eqn:Ec.
    + apply norm_of_mag_ge; [exact Hokv'|]. cbn [bn_top]. destruct (Nat.eq_dec (bn_top a - 1) 0) as [E0|E0]; [left; exact E0|right].
      rewrite Hmag', <- Hmag_a.
      assert (Hb : Bp (bn_top a - 1 - 1) * BW = Bp (bn_top a - 1)).
      { replace (bn_top a - 1)%nat with (S (bn_top a - 1 - 1)) at 2 by lia. rewrite Bp_S. lia. }
      pose proof (Bp_ge1 (bn_top a - 1 - 1)). nia.
    + right. cbn [bn_top bn_buf]. rewrite Hnb by lia.
      apply andb_false_iff in Ec. destruct Hnorm as [Hnorm|Hnorm]; [lia|].
      destruct (Nat.eq_dec i (bn_top a - 1)) as [Ei|Ei].
      * destruct Ec as [Ec|Ec]; [|apply Nat.eqb_neq in Ec; lia]. apply Z.eqb_neq in Ec. rewrite Hnb in Ec by lia. rewrite <- Ei. exact Ec.
      * rewrite P6 by lia. unfold src. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [exact Hnorm|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_mul_word_spec : forall r w F s, (r < length (st_bns s))%nat -> r <> ROne -> 0 <= w < BW ->
  bn_norm (getbn r s) -> Z.of_nat (bn_top (getbn r s)) + 1 <= BG_DMAX ->
  hoare F s (BN_mul_word ops r w) (upd1 r s (fun b' =>
     bn_mag b' = bn_mag (getbn r s) * w /\ bn_norm b' /\ (bn_neg (getbn r s) = false -> bn_neg b' = false) /\
     (bn_top b' <= bn_top (getbn r s) + 1)%nat)).
Proof.
  intros r w F s Hr Hn Hw Hnorm Hsz. apply hoare_wf. intros Hs. unfold BN_mul_word.
  pose proof (st_wf_ok r s Hs Hr Hn) as Hok. pose proof (bg_ok_okv _ Hok) as Hokv.
  apply hoare_bind_get. set (a := getbn r s) in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [Et|Et].
  { apply hoare_ret. exists a. split; [unfold a; rewrite setbn_getbn_id; reflexivity|]. rewrite (bn_mag_top0 a Et). repeat split; try assumption; try lia; auto. }
  destruct (Z.eqb_spec w 0) as [->|Hw0].
  { eapply hoare_mono; [apply BN_zero_spec; assumption|]. intros [] s1 _ (b1 & -> & T1 & T2). exists b1. split; [reflexivity|].
    rewrite (bn_mag_top0 b1 T1). split; [lia|]. split; [left; exact T1|]. split; [intros _; exact T2|lia]. }
  destruct (firstn_top_limbs a Hokv) as [Hsl Hslen]. set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hmag_a : bn_mag a = lval src) by reflexivity.
  pose proof (mul_words_spec src w Hsl ltac:(unfold limb; lia)) as Hp. destruct (mul_words src w) as [l ll] eqn:El.
  destruct Hp as (P1 & P2 & [P3 P3'] & P4). rewrite Hslen in P2, P4.
  pose proof Hok as (O1 & O2 & O3 & O4). unfold bn_dmax in *.
  assert (Hlen1 : length (splice (bn_buf a) 0 l) = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) (splice (bn_buf a) 0 l) = l) by (apply firstn_splice_0; [exact P2|lia]).
  pose proof (okv_mag_ge a Hokv Hnorm ltac:(lia)) as Hge.
  apply hoare_bind_set; try assumption; try reflexivity.
  { unfold bg_ok, bn_dmax. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite Hlen1. split; [apply splice_limbs; assumption|]. repeat split; try assumption. }
  set (b1 := bn_with_buf a (splice (bn_buf a) 0 l)).
  assert (Hb1 : bg_ok b1).
  { unfold bg_ok, bn_dmax, b1. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite Hlen1. split; [apply splice_limbs; assumption|]. repeat split; assumption. }
  destruct (Z.eqb_spec ll 0) as [Ew|Ew].
  - apply hoare_ret. exists b1. split; [reflexivity|].
    assert (Hm1 : bn_mag b1 = bn_mag a * w) by (unfold bn_mag at 1, b1; cbn [bn_with_buf bn_top bn_buf]; rewrite Hf1; lia).
    split; [exact Hm1|]. split; [|split; [intros H; exact H|cbn; lia]].
    apply norm_of_mag_ge; [apply bg_ok_okv; exact Hb1|]. right. rewrite Hm1. change (bn_top b1) with (bn_top a).
    assert (1 <= w) by lia. pose proof (Bp_pos (bn_top a - 1)). nia.
  - eapply hoare_bind; [apply bn_wexpand_spec; [rewrite length_setbn; exact Hr|exact Hn|lia]|].
    intros [] s2 Hs2 (b2 & -> & Hex). rewrite getbn_setbn_same in Hex by exact Hr. rewrite setbn_setbn_same.
    apply hoare_bind_get. rewrite getbn_setbn_same by exact Hr.
    pose proof (gexpanded_prefix b1 b2 _ Hb1 Hex) as Hpre.
    destruct Hex as (E1 & E2 & E3 & E4 & Hok2 & Hd2 & Hd3). pose proof Hok2 as (Q1 & Q2 & Q3 & Q4). unfold bn_dmax in *.
    cbn [b1 bn_with_buf bn_top bn_buf bn_neg bn_flags] in E1, E2, E3, Hpre. rewrite Hf1 in Hpre.
    assert (Hlen2 : length (upd (bn_buf b2) (bn_top a) ll) = length (bn_buf b2)) by (apply upd_length; lia).
    eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen2. split; [apply upd_limbs; [exact Q1|unfold limb; lia]|]. repeat split; try assumption; lia.
    + rewrite setbn_setbn_same. eexists. split; [reflexivity|].
      assert (Hfst : firstn (bn_top a + 1) (upd (bn_buf b2) (bn_top a) ll) = l ++ [ll]).
      { rewrite <- Hpre. apply firstn_upd_last. lia. }
      unfold bn_mag at 1, bn_norm. cbn [bn_top bn_buf bn_neg]. rewrite Hfst, lval_app, P2. cbn [lval].
      split; [lia|]. split; [|split; [rewrite E2; intros H; exact H|lia]].
      right. replace (bn_top a + 1 - 1)%nat with (bn_top a) by lia. rewrite nth_upd_same by lia. exact Ew.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_rshift1_spec : forall r F s, (r < length (st_bns s))%nat -> r <> ROne -> bn_norm (getbn r s) ->
  hoare F s (BN_rshift1 ops r r) (upd1 r s (fun b' =>
     bn_mag b' = bn_mag (getbn r s) / 2 /\ bn_norm b' /\ (bn_neg (getbn r s) = false -> bn_neg b' = false) /\
     (bn_top b' <= bn_top (getbn r s))%nat)).
Proof.
  intros r F s Hr Hn Hnorm. apply hoare_wf. intros Hs. unfold BN_rshift1.
  pose proof (st_wf_ok r s Hs Hr Hn) as Hok. pose proof (bg_ok_okv _ Hok) as Hokv.
  apply hoare_bind_get. set (a := getbn r s) in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [Et|Et].
  { eapply hoare_mono; [apply BN_zero_spec; assumption|]. intros [] s1 _ (b1 & -> & T1 & T2). exists b1. split; [reflexivity|].
    rewrite (bn_mag_top0 b1 T1), (bn_mag_top0 a Et). split; [reflexivity|]. split; [left; exact T1|]. split; [intros _; exact T2|lia]. }
  rewrite Nat.eqb_refl. apply hoare_bind_ret. apply hoare_bind_get. apply hoare_bind_get. fold a.
  destruct (firstn_top_limbs a Hokv) as [Hsl Hslen]. set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hmag_a : bn_mag a = lval src) by reflexivity.
  destruct (rshift_limbs_spec src 1 Hsl ltac:(lia)) as (R1 & R2 & R3). rewrite Hslen in R2.
  pose proof Hok as (O1 & O2 & O3 & O4). unfold bn_dmax in *.
  set (buf := splice (bn_buf a) 0 (rshift_limbs src 1)).
  assert (Hlen1 : length buf = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) buf = rshift_limbs src 1) by (apply firstn_splice_0; [exact R2|lia]).
  set (t := nth (bn_top a - 1) (bn_buf a) 0).
  set (top := if t =? 1 then (bn_top a - 1)%nat else bn_top a).
  pose proof (okv_mag_ge a Hokv Hnorm ltac:(lia)) as Hge.
  (* [comment removed for export] *)
  assert (Ht : bn_mag a = lval (firstn (bn_top a - 1) src) + Bp (bn_top a - 1) * t /\ 0 <= lval (firstn (bn_top a - 1) src) < Bp (bn_top a - 1)).
  { pose proof (lval_split_le (bn_top a - 1) src ltac:(lia)) as Hsp.
    assert (Hsk : skipn (bn_top a - 1) src = [t]).
    { assert (Hlk : length (skipn (bn_top a - 1) src) = 1%nat) by (rewrite length_skipn; lia).
      destruct (skipn (bn_top a - 1) src) as [|y [|z u]] eqn:Es; cbn in Hlk; try lia. f_equal.
      assert (Hy : nth (bn_top a - 1) src 0 = y).
      { rewrite <- (firstn_skipn (bn_top a - 1) src), Es. rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
        rewrite firstn_length_le by lia. rewrite Nat.sub_diag. reflexivity. }
      rewrite <- Hy. unfold src, t. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [reflexivity|lia]. }
    rewrite Hsk in Hsp. cbn [lval] in Hsp. rewrite Z.mul_0_r, Z.add_0_r in Hsp. split; [rewrite Hmag_a; exact Hsp|].
    pose proof (lval_bound _ (limbs_firstn (bn_top a - 1) src Hsl)) as Hb. rewrite firstn_length_le in Hb by lia. exact Hb. }
  destruct Ht as [Ht Hlo].
  assert (Htl : 0 <= t < BW) by (apply limbs_nth; exact O1).
  assert (Hokv' : bg_okv (mkBN (bn_d a) buf top (if (top =? 0)%nat then false else bn_neg a) (bn_flags a))).
  { split; cbn [bn_buf bn_top]; [apply splice_limbs; assumption|]. unfold bn_dmax. cbn [bn_buf]. rewrite Hlen1. unfold top. destruct (t =? 1); lia. }
  assert (Hmag' : bn_mag (mkBN (bn_d a) buf top (if (top =? 0)%nat then false else bn_neg a) (bn_flags a)) = bn_mag a / 2).
  { unfold bn_mag at 1. cbn [bn_top bn_buf]. unfold top. destruct (Z.eqb_spec t 1) as [E1|E1]; [|rewrite Hf1, R3; reflexivity].
    rewrite (firstn_of_firstn buf (bn_top a - 1) (bn_top a)) by lia. rewrite Hf1.
    rewrite lval_firstn_small; [rewrite R3; reflexivity|exact R1|]. rewrite R3, <- Hmag_a.
    apply Z.div_lt_upper_bound; [lia|]. rewrite Ht, E1. lia. }
  eapply hoare_set; try assumption; try reflexivity.
  - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen1. split; [apply splice_limbs; assumption|].
    repeat split; try assumption. unfold top. destruct (t =? 1); lia.
  - eexists. split; [reflexivity|]. split; [exact Hmag'|]. split; [|split].
    + apply norm_of_mag_ge; [exact Hokv'|]. cbn [bn_top]. rewrite Hmag'. unfold top.
      destruct (Z.eqb_spec t 1) as [E1|E1].
      * destruct (Nat.eq_dec (bn_top a - 1) 0) as [E0|E0]; [left; exact E0|right].
        assert (Hb : Bp (bn_top a - 1 - 1) * BW = Bp (bn_top a - 1)).
        { replace (bn_top a - 1)%nat with (S (bn_top a - 1 - 1)) at 2 by lia. rewrite Bp_S. lia. }
        apply Z.div_le_lower_bound; [lia|]. pose proof (Bp_ge1 (bn_top a - 1 - 1)). unfold BW in *. nia.
      * right. apply Z.div_le_lower_bound; [lia|].
        assert (t <> 0).
        { destruct Hnorm as [Hnorm|Hnorm]; [lia|]. exact Hnorm. }
        pose proof (Bp_pos (bn_top a - 1)). nia.
    + cbn [bn_neg]. intros ->. destruct (top =? 0)%nat; reflexivity.
    + cbn [bn_top]. unfold top. destruct (t =? 1); lia.
Qed.

End WordSpec.
