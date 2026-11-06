From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0u YO0x YO10 YO0q YO0d YO03 YO0j YO0m YO0n YO0o YO04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib Require Import AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Lemma znth_lv_add_u L k d j : 0 <= k < Z.of_nat (length L) -> 0 <= j ->
  znth j (lv_add L k d) = if j =? k then znth k L + d else znth j L.
Proof.
  intros Hk Hj. unfold lv_add. rewrite znth_zset by lia.
  destruct (Z.eqb_spec j k) as [->|N]; cbn [andb].
  - replace (k <? Z.of_nat (length L)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - reflexivity.
Qed.

Lemma UPB_step s s3 L n k : UPB s L -> length L = 49%nat -> 0 <= band n < 49 ->
  (forall b, bcount s3 b = bcount s b + (if band n =? b then 1 else 0)) ->
  (forall c, upc s3 c = upc s c + (if (k =? c) && (band n =? c - 1) then 1 else 0)) ->
  (k = band n + 1 -> 1 <= k < 48 -> upc s k <= 12) ->
  UPB s3 (lv_add L (band n) 1).
Proof.
  intros (U1 & U2) HL Hb HB HU HC. split.
  - intros j Hj. rewrite HB, znth_lv_add_u by (rewrite ?HL; lia). pose proof (U1 j Hj) as E.
    destruct (Z.eqb_spec (band n) j) as [->|N]; [rewrite Z.eqb_refl; lia|].
    replace (j =? band n) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - intros c Hc. rewrite HB, HU, znth_lv_add_u by (rewrite ?HL; lia).
    pose proof (U1 c ltac:(lia)) as E1. pose proof (U2 c Hc) as E2.
    destruct ((k =? c) && (band n =? c - 1)) eqn:Q.
    + apply andb_prop in Q as [Q1 Q2]. apply Z.eqb_eq in Q1. apply Z.eqb_eq in Q2. subst k.
      specialize (HC ltac:(lia) Hc).
      replace (band n =? c) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (c =? band n) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota. unfold COARSE in *. lia.
    + destruct (Z.eqb_spec (band n) c) as [e|e];
        [rewrite e, Z.eqb_refl; cbv iota; lia
        |replace (c =? band n) with false by (symmetry; apply Z.eqb_neq; lia); cbv iota; lia].
Qed.
