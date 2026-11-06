(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnWordsCorrect BnKaraCorrect BgWords BgSqrCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnKaraX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sgen3_ok (RES : list Z * list Z) (k' n : nat) (a R T : list Z) : Prop :=
  let '(rh, p2) := sqr_recursive k' (slice a n n) (slice R (2 * n) (2 * n)) (skipn (4 * n) T) in
  kc_ok RES n true (splice R (2 * n) rh) (splice T (4 * n) p2).

Definition sgen2_ok (RES : list Z * list Z) (k' n : nat) (a R T : list Z) : Prop :=
  let '(rl, p1) := sqr_recursive k' (firstn n a) (slice R 0 (2 * n)) (skipn (4 * n) T) in
  sgen3_ok RES k' n a (splice R 0 rl) (splice T (4 * n) p1).

Definition sjoin_ok (RES : list Z * list Z) (k' n : nat) (a R T : list Z) : Prop :=
  let '(tm, p0) := sqr_recursive k' (slice T 0 n) (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
  sgen2_ok RES k' n a R (splice T (2 * n) (tm ++ p0)).

Definition szero_ok (RES : list Z * list Z) (k' n : nat) (a R T : list Z) : Prop :=
  sgen2_ok RES k' n a R (splice T (2 * n) (repeat 0 (2 * n))).

Lemma sgen2_ok_intro : forall k' a r (F tm p0 : list Z),
  let n := Nat.pow 2 k' in
  let a_lo := firstn n a in let a_hi := slice a n n in
  limbs a -> limbs r -> length a = (2 * n)%nat -> length r = (2 * (2 * n))%nat ->
  limbs F -> length F = (2 * n)%nat -> limbs tm -> length tm = (2 * n)%nat -> limbs p0 -> (sqr_scratch k' <= length p0)%nat ->
  - lval tm = (lval a_lo - lval a_hi) * (lval a_hi - lval a_lo) ->
  sgen2_ok (let '(rl, p1) := sqr_recursive k' a_lo (slice r 0 (2 * n)) p0 in
            let '(rh, p2) := sqr_recursive k' a_hi (slice r (2 * n) (2 * n)) p1 in
            kara_combine n true (rl ++ rh) (F ++ tm ++ p2))
           k' n a r (F ++ tm ++ p0).
Proof.
  intros k' a r F tm p0 n a_lo a_hi Ha Hr Hla Hrl HF HFl Htm Html Hp0 Hp0s Hsgn.
  assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
  assert (Hahl : length a_hi = n) by (subst a_hi; apply slice_length; lia).
  assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
  assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound a_hi Hah) as HA1. rewrite Hahl in HA1.
  unfold sgen2_ok. fold a_lo.
  assert (E0 : skipn (4 * n) (F ++ tm ++ p0) = p0).
  { rewrite app_assoc. apply skipn_app_len. rewrite length_app. lia. }
  rewrite E0.
  pose proof (sqr_recursive_spec k' a_lo (slice r 0 (2 * n)) p0 Hal (slice_limbs _ _ _ Hr) Hp0 Hall
                ltac:(rewrite slice_length by lia; fold n; lia) Hp0s) as Hx.
  destruct (sqr_recursive k' a_lo (slice r 0 (2 * n)) p0) as [rl p1].
  destruct Hx as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.
  unfold sgen3_ok. fold a_hi.
  assert (E1 : slice (splice r 0 rl) (2 * n) (2 * n) = slice r (2 * n) (2 * n)) by (apply slice_splice_above; lia).
  assert (E2 : skipn (4 * n) (splice (F ++ tm ++ p0) (4 * n) p1) = p1).
  { rewrite splice_tail by (rewrite !length_app; lia). apply skipn_app_len. rewrite length_firstn, !length_app. lia. }
  rewrite E1, E2.
  pose proof (sqr_recursive_spec k' a_hi (slice r (2 * n) (2 * n)) p1 Hah (slice_limbs _ _ _ Hr) L4 Hahl
                ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
  destruct (sqr_recursive k' a_hi (slice r (2 * n) (2 * n)) p1) as [rh p2].
  destruct Hx as (H1 & H2 & H3 & H4 & H5). rewrite slice_length in H2 by lia.
  assert (ER : splice (splice r 0 rl) (2 * n) rh = rl ++ rh) by (apply two_splices_all; lia).
  assert (ET : splice (splice (F ++ tm ++ p0) (4 * n) p1) (4 * n) p2 = F ++ tm ++ p2).
  { rewrite (splice_tail (F ++ tm ++ p0)) by (rewrite !length_app; lia).
    assert (EF : firstn (4 * n) (F ++ tm ++ p0) = F ++ tm) by (rewrite app_assoc; apply firstn_app_len; rewrite length_app; lia).
    rewrite EF. rewrite splice_tail by (rewrite !length_app; lia).
    rewrite firstn_app_len by (rewrite length_app; lia). rewrite <- app_assoc. reflexivity. }
  rewrite ER, ET.
  assert (S1 : slice (rl ++ rh) 0 (2 * n) = rl).
  { unfold slice. cbn [skipn]. apply firstn_app_len. exact L2. }
  assert (S2 : slice (rl ++ rh) (2 * n) (2 * n) = rh).
  { unfold slice. rewrite skipn_app_len by exact L2. apply firstn_all2. lia. }
  assert (S3 : slice (F ++ tm ++ p2) (2 * n) (2 * n) = tm).
  { unfold slice. rewrite skipn_app_len by exact HFl. apply firstn_app_len. exact Html. }
  apply (kc_ok_finish n true (rl ++ rh) (F ++ tm ++ p2) (lval a_lo) (lval a_hi) (lval a_lo) (lval a_hi)); try assumption.
  - apply limbs_app; assumption.
  - rewrite length_app. lia.
  - apply limbs_app; [exact HF | apply limbs_app; assumption].
  - rewrite !length_app. lia.
  - rewrite S1. exact L3.
  - rewrite S2. exact H3.
  - rewrite S3. exact Hsgn.
Qed.

Lemma srec_staged : forall k' a R T,
  limbs a -> limbs R -> limbs T ->
  length a = Nat.pow 2 (S k') -> length R = (2 * Nat.pow 2 (S k'))%nat -> (sqr_scratch (S k') <= length T)%nat ->
  (16 <= Nat.pow 2 (S k'))%nat ->
  let n := Nat.pow 2 k' in
  let c1 := cmp_words (firstn n a) (slice a n n) in
  if 0 <? c1 then sjoin_ok (sqr_recursive (S k') a R T) k' n a R (splice T 0 (fst (sub_words (firstn n a) (slice a n n))))
  else if c1 <? 0 then sjoin_ok (sqr_recursive (S k') a R T) k' n a R (splice T 0 (fst (sub_words (slice a n n) (firstn n a))))
  else szero_ok (sqr_recursive (S k') a R T) k' n a R T.
Proof.
  intros k' a r t Ha Hr Ht Hla Hrl Hsc Hbig n.
  pose proof (pow2_pos k') as Hp. assert (Epow : Nat.pow 2 (S k') = (2 * n)%nat) by (subst n; cbn [Nat.pow]; lia).
  assert (Hn8 : (8 <= n)%nat) by lia.
  cbn [sqr_scratch] in Hsc. rewrite Epow in Hla, Hrl, Hsc.
  pose proof (sqr_scratch_ge k') as Hsg. fold n in Hsg.
  set (a_lo := firstn n a). set (a_hi := slice a n n).

  assert (EM : sqr_recursive (S k') a r t =
    (let c1 := cmp_words a_lo a_hi in
     let td := if 0 <? c1 then splice t 0 (fst (sub_words a_lo a_hi))
               else if c1 <? 0 then splice t 0 (fst (sub_words a_hi a_lo)) else t in
     let p := skipn (2 * (2 * n)) td in
     let '(tm, p0) := if c1 =? 0 then (repeat 0 (2 * n), p) else sqr_recursive k' (slice td 0 n) (slice td (2 * n) (2 * n)) p in
     let '(rl, p1) := sqr_recursive k' a_lo (slice r 0 (2 * n)) p0 in
     let '(rh, p2) := sqr_recursive k' a_hi (slice r (2 * n) (2 * n)) p1 in
     kara_combine n true (rl ++ rh) (firstn (2 * n) td ++ tm ++ p2))).
  { cbn [sqr_recursive]. fold n. rewrite Epow.
    destruct (Nat.eqb_spec (2 * n) 4) as [E|_]; [lia|]. destruct (Nat.eqb_spec (2 * n) 8) as [E|_]; [lia|].
    destruct (Nat.ltb_spec (2 * n) 16) as [E|_]; [lia|]. reflexivity. }
  assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
  assert (Hahl : length a_hi = n) by (subst a_hi; apply slice_length; lia).
  assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
  assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound a_hi Hah) as HA1. rewrite Hahl in HA1.
  rewrite EM. clear EM. cbv zeta.
  rewrite (cmp_words_spec a_lo a_hi Hal Hah ltac:(lia)).
  pose proof (Bp_pos n) as HBn.
  destruct (Z.ltb_spec 0 (sgn3 (lval a_lo) (lval a_hi))) as [Hs|Hs];
    [|destruct (Z.ltb_spec (sgn3 (lval a_lo) (lval a_hi)) 0) as [Hs2|Hs2]].
  -
    assert (Hgt : lval a_hi < lval a_lo).
    { apply sgn3_pos_iff. destruct (sgn3_range (lval a_lo) (lval a_hi)) as [Eq|[Eq|Eq]]; lia. }
    destruct (Z.eqb_spec (sgn3 (lval a_lo) (lval a_hi)) 0) as [E0|_]; [lia|].
    pose proof (sub_words_spec a_lo a_hi Hal Hah ltac:(lia)) as Hsw. destruct (sub_words a_lo a_hi) as [d bw]. cbn [fst].
    destruct Hsw as (W1 & W2 & W3 & W4). rewrite Hall in W2, W4.
    pose proof (lval_bound d W1) as Hdb. rewrite W2 in Hdb.
    assert (Ebw : bw = 0) by nia. subst bw. assert (Ed : lval d = lval a_lo - lval a_hi) by lia.
    set (td := splice t 0 d).
    assert (Htdl : limbs td) by (subst td; apply splice_limbs; assumption).
    assert (Htdlen : length td = length t) by (subst td; apply splice_length; lia).
    assert (E0 : slice td 0 n = d) by (subst td; rewrite <- W2; apply slice_splice_same; lia).
    unfold sjoin_ok. replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
    pose proof (sqr_recursive_spec k' (slice td 0 n) (slice td (2 * n) (2 * n)) (skipn (4 * n) td)
                  ltac:(rewrite E0; exact W1) (slice_limbs _ _ _ Htdl) (limbs_skipn _ _ Htdl)
                  ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                  ltac:(rewrite length_skipn; lia)) as Hx.
    destruct (sqr_recursive k' (slice td 0 n) (slice td (2 * n) (2 * n)) (skipn (4 * n) td)) as [tm p0].
    destruct Hx as (X1 & X2 & X3 & X4 & X5). rewrite slice_length in X2 by lia. rewrite length_skipn in X5.
    rewrite splice_tail by (rewrite length_app; lia).
    apply sgen2_ok_intro; try assumption; try lia.
    + apply limbs_firstn. exact Htdl.
    + apply firstn_length_le. lia.
    + rewrite X3, E0, Ed. fold n. fold a_lo a_hi. ring.
  -
    assert (Hlt' : lval a_lo < lval a_hi).
    { apply sgn3_neg_iff. destruct (sgn3_range (lval a_lo) (lval a_hi)) as [Eq|[Eq|Eq]]; lia. }
    destruct (Z.eqb_spec (sgn3 (lval a_lo) (lval a_hi)) 0) as [E0|_]; [lia|].
    pose proof (sub_words_spec a_hi a_lo Hah Hal ltac:(lia)) as Hsw. destruct (sub_words a_hi a_lo) as [d bw]. cbn [fst].
    destruct Hsw as (W1 & W2 & W3 & W4). rewrite Hahl in W2, W4.
    pose proof (lval_bound d W1) as Hdb. rewrite W2 in Hdb.
    assert (Ebw : bw = 0) by nia. subst bw. assert (Ed : lval d = lval a_hi - lval a_lo) by lia.
    set (td := splice t 0 d).
    assert (Htdl : limbs td) by (subst td; apply splice_limbs; assumption).
    assert (Htdlen : length td = length t) by (subst td; apply splice_length; lia).
    assert (E0' : slice td 0 n = d) by (subst td; rewrite <- W2; apply slice_splice_same; lia).
    unfold sjoin_ok. replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
    pose proof (sqr_recursive_spec k' (slice td 0 n) (slice td (2 * n) (2 * n)) (skipn (4 * n) td)
                  ltac:(rewrite E0'; exact W1) (slice_limbs _ _ _ Htdl) (limbs_skipn _ _ Htdl)
                  ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                  ltac:(rewrite length_skipn; lia)) as Hx.
    destruct (sqr_recursive k' (slice td 0 n) (slice td (2 * n) (2 * n)) (skipn (4 * n) td)) as [tm p0].
    destruct Hx as (X1 & X2 & X3 & X4 & X5). rewrite slice_length in X2 by lia. rewrite length_skipn in X5.
    rewrite splice_tail by (rewrite length_app; lia).
    apply sgen2_ok_intro; try assumption; try lia.
    + apply limbs_firstn. exact Htdl.
    + apply firstn_length_le. lia.
    + rewrite X3, E0', Ed. fold n. fold a_lo a_hi. ring.
  -
    assert (Ez : sgn3 (lval a_lo) (lval a_hi) = 0) by lia. rewrite Ez. cbn [Z.eqb].
    apply (proj1 (sgn3_0_iff _ _)) in Ez.
    unfold szero_ok. replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
    assert (ES : splice t (2 * n) (repeat 0 (2 * n)) = firstn (2 * n) t ++ repeat 0 (2 * n) ++ skipn (4 * n) t).
    { unfold splice. rewrite repeat_length. replace (2 * n + 2 * n)%nat with (4 * n)%nat by lia. reflexivity. }
    rewrite ES.
    apply sgen2_ok_intro; try assumption; try lia.
    + apply limbs_firstn. exact Ht.
    + apply firstn_length_le. lia.
    + apply limbs_repeat. exact limb_0.
    + apply repeat_length.
    + apply limbs_skipn. exact Ht.
    + rewrite length_skipn. lia.
    + rewrite lval_repeat0. fold n. fold a_lo a_hi. rewrite Ez. ring.
Qed.

Lemma sqr_recursive_c4 : forall k a r t, Nat.pow 2 k = 4%nat ->
  sqr_recursive k a r t = (splice r 0 (sqr_comba4 (firstn 4 a)), t).
Proof. intros k a r t E. destruct k as [|k0]; cbn [sqr_recursive]; rewrite E; reflexivity. Qed.

Lemma sqr_recursive_c8 : forall k a r t, Nat.pow 2 k = 8%nat ->
  sqr_recursive k a r t = (splice r 0 (sqr_comba8 (firstn 8 a)), t).
Proof. intros k a r t E. destruct k as [|k0]; cbn [sqr_recursive]; rewrite E; reflexivity. Qed.

Lemma sqr_recursive_small : forall k a r t, (Nat.pow 2 k < 16)%nat -> Nat.pow 2 k <> 4%nat -> Nat.pow 2 k <> 8%nat ->
  sqr_recursive k a r t =
  (let n2 := Nat.pow 2 k in
   let '(ro, tmp) := sqr_normal (firstn n2 a) (firstn (2 * n2) r) in (splice r 0 ro, splice t 0 tmp)).
Proof.
  intros k a r t Hs H4 H8. apply Nat.ltb_lt in Hs. apply Nat.eqb_neq in H4. apply Nat.eqb_neq in H8.
  destruct k as [|k0]; cbn [sqr_recursive]; rewrite ?H4, ?H8, ?Hs; reflexivity.
Qed.
