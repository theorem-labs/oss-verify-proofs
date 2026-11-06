(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs BnSpecs2 BnAddSpec BnMulSpec.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgState BgWords BgLib BgInv BgSpecs BgLibSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section AddSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma hoare_bind_update : forall {B} r (g : BN -> BN) (f : unit -> BM B) F s Q,
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok (g (getbn r s)) ->
  bn_d (g (getbn r s)) = bn_d (getbn r s) -> length (bn_buf (g (getbn r s))) = length (bn_buf (getbn r s)) ->
  bn_flags (g (getbn r s)) = bn_flags (getbn r s) ->
  hoare F (setbn r (g (getbn r s)) s) (f tt) Q ->
  hoare F s (bbind ops (bbind ops (bget ops r) (fun b => bset ops r (g b))) f) Q.
Proof.
  intros B r g f F s Q Hr Hn Hok Ed El Ef H.
  eapply hoare_bind with (R := fun _ s' => s' = setbn r (g (getbn r s)) s).
  - apply hoare_bind_get. eapply hoare_set; try assumption. reflexivity.
  - intros [] s' _ ->. exact H.
Qed.

Lemma hoare_update : forall r (g : BN -> BN) F s (Q : unit -> ST -> Prop),
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok (g (getbn r s)) ->
  bn_d (g (getbn r s)) = bn_d (getbn r s) -> length (bn_buf (g (getbn r s))) = length (bn_buf (getbn r s)) ->
  Q tt (setbn r (g (getbn r s)) s) -> bn_flags (g (getbn r s)) = bn_flags (getbn r s) ->
  hoare F s (bbind ops (bget ops r) (fun b => bset ops r (g b))) Q.
Proof. intros r g F s Q Hr Hn Hok Ed El H Ef. apply hoare_bind_get. eapply hoare_set; try assumption. Qed.

Lemma fetch_after : forall rr rx (s : ST) words r1 r1', st_wf s ->
  (rr < length (st_bns s))%nat -> rr <> ROne ->
  gexpanded (getbn rr s) words r1 -> bn_buf r1' = bn_buf r1 ->
  firstn (bn_top (getbn rx s)) (bn_buf (getbn rx (setbn rr r1' s))) = firstn (bn_top (getbn rx s)) (bn_buf (getbn rx s)).
Proof.
  intros rr rx s words r1 r1' Hs Hr Hn Hexp Ebuf. destruct (Nat.eq_dec rr rx) as [->|Hne].
  - rewrite getbn_setbn_same by assumption. rewrite Ebuf. eapply gexpanded_prefix; [apply st_wf_ok; assumption|exact Hexp].
  - rewrite getbn_setbn_other by exact Hne. reflexivity.
Qed.

Lemma okv_mag_ge : forall c : BN, bg_okv c -> bn_norm c -> (0 < bn_top c)%nat -> Bp (bn_top c - 1) <= bn_mag c.
Proof.
  intros c (C1 & C2) [Hc|Hc] Hpos; [lia|]. unfold bn_mag.
  set (l := firstn (bn_top c) (bn_buf c)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact C1).
  assert (Hll : length l = bn_top c) by (apply firstn_length_le; exact C2).
  pose proof (nth_limb_val l (bn_top c - 1) Hl ltac:(lia)) as En.
  assert (Enn : nth (bn_top c - 1) l 0 = nth (bn_top c - 1) (bn_buf c) 0).
  { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top c - 1) (bn_top c)); [reflexivity|lia]. }
  rewrite Enn in En. pose proof (limbs_nth (bn_buf c) (bn_top c - 1) C1) as [Hx0 _].
  pose proof (lval_nonneg _ (limbs_firstn (bn_top c - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (bn_top c - 1)) l Hl)).
  pose proof (Bp_pos (bn_top c - 1)). pose proof (Bp_pos (S (bn_top c - 1))). nia.
Qed.

Lemma norm_top_le : forall a b : BN, bg_okv a -> bg_okv b -> bn_norm b -> bn_mag b <= bn_mag a -> (bn_top b <= bn_top a)%nat.
Proof.
  intros a b Ha Hb Hnb Hm. destruct (Nat.le_gt_cases (bn_top b) (bn_top a)) as [|Hgt]; [assumption|exfalso].
  pose proof (okv_mag_lt a Ha). pose proof (okv_mag_ge b Hb Hnb ltac:(lia)).
  pose proof (Bp_mono (bn_top a) (bn_top b - 1) ltac:(lia)). lia.
Qed.

Lemma norm_zero_iff : forall b : BN, bg_okv b -> bn_norm b -> (bn_top b = 0%nat <-> bn_mag b = 0).
Proof.
  intros b Hb Hn. split.
  - intros E. apply bn_mag_top0. exact E.
  - intros E. destruct (Nat.eq_dec (bn_top b) 0) as [|Hne]; [assumption|exfalso].
    pose proof (okv_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_pos (bn_top b - 1)). lia.
Qed.

Definition uadd_body (rr ra rb : bnref) : BM (M:=btree ptr) (ptr:=ptr) unit :=
  bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b =>
  let max := bn_top a in let min := bn_top b in
  bbind ops (bn_wexpand ops rr (max + 1)) (fun _ =>
  bbind ops (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_top r max))) (fun _ =>
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
                  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false))))))).

Lemma BN_uadd_unfold : forall rr ra rb (s : ST),
  BN_uadd ops rr ra rb s =
  (if (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat then uadd_body rr rb ra s else uadd_body rr ra rb s).
Proof.
  intros rr ra rb s. unfold BN_uadd, bbind at 1 2. cbn [bind tree_ops bget tbind ret fst snd].
  destruct (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat; reflexivity.
Qed.

Definition uadd_post (a b : BN) (r' : BN) : Prop :=
  bn_norm r' /\ bn_mag r' = bn_mag a + bn_mag b /\ bn_neg r' = false /\ (bn_top r' <= Nat.max (bn_top a) (bn_top b) + 1)%nat.

Lemma uadd_body_spec : forall rr ra rb F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  (bn_top (getbn rb s) <= bn_top (getbn ra s))%nat -> bn_norm (getbn ra s) ->
  Z.of_nat (bn_top (getbn ra s)) + 1 <= BG_DMAX ->
  hoare F s (uadd_body rr ra rb) (upd1 rr s (uadd_post (getbn ra s) (getbn rb s))).
Proof.
  intros rr ra rb F s Hr Hn Hva Hvb Htops Hna Hsz. apply hoare_wf. intros Hs. unfold uadd_body.
  apply hoare_bind_get. apply hoare_bind_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *. set (max := bn_top a) in *. set (min := bn_top b) in *.
  pose proof (st_wf_okv ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_wf_okv rb s Hs Hvb) as Hb. fold b in Hb.
  eapply hoare_bind; [apply bn_wexpand_spec; [exact Hr|exact Hn|lia]|].
  intros [] s1 Hs1 (r1 & -> & Hexp). pose proof Hexp as (E1 & E2 & E3 & E4 & Hr1 & E5 & E6).
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
  assert (Hr1t : bg_ok (bn_with_top r1 max)).
  { unfold bg_ok, bn_dmax, bn_with_top. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
  apply hoare_bind_update; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
  rewrite setbn_setbn_same. set (s2 := setbn rr (bn_with_top r1 max) s) in *.
  assert (Hl2 : length (st_bns s2) = length (st_bns s)) by (subst s2; apply length_setbn).
  assert (Egr2 : getbn rr s2 = bn_with_top r1 max) by (subst s2; apply getbn_setbn_same; assumption).

  assert (Htail : forall r3, bg_ok r3 -> uadd_post a b (bn_with_neg r3 false) -> length (bn_buf r3) = length (bn_buf r1) ->
            bn_d r3 = bn_d r1 ->
            hoare F (setbn rr r3 s) (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false))) (upd1 rr s (uadd_post a b))).
  { intros r3 Hr3 Hp3 Hl3 Hd3.
    apply hoare_update; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    rewrite setbn_setbn_same. eexists. split; [reflexivity|exact Hp3]. }
  eapply hoare_bind with (R := fun _ s' => exists r3, s' = setbn rr r3 s /\ bg_ok r3 /\ uadd_post a b (bn_with_neg r3 false) /\
                                            length (bn_buf r3) = length (bn_buf r1) /\ bn_d r3 = bn_d r1).
  2:{ intros [] s3 _ (r3 & -> & K1 & K2 & K3 & K4). apply Htail; assumption. }
  destruct (Nat.eqb_spec max 0) as [Emax|Nmax].
  - apply hoare_ret. exists (bn_with_top r1 max). split; [reflexivity|]. split; [exact Hr1t|]. split; [|split; reflexivity].
    assert (Ma : bn_mag a = 0) by (apply bn_mag_top0; fold max; exact Emax).
    assert (Mb : bn_mag b = 0) by (apply bn_mag_top0; fold min; lia).
    unfold uadd_post. rewrite Ma, Mb. unfold bn_norm, bn_mag. cbn [bn_with_neg bn_with_top bn_top bn_buf bn_neg]. rewrite Emax. cbn [firstn lval].
    repeat split; auto. lia.
  - apply hoare_bind_get. apply hoare_bind_get. apply hoare_bind_get. rewrite Egr2.
    set (a2 := getbn ra s2). set (b2 := getbn rb s2).
    set (la := firstn max (bn_buf a)). set (lb := firstn min (bn_buf b)).
    assert (Ela : firstn max (bn_buf a2) = la) by (subst a2 s2 la max a; eapply fetch_after; eauto).
    assert (Elb : firstn min (bn_buf b2) = lb) by (subst b2 s2 lb min b; eapply fetch_after; eauto).
    destruct Ha as (A1 & A2). destruct Hb as (B1 & B2). unfold bn_dmax in *.
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1). assert (Hlb : limbs lb) by (apply limbs_firstn; exact B1).
    assert (Hlal : length la = max) by (apply firstn_length_le; lia). assert (Hlbl : length lb = min) by (apply firstn_length_le; lia).
    rewrite (firstn_of_firstn (bn_buf a2) min max) by lia. rewrite (slice_of_firstn (bn_buf a2) min max) by lia. rewrite Ela, Elb.
    pose proof (uadd_pure la lb Hla Hlb ltac:(lia)) as Hp. cbv zeta in Hp. rewrite Hlbl in Hp.
    destruct (add_words (firstn min la) lb) as [sv c1]. destruct (add_carry_words (skipn min la) c1) as [sv2 c2].
    destruct Hp as (W1 & W2 & W3 & W4 & W5). rewrite Hlal in W2, W5.
    set (w := sv ++ sv2 ++ [c2]) in *.
    set (r3 := mkBN (bn_d (bn_with_top r1 max)) (splice (bn_buf (bn_with_top r1 max)) 0 w) (max + Z.to_nat c2)
                    (bn_neg (bn_with_top r1 max)) (bn_flags (bn_with_top r1 max))).
    cbn [bn_with_top bn_buf bn_d bn_neg bn_flags] in r3.
    assert (L3 : length (bn_buf r3) = length (bn_buf r1)) by (subst r3; cbn [bn_buf]; apply splice_length; lia).
    assert (Hfw : firstn (max + 1) (bn_buf r3) = w) by (subst r3; cbn [bn_buf]; apply firstn_splice_0; lia).
    assert (Hr3 : bg_ok r3).
    { unfold bg_ok, bn_dmax. rewrite L3. subst r3. cbn [bn_buf bn_top bn_flags].
      split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia. }
    assert (Hmag3 : bn_mag r3 = bn_mag a + bn_mag b).
    { unfold bn_mag at 1. change (bn_top r3) with (max + Z.to_nat c2)%nat. fold la lb in W4, W5.
      change (bn_mag a) with (lval la). change (bn_mag b) with (lval lb).
      assert (c2 = 0 \/ c2 = 1) as [E|E] by lia; rewrite E in *; cbn [Z.to_nat].
      - rewrite Nat.add_0_r. rewrite (firstn_of_firstn (bn_buf r3) max (max + 1)) by lia. rewrite Hfw. lia.
      - change (Pos.to_nat 1) with 1%nat. rewrite Hfw. exact W4. }
    assert (Hn3 : bn_norm r3).
    { right. change (bn_top r3) with (max + Z.to_nat c2)%nat.
      assert (Hnth : forall i, (i < max + 1)%nat -> nth i (bn_buf r3) 0 = nth i w 0).
      { intros i Hi. rewrite <- Hfw. rewrite nth_firstn. destruct (Nat.ltb_spec i (max + 1)); [reflexivity|lia]. }
      assert (c2 = 0 \/ c2 = 1) as [E|E] by lia; rewrite E in *; cbn [Z.to_nat].
      - rewrite Nat.add_0_r, Hnth by lia.
        assert (En : nth (max - 1) w 0 = nth (max - 1) (firstn max w) 0).
        { rewrite nth_firstn. destruct (Nat.ltb_spec (max - 1) max); [reflexivity|lia]. }
        rewrite En. apply top_limb_nonzero; [apply limbs_firstn; exact W1|apply firstn_length_le; lia|lia|].
        pose proof (okv_mag_ge a (conj A1 A2) Hna ltac:(fold max; lia)) as Hge. fold max in Hge.
        change (bn_mag a) with (lval la) in Hge. pose proof (lval_nonneg lb Hlb). lia.
      - change (Pos.to_nat 1) with 1%nat. replace (max + 1 - 1)%nat with max by lia. rewrite Hnth by lia.
        assert (Hl12 : length (sv ++ sv2) = max).
        { subst w. rewrite app_assoc, length_app in W2. cbn [length] in W2. lia. }
        subst w. rewrite app_assoc, app_nth2 by lia. rewrite Hl12, Nat.sub_diag. cbn [nth]. lia. }
    eapply hoare_set; try rewrite Hl2; try rewrite Egr2; try assumption; try reflexivity.
    subst s2. rewrite setbn_setbn_same. exists r3. split; [reflexivity|]. split; [exact Hr3|]. split; [|split; [exact L3|reflexivity]].
    unfold uadd_post. split; [exact Hn3|]. split; [exact Hmag3|]. split; [reflexivity|].
    change (bn_top (bn_with_neg r3 false)) with (max + Z.to_nat c2)%nat. fold max min.
    assert (c2 = 0 \/ c2 = 1) as [E|E] by lia; rewrite E; cbn; lia.
Qed.

Lemma BN_uadd_spec : forall rr ra rb F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  bn_norm (getbn ra s) -> bn_norm (getbn rb s) ->
  Z.of_nat (Nat.max (bn_top (getbn ra s)) (bn_top (getbn rb s))) + 1 <= BG_DMAX ->
  hoare F s (BN_uadd ops rr ra rb) (upd1 rr s (uadd_post (getbn ra s) (getbn rb s))).
Proof.
  intros rr ra rb F s Hr Hn Hva Hvb Hna Hnb Hsz.
  assert (H : hoare F s (if (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat then uadd_body rr rb ra else uadd_body rr ra rb)
                    (upd1 rr s (uadd_post (getbn ra s) (getbn rb s)))).
  { destruct (Nat.ltb_spec (bn_top (getbn ra s)) (bn_top (getbn rb s))) as [Hlt|Hge].
    - eapply hoare_mono; [apply uadd_body_spec; try assumption; lia|].
      intros [] s' _ (r' & -> & P1 & P2 & P3 & P4). exists r'. split; [reflexivity|]. unfold uadd_post. repeat split; try assumption; lia.
    - apply uadd_body_spec; try assumption; lia. }
  intros X Hs Hfl Ho. specialize (H X Hs Hfl Ho). rewrite BN_uadd_unfold.
  destruct (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat; exact H.
Qed.

Definition usub_post (a b : BN) (r' : BN) : Prop :=
  bn_norm r' /\ bn_mag r' = bn_mag a - bn_mag b /\ bn_neg r' = false /\ (bn_top r' <= bn_top a)%nat.

Lemma BN_usub_spec : forall rr ra rb F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  bn_norm (getbn rb s) -> bn_mag (getbn rb s) <= bn_mag (getbn ra s) ->
  hoare F s (BN_usub ops rr ra rb) (upd1 rr s (usub_post (getbn ra s) (getbn rb s))).
Proof.
  intros rr ra rb F s Hr Hn Hva Hvb Hnb Hmags. apply hoare_wf. intros Hs. unfold BN_usub.
  apply hoare_bind_get. apply hoare_bind_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *. set (max := bn_top a) in *. set (min := bn_top b) in *.
  pose proof (st_wf_okv ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_wf_okv rb s Hs Hvb) as Hb. fold b in Hb.
  pose proof (norm_top_le a b Ha Hb Hnb Hmags) as Htops. fold max min in Htops.
  destruct (Nat.ltb_spec max min) as [|_]; [lia|].
  destruct Ha as (A1 & A2). destruct Hb as (B1 & B2). unfold bn_dmax in *.
  eapply hoare_bind; [apply bn_wexpand_spec; [exact Hr|exact Hn|pose proof (st_wf_top_le ra s Hs Hva); fold a max in H; lia]|].
  intros [] s1 Hs1 (r1 & -> & Hexp). pose proof Hexp as (E1 & E2 & E3 & E4 & Hr1 & E5 & E6).
  set (s1 := setbn rr r1 s) in *.
  assert (Hl1 : length (st_bns s1) = length (st_bns s)) by (subst s1; apply length_setbn).
  assert (Egr1 : getbn rr s1 = r1) by (subst s1; apply getbn_setbn_same; assumption).
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.

  assert (Htail : forall r2, limbs (bn_buf r2) -> length (bn_buf r2) = length (bn_buf r1) -> bn_d r2 = bn_d r1 -> bn_flags r2 = bn_flags r1 ->
            lval (firstn max (bn_buf r2)) = bn_mag a - bn_mag b ->
            hoare F (setbn rr r2 s) (bbind ops (bget ops rr) (fun r => bset ops rr (mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r))))
                  (upd1 rr s (usub_post a b))).
  { intros r2 L1 L2 L3 L4 L5.
    destruct (strip_top_spec (bn_buf r2) max ltac:(lia)) as (S1 & S2 & S3).
    apply (hoare_update rr (fun r => mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r)));
      try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite L2, L4. repeat split; try assumption; lia.
    - rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold usub_post, bn_norm, bn_mag. cbn [bn_buf bn_top bn_neg].
      rewrite S2. fold max. repeat split; try assumption. }
  eapply hoare_bind with (R := fun _ s' => exists r2, s' = setbn rr r2 s /\ limbs (bn_buf r2) /\ length (bn_buf r2) = length (bn_buf r1) /\
                                            bn_d r2 = bn_d r1 /\ bn_flags r2 = bn_flags r1 /\ lval (firstn max (bn_buf r2)) = bn_mag a - bn_mag b).
  2:{ intros [] s3 _ (r2 & -> & K1 & K2 & K3 & K4 & K5). apply Htail; assumption. }
  destruct (Nat.eqb_spec max 0) as [Emax|Nmax].
  - apply hoare_ret. exists r1. split; [reflexivity|]. repeat split; try assumption.
    rewrite Emax. cbn [firstn lval]. rewrite (bn_mag_top0 a) by (fold max; exact Emax). rewrite (bn_mag_top0 b) by (fold min; lia). reflexivity.
  - apply hoare_bind_get. apply hoare_bind_get. apply hoare_bind_get. rewrite Egr1.
    set (a2 := getbn ra s1). set (b2 := getbn rb s1).
    set (la := firstn max (bn_buf a)). set (lb := firstn min (bn_buf b)).
    assert (Ela : firstn max (bn_buf a2) = la) by (subst a2 s1 la max a; eapply fetch_after; eauto).
    assert (Elb : firstn min (bn_buf b2) = lb) by (subst b2 s1 lb min b; eapply fetch_after; eauto).
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1). assert (Hlb : limbs lb) by (apply limbs_firstn; exact B1).
    assert (Hlal : length la = max) by (apply firstn_length_le; lia). assert (Hlbl : length lb = min) by (apply firstn_length_le; lia).
    rewrite (firstn_of_firstn (bn_buf a2) min max) by lia. rewrite (slice_of_firstn (bn_buf a2) min max) by lia. rewrite Ela, Elb.
    pose proof (usub_pure la lb Hla Hlb ltac:(lia) Hmags) as Hp. cbv zeta in Hp. rewrite Hlbl in Hp.
    destruct (sub_words (firstn min la) lb) as [sv bw]. destruct (sub_part_pos (skipn min la) bw) as [sv2 c2].
    destruct Hp as (W1 & W2 & W3). rewrite Hlal in W2.
    set (r2 := bn_with_buf r1 (splice (bn_buf r1) 0 (sv ++ sv2))).
    assert (L2 : length (bn_buf r2) = length (bn_buf r1)) by (subst r2; cbn [bn_with_buf bn_buf]; apply splice_length; lia).
    assert (Hr2 : bg_ok r2).
    { unfold bg_ok, bn_dmax. rewrite L2. subst r2. cbn [bn_with_buf bn_buf bn_top bn_flags].
      split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia. }
    eapply hoare_set; try rewrite Hl1; try rewrite Egr1; try assumption; try reflexivity.
    subst s1. rewrite setbn_setbn_same. exists r2. split; [reflexivity|]. split; [destruct Hr2 as (H & _); exact H|].
    split; [exact L2|]. split; [reflexivity|]. split; [reflexivity|].
    subst r2. cbn [bn_with_buf bn_buf]. rewrite firstn_splice_0 by lia. exact W3.
Qed.

Definition signed_post (v : Z) (mx : nat) (r' : BN) : Prop :=
  bn_canon r' /\ bn_val r' = v /\ (bn_top r' <= mx + 1)%nat.

Lemma set_neg_spec : forall rr neg F s (P : BN -> Prop),
  (rr < length (st_bns s))%nat -> rr <> ROne -> P (bn_with_neg (getbn rr s) neg) ->
  hoare F s (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r neg))) (upd1 rr s P).
Proof.
  intros rr neg F s P Hr Hn HP. apply hoare_wf. intros Hs.
  apply hoare_update; try assumption; try reflexivity.
  - destruct (st_wf_ok rr s Hs Hr Hn) as (A1 & A2 & A3 & A4). unfold bg_ok, bn_dmax, bn_with_neg in *. cbn [bn_buf bn_top bn_flags]. tauto.
  - eexists. split; [reflexivity|exact HP].
Qed.

Lemma bn_val_with_neg : forall (b : BN) neg, bn_val (bn_with_neg b neg) = if neg then - bn_mag b else bn_mag b.
Proof. intros b neg. reflexivity. Qed.

Lemma BN_add_spec : forall rr ra rb F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  bn_canon (getbn ra s) -> bn_canon (getbn rb s) ->
  Z.of_nat (Nat.max (bn_top (getbn ra s)) (bn_top (getbn rb s))) + 1 <= BG_DMAX ->
  hoare F s (BN_add ops rr ra rb)
        (upd1 rr s (signed_post (bn_val (getbn ra s) + bn_val (getbn rb s)) (Nat.max (bn_top (getbn ra s)) (bn_top (getbn rb s))))).
Proof.
  intros rr ra rb F s Hr Hn Hva Hvb [Hna Hza] [Hnb Hzb] Hsz. apply hoare_wf. intros Hs. unfold BN_add.
  apply hoare_bind_get. apply hoare_bind_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *.
  pose proof (st_wf_okv ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_wf_okv rb s Hs Hvb) as Hb. fold b in Hb.
  pose proof (okv_mag_nonneg a Ha) as Ma. pose proof (okv_mag_nonneg b Hb) as Mb.
  pose proof (norm_zero_iff a Ha Hna) as Za. pose proof (norm_zero_iff b Hb Hnb) as Zb.
  set (mx := Nat.max (bn_top a) (bn_top b)) in *.

  eapply hoare_bind with (R := fun (r_neg : bool) (s' : ST) => exists r' : BN, s' = setbn rr r' s /\ bn_norm r' /\ (bn_top r' <= mx + 1)%nat /\
            (if r_neg then - bn_mag r' else bn_mag r') = bn_val a + bn_val b /\ (bn_mag r' = 0 -> r_neg = false)).
  2:{ intros r_neg s1 Hs1 (r1 & -> & N1 & N2 & N3 & N4).
      eapply hoare_mono; [apply (set_neg_spec rr r_neg F _ (fun x => x = bn_with_neg r1 r_neg)); [rewrite length_setbn; exact Hr|exact Hn|
                                 rewrite getbn_setbn_same by exact Hr; reflexivity]|].
      intros [] s2 _ (r2 & -> & ->). rewrite setbn_setbn_same. eexists. split; [reflexivity|].
      pose proof (st_wf_okv rr _ Hs1 ltac:(rewrite length_setbn; exact Hr)) as Hok1. rewrite getbn_setbn_same in Hok1 by exact Hr.
      unfold signed_post, bn_canon. rewrite bn_val_with_neg. split; [split; [exact N1|]|split; [exact N3|exact N2]].
      cbn [bn_with_neg bn_top bn_neg]. intros Et. apply N4. apply (bn_mag_top0 r1 Et). }
  unfold bn_val. destruct (Bool.eqb (bn_neg a) (bn_neg b)) eqn:Esgn.
  - apply eqb_prop in Esgn.
    eapply hoare_bind; [apply BN_uadd_spec; assumption|].
    intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. fold mx in P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|]. split; [exact P4|].
    rewrite P2, <- Esgn. split; [destruct (bn_neg a); lia|].
    intros Hz. assert (Hma0 : bn_mag a = 0) by lia. apply Hza. apply Za. exact Hma0.
  - apply eqb_false_iff in Esgn.
    eapply hoare_bind; [apply BN_ucmp_spec; assumption|]. intros c s1 _ [-> ->]. fold a b.
    destruct (ucmp_okv_spec a b Ha Hb Hna Hnb) as (U1 & U2 & U3).
    destruct (Z.ltb_spec 0 (ucmp_pure a b)) as [Hc|Hc].
    + specialize (U1 Hc).
      eapply hoare_bind; [apply BN_usub_spec; try assumption; fold a b; lia|].
      intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|].
      split; [unfold mx; lia|]. rewrite P2. split; [destruct (bn_neg a), (bn_neg b); try congruence; lia|lia].
    + destruct (Z.ltb_spec (ucmp_pure a b) 0) as [Hc'|Hc'].
      * specialize (U2 Hc').
        eapply hoare_bind; [apply BN_usub_spec; try assumption; fold a b; lia|].
        intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|].
        split; [unfold mx; lia|]. rewrite P2. split; [destruct (bn_neg a), (bn_neg b); try congruence; lia|lia].
      * assert (Ec : ucmp_pure a b = 0) by lia. specialize (U3 Ec).
        eapply hoare_bind; [apply BN_zero_spec; assumption|].
        intros [] s1 _ (r1 & -> & T1 & T2). apply hoare_ret. exists r1. split; [reflexivity|]. split; [left; exact T1|].
        split; [lia|]. rewrite (bn_mag_top0 r1 T1). split; [destruct (bn_neg a), (bn_neg b); try congruence; lia|reflexivity].
Qed.

Lemma BN_sub_spec : forall rr ra rb F s,
  (rr < length (st_bns s))%nat -> rr <> ROne -> (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  bn_canon (getbn ra s) -> bn_canon (getbn rb s) ->
  Z.of_nat (Nat.max (bn_top (getbn ra s)) (bn_top (getbn rb s))) + 1 <= BG_DMAX ->
  hoare F s (BN_sub ops rr ra rb)
        (upd1 rr s (signed_post (bn_val (getbn ra s) - bn_val (getbn rb s)) (Nat.max (bn_top (getbn ra s)) (bn_top (getbn rb s))))).
Proof.
  intros rr ra rb F s Hr Hn Hva Hvb [Hna Hza] [Hnb Hzb] Hsz. apply hoare_wf. intros Hs. unfold BN_sub.
  apply hoare_bind_get. apply hoare_bind_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *.
  pose proof (st_wf_okv ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_wf_okv rb s Hs Hvb) as Hb. fold b in Hb.
  pose proof (okv_mag_nonneg a Ha) as Ma. pose proof (okv_mag_nonneg b Hb) as Mb.
  pose proof (norm_zero_iff a Ha Hna) as Za. pose proof (norm_zero_iff b Hb Hnb) as Zb.
  set (mx := Nat.max (bn_top a) (bn_top b)) in *.
  eapply hoare_bind with (R := fun (r_neg : bool) (s' : ST) => exists r' : BN, s' = setbn rr r' s /\ bn_norm r' /\ (bn_top r' <= mx + 1)%nat /\
            (if r_neg then - bn_mag r' else bn_mag r') = bn_val a - bn_val b /\ (bn_mag r' = 0 -> r_neg = false)).
  2:{ intros r_neg s1 Hs1 (r1 & -> & N1 & N2 & N3 & N4).
      eapply hoare_mono; [apply (set_neg_spec rr r_neg F _ (fun x => x = bn_with_neg r1 r_neg)); [rewrite length_setbn; exact Hr|exact Hn|
                                 rewrite getbn_setbn_same by exact Hr; reflexivity]|].
      intros [] s2 _ (r2 & -> & ->). rewrite setbn_setbn_same. eexists. split; [reflexivity|].
      unfold signed_post, bn_canon. rewrite bn_val_with_neg. split; [split; [exact N1|]|split; [exact N3|exact N2]].
      cbn [bn_with_neg bn_top bn_neg]. intros Et. apply N4. apply (bn_mag_top0 r1 Et). }
  unfold bn_val. destruct (Bool.eqb (bn_neg a) (bn_neg b)) eqn:Esgn; cbn [negb].
  - apply eqb_prop in Esgn.
    eapply hoare_bind; [apply BN_ucmp_spec; assumption|]. intros c s1 _ [-> ->]. fold a b.
    destruct (ucmp_okv_spec a b Ha Hb Hna Hnb) as (U1 & U2 & U3).
    destruct (Z.ltb_spec 0 (ucmp_pure a b)) as [Hc|Hc].
    + specialize (U1 Hc).
      eapply hoare_bind; [apply BN_usub_spec; try assumption; fold a b; lia|].
      intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|].
      split; [unfold mx; lia|]. rewrite P2, <- Esgn. split; [destruct (bn_neg a); lia|lia].
    + destruct (Z.ltb_spec (ucmp_pure a b) 0) as [Hc'|Hc'].
      * specialize (U2 Hc').
        eapply hoare_bind; [apply BN_usub_spec; try assumption; fold a b; lia|].
        intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|].
        split; [unfold mx; lia|]. rewrite P2, Esgn. split; [destruct (bn_neg b); cbn [negb]; lia|lia].
      * assert (Ec : ucmp_pure a b = 0) by lia. specialize (U3 Ec).
        eapply hoare_bind; [apply BN_zero_spec; assumption|].
        intros [] s1 _ (r1 & -> & T1 & T2). apply hoare_ret. exists r1. split; [reflexivity|]. split; [left; exact T1|].
        split; [lia|]. rewrite (bn_mag_top0 r1 T1), Esgn. split; [destruct (bn_neg b); lia|reflexivity].
  - apply eqb_false_iff in Esgn.
    eapply hoare_bind; [apply BN_uadd_spec; assumption|].
    intros [] s1 _ (r1 & -> & P1 & P2 & P3 & P4). fold a b in P2, P4. fold mx in P4. apply hoare_ret. exists r1. split; [reflexivity|]. split; [exact P1|]. split; [exact P4|].
    rewrite P2. split; [destruct (bn_neg a), (bn_neg b); try congruence; lia|].
    intros Hz. assert (Hma0 : bn_mag a = 0) by lia. apply Hza. apply Za. exact Hma0.
Qed.

End AddSpec.
