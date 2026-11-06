(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnInv BnSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_carry_words_spec : forall a c, limbs a -> 0 <= c <= 1 ->
  let '(r, c') := add_carry_words a c in
  limbs r /\ length r = length a /\ 0 <= c' <= 1 /\ lval r + Bp (length a) * c' = lval a + c.
Proof.
  induction a as [|t a IH]; intros c Ha Hc.
  - cbn [add_carry_words lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [[Ht0 Ht1] Ha]. cbn [add_carry_words]. unfold addw.
    pose proof BW_pos as BWp.
    set (c1 := if (t + c) mod BW =? 0 then c else 0).
    assert (Hc1 : 0 <= c1 <= 1 /\ (t + c) mod BW + BW * c1 = t + c).
    { subst c1. destruct (Z.eq_dec (t + c) BW) as [E|E].
      - assert (Ec : c = 1) by lia. rewrite E, Z.mod_same by lia. cbn [Z.eqb]. rewrite Ec. lia.
      - rewrite (Z.mod_small (t + c) BW) by lia. destruct (Z.eqb_spec (t + c) 0); lia. }
    destruct Hc1 as [Hc1 Ec1]. specialize (IH c1 Ha Hc1). destruct (add_carry_words a c1) as [r c'].
    destruct IH as (H1 & H2 & H3 & H4). cbn [lval length]. rewrite Bp_S.
    split; [constructor; [apply limb_mod|exact H1]|]. split; [lia|]. split; [lia|]. nia.
Qed.

(* [comment removed for export] *)
Lemma top_limb_nonzero : forall l n, limbs l -> length l = n -> (1 <= n)%nat -> Bp (n - 1) <= lval l -> nth (n - 1) l 0 <> 0.
Proof.
  intros l n Hl Hlen Hn Hv E. pose proof (nth_limb_val l (n - 1) Hl ltac:(lia)) as Ev. rewrite E in Ev.
  rewrite (skipn_all2 l) in Ev by lia. cbn [lval] in Ev.
  pose proof (lval_bound _ (limbs_firstn (n - 1) l Hl)) as Hb. rewrite firstn_length_le in Hb by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma uadd_pure : forall a b, limbs a -> limbs b -> (length b <= length a)%nat ->
  let min := length b in
  let '(s, c1) := add_words (firstn min a) b in
  let '(s2, c2) := add_carry_words (skipn min a) c1 in
  let w := s ++ s2 ++ [c2] in
  limbs w /\ length w = S (length a) /\ 0 <= c2 <= 1 /\ lval w = lval a + lval b /\
  lval (firstn (length a) w) + Bp (length a) * c2 = lval a + lval b.
Proof.
  intros a b Ha Hb Hlen. cbv zeta.
  pose proof (add_words_spec (firstn (length b) a) b (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (add_words (firstn (length b) a) b) as [s c1]. destruct H1 as (S1 & S2 & S3 & S4).
  rewrite firstn_length_le in S2, S4 by lia.
  pose proof (add_carry_words_spec (skipn (length b) a) c1 (limbs_skipn _ _ Ha) S3) as H2.
  destruct (add_carry_words (skipn (length b) a) c1) as [s2 c2]. destruct H2 as (T1 & T2 & T3 & T4).
  rewrite length_skipn in T2, T4.
  pose proof (lval_split_le (length b) a Hlen) as Ea.
  assert (EB : Bp (length a) = Bp (length b) * Bp (length a - length b)) by (rewrite <- Bp_add; f_equal; lia).
  assert (Hw : lval (s ++ s2 ++ [c2]) = lval a + lval b).
  { rewrite !lval_app. cbn [lval]. rewrite S2, T2. nia. }
  split; [apply limbs_app; [exact S1|apply limbs_app; [exact T1|constructor; [unfold limb, BW; lia|constructor]]]|].
  split; [rewrite !length_app; cbn [length]; lia|]. split; [exact T3|]. split; [exact Hw|].
  assert (Ef : firstn (length a) (s ++ s2 ++ [c2]) = s ++ s2).
  { rewrite app_assoc. rewrite firstn_app. rewrite firstn_all2 by (rewrite length_app; lia).
    replace (length a - length (s ++ s2))%nat with 0%nat by (rewrite length_app; lia). cbn [firstn]. apply app_nil_r. }
  rewrite Ef. rewrite lval_app, S2. nia.
Qed.

(* [comment removed for export] *)
Lemma usub_pure : forall a b, limbs a -> limbs b -> (length b <= length a)%nat -> lval b <= lval a ->
  let min := length b in
  let '(s, bw) := sub_words (firstn min a) b in
  let '(s2, _) := sub_part_pos (skipn min a) bw in
  let w := s ++ s2 in
  limbs w /\ length w = length a /\ lval w = lval a - lval b.
Proof.
  intros a b Ha Hb Hlen Hge. cbv zeta.
  pose proof (sub_words_spec (firstn (length b) a) b (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (sub_words (firstn (length b) a) b) as [s bw]. destruct H1 as (S1 & S2 & S3 & S4).
  rewrite firstn_length_le in S2, S4 by lia.
  pose proof (sub_part_pos_spec (skipn (length b) a) bw (limbs_skipn _ _ Ha) S3) as H2.
  destruct (sub_part_pos (skipn (length b) a) bw) as [s2 c2]. destruct H2 as (T1 & T2 & T3 & T4).
  rewrite length_skipn in T2, T4.
  pose proof (lval_split_le (length b) a Hlen) as Ea.
  assert (EB : Bp (length a) = Bp (length b) * Bp (length a - length b)) by (rewrite <- Bp_add; f_equal; lia).
  assert (Hw : limbs (s ++ s2)) by (apply limbs_app; assumption).
  assert (Hwl : length (s ++ s2) = length a) by (rewrite length_app; lia).
  split; [exact Hw|]. split; [exact Hwl|].
  assert (E : lval (s ++ s2) - Bp (length a) * c2 = lval a - lval b) by (rewrite lval_app, S2; nia).
  pose proof (lval_bound _ Hw) as Hb1. rewrite Hwl in Hb1. pose proof (lval_bound a Ha). pose proof (lval_nonneg b Hb).
  pose proof (Bp_pos (length a)). assert (c2 = 0 \/ c2 = 1) as [E0|E1] by lia; [rewrite E0 in E; lia|rewrite E1 in E; lia].
Qed.

Section AddSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma bnref_eq_dec : forall r r' : bnref, {r = r'} + {r <> r'}.
Proof. decide equality. apply Nat.eq_dec. Qed.

Lemma expanded_prefix : forall (b b' : BN) words, bn_ok b -> expanded b words b' ->
  firstn (bn_top b) (bn_buf b') = firstn (bn_top b) (bn_buf b).
Proof.
  intros b b' words (H1 & H2 & _) (_ & _ & _ & E & _). rewrite E. unfold bn_dmax in *.
  destruct (words <=? length (bn_buf b))%nat; [reflexivity|].
  rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

(* [comment removed for export] *)
Lemma fetch_after_expand : forall rr rx (s : LS) words r1 r1',
  st_ok s -> valid_ref rr s -> valid_ref rx s -> expanded (getbn rr s) words r1 -> bn_buf r1' = bn_buf r1 ->
  firstn (bn_top (getbn rx s)) (bn_buf (getbn rx (setbn rr r1' s))) = firstn (bn_top (getbn rx s)) (bn_buf (getbn rx s)).
Proof.
  intros rr rx s words r1 r1' Hs Hvr Hvx Hexp Ebuf. destruct (bnref_eq_dec rr rx) as [->|Hne].
  - rewrite getbn_setbn_same by assumption. rewrite Ebuf. eapply expanded_prefix; [apply st_ok_getbn; assumption|exact Hexp].
  - rewrite getbn_setbn_other by exact Hne. reflexivity.
Qed.

Lemma slice_of_firstn : forall (l : list Z) m n, (m <= n)%nat -> slice l m (n - m) = skipn m (firstn n l).
Proof. intros l m n H. unfold slice. rewrite skipn_firstn_comm. reflexivity. Qed.

Lemma firstn_of_firstn : forall (l : list Z) m n, (m <= n)%nat -> firstn m l = firstn m (firstn n l).
Proof. intros l m n H. rewrite firstn_firstn, Nat.min_l by lia. reflexivity. Qed.

(* [comment removed for export] *)
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

Lemma BN_uadd_unfold : forall rr ra rb (s : LS),
  BN_uadd ops rr ra rb s =
  (if (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat then uadd_body rr rb ra s else uadd_body rr ra rb s).
Proof.
  intros rr ra rb s. unfold BN_uadd, bbind at 1 2. cbn [bind tree_ops bget tbind ret fst snd].
  destruct (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat; reflexivity.
Qed.

Lemma bwp_BN_uadd : forall rr ra rb (s : LS) X (Q : unit -> LS -> blocks -> Prop),
  bwp (if (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat then uadd_body rr rb ra else uadd_body rr ra rb) s X Q ->
  bwp (BN_uadd ops rr ra rb) s X Q.
Proof.
  intros rr ra rb s X Q H. unfold bwp in *. rewrite BN_uadd_unfold.
  destruct (bn_top (getbn ra s) <? bn_top (getbn rb s))%nat; exact H.
Qed.

Lemma uadd_body_spec : forall rr ra rb s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref rr s -> valid_ref ra s -> valid_ref rb s -> (rr = ra \/ rr = rb) ->
  (bn_top (getbn rb s) <= bn_top (getbn ra s))%nat -> bn_norm (getbn ra s) ->
  Z.of_nat (bn_top (getbn ra s)) + 1 <= DMAX_MAX ->
  (forall r' X', bn_ok r' -> bn_norm r' -> bn_mag r' = bn_mag (getbn ra s) + bn_mag (getbn rb s) -> bn_neg r' = false ->
     st_ok (setbn rr r' s) -> own (setbn rr r' s) X' -> Q tt (setbn rr r' s) X') ->
  bwp (uadd_body rr ra rb) s X Q.
Proof.
  intros rr ra rb s X Q Hs Ho Hvr Hva Hvb Hrr Htops Hna Hsz HQ. unfold uadd_body.
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *. set (max := bn_top a) in *. set (min := bn_top b) in *.
  pose proof (st_ok_getbn ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_ok_getbn rb s Hs Hvb) as Hb. fold b in Hb.
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|lia|].
  intros r1 X1 Hexp Hs1 Ho1. pose proof Hexp as (E1 & E2 & E3 & E4 & Hr1 & E5 & E6).
  assert (Hvr1 : valid_ref rr (setbn rr r1 s)) by (apply valid_ref_setbn; exact Hvr).
  apply bwp_bind. apply bwp_bind, bwp_get. rewrite getbn_setbn_same by assumption.
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
  assert (Hr1t : bn_ok (bn_with_top r1 max)).
  { unfold bn_ok, bn_dmax, bn_with_top. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. }
  apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; reflexivity|].
  rewrite setbn_setbn_same. intros Hs2 Ho2. set (s2 := setbn rr (bn_with_top r1 max) s) in *.
  assert (Hvr2 : valid_ref rr s2) by (subst s2; apply valid_ref_setbn; exact Hvr).
  assert (Egr2 : getbn rr s2 = bn_with_top r1 max) by (subst s2; apply getbn_setbn_same; assumption).
  (* [comment removed for export] *)
  assert (Htail : forall r3 X3, bn_ok r3 -> bn_norm r3 -> bn_mag r3 = bn_mag a + bn_mag b -> length (bn_buf r3) = length (bn_buf r1) ->
            bn_d r3 = bn_d r1 -> st_ok (setbn rr r3 s) -> own (setbn rr r3 s) X3 ->
            bwp (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false))) (setbn rr r3 s) X3 Q).
  { intros r3 X3 Hr3 Hn3 Hm3 Hl3 Hd3 Hs3 Ho3. apply bwp_bind, bwp_get.
    assert (Hv3 : valid_ref rr (setbn rr r3 s)) by (apply valid_ref_setbn; exact Hvr).
    rewrite getbn_setbn_same by assumption.
    assert (Hr4 : bn_ok (bn_with_neg r3 false)).
    { destruct Hr3 as (A1 & A2 & A3 & A4). unfold bn_ok, bn_dmax, bn_with_neg in *. cbn [bn_buf bn_top bn_flags]. tauto. }
    apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; reflexivity|].
    rewrite setbn_setbn_same. intros Hs4 Ho4. apply HQ; try assumption; try reflexivity. }
  apply bwp_bind. destruct (Nat.eqb_spec max 0) as [Emax|Nmax].
  - apply bwp_ret. subst s2. apply Htail; try assumption; try reflexivity.
    + left. cbn [bn_with_top bn_top]. exact Emax.
    + unfold bn_mag at 1. cbn [bn_with_top bn_top]. rewrite Emax. cbn [firstn lval].
      rewrite (bn_mag_top0 a) by (fold max; exact Emax). rewrite (bn_mag_top0 b) by (fold min; lia). reflexivity.
  - apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. rewrite Egr2.
    set (a2 := getbn ra s2). set (b2 := getbn rb s2).
    set (la := firstn max (bn_buf a)). set (lb := firstn min (bn_buf b)).
    assert (Ela : firstn max (bn_buf a2) = la) by (subst a2 s2 la max a; eapply fetch_after_expand; eauto).
    assert (Elb : firstn min (bn_buf b2) = lb) by (subst b2 s2 lb min b; eapply fetch_after_expand; eauto).
    destruct Ha as (A1 & A2 & A3 & A4). destruct Hb as (B1 & B2 & B3 & B4). unfold bn_dmax in *.
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
    assert (Hr3 : bn_ok r3).
    { unfold bn_ok, bn_dmax. rewrite L3. subst r3. cbn [bn_buf bn_top bn_flags].
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
        pose proof (bn_mag_ge a (conj A1 (conj A2 (conj A3 A4))) Hna ltac:(fold max; lia)) as Hge. fold max in Hge.
        change (bn_mag a) with (lval la) in Hge. pose proof (lval_nonneg lb Hlb). lia.
      - change (Pos.to_nat 1) with 1%nat. replace (max + 1 - 1)%nat with max by lia. rewrite Hnth by lia.
        assert (Hl12 : length (sv ++ sv2) = max).
        { subst w. rewrite app_assoc, length_app in W2. cbn [length] in W2. lia. }
        subst w. rewrite app_assoc, app_nth2 by lia. rewrite Hl12, Nat.sub_diag. cbn [nth]. lia. }
    apply bwp_update; try assumption; [rewrite Egr2; apply bn_blocks_same; [reflexivity|exact L3]|].
    subst s2. rewrite setbn_setbn_same. intros Hs3 Ho3. apply Htail; try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_usub_spec : forall rr ra rb s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref rr s -> valid_ref ra s -> valid_ref rb s -> (rr = ra \/ rr = rb) ->
  (bn_top (getbn rb s) <= bn_top (getbn ra s))%nat -> bn_mag (getbn rb s) <= bn_mag (getbn ra s) ->
  (forall r' X', bn_ok r' -> bn_norm r' -> bn_mag r' = bn_mag (getbn ra s) - bn_mag (getbn rb s) -> bn_neg r' = false ->
     st_ok (setbn rr r' s) -> own (setbn rr r' s) X' -> Q tt (setbn rr r' s) X') ->
  bwp (BN_usub ops rr ra rb) s X Q.
Proof.
  intros rr ra rb s X Q Hs Ho Hvr Hva Hvb Hrr Htops Hmags HQ. unfold BN_usub.
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *. set (max := bn_top a) in *. set (min := bn_top b) in *.
  pose proof (st_ok_getbn ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_ok_getbn rb s Hs Hvb) as Hb. fold b in Hb.
  destruct (Nat.ltb_spec max min) as [|_]; [lia|].
  destruct Ha as (A1 & A2 & A3 & A4). destruct Hb as (B1 & B2 & B3 & B4). unfold bn_dmax in *.
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption|lia|].
  intros r1 X1 Hexp Hs1 Ho1. pose proof Hexp as (E1 & E2 & E3 & E4 & Hr1 & E5 & E6).
  set (s1 := setbn rr r1 s) in *.
  assert (Hvr1 : valid_ref rr s1) by (subst s1; apply valid_ref_setbn; exact Hvr).
  assert (Egr1 : getbn rr s1 = r1) by (subst s1; apply getbn_setbn_same; assumption).
  destruct Hr1 as (R1 & R2 & R3 & R4). unfold bn_dmax in *.
  (* [comment removed for export] *)
  assert (Htail : forall r2 X2, limbs (bn_buf r2) -> length (bn_buf r2) = length (bn_buf r1) -> bn_d r2 = bn_d r1 -> bn_flags r2 = bn_flags r1 ->
            lval (firstn max (bn_buf r2)) = bn_mag a - bn_mag b -> st_ok (setbn rr r2 s) -> own (setbn rr r2 s) X2 ->
            bwp (bbind ops (bget ops rr) (fun r => bset ops rr (mkBN (bn_d r) (bn_buf r) (strip_top (bn_buf r) max) false (bn_flags r))))
                (setbn rr r2 s) X2 Q).
  { intros r2 X2 L1 L2 L3 L4 L5 Hs2 Ho2. apply bwp_bind, bwp_get.
    assert (Hv2 : valid_ref rr (setbn rr r2 s)) by (apply valid_ref_setbn; exact Hvr).
    rewrite getbn_setbn_same by assumption.
    destruct (strip_top_spec (bn_buf r2) max ltac:(lia)) as (S1 & S2 & S3).
    set (r3 := mkBN (bn_d r2) (bn_buf r2) (strip_top (bn_buf r2) max) false (bn_flags r2)).
    assert (Hr3 : bn_ok r3).
    { unfold bn_ok, bn_dmax. subst r3. cbn [bn_buf bn_top bn_flags]. rewrite L2, L4. repeat split; try assumption; lia. }
    apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; reflexivity|].
    rewrite setbn_setbn_same. intros Hs3 Ho3. apply HQ; try assumption; try reflexivity.
    unfold bn_mag at 1. subst r3. cbn [bn_buf bn_top]. rewrite S2. exact L5. }
  apply bwp_bind. destruct (Nat.eqb_spec max 0) as [Emax|Nmax].
  - apply bwp_ret. subst s1. apply Htail; try assumption; try reflexivity.
    rewrite Emax. cbn [firstn lval]. rewrite (bn_mag_top0 a) by (fold max; exact Emax). rewrite (bn_mag_top0 b) by (fold min; lia). reflexivity.
  - apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. rewrite Egr1.
    set (a2 := getbn ra s1). set (b2 := getbn rb s1).
    set (la := firstn max (bn_buf a)). set (lb := firstn min (bn_buf b)).
    assert (Ela : firstn max (bn_buf a2) = la) by (subst a2 s1 la max a; eapply fetch_after_expand; eauto).
    assert (Elb : firstn min (bn_buf b2) = lb) by (subst b2 s1 lb min b; eapply fetch_after_expand; eauto).
    assert (Hla : limbs la) by (apply limbs_firstn; exact A1). assert (Hlb : limbs lb) by (apply limbs_firstn; exact B1).
    assert (Hlal : length la = max) by (apply firstn_length_le; lia). assert (Hlbl : length lb = min) by (apply firstn_length_le; lia).
    rewrite (firstn_of_firstn (bn_buf a2) min max) by lia. rewrite (slice_of_firstn (bn_buf a2) min max) by lia. rewrite Ela, Elb.
    pose proof (usub_pure la lb Hla Hlb ltac:(lia) Hmags) as Hp. cbv zeta in Hp. rewrite Hlbl in Hp.
    destruct (sub_words (firstn min la) lb) as [sv bw]. destruct (sub_part_pos (skipn min la) bw) as [sv2 c2].
    destruct Hp as (W1 & W2 & W3). rewrite Hlal in W2.
    set (r2 := bn_with_buf r1 (splice (bn_buf r1) 0 (sv ++ sv2))).
    assert (L2 : length (bn_buf r2) = length (bn_buf r1)) by (subst r2; cbn [bn_with_buf bn_buf]; apply splice_length; lia).
    assert (Hr2 : bn_ok r2).
    { unfold bn_ok, bn_dmax. rewrite L2. subst r2. cbn [bn_with_buf bn_buf bn_top bn_flags].
      split; [apply splice_limbs; assumption|]. repeat split; try assumption; lia. }
    apply bwp_update; try assumption; [rewrite Egr1; apply bn_blocks_same; [reflexivity|exact L2]|].
    subst s1. rewrite setbn_setbn_same. intros Hs2 Ho2. apply Htail; try assumption; try reflexivity.
    + destruct Hr2 as (H & _). exact H.
    + subst r2. cbn [bn_with_buf bn_buf]. rewrite firstn_splice_0 by lia. exact W3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ucmp_pure_spec : forall a b : BN, bn_ok a -> bn_ok b -> bn_norm a -> bn_norm b ->
  (0 < ucmp_pure a b -> bn_mag b < bn_mag a /\ (bn_top b <= bn_top a)%nat) /\
  (ucmp_pure a b < 0 -> bn_mag a < bn_mag b /\ (bn_top a <= bn_top b)%nat) /\
  (ucmp_pure a b = 0 -> bn_mag a = bn_mag b).
Proof.
  intros a b Ha Hb Hna Hnb. unfold ucmp_pure.
  destruct (Z.eqb_spec (Z.of_nat (bn_top a) - Z.of_nat (bn_top b)) 0) as [E|E].
  - assert (Et : bn_top a = bn_top b) by lia. destruct Ha as (A1 & A2 & _). destruct Hb as (B1 & B2 & _). unfold bn_dmax in *.
    rewrite cmp_words_spec by (try (apply limbs_firstn; assumption); rewrite !firstn_length_le by lia; exact Et).
    fold (bn_mag a) (bn_mag b).
    destruct (Z.lt_trichotomy (bn_mag a) (bn_mag b)) as [H|[H|H]];
      [rewrite (sgn3_lt _ _ H)|rewrite H, sgn3_eq|rewrite (sgn3_gt _ _ H)]; repeat split; intros; lia.
  - split; [|split]; intros H; try lia.
    + assert (Hlt : (bn_top b < bn_top a)%nat) by lia. split; [|lia].
      pose proof (bn_mag_lt b Hb). pose proof (bn_mag_ge a Ha Hna ltac:(lia)). pose proof (Bp_mono (bn_top b) (bn_top a - 1) ltac:(lia)). lia.
    + assert (Hlt : (bn_top a < bn_top b)%nat) by lia. split; [|lia].
      pose proof (bn_mag_lt a Ha). pose proof (bn_mag_ge b Hb Hnb ltac:(lia)). pose proof (Bp_mono (bn_top a) (bn_top b - 1) ltac:(lia)). lia.
Qed.

Lemma cmp_pure_eq : forall a b : BN, bn_ok a -> bn_ok b -> bn_canon a -> bn_canon b -> bn_val a = bn_val b -> cmp_pure a b = 0.
Proof.
  intros a b Ha Hb [Hna Hza] [Hnb Hzb] Hv. unfold cmp_pure, bn_val in *.
  pose proof (bn_mag_nonneg a Ha). pose proof (bn_mag_nonneg b Hb).
  pose proof (bn_norm_zero_iff a Ha Hna) as Za. pose proof (bn_norm_zero_iff b Hb Hnb) as Zb.
  assert (Hneg : bn_neg a = bn_neg b).
  { destruct (bn_neg a) eqn:Ea; destruct (bn_neg b) eqn:Eb; try reflexivity.
    - assert (bn_mag a = 0) by lia. apply Za in H1. specialize (Hza H1). congruence.
    - assert (bn_mag b = 0) by lia. apply Zb in H1. specialize (Hzb H1). congruence. }
  assert (Hmag : bn_mag a = bn_mag b) by (rewrite Hneg in Hv; destruct (bn_neg b); lia).
  destruct (bn_norm_mag_inj a b Ha Hb Hna Hnb Hmag) as [Et Ef].
  rewrite Hneg. rewrite Bool.eqb_reflx. cbn [negb].
  rewrite Et. rewrite Nat.ltb_irrefl. rewrite <- Et at 1. rewrite Ef.
  destruct Hb as (B1 & B2 & _). unfold bn_dmax in *.
  rewrite cmp_words_spec by (try (apply limbs_firstn; assumption); reflexivity). rewrite sgn3_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_add_spec : forall ra rb s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref ra s -> valid_ref rb s -> ra <> rb ->
  bn_canon (getbn ra s) -> bn_canon (getbn rb s) ->
  Z.of_nat (bn_top (getbn ra s)) + 1 <= DMAX_MAX -> Z.of_nat (bn_top (getbn rb s)) + 1 <= DMAX_MAX ->
  (forall r' X', bn_ok r' -> bn_canon r' -> bn_val r' = bn_val (getbn ra s) + bn_val (getbn rb s) ->
     st_ok (setbn ra r' s) -> own (setbn ra r' s) X' -> Q tt (setbn ra r' s) X') ->
  bwp (BN_add ops ra ra rb) s X Q.
Proof.
  intros ra rb s X Q Hs Ho Hva Hvb Hne [Hna Hza] [Hnb Hzb] Hsa Hsb HQ. unfold BN_add.
  apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
  set (a := getbn ra s) in *. set (b := getbn rb s) in *.
  pose proof (st_ok_getbn ra s Hs Hva) as Ha. fold a in Ha. pose proof (st_ok_getbn rb s Hs Hvb) as Hb. fold b in Hb.
  pose proof (bn_mag_nonneg a Ha) as Ma. pose proof (bn_mag_nonneg b Hb) as Mb.
  pose proof (bn_norm_zero_iff a Ha Hna) as Za. pose proof (bn_norm_zero_iff b Hb Hnb) as Zb.
  (* [comment removed for export] *)
  assert (Htail : forall (r_neg : bool) r3 X3, bn_ok r3 -> bn_norm r3 -> bn_neg r3 = false ->
            (if r_neg then - bn_mag r3 else bn_mag r3) = bn_val a + bn_val b -> (bn_mag r3 = 0 -> r_neg = false) ->
            st_ok (setbn ra r3 s) -> own (setbn ra r3 s) X3 ->
            bwp (bbind ops (bget ops ra) (fun r => bset ops ra (bn_with_neg r r_neg))) (setbn ra r3 s) X3 Q).
  { intros r_neg r3 X3 Hr3 Hn3 Hneg3 Hval Hzero Hs3 Ho3. apply bwp_bind, bwp_get.
    assert (Hv3 : valid_ref ra (setbn ra r3 s)) by (apply valid_ref_setbn; exact Hva).
    rewrite getbn_setbn_same by assumption.
    assert (Hr4 : bn_ok (bn_with_neg r3 r_neg)).
    { destruct Hr3 as (A1 & A2 & A3 & A4). unfold bn_ok, bn_dmax, bn_with_neg in *. cbn [bn_buf bn_top bn_flags]. tauto. }
    apply bwp_update; try assumption; [rewrite getbn_setbn_same by assumption; reflexivity|].
    rewrite setbn_setbn_same. intros Hs4 Ho4. apply HQ; try assumption.
    split; [exact Hn3|]. intros Et. cbn [bn_with_neg bn_top bn_neg] in *. apply Hzero. apply (bn_mag_top0 r3 Et). }
  apply bwp_bind.
  destruct (Bool.eqb (bn_neg a) (bn_neg b)) eqn:Esign.
  - (* [comment removed for export] *)
    apply Bool.eqb_prop in Esign.
    apply bwp_bind. apply bwp_BN_uadd. fold a b.
    destruct (Nat.ltb_spec (bn_top a) (bn_top b)) as [Hlt|Hge].
    + apply (uadd_body_spec ra rb ra s X); try assumption; try (right; reflexivity); try (fold a b; lia).
      fold a b. intros r3 X3 Hr3 Hn3 Hm3 Hneg3 Hs3 Ho3. apply bwp_ret. apply Htail; try assumption.
      * rewrite Hm3. unfold bn_val. rewrite Esign. destruct (bn_neg b); lia.
      * intros E. rewrite Hm3 in E. assert (bn_mag a = 0) by lia. apply Za in H. exact (Hza H).
    + apply (uadd_body_spec ra ra rb s X); try assumption; try (left; reflexivity); try (fold a b; lia).
      fold a b. intros r3 X3 Hr3 Hn3 Hm3 Hneg3 Hs3 Ho3. apply bwp_ret. apply Htail; try assumption.
      * rewrite Hm3. unfold bn_val. rewrite Esign. destruct (bn_neg b); lia.
      * intros E. rewrite Hm3 in E. assert (bn_mag a = 0) by lia. apply Za in H. exact (Hza H).
  - (* [comment removed for export] *)
    apply Bool.eqb_false_iff in Esign.
    apply bwp_bind. unfold BN_ucmp. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. fold a b.
    unfold BN_FLG_CONSTTIME. rewrite (flags_land_0 a 4 Ha), (flags_land_0 b 4 Hb) by tauto. cbn [negb orb]. apply bwp_ret.
    destruct (ucmp_pure_spec a b Ha Hb Hna Hnb) as (U1 & U2 & U3).
    destruct (Z.ltb_spec 0 (ucmp_pure a b)) as [Hpos|Hnpos].
    + destruct (U1 Hpos) as [Um Ut].
      apply bwp_bind. apply (BN_usub_spec ra ra rb s X); try assumption; try (left; reflexivity); try (fold a b; lia).
      fold a b. intros r3 X3 Hr3 Hn3 Hm3 Hneg3 Hs3 Ho3. apply bwp_ret. apply Htail; try assumption.
      * rewrite Hm3. unfold bn_val. destruct (bn_neg a); destruct (bn_neg b); try congruence; lia.
      * intros E. lia.
    + destruct (Z.ltb_spec (ucmp_pure a b) 0) as [Hneg|Hz].
      * destruct (U2 Hneg) as [Um Ut].
        apply bwp_bind. apply (BN_usub_spec ra rb ra s X); try assumption; try (right; reflexivity); try (fold a b; lia).
        fold a b. intros r3 X3 Hr3 Hn3 Hm3 Hneg3 Hs3 Ho3. apply bwp_ret. apply Htail; try assumption.
        -- rewrite Hm3. unfold bn_val. destruct (bn_neg a); destruct (bn_neg b); try congruence; lia.
        -- intros E. lia.
      * assert (Hz0 : ucmp_pure a b = 0) by lia. specialize (U3 Hz0).
        apply bwp_bind. apply bwp_bind, bwp_get. fold a.
        apply bwp_update; try assumption; [apply bn_ok_zero; exact Ha|reflexivity|].
        intros Hs3 Ho3. apply bwp_ret. apply Htail; try assumption; try reflexivity.
        -- apply bn_ok_zero; exact Ha.
        -- left. reflexivity.
        -- unfold bn_mag at 1. cbn [bn_zero_pure bn_top firstn lval]. unfold bn_val. destruct (bn_neg a); destruct (bn_neg b); try congruence; lia.
Qed.

End AddSpec.
