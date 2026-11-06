(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv BnSpecs BnSpecs2 BnAddSpec.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BgState BgWords BgLib BgInv BgSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section LibSpec.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_wf_bn_ok : forall r (s : ST), st_wf s -> (r < length (st_bns s))%nat -> r <> ROne -> bn_ok (getbn r s).
Proof. intros. apply bg_ok_bn_ok, st_wf_ok; assumption. Qed.

Lemma st_wf_top_le : forall r (s : ST), st_wf s -> (r < length (st_bns s))%nat -> Z.of_nat (bn_top (getbn r s)) <= BG_DMAX.
Proof.
  intros r s Hs Hr. destruct (Nat.eq_dec r ROne) as [->|Hn].
  - destruct Hs as (_ & _ & E & _). rewrite E. cbn. unfold BG_DMAX. lia.
  - destruct (st_wf_ok r s Hs Hr Hn) as (_ & H1 & H2 & _). lia.
Qed.

Lemma st_wf_no_flag : forall r (s : ST) f, st_wf s -> (r < length (st_bns s))%nat ->
  (f = BN_FLG_CONSTTIME \/ f = BN_FLG_SECURE) -> has_flag (getbn r s) f = false.
Proof.
  intros r s f Hs Hr Hf. unfold has_flag. destruct (Nat.eq_dec r ROne) as [->|Hn].
  - destruct Hs as (_ & _ & E & _). rewrite E. cbn [bn_const_one bn_flags]. destruct Hf as [-> | ->]; reflexivity.
  - destruct (st_wf_ok r s Hs Hr Hn) as (_ & _ & _ & [E|E]); rewrite E; destruct Hf as [-> | ->]; reflexivity.
Qed.

Lemma st_wf_no_static : forall r (s : ST), st_wf s -> (r < length (st_bns s))%nat -> r <> ROne ->
  has_flag (getbn r s) BN_FLG_STATIC_DATA = false.
Proof.
  intros r s Hs Hr Hn. unfold has_flag. destruct (st_wf_ok r s Hs Hr Hn) as (_ & _ & _ & [E|E]); rewrite E; reflexivity.
Qed.

Lemma mag_of_firstn_eq : forall (a b : BN), bn_top a = bn_top b ->
  firstn (bn_top b) (bn_buf a) = firstn (bn_top b) (bn_buf b) -> bn_mag a = bn_mag b.
Proof. intros a b Et Ef. unfold bn_mag. rewrite Et, Ef. reflexivity. Qed.

Lemma nth_of_firstn_eq : forall (l l' : list Z) n i, firstn n l = firstn n l' -> (i < n)%nat -> nth i l 0 = nth i l' 0.
Proof.
  intros l l' n i E Hi. assert (H : forall m : list Z, nth i (firstn n m) 0 = nth i m 0).
  { intros m. rewrite nth_firstn. destruct (Nat.ltb_spec i n); [reflexivity|lia]. }
  rewrite <- (H l), <- (H l'), E. reflexivity.
Qed.

Lemma norm_of_firstn_eq : forall (a b : BN), bn_top a = bn_top b ->
  firstn (bn_top b) (bn_buf a) = firstn (bn_top b) (bn_buf b) -> bn_norm b -> bn_norm a.
Proof.
  intros a b Et Ef [H|H]; [left; congruence|]. destruct (Nat.eq_dec (bn_top b) 0) as [E0|E0]; [left; congruence|].
  right. rewrite Et. rewrite (nth_of_firstn_eq _ _ _ _ Ef) by lia. exact H.
Qed.

Lemma bn_mag_const_one : bn_mag (bn_const_one : BN) = 1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma okv_mag_nonneg : forall b : BN, bg_okv b -> 0 <= bn_mag b.
Proof. intros b (H & _). apply lval_nonneg, limbs_firstn. exact H. Qed.

Lemma okv_mag_lt : forall b : BN, bg_okv b -> bn_mag b < Bp (bn_top b).
Proof.
  intros b (H & Ht). unfold bn_mag. pose proof (lval_bound _ (limbs_firstn (bn_top b) _ H)) as Hb.
  rewrite firstn_length_le in Hb by exact Ht. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma BN_copy_spec : forall ra rb F s,
  (ra < length (st_bns s))%nat -> ra <> ROne -> (rb < length (st_bns s))%nat ->
  hoare F s (BN_copy ops ra rb) (upd1 ra s (fun a' =>
     bn_top a' = bn_top (getbn rb s) /\ bn_neg a' = bn_neg (getbn rb s) /\
     firstn (bn_top (getbn rb s)) (bn_buf a') = firstn (bn_top (getbn rb s)) (bn_buf (getbn rb s)))).
Proof.
  intros ra rb F s Ha Hna Hb. apply hoare_wf. intros Hs. unfold BN_copy.
  apply hoare_bind_get. rewrite (st_wf_no_flag rb s _ Hs Hb) by (left; reflexivity). set (b := getbn rb s) in *.
  destruct (Nat.eqb_spec ra rb) as [->|Hne].
  - apply hoare_ret. exists b. split; [unfold b; rewrite setbn_getbn_id; reflexivity|]. auto.
  - eapply hoare_bind; [apply bn_wexpand_spec; [exact Ha|exact Hna|apply st_wf_top_le; assumption]|].
    intros [] s1 Hs1 (a1 & -> & Ha1). fold b in Ha1.
    apply hoare_bind_get. rewrite getbn_setbn_same by exact Ha.
    destruct Ha1 as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). pose proof Hok1 as (O1 & O2 & O3 & O4).
    pose proof (st_wf_okv rb s Hs Hb) as (Hbl & Hbt). fold b in Hbl, Hbt.
    set (buf := if (0 <? bn_top b)%nat then splice (bn_buf a1) 0 (firstn (bn_top b) (bn_buf b)) else bn_buf a1).
    assert (Hlen : length buf = length (bn_buf a1)).
    { unfold buf. destruct (0 <? bn_top b)%nat; [|reflexivity]. apply splice_length.
      rewrite firstn_length_le by exact Hbt. unfold bn_dmax in Hd1. lia. }
    assert (Hfst : firstn (bn_top b) buf = firstn (bn_top b) (bn_buf b)).
    { unfold buf. destruct (Nat.ltb_spec 0 (bn_top b)) as [Hpos|Hz].
      - apply firstn_splice_0; [apply firstn_length_le; exact Hbt|unfold bn_dmax in Hd1; lia].
      - assert (bn_top b = 0)%nat as -> by lia. reflexivity. }
    eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Ha; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen. split; [|split; [unfold bn_dmax in Hd1; lia|split; assumption]].
      unfold buf. destruct (0 <? bn_top b)%nat; [|exact O1]. apply splice_limbs; [exact O1|apply limbs_firstn; exact Hbl].
    + rewrite setbn_setbn_same. eexists. split; [reflexivity|]. cbn [bn_top bn_neg bn_buf]. auto.
Qed.

Lemma BN_zero_spec : forall r F s, (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (BN_zero ops r) (upd1 r s (fun b' => bn_top b' = 0%nat /\ bn_neg b' = false)).
Proof.
  intros r F s Hr Hn. apply hoare_wf. intros Hs. unfold BN_zero. apply hoare_bind_get.
  eapply hoare_set; try assumption; try reflexivity.
  - apply bg_ok_zero, st_wf_ok; assumption.
  - eexists. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma BN_set_word_spec : forall r w F s, (r < length (st_bns s))%nat -> r <> ROne -> limb w ->
  hoare F s (BN_set_word ops r w) (upd1 r s (fun b' =>
     bn_mag b' = w /\ bn_canon b' /\ bn_neg b' = false /\ (bn_top b' <= 1)%nat)).
Proof.
  intros r w F s Hr Hn Hw. unfold BN_set_word.
  eapply hoare_bind; [apply bn_wexpand_spec; [exact Hr|exact Hn|unfold BG_DMAX; lia]|].
  intros [] s1 Hs1 (b1 & -> & Hb1). apply hoare_bind_get. rewrite getbn_setbn_same by exact Hr.
  destruct Hb1 as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). pose proof Hok1 as (O1 & O2 & O3 & O4).
  assert (Hlen : length (upd (bn_buf b1) 0 w) = length (bn_buf b1)) by (apply upd_length; unfold bn_dmax in Hd1; lia).
  assert (Hn0 : nth 0 (upd (bn_buf b1) 0 w) 0 = w) by (apply nth_upd_same; unfold bn_dmax in Hd1; lia).
  eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
  - unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen.
    split; [apply upd_limbs; assumption|]. split; [unfold bn_dmax in Hd1; destruct (w =? 0); lia|split; assumption].
  - rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold bn_mag, bn_canon, bn_norm. cbn [bn_top bn_neg bn_buf].
    destruct (Z.eqb_spec w 0) as [->|Hw0].
    + cbn [firstn lval]. repeat split; auto.
    + assert (Hf : firstn 1 (upd (bn_buf b1) 0 w) = [w]).
      { destruct (upd (bn_buf b1) 0 w) as [|x l] eqn:El; [cbn in Hlen; unfold bn_dmax in Hd1; lia|]. cbn in Hn0. subst x. reflexivity. }
      rewrite Hf. cbn [lval]. repeat split; try lia.
      right. cbn [Nat.sub]. rewrite Hn0. exact Hw0.
Qed.

Lemma BN_one_spec : forall r F s, (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (BN_one ops r) (upd1 r s (fun b' => bn_mag b' = 1 /\ bn_canon b' /\ bn_neg b' = false /\ (bn_top b' <= 1)%nat)).
Proof. intros. apply BN_set_word_spec; try assumption. exact limb_1. Qed.

Lemma BN_set_negative_spec : forall r sgn F s, (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (BN_set_negative ops r sgn) (upd1 r s (fun b' =>
     b' = bn_with_neg (getbn r s) (sgn && negb (bn_top (getbn r s) =? 0)%nat))).
Proof.
  intros r sgn F s Hr Hn. apply hoare_wf. intros Hs. unfold BN_set_negative. apply hoare_bind_get.
  eapply hoare_set; try assumption; try reflexivity.
  - destruct (st_wf_ok r s Hs Hr Hn) as (A1 & A2 & A3 & A4). unfold bg_ok, bn_dmax in *. cbn [bn_with_neg bn_buf bn_top bn_flags]. tauto.
  - eexists. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Bp_pow2 : forall n, Bp n = 2 ^ (64 * Z.of_nat n).
Proof. intros n. unfold Bp. rewrite BW_pow, <- Z.pow_mul_r by lia. reflexivity. Qed.

Lemma lval_testbit : forall l n, limbs l -> 0 <= n ->
  Z.testbit (lval l) n = Z.testbit (nth (Z.to_nat (n / 64)) l 0) (n mod 64).
Proof.
  induction l as [|x l IH]; intros n Hl Hn.
  - cbn [lval]. destruct (Z.to_nat (n / 64)); cbn [nth]; rewrite !Z.testbit_0_l; reflexivity.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. cbn [lval].
    pose proof (lval_nonneg l Hl) as Hv.
    rewrite (Z.add_comm x (BW * lval l)).
    assert (Elor : Z.lor (BW * lval l) x = BW * lval l + x).
    { apply (lor_disjoint (BW * lval l) x 64); [lia|unfold BW in Hx1; lia|]. rewrite BW_pow, Z.mul_comm. apply Z.mod_mul. lia. }
    rewrite <- Elor.
    rewrite Z.lor_spec. destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
    + assert (E : n / 64 = 0) by (apply Z.div_small; lia). rewrite E. cbn [Z.to_nat nth].
      rewrite Z.mod_small by lia. rewrite BW_pow, Z.mul_comm, Z.mul_pow2_bits_low by lia. reflexivity.
    + assert (Hx : Z.testbit x n = false).
      { destruct (Z.eq_dec x 0) as [->|Hx]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
        apply Z.log2_lt_pow2; [lia|]. unfold BW in Hx1. eapply Z.lt_le_trans; [exact Hx1|]. apply (Z.pow_le_mono_r 2 64 n); lia. }
      rewrite Hx, orb_false_r. rewrite BW_pow, Z.mul_comm, Z.mul_pow2_bits by lia.
      rewrite IH by (try assumption; lia).
      replace (n / 64) with ((n - 64) / 64 + 1) by (replace n with ((n - 64) + 1 * 64) at 2 by lia; rewrite Z.div_add by lia; reflexivity).
      assert (0 <= (n - 64) / 64) by (apply Z.div_pos; lia).
      rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth].
      replace (n mod 64) with ((n - 64) mod 64) by (replace n with ((n - 64) + 1 * 64) at 2 by lia; rewrite Z.mod_add by lia; reflexivity).
      reflexivity.
Qed.

Lemma is_bit_set_pure_spec : forall (b : BN) n, bg_okv b -> 0 <= n -> is_bit_set_pure b n = Z.testbit (bn_mag b) n.
Proof.
  intros b n (Hl & Ht) Hn. unfold is_bit_set_pure, bn_mag. destruct (Z.ltb_spec n 0); [lia|].
  rewrite lval_testbit by (try apply limbs_firstn; assumption).
  assert (0 <= n / 64) by (apply Z.div_pos; lia).
  rewrite nth_firstn. destruct (Nat.leb_spec (bn_top b) (Z.to_nat (n / 64))) as [Hle|Hgt].
  - destruct (Nat.ltb_spec (Z.to_nat (n / 64)) (bn_top b)); [lia|]. rewrite Z.testbit_0_l. reflexivity.
  - destruct (Nat.ltb_spec (Z.to_nat (n / 64)) (bn_top b)); [reflexivity|lia].
Qed.

Lemma is_odd_pure_spec : forall b : BN, bg_okv b -> is_odd_pure b = Z.odd (bn_mag b).
Proof.
  intros b Hb. rewrite <- Z.bit0_odd, <- (is_bit_set_pure_spec b 0 Hb) by lia.
  unfold is_odd_pure, is_bit_set_pure. cbn [Z.ltb Z.compare Z.div Z.div_eucl Z.to_nat fst Z.modulo snd].
  destruct (Nat.leb_spec (bn_top b) 0) as [Hle|Hgt].
  - destruct (Nat.ltb_spec 0 (bn_top b)); [lia|reflexivity].
  - destruct (Nat.ltb_spec 0 (bn_top b)); [|lia]. rewrite Z.bit0_odd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma num_bits_pure_spec : forall b : BN, bg_okv b -> bn_norm b ->
  0 <= num_bits_pure b /\ (bn_mag b = 0 -> num_bits_pure b = 0) /\
  (0 < bn_mag b -> 2 ^ (num_bits_pure b - 1) <= bn_mag b < 2 ^ (num_bits_pure b)) /\
  num_bits_pure b <= 64 * Z.of_nat (bn_top b).
Proof.
  intros b (Hl & Ht) Hn. unfold num_bits_pure. destruct (Nat.eqb_spec (bn_top b) 0) as [E0|E0].
  - rewrite (bn_mag_top0 b E0). repeat split; try lia.
  - destruct Hn as [Hn|Hn]; [contradiction|]. set (t := nth (bn_top b - 1) (bn_buf b) 0) in *.
    pose proof (limbs_nth (bn_buf b) (bn_top b - 1) Hl) as [Ht0 Ht1]. fold t in Ht0, Ht1.
    destruct (num_bits_word_spec t ltac:(lia)) as (N1 & N2 & N3).
    pose proof (num_bits_word_le t 64 ltac:(lia) ltac:(unfold BW in Ht1; lia)) as N4.
    (* [comment removed for export] *)
    unfold bn_mag. set (l := firstn (bn_top b) (bn_buf b)).
    assert (Hll : limbs l) by (apply limbs_firstn; exact Hl).
    assert (Hlen : length l = bn_top b) by (apply firstn_length_le; exact Ht).
    pose proof (lval_split_le (bn_top b - 1) l ltac:(lia)) as Hsp.
    assert (Hsk : skipn (bn_top b - 1) l = [t]).
    { pose proof (firstn_skipn (bn_top b - 1) l) as Hfs.
      assert (Hlk : length (skipn (bn_top b - 1) l) = 1%nat) by (rewrite length_skipn; lia).
      destruct (skipn (bn_top b - 1) l) as [|y [|z r]] eqn:Es; cbn in Hlk; try lia. f_equal.
      assert (Hy : nth (bn_top b - 1) l 0 = y).
      { rewrite <- Hfs. rewrite app_nth2 by (rewrite firstn_length_le by lia; lia). rewrite firstn_length_le by lia.
        rewrite Nat.sub_diag. reflexivity. }
      rewrite <- Hy. unfold l, t. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
    rewrite Hsk in Hsp. cbn [lval] in Hsp. rewrite Z.mul_0_r, Z.add_0_r in Hsp.
    pose proof (lval_bound _ (limbs_firstn (bn_top b - 1) l Hll)) as Hlo. rewrite firstn_length_le in Hlo by lia.
    rewrite Bp_pow2 in *. set (k := 64 * Z.of_nat (bn_top b - 1)) in *.
    assert (Hk : 0 <= k) by (unfold k; lia).
    assert (Ek : (Z.of_nat (bn_top b) - 1) * 64 = k) by (unfold k; lia). rewrite Ek.
    split; [lia|]. split; [intros Hz; rewrite Hsp in Hz; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); nia|].
    split; [|unfold k; lia]. intros _.
    replace (k + num_bits_word t - 1) with (k + (num_bits_word t - 1)) by lia. rewrite !Z.pow_add_r by lia.
    pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). rewrite Hsp. split; nia.
Qed.

Lemma BN_num_bits_spec : forall r F s, (r < length (st_bns s))%nat ->
  hoare F s (BN_num_bits ops r) (fun a s' => s' = s /\ a = num_bits_pure (getbn r s)).
Proof.
  intros r F s Hr. apply hoare_wf. intros Hs. unfold BN_num_bits. apply hoare_bind_get.
  rewrite (st_wf_no_flag r s _ Hs Hr) by (left; reflexivity). apply hoare_ret. auto.
Qed.

Lemma BN_ucmp_spec : forall ra rb F s, (ra < length (st_bns s))%nat -> (rb < length (st_bns s))%nat ->
  hoare F s (BN_ucmp ops ra rb) (fun a s' => s' = s /\ a = ucmp_pure (getbn ra s) (getbn rb s)).
Proof.
  intros ra rb F s Ha Hb. apply hoare_wf. intros Hs. unfold BN_ucmp. apply hoare_bind_get. apply hoare_bind_get.
  rewrite (st_wf_no_flag ra s _ Hs Ha) by (left; reflexivity). rewrite (st_wf_no_flag rb s _ Hs Hb) by (left; reflexivity).
  apply hoare_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma ucmp_okv_spec : forall a b : BN, bg_okv a -> bg_okv b -> bn_norm a -> bn_norm b ->
  (0 < ucmp_pure a b -> bn_mag b < bn_mag a) /\ (ucmp_pure a b < 0 -> bn_mag a < bn_mag b) /\
  (ucmp_pure a b = 0 -> bn_mag a = bn_mag b).
Proof.
  intros a b (A1 & A2) (B1 & B2) Hna Hnb.
  set (a0 := mkBN (bn_d a) (bn_buf a) (bn_top a) (bn_neg a) 0).
  set (b0 := mkBN (bn_d b) (bn_buf b) (bn_top b) (bn_neg b) 0).
  (* [comment removed for export] *)
  set (a1 := mkBN (bn_d a) (firstn (bn_top a) (bn_buf a)) (bn_top a) (bn_neg a) 0).
  set (b1 := mkBN (bn_d b) (firstn (bn_top b) (bn_buf b)) (bn_top b) (bn_neg b) 0).
  assert (Hlt : forall c : BN, bg_okv c -> Z.of_nat (bn_top c) <= DMAX_MAX \/ DMAX_MAX < Z.of_nat (bn_top c)) by (intros; lia).
  assert (Eu : ucmp_pure a b = ucmp_pure a1 b1).
  { unfold ucmp_pure, a1, b1. cbn [bn_top bn_buf]. rewrite !firstn_firstn, !Nat.min_id. reflexivity. }
  assert (Ema : bn_mag a1 = bn_mag a) by (unfold bn_mag, a1; cbn [bn_top bn_buf]; rewrite firstn_firstn, Nat.min_id; reflexivity).
  assert (Emb : bn_mag b1 = bn_mag b) by (unfold bn_mag, b1; cbn [bn_top bn_buf]; rewrite firstn_firstn, Nat.min_id; reflexivity).
  rewrite Eu, <- Ema, <- Emb.
  (* [comment removed for export] *)
  unfold ucmp_pure. cbn [a1 b1 bn_top bn_buf]. rewrite !firstn_firstn, !Nat.min_id. rewrite Ema, Emb.
  destruct (Z.eqb_spec (Z.of_nat (bn_top a) - Z.of_nat (bn_top b)) 0) as [E|E].
  - assert (Et : bn_top a = bn_top b) by lia. unfold bn_dmax in *.
    rewrite cmp_words_spec by (try (apply limbs_firstn; assumption); rewrite !firstn_length_le by lia; exact Et).
    fold (bn_mag a) (bn_mag b).
    destruct (Z.lt_trichotomy (bn_mag a) (bn_mag b)) as [H|[H|H]];
      [rewrite (sgn3_lt _ _ H)|rewrite H, sgn3_eq|rewrite (sgn3_gt _ _ H)]; repeat split; intros; lia.
  - assert (Hge : forall c : BN, bg_okv c -> bn_norm c -> (0 < bn_top c)%nat -> Bp (bn_top c - 1) <= bn_mag c).
    { intros c (C1 & C2) [Hc|Hc] Hpos; [lia|]. unfold bn_mag.
      set (l := firstn (bn_top c) (bn_buf c)).
      assert (Hl : limbs l) by (apply limbs_firstn; exact C1).
      assert (Hll : length l = bn_top c) by (apply firstn_length_le; exact C2).
      pose proof (nth_limb_val l (bn_top c - 1) Hl ltac:(lia)) as En.
      assert (Enn : nth (bn_top c - 1) l 0 = nth (bn_top c - 1) (bn_buf c) 0).
      { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top c - 1) (bn_top c)); [reflexivity|lia]. }
      rewrite Enn in En. pose proof (limbs_nth (bn_buf c) (bn_top c - 1) C1) as [Hx0 _].
      pose proof (lval_nonneg _ (limbs_firstn (bn_top c - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (bn_top c - 1)) l Hl)).
      pose proof (Bp_pos (bn_top c - 1)). pose proof (Bp_pos (S (bn_top c - 1))). nia. }
    split; [|split]; intros H; try lia.
    + assert (Hlt' : (bn_top b < bn_top a)%nat) by lia.
      pose proof (okv_mag_lt b (conj B1 B2)). pose proof (Hge a (conj A1 A2) Hna ltac:(lia)). pose proof (Bp_mono (bn_top b) (bn_top a - 1) ltac:(lia)). lia.
    + assert (Hlt' : (bn_top a < bn_top b)%nat) by lia.
      pose proof (okv_mag_lt a (conj A1 A2)). pose proof (Hge b (conj B1 B2) Hnb ltac:(lia)). pose proof (Bp_mono (bn_top a) (bn_top b - 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bg_correct_top_ok : forall b : BN, bg_ok b ->
  let b' := bn_correct_top_pure b in
  bg_ok b' /\ bn_canon b' /\ bn_mag b' = bn_mag b /\ (bn_top b' <= bn_top b)%nat /\
  bn_buf b' = bn_buf b /\ bn_d b' = bn_d b /\ bn_neg b' = (bn_neg b && negb (bn_top b' =? 0)%nat).
Proof.
  intros b Hb. pose proof (bn_correct_top_ok b (bg_ok_bn_ok b Hb)) as H. cbv zeta in *.
  destruct H as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8). destruct Hb as (B1 & B2 & B3 & B4).
  split; [|repeat split; assumption || (destruct K2; assumption)].
  unfold bg_ok, bn_dmax in *. rewrite K5, K7. repeat split; try assumption. lia.
Qed.

Lemma correct_top_spec : forall r F s, (r < length (st_bns s))%nat -> r <> ROne ->
  hoare F s (bbind ops (bget ops r) (fun b => bset ops r (bn_correct_top_pure b)))
        (upd1 r s (fun b' => b' = bn_correct_top_pure (getbn r s))).
Proof.
  intros r F s Hr Hn. apply hoare_wf. intros Hs. apply hoare_bind_get.
  destruct (bg_correct_top_ok (getbn r s) (st_wf_ok r s Hs Hr Hn)) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  eapply hoare_set; try assumption.
  - rewrite K5. reflexivity.
  - eexists. split; reflexivity.
  - unfold bn_correct_top_pure. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_repeat_le : forall (a : Z) n m, (n <= m)%nat -> firstn n (repeat a m) = repeat a n.
Proof. induction n as [|n IH]; intros [|m] H; cbn; try lia; try reflexivity. f_equal. apply IH. lia. Qed.

Lemma lval_zeros_one : forall i x, lval (repeat 0 i ++ [x]) = Bp i * x.
Proof. intros i x. rewrite lval_app, lval_repeat0, repeat_length. cbn [lval]. lia. Qed.

Lemma upd_repeat0_last : forall i x, upd (repeat 0 (i + 1)) i x = repeat 0 i ++ [x].
Proof.
  intros i x. unfold upd, splice. rewrite firstn_repeat_le by lia. cbn [length].
  rewrite skipn_all2 by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma BN_set_bit_zero_spec : forall r n F s, (r < length (st_bns s))%nat -> r <> ROne -> 0 <= n -> n / 64 + 1 <= BG_DMAX ->
  bn_top (getbn r s) = 0%nat ->
  hoare F s (BN_set_bit ops r n) (upd1 r s (fun b' =>
     bn_mag b' = 2 ^ n /\ bn_norm b' /\ bn_top b' = (Z.to_nat (n / 64) + 1)%nat /\ bn_neg b' = bn_neg (getbn r s))).
Proof.
  intros r n F s Hr Hn Hn0 Hsz Ht0. apply hoare_wf. intros Hs. unfold BN_set_bit.
  destruct (Z.ltb_spec n 0); [lia|]. set (i := Z.to_nat (n / 64)). set (j := n mod 64).
  assert (Hi : 0 <= n / 64) by (apply Z.div_pos; lia).
  assert (Hj : 0 <= j < 64) by (apply Z.mod_pos_bound; lia).
  apply hoare_bind_get. rewrite Ht0. cbn [Nat.leb].
  eapply hoare_bind with (R := upd1 r s (fun b' => bn_top b' = (i + 1)%nat /\ bn_neg b' = bn_neg (getbn r s) /\
                                     firstn (i + 1) (bn_buf b') = repeat 0 (i + 1) /\ (i + 1 <= bn_dmax b')%nat)).
  - eapply hoare_bind; [apply bn_wexpand_spec; [exact Hr|exact Hn|unfold i; lia]|].
    intros [] s1 Hs1 (b1 & -> & Hb1). apply hoare_bind_get. rewrite getbn_setbn_same by exact Hr.
    destruct Hb1 as (E1 & E2 & E3 & E4 & Hok1 & Hd1 & Hd2). pose proof Hok1 as (O1 & O2 & O3 & O4).
    rewrite E1, Ht0, Nat.sub_0_r.
    assert (Hlen : length (splice (bn_buf b1) 0 (repeat 0 (i + 1))) = length (bn_buf b1))
      by (apply splice_length; rewrite repeat_length; unfold bn_dmax in Hd1; lia).
    eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax. cbn [bn_buf bn_top bn_flags]. rewrite Hlen.
      split; [apply splice_limbs; [exact O1|apply limbs_repeat; exact limb_0]|]. split; [unfold bn_dmax in Hd1; lia|split; assumption].
    + rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold bn_dmax. cbn [bn_top bn_neg bn_buf]. rewrite Hlen.
      split; [reflexivity|]. split; [exact E2|]. split; [|unfold bn_dmax in Hd1; lia].
      apply firstn_splice_0; [apply repeat_length|unfold bn_dmax in Hd1; lia].
  - intros [] s1 Hs1 (b1 & -> & T1 & T2 & T3 & T4). apply hoare_bind_get. rewrite getbn_setbn_same by exact Hr.
    pose proof (st_wf_ok r _ Hs1 ltac:(rewrite length_setbn; exact Hr) Hn) as Hok1. rewrite getbn_setbn_same in Hok1 by exact Hr.
    pose proof Hok1 as (O1 & O2 & O3 & O4).
    assert (Hni : nth i (bn_buf b1) 0 = 0).
    { rewrite <- (nth_of_firstn_eq (repeat 0 (i + 1)) (bn_buf b1) (i + 1) i) by (try lia; rewrite T3, firstn_repeat_le by lia; reflexivity).
      apply nth_repeat_lt. lia. }
    rewrite Hni. rewrite Z.lor_0_l.
    assert (Hp : 0 < 2 ^ j < BW) by (split; [apply Z.pow_pos_nonneg; lia|rewrite BW_pow; apply Z.pow_lt_mono_r; lia]).
    assert (Hlen : length (upd (bn_buf b1) i (2 ^ j)) = length (bn_buf b1)) by (apply upd_length; unfold bn_dmax in T4; lia).
    assert (Hfst : firstn (i + 1) (upd (bn_buf b1) i (2 ^ j)) = repeat 0 i ++ [2 ^ j]).
    { rewrite <- (splice_slice_id (bn_buf b1) 0 (i + 1)) by (unfold bn_dmax in T4; lia). rewrite slice_0, T3.
      assert (Eu : upd (splice (bn_buf b1) 0 (repeat 0 (i + 1))) i (2 ^ j) = splice (bn_buf b1) 0 (upd (repeat 0 (i + 1)) i (2 ^ j)))
        by (apply (upd_splice (bn_buf b1) 0 (repeat 0 (i + 1)) i (2 ^ j)); rewrite ?repeat_length; unfold bn_dmax in T4; lia).
      rewrite Eu, upd_repeat0_last. apply firstn_splice_0; [rewrite length_app, repeat_length; cbn; lia|unfold bn_dmax in T4; lia]. }
    eapply hoare_set; try rewrite length_setbn; try rewrite getbn_setbn_same by exact Hr; try assumption; try reflexivity.
    + unfold bg_ok, bn_dmax in *. cbn [bn_with_buf bn_buf bn_top bn_flags]. rewrite Hlen.
      split; [apply upd_limbs; [exact O1|unfold limb; lia]|]. split; [lia|split; assumption].
    + rewrite setbn_setbn_same. eexists. split; [reflexivity|]. unfold bn_mag, bn_norm. cbn [bn_with_buf bn_top bn_neg bn_buf].
      rewrite T1, Hfst, lval_zeros_one, Bp_pow2. split; [|split; [|split; [reflexivity|exact T2]]].
      * rewrite <- Z.pow_add_r by lia. f_equal. unfold i, j. rewrite Z2Nat.id by lia. pose proof (Z.div_mod n 64 ltac:(lia)). lia.
      * right. replace (i + 1 - 1)%nat with i by lia. rewrite nth_upd_same by (unfold bn_dmax in T4; lia). lia.
Qed.

End LibSpec.
