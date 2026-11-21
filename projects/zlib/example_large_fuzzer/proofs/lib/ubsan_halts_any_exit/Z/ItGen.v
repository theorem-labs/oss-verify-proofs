(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ItDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma sumn_ext : forall f g lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> f i = g i) -> sumn f lo n = sumn g lo n.
Proof.
  intros f g lo n. induction n as [|n IH]; intros H; cbn [sumn]; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumz_nil : forall f lo hi, hi <= lo -> sumz f lo hi = 0.
Proof. intros f lo hi H. unfold sumz. replace (Z.to_nat (hi - lo)) with 0%nat by lia. reflexivity. Qed.

Lemma sumz_snoc : forall f lo hi, lo <= hi -> sumz f lo (hi + 1) = sumz f lo hi + f hi.
Proof.
  intros f lo hi H. unfold sumz.
  replace (Z.to_nat (hi + 1 - lo)) with (S (Z.to_nat (hi - lo))) by lia.
  cbn [sumn]. f_equal. f_equal. lia.
Qed.

Lemma sumz_ext : forall f g lo hi,
  (forall i, lo <= i < hi -> f i = g i) -> sumz f lo hi = sumz g lo hi.
Proof.
  intros f g lo hi H. unfold sumz. apply sumn_ext. intros i Hi. apply H. lia.
Qed.

Lemma sumz_split : forall f lo mid hi,
  lo <= mid <= hi -> sumz f lo hi = sumz f lo mid + sumz f mid hi.
Proof.
  intros f lo mid hi H.
  remember (Z.to_nat (hi - mid)) as n eqn:Hn. revert hi H Hn.
  induction n as [|n IH]; intros hi H Hn.
  - assert (hi = mid) by lia. subst hi. rewrite (sumz_nil f mid mid) by lia. lia.
  - replace hi with ((hi - 1) + 1) by lia.
    rewrite (sumz_snoc f lo (hi - 1)) by lia. rewrite (sumz_snoc f mid (hi - 1)) by lia.
    rewrite (IH (hi - 1)) by lia. lia.
Qed.

Lemma sumz_one : forall f i, sumz f i (i + 1) = f i.
Proof. intros f i. rewrite sumz_snoc by lia. rewrite sumz_nil by lia. lia. Qed.

Lemma sumz_cons : forall f lo hi, lo < hi -> sumz f lo hi = f lo + sumz f (lo + 1) hi.
Proof.
  intros f lo hi H. rewrite (sumz_split f lo (lo + 1) hi) by lia. rewrite sumz_one. reflexivity.
Qed.

Lemma sumz_nonneg : forall f lo hi,
  (forall i, lo <= i < hi -> 0 <= f i) -> 0 <= sumz f lo hi.
Proof.
  intros f lo hi. remember (Z.to_nat (hi - lo)) as n eqn:Hn. revert hi Hn.
  induction n as [|n IH]; intros hi Hn H.
  - rewrite sumz_nil by lia. lia.
  - replace hi with ((hi - 1) + 1) by lia. rewrite sumz_snoc by lia.
    assert (0 <= f (hi - 1)) by (apply H; lia).
    assert (0 <= sumz f lo (hi - 1)) by (apply IH; [lia | intros; apply H; lia]). lia.
Qed.

Lemma sumz_mono_hi : forall f lo hi hi',
  (forall i, lo <= i < hi' -> 0 <= f i) -> lo <= hi <= hi' -> sumz f lo hi <= sumz f lo hi'.
Proof.
  intros f lo hi hi' H Hle. rewrite (sumz_split f lo hi hi') by lia.
  assert (0 <= sumz f hi hi') by (apply sumz_nonneg; intros; apply H; lia). lia.
Qed.

Lemma sumz_scale : forall f c lo hi,
  sumz (fun i => f i * c) lo hi = sumz f lo hi * c.
Proof.
  intros f c lo hi. remember (Z.to_nat (hi - lo)) as n eqn:Hn. revert hi Hn.
  induction n as [|n IH]; intros hi Hn.
  - rewrite !sumz_nil by lia. lia.
  - replace hi with ((hi - 1) + 1) by lia. rewrite !sumz_snoc by lia. rewrite IH by lia. lia.
Qed.

Lemma sumz_zero : forall f lo hi, (forall i, lo <= i < hi -> f i = 0) -> sumz f lo hi = 0.
Proof.
  intros f lo hi H. rewrite (sumz_ext f (fun _ => 0)) by exact H.
  remember (Z.to_nat (hi - lo)) as n eqn:Hn. revert hi Hn H.
  induction n as [|n IH]; intros hi Hn H.
  - apply sumz_nil. lia.
  - replace hi with ((hi - 1) + 1) by lia. rewrite sumz_snoc by lia. rewrite IH; [lia|lia|]. intros; apply H; lia.
Qed.

Lemma sumz_add : forall f g lo hi,
  sumz (fun i => f i + g i) lo hi = sumz f lo hi + sumz g lo hi.
Proof.
  intros f g lo hi. remember (Z.to_nat (hi - lo)) as n eqn:Hn. revert hi Hn.
  induction n as [|n IH]; intros hi Hn.
  - rewrite !sumz_nil by lia. lia.
  - replace hi with ((hi - 1) + 1) by lia. rewrite !sumz_snoc by lia. rewrite IH by lia. lia.
Qed.

Lemma sumz_indicator : forall x lo hi, lo <= hi ->
  sumz (fun i => if i =? x then 1 else 0) lo hi = (if (lo <=? x) && (x <? hi) then 1 else 0).
Proof.
  intros x lo hi H. remember (Z.to_nat (hi - lo)) as n eqn:Hn. revert hi H Hn.
  induction n as [|n IH]; intros hi H Hn.
  - rewrite sumz_nil by lia. destruct (Z.leb_spec lo x), (Z.ltb_spec x hi); cbn [andb]; lia.
  - replace hi with ((hi - 1) + 1) by lia. rewrite sumz_snoc by lia. rewrite IH by lia.
    destruct (Z.leb_spec lo x), (Z.ltb_spec x (hi - 1)), (Z.ltb_spec x (hi - 1 + 1)), (Z.eqb_spec (hi - 1) x); cbn [andb]; lia.
Qed.


Lemma zsearch_bound : forall p lo n, lo <= zsearch p lo n <= lo + Z.of_nat n.
Proof.
  intros p lo n. revert lo. induction n as [|n IH]; intros lo; cbn [zsearch]; [lia|].
  destruct (p lo); [lia|]. specialize (IH (lo + 1)). lia.
Qed.

Lemma zsearch_before : forall p lo n i, lo <= i < zsearch p lo n -> p i = false.
Proof.
  intros p lo n. revert lo. induction n as [|n IH]; intros lo i Hi; cbn [zsearch] in Hi; [lia|].
  destruct (p lo) eqn:E; [lia|].
  destruct (Z.eq_dec i lo) as [->|Hne]; [exact E|]. apply (IH (lo + 1)). lia.
Qed.

Lemma zsearch_found : forall p lo n, zsearch p lo n < lo + Z.of_nat n -> p (zsearch p lo n) = true.
Proof.
  intros p lo n. revert lo. induction n as [|n IH]; intros lo H; cbn [zsearch] in *; [lia|].
  destruct (p lo) eqn:E; [exact E|]. apply IH. lia.
Qed.

Lemma zsearch_eq : forall p lo n m,
  lo <= m < lo + Z.of_nat n -> p m = true -> (forall i, lo <= i < m -> p i = false) ->
  zsearch p lo n = m.
Proof.
  intros p lo n m Hm Hp Hb.
  pose proof (zsearch_bound p lo n) as B.
  destruct (Z.lt_total (zsearch p lo n) m) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
  - exfalso. assert (p (zsearch p lo n) = true) by (apply zsearch_found; lia).
    rewrite (Hb (zsearch p lo n)) in H by lia. discriminate H.
  - exfalso. pose proof (zsearch_before p lo n m ltac:(lia)) as E. rewrite Hp in E. discriminate E.
Qed.

Lemma zsearch_none : forall p lo n,
  (forall i, lo <= i < lo + Z.of_nat n -> p i = false) -> zsearch p lo n = lo + Z.of_nat n.
Proof.
  intros p lo n H. pose proof (zsearch_bound p lo n) as B.
  destruct (Z.eq_dec (zsearch p lo n) (lo + Z.of_nat n)) as [E|E]; [exact E|].
  exfalso. assert (p (zsearch p lo n) = true) by (apply zsearch_found; lia).
  rewrite H in H0 by lia. discriminate H0.
Qed.

Lemma zsearch_cases : forall p lo n,
  zsearch p lo n = lo + Z.of_nat n \/ (zsearch p lo n < lo + Z.of_nat n /\ p (zsearch p lo n) = true).
Proof.
  intros p lo n. pose proof (zsearch_bound p lo n).
  destruct (Z.eq_dec (zsearch p lo n) (lo + Z.of_nat n)); [left; lia|right].
  split; [lia|]. apply zsearch_found. lia.
Qed.


Lemma applyw_cons : forall i v ws a, applyw ((i, v) :: ws) a = applyw ws (arr_set a i v).
Proof. reflexivity. Qed.
Lemma applyw_app : forall ws1 ws2 a, applyw (ws1 ++ ws2) a = applyw ws2 (applyw ws1 a).
Proof. intros. unfold applyw. apply fold_left_app. Qed.
Lemma applyw_snoc : forall ws i v a, applyw (ws ++ [(i, v)]) a = arr_set (applyw ws a) i v.
Proof. intros. rewrite applyw_app. reflexivity. Qed.

Lemma arr_len_applyw : forall ws a, arr_len (applyw ws a) = arr_len a.
Proof.
  induction ws as [|[i v] ws IH]; intros a; [reflexivity|].
  rewrite applyw_cons, IH. apply arr_len_set.
Qed.

Lemma applyw_other : forall ws a i,
  (forall v, ~ In (i, v) ws) -> arr_get (applyw ws a) i = arr_get a i.
Proof.
  induction ws as [|[j w] ws IH]; intros a i H; [reflexivity|].
  rewrite applyw_cons. rewrite IH.
  - apply arr_get_set_other. intros ->. apply (H w). left; reflexivity.
  - intros v Hv. apply (H v). right; exact Hv.
Qed.

Lemma applyw_in : forall ws a i,
  In i (map fst ws) -> 0 <= i < arr_len a ->
  exists v, In (i, v) ws /\ arr_get (applyw ws a) i = v.
Proof.
  intros ws. induction ws as [|[j w] ws IH] using rev_ind; intros a i Hin Hr.
  - destruct Hin.
  - rewrite map_app in Hin. cbn [map fst] in Hin. rewrite applyw_snoc.
    destruct (Z.eq_dec j i) as [->|Hne].
    + exists w. split; [apply in_app_iff; right; left; reflexivity|].
      apply arr_get_set_same. rewrite arr_len_applyw. exact Hr.
    + apply in_app_iff in Hin. destruct Hin as [Hin|[Hin|[]]]; [|cbn in Hin; lia].
      destruct (IH a i Hin Hr) as [v [Hv Hg]]. exists v. split; [apply in_app_iff; left; exact Hv|].
      rewrite arr_get_set_other by exact Hne. exact Hg.
Qed.

Lemma applyw_all : forall (P : Z -> Z -> Prop) ws a i,
  (forall j v, In (j, v) ws -> P j v) ->
  In i (map fst ws) -> 0 <= i < arr_len a -> P i (arr_get (applyw ws a) i).
Proof.
  intros P ws a i HP Hin Hr. destruct (applyw_in ws a i Hin Hr) as [v [Hv ->]]. apply HP. exact Hv.
Qed.

Lemma applyw_agree : forall ws a1 a2 i,
  arr_len a1 = arr_len a2 -> In i (map fst ws) -> 0 <= i < arr_len a1 ->
  arr_get (applyw ws a1) i = arr_get (applyw ws a2) i.
Proof.
  intros ws. induction ws as [|[j w] ws IH] using rev_ind; intros a1 a2 i HL Hin Hr.
  - destruct Hin.
  - rewrite !applyw_snoc. rewrite map_app in Hin.
    destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite !arr_get_set_same by (rewrite arr_len_applyw; lia). reflexivity.
    + apply in_app_iff in Hin. destruct Hin as [Hin|[Hin|[]]]; [|cbn in Hin; lia].
      rewrite !arr_get_set_other by exact Hne. apply IH; assumption.
Qed.

Lemma in_map_fst : forall (ws : list (Z * Z)) i v, In (i, v) ws -> In i (map fst ws).
Proof. intros ws i v H. apply in_map_iff. exists (i, v). split; [reflexivity|exact H]. Qed.


Lemma brev_bound : forall w c, 0 <= brev w c < 2 ^ Z.of_nat w.
Proof.
  induction w as [|w IH]; intros c; cbn [brev].
  - cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. specialize (IH (c / 2)).
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)). nia.
Qed.

Lemma brev_0 : forall w, brev w 0 = 0.
Proof. induction w as [|w IH]; cbn [brev]; [reflexivity|]. rewrite Zdiv_0_l, IH. reflexivity. Qed.

Lemma brev_split : forall w1 w2 c, 0 <= c ->
  brev (w1 + w2) c = brev w1 (c mod 2 ^ Z.of_nat w1) * 2 ^ Z.of_nat w2 + brev w2 (c / 2 ^ Z.of_nat w1).
Proof.
  induction w1 as [|w1 IH]; intros w2 c Hc.
  - cbn [brev Nat.add]. change (2 ^ Z.of_nat 0) with 1. rewrite Z.div_1_r. lia.
  - cbn [brev Nat.add]. rewrite IH by (apply Z.div_pos; lia).
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    set (A := 2 ^ Z.of_nat w1). set (B := 2 ^ Z.of_nat w2).
    assert (HA : 0 < A) by (subst A; apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hm.
    pose proof (Z.rem_mul_r c 2 A ltac:(lia) ltac:(lia)) as Hr.
    set (X := (c / 2) mod A) in *.
    assert (E1 : (c mod (2 * A)) mod 2 = c mod 2).
    { rewrite Hr. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
    assert (E2 : (c mod (2 * A)) / 2 = X).
    { rewrite Hr. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    rewrite E1, E2. rewrite Z.div_div by lia. lia.
Qed.

Lemma brev_brev : forall w c, 0 <= c < 2 ^ Z.of_nat w -> brev w (brev w c) = c.
Proof.
  induction w as [|w IH]; intros c Hc.
  - cbn in *. lia.
  - change (brev (S w) (brev (S w) c)) with (brev (S w) ((c mod 2) * 2 ^ Z.of_nat w + brev w (c / 2))).
    replace (S w) with (w + 1)%nat by lia.
    pose proof (brev_bound w (c / 2)) as Bb.
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hm.
    rewrite brev_split by nia.
    set (A := 2 ^ Z.of_nat w) in *.
    assert (HA : 0 < A) by (subst A; apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hc by lia.
    replace ((c mod 2 * A + brev w (c / 2)) mod A) with (brev w (c / 2)).
    2:{ rewrite Z.add_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
    replace ((c mod 2 * A + brev w (c / 2)) / A) with (c mod 2).
    2:{ rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    rewrite IH by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    cbn [brev]. change (2 ^ Z.of_nat 0) with 1. rewrite Z.mul_1_r.
    rewrite (Z.mod_small (c mod 2) 2) by lia.
    pose proof (Z.div_mod c 2 ltac:(lia)). lia.
Qed.

Lemma brev_inj : forall w c1 c2,
  0 <= c1 < 2 ^ Z.of_nat w -> 0 <= c2 < 2 ^ Z.of_nat w -> brev w c1 = brev w c2 -> c1 = c2.
Proof.
  intros w c1 c2 H1 H2 E. rewrite <- (brev_brev w c1), <- (brev_brev w c2) by assumption. rewrite E. reflexivity.
Qed.

Lemma rev_bound : forall w c, 0 <= w -> 0 <= rev w c < 2 ^ w.
Proof. intros w c Hw. unfold rev. pose proof (brev_bound (Z.to_nat w) c). rewrite Z2Nat.id in H by lia. exact H. Qed.

Lemma rev_0 : forall w, rev w 0 = 0.
Proof. intros. unfold rev. apply brev_0. Qed.

Lemma rev_rev : forall w c, 0 <= w -> 0 <= c < 2 ^ w -> rev w (rev w c) = c.
Proof. intros w c Hw Hc. unfold rev. apply brev_brev. rewrite Z2Nat.id by lia. exact Hc. Qed.

Lemma rev_inj : forall w c1 c2, 0 <= w ->
  0 <= c1 < 2 ^ w -> 0 <= c2 < 2 ^ w -> rev w c1 = rev w c2 -> c1 = c2.
Proof.
  intros w c1 c2 Hw H1 H2 E. unfold rev in E. apply (brev_inj (Z.to_nat w)); rewrite ?Z2Nat.id by lia; assumption.
Qed.

Lemma rev_split : forall w1 w2 c, 0 <= w1 -> 0 <= w2 -> 0 <= c ->
  rev (w1 + w2) c = rev w1 (c mod 2 ^ w1) * 2 ^ w2 + rev w2 (c / 2 ^ w1).
Proof.
  intros w1 w2 c H1 H2 Hc. unfold rev.
  replace (Z.to_nat (w1 + w2)) with (Z.to_nat w1 + Z.to_nat w2)%nat by lia.
  rewrite brev_split by exact Hc. rewrite !Z2Nat.id by lia. reflexivity.
Qed.

Lemma rev_mod : forall w w2 c, 0 <= w2 <= w -> 0 <= c ->
  rev w c mod 2 ^ w2 = rev w2 (c / 2 ^ (w - w2)).
Proof.
  intros w w2 c Hw Hc. replace w with ((w - w2) + w2) at 1 by lia.
  rewrite rev_split by lia.
  rewrite Z.add_comm, Z.mod_add by (apply Z.pow_nonzero; lia).
  apply Z.mod_small. apply rev_bound. lia.
Qed.

Lemma rev_div : forall w w2 c, 0 <= w2 <= w -> 0 <= c ->
  rev w c / 2 ^ w2 = rev (w - w2) (c mod 2 ^ (w - w2)).
Proof.
  intros w w2 c Hw Hc. replace w with ((w - w2) + w2) at 1 by lia.
  rewrite rev_split by lia.
  rewrite Z.add_comm, Z.div_add by (apply Z.pow_nonzero; lia).
  rewrite Z.div_small by (apply rev_bound; lia). lia.
Qed.

Lemma rev_shift : forall w d c, 0 <= w -> 0 <= d -> 0 <= c ->
  rev (w + d) (c * 2 ^ d) = rev w c.
Proof.
  intros w d c Hw Hd Hc. replace (w + d) with (d + w) by lia.
  rewrite rev_split by nia.
  rewrite Z.mod_mul by (apply Z.pow_nonzero; lia). rewrite rev_0.
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
Qed.

Lemma rev_S : forall w c, 0 <= w -> 0 <= c ->
  rev (w + 1) c = (c mod 2) * 2 ^ w + rev w (c / 2).
Proof.
  intros w c Hw Hc. replace (w + 1) with (1 + w) by lia. rewrite rev_split by lia.
  change (2 ^ 1) with 2. f_equal. f_equal.
  unfold rev. change (Z.to_nat 1) with 1%nat. cbn [brev]. change (2 ^ Z.of_nat 0) with 1.
  pose proof (Z.mod_pos_bound c 2 ltac:(lia)). rewrite (Z.mod_small (c mod 2) 2) by lia. lia.
Qed.


Lemma land_ones' : forall a n, 0 <= n -> Z.land a (2 ^ n - 1) = a mod 2 ^ n.
Proof.
  intros a n Hn. rewrite <- Z.land_ones by exact Hn. f_equal.
  unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma testbit_odd_div : forall a n, 0 <= n -> Z.testbit a n = Z.odd (a / 2 ^ n).
Proof.
  intros a n Hn. rewrite <- (Z.shiftr_div_pow2 a n) by lia.
  rewrite <- (Z.add_0_l n) at 1. rewrite <- Z.shiftr_spec by lia. apply Z.bit0_odd.
Qed.

Lemma land_pow2_eq0 : forall a n, 0 <= n ->
  (Z.land a (2 ^ n) =? 0) = negb (Z.odd (a / 2 ^ n)).
Proof.
  intros a n Hn.
  destruct (Z.odd (a / 2 ^ n)) eqn:E; cbn [negb].
  - apply Z.eqb_neq. intros H.
    apply (f_equal (fun z => Z.testbit z n)) in H.
    rewrite Z.land_spec, Z.pow2_bits_true, Z.bits_0 in H by lia.
    rewrite testbit_odd_div, E in H by lia. discriminate H.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros m Hm.
    rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec n m) as [<-|Hne]; [|apply Bool.andb_false_r].
    rewrite testbit_odd_div, E by lia. reflexivity.
Qed.

Lemma wrap8_small : forall z, 0 <= z < 256 -> wrap8 z = z.
Proof. intros z H. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_small. lia. Qed.
Lemma wrap16_small : forall z, 0 <= z < 65536 -> wrap16 z = z.
Proof. intros z H. unfold wrap16. change 65535 with (2 ^ 16 - 1). rewrite land_ones' by lia. apply Z.mod_small. lia. Qed.
Lemma wrap32_small : forall z, 0 <= z < 4294967296 -> wrap32 z = z.
Proof. intros z H. unfold wrap32. change 4294967295 with (2 ^ 32 - 1). rewrite land_ones' by lia. apply Z.mod_small. lia. Qed.
Lemma shl32_pow2 : forall n, 0 <= n < 32 -> shl32 1 n = 2 ^ n.
Proof.
  intros n H. unfold shl32. rewrite Z.shiftl_1_l. apply wrap32_small.
  split; [apply Z.pow_nonneg; lia|]. change 4294967296 with (2 ^ 32). apply Z.pow_lt_mono_r; lia.
Qed.
Lemma swrap32_small : forall z, 0 <= z < 2147483648 -> swrap32 z = z.
Proof. intros z H. unfold swrap32, two31. rewrite wrap32_small by lia. lia. Qed.

Lemma pow2_le_15 : forall n, 0 <= n <= 15 -> 1 <= 2 ^ n <= 32768.
Proof.
  intros n H. split. 
  - change 1 with (2 ^ 0). apply Z.pow_le_mono_r; lia.
  - change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia.
Qed.

Lemma code_op_pack : forall op bits val, code_op (code_pack op bits val) = wrap8 op.
Proof.
  intros op bits val. unfold code_op, code_pack.
  assert (H8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  assert (H16 : forall z, 0 <= wrap16 z < 65536).
  { intros z. unfold wrap16. change 65535 with (2 ^ 16 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  pose proof (H8 op). pose proof (H8 bits). pose proof (H16 val).
  change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with (wrap8 op + (wrap8 bits + 256 * wrap16 val) * 2 ^ 8) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma code_bits_pack : forall op bits val, code_bits (code_pack op bits val) = wrap8 bits.
Proof.
  intros op bits val. unfold code_bits, code_pack.
  assert (H8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  assert (H16 : forall z, 0 <= wrap16 z < 65536).
  { intros z. unfold wrap16. change 65535 with (2 ^ 16 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  pose proof (H8 op). pose proof (H8 bits). pose proof (H16 val).
  change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with (wrap8 op + (wrap8 bits + wrap16 val * 2 ^ 8) * 2 ^ 8) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma code_val_pack : forall op bits val, code_val (code_pack op bits val) = wrap16 val.
Proof.
  intros op bits val. unfold code_val, code_pack.
  assert (H8 : forall z, 0 <= wrap8 z < 256).
  { intros z. unfold wrap8. change 255 with (2 ^ 8 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  assert (H16 : forall z, 0 <= wrap16 z < 65536).
  { intros z. unfold wrap16. change 65535 with (2 ^ 16 - 1). rewrite land_ones' by lia. apply Z.mod_pos_bound. lia. }
  pose proof (H8 op). pose proof (H8 bits). pose proof (H16 val).
  change 65535 with (2 ^ 16 - 1). rewrite land_ones' by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (wrap8 op + 256 * wrap8 bits + 65536 * wrap16 val) with ((wrap8 op + 256 * wrap8 bits) + wrap16 val * 2 ^ 16) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.
