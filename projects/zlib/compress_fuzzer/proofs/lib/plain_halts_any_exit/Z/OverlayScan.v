(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayHuff1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayBlock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition E1 (r : Z) : Z :=
  if r <=? 3 then r else if r <=? 6 then 1 else 1 + (let u := (r - 7) mod 6 in if u <? 3 then u else 0).
Definition M1 (r : Z) : Z :=
  if r <=? 3 then 0 else if r <=? 6 then 1 else 1 + (r - 7) / 6 + (let u := (r - 7) mod 6 in if 3 <=? u then 1 else 0).

Definition e0 (r : Z) : Z := let u := r mod 138 in if u <? 3 then u else 0.
Definition e17 (r : Z) : Z := let u := r mod 138 in if (3 <=? u) && (u <=? 10) then 1 else 0.
Definition e18 (r : Z) : Z := let u := r mod 138 in r / 138 + (if 11 <=? u then 1 else 0).

Definition RUN (v r x : Z) : Z :=
  if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? REPZ_3_10) + e18 r * zind (x =? REPZ_11_138)
  else E1 r * zind (x =? v) + M1 r * zind (x =? REP_3_6).

Lemma E1_M1_facts : forall r, 1 <= r -> 0 <= E1 r <= r /\ 0 <= M1 r /\ E1 r + 3 * M1 r <= r /\ 4 * M1 r <= r.
Proof.
  intros r Hr. unfold E1, M1.
  destruct (Z.leb_spec r 3); [lia|]. destruct (Z.leb_spec r 6); [lia|].
  pose proof (Z.div_mod (r - 7) 6 ltac:(lia)). pose proof (Z.mod_pos_bound (r - 7) 6 ltac:(lia)).
  set (u := (r - 7) mod 6) in *. set (q := (r - 7) / 6) in *.
  destruct (Z.ltb_spec u 3); destruct (Z.leb_spec 3 u); lia.
Qed.

Lemma e_facts : forall r, 1 <= r -> 0 <= e0 r <= 2 /\ 0 <= e17 r <= 1 /\ 0 <= e18 r /\ e0 r + 3 * e17 r + 11 * e18 r <= r.
Proof.
  intros r Hr. unfold e0, e17, e18.
  pose proof (Z.div_mod r 138 ltac:(lia)). pose proof (Z.mod_pos_bound r 138 ltac:(lia)).
  set (u := r mod 138) in *. set (q := r / 138) in *.
  destruct (Z.ltb_spec u 3); destruct (Z.leb_spec 3 u); destruct (Z.leb_spec u 10); destruct (Z.leb_spec 11 u); cbn [andb]; lia.
Qed.

Lemma mod_div_138 : forall r, 1 <= r <= 276 ->
  (r < 138 /\ r mod 138 = r /\ r / 138 = 0) \/ (r = 138 /\ r mod 138 = 0 /\ r / 138 = 1)
  \/ (138 < r < 276 /\ r mod 138 = r - 138 /\ r / 138 = 1) \/ (r = 276 /\ r mod 138 = 0 /\ r / 138 = 2).
Proof.
  intros r Hr.
  destruct (Z_lt_le_dec r 138) as [A|A].
  - left. rewrite Z.mod_small, Z.div_small by lia. lia.
  - destruct (Z.eq_dec r 138) as [->|B]; [right; left; repeat split; reflexivity|].
    destruct (Z.eq_dec r 276) as [->|C]; [right; right; right; repeat split; reflexivity|].
    right; right; left. split; [lia|]. split.
    + symmetry. apply (Z.mod_unique_pos r 138 1); lia.
    + symmetry. apply (Z.div_unique_pos r 138 1 (r - 138)); lia.
Qed.

Lemma e0_is12 : forall r, 1 <= r <= 276 -> e0 r = is1 r + 2 * is2 r.
Proof.
  intros r Hr. unfold e0, is1, is2, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity].
  - destruct (Z.ltb_spec r 3); destruct (Z.eqb_spec r 1); destruct (Z.eqb_spec r 2); lia.
  - destruct (Z.ltb_spec (r - 138) 3); destruct (Z.eqb_spec (r - 138) 1); destruct (Z.eqb_spec (r - 138) 2); lia.
Qed.

Lemma e17_isa : forall r, 1 <= r <= 276 -> e17 r = isa r.
Proof.
  intros r Hr. unfold e17, isa, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity]; reflexivity.
Qed.

Lemma e18_isb : forall r, 1 <= r <= 276 -> e18 r = isb r + nlong r.
Proof.
  intros r Hr. unfold e18, isb, nlong, rem138.
  destruct (mod_div_138 r Hr) as [(A & B & C)|[(A & B & C)|[(A & B & C)|(A & B & C)]]]; rewrite B, C;
    [replace (138 <? r) with false by (symmetry; apply Z.ltb_ge; lia) | subst r; reflexivity
    | replace (138 <? r) with true by (symmetry; apply Z.ltb_lt; lia) | subst r; reflexivity].
  - destruct (Z.leb_spec 11 r); lia.
  - destruct (Z.leb_spec 11 (r - 138)); lia.
Qed.

Fixpoint zr (L : Z -> Z) (i : Z) (n : nat) (cur : Z) : list Z :=
  match n with
  | O => if cur =? 0 then [] else [cur]
  | S k => if L i =? 0 then zr L (i + 1) k (cur + 1)
           else (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) k 0
  end.

Lemma zruns_go_lsum : forall f L n i cur acc, lsum f (zruns_go L i n cur acc) = lsum f acc + lsum f (zr L i n cur).
Proof.
  intros f L. induction n as [|n IH]; intros i cur acc; cbn [zruns_go zr].
  - destruct (cur =? 0); cbn; lia.
  - destruct (L i =? 0); [apply IH|]. rewrite IH, lsum_app. destruct (cur =? 0); cbn; lia.
Qed.

Lemma zruns_lsum : forall f L lo n, lsum f (zruns L lo n) = lsum f (zr L lo n 0).
Proof. intros. unfold zruns. rewrite zruns_go_lsum. cbn. lia. Qed.

Lemma zr_zeros : forall L c m i cur, (forall j, i <= j < i + Z.of_nat c -> L j = 0) ->
  zr L i (c + m) cur = zr L (i + Z.of_nat c) m (cur + Z.of_nat c).
Proof.
  intros L. induction c as [|c IH]; intros m i cur Hz.
  - cbn [Nat.add]. rewrite !Z.add_0_r. reflexivity.
  - cbn [Nat.add zr]. rewrite (proj2 (Z.eqb_eq _ _) (Hz i ltac:(lia))).
    rewrite (IH m (i + 1) (cur + 1)) by (intros; apply Hz; lia). f_equal; lia.
Qed.

Lemma zr_nonzero : forall L m i cur, L i <> 0 -> zr L i (S m) cur = (if cur =? 0 then [] else [cur]) ++ zr L (i + 1) m 0.
Proof. intros L m i cur H. cbn [zr]. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma zr_end : forall L i cur, zr L i 0 cur = (if cur =? 0 then [] else [cur]).
Proof. reflexivity. Qed.

Lemma zr_sum : forall L n i cur, 0 <= cur ->
  lsum (fun r => r) (zr L i n cur) = cur + zsum (fun j => zind (L j =? 0)) i n.
Proof.
  intros L. induction n as [|n IH]; intros i cur Hc; cbn [zr].
  - cbn [zsum]. destruct (Z.eqb_spec cur 0); cbn; lia.
  - rewrite zsum_shift. cbv beta. destruct (Z.eqb_spec (L i) 0); cbn [zind].
    + rewrite IH by lia. lia.
    + rewrite lsum_app, IH by lia. destruct (Z.eqb_spec cur 0); cbn; lia.
Qed.

Lemma zr_split : forall f L a b i cur, L (i + Z.of_nat a) <> 0 ->
  lsum f (zr L i (a + S b) cur) = lsum f (zr L i a cur) + lsum f (zr L (i + Z.of_nat a + 1) b 0).
Proof.
  intros f L. induction a as [|a IH]; intros b i cur Hnz.
  - cbn [Nat.add]. rewrite Z.add_0_r in Hnz |- *. rewrite zr_nonzero, lsum_app, zr_end by exact Hnz. reflexivity.
  - cbn [Nat.add zr]. destruct (L i =? 0).
    + rewrite (IH b (i + 1) (cur + 1)) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      f_equal. f_equal. f_equal. lia.
    + rewrite !lsum_app, (IH b (i + 1) 0) by (replace (i + 1 + Z.of_nat a) with (i + Z.of_nat (S a)) by lia; exact Hnz).
      replace (i + 1 + Z.of_nat a + 1) with (i + Z.of_nat (S a) + 1) by lia. lia.
Qed.

Lemma zruns_sum : forall L lo n, lsum (fun r => r) (zruns L lo n) = zsum (fun j => zind (L j =? 0)) lo n.
Proof. intros. rewrite zruns_lsum, zr_sum by lia. lia. Qed.

Lemma zruns_pos : forall L lo n r, In r (zruns L lo n) -> 1 <= r <= Z.of_nat n.
Proof.
  intros L lo n r Hr. unfold zruns in Hr.
  assert (G : forall m i cur acc B, 0 <= cur -> cur + Z.of_nat m <= B -> (forall x, In x acc -> 1 <= x <= B) ->
             forall x, In x (zruns_go L i m cur acc) -> 1 <= x <= B).
  { induction m as [|m IH]; intros i cur acc B Hc HB Hacc x Hx; cbn [zruns_go] in Hx.
    - destruct (Z.eqb_spec cur 0); [exact (Hacc x Hx)|]. destruct Hx as [<-|Hx]; [lia | exact (Hacc x Hx)].
    - destruct (L i =? 0).
      + exact (IH (i + 1) (cur + 1) acc B ltac:(lia) ltac:(lia) Hacc x Hx).
      + apply (IH (i + 1) 0 (if cur =? 0 then acc else cur :: acc) B ltac:(lia) ltac:(lia)); [| exact Hx].
        intros y Hy. destruct (Z.eqb_spec cur 0); [exact (Hacc y Hy)|]. destruct Hy as [<-|Hy]; [lia | exact (Hacc y Hy)]. }
  exact (G n lo 0 [] (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(intros x Hx; destruct Hx) r Hr).
Qed.

Lemma zruns_split : forall f L lo a b, L (lo + Z.of_nat a) <> 0 ->
  lsum f (zruns L lo (a + S b)) = lsum f (zruns L lo a) + lsum f (zruns L (lo + Z.of_nat a + 1) b).
Proof. intros. rewrite !zruns_lsum. apply zr_split. exact H. Qed.

Section Scan.
Variable L : Z -> Z.
Variable mc : Z.
Hypothesis Hmc : 0 <= mc.
Hypothesis HL : forall i, 0 <= i <= mc -> 0 <= L i <= 15.
Hypothesis HG : 15 < L (mc + 1).

Definition TC (n p q k mx mn x : Z) : Z := td_cnt L mc (Z.to_nat (mc + 1 - n)) n p q k mx mn x.

Lemma TC_end : forall n p q k mx mn x, mc < n -> TC n p q k mx mn x = 0.
Proof. intros. unfold TC. replace (Z.to_nat (mc + 1 - n)) with 0%nat by lia. reflexivity. Qed.

Lemma TC_step : forall n p q k mx mn x, n <= mc ->
  TC n p q k mx mn x =
    (if (k + 1 <? mx) && (q =? L (n + 1)) then TC (n + 1) p (L (n + 1)) (k + 1) mx mn x
     else trip_cnt mn q p (k + 1) x + (let '(mx', mn') := tree_counts q (L (n + 1)) in TC (n + 1) q (L (n + 1)) 0 mx' mn' x)).
Proof.
  intros n p q k mx mn x Hn. unfold TC. replace (Z.to_nat (mc + 1 - n)) with (S (Z.to_nat (mc + 1 - (n + 1)))) by lia.
  cbn [td_cnt]. replace (n <=? mc) with true by (symmetry; apply Z.leb_le; lia).
  destruct (_ && _); [reflexivity|]. destruct (tree_counts q (L (n + 1))); reflexivity.
Qed.

Lemma TDcnt_TC : forall x, TDcnt L mc x = (let '(mx, mn) := tree_counts (-1) (L 0) in TC 0 (-1) (L 0) 0 mx mn x).
Proof.
  intros x. unfold TDcnt, TC, cnts0, tree_counts. pose proof (HL 0 ltac:(lia)).
  replace (-1 =? L 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.sub_0_r. reflexivity.
Qed.

Definition TCs (n p x : Z) : Z := let '(mx, mn) := tree_counts p (L n) in TC n p (L n) 0 mx mn x.

Lemma chunk : forall (c : nat) n p v k mx mn x,
  (1 <= c)%nat -> n + Z.of_nat c - 1 <= mc -> (forall i, n <= i < n + Z.of_nat c -> L i = v) ->
  k + Z.of_nat c <= mx -> (k + Z.of_nat c = mx \/ L (n + Z.of_nat c) <> v) ->
  TC n p v k mx mn x = trip_cnt mn v p (k + Z.of_nat c) x + TCs (n + Z.of_nat c) v x.
Proof.
  induction c as [|c IH]; intros n p v k mx mn x Hc Hn Hv Hk Hstop; [lia|].
  rewrite TC_step by lia.
  destruct c as [|c'].
  - cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *. replace ((k + 1 <? mx) && (v =? L (n + 1))) with false.
    + unfold TCs. reflexivity.
    + symmetry. destruct Hstop as [E|N]; [apply andb_false_intro1; apply Z.ltb_ge; lia | apply andb_false_intro2; apply Z.eqb_neq; exact (fun H => N (eq_sym H))].
  - assert (E1' : L (n + 1) = v) by (apply Hv; lia).
    replace ((k + 1 <? mx) && (v =? L (n + 1))) with true by (symmetry; apply andb_true_intro; split; [apply Z.ltb_lt; lia | apply Z.eqb_eq; symmetry; exact E1']).
    rewrite E1'. rewrite (IH (n + 1) p v (k + 1) mx mn x ltac:(lia) ltac:(lia)); [| intros; apply Hv; lia | lia | ].
    + f_equal; [f_equal; lia | f_equal; lia].
    + destruct Hstop as [E|N]; [left; lia | right]. replace (n + 1 + Z.of_nat (S c')) with (n + Z.of_nat (S (S c'))) by lia. exact N.
Qed.

Lemma trip_short : forall mn q p k x, k < mn -> trip_cnt mn q p k x = k * zind (x =? q).
Proof. intros. unfold trip_cnt. replace (k <? mn) with true by (symmetry; apply Z.ltb_lt; lia). destruct (x =? q); cbn; lia. Qed.

Lemma trip_rep_new : forall mn q p k x, mn <= k -> q <> 0 -> q <> p -> trip_cnt mn q p k x = zind (x =? q) + zind (x =? REP_3_6).
Proof.
  intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (q =? p) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma trip_rep_same : forall mn q k x, mn <= k -> q <> 0 -> trip_cnt mn q q k x = zind (x =? REP_3_6).
Proof.
  intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma trip_z : forall mn p k x, mn <= k -> trip_cnt mn 0 p k x = if k <=? 10 then zind (x =? REPZ_3_10) else zind (x =? REPZ_11_138).
Proof. intros. unfold trip_cnt. replace (k <? mn) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma run_cont : forall (m : nat) t n v x, 1 <= t <= 6 * Z.of_nat m -> 1 <= v <= 15 ->
  n + t - 1 <= mc -> (forall i, n <= i < n + t -> L i = v) -> L (n + t) <> v -> L n = v ->
  TC n v v 0 6 3 x =
    (t / 6) * zind (x =? REP_3_6) + (let u := t mod 6 in if u =? 0 then 0 else if u <? 3 then u * zind (x =? v) else zind (x =? REP_3_6))
    + TCs (n + t) v x.
Proof.
  induction m as [|m IH]; intros t n v x Ht Hv Hn Hrun Hend Hn0; [lia|].
  destruct (Z_lt_le_dec t 6) as [T6|T6].
  - rewrite (chunk (Z.to_nat t) n v v 0 6 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia. rewrite Z.div_small, Z.mod_small by lia. cbv zeta.
    replace (t =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.ltb_spec t 3).
    + rewrite trip_short by lia. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + rewrite trip_rep_same by lia. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
  - rewrite (chunk 6 n v v 0 6 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 6) with 6. rewrite trip_rep_same by lia. change (0 + 6) with 6.
    pose proof (Z.div_mod t 6 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound t 6 ltac:(lia)) as MB.
    assert (D6 : (t - 6) / 6 = t / 6 - 1) by (Z.to_euclidean_division_equations; lia).
    assert (M6 : (t - 6) mod 6 = t mod 6) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec t 6) as [->|N6].
    +
      unfold TCs. change (6 / 6) with 1. change (6 mod 6) with 0. cbn [Z.eqb Pos.eqb]. destruct (x =? REP_3_6); cbn [zind]; lia.
    +
      unfold TCs at 1. rewrite (Hrun (n + 6)) by lia. unfold tree_counts.
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
      rewrite (IH (t - 6) (n + 6) v x ltac:(lia) Hv ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 6 + (t - 6)) with (n + t) by lia; exact Hend | apply Hrun; lia].
      rewrite D6, M6. replace (n + 6 + (t - 6)) with (n + t) by lia. cbv zeta.
      destruct (x =? REP_3_6); destruct (x =? v); destruct (t mod 6 =? 0); destruct (t mod 6 <? 3); cbn [zind]; lia.
Qed.

Lemma run_nz : forall r n p v x, 1 <= r -> 1 <= v <= 15 -> p <> v ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = v) -> L (n + r) <> v -> L n = v ->
  TCs n p x = E1 r * zind (x =? v) + M1 r * zind (x =? REP_3_6) + TCs (n + r) v x.
Proof.
  intros r n p v x Hr Hv Hpv Hn Hrun Hend Hn0.
  unfold TCs at 1. rewrite Hn0. unfold tree_counts.
  replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (p =? v) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold E1, M1.
  destruct (Z_lt_le_dec r 7) as [R7|R7].
  - rewrite (chunk (Z.to_nat r) n p v 0 7 4 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia.
    destruct (Z.leb_spec r 3).
    + rewrite trip_short by lia. replace (r <=? 6) with true by (symmetry; apply Z.leb_le; lia).
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + rewrite trip_rep_new by lia. replace (r <=? 6) with true by (symmetry; apply Z.leb_le; lia).
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
  - rewrite (chunk 7 n p v 0 7 4 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 7) with 7. rewrite trip_rep_new by lia.
    replace (r <=? 3) with false by (symmetry; apply Z.leb_gt; lia). replace (r <=? 6) with false by (symmetry; apply Z.leb_gt; lia).
    destruct (Z.eq_dec r 7) as [->|N7].
    + change ((7 - 7) / 6) with 0. change ((7 - 7) mod 6) with 0. cbv zeta. change (0 <? 3) with true. change (3 <=? 0) with false. cbv iota.
      destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
    + unfold TCs at 1. rewrite (Hrun (n + 7)) by lia. unfold tree_counts.
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl.
      rewrite (run_cont (Z.to_nat (r - 7)) (r - 7) (n + 7) v x ltac:(lia) Hv ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 7 + (r - 7)) with (n + r) by lia; exact Hend | apply Hrun; lia].
      replace (n + 7 + (r - 7)) with (n + r) by lia. cbv zeta.
      pose proof (Z.mod_pos_bound (r - 7) 6 ltac:(lia)).
      destruct (Z.eqb_spec ((r - 7) mod 6) 0) as [E0|NE0].
      * rewrite E0. change (0 <? 3) with true. change (3 <=? 0) with false. cbv iota. destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
      * destruct (Z.ltb_spec ((r - 7) mod 6) 3).
        -- replace (3 <=? (r - 7) mod 6) with false by (symmetry; apply Z.leb_gt; lia). destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
        -- replace (3 <=? (r - 7) mod 6) with true by (symmetry; apply Z.leb_le; lia). destruct (x =? v); destruct (x =? REP_3_6); cbn [zind]; lia.
Qed.

Lemma run_z : forall (m : nat) r n p x, 1 <= r <= 138 * Z.of_nat m ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = 0) -> L (n + r) <> 0 -> L n = 0 ->
  TCs n p x = e0 r * zind (x =? 0) + e17 r * zind (x =? REPZ_3_10) + e18 r * zind (x =? REPZ_11_138) + TCs (n + r) 0 x.
Proof.
  induction m as [|m IH]; intros r n p x Hr Hn Hrun Hend Hn0; [lia|].
  unfold TCs at 1. rewrite Hn0. unfold tree_counts. cbn [Z.eqb Pos.eqb].
  unfold e0, e17, e18.
  destruct (Z_lt_le_dec r 138) as [R|R].
  - rewrite (chunk (Z.to_nat r) n p 0 0 138 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | right; rewrite Z2Nat.id by lia; exact Hend].
    rewrite Z2Nat.id by lia. rewrite Z.mod_small, Z.div_small by lia. cbv zeta. change (0 + r) with r.
    destruct (Z.ltb_spec r 3).
    + rewrite trip_short by lia. replace (3 <=? r) with false by (symmetry; apply Z.leb_gt; lia). replace (11 <=? r) with false by (symmetry; apply Z.leb_gt; lia).
      cbn [andb]. destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
    + rewrite trip_z by lia. replace (3 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      destruct (Z.leb_spec r 10).
      * replace (11 <=? r) with false by (symmetry; apply Z.leb_gt; lia). destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
      * replace (11 <=? r) with true by (symmetry; apply Z.leb_le; lia). destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
  - rewrite (chunk 138 n p 0 0 138 3 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | lia | left; lia].
    change (Z.of_nat 138) with 138. rewrite trip_z by lia. change (0 + 138 <=? 10) with false. cbv iota.
    pose proof (Z.mod_pos_bound r 138 ltac:(lia)) as MB.
    assert (D138 : (r - 138) / 138 = r / 138 - 1) by (Z.to_euclidean_division_equations; lia).
    assert (M138 : (r - 138) mod 138 = r mod 138) by (Z.to_euclidean_division_equations; lia).
    destruct (Z.eq_dec r 138) as [->|N].
    + change (138 mod 138) with 0. change (138 / 138) with 1. cbv zeta. change (0 <? 3) with true. change (3 <=? 0) with false. change (11 <=? 0) with false. cbn [andb].
      destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
    + fold (TCs (n + 138) 0 x).
      rewrite (IH (r - 138) (n + 138) 0 x ltac:(lia) ltac:(lia)); [| intros; apply Hrun; lia | replace (n + 138 + (r - 138)) with (n + r) by lia; exact Hend | apply Hrun; lia].
      unfold e0, e17, e18. rewrite D138, M138. replace (n + 138 + (r - 138)) with (n + r) by lia. cbv zeta.
      destruct (r mod 138 <? 3); destruct ((3 <=? r mod 138) && (r mod 138 <=? 10)); destruct (11 <=? r mod 138);
        destruct (x =? 0); destruct (x =? REPZ_3_10); destruct (x =? REPZ_11_138); cbn [zind]; lia.
Qed.

Lemma run_any : forall r n p v x, 1 <= r -> 0 <= v <= 15 -> p <> v ->
  n + r - 1 <= mc -> (forall i, n <= i < n + r -> L i = v) -> L (n + r) <> v -> L n = v ->
  TCs n p x = RUN v r x + TCs (n + r) v x.
Proof.
  intros r n p v x Hr Hv Hpv Hn Hrun Hend Hn0. unfold RUN.
  destruct (Z.eqb_spec v 0) as [->|Nv].
  - apply (run_z (Z.to_nat r)); try assumption. lia.
  - apply run_nz; try assumption. lia.
Qed.

Fixpoint runlen (v i : Z) (f : nat) : Z :=
  match f with O => 0 | S f' => if L i =? v then 1 + runlen v (i + 1) f' else 0 end.

Lemma runlen_spec : forall f v i, 0 <= runlen v i f <= Z.of_nat f
  /\ (forall j, i <= j < i + runlen v i f -> L j = v)
  /\ (runlen v i f < Z.of_nat f -> L (i + runlen v i f) <> v).
Proof.
  induction f as [|f IH]; intros v i; cbn [runlen].
  - split; [lia|]. split; [intros; lia | intros; lia].
  - destruct (Z.eqb_spec (L i) v) as [E|N].
    + destruct (IH v (i + 1)) as (A & B & C). split; [lia|]. split.
      * intros j Hj. destruct (Z.eq_dec j i) as [->|Nj]; [exact E | apply B; lia].
      * intros Hlt. replace (i + (1 + runlen v (i + 1) f)) with (i + 1 + runlen v (i + 1) f) by lia. apply C. lia.
    + split; [lia|]. split; [intros; lia | intros _; rewrite Z.add_0_r; exact N].
Qed.

Lemma max_run : forall n, 0 <= n <= mc -> exists r, 1 <= r /\ n + r - 1 <= mc
  /\ (forall i, n <= i < n + r -> L i = L n) /\ L (n + r) <> L n.
Proof.
  intros n Hn. destruct (runlen_spec (Z.to_nat (mc + 2 - n)) (L n) n) as (A & B & C).
  set (r := runlen (L n) n (Z.to_nat (mc + 2 - n))) in *.
  assert (R1 : 1 <= r).
  { subst r. replace (Z.to_nat (mc + 2 - n)) with (S (Z.to_nat (mc + 1 - n))) by lia. cbn [runlen]. rewrite Z.eqb_refl.
    pose proof (runlen_spec (Z.to_nat (mc + 1 - n)) (L n) (n + 1)). lia. }
  assert (Rlt : r < Z.of_nat (Z.to_nat (mc + 2 - n))).
  { destruct (Z_lt_le_dec r (Z.of_nat (Z.to_nat (mc + 2 - n)))) as [|Ge]; [assumption|]. exfalso.
    pose proof (B (mc + 1) ltac:(lia)). pose proof (HL n ltac:(lia)). lia. }
  exists r. split; [exact R1|]. split; [lia|]. split; [exact B | exact (C Rlt)].
Qed.

Lemma zsum_run : forall (P : Z -> bool) n r v, 0 <= r -> (forall i, n <= i < n + r -> L i = v) ->
  zsum (fun i => zind (P (L i))) n (Z.to_nat r) = r * zind (P v).
Proof.
  intros P n r v Hr Hrun.
  rewrite (zsum_ext (fun i => zind (P (L i))) (fun _ => zind (P v))) by (intros i Hi; rewrite Hrun by lia; reflexivity).
  destruct (P v); cbn [zind].
  - rewrite zsum_const1. lia.
  - rewrite zsum_0 by (intros; reflexivity). lia.
Qed.

Lemma scan_from : forall (d : nat) n p, Z.of_nat d = mc + 1 - n -> 0 <= n <= mc + 1 -> (n <= mc -> p <> L n) -> -1 <= p <= 15 ->
  (forall j, 1 <= j <= 15 -> TCs n p j <= zsum (fun i => zind (L i =? j)) n d)
  /\ zsum (fun j => TCs n p j) 1 15 + 3 * TCs n p REP_3_6 <= zsum (fun i => zind (negb (L i =? 0))) n d
  /\ 4 * TCs n p REP_3_6 <= zsum (fun i => zind (negb (L i =? 0))) n d
  /\ TCs n p 0 = lsum e0 (zr L n d 0) /\ TCs n p REPZ_3_10 = lsum e17 (zr L n d 0) /\ TCs n p REPZ_11_138 = lsum e18 (zr L n d 0)
  /\ (forall x, 0 <= TCs n p x).
Proof.
  induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf). intros n p Hd Hn Hp Rp.
  unfold REP_3_6, REPZ_3_10, REPZ_11_138 in *.
  destruct (Z_lt_le_dec mc n) as [END|GO].
  -
    assert (d = 0%nat) by lia. subst d.
    assert (Z0 : forall x, TCs n p x = 0) by (intros x; unfold TCs; destruct (tree_counts p (L n)); apply TC_end; lia).
    rewrite (zsum_0 (fun j : Z => TCs n p j) 1 15) by (intros; apply Z0).
    rewrite !Z0. cbn [zsum zr Z.eqb lsum]. repeat split; intros; rewrite ?Z0; lia.
  - destruct (max_run n ltac:(lia)) as (r & Hr & Hnr & Hrun & Hend).
    pose proof (HL n ltac:(lia)) as Rv. set (v := L n) in *.
    assert (RA : forall x, TCs n p x = RUN v r x + TCs (n + r) v x).
    { intros x. apply run_any; try assumption; try lia; apply Hp; lia. }
    assert (Hp' : n + r <= mc -> v <> L (n + r)) by (intros _ E; apply Hend; rewrite E; reflexivity).
    destruct (IH (Z.to_nat (mc + 1 - (n + r))) ltac:(lia) (n + r) v ltac:(lia) ltac:(lia) Hp' ltac:(lia)) as (I1 & I2 & I3 & I4a & I4b & I4c & I5).
    replace d with (Z.to_nat r + Z.to_nat (mc + 1 - (n + r)))%nat by lia.
    rewrite !zsum_split. rewrite !Z2Nat.id by lia. replace (n + Z.of_nat (Z.to_nat r)) with (n + r) by lia.
    rewrite (zsum_run (fun y => negb (y =? 0)) n r v) by (try lia; exact Hrun).

    assert (ZR : forall f, lsum f (zr L n (Z.to_nat r + Z.to_nat (mc + 1 - (n + r))) 0) =
                         (if v =? 0 then f r else 0) + lsum f (zr L (n + r) (Z.to_nat (mc + 1 - (n + r))) 0)).
    { intros f. destruct (Z.eqb_spec v 0) as [V0|V0].
      - rewrite zr_zeros by (intros; rewrite Hrun by lia; exact V0). rewrite Z2Nat.id, Z.add_0_l by lia.
        destruct (Z.to_nat (mc + 1 - (n + r))) as [|m] eqn:Em.
        + rewrite !zr_end. rewrite Z.eqb_refl. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia.
        + rewrite (zr_nonzero L m (n + r) r) by (rewrite <- V0; exact Hend). rewrite (zr_nonzero L m (n + r) 0) by (rewrite <- V0; exact Hend).
          replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. cbn [app lsum]. lia.
      - assert (G : forall c m i, (forall j, i <= j < i + Z.of_nat c -> L j <> 0) -> zr L i (c + m) 0 = zr L (i + Z.of_nat c) m 0).
        { induction c as [|c IHc]; intros m i Hnz; [cbn [Nat.add]; rewrite Z.add_0_r; reflexivity|].
          cbn [Nat.add]. rewrite zr_nonzero by (apply Hnz; lia). cbn [Z.eqb app].
          rewrite (IHc m (i + 1)) by (intros; apply Hnz; lia). f_equal. lia. }
        rewrite G by (intros; rewrite Hrun by lia; exact V0). rewrite Z2Nat.id by lia. lia. }
    rewrite !ZR.

    assert (RUNv : forall x, RUN v r x = (if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? 17) + e18 r * zind (x =? 18)
                                        else E1 r * zind (x =? v) + M1 r * zind (x =? 16))) by (intros; reflexivity).
    pose proof (E1_M1_facts r ltac:(lia)) as (F1 & F2 & F3 & F4). pose proof (e_facts r ltac:(lia)) as (G1 & G2 & G3 & G4).
    assert (NN : forall x, 0 <= RUN v r x).
    { intros x. rewrite RUNv. destruct (v =? 0); destruct (x =? 0); destruct (x =? 17); destruct (x =? 18); destruct (x =? v); destruct (x =? 16); cbn [zind]; lia. }
    assert (S4 : forall x, x = 0 \/ x = 17 \/ x = 18 ->
              TCs n p x = (if v =? 0 then e0 r * zind (x =? 0) + e17 r * zind (x =? 17) + e18 r * zind (x =? 18) else 0) + TCs (n + r) v x).
    { intros x Hx. rewrite RA, RUNv. destruct (Z.eqb_spec v 0) as [V0|V0]; [reflexivity|].
      replace (x =? v) with false by (symmetry; apply Z.eqb_neq; lia). replace (x =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    +
      intros j Hj. rewrite RA. rewrite zsum_split, Z2Nat.id by lia. rewrite (zsum_run (fun y => y =? j) n r v) by (try lia; exact Hrun).
      pose proof (I1 j Hj). rewrite RUNv. idtac.
      destruct (Z.eqb_spec v 0) as [V0|V0].
      * replace (v =? 0) with true by (symmetry; apply Z.eqb_eq; exact V0). replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (v =? j) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (j =? 17) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 18) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
      * replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact V0). replace (j =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
        destruct (Z.eqb_spec j v) as [->|Njv]; [rewrite Z.eqb_refl | replace (v =? j) with false by (symmetry; apply Z.eqb_neq; lia)]; cbn [zind]; lia.
    +
      rewrite (zsum_ext (fun j => TCs n p j) (fun j => RUN v r j + TCs (n + r) v j)) by (intros; apply RA). rewrite zsum_add, RA.
      change (zsum (RUN v r) 1 15) with (zsum (fun j => RUN v r j) 1 15). change (zsum (TCs (n + r) v) 1 15) with (zsum (fun j => TCs (n + r) v j) 1 15).
      assert (SR : zsum (fun j => RUN v r j) 1 15 = (if v =? 0 then 0 else E1 r)).
      { destruct (Z.eqb_spec v 0) as [V0|V0].
        - apply zsum_0. intros j Hj. rewrite RUNv; try rewrite V0; cbn [Z.eqb Pos.eqb]. idtac.
          replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 17) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 18) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
        - rewrite (zsum_single (fun j => RUN v r j) 1 15 v); [| lia |].
          + rewrite RUNv. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. idtac. replace (v =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia.
          + intros j Hj Njv. rewrite RUNv. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). idtac.
            replace (j =? v) with false by (symmetry; apply Z.eqb_neq; lia). replace (j =? 16) with false by (symmetry; apply Z.eqb_neq; lia). cbn [zind]. lia. }
      rewrite SR, RUNv.
      destruct (Z.eqb_spec v 0) as [V0|V0]; [cbn [Z.eqb Pos.eqb zind negb]; lia|].
      replace (16 =? v) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb Pos.eqb zind negb]. lia.
    +
      rewrite RA, RUNv.
      destruct (Z.eqb_spec v 0) as [V0|V0]; [cbn [Z.eqb Pos.eqb zind negb]; lia|].
      replace (16 =? v) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb Pos.eqb zind negb]. lia.
    + rewrite (S4 0 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + rewrite (S4 17 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + rewrite (S4 18 ltac:(lia)). destruct (v =? 0); cbn [Z.eqb Pos.eqb zind]; lia.
    + intros x. rewrite RA. pose proof (NN x). pose proof (I5 x). lia.
Qed.

End Scan.

Theorem scan_facts : forall (L : Z -> Z) (mc : Z),
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> 15 < L (mc + 1) ->
  let cnt j := zsum (fun i => zind (L i =? j)) 0 (Z.to_nat (mc + 1)) in
  let nz := zsum (fun i => zind (negb (L i =? 0))) 0 (Z.to_nat (mc + 1)) in
  let runs := zruns L 0 (Z.to_nat (mc + 1)) in
  (forall j, 1 <= j <= 15 -> TDcnt L mc j <= cnt j)
  /\ zsum (TDcnt L mc) 1 15 + 3 * TDcnt L mc REP_3_6 <= nz
  /\ 4 * TDcnt L mc REP_3_6 <= nz
  /\ TDcnt L mc 0 = lsum e0 runs
  /\ TDcnt L mc REPZ_3_10 = lsum e17 runs
  /\ TDcnt L mc REPZ_11_138 = lsum e18 runs
  /\ (forall x, 0 <= TDcnt L mc x).
Proof.
  intros L mc Hmc HL HG. cbv zeta.
  assert (E : forall x, TDcnt L mc x = TCs L mc 0 (-1) x) by (intros x; rewrite (TDcnt_TC L mc Hmc HL x); reflexivity).
  pose proof (HL 0 ltac:(lia)).
  destruct (scan_from L mc HL HG (Z.to_nat (mc + 1)) 0 (-1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  rewrite !zruns_lsum.
  split; [intros j Hj; rewrite E; apply A1; exact Hj|].
  split; [rewrite (zsum_ext (TDcnt L mc) (fun j => TCs L mc 0 (-1) j)) by (intros; apply E); rewrite E; exact A2|].
  split; [rewrite E; exact A3|]. split; [rewrite E; exact A4|]. split; [rewrite E; exact A5|]. split; [rewrite E; exact A6|].
  intros x. rewrite E. apply A7.
Qed.

Corollary scan_total : forall (L : Z -> Z) (mc : Z),
  0 <= mc -> (forall i, 0 <= i <= mc -> 0 <= L i <= 15) -> 15 < L (mc + 1) ->
  zsum (TDcnt L mc) 0 19 <= mc + 1.
Proof.
  intros L mc Hmc HL HG.
  destruct (scan_facts L mc Hmc HL HG) as (_ & A2 & _ & A4 & A5 & A6 & A7).
  pose proof (A7 REP_3_6) as P16.
  assert (Z3 : TDcnt L mc 0 + TDcnt L mc REPZ_3_10 + TDcnt L mc REPZ_11_138 <= zsum (fun j => zind (L j =? 0)) 0 (Z.to_nat (mc + 1))).
  { rewrite A4, A5, A6, <- zruns_sum, <- !lsum_add. apply lsum_le. intros r Hr.
    pose proof (zruns_pos L 0 _ r Hr). pose proof (e_facts r ltac:(lia)). lia. }
  assert (TOT : zsum (fun j => zind (L j =? 0)) 0 (Z.to_nat (mc + 1)) + zsum (fun i => zind (negb (L i =? 0))) 0 (Z.to_nat (mc + 1)) = mc + 1).
  { rewrite <- zsum_add. rewrite (zsum_ext _ (fun _ => 1)) by (intros; destruct (L i =? 0); reflexivity). rewrite zsum_const1. lia. }
  change 19%nat with (S (15 + 3))%nat. rewrite zsum_shift, zsum_split.
  change (0 + 1 + Z.of_nat 15) with 16. change (0 + 1) with 1.
  change (zsum (TDcnt L mc) 16 3) with (0 + TDcnt L mc (16 + 0) + TDcnt L mc (16 + 1) + TDcnt L mc (16 + 2)).
  change (16 + 0) with REP_3_6. change (16 + 1) with REPZ_3_10. change (16 + 2) with REPZ_11_138. lia.
Qed.
