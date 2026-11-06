(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import ScanInt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zdig (l : list Z) (t : nat) : Prop := exists c, nth_error l t = Some c /\ is_digit c = true.
Definition zndig (l : list Z) (t : nat) : Prop := exists c, nth_error l t = Some c /\ is_digit c = false.

Lemma nth_error_Some_lt : forall {X} (l : list X) t c, nth_error l t = Some c -> (t < length l)%nat.
Proof. intros X l t c H. destruct (Nat.lt_ge_cases t (length l)) as [LT|GE]; [exact LT|]. apply nth_error_None in GE. congruence. Qed.

Lemma twl_le : forall f l, (take_while_len f l <= length l)%nat.
Proof. induction l as [|c l IH]; intros; cbn; [lia|]. destruct (f c); cbn; lia. Qed.

Lemma twl_prefix : forall f l t, (t < take_while_len f l)%nat -> exists c, nth_error l t = Some c /\ f c = true.
Proof.
  induction l as [|c l IH]; intros t Ht; cbn in Ht; [lia|].
  destruct (f c) eqn:E; [|lia]. destruct t as [|t]; cbn; [exists c; split; [reflexivity| exact E]|]. apply IH. lia.
Qed.

Lemma twl_end : forall f l, take_while_len f l = length l \/ exists c, nth_error l (take_while_len f l) = Some c /\ f c = false.
Proof.
  induction l as [|c l IH]; cbn; [left; reflexivity|].
  destruct (f c) eqn:E; cbn.
  - destruct IH as [IH|IH]; [left; lia| right; exact IH].
  - right. exists c. split; [reflexivity| exact E].
Qed.

Lemma drop_while_skipn : forall f l, drop_while f l = skipn (take_while_len f l) l.
Proof. induction l as [|c l IH]; cbn; [reflexivity|]. destruct (f c); cbn; [exact IH| reflexivity]. Qed.

Lemma skipn_skipn' : forall {X} (a b : nat) (l : list X), skipn a (skipn b l) = skipn (b + a) l.
Proof. intros X a b l. revert a l. induction b as [|b IH]; intros a l; cbn; [reflexivity|]. destruct l; cbn; [now destruct a| apply IH]. Qed.

Lemma nth_error_skipn' : forall {X} (k t : nat) (l : list X), nth_error (skipn k l) t = nth_error l (k + t).
Proof. intros X k. induction k as [|k IH]; intros t l; cbn; [reflexivity|]. destruct l; cbn; [now destruct t| apply IH]. Qed.

Lemma space_not_digit : forall c, is_space c = true -> is_digit c = false.
Proof. intros c H. unfold is_space, is_digit in *. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.eqb_eq in H| apply andb_true_iff in H; destruct H as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2]; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia. Qed.

Fixpoint nsd (fmt : list sdir) : Z := match fmt with [] => 0 | SD :: f => 1 + nsd f | _ :: f => nsd f end.

Lemma nsd_nonneg : forall fmt, 0 <= nsd fmt. Proof. induction fmt as [|[| |] f IH]; cbn -[Z.add]; lia. Qed.
Lemma scan_count_bounds : forall fmt inp acc, acc <= scan_count fmt inp acc <= acc + nsd fmt.
Proof.
  induction fmt as [|d fmt IH]; intros inp acc; [cbn; lia|]. pose proof (nsd_nonneg fmt) as NN.
  destruct d; cbn -[Z.add skipn drop_while take_while_len].
  - destruct (Nat.eqb _ 0); [lia|]. match goal with |- context [scan_count fmt ?i ?a] => specialize (IH i a) end. lia.
  - specialize (IH (drop_while is_space inp) acc). lia.
  - destruct inp as [|c' inp']; [lia|]. destruct (c' =? c); [| lia]. specialize (IH inp' acc). lia.
Qed.

Lemma sw_step : forall fmt' pre k acc, (k <= length pre)%nat ->
  exists k', (k <= k' <= length pre)%nat /\ (forall t, (k <= t < k')%nat -> zndig pre t)
    /\ scan_count (SW :: fmt') (skipn k pre) acc = scan_count fmt' (skipn k' pre) acc.
Proof.
  intros fmt' pre k acc Hk. cbn. rewrite drop_while_skipn, skipn_skipn'.
  set (a := take_while_len is_space (skipn k pre)). pose proof (twl_le is_space (skipn k pre)) as LE. rewrite length_skipn in LE.
  exists (k + a)%nat. split; [lia|]. split; [| reflexivity].
  intros t Ht. destruct (twl_prefix is_space (skipn k pre) (t - k) ltac:(lia)) as (c & Hc & SP).
  rewrite nth_error_skipn' in Hc. replace (k + (t - k))%nat with t in Hc by lia. exists c. split; [exact Hc| apply space_not_digit; exact SP].
Qed.

Lemma sl_step : forall c fmt' pre k acc, is_digit c = false ->
  scan_count (SL c :: fmt') (skipn k pre) acc = acc
  \/ (zndig pre k /\ (k < length pre)%nat /\ scan_count (SL c :: fmt') (skipn k pre) acc = scan_count fmt' (skipn (k + 1) pre) acc).
Proof.
  intros c fmt' pre k acc ND. cbn. destruct (skipn k pre) as [|c' inp'] eqn:E; [left; reflexivity|].
  destruct (Z.eqb_spec c' c) as [->|NE]; [right| left; reflexivity].
  assert (Hk : nth_error pre k = Some c). { rewrite <- (Nat.add_0_r k), <- nth_error_skipn', E. reflexivity. }
  split; [exists c; split; [exact Hk| exact ND]|]. split; [exact (nth_error_Some_lt _ _ _ Hk)|].
  replace inp' with (skipn (k + 1) pre); [reflexivity|]. rewrite <- skipn_skipn', E. reflexivity.
Qed.

Lemma sd_step : forall fmt' pre k acc, (k <= length pre)%nat ->
  scan_count (SD :: fmt') (skipn k pre) acc = acc
  \/ exists j e, (k <= j)%nat /\ (j < e)%nat /\ (e <= length pre)%nat /\ (forall t, (k <= t < j)%nat -> zndig pre t) /\ (forall t, (j <= t < e)%nat -> zdig pre t)
       /\ (e = length pre \/ zndig pre e)
       /\ scan_count (SD :: fmt') (skipn k pre) acc = scan_count fmt' (skipn e pre) (acc + 1).
Proof.
  intros fmt' pre k acc Hk. cbn -[skipn Z.add]. rewrite drop_while_skipn, skipn_skipn'.
  set (a := take_while_len is_space (skipn k pre)). pose proof (twl_le is_space (skipn k pre)) as LE. rewrite length_skipn in LE. fold a in LE.
  assert (SPC : forall t, (k <= t < k + a)%nat -> zndig pre t).
  { intros t Ht. destruct (twl_prefix is_space (skipn k pre) (t - k) ltac:(lia)) as (c & Hc & SP).
    rewrite nth_error_skipn' in Hc. replace (k + (t - k))%nat with t in Hc by lia. exists c. split; [exact Hc| apply space_not_digit; exact SP]. }

  set (i1 := skipn (k + a) pre).
  assert (SGN : exists s, (s <= 1)%nat /\ (k + a + s <= length pre)%nat /\ (forall t, (k + a <= t < k + a + s)%nat -> zndig pre t) /\
            match i1 with c :: r => if (c =? 43) || (c =? 45) then r else i1 | [] => i1 end = skipn (k + a + s) pre).
  { destruct i1 as [|c r] eqn:E.
    - exists 0%nat. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. split; [intros; lia|]. symmetry. exact E.
    - assert (Hc : nth_error pre (k + a) = Some c). { rewrite <- (Nat.add_0_r (k + a)), <- nth_error_skipn'. unfold i1 in E. rewrite E. reflexivity. }
      pose proof (nth_error_Some_lt _ _ _ Hc) as LT.
      destruct ((c =? 43) || (c =? 45)) eqn:SG.
      + exists 1%nat. split; [lia|]. split; [lia|]. split.
        * intros t Ht. assert (t = k + a)%nat as -> by lia. exists c. split; [exact Hc|].
          apply Bool.orb_true_iff in SG. unfold is_digit. apply Bool.andb_false_iff. destruct SG as [SG|SG]; apply Z.eqb_eq in SG; subst c; [left|left]; apply Z.leb_gt; lia.
        * unfold i1 in E. change r with (skipn 1 (c :: r)). rewrite <- E, skipn_skipn'. reflexivity.
      + exists 0%nat. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. split; [intros; lia|]. unfold i1 in E. rewrite <- E. reflexivity. }
  destruct SGN as (s & S1 & S2 & S3 & ES). rewrite ES.
  set (nd := take_while_len is_digit (skipn (k + a + s) pre)).
  pose proof (twl_le is_digit (skipn (k + a + s) pre)) as LEd. rewrite length_skipn in LEd. fold nd in LEd.
  destruct (Nat.eqb_spec nd 0) as [Z0|NZ]; [left; reflexivity| right].
  exists (k + a + s)%nat, (k + a + s + nd)%nat. split; [lia|]. split; [lia|]. split; [lia|]. split.
  { intros t Ht. destruct (Nat.lt_ge_cases t (k + a)); [apply SPC; lia| apply S3; lia]. }
  split.
  { intros t Ht. destruct (twl_prefix is_digit (skipn (k + a + s) pre) (t - (k + a + s)) ltac:(lia)) as (c & Hc & DG).
    rewrite nth_error_skipn' in Hc. replace (k + a + s + (t - (k + a + s)))%nat with t in Hc by lia. exists c. split; assumption. }
  split.
  { destruct (twl_end is_digit (skipn (k + a + s) pre)) as [E|(c & Hc & NDc)]; [left; rewrite length_skipn in E; lia| right].
    rewrite nth_error_skipn' in Hc. exists c. split; [exact Hc| exact NDc]. }
  rewrite skipn_skipn'. reflexivity.
Qed.

Definition resp_runs (pre : list Z) (j1 e1 j2 e2 j3 e3 : nat) : Prop :=
  (j1 < e1)%nat /\ (e1 <= j2)%nat /\ (j2 < e2)%nat /\ (e2 <= j3)%nat /\ (j3 < e3)%nat /\ (e3 <= length pre)%nat
  /\ (forall t, (t < j1)%nat -> zndig pre t) /\ (forall t, (j1 <= t < e1)%nat -> zdig pre t) /\ zndig pre e1
  /\ (forall t, (e1 <= t < j2)%nat -> zndig pre t) /\ (forall t, (j2 <= t < e2)%nat -> zdig pre t) /\ zndig pre e2
  /\ (forall t, (e2 <= t < j3)%nat -> zndig pre t) /\ (forall t, (j3 <= t < e3)%nat -> zdig pre t)
  /\ (e3 = length pre \/ zndig pre e3).

Theorem statusline_runs : forall pre, scan_count FMT_STATUSLINE pre 0 = 3 ->
  exists j1 e1 j2 e2 j3 e3, resp_runs pre j1 e1 j2 e2 j3 e3.
Proof.
  intros pre H. unfold FMT_STATUSLINE in H.
  change pre with (skipn 0 pre) in H.

  destruct (sd_step [SW; SL 46; SW; SD; SW; SD] pre 0 0 ltac:(lia)) as [F|(j1 & e1 & B1 & B1' & B1'' & N1 & D1 & X1 & E1)]; [rewrite F in H; lia|].
  rewrite E1 in H. clear E1.

  destruct (sw_step [SL 46; SW; SD; SW; SD] pre e1 (0 + 1) ltac:(lia)) as (k2 & B2 & N2 & E2). rewrite E2 in H. clear E2.

  destruct (sl_step 46 [SW; SD; SW; SD] pre k2 (0 + 1) ltac:(reflexivity)) as [F|(N3 & B3 & E3)]; [rewrite F in H; lia|].
  rewrite E3 in H. clear E3.

  destruct (sw_step [SD; SW; SD] pre (k2 + 1) (0 + 1) ltac:(lia)) as (k4 & B4 & N4 & E4). rewrite E4 in H. clear E4.

  destruct (sd_step [SW; SD] pre k4 (0 + 1) ltac:(lia)) as [F|(j2 & e2 & B5 & B5' & B5'' & N5 & D5 & X5 & E5)]; [rewrite F in H; lia|].
  rewrite E5 in H. clear E5.

  destruct (sw_step [SD] pre e2 (0 + 1 + 1) ltac:(lia)) as (k6 & B6 & N6 & E6). rewrite E6 in H. clear E6.

  destruct (sd_step [] pre k6 (0 + 1 + 1) ltac:(lia)) as [F|(j3 & e3 & B7 & B7' & B7'' & N7 & D7 & X7 & E7)]; [rewrite F in H; lia|].
  clear E7 H.
  exists j1, e1, j2, e2, j3, e3. unfold resp_runs.
  do 6 (split; [lia|]).
  split; [intros t Ht; apply N1; lia|]. split; [exact D1|].
  split. { destruct X1 as [X1|X1]; [exfalso; lia| exact X1]. }
  split. { intros t Ht. destruct (Nat.lt_ge_cases t k2); [apply N2; lia|]. destruct (Nat.eq_dec t k2) as [->|]; [exact N3|].
           destruct (Nat.lt_ge_cases t k4); [apply N4; lia| apply N5; lia]. }
  split; [exact D5|].
  split. { destruct X5 as [X5|X5]; [exfalso; lia| exact X5]. }
  split. { intros t Ht. destruct (Nat.lt_ge_cases t k6); [apply N6; lia| apply N7; lia]. }
  split; [exact D7| exact X7].
Qed.
