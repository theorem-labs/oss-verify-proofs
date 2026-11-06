(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwSearchPf.v, unchanged. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import TwoWay StrStr TwSearch.
Import ListNotations.
Open Scope nat_scope.
Unset Lia Cache.

Lemma ts_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0%Z = nth (k + i) l 0%Z.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros l i; simpl.
  - reflexivity.
  - destruct l as [|a l]; simpl.
    + destruct i; reflexivity.
    + apply IH.
Qed.

Lemma ts_length_skipn : forall (l : list Z) k, length (skipn k l) = length l - k.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros l; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct l as [|a l]; simpl; [reflexivity | apply IH].
Qed.

Lemma ts_prefix_true : forall x h, prefix_eqb x h = true <->
  length x <= length h /\ forall j, j < length x -> at_ x j = at_ h j.
Proof.
  unfold at_. induction x as [|a x IH]; intros [|b h]; cbn [prefix_eqb length].
  - split; [intros _; split; [lia | intros j Hj; lia] | intros _; reflexivity].
  - split; [intros _; split; [lia | intros j Hj; lia] | intros _; reflexivity].
  - split; [discriminate | intros [H _]; lia].
  - rewrite andb_true_iff, Z.eqb_eq, IH. split.
    + intros [E [Hl Hj]]. subst b. split; [lia|].
      intros [|j] Hj'; cbn [nth]; [reflexivity | apply Hj; lia].
    + intros [Hl Hj]. split.
      * pose proof (Hj 0 ltac:(lia)) as H0. cbn [nth] in H0. exact H0.
      * split; [lia|]. intros j Hj'.
        pose proof (Hj (S j) ltac:(lia)) as H1. cbn [nth] in H1. exact H1.
Qed.

Lemma ts_occ : forall x y i, 1 <= length x ->
  prefix_eqb x (skipn i y) = true <->
  i + length x <= length y /\ forall j, j < length x -> at_ x j = at_ y (i + j).
Proof.
  intros x y i Hx. rewrite ts_prefix_true, ts_length_skipn. unfold at_. split.
  - intros [H1 H2]. split; [lia|]. intros j Hj. rewrite H2 by exact Hj. apply ts_nth_skipn.
  - intros [H1 H2]. split; [lia|]. intros j Hj. rewrite H2 by exact Hj. symmetry. apply ts_nth_skipn.
Qed.

Lemma ts_ff_none : forall x h, (forall i, prefix_eqb x (skipn i h) = false) -> find_first h x = None.
Proof.
  intros x h; induction h as [|b h IH]; intros H; cbn [find_first].
  - pose proof (H 0) as H0. cbn [skipn] in H0. rewrite H0. reflexivity.
  - pose proof (H 0) as H0. cbn [skipn] in H0. rewrite H0.
    rewrite IH; [reflexivity|]. intros i. exact (H (S i)).
Qed.

Lemma ts_ff_some : forall x h i, (forall i', i' < i -> prefix_eqb x (skipn i' h) = false) ->
  prefix_eqb x (skipn i h) = true -> find_first h x = Some i.
Proof.
  intros x h; induction h as [|b h IH]; intros [|i] Hlt Hi; cbn [find_first].
  - cbn [skipn] in Hi. rewrite Hi. reflexivity.
  - pose proof (Hlt 0 ltac:(lia)) as H0. cbn [skipn] in H0, Hi. congruence.
  - cbn [skipn] in Hi. rewrite Hi. reflexivity.
  - pose proof (Hlt 0 ltac:(lia)) as H0. cbn [skipn] in H0. rewrite H0.
    assert (E : find_first h x = Some i).
    { apply IH; [|exact Hi]. intros i' Hi'. exact (Hlt (S i') ltac:(lia)). }
    rewrite E. reflexivity.
Qed.

Lemma ts_inset_false : forall x b, inset x b = false -> forall i, i < length x -> at_ x i <> b.
Proof.
  intros x b H i Hi E. unfold inset in H.
  assert (H' : existsb (Z.eqb b) x = true).
  { apply existsb_exists. exists (at_ x i). split.
    - unfold at_. apply nth_In. exact Hi.
    - rewrite E. apply Z.eqb_refl. }
  congruence.
Qed.

Lemma ts_shift_gen : forall x b n a acc, acc <= a -> (forall i, acc <= i < a -> at_ x i <> b) ->
  fold_left (fun acc i => if Z.eqb (at_ x i) b then S i else acc) (seq a n) acc <= a + n /\
  forall i, fold_left (fun acc i => if Z.eqb (at_ x i) b then S i else acc) (seq a n) acc <= i < a + n ->
    at_ x i <> b.
Proof.
  intros x b n; induction n as [|n IH]; intros a acc Ha Hi; cbn [seq fold_left].
  - split; [lia|]. intros i Hi'. apply Hi. lia.
  - destruct (Z.eqb (at_ x a) b) eqn:E; cbn [negb].
    + assert (Ha' : S a <= S a) by lia.
      assert (Hi' : forall i, S a <= i < S a -> at_ x i <> b) by (intros i Hi'; lia).
      destruct (IH (S a) (S a) Ha' Hi') as [H1 H2].
      split; [lia|]. intros i Hi2. apply H2; lia.
    + apply Z.eqb_neq in E.
      assert (Ha' : acc <= S a) by lia.
      assert (Hi' : forall i, acc <= i < S a -> at_ x i <> b).
      { intros i Hi2. destruct (Nat.eq_dec i a) as [->|Hne]; [exact E|]. apply Hi; lia. }
      destruct (IH (S a) acc Ha' Hi') as [H1 H2].
      split; [lia|]. intros i Hi2. apply H2; lia.
Qed.

Lemma ts_shift_of : forall x b, shift_of x b <= length x /\
  forall i, shift_of x b <= i < length x -> at_ x i <> b.
Proof.
  intros x b. unfold shift_of.
  assert (H0 : 0 <= 0) by lia.
  assert (Hi0 : forall i, 0 <= i < 0 -> at_ x i <> b) by (intros i Hi; lia).
  destruct (ts_shift_gen x b (length x) 0 0 H0 Hi0) as [H1 H2].
  split; [exact H1|]. intros i Hi. apply H2. exact Hi.
Qed.

Lemma ts_rscan : forall x y pos fuel k r, k + fuel = length x -> rscan x y pos k fuel = r ->
  k <= r /\ r <= length x /\ (forall i, k <= i < r -> at_ x i = at_ y (pos + i)) /\
  (r < length x -> at_ x r <> at_ y (pos + r)).
Proof.
  intros x y pos fuel; induction fuel as [|f IH]; intros k r Hk Hr; cbn [rscan] in Hr.
  - subst r. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|]. intros H; lia.
  - revert Hr. destruct (k <? length x) eqn:E1;
      [destruct (at_ x k =? at_ y (pos + k))%Z eqn:E2|]; cbn [andb]; intros Hr.
    + apply Z.eqb_eq in E2.
      destruct (IH (S k) r ltac:(lia) Hr) as (H1 & H2 & H3 & H4).
      split; [lia|]. split; [lia|]. split; [|exact H4].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|Hne]; [exact E2|]. apply H3; lia.
    + apply Z.eqb_neq in E2. subst r. split; [lia|]. split; [lia|]. split; [intros i Hi; lia|].
      intros _. exact E2.
    + apply Nat.ltb_ge in E1. lia.
Qed.

Lemma ts_lscan : forall x y pos mem k r, lscan x y pos mem k = r ->
  r <= k /\ (forall i, r <= i < k -> at_ x i = at_ y (pos + i)) /\
  (mem < r -> at_ x (r - 1) <> at_ y (pos + (r - 1))).
Proof.
  intros x y pos mem k; induction k as [|k IH]; intros r Hr; cbn [lscan] in Hr.
  - subst r. split; [lia|]. split; [intros i Hi; lia|]. intros H; lia.
  - revert Hr. destruct (mem <? S k) eqn:E1;
      [destruct (at_ x k =? at_ y (pos + k))%Z eqn:E2|]; cbn [andb]; intros Hr.
    + apply Z.eqb_eq in E2. destruct (IH r Hr) as (H1 & H2 & H3).
      split; [lia|]. split; [|exact H3].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|Hne]; [exact E2|]. apply H2; lia.
    + apply Z.eqb_neq in E2. subst r. split; [lia|]. split; [intros i Hi; lia|].
      intros _. replace (S k - 1) with k by lia. exact E2.
    + apply Nat.ltb_ge in E1. subst r. split; [lia|]. split; [intros i Hi; lia|]. intros H; lia.
Qed.

Lemma ts_tw_periodic : forall x c p0,
  tw_periodic x c p0 = true <-> (forall j, j < c -> at_ x j = at_ x (j + p0)).
Proof.
  intros x c p0. unfold tw_periodic. rewrite forallb_forall. split.
  - intros H j Hj. apply Z.eqb_eq. apply H. apply in_seq. lia.
  - intros H j Hj. apply in_seq in Hj. apply Z.eqb_eq. apply H. lia.
Qed.

Lemma ts_p_per : forall x c p0, tw_periodic x c p0 = true -> tw_p x c p0 = p0.
Proof. intros x c p0 H. unfold tw_p. rewrite H. reflexivity. Qed.

Lemma ts_p_nper : forall x c p0, tw_periodic x c p0 = false ->
  tw_p x c p0 = Nat.max (c - 1) (length x - c) + 1.
Proof. intros x c p0 H. unfold tw_p. rewrite H. reflexivity. Qed.

Lemma ts_mem0_per : forall x c p0, tw_periodic x c p0 = true -> tw_mem0 x c p0 = length x - p0.
Proof. intros x c p0 H. unfold tw_mem0. rewrite H. reflexivity. Qed.

Lemma ts_mem0_nper : forall x c p0, tw_periodic x c p0 = false -> tw_mem0 x c p0 = 0.
Proof. intros x c p0 H. unfold tw_mem0. rewrite H. reflexivity. Qed.

Lemma ts_lr_period : forall x c p0,
  (forall j, j + p0 < length x -> at_ x j = at_ x (j + p0)) ->
  1 <= p0 -> (forall d, 1 <= d < p0 -> ~ LR x c d) ->
  forall d, 1 <= d -> c + d <= length x -> LR x c d ->
  forall i, i + d < length x -> at_ x i = at_ x (i + d).
Proof.
  intros x c p0 Hper Hp0 Hno d.
  induction d as [d IH] using (well_founded_ind lt_wf).
  intros Hd Hcd HLR i Hi.
  destruct (Nat.lt_ge_cases d p0) as [Hlt|Hge].
  - exfalso. exact (Hno d (conj Hd Hlt) HLR).
  - destruct (Nat.eq_dec d p0) as [E|Hne].
    + subst d. apply Hper. exact Hi.
    + assert (HLR' : LR x c (d - p0)).
      { unfold LR. intros j Hj1 Hj2 Hj3.
        rewrite (Hper j) by lia.
        rewrite (HLR (j + p0)) by lia.
        f_equal. lia. }
      assert (H1 : at_ x i = at_ x (i + (d - p0))).
      { apply (IH (d - p0)); [lia | lia | lia | exact HLR' | lia]. }
      rewrite H1, (Hper (i + (d - p0))) by lia. f_equal. lia.
Qed.

Lemma ts_lr_of_occ : forall x y pos a e d c,
  a <= c -> e <= length x -> (c + d <= e \/ e = length x) ->
  (forall i, a <= i < e -> at_ x i = at_ y (pos + i)) ->
  (forall j, j < length x -> at_ x j = at_ y (pos + d + j)) ->
  LR x c d.
Proof.
  intros x y pos a e d c Ha He Hcd Hm Hocc. unfold LR. intros j Hj1 Hj2 Hj3.
  rewrite (Hm j) by lia. rewrite (Hocc (j - d)) by lia. f_equal. lia.
Qed.

Lemma ts_inv_step : forall x y pos mem s mem',
  TW_INV x y pos mem ->
  (forall d, d < s -> (forall j, j < length x -> at_ x j = at_ y (pos + d + j)) -> False) ->
  mem' < length x -> (forall j, j < mem' -> at_ x j = at_ y (pos + s + j)) ->
  TW_INV x y (pos + s) mem'.
Proof.
  intros x y pos mem s mem' (Hno & Hm & Hpre) Hd Hm' Hpre'.
  split; [|split; assumption].
  intros i Hi. destruct (Nat.lt_ge_cases i pos) as [Hip|Hip]; [apply Hno; exact Hip|].
  destruct (prefix_eqb x (skipn i y)) eqn:E; [|reflexivity].
  exfalso. assert (Hx : 1 <= length x) by lia.
  apply (ts_occ x y i Hx) in E as [_ E].
  apply (Hd (i - pos)); [lia|]. intros j Hj. rewrite E by exact Hj. f_equal. lia.
Qed.

Theorem search_end_ok : SEARCH_END_OK.
Proof.
  intros x y pos mem Hl (Hno & _ & _) Hy. apply ts_ff_none. intros i.
  destruct (Nat.lt_ge_cases i pos) as [Hi|Hi]; [apply Hno; exact Hi|].
  destruct (prefix_eqb x (skipn i y)) eqn:E; [|reflexivity].
  apply (ts_occ x y i Hl) in E as [E _]. lia.
Qed.

Theorem search_found_ok : SEARCH_FOUND_OK.
Proof.
  intros x y pos mem (Hno & _ & _) Hp. apply ts_ff_some; assumption.
Qed.

Theorem search_ok : SEARCH_OK.
Proof.
  intros x y c p0 Hl Hcrit pos mem Hinv Hmem Hy.
  destruct Hcrit as (Hc & Hp0 & Hcp & Hper & Hnper).
  pose proof Hinv as (Hno & Hml & Hpre).
  unfold tw_body. cbv beta zeta.
  remember (at_ y (pos + length x - 1)) as b eqn:Hb0.
  destruct (inset x b) eqn:Hin; cbn [negb].
  2:{
    split; [lia|]. split; [|left; reflexivity].
    apply (ts_inv_step x y pos mem); [exact Hinv | | lia | intros j Hj; lia].
    intros d Hd Hocc. apply (ts_inset_false x b Hin (length x - 1 - d)); [lia|].
    rewrite Hb0. rewrite Hocc by lia. f_equal. lia. }
  destruct (ts_shift_of x b) as [Hs1 Hs2].
  destruct (length x - shift_of x b =? 0) eqn:Hk; cbn [negb].
  2:{
    apply Nat.eqb_neq in Hk.
    assert (Hb : at_ x (length x - 1) <> b) by (apply Hs2; lia).
    split; [lia|]. split; [|left; reflexivity].
    apply (ts_inv_step x y pos mem); [exact Hinv | | lia | intros j Hj; lia].
    intros d Hd Hocc.
    assert (Hbd : at_ x (length x - 1 - d) = b).
    { rewrite Hb0. rewrite Hocc by lia. f_equal. lia. }
    destruct (Nat.lt_ge_cases d (length x - shift_of x b)) as [Hdk|Hdk].
    - apply (Hs2 (length x - 1 - d)); [lia | exact Hbd].
    - assert (Hdm : d < mem) by lia.
      destruct Hmem as [Hm0|Hm0]; [lia|].
      destruct (tw_periodic x c p0) eqn:Hpp.
      + rewrite (ts_mem0_per x c p0 Hpp) in Hm0.
        destruct (Hper (proj1 (ts_tw_periodic x c p0) Hpp)) as (Hperiod & _ & _).
        assert (E1 : at_ x (mem - 1 - d) = at_ x (length x - 1 - d)).
        { rewrite (Hperiod (mem - 1 - d)) by lia. f_equal. lia. }
        assert (E2 : at_ x (mem - 1) = at_ x (length x - 1)).
        { rewrite (Hperiod (mem - 1)) by lia. f_equal. lia. }
        assert (E3 : at_ x (mem - 1 - d) = at_ x (mem - 1)).
        { rewrite Hocc by lia. rewrite Hpre by lia. f_equal. lia. }
        apply Hb. congruence.
      + rewrite (ts_mem0_nper x c p0 Hpp) in Hm0. lia. }
  remember (Nat.max c mem) as M eqn:HM.
  remember (rscan x y pos M (length x - M)) as kr eqn:Hkr0.
  destruct (ts_rscan x y pos (length x - M) M kr ltac:(lia) (eq_sym Hkr0)) as (Hr1 & Hr2 & Hr3 & Hr4).
  destruct (kr <? length x) eqn:Hlt; cbn [negb].
  - apply Nat.ltb_lt in Hlt.
    split; [lia|]. split; [|left; reflexivity].
    assert (Hmatch : forall i, c <= i < kr -> at_ x i = at_ y (pos + i)).
    { intros i Hi. destruct (Nat.lt_ge_cases i mem); [apply Hpre; lia | apply Hr3; lia]. }
    apply (ts_inv_step x y pos mem); [exact Hinv | | lia | intros j Hj; lia].
    intros d Hd Hocc.
    destruct (Nat.eq_dec d 0) as [->|Hd0].
    + apply Hr4; [exact Hlt|]. rewrite Hocc by lia. f_equal. lia.
    + assert (HLR : LR x c d).
      { apply (ts_lr_of_occ x y pos c kr d c); [lia | lia | lia | exact Hmatch | exact Hocc]. }
      destruct (tw_periodic x c p0) eqn:Hpp.
      * destruct (Hper (proj1 (ts_tw_periodic x c p0) Hpp)) as (Hperiod & Hcp0 & HnoLR).
        pose proof (ts_lr_period x c p0 Hperiod Hp0 HnoLR d ltac:(lia) ltac:(lia) HLR) as Hdp.
        assert (E : at_ x (kr - d) = at_ x kr).
        { rewrite (Hdp (kr - d)) by lia. f_equal. lia. }
        apply Hr4; [exact Hlt|]. rewrite <- E. rewrite Hocc by lia. f_equal. lia.
      * assert (Hnp : ~ (forall j, j < c -> at_ x j = at_ x (j + p0))).
        { intros H. pose proof (proj2 (ts_tw_periodic x c p0) H). congruence. }
        destruct (Hnper Hnp) as (Hc1 & HnoLR).
        apply (HnoLR d); [lia | exact HLR].
  - apply Nat.ltb_ge in Hlt. assert (Hkr : kr = length x) by lia.
    remember (lscan x y pos mem c) as kl eqn:Hkl0.
    destruct (ts_lscan x y pos mem c kl (eq_sym Hkl0)) as (Hl1 & Hl2 & Hl3).
    destruct (kl <=? mem) eqn:Hle; cbn [negb].
    + apply Nat.leb_le in Hle. split; [reflexivity|].
      apply (proj2 (ts_occ x y pos Hl)). split; [lia|].
      intros j Hj. destruct (Nat.lt_ge_cases j mem); [apply Hpre; lia|].
      destruct (Nat.lt_ge_cases j c); [apply Hl2; lia | apply Hr3; lia].
    + apply Nat.leb_gt in Hle.
      assert (Hmatch : forall i, kl <= i < length x -> at_ x i = at_ y (pos + i)).
      { intros i Hi. destruct (Nat.lt_ge_cases i c); [apply Hl2; lia|].
        destruct (Nat.lt_ge_cases i mem); [apply Hpre; lia | apply Hr3; lia]. }
      assert (Hd0 : forall d, d = 0 -> (forall j, j < length x -> at_ x j = at_ y (pos + d + j)) -> False).
      { intros d -> Hocc. apply Hl3; [exact Hle|]. rewrite Hocc by lia. f_equal. lia. }
      destruct (tw_periodic x c p0) eqn:Hpp.
      * rewrite (ts_p_per x c p0 Hpp), (ts_mem0_per x c p0 Hpp).
        destruct (Hper (proj1 (ts_tw_periodic x c p0) Hpp)) as (Hperiod & Hcp0 & HnoLR).
        split; [lia|]. split; [|right; reflexivity].
        apply (ts_inv_step x y pos mem); [exact Hinv | | lia |].
        -- intros d Hd Hocc. destruct (Nat.eq_dec d 0) as [E|E]; [exact (Hd0 d E Hocc)|].
           apply (HnoLR d); [lia|].
           apply (ts_lr_of_occ x y pos kl (length x) d c); [lia | lia | lia | exact Hmatch | exact Hocc].
        -- intros j Hj. rewrite (Hperiod j) by lia. rewrite Hmatch by lia. f_equal. lia.
      * rewrite (ts_p_nper x c p0 Hpp), (ts_mem0_nper x c p0 Hpp).
        assert (Hnp : ~ (forall j, j < c -> at_ x j = at_ x (j + p0))).
        { intros H. pose proof (proj2 (ts_tw_periodic x c p0) H). congruence. }
        destruct (Hnper Hnp) as (Hc1 & HnoLR).
        split; [lia|]. split; [|left; reflexivity].
        apply (ts_inv_step x y pos mem); [exact Hinv | | lia | intros j Hj; lia].
        intros d Hd Hocc. destruct (Nat.eq_dec d 0) as [E|E]; [exact (Hd0 d E Hocc)|].
        apply (HnoLR d); [lia|].
        apply (ts_lr_of_occ x y pos kl (length x) d c); [lia | lia | lia | exact Hmatch | exact Hocc].
Qed.
