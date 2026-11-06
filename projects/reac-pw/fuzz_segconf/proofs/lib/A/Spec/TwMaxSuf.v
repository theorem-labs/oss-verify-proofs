(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwMaxSuf.v, unchanged. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Spec Require Import TwoWay.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope nat_scope.

Section MS.
Variable gt : Z -> Z -> bool.
Hypothesis Hasym : forall a b, gt a b = true -> gt b a = false.
Hypothesis Htot : forall a b, a <> b -> gt a b = true \/ gt b a = true.
Hypothesis Htr : forall a b d, gt a b = true -> gt b d = true -> gt a d = true.
Variable x : list Z.

Lemma gt_irr : forall a, gt a a = false.
Proof.
  intros a. destruct (gt a a) eqn:E; [|reflexivity].
  pose proof (Hasym _ _ E) as F. rewrite E in F. discriminate.
Qed.

Lemma gt_neq : forall a b, gt a b = true -> a <> b.
Proof. intros a b H E. subst. rewrite gt_irr in H. discriminate. Qed.

Lemma lexlt_trans : forall a b d, lexlt gt a b -> lexlt gt b d -> lexlt gt a d.
Proof.
  induction a as [|u a IH]; intros b d H1 H2.
  - destruct b as [|v b]; destruct d as [|w d]; simpl in *; tauto.
  - destruct b as [|v b]; [simpl in H1; contradiction|].
    destruct d as [|w d]; [simpl in H2; contradiction|].
    simpl in *.
    destruct H1 as [[H1a H1b]|[H1a H1b]]; destruct H2 as [[H2a H2b]|[H2a H2b]].
    + left. assert (G : gt w u = true) by (apply (Htr w v u); assumption).
      split; [apply not_eq_sym, gt_neq; exact G | exact G].
    + subst w. left. split; assumption.
    + subst v. left. split; assumption.
    + subst v w. right. split; [reflexivity|]. apply (IH b d); assumption.
Qed.

Lemma nth_sk : forall n (l : list Z) i, nth i (skipn n l) 0%Z = nth (n + i) l 0%Z.
Proof.
  induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|a l]; simpl; [destruct i; reflexivity | apply IH].
Qed.

Lemma len_sk : forall n (l : list Z), length (skipn n l) = length l - n.
Proof.
  induction n as [|n IH]; intros l; [simpl; lia|].
  destruct l as [|a l]; simpl; [reflexivity | apply IH].
Qed.

Lemma at_sk : forall n i, at_ (skipn n x) i = at_ x (n + i).
Proof. intros n i. unfold at_. apply nth_sk. Qed.

Lemma lex_mis : forall t a b, (forall r, r < t -> nth r a 0%Z = nth r b 0%Z) ->
  t < length a -> t < length b -> gt (nth t b 0%Z) (nth t a 0%Z) = true -> lexlt gt a b.
Proof.
  induction t as [|t IH]; intros a b Heq Ha Hb Hg.
  - destruct a as [|u a]; [simpl in Ha; lia|]. destruct b as [|v b]; [simpl in Hb; lia|].
    simpl in Hg. simpl. left. split; [apply not_eq_sym, gt_neq; exact Hg | exact Hg].
  - destruct a as [|u a]; [simpl in Ha; lia|]. destruct b as [|v b]; [simpl in Hb; lia|].
    simpl in Ha, Hb, Hg. simpl. right. split.
    + pose proof (Heq 0 ltac:(lia)) as E. simpl in E. exact E.
    + apply IH; [|lia|lia|exact Hg].
      intros r Hr. pose proof (Heq (S r) ltac:(lia)) as E. simpl in E. exact E.
Qed.

Lemma lex_pre : forall a b, length a < length b ->
  (forall r, r < length a -> nth r a 0%Z = nth r b 0%Z) -> lexlt gt a b.
Proof.
  induction a as [|u a IH]; intros b Hl Heq.
  - destruct b as [|v b]; simpl in *; [lia | exact I].
  - destruct b as [|v b]; simpl in Hl; [lia|].
    simpl. right. split.
    + pose proof (Heq 0 ltac:(simpl; lia)) as E. simpl in E. exact E.
    + apply IH; [lia|]. intros r Hr. pose proof (Heq (S r) ltac:(simpl; lia)) as E. simpl in E. exact E.
Qed.

Lemma sk_mis : forall i c t, i + t < length x -> c + t < length x ->
  (forall r, r < t -> at_ x (i + r) = at_ x (c + r)) ->
  gt (at_ x (c + t)) (at_ x (i + t)) = true -> lexlt gt (skipn i x) (skipn c x).
Proof.
  intros i c t Hi Hc Heq Hg. unfold at_ in *. apply (lex_mis t).
  - intros r Hr. rewrite !nth_sk. apply Heq. exact Hr.
  - rewrite len_sk. lia.
  - rewrite len_sk. lia.
  - rewrite !nth_sk. exact Hg.
Qed.

Lemma sk_pre : forall i c, c < i -> i <= length x ->
  (forall r, i + r < length x -> at_ x (i + r) = at_ x (c + r)) -> lexlt gt (skipn i x) (skipn c x).
Proof.
  intros i c H1 H2 Heq. unfold at_ in *. apply lex_pre.
  - rewrite !len_sk. lia.
  - intros r Hr. rewrite len_sk in Hr. rewrite !nth_sk. apply Heq. lia.
Qed.

Definition Inv (c jp k p : nat) : Prop :=
  1 <= k <= p /\
  (exists e, jp + 1 = c + p + e * p) /\
  jp + k <= length x /\
  (forall i, c <= i -> i + p < jp + k -> at_ x i = at_ x (i + p)) /\
  (forall s, 0 < s < p -> exists t, s + t < p /\
     (forall r, r < t -> at_ x (c + s + r) = at_ x (c + r)) /\
     gt (at_ x (c + t)) (at_ x (c + s + t)) = true) /\
  (forall i, i < c -> lexlt gt (skipn i x) (skipn c x)).

Lemma per_shift : forall c m p, (forall i, c <= i -> i + p < m -> at_ x i = at_ x (i + p)) ->
  forall q i, c <= i -> i + q * p < m -> at_ x i = at_ x (i + q * p).
Proof.
  intros c m p HP q. induction q as [|q IH]; intros i Hi Hm.
  - f_equal. lia.
  - rewrite (IH i Hi) by nia. replace (i + S q * p) with (i + q * p + p) by nia. apply HP; nia.
Qed.

Lemma key : forall c jp k p, Inv c jp k p -> forall i, c < i <= jp + k ->
  (exists t, i + t < jp + k /\ (forall r, r < t -> at_ x (i + r) = at_ x (c + r)) /\
     gt (at_ x (c + t)) (at_ x (i + t)) = true) \/
  ((forall r, i + r < jp + k -> at_ x (i + r) = at_ x (c + r)) /\
   (at_ x (c + (jp + k - i)) = at_ x (c + k - 1) \/
    gt (at_ x (c + (jp + k - i))) (at_ x (c + k - 1)) = true)).
Proof.
  intros c jp k p [Hk [[e He] [Hl [HP [HL HG]]]]] i Hi.
  pose proof (per_shift c (jp + k) p HP) as PS.
  pose proof (Nat.div_mod_eq (i - c) p) as Hdm.
  pose proof (Nat.mod_upper_bound (i - c) p ltac:(lia)) as Hmb.
  remember ((i - c) / p) as q eqn:Hq. remember ((i - c) mod p) as s0 eqn:Hs0.
  clear Hq Hs0.
  assert (Hiq : i = c + q * p + s0) by nia.
  clear Hdm.
  destruct (Nat.eq_dec s0 0) as [Hz|Hz].
  - subst s0. right.
    destruct q as [|q]; [lia|].
    assert (Hqe : q <= e) by nia.
    assert (Hd : exists d, e = q + d) by (exists (e - q); lia).
    destruct Hd as [d Hd]. subst e.
    split.
    + intros r Hr. rewrite (PS (S q) (c + r)) by nia. f_equal. nia.
    + left. rewrite (PS d (c + k - 1)) by nia. f_equal. nia.
  - destruct (HL s0 ltac:(lia)) as [t0 [Hst [Heq0 Hg0]]].
    assert (Hsh : forall r, i + r < jp + k -> at_ x (i + r) = at_ x (c + s0 + r)).
    { intros r Hr. rewrite (PS q (c + s0 + r)) by nia. f_equal. nia. }
    destruct (lt_dec (i + t0) (jp + k)) as [Hin|Hout].
    + left. exists t0. split; [exact Hin|]. split.
      * intros r Hr. rewrite Hsh by lia. apply Heq0. exact Hr.
      * rewrite Hsh by lia. exact Hg0.
    + right.
      assert (Hq1 : e < q) by nia.
      assert (Hq2 : q < e + 2) by nia.
      assert (Hqe : q = S e) by lia. subst q.
      assert (Hmi : jp + k - i = k - 1 - s0) by nia.
      assert (Hsk : s0 <= k - 1) by nia.
      split.
      * intros r Hr. rewrite Hsh by lia. apply Heq0. lia.
      * rewrite Hmi. destruct (Nat.eq_dec (k - 1 - s0) t0) as [Ht|Ht].
        -- right. rewrite Ht. replace (c + k - 1) with (c + s0 + t0) by lia. exact Hg0.
        -- left. rewrite <- (Heq0 (k - 1 - s0)) by lia. f_equal. lia.
Qed.

Lemma run_ok : forall c jp k p c' p', msuf_run gt x c jp k p c' p' -> Inv c jp k p ->
  is_maxsuf gt x c' /\ smallest_period (skipn c' x) p'.
Proof.
  intros c jp k p c' p' R.
  induction R as [c jp k p Hstop
                 | c jp k p c' p' Hlt Heq Hkp R IH
                 | c jp k p c' p' Hlt Heq Hkp R IH
                 | c jp k p c' p' Hlt Hne Hg R IH
                 | c jp k p c' p' Hlt Hne Hg R IH]; intros HI.
  - pose proof HI as HI'. destruct HI as [Hk [[e He] [Hl [HP [HL HG]]]]].
    assert (Hm : jp + k = length x) by lia.
    assert (Hcp : c + p <= jp + 1) by nia.
    unfold is_maxsuf, smallest_period, is_period.
    split.
    + split; [lia|].
      intros i Hi Hic. destruct (lt_dec i c) as [Hlt|Hge]; [apply HG; exact Hlt|].
      destruct (key c jp k p HI' i ltac:(lia)) as [[t [Ht [Heqt Hgt]]] | [HA _]].
      * apply (sk_mis i c t); [lia|lia|exact Heqt|exact Hgt].
      * apply sk_pre; [lia|lia|]. intros r Hr. apply HA. lia.
    + split; [split|split].
      * lia.
      * intros j Hj. rewrite len_sk in Hj. rewrite !at_sk.
        replace (c + (j + p)) with (c + j + p) by lia. apply HP; lia.
      * rewrite len_sk. lia.
      * intros q [Hq1 Hq2] Hq3. rewrite len_sk in Hq3.
        destruct (le_lt_dec p q) as [Hpq|Hpq]; [exact Hpq|exfalso].
        destruct (HL q ltac:(lia)) as [t [Hst [_ Hgt]]].
        pose proof (Hq2 t) as E. rewrite len_sk in E. rewrite !at_sk in E.
        assert (E2 : at_ x (c + t) = at_ x (c + (t + q))) by (apply E; lia).
        replace (c + q + t) with (c + (t + q)) in Hgt by lia.
        rewrite <- E2 in Hgt. rewrite gt_irr in Hgt. discriminate.
  - apply IH. destruct HI as [Hk [[e He] [Hl [HP [HL HG]]]]]. subst k.
    pose proof (per_shift c (jp + p) p HP) as PS.
    unfold Inv. split; [lia|]. split; [exists (S e); nia|].
    split; [lia|]. split; [|split; assumption].
    intros i Hi1 Hi2. destruct (lt_dec (i + p) (jp + p)) as [Hlt'|Hge'].
    + apply HP; lia.
    + replace i with jp by lia. rewrite <- Heq. rewrite (PS e (c + p - 1)) by nia. f_equal. nia.
  - apply IH. destruct HI as [Hk [[e He] [Hl [HP [HL HG]]]]].
    pose proof (per_shift c (jp + k) p HP) as PS.
    unfold Inv. split; [lia|]. split; [exists e; exact He|].
    split; [lia|]. split; [|split; assumption].
    intros i Hi1 Hi2. destruct (lt_dec (i + p) (jp + k)) as [Hlt'|Hge'].
    + apply HP; lia.
    + assert (Hi : i + p = jp + k) by lia.
      rewrite Hi. rewrite <- Heq. rewrite (PS e (c + k - 1)) by nia. f_equal. nia.
  - apply IH. pose proof HI as HI'. destruct HI as [Hk [[e He] [Hl [HP [HL HG]]]]].
    assert (Hcp : c + p <= jp + 1) by nia.
    unfold Inv. split; [lia|]. split; [exists 0; lia|].
    split; [lia|]. split; [intros i Hi1 Hi2; exfalso; lia|]. split; [|exact HG].
    intros s Hs.
    destruct (key c jp k p HI' (c + s) ltac:(lia)) as [[t [Ht [Heqt Hgt]]] | [HA Hle]].
    + exists t. split; [lia|]. split; [exact Heqt|exact Hgt].
    + exists (jp + k - (c + s)). split; [lia|]. split.
      * intros r Hr. apply HA. lia.
      * replace (c + s + (jp + k - (c + s))) with (jp + k) by lia.
        destruct Hle as [E|E].
        -- rewrite E. exact Hg.
        -- apply (Htr _ _ _ E Hg).
  - apply IH. pose proof HI as HI'. destruct HI as [Hk [[e He] [Hl [HP [HL HG]]]]].
    pose proof (per_shift c (jp + k) p HP) as PS.
    assert (Hcp : c + p <= jp + 1) by nia.
    assert (Hg' : gt (at_ x (jp + k)) (at_ x (c + k - 1)) = true).
    { destruct (Htot _ _ Hne) as [E|E]; [congruence|exact E]. }
    assert (Hcj : forall r, r < k - 1 -> at_ x (jp + 1 + r) = at_ x (c + r)).
    { intros r Hr. rewrite (PS (S e) (c + r)) by nia. f_equal. nia. }
    assert (HCJ : lexlt gt (skipn c x) (skipn (jp + 1) x)).
    { apply (sk_mis c (jp + 1) (k - 1)); [lia|lia| |].
      - intros r Hr. symmetry. apply Hcj. exact Hr.
      - replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        replace (c + (k - 1)) with (c + k - 1) by lia. exact Hg'. }
    unfold Inv. split; [lia|]. split; [exists 0; lia|]. split; [lia|].
    split; [intros i Hi1 Hi2; exfalso; lia|]. split; [intros s Hs; exfalso; lia|].
    intros i Hi.
    destruct (lt_dec i c) as [Hic|Hic].
    { apply (lexlt_trans _ (skipn c x)); [apply HG; exact Hic | exact HCJ]. }
    destruct (Nat.eq_dec i c) as [Hic2|Hic2].
    { subst i. exact HCJ. }
    destruct (key c jp k p HI' i ltac:(lia)) as [[t [Ht [Heqt Hgt]]] | [HA _]].
    + apply (lexlt_trans _ (skipn c x)); [|exact HCJ].
      apply (sk_mis i c t); [lia|lia|exact Heqt|exact Hgt].
    + apply (sk_mis i (jp + 1) (k - 1)); [lia|lia| |].
      * intros r Hr. rewrite HA by lia. symmetry. apply Hcj. exact Hr.
      * rewrite HA by lia. replace (jp + 1 + (k - 1)) with (jp + k) by lia.
        replace (c + (k - 1)) with (c + k - 1) by lia. exact Hg'.
Qed.

Lemma ms_ok : forall c p, 1 <= length x -> msuf_run gt x 0 0 1 1 c p ->
  is_maxsuf gt x c /\ smallest_period (skipn c x) p.
Proof.
  intros c p Hl R. apply (run_ok 0 0 1 1 c p R).
  unfold Inv. split; [lia|]. split; [exists 0; lia|]. split; [lia|].
  split; [intros; exfalso; lia|]. split; [intros; exfalso; lia|]. intros; exfalso; lia.
Qed.

End MS.

Theorem maxsuf_ok : MAXSUF_OK.
Proof.
  unfold MAXSUF_OK. intros gt x c p H1 H2 H3 Hl R.
  eapply ms_ok; eassumption.
Qed.
