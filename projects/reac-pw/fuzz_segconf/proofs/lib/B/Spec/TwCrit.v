(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwCrit.v, unchanged. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Spec/TwCrit.v for reac-pw/fuzz_segconf.asan-ubsan (image B), with its module paths changed. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import TwoWay.
Import ListNotations.
Open Scope nat_scope.
Unset Lia Cache.

Lemma cr_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0%Z = nth (k + i) l 0%Z.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros l i; simpl.
  - reflexivity.
  - destruct l as [|a l]; simpl.
    + destruct i; reflexivity.
    + apply IH.
Qed.

Lemma cr_nth_firstn : forall (l : list Z) n i, i < n -> nth i (firstn n l) 0%Z = nth i l 0%Z.
Proof.
  intros l n; revert l; induction n as [|n IH]; intros l i Hi.
  - lia.
  - destruct l as [|a l]; simpl.
    + reflexivity.
    + destruct i as [|i]; simpl; [reflexivity | apply IH; lia].
Qed.

Lemma cr_length_skipn : forall (l : list Z) k, length (skipn k l) = length l - k.
Proof.
  intros l k; revert l; induction k as [|k IH]; intros l; simpl.
  - lia.
  - destruct l as [|a l]; simpl; [reflexivity | apply IH].
Qed.

Lemma cr_length_firstn : forall (l : list Z) n, n <= length l -> length (firstn n l) = n.
Proof.
  intros l n; revert l; induction n as [|n IH]; intros l Hn; simpl.
  - reflexivity.
  - destruct l as [|a l]; simpl in *.
    + lia.
    + f_equal. apply IH. lia.
Qed.

Lemma cr_skipn_skipn : forall (l : list Z) a b, skipn a (skipn b l) = skipn (a + b) l.
Proof.
  intros l a b; revert l; induction b as [|b IH]; intros l.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. destruct l as [|z l]; simpl.
    + destruct a; reflexivity.
    + apply IH.
Qed.

Lemma cr_split : forall (l : list Z) n k, skipn k l = firstn n (skipn k l) ++ skipn (n + k) l.
Proof.
  intros l n k. rewrite <- cr_skipn_skipn. symmetry. apply firstn_skipn.
Qed.

Lemma cr_list_ext : forall (l l' : list Z), length l = length l' ->
  (forall i, i < length l -> nth i l 0%Z = nth i l' 0%Z) -> l = l'.
Proof.
  induction l as [|a l IH]; intros [|b l'] Hlen Hn; simpl in *; try lia.
  - reflexivity.
  - f_equal.
    + exact (Hn 0 ltac:(lia)).
    + apply IH; [lia|]. intros i Hi. exact (Hn (S i) ltac:(lia)).
Qed.

Lemma cr_lex_cancel : forall g (s a b : list Z), lexlt g (s ++ a) (s ++ b) -> lexlt g a b.
Proof.
  intros g s a b; induction s as [|z s IH]; simpl; intros H.
  - exact H.
  - destruct H as [[H _] | [_ H]]; [congruence | exact (IH H)].
Qed.

Lemma cr_lex_asym : forall g, (forall a b, g a b = true -> g b a = false) ->
  forall (a b : list Z), lexlt g a b -> lexlt g b a -> False.
Proof.
  intros g Hg a; induction a as [|u a IH]; intros [|v b] H1 H2; simpl in *; try contradiction.
  destruct H1 as [[H1 H1'] | [H1 H1']]; destruct H2 as [[H2 H2'] | [H2 H2']]; try congruence.
  - rewrite (Hg _ _ H1') in H2'. discriminate.
  - exact (IH _ H1' H2').
Qed.

Lemma cr_lex_prefix : forall g (a b : list Z), b <> [] -> lexlt g a (a ++ b).
Proof.
  intros g a b Hb; induction a as [|z a IH]; simpl.
  - destruct b as [|z b]; [congruence | exact I].
  - right; split; [reflexivity | exact IH].
Qed.

Lemma cr_lex_both : forall g1 g2, (forall a b, a <> b -> g1 a b = true -> g2 a b = true -> False) ->
  forall (t v : list Z), lexlt g1 t v -> lexlt g2 t v ->
  forall i, i < length t -> nth i t 0%Z = nth i v 0%Z.
Proof.
  intros g1 g2 Hg t; induction t as [|a t IH]; intros [|b v] H1 H2 i Hi; simpl in *; try contradiction; try lia.
  destruct H1 as [[H1 H1'] | [H1 H1']]; destruct H2 as [[H2 H2'] | [H2 H2']]; try congruence.
  - exfalso. apply (Hg b a); [congruence | exact H1' | exact H2'].
  - subst b. destruct i as [|i]; simpl; [reflexivity | apply IH; auto; lia].
Qed.

Lemma cr_ltb_asym : forall a b, Z.ltb a b = true -> Z.ltb b a = false.
Proof.
  intros a b H. apply Z.ltb_lt in H. apply Z.ltb_ge. lia.
Qed.

Lemma cr_gtb_asym : forall a b, Z.gtb a b = true -> Z.gtb b a = false.
Proof.
  intros a b H. rewrite Z.gtb_ltb in *. apply cr_ltb_asym. exact H.
Qed.

Lemma cr_gl : forall a b, a <> b -> Z.gtb a b = true -> Z.ltb a b = true -> False.
Proof.
  intros a b _ H1 H2. rewrite Z.gtb_ltb in H1. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma cr_lg : forall a b, a <> b -> Z.ltb a b = true -> Z.gtb a b = true -> False.
Proof.
  intros a b H H1 H2. exact (cr_gl a b H H2 H1).
Qed.

Lemma cr_no_short : forall g (x : list Z) c d,
  (forall a b, g a b = true -> g b a = false) ->
  is_maxsuf g x c -> 1 <= d -> d <= c -> LR x c d -> False.
Proof.
  intros g x c d Hg [Hc Hmax] Hd1 Hdc HLR.
  assert (Hy : lexlt g (skipn (c - d) x) (skipn c x)) by (apply Hmax; lia).
  destruct (le_lt_dec (length x) (c + d)) as [Hle | Hlt].
  - assert (F : firstn (length x - c) (skipn (c - d) x) = skipn c x).
    { apply cr_list_ext.
      - rewrite cr_length_firstn by (rewrite cr_length_skipn; lia). rewrite cr_length_skipn. reflexivity.
      - intros i Hi. rewrite cr_length_firstn in Hi by (rewrite cr_length_skipn; lia).
        rewrite cr_nth_firstn by lia. rewrite !cr_nth_skipn.
        specialize (HLR (c + i)). unfold at_ in HLR.
        replace (c + i - d) with (c - d + i) in HLR by lia.
        symmetry. apply HLR; lia. }
    assert (E2 := cr_split x (length x - c) (c - d)). rewrite F in E2.
    apply (cr_lex_asym g Hg _ _ Hy). rewrite E2. apply cr_lex_prefix.
    intros E. apply (f_equal (@length Z)) in E. rewrite cr_length_skipn in E. simpl in E. lia.
  - assert (F : firstn d (skipn (c - d) x) = firstn d (skipn c x)).
    { apply cr_list_ext.
      - rewrite cr_length_firstn by (rewrite cr_length_skipn; lia).
        rewrite cr_length_firstn by (rewrite cr_length_skipn; lia). reflexivity.
      - intros i Hi. rewrite cr_length_firstn in Hi by (rewrite cr_length_skipn; lia).
        rewrite !cr_nth_firstn by lia. rewrite !cr_nth_skipn.
        specialize (HLR (c + i)). unfold at_ in HLR.
        replace (c + i - d) with (c - d + i) in HLR by lia.
        symmetry. apply HLR; lia. }
    assert (Ey := cr_split x d (c - d)). replace (d + (c - d)) with c in Ey by lia. rewrite F in Ey.
    assert (Ev := cr_split x d c). replace (d + c) with (c + d) in Ev by lia.
    assert (H2 : lexlt g (skipn c x) (skipn (c + d) x)).
    { apply (cr_lex_cancel g (firstn d (skipn c x))). rewrite <- Ev, <- Ey. exact Hy. }
    assert (H3 : lexlt g (skipn (c + d) x) (skipn c x)) by (apply Hmax; lia).
    exact (cr_lex_asym g Hg _ _ H2 H3).
Qed.

Lemma cr_crit : forall g1 g2 (x : list Z) c c' d,
  (forall a b, g1 a b = true -> g1 b a = false) ->
  (forall a b, a <> b -> g1 a b = true -> g2 a b = true -> False) ->
  is_maxsuf g1 x c -> is_maxsuf g2 x c' -> c' <= c ->
  1 <= d -> LR x c d -> c < d /\ (forall j, j + d < length x -> at_ x j = at_ x (j + d)).
Proof.
  intros g1 g2 x c c' d Hg1 Hg12 Hm1 Hm2 Hcc Hd HLR.
  assert (Hcd : c < d).
  { destruct (le_lt_dec d c) as [Hdc | Hdc]; [| exact Hdc].
    exfalso. exact (cr_no_short g1 x c d Hg1 Hm1 Hd Hdc HLR). }
  split; [exact Hcd |].
  destruct Hm1 as [Hc1 Hmax1]. destruct Hm2 as [Hc2 Hmax2].
  destruct (le_lt_dec (length x) (c + d)) as [Hle | Hlt].
  - intros j Hj. specialize (HLR (j + d)). replace (j + d - d) with j in HLR by lia.
    symmetry. apply HLR; lia.
  - assert (Ht1 : lexlt g1 (skipn (c + d) x) (skipn c x)) by (apply Hmax1; lia).
    assert (E1 := cr_split x (c - c') c'). replace (c - c' + c') with c in E1 by lia.
    assert (F : firstn (c - c') (skipn (c' + d) x) = firstn (c - c') (skipn c' x)).
    { apply cr_list_ext.
      - rewrite cr_length_firstn by (rewrite cr_length_skipn; lia).
        rewrite cr_length_firstn by (rewrite cr_length_skipn; lia). reflexivity.
      - intros i Hi. rewrite cr_length_firstn in Hi by (rewrite cr_length_skipn; lia).
        rewrite !cr_nth_firstn by lia. rewrite !cr_nth_skipn.
        specialize (HLR (c' + d + i)). unfold at_ in HLR.
        replace (c' + d + i - d) with (c' + i) in HLR by lia. apply HLR; lia. }
    assert (E2 := cr_split x (c - c') (c' + d)). replace (c - c' + (c' + d)) with (c + d) in E2 by lia.
    rewrite F in E2.
    assert (Ht2 : lexlt g2 (skipn (c + d) x) (skipn c x)).
    { apply (cr_lex_cancel g2 (firstn (c - c') (skipn c' x))). rewrite <- E1, <- E2. apply Hmax2; lia. }
    pose proof (cr_lex_both g1 g2 Hg12 _ _ Ht1 Ht2) as Hpre.
    intros j Hj. destruct (le_lt_dec c j) as [Hcj | Hjc].
    + specialize (Hpre (j - c)). rewrite !cr_nth_skipn, cr_length_skipn in Hpre.
      replace (c + d + (j - c)) with (j + d) in Hpre by lia. replace (c + (j - c)) with j in Hpre by lia.
      unfold at_. symmetry. apply Hpre. lia.
    + specialize (HLR (j + d)). replace (j + d - d) with j in HLR by lia.
      symmetry. apply HLR; lia.
Qed.

Lemma cr_nonper : forall g1 g2 (x : list Z) c c' p,
  (forall a b, g1 a b = true -> g1 b a = false) ->
  (forall a b, a <> b -> g1 a b = true -> g2 a b = true -> False) ->
  is_maxsuf g1 x c -> is_maxsuf g2 x c' -> c' <= c ->
  smallest_period (skipn c x) p ->
  forall d, 1 <= d -> d <= length x - c -> LR x c d ->
  forall j, j + p < length x -> at_ x j = at_ x (j + p).
Proof.
  intros g1 g2 x c c' p Hg1 Hg12 Hm1 Hm2 Hcc Hsp.
  assert (Hc : c < length x) by (destruct Hm1; assumption).
  destruct Hsp as [[Hp1 Hpv] [Hplen Hpmin]].
  assert (Main : forall n d, d <= n -> 1 <= d -> d <= length x - c -> LR x c d ->
    forall j, j + p < length x -> at_ x j = at_ x (j + p)).
  { induction n as [|n IHn]; intros d Hdn Hd1 Hdv HLR.
    - lia.
    - destruct (cr_crit g1 g2 x c c' d Hg1 Hg12 Hm1 Hm2 Hcc Hd1 HLR) as [Hcd Hper].
      assert (Hpd : p <= d).
      { apply Hpmin; [| rewrite cr_length_skipn; exact Hdv].
        unfold is_period. split; [exact Hd1|]. intros j Hj. rewrite cr_length_skipn in Hj.
        unfold at_ in *. rewrite !cr_nth_skipn.
        replace (c + (j + d)) with (c + j + d) by lia. apply Hper. lia. }
      destruct (Nat.eq_dec p d) as [Epd | Npd].
      + rewrite Epd. exact Hper.
      + refine (IHn (d - p) _ _ _ _); [lia | lia | lia |].
        intros j Hj1 Hj2 Hj3.
        assert (A1 : at_ x j = at_ x (j + p)).
        { specialize (Hpv (j - c)). unfold at_ in Hpv |- *. rewrite !cr_nth_skipn, cr_length_skipn in Hpv.
          replace (c + (j - c)) with j in Hpv by lia. replace (c + (j - c + p)) with (j + p) in Hpv by lia.
          apply Hpv. lia. }
        assert (A2 : at_ x (j - (d - p)) = at_ x (j + p)).
        { replace (j + p) with (j - (d - p) + d) by lia. apply Hper. lia. }
        congruence. }
  intros d Hd1 Hdv HLR. exact (Main d d (le_n d) Hd1 Hdv HLR).
Qed.

Lemma cr_crit_main : forall g1 g2 (x : list Z) c c' p,
  (forall a b, g1 a b = true -> g1 b a = false) ->
  (forall a b, a <> b -> g1 a b = true -> g2 a b = true -> False) ->
  is_maxsuf g1 x c -> is_maxsuf g2 x c' -> c' <= c ->
  smallest_period (skipn c x) p -> TW_CRIT x c p.
Proof.
  intros g1 g2 x c c' p Hg1 Hg12 Hm1 Hm2 Hcc Hsp.
  assert (Hc : c < length x) by (destruct Hm1; assumption).
  pose proof Hsp as [[Hp1 Hpv] [Hplen Hpmin]].
  rewrite cr_length_skipn in Hplen.
  assert (Hvper : forall d, (forall j, j + d < length x -> at_ x j = at_ x (j + d)) ->
    1 <= d -> d <= length x - c -> p <= d).
  { intros d Hper Hd1 Hdv. apply Hpmin; [| rewrite cr_length_skipn; exact Hdv].
    unfold is_period. split; [exact Hd1|]. intros j Hj. rewrite cr_length_skipn in Hj.
    unfold at_ in *. rewrite !cr_nth_skipn.
    replace (c + (j + d)) with (c + j + d) by lia. apply Hper. lia. }
  unfold TW_CRIT. split; [exact Hc|]. split; [exact Hp1|]. split; [lia|]. split.
  - intros H.
    assert (Hxp : forall j, j + p < length x -> at_ x j = at_ x (j + p)).
    { intros j Hj. destruct (le_lt_dec c j) as [Hcj | Hjc]; [| exact (H j Hjc)].
      specialize (Hpv (j - c)). unfold at_ in Hpv |- *. rewrite !cr_nth_skipn, cr_length_skipn in Hpv.
      replace (c + (j - c)) with j in Hpv by lia. replace (c + (j - c + p)) with (j + p) in Hpv by lia.
      apply Hpv. lia. }
    split; [exact Hxp|]. split.
    + assert (HLRp : LR x c p).
      { intros j Hj1 Hj2 Hj3. pose proof (Hxp (j - p) ltac:(lia)) as E.
        replace (j - p + p) with j in E by lia. symmetry. exact E. }
      destruct (cr_crit g1 g2 x c c' p Hg1 Hg12 Hm1 Hm2 Hcc Hp1 HLRp) as [Hcp _]. lia.
    + intros d Hd HLR.
      destruct (cr_crit g1 g2 x c c' d Hg1 Hg12 Hm1 Hm2 Hcc ltac:(lia) HLR) as [_ Hper].
      assert (p <= d) by (apply Hvper; [exact Hper | lia | lia]). lia.
  - intros H. split.
    + destruct (Nat.eq_dec c 0) as [E | E]; [| lia].
      exfalso. apply H. intros j Hj. lia.
    + intros d Hd HLR.
      destruct (cr_crit g1 g2 x c c' d Hg1 Hg12 Hm1 Hm2 Hcc ltac:(lia) HLR) as [Hcd _].
      assert (Hdv : d <= length x - c).
      { destruct (Nat.max_spec (c - 1) (length x - c)) as [[_ M] | [_ M]]; rewrite M in Hd; lia. }
      apply H. intros j Hj.
      exact (cr_nonper g1 g2 x c c' p Hg1 Hg12 Hm1 Hm2 Hcc Hsp d ltac:(lia) Hdv HLR j ltac:(lia)).
Qed.

Theorem crit_ok : CRIT_OK.
Proof.
  unfold CRIT_OK. intros x c1 p1 c2 p2 Hx Hm1 Hs1 Hm2 Hs2.
  unfold tw_cut. destruct (c1 <? c2) eqn:E.
  - apply Nat.ltb_lt in E.
    exact (cr_crit_main Z.ltb Z.gtb x c2 c1 p2 cr_ltb_asym cr_lg Hm2 Hm1 ltac:(lia) Hs2).
  - apply Nat.ltb_ge in E.
    exact (cr_crit_main Z.gtb Z.ltb x c1 c2 p1 cr_gtb_asym cr_gl Hm1 Hm2 E Hs1).
Qed.
