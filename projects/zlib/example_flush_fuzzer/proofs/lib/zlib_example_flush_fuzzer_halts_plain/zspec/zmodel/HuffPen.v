(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffFib HuffHeap HuffBuild HuffBuild2 HuffGen HuffGen2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint nondec (l : list Z) : Prop :=
  match l with [] => True | x :: r => match r with [] => True | y :: _ => x <= y end /\ nondec r end.
Fixpoint noninc (l : list Z) : Prop :=
  match l with [] => True | x :: r => match r with [] => True | y :: _ => y <= x end /\ noninc r end.

Lemma nondec_cons_inv : forall x l, nondec (x :: l) -> nondec l /\ forall y, In y l -> x <= y.
Proof.
  intros x l. revert x. induction l as [|y l IH]; intros x H; cbn in H.
  - split; [exact I| intros ? []].
  - destruct H as [Hxy Hl]. split; [exact Hl|]. intros z [<-|Hz]; [lia|].
    destruct (IH y Hl) as [_ A]. specialize (A z Hz). lia.
Qed.
Lemma noninc_cons_inv : forall x l, noninc (x :: l) -> noninc l /\ forall y, In y l -> y <= x.
Proof.
  intros x l. revert x. induction l as [|y l IH]; intros x H; cbn in H.
  - split; [exact I| intros ? []].
  - destruct H as [Hxy Hl]. split; [exact Hl|]. intros z [<-|Hz]; [lia|].
    destruct (IH y Hl) as [_ A]. specialize (A z Hz). lia.
Qed.
Lemma nondec_cons : forall x l, nondec l -> (forall y, In y l -> x <= y) -> nondec (x :: l).
Proof. intros x [|y l] H A; cbn; [tauto|]. split; [apply A; left; reflexivity| exact H]. Qed.
Lemma noninc_cons : forall x l, noninc l -> (forall y, In y l -> y <= x) -> noninc (x :: l).
Proof. intros x [|y l] H A; cbn; [tauto|]. split; [apply A; left; reflexivity| exact H]. Qed.

Lemma nondec_app : forall a b, nondec (a ++ b) <-> nondec a /\ nondec b /\ (forall x y, In x a -> In y b -> x <= y).
Proof.
  induction a as [|x a IH]; intros b; cbn [app].
  - split; [intros H; split; [exact I|]; split; [exact H| intros ? ? []] | intros (_ & H & _); exact H].
  - split.
    + intros H. apply nondec_cons_inv in H. destruct H as [H A]. apply IH in H. destruct H as (H1 & H2 & H3).
      split; [apply nondec_cons; [exact H1| intros; apply A; apply in_app_iff; now left]|]. split; [exact H2|].
      intros p q [<-|Hp] Hq; [apply A; apply in_app_iff; now right| apply H3; assumption].
    + intros (H1 & H2 & H3). apply nondec_cons_inv in H1. destruct H1 as [H1 A]. apply nondec_cons.
      * apply IH. repeat split; auto. intros; apply H3; [right|]; assumption.
      * intros y Hy. apply in_app_iff in Hy. destruct Hy; [apply A| apply H3; [left; reflexivity|]]; assumption.
Qed.

Lemma sorted_perm_eq : forall a b, nondec a -> nondec b -> Permutation a b -> a = b.
Proof.
  induction a as [|x a IH]; intros b Sa Sb P.
  - apply Permutation_nil in P. congruence.
  - destruct b as [|y b]; [apply Permutation_sym, Permutation_nil in P; congruence|].
    apply nondec_cons_inv in Sa. apply nondec_cons_inv in Sb. destruct Sa as [Sa Ax]. destruct Sb as [Sb Ay].
    assert (x = y).
    { assert (Hx : In x (y :: b)) by (apply (Permutation_in _ P); left; reflexivity).
      assert (Hy : In y (x :: a)) by (apply (Permutation_in _ (Permutation_sym P)); left; reflexivity).
      destruct Hx as [<-|Hx]; [reflexivity|]. destruct Hy as [<-|Hy]; [reflexivity|].
      specialize (Ax y Hy). specialize (Ay x Hx). lia. }
    subst y. f_equal. apply IH; [exact Sa| exact Sb|]. eapply Permutation_cons_inv. exact P.
Qed.

Lemma noninc_perm_eq : forall a b, noninc a -> noninc b -> Permutation a b -> a = b.
Proof.
  intros a b Sa Sb P.
  assert (N : forall l, noninc l -> nondec (map Z.opp l)).
  { induction l as [|x [|y l] IH]; intros H; cbn in *; [exact I| tauto|]. split; [lia|]. apply IH. tauto. }
  assert (E : map Z.opp a = map Z.opp b) by (apply sorted_perm_eq; [apply N; exact Sa| apply N; exact Sb| apply Permutation_map; exact P]).
  assert (I : forall l, map Z.opp (map Z.opp l) = l) by (induction l; cbn; [reflexivity|]; rewrite IHl; f_equal; lia).
  rewrite <- (I a), <- (I b), E. reflexivity.
Qed.

Fixpoint dot (a b : list Z) : Z :=
  match a, b with x :: a', y :: b' => x * y + dot a' b' | _, _ => 0 end.

Lemma dot_app_l : forall a1 a2 b, (length a1 <= length b)%nat ->
  dot (a1 ++ a2) b = dot a1 (firstn (length a1) b) + dot a2 (skipn (length a1) b).
Proof.
  induction a1 as [|x a1 IH]; intros a2 b Hl; cbn; [reflexivity|].
  destruct b as [|y b]; cbn in *; [lia|]. rewrite IH by lia. lia.
Qed.

Lemma dot_bubble : forall w d1 c0 d2,
  noninc w -> (forall e, In e d1 -> c0 <= e) -> (length (d1 ++ c0 :: d2) <= length w)%nat ->
  dot w (c0 :: d1 ++ d2) <= dot w (d1 ++ c0 :: d2).
Proof.
  intros w d1. revert w. induction d1 as [|e d1 IH]; intros w c0 d2 Sw Hmin Hl; cbn [app]; [lia|].
  rewrite !length_app in Hl. cbn [length] in Hl.
  destruct w as [|w0 [|w1 w]]; cbn [length] in Hl; [lia| lia|].
  pose proof (noninc_cons_inv _ _ Sw) as [Sw1 A0]. 
  specialize (IH (w1 :: w) c0 d2 Sw1 ltac:(intros; apply Hmin; right; assumption) ltac:(rewrite length_app; cbn [length] in *; lia)).
  pose proof (Hmin e (or_introl eq_refl)) as He. pose proof (A0 w1 (or_introl eq_refl)) as W01.
  cbn [dot] in *. nia.
Qed.

Theorem dot_sorted_le : forall w c d,
  noninc w -> nondec c -> Permutation c d -> (length d <= length w)%nat -> dot w c <= dot w d.
Proof.
  intros w c. revert w. induction c as [|c0 c IH]; intros w d Sw Sc P Hl.
  - apply Permutation_nil in P. subst d. destruct w; cbn; lia.
  - assert (Hin : In c0 d) by (apply (Permutation_in _ P); left; reflexivity).
    destruct (in_split _ _ Hin) as (d1 & d2 & ->).
    apply nondec_cons_inv in Sc. destruct Sc as [Sc Amin].
    assert (P' : Permutation c (d1 ++ d2)) by (apply Permutation_cons_inv with c0; rewrite P; apply Permutation_sym, Permutation_middle).
    etransitivity; [| apply dot_bubble; [exact Sw| | exact Hl]].
    + destruct w as [|w0 w]; [rewrite length_app in Hl; cbn in Hl; lia|]. cbn [dot app].
      pose proof (noninc_cons_inv _ _ Sw) as [Sw' _].
      specialize (IH w (d1 ++ d2) Sw' Sc P' ltac:(rewrite length_app in *; cbn in Hl; lia)). lia.
    + intros e He. apply Amin. apply (Permutation_in _ (Permutation_sym P')). apply in_app_iff. now left.
Qed.

Lemma dot_map : forall {A} (f g : A -> Z) l, dot (map f l) (map g l) = zsum (map (fun x => f x * g x) l).
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma combine_map : forall {A} (f g : A -> Z) l, combine (map f l) (map g l) = map (fun x => (f x, g x)) l.
Proof. induction l; cbn; [reflexivity|]. rewrite IHl. reflexivity. Qed.


Lemma hprof_length : forall d t, length (hprof d t) = length (hprof 0 t).
Proof.
  intros d t. revert d. induction t; intros d; cbn [hprof]; [reflexivity|].
  rewrite !length_app, (IHt1 (d + 1)), (IHt2 (d + 1)). symmetry. rewrite (IHt1 (0 + 1)), (IHt2 (0 + 1)). reflexivity.
Qed.

Lemma hheight_leaves : forall t, hheight t + 1 <= Z.of_nat (length (hprof 0 t)).
Proof.
  induction t; cbn [hheight hprof length]; [lia|]. rewrite length_app, !(hprof_length (0 + 1)), Nat2Z.inj_add.
  pose proof (hheight_nonneg t1). pose proof (hheight_nonneg t2). lia.
Qed.

Lemma depth_le_leaves : forall (U : list Z) (L : Z -> Z) (T : htree),
  Permutation (map (fun e => (ea e, ed e)) (hprof 0 T)) (map (fun j => (j, L j)) U) ->
  forall j, In j U -> L j <= zlen U - 1.
Proof.
  intros U L T P j Hj.
  assert (Hin : In (j, L j) (map (fun e => (ea e, ed e)) (hprof 0 T))).
  { apply (Permutation_in _ (Permutation_sym P)). apply in_map_iff. exists j. auto. }
  apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2.
  pose proof (hprof_dep 0 T e He) as D. pose proof (hheight_leaves T) as HH.
  pose proof (Permutation_length P) as PL. rewrite !length_map in PL. unfold zlen. rewrite <- PL. lia.
Qed.


Fixpoint afind (f : nat) (BC : arr) (b : Z) : Z :=
  match f with O => b | S f' => if arr_get BC b =? 0 then afind f' BC (b - 1) else b end.

Definition atrip (ML : Z) (BC : arr) : arr := bl_adj ML BC (afind (Z.to_nat ML) BC (ML - 1)).

Fixpoint arepair (n : nat) (ML : Z) (BC : arr) : arr :=
  match n with O => BC | S n' => arepair n' ML (atrip ML BC) end.

Lemma afind_flat : forall t f s FC DL HP HL HM DP BC OL SL MC b,
  gen_bitlen_find f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) b = afind f BC b.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_find afind]; [reflexivity|].
  unfold bl_count_get. autorewrite with btupd. destruct (arr_get BC b =? 0); [apply IH| reflexivity].
Qed.

Lemma gb_loop2_fun : forall t f s FC DL HP HL HM DP BC OL SL MC rex,
  1 <= rex -> (Z.to_nat rex <= f)%nat ->
  gen_bitlen_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (sd_max_length t) (2 * rex)
  = bt_upd s t FC DL HP HL HM DP (arepair (Z.to_nat rex) (sd_max_length t) BC) OL SL MC.
Proof.
  intros t. induction f as [|f IH]; intros s FC DL HP HL HM DP BC OL SL MC rex Hrex Hf; [lia|].
  pose proof (GL2_step t (sd_max_length t) f s FC DL HP HL HM DP BC OL SL MC (2 * rex)) as E. cbv zeta in E. rewrite E. clear E.
  rewrite afind_flat. replace (Z.to_nat rex) with (S (Z.to_nat (rex - 1))) by lia. cbn [arepair]. unfold atrip.
  destruct (Z.ltb_spec 0 (2 * rex - 2)).
  - replace (2 * rex - 2) with (2 * (rex - 1)) by lia. rewrite IH by lia. reflexivity.
  - replace (Z.to_nat (rex - 1)) with 0%nat by lia. reflexivity.
Qed.

Lemma afind_ext : forall f B1 B2 b, (forall i, b - Z.of_nat f < i <= b -> arr_get B1 i = arr_get B2 i) ->
  afind f B1 b = afind f B2 b.
Proof.
  induction f as [|f IH]; intros B1 B2 b E; cbn [afind]; [reflexivity|].
  rewrite Nat2Z.inj_succ in E. rewrite (E b) by lia. destruct (arr_get B2 b =? 0); [|reflexivity]. apply IH. intros i Hi. apply E. lia.
Qed.

Lemma afind_range : forall f B b, b - Z.of_nat f <= afind f B b <= b.
Proof.
  induction f as [|f IH]; intros B b; cbn [afind]; [lia|]. rewrite Nat2Z.inj_succ.
  destruct (arr_get B b =? 0); [|lia]. pose proof (IH B (b - 1)). lia.
Qed.

Definition lens_asc (B : Z -> Z) (ML : Z) : list Z :=
  flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota 1 (Z.to_nat ML)).

Lemma lens_asc_nondec : forall B ML, nondec (lens_asc B ML).
Proof.
  intros B ML. unfold lens_asc.
  assert (G : forall a n, nondec (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n)) /\
                         forall x, In x (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n)) -> a <= x).
  { intros a n. revert a. induction n as [|n IH]; intros a; cbn; [split; [exact I| intros ? []]|].
    destruct (IH (a + 1)) as [S1 A1]. split.
    - apply nondec_app. split; [|split; [exact S1|]].
      + induction (Z.to_nat (B a)); cbn; [exact I|]. destruct n0; cbn in *; [tauto|]. split; [lia| exact IHn0].
      + intros x y Hx Hy. apply repeat_spec in Hx. subst x. specialize (A1 y Hy). lia.
    - intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [apply repeat_spec in Hx; lia|]. specialize (A1 x Hx). lia. }
  apply (proj1 (G 1 (Z.to_nat ML))).
Qed.

Definition zcnt (v : Z) (l : list Z) : Z := zsum (map (fun x => if x =? v then 1 else 0) l).

Lemma zcnt_app : forall v a b, zcnt v (a ++ b) = zcnt v a + zcnt v b.
Proof. intros. unfold zcnt. rewrite map_app, zsum_app. reflexivity. Qed.
Lemma zcnt_cons : forall v x l, zcnt v (x :: l) = (if x =? v then 1 else 0) + zcnt v l.
Proof. intros. reflexivity. Qed.
Lemma zcnt_nonneg : forall v l, 0 <= zcnt v l.
Proof. intros. unfold zcnt. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & _). destruct (y =? v); lia. Qed.
Lemma zcnt_repeat : forall v b n, zcnt v (repeat b n) = if b =? v then Z.of_nat n else 0.
Proof. intros. induction n; cbn [repeat]; [destruct (b =? v); reflexivity|]. rewrite zcnt_cons, IHn. destruct (b =? v); lia. Qed.
Lemma zcnt_count_occ : forall v l, zcnt v l = Z.of_nat (count_occ Z.eq_dec l v).
Proof.
  intros v l. induction l as [|x l IH]; [reflexivity|]. rewrite zcnt_cons, IH. cbn [count_occ].
  destruct (Z.eq_dec x v), (Z.eqb_spec x v); try lia; subst; contradiction.
Qed.
Lemma zcnt_perm : forall a b, (forall v, zcnt v a = zcnt v b) -> Permutation a b.
Proof.
  intros a b H. apply (Permutation_count_occ Z.eq_dec). intros v. specialize (H v). rewrite !zcnt_count_occ in H. lia.
Qed.
Lemma zcnt_In : forall v l, In v l <-> 0 < zcnt v l.
Proof.
  intros v l. induction l as [|x l IH]; [cbn; unfold zcnt; cbn; split; [tauto|lia]|].
  rewrite zcnt_cons. cbn. pose proof (zcnt_nonneg v l). destruct (Z.eqb_spec x v); [split; [lia| intros; left; auto]|].
  rewrite IH. split; [intros [?|?]; [congruence|lia]| intros; right; lia].
Qed.
Lemma zcnt_length : forall l lo n,
  (forall x, In x l -> lo <= x < lo + Z.of_nat n) ->
  zsum (map (fun v => zcnt v l) (ziota lo n)) = Z.of_nat (length l).
Proof.
  intros l lo n H. induction l as [|x l IH].
  - cbn [length]. change (Z.of_nat 0) with 0. unfold zcnt. cbn [map zsum]. induction (ziota lo n); cbn; lia.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    transitivity (zsum (map (fun v => (if x =? v then 1 else 0) + zcnt v l) (ziota lo n))); [apply zsum_map_ext; intros; rewrite zcnt_cons; reflexivity|].
    rewrite zsum_map_add, IH by (intros; apply H; right; assumption).
    enough (zsum (map (fun v => if x =? v then 1 else 0) (ziota lo n)) = 1) by lia.
    pose proof (H x (or_introl eq_refl)) as Hx. clear IH H. revert lo Hx. induction n as [|n IH]; intros lo Hx; [cbn in Hx; lia|].
    cbn [ziota map zsum]. rewrite Nat2Z.inj_succ in Hx. destruct (Z.eqb_spec x lo).
    + subst. enough (zsum (map (fun v : Z => if lo =? v then 1 else 0) (ziota (lo + 1) n)) = 0) by lia.
      clear. assert (G : forall a, lo < a -> zsum (map (fun v : Z => if lo =? v then 1 else 0) (ziota a n)) = 0).
      { induction n; intros a Ha; cbn; [reflexivity|]. destruct (Z.eqb_spec lo a); [lia|]. rewrite IHn by lia. reflexivity. }
      apply G. lia.
    + rewrite IH by lia. reflexivity.
Qed.

Lemma lens_asc_cnt_gen : forall B a n v, (forall b, a <= b < a + Z.of_nat n -> 0 <= B b) ->
  zcnt v (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n)) = if (a <=? v) && (v <? a + Z.of_nat n) then B v else 0.
Proof.
  intros B a n. revert a. induction n as [|n IH]; intros a v NN; cbn [ziota flat_map].
  - unfold zcnt. cbn [map zsum]. change (Z.of_nat 0) with 0. destruct (Z.leb_spec a v), (Z.ltb_spec v (a + 0)); cbn [andb]; lia.
  - rewrite zcnt_app, zcnt_repeat, Nat2Z.inj_succ. rewrite IH by (intros; apply NN; lia).
    pose proof (NN a ltac:(lia)).
    destruct (Z.eqb_spec a v), (Z.leb_spec a v), (Z.leb_spec (a + 1) v), (Z.ltb_spec v (a + 1 + Z.of_nat n)), (Z.ltb_spec v (a + Z.succ (Z.of_nat n))); subst; cbn [andb]; lia.
Qed.

Lemma lens_asc_cnt : forall B ML v, (forall b, 1 <= b <= ML -> 0 <= B b) ->
  zcnt v (lens_asc B ML) = if (1 <=? v) && (v <=? ML) then B v else 0.
Proof.
  intros B ML v NN. unfold lens_asc. rewrite lens_asc_cnt_gen by (intros; apply NN; lia).
  destruct (Z.leb_spec 1 v), (Z.ltb_spec v (1 + Z.of_nat (Z.to_nat ML))), (Z.leb_spec v ML); cbn [andb]; try reflexivity; try lia.
Qed.

Lemma lens_asc_In : forall B ML x, In x (lens_asc B ML) -> 1 <= x <= ML /\ 0 < B x.
Proof.
  intros B ML x Hx. unfold lens_asc in Hx. apply in_flat_map in Hx. destruct Hx as (b & Hb & Hx).
  apply in_ziota in Hb. pose proof (repeat_spec _ _ _ Hx). subst.
  assert (Z.to_nat (B b) <> 0%nat) by (intros E; rewrite E in Hx; destruct Hx). lia.
Qed.

Lemma nondec_is_lens_asc : forall l B ML,
  nondec l -> (forall x, In x l -> 1 <= x <= ML) -> (forall b, 1 <= b <= ML -> 0 <= B b) ->
  (forall v, 1 <= v <= ML -> zcnt v l = B v) -> l = lens_asc B ML.
Proof.
  intros l B ML ND RG NN CNT. apply sorted_perm_eq; [exact ND| apply lens_asc_nondec|].
  apply zcnt_perm. intros v. rewrite lens_asc_cnt by exact NN.
  destruct (Z.leb_spec 1 v); destruct (Z.leb_spec v ML); cbn [andb]; try (apply CNT; lia);
    (destruct (Z_lt_le_dec 0 (zcnt v l)) as [P|P]; [apply zcnt_In in P; specialize (RG v P); lia| pose proof (zcnt_nonneg v l); lia]).
Qed.

Lemma lens_asc_split : forall B ML m, 1 <= m <= ML ->
  lens_asc B ML = flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota 1 (Z.to_nat (m - 1)))
                  ++ repeat m (Z.to_nat (B m))
                  ++ flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota (m + 1) (Z.to_nat (ML - m))).
Proof.
  intros B ML m Hm. unfold lens_asc.
  replace (Z.to_nat ML) with (Z.to_nat (m - 1) + S (Z.to_nat (ML - m)))%nat by lia.
  assert (G : forall a p q, ziota a (p + q) = ziota a p ++ ziota (a + Z.of_nat p) q).
  { intros a p. revert a. induction p; intros a q; cbn; [f_equal; lia|]. rewrite IHp. f_equal. f_equal. f_equal. lia. }
  rewrite G, flat_map_app. f_equal. cbn [ziota flat_map]. replace (1 + Z.of_nat (Z.to_nat (m - 1))) with m by lia. reflexivity.
Qed.

Lemma nth_app_l : forall {A} (d : A) a b i, (i < length a)%nat -> nth i (a ++ b) d = nth i a d.
Proof. intros. apply app_nth1. assumption. Qed.
Lemma nth_app_r : forall {A} (d : A) a b i, (length a <= i)%nat -> nth i (a ++ b) d = nth (i - length a) b d.
Proof. intros. apply app_nth2. assumption. Qed.

Lemma flat_map_repeat_In_ge : forall B a n x,
  In x (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n)) -> a <= x.
Proof.
  intros B a n x Hx. apply in_flat_map in Hx. destruct Hx as (b & Hb & Hx). apply in_ziota in Hb. apply repeat_spec in Hx. lia.
Qed.

Lemma length_flat_map_repeat : forall B a n, (forall b, a <= b < a + Z.of_nat n -> 0 <= B b) ->
  Z.of_nat (length (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n))) = zsum (map B (ziota a n)).
Proof.
  intros B a n. revert a. induction n; intros a NN; cbn [ziota flat_map map zsum]; [reflexivity|].
  rewrite length_app, repeat_length, Nat2Z.inj_add, IHn by (intros; apply NN; lia). pose proof (NN a ltac:(lia)). lia.
Qed.

Lemma kraft_cut : forall t d D H,
  0 <= d <= D -> D < d + hheight t -> d + hheight t <= H ->
  zsum (map (fun e => if ed e <=? D then 2 ^ (H - ed e) else 0) (hprof d t)) <= 2 ^ (H - d) - 2 ^ (H - D).
Proof.
  induction t as [w a|l IHl r IHr]; intros d D H Hd HD HH; cbn [hprof hheight map zsum ed] in *; [lia|].
  rewrite map_app, zsum_app.
  pose proof (hheight_nonneg l). pose proof (hheight_nonneg r).
  assert (FULL : forall t' , d + 1 + hheight t' <= H ->
            zsum (map (fun e => if ed e <=? D then 2 ^ (H - ed e) else 0) (hprof (d + 1) t')) <= 2 ^ (H - (d + 1))).
  { intros t' Ht'. rewrite <- (kraft_hprof H (d + 1) t') by lia. unfold kraft.
    assert (G : forall lst, (forall e, In e lst -> 0 <= H - ed e) ->
              zsum (map (fun e => if ed e <=? D then 2 ^ (H - ed e) else 0) lst) <= zsum (map (fun e => 2 ^ (H - ed e)) lst)).
    { induction lst as [|e lst IH]; intros He; cbn; [lia|]. pose proof (Z.pow_nonneg 2 (H - ed e) ltac:(lia)).
      specialize (IH ltac:(intros; apply He; right; assumption)). destruct (ed e <=? D); lia. }
    apply G. intros e He. pose proof (hprof_dep (d + 1) t' e He). lia. }
  assert (E2 : 2 ^ (H - d) = 2 * 2 ^ (H - (d + 1))) by (replace (H - d) with (Z.succ (H - (d + 1))) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  destruct (Z_le_gt_dec (d + 1) D) as [LE|GT].
  -
    destruct (Z_lt_le_dec D (d + 1 + hheight l)) as [INL|NL].
    + pose proof (IHl (d + 1) D H ltac:(lia) INL ltac:(lia)). pose proof (FULL r ltac:(lia)). lia.
    + assert (INR : D < d + 1 + hheight r) by lia.
      pose proof (IHr (d + 1) D H ltac:(lia) INR ltac:(lia)). pose proof (FULL l ltac:(lia)). lia.
  -
    assert (Z0 : forall t', zsum (map (fun e => if ed e <=? D then 2 ^ (H - ed e) else 0) (hprof (d + 1) t')) = 0).
    { intros t'. assert (G : forall lst, (forall e, In e lst -> D < ed e) -> zsum (map (fun e => if ed e <=? D then 2 ^ (H - ed e) else 0) lst) = 0).
      { induction lst as [|e lst IH]; intros He; cbn; [reflexivity|]. pose proof (He e (or_introl eq_refl)).
        destruct (Z.leb_spec (ed e) D); [lia|]. rewrite IH by (intros; apply He; right; assumption). lia. }
      apply G. intros e He. pose proof (hprof_dep (d + 1) t' e He). lia. }
    rewrite !Z0. assert (D = d) by lia. subst D. pose proof (Z.pow_nonneg 2 (H - d) ltac:(lia)). lia.
Qed.


Fixpoint sincr (l : list Z) : Prop :=
  match l with [] => True | x :: r => match r with [] => True | y :: _ => x < y end /\ sincr r end.

Lemma sincr_cons_inv : forall x l, sincr (x :: l) -> sincr l /\ forall y, In y l -> x < y.
Proof.
  intros x l. revert x. induction l as [|y l IH]; intros x H; cbn in H.
  - split; [exact I| intros ? []].
  - destruct H as [Hxy Hl]. split; [exact Hl|]. intros z [<-|Hz]; [lia|]. destruct (IH y Hl) as [_ A]. specialize (A z Hz). lia.
Qed.

Lemma sincr_ziota : forall a n, sincr (ziota a n).
Proof.
  intros a n. revert a. induction n; intros a; cbn; [exact I|]. split; [|apply IHn].
  destruct n; cbn; [exact I| lia].
Qed.

Lemma sincr_filter : forall p l, sincr l -> sincr (filter p l).
Proof.
  induction l as [|x l IH]; intros H; cbn; [exact I|].
  apply sincr_cons_inv in H. destruct H as [H A]. specialize (IH H).
  destruct (p x); [|exact IH].
  destruct (filter p l) as [|y r] eqn:E; cbn; [tauto|]. split; [|exact IH].
  apply A. apply (filter_In p y l). rewrite E. left. reflexivity.
Qed.

Lemma sincr_NoDup : forall l, sincr l -> NoDup l.
Proof.
  induction l as [|x l IH]; intros H; constructor.
  - apply sincr_cons_inv in H. destruct H as [_ A]. intros Hx. specialize (A x Hx). lia.
  - apply IH. apply sincr_cons_inv in H. tauto.
Qed.

Lemma noninc_map_sincr : forall (g : Z -> Z) l, sincr l ->
  (forall x y, In x l -> In y l -> x <= y -> g y <= g x) -> noninc (map g l).
Proof.
  induction l as [|x l IH]; intros Sl M; cbn; [exact I|].
  apply sincr_cons_inv in Sl. destruct Sl as [Sl A].
  split; [| apply IH; [exact Sl| intros; apply M; cbn; auto]].
  destruct l as [|y l']; cbn; [exact I|]. apply M; cbn; auto. specialize (A y (or_introl eq_refl)). lia.
Qed.

Lemma nondec_map_sincr : forall (g : Z -> Z) l, sincr l ->
  (forall x y, In x l -> In y l -> x <= y -> g x <= g y) -> nondec (map g l).
Proof.
  induction l as [|x l IH]; intros Sl M; cbn; [exact I|].
  apply sincr_cons_inv in Sl. destruct Sl as [Sl A].
  split; [| apply IH; [exact Sl| intros; apply M; cbn; auto]].
  destruct l as [|y l']; cbn; [exact I|]. apply M; cbn; auto. specialize (A y (or_introl eq_refl)). lia.
Qed.

Lemma nondec_map_min : forall M l, nondec l -> nondec (map (fun x => Z.min x M) l).
Proof.
  induction l as [|x [|y l] IH]; intros H; cbn in *; [exact I| tauto|]. destruct H as [H1 H2]. split; [lia|]. apply IH. exact H2.
Qed.

Fixpoint idx (j : Z) (l : list Z) : nat :=
  match l with [] => O | x :: r => if x =? j then O else S (idx j r) end.

Lemma idx_lt : forall j l, In j l -> (idx j l < length l)%nat.
Proof.
  induction l as [|x l IH]; intros H; cbn in *; [tauto|]. destruct (Z.eqb_spec x j); [lia|].
  destruct H as [->|H]; [congruence|]. specialize (IH H). lia.
Qed.

Lemma nth_idx : forall j l d, In j l -> nth (idx j l) l d = j.
Proof.
  induction l as [|x l IH]; intros d H; cbn in *; [tauto|]. destruct (Z.eqb_spec x j); [cbn; congruence|].
  destruct H as [->|H]; [congruence|]. apply IH. exact H.
Qed.

Lemma idx_nth : forall l k d, NoDup l -> (k < length l)%nat -> idx (nth k l d) l = k.
Proof.
  induction l as [|x l IH]; intros k d ND Hk; cbn in *; [lia|].
  inversion ND; subst. destruct k as [|k].
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec x (nth k l d)).
    + exfalso. apply H1. rewrite e. apply nth_In. lia.
    + rewrite IH; auto. lia.
Qed.

Lemma nth_map' : forall (f : Z -> Z) l n d, (n < length l)%nat -> nth n (map f l) d = f (nth n l d).
Proof.
  induction l as [|x l IH]; intros n d Hn; cbn in *; [lia|]. destruct n; [reflexivity|]. apply IH. lia.
Qed.

Lemma list_eq_nth : forall (a b : list Z) d, length a = length b -> (forall n, (n < length a)%nat -> nth n a d = nth n b d) -> a = b.
Proof.
  induction a as [|x a IH]; intros b d Hl Hn; destruct b as [|y b]; cbn in Hl; try discriminate; [reflexivity|].
  f_equal; [exact (Hn 0%nat ltac:(cbn; lia))|]. apply (IH b d); [lia|]. intros n H. exact (Hn (S n) ltac:(cbn; lia)).
Qed.

Lemma map_nth_idx : forall (c : list Z) (l : list Z) d, NoDup l -> length c = length l ->
  map (fun x => nth (idx x l) c d) l = c.
Proof.
  intros c l d ND Hl. apply (list_eq_nth _ _ d); [rewrite length_map; congruence|].
  intros n Hn. rewrite length_map in Hn. rewrite nth_map' by exact Hn. rewrite idx_nth by assumption. reflexivity.
Qed.

Lemma nondec_nth : forall l i j d, nondec l -> (i <= j)%nat -> (j < length l)%nat -> nth i l d <= nth j l d.
Proof.
  induction l as [|x l IH]; intros i j d ND Hij Hj; cbn in Hj; [lia|].
  apply nondec_cons_inv in ND. destruct ND as [ND A].
  destruct i as [|i], j as [|j]; cbn; [lia| | lia|].
  - apply A. apply nth_In. lia.
  - apply IH; auto; lia.
Qed.

Lemma noninc_nth : forall l i j d, noninc l -> (i <= j)%nat -> (j < length l)%nat -> nth j l d <= nth i l d.
Proof.
  induction l as [|x l IH]; intros i j d ND Hij Hj; cbn in Hj; [lia|].
  apply noninc_cons_inv in ND. destruct ND as [ND A].
  destruct i as [|i], j as [|j]; cbn; [lia| | lia|].
  - apply A. apply nth_In. lia.
  - apply IH; auto; lia.
Qed.

Lemma zcnt_map_perm : forall (g : Z -> Z) a b v, Permutation a b -> zcnt v (map g a) = zcnt v (map g b).
Proof. intros. unfold zcnt. rewrite map_map, map_map. apply zsum_map_perm. assumption. Qed.



Lemma zsum_map_nth : forall (g : Z -> Z) (l : list Z) (d : Z),
  zsum (map g l) = zsum (map (fun r => g (nth r l d)) (seq 0 (length l))).
Proof.
  intros g l d. induction l as [|x l IH] using rev_ind; [reflexivity|].
  rewrite map_app, zsum_app, length_app, seq_app, map_app, zsum_app. cbn [length map zsum seq].
  rewrite Nat.add_0_l. rewrite nth_app_r, Nat.sub_diag by lia. cbn [nth].
  rewrite IH. rewrite (zsum_map_ext (fun r : nat => g (nth r (l ++ [x]) d)) (fun r => g (nth r l d)) (seq 0 (length l))); [lia|].
  intros r Hr. apply in_seq in Hr. rewrite nth_app_l by lia. reflexivity.
Qed.

Lemma zsum_map_seq_split : forall (g : nat -> Z) k n, (k <= n)%nat ->
  zsum (map g (seq 0 n)) = zsum (map g (seq 0 k)) + zsum (map g (seq k (n - k))).
Proof. intros g k n Hk. replace n with (k + (n - k))%nat at 1 by lia. rewrite seq_app, map_app, zsum_app. reflexivity. Qed.

Lemma zsum_map_seq_shift : forall (g : nat -> Z) k m,
  zsum (map g (seq k m)) = zsum (map (fun i => g (k + i)%nat) (seq 0 m)).
Proof.
  intros g k m. revert k. induction m as [|m IH]; intros k; cbn [seq map zsum]; [reflexivity|].
  rewrite Nat.add_0_r. f_equal. rewrite IH. rewrite <- seq_shift, map_map. apply zsum_map_ext. intros i _. f_equal. lia.
Qed.

Lemma zsum_repeat : forall (g : Z -> Z) b n, zsum (map g (repeat b n)) = Z.of_nat n * g b.
Proof. intros g b n. induction n; cbn [repeat map zsum]; [lia|]. rewrite IHn. lia. Qed.

Lemma zsum_flat_map_repeat : forall (g : Z -> Z) B a n, (forall b, a <= b < a + Z.of_nat n -> 0 <= B b) ->
  zsum (map g (flat_map (fun b => repeat b (Z.to_nat (B b))) (ziota a n))) = zsum (map (fun b => B b * g b) (ziota a n)).
Proof.
  intros g B a n. revert a. induction n; intros a NN; cbn [ziota flat_map map zsum]; [reflexivity|].
  rewrite map_app, zsum_app, zsum_repeat, IHn by (intros; apply NN; lia). pose proof (NN a ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma filter_length_firstn : forall {A} (p : A -> bool) k (l : list A),
  (length (filter p (firstn k l)) <= length (filter p l))%nat.
Proof.
  intros A p k l. rewrite <- (firstn_skipn k l) at 2. rewrite filter_app, length_app. lia.
Qed.

Lemma filter_all_length : forall {A} (p : A -> bool) (l : list A), (forall x, In x l -> p x = true) -> length (filter p l) = length l.
Proof.
  intros A p l H. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)). cbn. rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma filter_none : forall {A} (p : A -> bool) (l : list A), (forall x, In x l -> p x = false) -> filter p l = [].
Proof.
  intros A p l H. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)). apply IH. intros; apply H; right; assumption.
Qed.

Lemma perm_filter_length : forall {A} (p : A -> bool) (l m : list A), Permutation l m -> length (filter p l) = length (filter p m).
Proof.
  intros A p l m P. induction P as [|x l m P IH|x y l|l m k P1 IH1 P2 IH2]; cbn.
  - reflexivity.
  - destruct (p x); cbn; rewrite IH; reflexivity.
  - destruct (p x), (p y); reflexivity.
  - lia.
Qed.

Lemma nondec_count_lt : forall (l : list Z) (r : nat), nondec l -> (r < length l)%nat ->
  (length (filter (fun x : Z => (x <? nth r l 0)%Z) l) <= r)%nat.
Proof.
  intros l r ND Hr. set (v := nth r l 0). rewrite <- (firstn_skipn r l) at 1. rewrite filter_app, length_app.
  rewrite (filter_none _ (skipn r l)).
  - cbn [length]. pose proof (firstn_le_length r l). pose proof (filter_length_le (fun x : Z => x <? v) (firstn r l)). lia.
  - intros x Hx. apply Z.ltb_ge. apply (In_nth _ _ 0) in Hx. destruct Hx as (i & Hi & <-).
    rewrite nth_skipn. rewrite length_skipn in Hi. subst v. apply nondec_nth; [exact ND| lia| lia].
Qed.

Definition cpen (b : Z) : Z := if b =? 7 then 4320 else 21 * (2 ^ (15 - b) - 1).

Lemma cpen_fib : forall b, 7 <= b <= 15 -> 11340 * (15 - b) <= cpen b * fibZ (b + 1) /\ 0 <= cpen b <= 21 * (2 ^ (15 - b) - 1) /\ cpen b <= 4320.
Proof.
  intros b Hb.
  assert (G : forall k, (k < 9)%nat -> let b := 7 + Z.of_nat k in 11340 * (15 - b) <= cpen b * fibZ (b + 1) /\ 0 <= cpen b <= 21 * (2 ^ (15 - b) - 1) /\ cpen b <= 4320).
  { intros k Hk. do 9 (destruct k as [|k]; [vm_compute; repeat split; discriminate|]). lia. }
  specialize (G (Z.to_nat (b - 7)) ltac:(lia)). cbv zeta in G. replace (7 + Z.of_nat (Z.to_nat (b - 7))) with b in G by lia. exact G.
Qed.


Section Pen.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr) (BC : arr) (OL SL : Z).
Variables (FC DL HP DP : arr) (sub : Z -> htree).

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation UPl := (UP FC0 t).
Local Notation FPf := (FP FC0 t).
Local Notation uu := (u t FC0).
Local Notation MCv := (MCP FC0 t).
Local Notation ML := (sd_max_length t).
Local Notation hm := (hm t FC0).
Local Notation HP7 := (HP7 t FC0 HP).
Local Notation nd := (nd DL HP).
Local Notation leafp := (leafp t FC0 HP).
Local Notation SUM := (SUM t FC0).
Local Notation rng := (rng t FC0).
Local Notation xb := (xbits t).
Local Notation LI := (LI t FC0).
Local Notation KB := (KB t).
Local Notation cntB := (cntB t).
Local Notation N := (N t FC0 DL HP).

Hypothesis INV : Inv4 t FC0 (uu - 1) FC DL HP 1 hm DP sub.

Let U2 := u_ge2 t FC0.
Let H7inj := HP7_inj t FC0 FC DL HP DP sub INV.
Let IDR := ids_range t FC0 FC DL HP DP sub INV.
Let NDNN := nd_nonneg t FC0 FC DL HP DP sub INV.
Let MCF := MC_facts t FC0 FC DL HP DP sub INV.
Let LPOS := leaf_positions t FC0 FC DL HP DP sub INV.
Let SUML := SUM_leaves t FC0 FC DL HP DP sub INV.
Let MLR := ML_range t FC0 FC DL HP DP sub INV.
Let US := u_small t FC0.
Let WO := weight_order t FC0 FC DL HP DP sub INV.
Let LT2 := loop2_trip s t FC0 FC DL HP DP sub INV.


Lemma LI_exists_low : forall BCx rex, LI BCx rex -> 1 <= rex ->
  exists b0, 1 <= b0 <= ML - 1 /\ arr_get BCx b0 <> 0.
Proof.
  intros BCx rex [LEN NN OUT CNT K REX LOW] Hrex. pose proof MLR as MR. pose proof US as [USm _].
  destruct (Exists_dec (fun b => arr_get BCx b <> 0) (ziota 1 (Z.to_nat (ML - 1)))) as [E|NE].
  { intros b. destruct (Z.eq_dec (arr_get BCx b) 0); [right; lia| left; lia]. }
  - apply Exists_exists in E. destruct E as (b0 & Hb0 & Nb0). apply in_ziota in Hb0. exists b0. split; [lia| exact Nb0].
  - exfalso. apply Forall_Exists_neg in NE. rewrite Forall_forall in NE.
    assert (Z0 : SlowB t (arr_get BCx) = 0).
    { unfold SlowB, isum. etransitivity; [apply zsum_map_ext|].
      + intros b Hb. specialize (NE b Hb). apply in_ziota in Hb. replace (arr_get BCx b) with 0 by lia. apply Z.mul_0_l.
      + generalize (ziota 1 (Z.to_nat (ML - 1))). clear. induction l; cbn; lia. }
    unfold HuffGen2.KB in K. unfold SlowB in Z0.
    replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia. replace (ML - 1 + 1) with ML in K by lia.
    rewrite Z.sub_diag, Z.pow_0_r, Z0 in K.
    pose proof (isum_le1 (arr_get BCx) ML ML ltac:(lia) ltac:(lia) ltac:(intros; apply NN; lia)) as LE. unfold HuffGen2.cntB in CNT. rewrite CNT in LE. lia.
Qed.

Lemma trip_facts : forall BCx rex, LI BCx rex -> 1 <= rex ->
  let r := afind (Z.to_nat ML) BCx (ML - 1) in
  1 <= r <= ML - 1 /\ 1 <= arr_get BCx r /\ (forall j, r < j <= ML - 1 -> arr_get BCx j = 0)
  /\ rex <= arr_get BCx ML
  /\ (forall b, 0 <= b <= 15 -> arr_get (atrip ML BCx) b =
        arr_get BCx b - (if b =? r then 1 else 0) + (if b =? r + 1 then 2 else 0) - (if b =? ML then 1 else 0))
  /\ LI (atrip ML BCx) (rex - 1).
Proof.
  intros BCx rex L Hrex. pose proof L as [LEN NN OUT CNT K REX LOW]. pose proof MLR as MR. pose proof US as [USm USu].
  pose proof (LI_exists_low BCx rex L Hrex) as (b0 & Hb0 & Nb0).
  pose proof (find_spec2 s t FC0 FC HP DP DL (Z.to_nat ML) BCx (ML - 1) ltac:(exists b0; split; [lia| exact Nb0])) as FS.
  cbv zeta in FS. rewrite afind_flat in FS.
  set (r := afind (Z.to_nat ML) BCx (ML - 1)) in *. destruct FS as (Hr & Br & Zr).
  assert (Hr1 : 1 <= r <= ML - 1).
  { split; [|lia]. destruct (Z_le_gt_dec 1 r); [assumption|]. exfalso. apply Br. apply OUT; lia. }
  pose proof (NN r ltac:(lia)) as NNr.
  assert (LEu : forall b, 1 <= b <= ML -> arr_get BCx b <= uu).
  { intros b Hb. unfold HuffGen2.cntB in CNT. rewrite <- CNT. apply isum_le1; [lia| lia| intros; apply NN; lia]. }
  assert (BML : rex <= arr_get BCx ML).
  { unfold HuffGen2.KB in K. unfold SlowB in LOW. replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia.
    replace (ML - 1 + 1) with ML in K by lia. rewrite Z.sub_diag, Z.pow_0_r in K. lia. }
  assert (ADJ0 : forall b, arr_get (bl_adj ML BCx r) b =
            if b =? ML then (if r + 1 =? ML then arr_get BCx (r + 1) + 2 else arr_get BCx ML) - 1
            else if b =? r + 1 then arr_get BCx (r + 1) + 2
            else if b =? r then arr_get BCx r - 1 else arr_get BCx b).
  { intros b. unfold bl_adj. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LEN.
    pose proof (LEu r ltac:(lia)). pose proof (LEu (r + 1) ltac:(lia)). pose proof (LEu ML ltac:(lia)). pose proof (NN (r + 1) ltac:(lia)). pose proof (NN ML ltac:(lia)).
    replace ((0 <=? ML) && (ML <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    replace ((0 <=? r + 1) && (r + 1 <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    replace ((0 <=? r) && (r <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    rewrite !Bool.andb_true_r.
    replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (r =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (Z.eqb_sym ML b), (Z.eqb_sym (r + 1) b), (Z.eqb_sym r b).
    destruct (Z.eqb_spec b ML); destruct (Z.eqb_spec (r + 1) ML); destruct (Z.eqb_spec b (r + 1)); destruct (Z.eqb_spec b r);
      subst; try lia; rewrite ?(wrap16_id (arr_get BCx (r + 1) + 2)) by lia; rewrite ?(wrap16_id (arr_get BCx r - 1)) by lia; rewrite ?wrap16_id by lia; try reflexivity; lia. }
  assert (ADJ : forall b, 0 <= b <= 15 -> arr_get (atrip ML BCx) b =
        arr_get BCx b - (if b =? r then 1 else 0) + (if b =? r + 1 then 2 else 0) - (if b =? ML then 1 else 0)).
  { intros b Hb. unfold atrip. fold r. rewrite ADJ0.
    destruct (Z.eq_dec (r + 1) ML) as [E|NE].
    - rewrite <- !E in *. rewrite Z.eqb_refl.
      destruct (Z.eqb_spec b (r + 1)); destruct (Z.eqb_spec b r); subst; lia.
    - replace (r + 1 =? ML) with false by (symmetry; apply Z.eqb_neq; exact NE).
      destruct (Z.eqb_spec b ML); destruct (Z.eqb_spec b (r + 1)); destruct (Z.eqb_spec b r); subst; lia. }
  split; [exact Hr1|]. split; [lia|]. split; [intros j Hj; apply Zr; lia|]. split; [exact BML|]. split; [exact ADJ|].
  pose proof (LT2 DL BCx rex L Hrex) as LT. cbv zeta in LT. rewrite afind_flat in LT. exact LT.
Qed.

Lemma arepair_ext : forall n B1 B2 rex, LI B1 rex -> Z.of_nat n <= rex -> arr_len B2 = 16 ->
  (forall i, 0 <= i <= 15 -> arr_get B1 i = arr_get B2 i) ->
  forall i, 0 <= i <= 15 -> arr_get (arepair n ML B1) i = arr_get (arepair n ML B2) i.
Proof.
  induction n as [|n IH]; intros B1 B2 rex L1 Hn L2 E i Hi; cbn [arepair]; [apply E; exact Hi|].
  rewrite Nat2Z.inj_succ in Hn. pose proof MLR as MR.
  pose proof (trip_facts B1 rex L1 ltac:(lia)) as TF. cbv zeta in TF. destruct TF as (Hr & _ & _ & _ & _ & LI1).
  destruct L1 as [LB1 _ _ _ _ _ _].
  assert (ER : afind (Z.to_nat ML) B2 (ML - 1) = afind (Z.to_nat ML) B1 (ML - 1)) by (apply afind_ext; intros; symmetry; apply E; lia).
  apply (IH _ _ (rex - 1) LI1 ltac:(lia)).
  - unfold atrip, bl_adj. rewrite !arr_len_set. exact L2.
  - intros k Hk. unfold atrip. rewrite ER. set (r := afind (Z.to_nat ML) B1 (ML - 1)) in *.
    unfold bl_adj. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LB1, L2. rewrite !E by lia. reflexivity.
  - exact Hi.
Qed.


Lemma isum_zero_range : forall f m n, 0 <= m <= n -> (forall i, m < i <= n -> f i = 0) -> isum f n = isum f m.
Proof.
  intros f m n Hmn Z0. replace n with (m + Z.of_nat (Z.to_nat (n - m))) in * by lia.
  induction (Z.to_nat (n - m)) as [|k IH]; [f_equal; lia|].
  rewrite Nat2Z.inj_succ in *. replace (m + Z.succ (Z.of_nat k)) with (m + Z.of_nat k + 1) in * by lia.
  rewrite isum_snoc by lia. rewrite IH by (lia || (intros; apply Z0; lia)). rewrite Z0 by lia. lia.
Qed.

Lemma isum_mono_le : forall f m n, 0 <= m <= n -> (forall i, m < i <= n -> 0 <= f i) -> isum f m <= isum f n.
Proof.
  intros f m n Hmn NN. replace n with (m + Z.of_nat (Z.to_nat (n - m))) in * by lia.
  induction (Z.to_nat (n - m)) as [|k IH]; [apply Z.eq_le_incl; f_equal; lia|].
  rewrite Nat2Z.inj_succ in *. replace (m + Z.succ (Z.of_nat k)) with (m + Z.of_nat k + 1) in * by lia.
  rewrite isum_snoc by lia. specialize (IH ltac:(lia) ltac:(intros; apply NN; lia)). pose proof (NN (m + Z.of_nat k + 1) ltac:(lia)). lia.
Qed.

Lemma isum_ind1 : forall (c : Z) v n, 1 <= v <= n -> isum (fun b => if b =? v then c else 0) n = c.
Proof.
  intros c v n Hv. replace n with (Z.of_nat (Z.to_nat n)) by lia.
  assert (G : forall k, isum (fun b => if b =? v then c else 0) (Z.of_nat k) = if v <=? Z.of_nat k then c else 0).
  { induction k as [|k IH].
    - rewrite isum_0. destruct (Z.leb_spec v (Z.of_nat 0)); lia.
    - rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia. rewrite isum_snoc by lia. rewrite IH.
      destruct (Z.eqb_spec (Z.of_nat k + 1) v), (Z.leb_spec v (Z.of_nat k)), (Z.leb_spec v (Z.of_nat k + 1)); lia. }
  rewrite G. destruct (Z.leb_spec v (Z.of_nat (Z.to_nat n))); lia.
Qed.

Section Repair.
  Variable BCc : arr.
  Hypothesis L0 : LI BCc N.
  Hypothesis N1 : 1 <= N.
  Hypothesis KC : forall d, 1 <= d <= ML - 1 -> isum (fun b => arr_get BCc b * 2 ^ (ML - b)) d <= 2 ^ ML - 2 ^ (ML - d).

  Definition RB (n : nat) : arr := arepair n ML BCc.
  Definition rlev (n : nat) : Z := afind (Z.to_nat ML) (RB n) (ML - 1).

  Lemma RB_S : forall n, RB (S n) = atrip ML (RB n).
  Proof.
    intros n. unfold RB. generalize BCc. induction n as [|n IH]; intros B; [reflexivity|].
    cbn [arepair]. rewrite <- IH. reflexivity.
  Qed.

  Lemma LI_RB : forall n, (Z.of_nat n <= N) -> LI (RB n) (N - Z.of_nat n).
  Proof.
    induction n as [|n IH]; intros Hn; [rewrite Z.sub_0_r; exact L0|].
    rewrite RB_S. rewrite Nat2Z.inj_succ. replace (N - Z.succ (Z.of_nat n)) with (N - Z.of_nat n - 1) by lia.
    pose proof (trip_facts (RB n) (N - Z.of_nat n) (IH ltac:(lia)) ltac:(lia)) as TF. cbv zeta in TF. apply TF.
  Qed.

  Definition MIDf (m : Z) : Z := isum (fun b => if m <? b then arr_get BCc b * (2 ^ (ML - b) - 1) else 0) (ML - 1).

  Lemma MIDf_nonneg : forall m, 0 <= MIDf m.
  Proof.
    intros m. unfold MIDf. pose proof MLR. destruct L0 as [LEN NN _ _ _ _ _].
    apply isum_nonneg. intros i Hi. destruct (m <? i); [|lia].
    pose proof (NN i ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (ML - i) ltac:(lia) ltac:(lia)). nia.
  Qed.

  Lemma trip_identity : forall n d, Z.of_nat n < N ->
    let r := rlev n in
    (forall b, 1 <= b < r -> arr_get (RB n) b = arr_get BCc b) -> arr_get (RB n) r = arr_get BCc r - d ->
    Z.of_nat n = d * (2 ^ (ML - r) - 1) + MIDf r.
  Proof.
    intros n d Hn. cbv zeta. intros LOWb ATb. pose proof MLR as MR.
    pose proof (LI_RB n ltac:(lia)) as L. pose proof (trip_facts (RB n) (N - Z.of_nat n) L ltac:(lia)) as TF. cbv zeta in TF.
    fold (rlev n) in TF. set (r := rlev n) in *. destruct TF as (Hr & Br & Zr & BML & _ & _).
    destruct L as [LEN NN OUT CNT K REX LOW]. destruct L0 as [LEN0 NN0 OUT0 CNT0 K0' REX0 LOW0].
    set (B := arr_get (RB n)) in *. set (C := arr_get BCc) in *.
    unfold HuffGen2.KB in K, K0'. unfold HuffGen2.cntB in CNT, CNT0.
    assert (E1 : Z.of_nat n = isum (fun b => (C b - B b) * 2 ^ (ML - b)) ML).
    { rewrite (isum_ext _ (fun b => C b * 2 ^ (ML - b) + (-1) * (B b * 2 ^ (ML - b)))) by (intros; lia).
      rewrite isum_add, isum_mul. lia. }
    assert (E2 : 0 = isum (fun b => C b - B b) ML).
    { rewrite (isum_ext _ (fun b => C b + (-1) * B b)) by (intros; lia). rewrite isum_add, isum_mul. lia. }
    assert (E3 : Z.of_nat n = isum (fun b => (C b - B b) * (2 ^ (ML - b) - 1)) (ML - 1)).
    { replace ML with (ML - 1 + 1) in E1, E2 by lia. rewrite isum_snoc in E1, E2 by lia. replace (ML - 1 + 1) with ML in E1, E2 by lia.
      rewrite Z.sub_diag, Z.pow_0_r in E1.
      rewrite (isum_ext _ (fun b => (C b - B b) * 2 ^ (ML - b) + (-1) * (C b - B b))) by (intros; lia).
      rewrite isum_add, isum_mul. lia. }
    rewrite E3. unfold MIDf. fold C.
    rewrite (isum_ext (fun b => (C b - B b) * (2 ^ (ML - b) - 1)) (fun b => (if b =? r then d * (2 ^ (ML - r) - 1) else 0) + (if r <? b then C b * (2 ^ (ML - b) - 1) else 0))).
    2:{ intros b Hb0. destruct (Z.eqb_spec b r) as [->|NE].
        - replace (r <? r) with false by (symmetry; apply Z.ltb_irrefl). rewrite ATb. lia.
        - destruct (Z.ltb_spec r b).
          + rewrite (Zr b) by lia. lia.
          + rewrite (LOWb b) by lia. lia. }
    rewrite isum_add, isum_ind1 by lia. reflexivity.
  Qed.

  Record STR (n : nat) (m sN : Z) : Prop := STRc {
    str_m : 1 <= m <= ML - 1;
    str_s : 1 <= sN;
    str_low : forall b, 1 <= b < m -> arr_get (RB n) b = arr_get BCc b;
    str_at : arr_get (RB n) m = arr_get BCc m - sN;
    str_gap : 2 ^ (ML - m) <= uu - 2;
    str_budget : MIDf m + (sN - 1) * (2 ^ (ML - m) - 1) + 1 <= Z.of_nat n }.

  Lemma gap_at : forall n, Z.of_nat n < N ->
    (forall b, 1 <= b <= rlev n -> arr_get (RB n) b = arr_get BCc b) ->
    2 ^ (ML - rlev n) <= uu - 2.
  Proof.
    intros n Hn LOWEQ. pose proof MLR as MR.
    pose proof (LI_RB n ltac:(lia)) as L. pose proof (trip_facts (RB n) (N - Z.of_nat n) L ltac:(lia)) as TF. cbv zeta in TF.
    fold (rlev n) in TF. set (r := rlev n) in *. destruct TF as (Hr & Br & Zr & BML & _ & _).
    destruct L as [LEN NN OUT CNT K REX LOW]. set (B := arr_get (RB n)) in *.
    unfold HuffGen2.KB in K.
    replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia. replace (ML - 1 + 1) with ML in K by lia.
    rewrite Z.sub_diag, Z.pow_0_r in K.
    rewrite (isum_zero_range _ r (ML - 1)) in K by (lia || (intros; rewrite Zr by lia; lia)).
    rewrite (isum_ext _ (fun b => arr_get BCc b * 2 ^ (ML - b)) r) in K by (intros; rewrite LOWEQ by lia; reflexivity).
    pose proof (KC r ltac:(lia)) as KCr.
    unfold HuffGen2.cntB in CNT.
    replace ML with (ML - 1 + 1) in CNT at 1 by lia. rewrite isum_snoc in CNT by lia. replace (ML - 1 + 1) with ML in CNT by lia.
    pose proof (isum_mono_le B r (ML - 1) ltac:(lia) ltac:(intros; apply NN; lia)) as M1.
    pose proof (isum_le1 B r r ltac:(lia) ltac:(lia) ltac:(intros; apply NN; lia)) as M2.
    lia.
  Qed.

  Lemma N_small : N <= uu - 3.
  Proof.
    pose proof MLR as MR.
    pose proof (trip_facts BCc N L0 N1) as TF. cbv zeta in TF.
    set (r := afind (Z.to_nat ML) BCc (ML - 1)) in *. destruct TF as (Hr & Br & Zr & BML & _ & _).
    destruct L0 as [LEN NN OUT CNT K REX LOW]. set (B := arr_get BCc) in *.
    unfold HuffGen2.KB in K.
    replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia. replace (ML - 1 + 1) with ML in K by lia.
    rewrite Z.sub_diag, Z.pow_0_r in K.
    rewrite (isum_zero_range _ r (ML - 1)) in K by (lia || (intros; rewrite Zr by lia; lia)).
    pose proof (KC r ltac:(lia)) as KCr.
    unfold HuffGen2.cntB in CNT.
    replace ML with (ML - 1 + 1) in CNT at 1 by lia. rewrite isum_snoc in CNT by lia. replace (ML - 1 + 1) with ML in CNT by lia.
    pose proof (isum_mono_le B r (ML - 1) ltac:(lia) ltac:(intros; apply NN; lia)) as M1.
    pose proof (isum_le1 B r r ltac:(lia) ltac:(lia) ltac:(intros; apply NN; lia)) as M2.
    assert (2 ^ 1 <= 2 ^ (ML - r)) by (apply Z.pow_le_mono_r; lia).
    lia.
  Qed.

  Lemma STR_all : forall n, (1 <= n)%nat -> Z.of_nat n <= N -> exists m sN, STR n m sN.
  Proof.
    induction n as [|n IH]; intros Hn1 HnN; [lia|].
    pose proof MLR as MR.
    pose proof (LI_RB n ltac:(lia)) as L. pose proof (trip_facts (RB n) (N - Z.of_nat n) L ltac:(lia)) as TF. cbv zeta in TF.
    fold (rlev n) in TF. set (r := rlev n) in *. destruct TF as (Hr & Br & Zr & BML & ADJ & _).
    assert (RBS : forall b, 0 <= b <= 15 -> arr_get (RB (S n)) b = arr_get (RB n) b - (if b =? r then 1 else 0) + (if b =? r + 1 then 2 else 0) - (if b =? ML then 1 else 0)).
    { intros b Hb. rewrite RB_S. apply ADJ. exact Hb. }
    pose proof (MIDf_nonneg r) as MG.
    destruct n as [|n'].
    -
      pose proof (trip_identity 0 0 ltac:(cbn; lia) ltac:(intros; reflexivity) ltac:(unfold RB; cbn [arepair]; lia)) as TI. cbv zeta in TI. fold r in TI.
      exists r, 1. split; [lia| lia| | | |].
      + intros b Hb. rewrite RBS by lia. destruct (Z.eqb_spec b r); [lia|]. destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b ML); [lia|]. unfold RB. cbn. lia.
      + rewrite RBS by lia. rewrite Z.eqb_refl. destruct (Z.eqb_spec r (r + 1)); [lia|]. destruct (Z.eqb_spec r ML); [lia|]. unfold RB. cbn. lia.
      + apply (gap_at 0 ltac:(cbn; lia)). intros; reflexivity.
      + cbn in TI. lia.
    - destruct (IH ltac:(lia) ltac:(lia)) as (m & sN & [Sm Ss Slow Sat Sgap Sbud]).
      destruct (Z_lt_le_dec r m) as [LT|GE].
      +
        pose proof (trip_identity (S n') 0 ltac:(lia) ltac:(intros b Hb; apply Slow; fold r in Hb; lia) ltac:(fold r; rewrite Slow by lia; lia)) as TI.
        cbv zeta in TI. fold r in TI.
        exists r, 1. split; [lia| lia| | | |].
        * intros b Hb. rewrite RBS by lia. destruct (Z.eqb_spec b r); [lia|]. destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b ML); [lia|].
          rewrite Slow by lia. lia.
        * rewrite RBS by lia. rewrite Z.eqb_refl. destruct (Z.eqb_spec r (r + 1)); [lia|]. destruct (Z.eqb_spec r ML); [lia|]. rewrite Slow by lia. lia.
        * apply gap_at; [lia|]. intros b Hb. fold r in Hb. destruct (Z.eq_dec b m); [subst|]; [|apply Slow; lia]. lia.
        * lia.
      + destruct (Z.eq_dec r m) as [EQ|NE].
        *
          pose proof (trip_identity (S n') sN ltac:(lia) ltac:(intros b Hb; apply Slow; fold r in Hb; lia) ltac:(fold r; rewrite EQ; exact Sat)) as TI.
          cbv zeta in TI. fold r in TI. rewrite EQ in TI.
          exists m, (sN + 1). split; [lia| lia| | | exact Sgap|].
          -- intros b Hb. rewrite RBS by lia. destruct (Z.eqb_spec b r); [lia|]. destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b ML); [lia|].
             rewrite Slow by lia. lia.
          -- rewrite RBS by lia. destruct (Z.eqb_spec m r); [|lia]. destruct (Z.eqb_spec m (r + 1)); [lia|]. destruct (Z.eqb_spec m ML); [lia|]. rewrite Sat. lia.
          -- replace (sN + 1 - 1) with (sN - 1 + 1) by lia. rewrite Z.mul_add_distr_r. lia.
        *
          exists m, sN. split; [lia| lia| | | exact Sgap| lia].
          -- intros b Hb. rewrite RBS by lia. destruct (Z.eqb_spec b r); [lia|]. destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b ML); [lia|].
             rewrite Slow by lia. lia.
          -- rewrite RBS by lia. destruct (Z.eqb_spec m r); [lia|]. destruct (Z.eqb_spec m (r + 1)); [lia|]. destruct (Z.eqb_spec m ML); [lia|]. rewrite Sat. lia.
  Qed.

  Definition BCF : arr := RB (Z.to_nat N).

  Theorem repair_structure :
    LI BCF 0 /\ BCF = arepair (Z.to_nat N) ML BCc /\
    exists bstar sN, 1 <= bstar <= ML - 1 /\ 1 <= sN
      /\ (forall b, 1 <= b < bstar -> arr_get BCF b = arr_get BCc b)
      /\ arr_get BCF bstar = arr_get BCc bstar - sN
      /\ 2 ^ (ML - bstar) <= uu - 2
      /\ MIDf bstar + (sN - 1) * (2 ^ (ML - bstar) - 1) + 1 <= N
      /\ N <= uu - 3.
  Proof.
    split; [pose proof (LI_RB (Z.to_nat N) ltac:(lia)) as L; replace (N - Z.of_nat (Z.to_nat N)) with 0 in L by lia; exact L|].
    split; [reflexivity|].
    destruct (STR_all (Z.to_nat N) ltac:(lia) ltac:(lia)) as (m & sN & [Sm Ss Slow Sat Sgap Sbud]).
    pose proof N_small.
    exists m, sN. repeat split; auto; lia.
  Qed.
End Repair.


Definition LQ : list Z := filter leafp (rng 573).
Definition RLl : list Z := map (arr_get HP7) LQ.

Lemma LQ_in : forall q, In q LQ -> hm <= q <= 572 /\ leafp q = true.
Proof. intros q Hq. unfold LQ in Hq. apply filter_In in Hq. destruct Hq as [Hq Lq]. unfold HuffGen.rng in Hq. apply in_ziota in Hq. split; [lia| exact Lq]. Qed.

Lemma LQ_sincr : sincr LQ.
Proof. unfold LQ, HuffGen.rng. apply sincr_filter. apply sincr_ziota. Qed.

Lemma RL_perm : Permutation RLl UPl.
Proof. exact LPOS. Qed.

Lemma RL_NoDup : NoDup RLl.
Proof. apply (Permutation_NoDup' (Permutation_sym RL_perm)). pose proof (pads_facts t FC0) as (ND & _). exact ND. Qed.

Lemma RL_length : length RLl = Z.to_nat uu.
Proof. pose proof (Permutation_length RL_perm) as L. rewrite L. unfold u, zlen. lia. Qed.

Lemma LQ_length : length LQ = Z.to_nat uu.
Proof. rewrite <- RL_length. unfold RLl. rewrite length_map. reflexivity. Qed.

Lemma F_rank_noninc : noninc (map FPf RLl).
Proof.
  unfold RLl. rewrite map_map. apply noninc_map_sincr; [apply LQ_sincr|].
  intros x y Hx Hy Hxy. destruct (LQ_in x Hx) as [Rx Lx]. destruct (LQ_in y Hy) as [Ry Ly].
  pose proof INV as [? ? ? ? ? ? ? ? i_fc]. pose proof MCF as [MCr LF].
  pose proof (IDR x ltac:(lia)) as [Ix _]. pose proof (IDR y ltac:(lia)) as [Iy _].
  apply (proj1 (LF x ltac:(lia))) in Lx. apply (proj1 (LF y ltac:(lia))) in Ly.
  rewrite <- !i_fc by lia. apply WO; lia.
Qed.

Lemma zcnt_rank : forall (g : Z -> Z) v,
  zcnt v (map g LQ) = SUM (fun q => if leafp q then (if g q =? v then 1 else 0) else 0) 573.
Proof.
  intros g v. unfold zcnt, LQ, HuffGen.SUM. rewrite map_map. symmetry. apply zsum_filter_map.
Qed.

Lemma nd_leaf_range : forall j, In j UPl -> 1 <= nd j <= uu - 1.
Proof.
  intros j Hj. destruct (T_leaves t FC0 FC DL HP DP sub INV) as [PT WT].
  assert (Hin : In j (map ea (hprof 0 (T HP sub)))) by (apply (Permutation_in _ (Permutation_sym PT)); exact Hj).
  apply in_map_iff in Hin. destruct Hin as (e & <- & He).
  destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (_ & E & G1). rewrite E.
  pose proof (hprof_dep 0 _ e He). pose proof (hheight_leaves (T HP sub)).
  pose proof (Permutation_length PT) as PL. rewrite length_map in PL. unfold u, zlen. rewrite <- PL. lia.
Qed.

Section Final.
  Variables (DLc BCc DLf BCf : arr) (OLc : Z).
  Hypothesis SDL : forall j, In j UPl -> arr_get DLc j = Z.min (nd j) ML.
  Hypothesis SBC : forall b, 0 <= b <= 15 -> arr_get BCc b = zsum (map (fun j => if Z.min (nd j) ML =? b then 1 else 0) UPl).
  Hypothesis LIf : LI BCf 0.
  Hypothesis RNG : forall q, hm <= q <= 572 -> leafp q = true -> 1 <= arr_get DLf (arr_get HP7 q) <= ML.
  Hypothesis MONO : forall q1 q2, hm <= q1 <= q2 -> q2 <= 572 -> leafp q1 = true -> leafp q2 = true ->
                      arr_get DLf (arr_get HP7 q1) <= arr_get DLf (arr_get HP7 q2).
  Hypothesis SUMg : forall g, SUM (fun q => if leafp q then g (arr_get DLf (arr_get HP7 q)) else 0) 573 = isum (fun b => arr_get BCf b * g b) ML.
  Variables bstar sN : Z.
  Hypothesis Hb : 1 <= bstar <= ML - 1.
  Hypothesis Hs : 1 <= sN.
  Hypothesis LOWEQ : forall b, 1 <= b < bstar -> arr_get BCf b = arr_get BCc b.
  Hypothesis ATEQ : arr_get BCf bstar = arr_get BCc bstar - sN.

  Definition z : list Z := map (fun q => arr_get DLf (arr_get HP7 q)) LQ.
  Definition d0 : list Z := map (fun q => nd (arr_get HP7 q)) LQ.
  Definition ct : list Z := lens_asc (fun b => zcnt b d0) 573.
  Definition cs : list Z := map (fun x => Z.min x ML) ct.
  Definition L' (j : Z) : Z := nth (idx j RLl) ct 0.

  Lemma isum_indicator : forall (B : Z -> Z) v n, 0 <= n -> isum (fun b => B b * (if b =? v then 1 else 0)) n = if (1 <=? v) && (v <=? n) then B v else 0.
  Proof.
    intros B v n Hn. replace n with (Z.of_nat (Z.to_nat n)) by lia. generalize (Z.to_nat n) as k. clear n Hn. intros k.
    induction k as [|k IH].
    - rewrite isum_0. destruct (Z.leb_spec 1 v), (Z.leb_spec v (Z.of_nat 0)); cbn [andb]; lia.
    - rewrite Nat2Z.inj_succ. replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) by lia. rewrite isum_snoc by lia. rewrite IH.
      destruct (Z.eqb_spec (Z.of_nat k + 1) v), (Z.leb_spec 1 v), (Z.leb_spec v (Z.of_nat k)), (Z.leb_spec v (Z.of_nat k + 1)); cbn [andb]; try subst v; try lia.
  Qed.

  Lemma z_is : z = lens_asc (arr_get BCf) ML.
  Proof.
    pose proof MLR as MR. destruct LIf as [LBC NN OUT CNT K _ _].
    apply nondec_is_lens_asc.
    - unfold z. apply nondec_map_sincr; [apply LQ_sincr|]. intros x y Hx Hy Hxy.
      destruct (LQ_in x Hx) as [Rx Lx]. destruct (LQ_in y Hy) as [Ry Ly]. apply MONO; auto; lia.
    - intros v Hv. unfold z in Hv. apply in_map_iff in Hv. destruct Hv as (q & <- & Hq). destruct (LQ_in q Hq) as [Rq Lq]. apply RNG; auto.
    - intros b Hb0. apply NN. lia.
    - intros v Hv. unfold z. rewrite zcnt_rank. rewrite (SUMg (fun len => if len =? v then 1 else 0)). rewrite isum_indicator by lia.
      replace ((1 <=? v) && (v <=? ML)) with true by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia). reflexivity.
  Qed.

  Lemma d0_range : forall x, In x d0 -> 1 <= x <= uu - 1.
  Proof.
    intros x Hx. unfold d0 in Hx. apply in_map_iff in Hx. destruct Hx as (q & <- & Hq). destruct (LQ_in q Hq) as [Rq Lq].
    apply nd_leaf_range. pose proof MCF as [_ LF]. apply (proj2 (IDR q ltac:(lia))). apply (proj1 (LF q ltac:(lia))). exact Lq.
  Qed.

  Lemma ct_perm : Permutation ct d0.
  Proof.
    pose proof US as [_ USu].
    apply zcnt_perm. intros v. unfold ct. rewrite lens_asc_cnt by (intros; apply zcnt_nonneg).
    destruct (Z.leb_spec 1 v); destruct (Z.leb_spec v 573); cbn [andb]; try reflexivity;
      (destruct (Z_lt_le_dec 0 (zcnt v d0)) as [P|P]; [apply zcnt_In in P; pose proof (d0_range v P); lia| pose proof (zcnt_nonneg v d0); lia]).
  Qed.

  Lemma ct_length : length ct = Z.to_nat uu.
  Proof. rewrite (Permutation_length ct_perm). unfold d0. rewrite length_map. apply LQ_length. Qed.

  Lemma ct_nondec : nondec ct.
  Proof. unfold ct. apply lens_asc_nondec. Qed.

  Lemma cs_is : cs = lens_asc (arr_get BCc) ML.
  Proof.
    pose proof MLR as MR.
    apply nondec_is_lens_asc.
    - unfold cs. apply nondec_map_min. apply ct_nondec.
    - intros x Hx. unfold cs in Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
      pose proof (d0_range y (Permutation_in _ ct_perm Hy)). lia.
    - intros b Hb0. rewrite SBC by lia. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). destruct (_ =? b); lia.
    - intros v Hv. rewrite SBC by lia. unfold cs. rewrite (zcnt_map_perm _ _ _ v ct_perm). unfold d0. rewrite map_map.
      change (zcnt v (map (fun q => Z.min (nd (arr_get HP7 q)) ML) LQ)) with (zcnt v (map (fun j => Z.min (nd j) ML) RLl ++ [])) || idtac.
      transitivity (zcnt v (map (fun j => Z.min (nd j) ML) RLl)); [unfold RLl; rewrite map_map; reflexivity|].
      rewrite (zcnt_map_perm _ _ _ v RL_perm). unfold zcnt. rewrite map_map. reflexivity.
  Qed.

  Definition P0len : Z := zsum (map (arr_get BCc) (ziota 1 (Z.to_nat (bstar - 1)))) + (arr_get BCc bstar - sN).

  Lemma BCc_nn : forall b, 1 <= b <= ML -> 0 <= arr_get BCc b.
  Proof. intros b Hb0. pose proof MLR. rewrite SBC by lia. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). destruct (_ =? b); lia. Qed.

  Lemma prefix_structure :
    exists P Cf Cc, z = P ++ Cf /\ cs = P ++ Cc /\ Z.of_nat (length P) = P0len
      /\ (forall x, In x P -> 1 <= x <= bstar) /\ (forall x, In x Cf -> bstar + 1 <= x) /\ (forall x, In x Cc -> bstar <= x).
  Proof.
    pose proof MLR as MR. destruct LIf as [LBC NN OUT CNT K _ _].
    rewrite z_is, cs_is.
    rewrite (lens_asc_split (arr_get BCf) ML bstar) by lia. rewrite (lens_asc_split (arr_get BCc) ML bstar) by lia.
    set (A := flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota 1 (Z.to_nat (bstar - 1)))).
    assert (EA : flat_map (fun b => repeat b (Z.to_nat (arr_get BCf b))) (ziota 1 (Z.to_nat (bstar - 1))) = A).
    { subst A.
      assert (G : forall l, (forall b, In b l -> 1 <= b < bstar) ->
                 flat_map (fun b => repeat b (Z.to_nat (arr_get BCf b))) l = flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) l).
      { induction l as [|b1 l IH]; intros Hl; cbn [flat_map]; [reflexivity|].
        rewrite LOWEQ. 2:{ apply Hl. left. reflexivity. } rewrite IH; [reflexivity|]. intros; apply Hl; right; assumption. }
      apply G. intros b' Hb0. apply in_ziota in Hb0. lia. }
    rewrite EA, ATEQ.
    pose proof (BCc_nn bstar ltac:(lia)) as NNb. pose proof (NN bstar ltac:(lia)) as NNf. rewrite ATEQ in NNf.
    replace (Z.to_nat (arr_get BCc bstar)) with (Z.to_nat (arr_get BCc bstar - sN) + Z.to_nat sN)%nat by lia.
    rewrite repeat_app.
    exists (A ++ repeat bstar (Z.to_nat (arr_get BCc bstar - sN))).
    eexists. eexists. split; [rewrite <- app_assoc; reflexivity|]. split; [rewrite <- !app_assoc; reflexivity|].
    split.
    { rewrite length_app, repeat_length, Nat2Z.inj_add. unfold P0len. subst A. rewrite length_flat_map_repeat by (intros; apply BCc_nn; lia). lia. }
    split.
    { intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
      - subst A. apply in_flat_map in Hx. destruct Hx as (b & Hb0 & Hx). apply in_ziota in Hb0. apply repeat_spec in Hx. lia.
      - apply repeat_spec in Hx. lia. }
    split.
    { intros x Hx. apply flat_map_repeat_In_ge in Hx. lia. }
    intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [apply repeat_spec in Hx; lia|]. apply flat_map_repeat_In_ge in Hx. lia.
  Qed.

  Lemma rank_structure : forall r, (r < Z.to_nat uu)%nat ->
    (nth r cs 0 < bstar -> nth r z 0 = nth r cs 0)
    /\ ((nth r z 0 = nth r cs 0 /\ nth r cs 0 <= bstar) \/ (bstar + 1 <= nth r z 0 /\ bstar <= nth r cs 0)).
  Proof.
    intros r Hr. destruct prefix_structure as (P & Cf & Cc & EZ & ECS & LP & InP & InCf & InCc).
    assert (Lz : length z = Z.to_nat uu) by (unfold z; rewrite length_map; apply LQ_length).
    assert (Lcs : length cs = Z.to_nat uu) by (unfold cs; rewrite length_map; apply ct_length).
    rewrite EZ, ECS in *. rewrite length_app in Lz, Lcs.
    destruct (Nat.lt_ge_cases r (length P)) as [LT|GE].
    - rewrite !nth_app_l by exact LT. split; [intros; reflexivity| left]. split; [reflexivity|]. apply (fun H => proj2 (InP _ H)). apply nth_In. exact LT.
    - rewrite !nth_app_r by exact GE.
      pose proof (InCf (nth (r - length P) Cf 0) ltac:(apply nth_In; lia)).
      pose proof (InCc (nth (r - length P) Cc 0) ltac:(apply nth_In; lia)).
      split; [intros; lia| right; lia].
  Qed.

  Lemma cs_nth : forall r, (r < Z.to_nat uu)%nat -> nth r cs 0 = Z.min (nth r ct 0) ML.
  Proof. intros r Hr. unfold cs. rewrite nth_map' by (rewrite ct_length; exact Hr). reflexivity. Qed.

  Lemma rank_of : forall j, In j UPl -> exists r q, (r < Z.to_nat uu)%nat /\ idx j RLl = r /\ nth r LQ 0 = q /\ In q LQ /\ arr_get HP7 q = j
     /\ nth r z 0 = arr_get DLf j /\ L' j = nth r ct 0.
  Proof.
    intros j Hj. assert (HjR : In j RLl) by (apply (Permutation_in _ (Permutation_sym RL_perm)); exact Hj).
    pose proof (idx_lt j RLl HjR) as IL. rewrite RL_length in IL.
    pose proof (nth_idx j RLl 0 HjR) as E. set (r := idx j RLl) in *.
    exists r, (nth r LQ 0).
    assert (EQ : arr_get HP7 (nth r LQ 0) = j).
    { unfold RLl in E. rewrite nth_map' in E by (rewrite LQ_length; exact IL). exact E. }
    split; [exact IL|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply nth_In; rewrite LQ_length; exact IL|].
    split; [exact EQ|]. split; [| reflexivity].
    unfold z. rewrite nth_map' by (rewrite LQ_length; exact IL). rewrite EQ. reflexivity.
  Qed.



  Lemma FP_ge1 : forall j, In j UPl -> 1 <= FPf j.
  Proof.
    intros j Hj. pose proof (pads_facts t FC0) as (_ & RNGU & _). pose proof (RNGU j Hj).
    destruct INV as [? ? ? ? ? HLEAF ? ? ? ? ? ? HSUB]. destruct (HLEAF j Hj) as (p & Hp & Ep).
    destruct (HSUB p Hp) as (W & M & FL & _). rewrite Ep in *. rewrite (FL ltac:(lia)) in M. cbn in M. exact M.
  Qed.

  Lemma leaf_fib : forall j, In j UPl -> fibZ (nd j + 1) * FPf j <= Ftot t FC0.
  Proof.
    intros j Hj.
    pose proof (T_build t FC0 FC DL HP DP sub INV) as TB. pose proof (T_leaves t FC0 FC DL HP DP sub INV) as [PT WT].
    pose proof (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
    assert (LF : leaf_forest (F0 t FC0)).
    { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j' & <- & _). exact I. }
    assert (F0w : forall x, In x (F0 t FC0) -> 1 <= hw x).
    { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j' & <- & Hj'). cbn. apply FP_ge1. exact Hj'. }
    assert (HWT : hw (T HP sub) = Ftot t FC0).
    { unfold Ftot. rewrite <- (hw_prof 0). rewrite <- (zsum_map_perm _ _ _ PT). rewrite map_map. apply zsum_map_ext. intros e He. apply WT. exact He. }
    assert (Hin : In (j, nd j) (map (fun e => (ea e, ed e)) (hprof 0 (T HP sub)))).
    { apply (Permutation_in _ (Permutation_sym PD)). apply in_map_iff. exists j. auto. }
    apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2.
    pose proof (hbuild_fib _ _ TB LF F0w e He) as FB. rewrite (WT e He), E1, E2, HWT in FB.
    pose proof (fibZ_nonneg (nd j)). lia.
  Qed.

  Lemma rank_fib : forall r, (r < Z.to_nat uu)%nat -> fibZ (nth r ct 0 + 1) * nth r (map FPf RLl) 0 <= Ftot t FC0.
  Proof.
    intros r Hr.
    assert (Ed0 : d0 = map nd RLl) by (unfold d0, RLl; rewrite map_map; reflexivity).
    assert (Ld0 : length d0 = Z.to_nat uu) by (rewrite Ed0, length_map; apply RL_length).
    set (v := nth r ct 0).
    assert (EX : exists i, (i <= r)%nat /\ v <= nth i d0 0).
    { destruct (existsb (fun i => v <=? nth i d0 0) (seq 0 (S r))) eqn:E.
      - apply existsb_exists in E. destruct E as (i & Hi & Ci). apply in_seq in Hi. apply Z.leb_le in Ci. exists i. split; [lia| exact Ci].
      - exfalso.
        assert (ALL : forall i, (i <= r)%nat -> nth i d0 0 < v).
        { intros i Hi. destruct (Z_lt_le_dec (nth i d0 0) v); [assumption|]. exfalso.
          assert (X : existsb (fun i => v <=? nth i d0 0) (seq 0 (S r)) = true); [|congruence].
          apply existsb_exists. exists i. split; [apply in_seq; lia| apply Z.leb_le; lia]. }
        pose proof (nondec_count_lt ct r ct_nondec ltac:(rewrite ct_length; exact Hr)) as C1. fold v in C1.
        assert (C2 : length (filter (fun x => x <? v) ct) = length (filter (fun x => x <? v) d0)).
        { apply perm_filter_length. apply ct_perm. }
        pose proof (filter_length_firstn (fun x => x <? v) (S r) d0) as C3.
        rewrite (filter_all_length (fun x => x <? v) (firstn (S r) d0)) in C3.
        + rewrite length_firstn in C3. lia.
        + intros x Hx. apply (In_nth _ _ 0) in Hx. destruct Hx as (i & Hi & <-). rewrite length_firstn in Hi.
          rewrite nth_firstn. apply Z.ltb_lt. replace (i <? S r)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply ALL. lia. }
    destruct EX as (i & Hi & Ci).
    set (j := nth i RLl 0).
    assert (Hj : In j UPl) by (apply (Permutation_in _ RL_perm); apply nth_In; rewrite RL_length; lia).
    assert (Dj : nth i d0 0 = nd j) by (rewrite Ed0; rewrite nth_map' by (rewrite RL_length; lia); reflexivity).
    pose proof (leaf_fib j Hj) as LFj.
    assert (Fi : nth r (map FPf RLl) 0 <= FPf j).
    { pose proof (noninc_nth (map FPf RLl) i r 0 F_rank_noninc Hi ltac:(rewrite length_map, RL_length; exact Hr)) as X.
      rewrite (nth_map' FPf RLl i 0) in X by (rewrite RL_length; lia). exact X. }
    pose proof (fibZ_mono (v + 1) (nd j + 1) ltac:(lia)). pose proof (fibZ_nonneg (v + 1)). pose proof (FP_ge1 j Hj).
    pose proof (noninc_nth (map FPf RLl) r r 0 F_rank_noninc ltac:(lia) ltac:(rewrite length_map, RL_length; exact Hr)).
    nia.
  Qed.

  Lemma rank_fib2 : forall r, (r < Z.to_nat uu)%nat -> fibZ (nth r ct 0 + 1) * nth r (map FPf RLl) 0 + fibZ (nth r ct 0) <= Ftot t FC0.
  Proof.
    intros r Hr.
    assert (Ed0 : d0 = map nd RLl) by (unfold d0, RLl; rewrite map_map; reflexivity).
    assert (Ld0 : length d0 = Z.to_nat uu) by (rewrite Ed0, length_map; apply RL_length).
    set (v := nth r ct 0).
    assert (EX : exists i, (i <= r)%nat /\ v <= nth i d0 0).
    { destruct (existsb (fun i => v <=? nth i d0 0) (seq 0 (S r))) eqn:E.
      - apply existsb_exists in E. destruct E as (i & Hi & Ci). apply in_seq in Hi. apply Z.leb_le in Ci. exists i. split; [lia| exact Ci].
      - exfalso.
        assert (ALL : forall i, (i <= r)%nat -> nth i d0 0 < v).
        { intros i Hi. destruct (Z_lt_le_dec (nth i d0 0) v); [assumption|]. exfalso.
          assert (X : existsb (fun i => v <=? nth i d0 0) (seq 0 (S r)) = true); [|congruence].
          apply existsb_exists. exists i. split; [apply in_seq; lia| apply Z.leb_le; lia]. }
        pose proof (nondec_count_lt ct r ct_nondec ltac:(rewrite ct_length; exact Hr)) as C1. fold v in C1.
        assert (C2 : length (filter (fun x => x <? v) ct) = length (filter (fun x => x <? v) d0)) by (apply perm_filter_length; apply ct_perm).
        pose proof (filter_length_firstn (fun x => x <? v) (S r) d0) as C3.
        rewrite (filter_all_length (fun x => x <? v) (firstn (S r) d0)) in C3.
        + rewrite length_firstn in C3. lia.
        + intros x Hx. apply (In_nth _ _ 0) in Hx. destruct Hx as (i & Hi & <-). rewrite length_firstn in Hi.
          rewrite nth_firstn. apply Z.ltb_lt. replace (i <? S r)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply ALL. lia. }
    destruct EX as (i & Hi & Ci).
    set (j := nth i RLl 0).
    assert (Hj : In j UPl) by (apply (Permutation_in _ RL_perm); apply nth_In; rewrite RL_length; lia).
    assert (Dj : nth i d0 0 = nd j) by (rewrite Ed0; rewrite nth_map' by (rewrite RL_length; lia); reflexivity).
    pose proof (T_build t FC0 FC DL HP DP sub INV) as TB. pose proof (T_leaves t FC0 FC DL HP DP sub INV) as [PT WT].
    pose proof (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
    assert (LF : leaf_forest (F0 t FC0)).
    { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j' & <- & _). exact I. }
    assert (F0w : forall x, In x (F0 t FC0) -> 1 <= hw x).
    { intros x Hx. unfold F0 in Hx. apply in_map_iff in Hx. destruct Hx as (j' & <- & Hj'). cbn. apply FP_ge1. exact Hj'. }
    assert (HWT : hw (T HP sub) = Ftot t FC0).
    { unfold Ftot. rewrite <- (hw_prof 0). rewrite <- (zsum_map_perm _ _ _ PT). rewrite map_map. apply zsum_map_ext. intros e He. apply WT. exact He. }
    assert (Hin : In (j, nd j) (map (fun e => (ea e, ed e)) (hprof 0 (T HP sub)))).
    { apply (Permutation_in _ (Permutation_sym PD)). apply in_map_iff. exists j. auto. }
    apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2.
    pose proof (hbuild_fib _ _ TB LF F0w e He) as FB. rewrite (WT e He), E1, E2, HWT in FB.
    assert (Fi : nth r (map FPf RLl) 0 <= FPf j).
    { pose proof (noninc_nth (map FPf RLl) i r 0 F_rank_noninc Hi ltac:(rewrite length_map, RL_length; exact Hr)) as X.
      rewrite (nth_map' FPf RLl i 0) in X by (rewrite RL_length; lia). exact X. }
    pose proof (fibZ_mono (v + 1) (nd j + 1) ltac:(lia)). pose proof (fibZ_mono v (nd j) ltac:(lia)). pose proof (fibZ_nonneg (v + 1)). pose proof (fibZ_nonneg v). pose proof (FP_ge1 j Hj).
    pose proof (noninc_nth (map FPf RLl) r r 0 F_rank_noninc ltac:(lia) ltac:(rewrite length_map, RL_length; exact Hr)).
    nia.
  Qed.

  Definition bc_of (l : list Z) : arr := arr_init 16 (fun b => zcnt b l).

  Hypothesis EBCF : BCf = arepair (Z.to_nat N) ML BCc.
  Hypothesis L0c : LI BCc N.

  Lemma z_canon : z = lens_asc (arr_get (arepair (Z.to_nat N) ML (bc_of cs))) ML.
  Proof.
    pose proof MLR as MR. rewrite z_is, EBCF.
    assert (CELLS : forall i, 0 <= i <= 15 -> arr_get BCc i = arr_get (bc_of cs) i).
    { intros i Hi. unfold bc_of. rewrite arr_get_init. rewrite SBC by lia. unfold cs.
      rewrite (zcnt_map_perm _ _ _ i ct_perm). unfold d0.
      transitivity (zcnt i (map (fun j => Z.min (nd j) ML) RLl)); [| unfold RLl; rewrite !map_map; reflexivity].
      rewrite (zcnt_map_perm _ _ _ i RL_perm). unfold zcnt. rewrite map_map. reflexivity. }
    pose proof L0c as [_ _ _ _ _ REX0 _].
    pose proof (arepair_ext (Z.to_nat N) BCc (bc_of cs) N L0c ltac:(lia) ltac:(unfold bc_of; apply arr_len_init) CELLS) as E.
    unfold lens_asc. apply flat_map_ext_in || idtac.
    assert (G : forall l, (forall b, In b l -> 1 <= b <= ML) ->
              flat_map (fun b => repeat b (Z.to_nat (arr_get (arepair (Z.to_nat N) ML BCc) b))) l
              = flat_map (fun b => repeat b (Z.to_nat (arr_get (arepair (Z.to_nat N) ML (bc_of cs)) b))) l).
    { induction l as [|b l IH]; intros Hl; cbn; [reflexivity|]. rewrite (E b) by (pose proof (Hl b (or_introl eq_refl)); lia). rewrite IH; [reflexivity|]. intros; apply Hl; right; assumption. }
    apply G. intros b Hb0. apply in_ziota in Hb0. lia.
  Qed.

  Lemma N_canon : N = zsum (map (fun x => 2 ^ (ML - x)) cs) - 2 ^ ML.
  Proof.
    pose proof (excess_identity t FC0 0 FC DL HP DP sub INV) as (EK & _ & _). fold N in EK. unfold K0, phi in EK.
    enough (zsum (map (fun x => 2 ^ (ML - x)) cs) = zsum (map (fun j => 2 ^ (ML - Z.min (nd j) ML)) UPl)) by lia.
    unfold cs. rewrite map_map. rewrite (zsum_map_perm _ _ _ ct_perm). unfold d0. rewrite map_map.
    transitivity (zsum (map (fun j => 2 ^ (ML - Z.min (nd j) ML)) RLl)); [unfold RLl; rewrite map_map; reflexivity|].
    apply zsum_map_perm. apply RL_perm.
  Qed.

  Lemma prefix_structure2 :
    exists P, cs = P ++ (repeat bstar (Z.to_nat sN) ++ flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota (bstar + 1) (Z.to_nat (ML - bstar))))
      /\ Z.of_nat (length P) = P0len
      /\ forall r, (r < length P)%nat -> nth r z 0 = nth r cs 0.
  Proof.
    pose proof MLR as MR. destruct LIf as [LBC NN OUT CNT K _ _].
    destruct prefix_structure as (P & Cf & Cc & EZ & ECS & LP & InP & InCf & InCc).
    exists P.
    assert (E2 : cs = (flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota 1 (Z.to_nat (bstar - 1))) ++ repeat bstar (Z.to_nat (arr_get BCc bstar - sN)))
                      ++ (repeat bstar (Z.to_nat sN) ++ flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota (bstar + 1) (Z.to_nat (ML - bstar))))).
    { rewrite cs_is. rewrite (lens_asc_split (arr_get BCc) ML bstar) by lia.
      pose proof (BCc_nn bstar ltac:(lia)) as NNb. pose proof (NN bstar ltac:(lia)) as NNf. rewrite ATEQ in NNf.
      replace (Z.to_nat (arr_get BCc bstar)) with (Z.to_nat (arr_get BCc bstar - sN) + Z.to_nat sN)%nat by lia.
      rewrite repeat_app. rewrite <- !app_assoc. reflexivity. }
    assert (LEN1 : Z.of_nat (length (flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota 1 (Z.to_nat (bstar - 1))) ++ repeat bstar (Z.to_nat (arr_get BCc bstar - sN)))) = P0len).
    { rewrite length_app, repeat_length, Nat2Z.inj_add. unfold P0len. rewrite length_flat_map_repeat by (intros; apply BCc_nn; lia).
      pose proof (BCc_nn bstar ltac:(lia)). pose proof (NN bstar ltac:(lia)) as NNf. rewrite ATEQ in NNf. lia. }
    assert (EP : P = flat_map (fun b => repeat b (Z.to_nat (arr_get BCc b))) (ziota 1 (Z.to_nat (bstar - 1))) ++ repeat bstar (Z.to_nat (arr_get BCc bstar - sN))).
    { rewrite ECS in E2. apply (f_equal (firstn (length P))) in E2. rewrite firstn_app, Nat.sub_diag, firstn_O, firstn_all, app_nil_r in E2.
      rewrite E2. replace (length P) with (length (flat_map (fun b : Z => repeat b (Z.to_nat (arr_get BCc b))) (ziota 1 (Z.to_nat (bstar - 1))) ++ repeat bstar (Z.to_nat (arr_get BCc bstar - sN)))) by lia.
      rewrite firstn_app, Nat.sub_diag, firstn_O, firstn_all, app_nil_r. reflexivity. }
    split; [rewrite E2, EP; reflexivity|]. split; [exact LP|].
    intros r Hr. rewrite EZ, ECS. rewrite !nth_app_l by exact Hr. reflexivity.
  Qed.

  Theorem pen_rank_bound :
    ML = 15 -> 2 ^ (ML - bstar) <= uu - 2 -> N <= uu - 3 ->
    isum (fun b => if bstar <? b then arr_get BCc b * (2 ^ (ML - b) - 1) else 0) (ML - 1) + (sN - 1) * (2 ^ (ML - bstar) - 1) + 1 <= N ->
    zsum (map (fun j => FPf j * Z.max 0 (arr_get DLf j - L' j)) UPl) <= Ftot t FC0.
  Proof.
    intros M15 GAP NU BUD. pose proof US as [_ USu]. pose proof MLR as MR. destruct LIf as [LBC NN OUT CNT K _ _].
    assert (B7 : 7 <= bstar <= 14).
    { split; [|lia]. destruct (Z_le_gt_dec 7 bstar); [assumption|]. exfalso.
      assert (2 ^ 9 <= 2 ^ (ML - bstar)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in H. lia. }
    assert (M1 : map L' RLl = ct).
    { unfold L'. apply map_nth_idx; [apply RL_NoDup| rewrite ct_length, RL_length; reflexivity]. }
    assert (Ez : z = map (fun j => arr_get DLf j) RLl) by (unfold z, RLl; rewrite map_map; reflexivity).
    set (Fs := map FPf RLl).
    set (g := fun r : nat => nth r Fs 0 * Z.max 0 (nth r z 0 - nth r ct 0)).
    assert (S1 : zsum (map (fun j => FPf j * Z.max 0 (arr_get DLf j - L' j)) UPl) = zsum (map g (seq 0 (Z.to_nat uu)))).
    { rewrite <- (zsum_map_perm _ _ _ RL_perm). rewrite (zsum_map_nth _ RLl 0), RL_length. apply zsum_map_ext. intros r Hr. apply in_seq in Hr.
      subst g Fs. cbn beta. rewrite Ez, <- M1. rewrite !nth_map' by (rewrite RL_length; lia). reflexivity. }
    rewrite S1.
    destruct prefix_structure2 as (P & ECS & LP & ZP).
    set (coef := fun r : nat => if (r <? length P)%nat then 0 else cpen (nth r cs 0)).
    assert (Lcs : length cs = Z.to_nat uu) by (unfold cs; rewrite length_map; apply ct_length).
    assert (Lz : length z = Z.to_nat uu) by (unfold z; rewrite length_map; apply LQ_length).
    assert (TW : forall r, In r (seq 0 (Z.to_nat uu)) -> 11340 * g r <= Ftot t FC0 * coef r).
    { intros r Hr. apply in_seq in Hr. subst g coef. cbn beta.
      pose proof (rank_fib r ltac:(lia)) as RF. fold Fs in RF.
      assert (F0r : 0 <= nth r Fs 0).
      { subst Fs. rewrite nth_map' by (rewrite RL_length; lia). pose proof (FP_ge1 (nth r RLl 0) ltac:(apply (Permutation_in _ RL_perm); apply nth_In; rewrite RL_length; lia)). lia. }
      pose proof (cs_nth r ltac:(lia)) as CS.
      destruct (Nat.ltb_spec r (length P)) as [LT|GE].
      - rewrite (ZP r LT), CS. rewrite Z.mul_0_r. enough (Z.max 0 (Z.min (nth r ct 0) ML - nth r ct 0) = 0) by nia. lia.
      -
        assert (Zr : 1 <= nth r z 0 <= ML).
        { apply (lens_asc_In (arr_get BCf) ML). rewrite <- z_is. apply nth_In. lia. }
        assert (Cr : bstar <= nth r cs 0 <= ML).
        { split.
          - rewrite ECS. rewrite nth_app_r by lia.
            assert (IN : In (nth (r - length P) (repeat bstar (Z.to_nat sN) ++ flat_map (fun b : Z => repeat b (Z.to_nat (arr_get BCc b))) (ziota (bstar + 1) (Z.to_nat (ML - bstar)))) 0)
                          (repeat bstar (Z.to_nat sN) ++ flat_map (fun b : Z => repeat b (Z.to_nat (arr_get BCc b))) (ziota (bstar + 1) (Z.to_nat (ML - bstar))))).
            { apply nth_In. apply (f_equal (@length Z)) in ECS. rewrite length_app in ECS. lia. }
            apply in_app_iff in IN. destruct IN as [IN|IN]; [apply repeat_spec in IN; lia| apply flat_map_repeat_In_ge in IN; lia].
          - rewrite CS. lia. }
        pose proof (cpen_fib (nth r cs 0) ltac:(lia)) as (CF & Cnn & _).
        pose proof (fibZ_nonneg (nth r ct 0 + 1)).
        destruct (Z_lt_le_dec (nth r ct 0) ML) as [LTM|GEM].
        + assert (EQ : nth r cs 0 = nth r ct 0) by (rewrite CS; lia). rewrite EQ in *.
          assert (Z.max 0 (nth r z 0 - nth r ct 0) <= 15 - nth r ct 0) by lia.
          assert (11340 * (nth r Fs 0 * Z.max 0 (nth r z 0 - nth r ct 0)) <= nth r Fs 0 * (11340 * (15 - nth r ct 0))) by nia.
          assert (nth r Fs 0 * (11340 * (15 - nth r ct 0)) <= nth r Fs 0 * (cpen (nth r ct 0) * fibZ (nth r ct 0 + 1))) by nia.
          nia.
        + replace (Z.max 0 (nth r z 0 - nth r ct 0)) with 0 by lia. pose proof (Ftot_nonneg := I). nia. }
    pose proof (zsum_map_le (fun r => 11340 * g r) (fun r => Ftot t FC0 * coef r) (seq 0 (Z.to_nat uu)) TW) as SUMLE.
    rewrite !zsum_map_mul in SUMLE.
    assert (CSUM : zsum (map coef (seq 0 (Z.to_nat uu))) = sN * cpen bstar + zsum (map (fun b => arr_get BCc b * cpen b) (ziota (bstar + 1) (Z.to_nat (ML - bstar))))).
    { rewrite (zsum_map_seq_split coef (length P) (Z.to_nat uu)) by (apply (f_equal (@length Z)) in ECS; rewrite length_app in ECS; lia).
      rewrite (zsum_map_ext coef (fun _ => 0) (seq 0 (length P))) by (intros r Hr; apply in_seq in Hr; subst coef; cbn beta; replace (r <? length P)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity).
      replace (zsum (map (fun _ : nat => 0) (seq 0 (length P)))) with 0 by (induction (seq 0 (length P)); cbn; lia).
      rewrite zsum_map_seq_shift.
      transitivity (zsum (map cpen (skipn (length P) cs))).
      - rewrite (zsum_map_nth cpen (skipn (length P) cs) 0). rewrite length_skipn, Lcs. apply zsum_map_ext. intros i Hi. apply in_seq in Hi.
        subst coef. cbn beta. replace (length P + i <? length P)%nat with false by (symmetry; apply Nat.ltb_ge; lia). rewrite nth_skipn. reflexivity.
      - rewrite ECS at 1. rewrite skipn_app, Nat.sub_diag, skipn_all, app_nil_l, skipn_O.
        rewrite map_app, zsum_app, zsum_repeat, Z2Nat.id by lia. rewrite zsum_flat_map_repeat by (intros; apply BCc_nn; lia). lia. }
    assert (TAIL : zsum (map (fun b => arr_get BCc b * cpen b) (ziota (bstar + 1) (Z.to_nat (ML - bstar))))
                   = 21 * isum (fun b => if bstar <? b then arr_get BCc b * (2 ^ (ML - b) - 1) else 0) (ML - 1)).
    { unfold isum. replace (Z.to_nat (ML - 1)) with (Z.to_nat bstar + Z.to_nat (ML - 1 - bstar))%nat by lia.
      assert (G : forall a p q, ziota a (p + q) = ziota a p ++ ziota (a + Z.of_nat p) q).
      { intros a p0. revert a. induction p0; intros a q; cbn; [f_equal; lia|]. rewrite IHp0. f_equal. f_equal. f_equal. lia. }
      rewrite G, map_app, zsum_app. replace (1 + Z.of_nat (Z.to_nat bstar)) with (bstar + 1) by lia.
      rewrite (zsum_map_ext (fun b => if bstar <? b then _ else 0) (fun _ => 0) (ziota 1 (Z.to_nat bstar))) by (intros b Hb0; apply in_ziota in Hb0; replace (bstar <? b) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      replace (zsum (map (fun _ : Z => 0) (ziota 1 (Z.to_nat bstar)))) with 0 by (induction (ziota 1 (Z.to_nat bstar)); cbn; lia).
      replace (Z.to_nat (ML - bstar)) with (S (Z.to_nat (ML - 1 - bstar))) by lia. rewrite ziota_S_r, map_app, zsum_app.
      cbn [map zsum]. replace (bstar + 1 + Z.of_nat (Z.to_nat (ML - 1 - bstar))) with ML by lia.
      replace (cpen ML) with 0 by (rewrite M15; reflexivity).
      enough (E : zsum (map (fun b => arr_get BCc b * cpen b) (ziota (bstar + 1) (Z.to_nat (ML - 1 - bstar))))
                  = 21 * zsum (map (fun b => if bstar <? b then arr_get BCc b * (2 ^ (ML - b) - 1) else 0) (ziota (bstar + 1) (Z.to_nat (ML - 1 - bstar))))) by lia.
      rewrite <- zsum_map_mul. apply zsum_map_ext.
      intros b Hb0. apply in_ziota in Hb0. replace (bstar <? b) with true by (symmetry; apply Z.ltb_lt; lia).
      unfold cpen. replace (b =? 7) with false by (symmetry; apply Z.eqb_neq; lia). rewrite M15. lia. }
    pose proof (cpen_fib bstar ltac:(lia)) as (_ & [C0 C21] & C4320).
    assert (E2 : 2 ^ (ML - bstar) = 2 ^ (15 - bstar)) by (rewrite M15; reflexivity).
    rewrite E2 in BUD, GAP.
    pose proof (isum_nonneg (fun b => if bstar <? b then arr_get BCc b * (2 ^ (ML - b) - 1) else 0) (ML - 1)
                  ltac:(intros i Hi; cbn beta; destruct (bstar <? i); [|lia]; pose proof (BCc_nn i ltac:(lia)); pose proof (Z.pow_pos_nonneg 2 (ML - i) ltac:(lia) ltac:(lia)); nia)) as MIDnn.
    set (MID := isum _ (ML - 1)) in TAIL, BUD, MIDnn.
    assert (COEF : zsum (map coef (seq 0 (Z.to_nat uu))) <= 11340).
    { rewrite CSUM, TAIL.
      replace (sN * cpen bstar) with (cpen bstar + (sN - 1) * cpen bstar) by lia.
      assert ((sN - 1) * cpen bstar <= (sN - 1) * (21 * (2 ^ (15 - bstar) - 1))) by (apply Z.mul_le_mono_nonneg_l; [lia | exact C21]).
      nia. }
    assert (FT0 : 0 <= Ftot t FC0).
    { unfold Ftot. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & Hj). pose proof (FP_ge1 j Hj). lia. }
    assert (G0 : 0 <= zsum (map g (seq 0 (Z.to_nat uu)))).
    { apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (r & <- & Hr). apply in_seq in Hr. subst g. cbn beta.
      assert (0 <= nth r Fs 0); [|nia]. subst Fs. rewrite nth_map' by (rewrite RL_length; lia).
      pose proof (FP_ge1 (nth r RLl 0) ltac:(apply (Permutation_in _ RL_perm); apply nth_In; rewrite RL_length; lia)). lia. }
    nia.
  Qed.

  Theorem Lprime_facts :
    map L' RLl = ct
    /\ Permutation (map L' UPl) (map nd UPl)
    /\ nondec (map L' RLl)
    /\ (forall j, In j UPl -> 1 <= L' j <= uu - 1)
    /\ (forall i j, In i UPl -> In j UPl -> FPf i < FPf j -> L' j <= L' i)
    /\ zsum (map (fun j => FPf j * L' j) UPl) <= zsum (map (fun j => FPf j * nd j) UPl)
    /\ (forall j, In j UPl -> (L' j < bstar -> arr_get DLf j = L' j)
                              /\ (arr_get DLf j = L' j \/ (bstar + 1 <= arr_get DLf j <= ML /\ bstar <= L' j)))
    /\ map (fun j => arr_get DLf j) RLl = lens_asc (arr_get BCf) ML.
  Proof.
    pose proof MLR as MR.
    assert (M1 : map L' RLl = ct).
    { unfold L'. apply map_nth_idx; [apply RL_NoDup| rewrite ct_length, RL_length; reflexivity]. }
    split; [exact M1|].
    split.
    { transitivity (map L' RLl); [apply Permutation_map; apply Permutation_sym; apply RL_perm|]. rewrite M1.
      transitivity d0; [apply ct_perm|]. unfold d0, RLl. rewrite <- (map_map (arr_get HP7) nd). apply Permutation_map. apply RL_perm. }
    split; [rewrite M1; apply ct_nondec|].
    split.
    { intros j Hj. destruct (rank_of j Hj) as (r & q & Hr & Ir & Nq & Iq & Eq & Zr & Lr). rewrite Lr.
      apply d0_range. apply (Permutation_in _ ct_perm). apply nth_In. rewrite ct_length. exact Hr. }
    split.
    { intros i j Hi Hj Fij.
      destruct (rank_of i Hi) as (ri & qi & Hri & Iri & Nqi & Iqi & Eqi & Zri & Lri).
      destruct (rank_of j Hj) as (rj & qj & Hrj & Irj & Nqj & Iqj & Eqj & Zrj & Lrj).
      rewrite Lri, Lrj.
      destruct (Nat.lt_ge_cases ri rj) as [LT|GE].
      - exfalso. pose proof (noninc_nth (map FPf RLl) ri rj 0 F_rank_noninc ltac:(lia) ltac:(rewrite length_map, RL_length; exact Hrj)) as X.
        rewrite !nth_map' in X by (rewrite RL_length; assumption).
        rewrite <- Iri, (nth_idx i) in X by (apply (Permutation_in _ (Permutation_sym RL_perm)); exact Hi).
        rewrite <- Irj, (nth_idx j) in X by (apply (Permutation_in _ (Permutation_sym RL_perm)); exact Hj). lia.
      - apply nondec_nth; [apply ct_nondec| exact GE| rewrite ct_length; exact Hri]. }
    split.
    {
      rewrite <- (zsum_map_perm (fun j => FPf j * L' j) _ _ RL_perm). rewrite <- (zsum_map_perm (fun j => FPf j * nd j) _ _ RL_perm).
      rewrite <- !dot_map. rewrite M1.
      replace (map nd RLl) with d0 by (unfold d0, RLl; rewrite map_map; reflexivity).
      apply dot_sorted_le; [apply F_rank_noninc| apply ct_nondec| apply ct_perm|].
      unfold d0. rewrite !length_map. unfold RLl. rewrite length_map. lia. }
    split.
    { intros j Hj. destruct (rank_of j Hj) as (r & q & Hr & Ir & Nq & Iq & Eq & Zr & Lr).
      rewrite <- Zr, Lr. pose proof (rank_structure r Hr) as [A B]. rewrite cs_nth in A, B by exact Hr.
      destruct (LQ_in q Iq) as [Rq Lq0]. pose proof (RNG q Rq Lq0) as RG. rewrite Eq in RG. rewrite <- Zr in RG.
      split.
      - intros LT. rewrite A by lia. lia.
      - destruct B as [[B1 B2]|B]; [left; rewrite B1 in *; lia| right; lia]. }
    rewrite <- z_is. unfold z, RLl. rewrite map_map. reflexivity.
  Qed.
End Final.


Local Notation X6 DLc BCc OLc SLc := (bt_upd s t FC DLc HP7 1 (hm - 1) DP BCc OLc SLc MCv).

Lemma capped_kraft_cut : forall BCc d,
  (forall b, 0 <= b <= 15 -> arr_get BCc b = zsum (map (fun j => if Z.min (nd j) ML =? b then 1 else 0) UPl)) ->
  (exists e, In e (hprof 0 (T HP sub)) /\ ML < ed e) ->
  1 <= d <= ML - 1 ->
  isum (fun b => arr_get BCc b * 2 ^ (ML - b)) d <= 2 ^ ML - 2 ^ (ML - d).
Proof.
  intros BCc d SBC (e0 & He0 & De0) Hd. pose proof MLR as MR.
  destruct (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
  set (TT := T HP sub) in *.
  set (g := fun b => if b <=? d then 2 ^ (ML - b) else 0).
  rewrite <- (isum_ext (fun b => arr_get BCc b * g b)) by (intros b Hb0; subst g; cbn beta; replace (b <=? d) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
  rewrite <- (isum_zero_range (fun b => arr_get BCc b * g b) d ML) by (lia || (intros; subst g; cbn beta; replace (i <=? d) with false by (symmetry; apply Z.leb_gt; lia); lia)).
  assert (MIN : forall j, In j UPl -> 1 <= Z.min (nd j) ML <= ML).
  { intros j Hj. pose proof (nd_leaf_range j Hj). lia. }
  rewrite (isum_ext _ (fun b => zsum (map (fun j => if Z.min (nd j) ML =? b then 1 else 0) UPl) * g b)) by (intros b Hb0; rewrite SBC by lia; reflexivity).
  rewrite <- (regroup UPl (fun j => Z.min (nd j) ML) g ML ltac:(lia) MIN).
  transitivity (zsum (map (fun p : Z * Z => g (Z.min (snd p) ML)) (map (fun j => (j, nd j)) UPl))); [rewrite map_map; apply Z.le_refl|].
  rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. cbn [snd].
  transitivity (zsum (map (fun e => if ed e <=? d then 2 ^ (ML - ed e) else 0) (hprof 0 TT))).
  { apply Z.eq_le_incl. apply zsum_map_ext. intros e He. subst g. cbn beta.
    destruct (Z.leb_spec (Z.min (ed e) ML) d), (Z.leb_spec (ed e) d); try lia. f_equal. lia. }
  set (Hs := hheight TT + ML).
  assert (HH : d < 0 + hheight TT).
  { pose proof (hprof_dep 0 TT e0 He0). lia. }
  pose proof (kraft_cut TT 0 d Hs ltac:(lia) HH ltac:(subst Hs; lia)) as KC. rewrite Z.sub_0_r in KC.
  assert (SC : zsum (map (fun e => if ed e <=? d then 2 ^ (Hs - ed e) else 0) (hprof 0 TT))
             = 2 ^ (Hs - ML) * zsum (map (fun e => if ed e <=? d then 2 ^ (ML - ed e) else 0) (hprof 0 TT))).
  { rewrite <- zsum_map_mul. apply zsum_map_ext. intros e He. destruct (Z.leb_spec (ed e) d); [|lia].
    rewrite <- Z.pow_add_r by (subst Hs; pose proof (hheight_nonneg TT); lia). f_equal. lia. }
  assert (P1 : 2 ^ Hs = 2 ^ (Hs - ML) * 2 ^ ML) by (rewrite <- Z.pow_add_r by (subst Hs; pose proof (hheight_nonneg TT); lia); f_equal; lia).
  assert (P2 : 2 ^ (Hs - d) = 2 ^ (Hs - ML) * 2 ^ (ML - d)) by (rewrite <- Z.pow_add_r by (subst Hs; pose proof (hheight_nonneg TT); lia); f_equal; lia).
  pose proof (Z.pow_pos_nonneg 2 (Hs - ML) ltac:(lia) ltac:(subst Hs; pose proof (hheight_nonneg TT); lia)). nia.
Qed.

Theorem gen_bitlen_overflow2 : forall DLc BCc OLc SLc ovc,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  GI t FC0 OL SL FC DL HP 573 DLc BCc OLc SLc ovc -> ovc <> 0 ->
  exists DLf BCf OLf bstar sN,
    gen_bitlen_loop3 (Z.to_nat ML) (gen_bitlen_loop2 573 (X6 DLc BCc OLc SLc) ML ovc) t MCv ML HEAP_SIZE = X6 DLf BCf OLf SLc
    /\ arr_len DLf = tsize t /\ arr_len BCf = 16
    /\ (forall j, In j UPl -> 1 <= arr_get DLf j <= ML)
    /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLf j = 0)
    /\ (forall g, zsum (map (fun j => g (arr_get DLf j)) UPl) = isum (fun b => arr_get BCf b * g b) ML)
    /\ KB (arr_get BCf) = 2 ^ ML
    /\ (forall b, 0 <= b <= 15 -> (b < 1 \/ ML < b) -> arr_get BCf b = 0)
    /\ (forall b, 0 <= b <= 15 -> 0 <= arr_get BCf b)
    /\ OLf = wrap64 (OL + zsum (map (fun j => FPf j * (arr_get DLf j + xb j)) UPl))
    /\ (forall i j, In i UPl -> In j UPl -> FPf i < FPf j -> arr_get DLf j <= arr_get DLf i)
    /\ BCf = arepair (Z.to_nat N) ML BCc /\ 1 <= N
    /\ 1 <= bstar <= ML - 1 /\ 1 <= sN
    /\ (forall b, 1 <= b < bstar -> arr_get BCf b = arr_get BCc b)
    /\ arr_get BCf bstar = arr_get BCc bstar - sN
    /\ 2 ^ (ML - bstar) <= uu - 2
    /\ let Lp := L' in
       map Lp RLl = ct
    /\ Permutation (map Lp UPl) (map nd UPl)
    /\ nondec (map Lp RLl)
    /\ (forall j, In j UPl -> 1 <= Lp j <= uu - 1)
    /\ (forall i j, In i UPl -> In j UPl -> FPf i < FPf j -> Lp j <= Lp i)
    /\ zsum (map (fun j => FPf j * Lp j) UPl) <= zsum (map (fun j => FPf j * nd j) UPl)
    /\ (forall j, In j UPl -> (Lp j < bstar -> arr_get DLf j = Lp j)
                              /\ (arr_get DLf j = Lp j \/ (bstar + 1 <= arr_get DLf j <= ML /\ bstar <= Lp j)))
    /\ map (fun j => arr_get DLf j) RLl = lens_asc (arr_get BCf) ML
    /\ (ML = 15 -> zsum (map (fun j => FPf j * Z.max 0 (arr_get DLf j - Lp j)) UPl) <= Ftot t FC0)
    /\ (forall r, (r < length RLl)%nat ->
          fibZ (nth r (map Lp RLl) 0 + 1) * nth r (map FPf RLl) 0 + fibZ (nth r (map Lp RLl) 0) <= Ftot t FC0)
    /\ map (fun j => arr_get DLf j) RLl
         = lens_asc (arr_get (arepair (Z.to_nat (zsum (map (fun x => 2 ^ (ML - x)) (map (fun x => Z.min x ML) (map Lp RLl))) - 2 ^ ML)) ML
                               (bc_of (map (fun x => Z.min x ML) (map Lp RLl))))) ML.
Proof.
  intros DLc BCc OLc SLc ovc LBC OLr SLr G Hov.
  pose proof (pass1_summary t FC0 OL SL FC DL HP DP sub INV OLr SLr DLc BCc OLc SLc ovc G) as (SDL & SZ & SBC & SOL & SSL & SOV & LDLc & LBCc).
  pose proof (excess_identity t FC0 0 FC DL HP DP sub INV) as (EK & EO & NN). pose proof MLR as MR.
  pose proof MCF as [MCr LF].
  destruct G as [GL GD GT GZ GB GO GS GV].
  assert (OV : ovc = 2 * N) by (rewrite GV; exact EO).
  assert (N1 : 1 <= N) by lia.
  pose proof (LI_start t FC0 0 FC DL HP DP sub INV BCc LBCc SBC) as L0.
  assert (DEEP : exists e, In e (hprof 0 (T HP sub)) /\ ML < ed e).
  { destruct (Exists_dec (fun e => ML < ed e) (hprof 0 (T HP sub))) as [E|NE]; [intros e; destruct (Z_lt_le_dec ML (ed e)); [left|right]; lia| |].
    - apply Exists_exists in E. exact E.
    - exfalso. apply Hov. apply (proj2 SOV). intros e He. apply Forall_Exists_neg in NE. rewrite Forall_forall in NE. specialize (NE e He). lia. }
  pose proof (repair_structure BCc L0 N1 ltac:(intros d Hd; apply (capped_kraft_cut BCc d SBC DEEP Hd))) as (LIf & EBCF & bstar & sN & Hb & Hs & LOWEQ & ATEQ & GAP & BUD & NU).
  set (BCf := BCF BCc) in *.
  assert (Nk : N <= uu - 1).
  { unfold HuffGen2.N.
    assert (G : forall f n, 0 <= n -> (forall i, 1 <= i <= n -> 0 <= f i <= 1) -> isum f n <= n).
    { intros f n Hn Hf. replace n with (Z.of_nat (Z.to_nat n)) in * by lia. revert Hf. generalize (Z.to_nat n) as k. clear n Hn.
      induction k as [|k IH]; intros Hf; [rewrite isum_0; lia|].
      rewrite Nat2Z.inj_succ in *. replace (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1) in * by lia. rewrite isum_snoc by lia.
      specialize (IH ltac:(intros; apply Hf; lia)). pose proof (Hf (Z.of_nat k + 1) ltac:(lia)). lia. }
    apply G; [pose proof U2; lia|]. intros i Hi. destruct (_ <=? _); lia. }
  assert (E2 : gen_bitlen_loop2 573 (X6 DLc BCc OLc SLc) ML ovc = X6 DLc BCf OLc SLc).
  { rewrite OV. pose proof U2. rewrite gb_loop2_fun by lia. rewrite <- EBCF. reflexivity. }
  rewrite E2.
  assert (OLcr : 0 <= OLc < 2 ^ 64) by (rewrite GO; apply wrap64_range).
  destruct (gb_loop3 s t FC0 FC DL HP DP sub INV DLc BCf OLc SLc LIf OLcr (Z.to_nat ML) ML 573 DLc OLc ltac:(lia) ltac:(lia) (OI_start t FC0 FC HP DLc BCf OLc 0 OLcr LDLc))
    as (DLf & OLf & hf & E3 & O3).
  unfold HEAP_SIZE. rewrite E3.
  destruct (OI_final t FC0 FC DL HP DP sub INV DLc BCf OLc LIf OLcr hf DLf OLf O3) as (ALL & RNG & MONO & SUMg & ZERO & OLF & LDLf).
  pose proof LIf as [LBCf NNf OUTf CNTf KKf _ _].
  assert (POS : forall j, In j UPl -> exists q, hm <= q <= 572 /\ leafp q = true /\ arr_get HP7 q = j).
  { intros j Hj. pose proof (Permutation_in j (Permutation_sym LPOS) Hj) as Hin.
    apply in_map_iff in Hin. destruct Hin as (q & Eq & Hq). apply filter_In in Hq. destruct Hq as [Hq Lq].
    unfold HuffGen.rng in Hq. apply in_ziota in Hq. exists q. split; [lia|]. split; assumption. }
  pose proof (Lprime_facts BCc DLf BCf SBC LIf RNG MONO SUMg bstar sN Hb Hs LOWEQ ATEQ) as LPF.
  exists DLf, BCf, OLf, bstar, sN. split; [reflexivity|]. split; [exact LDLf|]. split; [exact LBCf|].
  split. { intros j Hj. destruct (POS j Hj) as (q & Hq & Lq & <-). apply RNG; assumption. }
  split. { intros j Hj Hnj. rewrite ZERO by assumption. apply SZ; assumption. }
  split.
  { intros g. rewrite <- SUMg. symmetry. apply SUML.
    - intros h Hh Lh. rewrite Lh. reflexivity.
    - intros h Hh Lh. rewrite Lh. reflexivity. }
  split; [rewrite KKf; lia|]. split; [exact OUTf|]. split; [exact NNf|].
  split.
  { rewrite OLF, GO. rewrite BuildTreeModel.wrap64_add_l. f_equal. rewrite <- Z.add_assoc. f_equal.
    rewrite (SUML (fun j => FPf j * (Z.min (nd j) ML + xb j)) (olf t FC0 FC DL HP)).
    2:{ intros h Hh Lh. unfold olf. rewrite Lh. unfold Ld. pose proof INV as [? ? ? ? ? ? ? ? i_fc]. rewrite i_fc; [reflexivity|].
        apply (proj1 (LF h ltac:(lia))) in Lh. pose proof (IDR h ltac:(lia)). lia. }
    2:{ intros h Hh Lh. unfold olf. rewrite Lh. reflexivity. }
    rewrite (SUML (fun j => (arr_get DLf j - Z.min (nd j) ML) * FPf j) (fun q => if leafp q then (arr_get DLf (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0)).
    2:{ intros h Hh Lh. rewrite Lh. pose proof INV as [? ? ? ? ? ? ? ? i_fc].
        pose proof (proj1 (LF h ltac:(lia)) Lh) as Lt. pose proof (IDR h ltac:(lia)) as [R1 R2].
        rewrite i_fc by lia. rewrite SDL by (apply (proj1 R2); exact Lt). reflexivity. }
    2:{ intros h Hh Lh. rewrite Lh. reflexivity. }
    rewrite <- zsum_map_add. apply zsum_map_ext. intros; lia. }
  split.
  { intros i j Hi Hj Fij.
    destruct (POS i Hi) as (qi & Hqi & Lqi & Ei). destruct (POS j Hj) as (qj & Hqj & Lqj & Ej).
    pose proof INV as [? ? ? ? ? ? ? ? i_fc].
    pose proof (IDR qi ltac:(lia)) as [Ri1 Ri2]. pose proof (IDR qj ltac:(lia)) as [Rj1 Rj2].
    pose proof (proj1 (LF qi ltac:(lia)) Lqi) as Lti. pose proof (proj1 (LF qj ltac:(lia)) Lqj) as Ltj.
    assert (Wi : FPf i = arr_get FC (arr_get HP7 qi)) by (rewrite i_fc by lia; rewrite Ei; reflexivity).
    assert (Wj : FPf j = arr_get FC (arr_get HP7 qj)) by (rewrite i_fc by lia; rewrite Ej; reflexivity).
    destruct (Z_le_gt_dec qi qj).
    - pose proof (WO qi qj ltac:(lia) ltac:(lia)). lia.
    - rewrite <- Ei, <- Ej. apply MONO; try assumption; lia. }
  split; [unfold BCf, BCF, RB; reflexivity|]. split; [exact N1|].
  split; [exact Hb|]. split; [exact Hs|]. split; [exact LOWEQ|]. split; [exact ATEQ|]. split; [exact GAP|].
  cbv zeta. destruct LPF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
  split; [intros M15; unfold MIDf in BUD; exact (pen_rank_bound BCc DLf BCf SBC LIf RNG MONO SUMg bstar sN Hb Hs LOWEQ ATEQ M15 GAP NU BUD)|].
  split.
  { intros r Hr. rewrite Q1. rewrite RL_length in Hr. exact (rank_fib2 r Hr). }
  rewrite Q1. fold cs. rewrite <- N_canon.
  pose proof (z_canon BCc DLf BCf SBC LIf RNG MONO SUMg eq_refl L0) as ZC. unfold z in ZC.
  unfold RLl at 1. rewrite map_map. exact ZC.
Qed.

End Pen.
