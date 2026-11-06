From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct ReaderRes parse_items_shape pj_set_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Frame.
Import ListNotations.
Open Scope Z_scope.

Lemma sh_perm_mid : forall (T X Y : list (Z * Z)), Permutation (T ++ X ++ Y) ((T ++ Y) ++ X).
Proof.
  intros T X Y. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma sh_nodup_swap : forall (P Du Dw Q : list (Z * Z)), NoDup (P ++ Du ++ Q) -> NoDup Dw ->
  (forall b, In b Dw -> ~ In b (P ++ Du ++ Q)) -> NoDup (P ++ Dw ++ Q).
Proof.
  intros P Du Dw Q H1 H2 H3.
  apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_sym (sh_perm_mid P Dw Q))).
  apply NoDup_ListNoDup. apply pis_nodup_app.
  - apply (pis_nodup_l _ _ Du). apply NoDup_ListNoDup. apply (Permutation_NoDup (sh_perm_mid P Du Q)).
    apply NoDup_ListNoDup. exact H1.
  - exact H2.
  - intros b Hb Hw. apply (H3 b Hw). apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb].
Qed.

Lemma sh_notin : forall (P Du Q : list (Z * Z)) b, NoDup (P ++ Du ++ Q) -> In b (P ++ Q) -> ~ In b Du.
Proof.
  intros P Du Q b H Hb Hu.
  assert (H' : NoDup ((P ++ Q) ++ Du)).
  { apply NoDup_ListNoDup. apply (Permutation_NoDup (sh_perm_mid P Du Q)). apply NoDup_ListNoDup. exact H. }
  exact (pis_nodup_app_disj _ _ _ b H' Hb Hu).
Qed.

Section S.
Variable segs : list Segment.

Lemma sh_node_nodup : forall m lblk p t D, pj_node segs m lblk p t D -> NoDup D.
Proof. intros m lblk p t D H. destruct t; cbn [pj_node] in H; exact (proj1 H). Qed.

Lemma sh_hit : forall m Lam o ms D num str kids keys n cap i nm vi w tv Dw,
  pj_node segs m (lin Lam) o (JObj ms) D -> pj_hdr segs m o 6 num str kids keys n cap -> cap <= 2 ^ 54 ->
  nth_error ms i = Some (nm, vi) ->
  pj_node segs m (lin Lam) w tv Dw -> (forall bk, In bk Dw -> ~ In bk D) -> pj_apart Dw o ->
  exists Du Dr, Permutation D (Du ++ Dr) /\ pj_node segs m (lin Lam) (kids + 56 * Z.of_nat i) vi Du /\
    (forall m' Lam',
       (forall y, o <= y < o + 56 -> pis_same segs m m' y) ->
       (forall b y, In b D -> ~ In b Du -> pj_holds b y ->
          (b <> (kids, 56 * cap) \/ ~ (kids + 56 * Z.of_nat i <= y < kids + 56 * Z.of_nat i + 56)) ->
          pis_same segs m m' y) ->
       (forall y, (exists b, In b Dw /\ pj_holds b y) -> pis_same segs m m' y) ->
       (forall j, 0 <= j < 56 -> mbyte segs m' (kids + 56 * Z.of_nat i + j) = mbyte segs m (w + j)) ->
       (forall j, 0 <= j < 56 -> writable_at segs m' (kids + 56 * Z.of_nat i + j)) ->
       (forall a k, In (a, k) D -> ~ In (a, k) Du -> lin Lam' a k) -> (forall a k, In (a, k) Dw -> lin Lam' a k) ->
       pj_apart Dw (kids + 56 * Z.of_nat i) ->
       exists Do, Permutation Do (Dr ++ Dw) /\
         pj_node segs m' (lin Lam') o (JObj (firstn i ms ++ (nm, tv) :: skipn (S i) ms)) Do).
Proof.
  intros m Lam o ms D num str kids keys n cap i nm vi w tv Dw HN HH Hc Hi HNw HDD HAw.
  destruct (ps_node_open segs m (lin Lam) o ms D num str kids keys n cap HN HH Hc) as (Di & ED & Es & En & HO).
  pose proof HO as (HND & HAP & HH' & HSL & _ & HIT).
  cbn [pis_items] in HIT. destruct HIT as (_ & HM). rewrite pis_combine_map in HM.
  destruct (ps_mems_split segs m (lin Lam) (pj_node segs m (lin Lam)) ms kids keys Di i nm vi HM Hi)
    as (Dpre & x & kx & Du & Dpost & EDi & Hpre & Hx & Hcx & Hu & Hpost).
  assert (Hil : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  pose proof (pis_mems_bnd segs m (lin Lam) ms kids keys Di HM ltac:(lia)) as (Hk8 & Hk0 & Hk1 & Hy0 & Hy1).
  pose proof HSL as (_ & (Hnc & _) & _ & _).
  pose proof HH as (_ & _ & _ & _ & _ & _ & _ & (Hc0 & _)).
  assert (Hcp : 0 < cap) by lia.
  assert (ES : pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
  { rewrite ps_slots_eq. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
  subst D Di str.
  set (T := pis_slots true kids keys cap ++ Dpre ++ [(x, kx)]).
  assert (ET : forall Y, pis_slots true kids keys cap ++ Dpre ++ (x, kx) :: Y = T ++ Y)
    by (intros Y; unfold T; rewrite <- !app_assoc; reflexivity).
  rewrite ET in HND, HDD, HAP, HN.
  assert (HnU : forall b, In b (T ++ Dpost) -> ~ In b Du) by (intros b Hb; exact (sh_notin T Du Dpost b HND Hb)).
  assert (HinD : forall b, In b (T ++ Dpost) -> In b (T ++ Du ++ Dpost)).
  { intros b Hb. apply in_app_or in Hb. apply in_or_app.
    destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_or_app; right; exact Hb]. }
  assert (HinT : forall b, In b (pis_slots true kids keys cap) \/ In b Dpre \/ b = (x, kx) \/ In b Dpost ->
    In b (T ++ Dpost)).
  { intros b [Hb|[Hb|[Hb|Hb]]]; apply in_or_app; unfold T.
    - left. apply in_or_app. left. exact Hb.
    - left. apply in_or_app. right. apply in_or_app. left. exact Hb.
    - left. apply in_or_app. right. apply in_or_app. right. left. symmetry. exact Hb.
    - right. exact Hb. }
  assert (HkT : In (kids, 56 * cap) (T ++ Dpost)) by (apply HinT; left; rewrite ES; left; reflexivity).
  assert (HyT : In (keys, 8 * cap) (T ++ Dpost)) by (apply HinT; left; rewrite ES; right; left; reflexivity).
  assert (Hnk : forall b, In b Dpre \/ b = (x, kx) \/ In b Dpost -> b <> (kids, 56 * cap)).
  { intros b Hb Eb. subst b.
    assert (HN2 : NoDup (pis_slots true kids keys cap ++ Dpre ++ (x, kx) :: Dpost)).
    { rewrite ET. apply (pis_nodup_l _ _ Du). apply NoDup_ListNoDup.
      apply (Permutation_NoDup (sh_perm_mid T Du Dpost)). apply NoDup_ListNoDup. exact HND. }
    apply (pis_nodup_app_disj _ _ _ (kids, 56 * cap) HN2); [rewrite ES; left; reflexivity|].
    destruct Hb as [Hb|[Hb|Hb]]; apply in_or_app;
      [left; exact Hb | right; left; symmetry; exact Hb | right; right; exact Hb]. }
  exists Du, (T ++ Dpost). rewrite !ET.
  split.
  { apply Permutation_sym. rewrite app_assoc. apply (Permutation_trans (Permutation_app_tail Dpost (Permutation_app_comm Du T))).
    rewrite <- app_assoc. apply Permutation_refl. }
  split; [exact Hu|].
  intros m' Lam' F1 F2 F3 F4 F5 F6 F7 F8.
  exists (T ++ Dw ++ Dpost). split.
  { rewrite <- (app_assoc T Dpost Dw). apply Permutation_app_head. apply Permutation_app_comm. }
  assert (Hlen : length (firstn i ms) = i) by (apply firstn_length_le; lia).
  assert (NDw : NoDup Dw) by exact (sh_node_nodup m (lin Lam) w tv Dw HNw).
  replace (T ++ Dw ++ Dpost) with (pis_slots true kids keys cap ++ (Dpre ++ (x, kx) :: Dw ++ Dpost))
    by (rewrite <- (ET (Dw ++ Dpost)); reflexivity).
  apply (ps_obj_node segs m' (lin Lam') o (firstn i ms ++ (nm, tv) :: skipn (S i) ms) (Dpre ++ (x, kx) :: Dw ++ Dpost)
    num kids keys n cap).
  2: { rewrite length_app. cbn [length]. rewrite Hlen, length_skipn. lia. }
  split.
  { rewrite (ET (Dw ++ Dpost)). apply (sh_nodup_swap T Du Dw Dpost HND NDw). intros b Hb Hb'. exact (HDD b Hb Hb'). }
  split.
  { rewrite (ET (Dw ++ Dpost)). intros b y Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
    - apply (HAP b y). apply in_or_app. left. exact Hb.
    - apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (HAw b y Hb)|].
      apply (HAP b y). apply in_or_app. right. apply in_or_app. right. exact Hb. }
  split; [exact (pis_hdr_frame segs m m' o _ num 0 kids keys n cap HH' F1)|].
  split.
  { apply (pis_slots_at_mv (lin Lam) (lin Lam') true kids keys n n cap HSL ltac:(lia) ltac:(lia)).
    intros a k Hak. apply F6; [apply HinD; apply HinT; left; exact Hak | apply HnU; apply HinT; left; exact Hak]. }
  split; [intros E; discriminate|].
  cbn [pis_items]. split; [rewrite !length_map; reflexivity|]. rewrite pis_combine_map.
  apply (ps_mems_join segs m' (lin Lam') (pj_node segs m' (lin Lam')) (firstn i ms) (skipn (S i) ms) kids keys Dpre x kx
    Dw Dpost nm tv); rewrite ?Hlen.
  - apply (ps_mems_frame segs m (lin Lam) m' (lin Lam') (firstn i ms) kids keys Dpre Hpre).
    + intros a' k' Hb. assert (Hb' : In (a', k') (T ++ Dpost)) by (apply HinT; right; left; exact Hb).
      exact (F6 a' k' (HinD _ Hb') (HnU _ Hb')).
    + rewrite Hlen. intros y [Hy|[Hy|(b & Hb & Hy)]].
      * apply (F2 (kids, 56 * cap) y (HinD _ HkT) (HnU _ HkT)); [unfold pj_holds; cbn [fst snd]; lia | right; lia].
      * apply (F2 (keys, 8 * cap) y (HinD _ HyT) (HnU _ HyT)); [unfold pj_holds; cbn [fst snd]; lia|].
        left. intros E. injection E. lia.
      * assert (Hb' : In b (T ++ Dpost)) by (apply HinT; right; left; exact Hb).
        apply (F2 b y (HinD _ Hb') (HnU _ Hb') Hy). left. apply Hnk. left. exact Hb.
  - apply (pis_u64_frame segs m m' _ x Hx). intros y Hy.
    apply (F2 (keys, 8 * cap) y (HinD _ HyT) (HnU _ HyT)); [unfold pj_holds; cbn [fst snd]; lia|].
    left. intros E. injection E. lia.
  - assert (Hb' : In (x, kx) (T ++ Dpost)) by (apply HinT; right; right; left; reflexivity).
    apply (pis_cstr_frame segs m (lin Lam) m' (lin Lam') x kx nm Hcx (F6 x kx (HinD _ Hb') (HnU _ Hb'))).
    intros y Hy. apply (F2 (x, kx) y (HinD _ Hb') (HnU _ Hb') Hy). left. apply Hnk. right. left. reflexivity.
  - apply (pis_node_xfer segs tv m (lin Lam) m' (lin Lam') w (kids + 56 * Z.of_nat i) Dw HNw F7 F3).
    + replace (kids + 56 * Z.of_nat i) with (kids + (7 * Z.of_nat i) * 8) by lia. rewrite Z_mod_plus_full. exact Hk8.
    + lia.
    + lia.
    + intros j Hj. exact (F4 j Hj).
    + intros j Hj _. exact (F5 j Hj).
    + exact F8.
  - apply (ps_mems_frame segs m (lin Lam) m' (lin Lam') (skipn (S i) ms) _ _ Dpost Hpost).
    + intros a' k' Hb. assert (Hb' : In (a', k') (T ++ Dpost)) by (apply HinT; right; right; right; exact Hb).
      exact (F6 a' k' (HinD _ Hb') (HnU _ Hb')).
    + rewrite length_skipn. intros y [Hy|[Hy|(b & Hb & Hy)]].
      * apply (F2 (kids, 56 * cap) y (HinD _ HkT) (HnU _ HkT)); [unfold pj_holds; cbn [fst snd]; lia | right; lia].
      * apply (F2 (keys, 8 * cap) y (HinD _ HyT) (HnU _ HyT)); [unfold pj_holds; cbn [fst snd]; lia|].
        left. intros E. injection E. lia.
      * assert (Hb' : In b (T ++ Dpost)) by (apply HinT; right; right; right; exact Hb).
        apply (F2 b y (HinD _ Hb') (HnU _ Hb') Hy). left. apply Hnk. right. right. exact Hb.
Qed.

End S.
