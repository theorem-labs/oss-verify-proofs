(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ent_good (dlo dhi : Z) (x : word * word) : Prop :=
  0 < bv_unsigned (snd x) /\
  bv_unsigned (fst x) + bv_unsigned (snd x) <= two_pow_64 /\
  (bv_unsigned (fst x) + bv_unsigned (snd x) <= dlo \/ dhi <= bv_unsigned (fst x)).
Definition all_good (dlo dhi : Z) (X : list (word * word)) : Prop := forall x, In x X -> ent_good dlo dhi x.

Lemma all_good_nil : forall dlo dhi, all_good dlo dhi [].
Proof. intros dlo dhi x []. Qed.
Lemma all_good_app : forall dlo dhi X Y, all_good dlo dhi X -> all_good dlo dhi Y -> all_good dlo dhi (X ++ Y).
Proof. intros dlo dhi X Y HX HY x Hin. apply in_app_or in Hin as [H|H]; auto. Qed.
Lemma all_good_cons_inv : forall dlo dhi x X, all_good dlo dhi (x :: X) -> ent_good dlo dhi x /\ all_good dlo dhi X.
Proof. intros dlo dhi x X H. split; [apply H; left; reflexivity | intros y Hy; apply H; right; exact Hy]. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_good : forall dlo dhi (a sz : word) lo hi,
  ent_good dlo dhi (a, sz) -> all_good dlo dhi (iv_subtract a sz lo hi).
Proof.
  intros dlo dhi a sz lo hi (Hpos & Hfit & Hmiss) [b s] Hin. cbn [fst snd] in *.
  pose proof (mremap_word_range a). pose proof (mremap_word_range sz).
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E1; cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E1. destruct Hin as [Heq|[]]. inversion Heq; subst b s. clear Heq.
    unfold ent_good. cbn [fst snd].
    rewrite mremap_u64 by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn in Hin; [| contradiction].
    apply Z.ltb_lt in E2. destruct Hin as [Heq|[]]. inversion Heq; subst b s. clear Heq.
    unfold ent_good. cbn [fst snd].
    rewrite !mremap_u64 by lia. lia.
Qed.

Lemma maps_subtract_good : forall dlo dhi X lo hi, all_good dlo dhi X -> all_good dlo dhi (maps_subtract X lo hi).
Proof.
  intros dlo dhi X lo hi HX [b s] Hin.
  destruct (maps_subtract_In X lo hi b s Hin) as (a & sz & Hin0 & Hiv).
  exact (iv_subtract_good dlo dhi a sz lo hi (HX _ Hin0) _ Hiv).
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_ext : forall (a sz : word) lo hi lo' hi',
  (bv_unsigned a <? lo) = (bv_unsigned a <? lo') ->
  (bv_unsigned a < lo -> Z.min (bv_unsigned sz) (lo - bv_unsigned a) = Z.min (bv_unsigned sz) (lo' - bv_unsigned a)) ->
  (hi <? bv_unsigned a + bv_unsigned sz) = (hi' <? bv_unsigned a + bv_unsigned sz) ->
  (hi < bv_unsigned a + bv_unsigned sz -> Z.max (bv_unsigned a) hi = Z.max (bv_unsigned a) hi') ->
  iv_subtract a sz lo hi = iv_subtract a sz lo' hi'.
Proof.
  intros a sz lo hi lo' hi' T1 V1 T2 V2. unfold iv_subtract. cbv zeta.
  rewrite <- T1, <- T2.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    try (apply Z.ltb_lt in E1); try (apply Z.ltb_lt in E2);
    try (rewrite <- (V1 E1)); try (rewrite <- (V2 E2)); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_disjoint_all : forall X lo hi,
  lo <= hi ->
  (forall (b s : word), In (b, s) X -> 0 < bv_unsigned s /\ (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)) ->
  maps_subtract X lo hi = X.
Proof.
  induction X as [|[b s] X IH]; intros lo hi Hle H; [reflexivity|].
  cbn [maps_subtract].
  destruct (H b s (or_introl eq_refl)) as [Hp Hd].
  rewrite (iv_subtract_disjoint b s lo hi Hp Hle Hd). cbn [app].
  rewrite IH; [reflexivity | exact Hle | intros b' s' Hin; apply H; right; exact Hin].
Qed.

Lemma maps_subtract_all_cuts_app : forall A B X,
  maps_subtract_all X (A ++ B) = maps_subtract_all (maps_subtract_all X A) B.
Proof.
  induction A as [|[c n] A IH]; intros B X; [reflexivity|].
  cbn [app maps_subtract_all]. apply IH.
Qed.

Section Forget.
Variables dlo dhi : Z.
Hypothesis Hd0 : 0 <= dlo.
Hypothesis Hd1 : dlo <= dhi.
Hypothesis Hd2 : dhi < two_pow_64.

(* [comment removed for export] *)
Lemma cut_forget_entry : forall (a sz c n : word),
  ent_good dlo dhi (a, sz) ->
  maps_subtract_all [(a, sz)] (iv_subtract c n dlo dhi)
  = iv_subtract a sz (bv_unsigned c) (bv_unsigned c + bv_unsigned n).
Proof.
  intros a sz c n Hg. pose proof Hg as (Hpos & Hfit & Hmiss). cbn [fst snd] in Hpos, Hfit, Hmiss.
  pose proof (mremap_word_range a). pose proof (mremap_word_range sz).
  pose proof (mremap_word_range c). pose proof (mremap_word_range n).
  set (cl := bv_unsigned c) in *. set (ch := cl + bv_unsigned n).
  assert (Hch : cl <= ch) by (unfold ch; lia).
  unfold iv_subtract at 1. cbv zeta. fold cl. fold ch.
  destruct (cl <? dlo) eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
  (destruct (dhi <? ch) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]);
  cbn [app maps_subtract_all maps_subtract]; rewrite ?app_nil_r.
  - (* [comment removed for export] *)
    rewrite (mremap_u64 (Z.min (bv_unsigned n) (dlo - cl))) by lia.
    rewrite (mremap_u64 (Z.max cl dhi)) by lia.
    rewrite (mremap_u64 (ch - Z.max cl dhi)) by (unfold ch in *; lia).
    fold cl.
    replace (Z.max cl dhi + (ch - Z.max cl dhi)) with ch by lia.
    destruct Hmiss as [Hlow | Hhigh].
    + (* [comment removed for export] *)
      rewrite (iv_subtract_ext a sz cl (cl + Z.min (bv_unsigned n) (dlo - cl)) cl ch);
        [| reflexivity | reflexivity
         | destruct (cl + Z.min (bv_unsigned n) (dlo - cl) <? bv_unsigned a + bv_unsigned sz) eqn:Ea;
           destruct (ch <? bv_unsigned a + bv_unsigned sz) eqn:Eb; try reflexivity;
           [apply Z.ltb_lt in Ea; apply Z.ltb_ge in Eb | apply Z.ltb_ge in Ea; apply Z.ltb_lt in Eb]; unfold ch in *; lia
         | intros Hx; unfold ch in *; lia ].
      apply maps_subtract_disjoint_all; [lia|].
      intros b s Hin.
      pose proof (iv_subtract_good dlo dhi a sz cl ch Hg _ Hin) as (Hp & _ & _). cbn [fst snd] in Hp.
      pose proof (iv_subtract_within a sz cl ch b s Hfit Hin) as Hw.
      split; [exact Hp | lia].
    + (* [comment removed for export] *)
      rewrite (iv_subtract_disjoint a sz cl (cl + Z.min (bv_unsigned n) (dlo - cl)) Hpos ltac:(lia) ltac:(lia)).
      cbn [app maps_subtract]. rewrite app_nil_r.
      apply iv_subtract_ext.
      * destruct (bv_unsigned a <? Z.max cl dhi) eqn:Ea; destruct (bv_unsigned a <? cl) eqn:Eb; try reflexivity;
          [apply Z.ltb_lt in Ea; apply Z.ltb_ge in Eb | apply Z.ltb_ge in Ea; apply Z.ltb_lt in Eb]; lia.
      * intros Hx. lia.
      * reflexivity.
      * reflexivity.
  - (* [comment removed for export] *)
    rewrite (mremap_u64 (Z.min (bv_unsigned n) (dlo - cl))) by lia. fold cl.
    destruct Hmiss as [Hlow | Hhigh].
    + apply iv_subtract_ext; [reflexivity | reflexivity | | intros Hx; unfold ch in *; lia].
      destruct (cl + Z.min (bv_unsigned n) (dlo - cl) <? bv_unsigned a + bv_unsigned sz) eqn:Ea;
        destruct (ch <? bv_unsigned a + bv_unsigned sz) eqn:Eb; try reflexivity;
        [apply Z.ltb_lt in Ea; apply Z.ltb_ge in Eb | apply Z.ltb_ge in Ea; apply Z.ltb_lt in Eb]; unfold ch in *; lia.
    + rewrite (iv_subtract_disjoint a sz cl (cl + Z.min (bv_unsigned n) (dlo - cl)) Hpos ltac:(lia) ltac:(lia)).
      symmetry. apply iv_subtract_disjoint; [exact Hpos | exact Hch | lia].
  - (* [comment removed for export] *)
    rewrite (mremap_u64 (Z.max cl dhi)) by lia.
    rewrite (mremap_u64 (ch - Z.max cl dhi)) by (unfold ch in *; lia).
    replace (Z.max cl dhi + (ch - Z.max cl dhi)) with ch by lia.
    destruct Hmiss as [Hlow | Hhigh].
    + rewrite (iv_subtract_disjoint a sz (Z.max cl dhi) ch Hpos ltac:(lia) ltac:(lia)).
      symmetry. apply iv_subtract_disjoint; [exact Hpos | exact Hch | lia].
    + apply iv_subtract_ext.
      * destruct (bv_unsigned a <? Z.max cl dhi) eqn:Ea; destruct (bv_unsigned a <? cl) eqn:Eb; try reflexivity;
          [apply Z.ltb_lt in Ea; apply Z.ltb_ge in Eb | apply Z.ltb_ge in Ea; apply Z.ltb_lt in Eb]; lia.
      * intros Hx. lia.
      * reflexivity.
      * reflexivity.
  - (* [comment removed for export] *)
    symmetry. apply iv_subtract_disjoint; [exact Hpos | exact Hch | lia].
Qed.

Lemma cut_forget_one : forall X (c n : word),
  all_good dlo dhi X ->
  maps_subtract_all X (iv_subtract c n dlo dhi) = maps_subtract X (bv_unsigned c) (bv_unsigned c + bv_unsigned n).
Proof.
  induction X as [|[a sz] X IH]; intros c n HX.
  - cbn [maps_subtract]. apply maps_subtract_all_nil.
  - apply all_good_cons_inv in HX as [Hx HX].
    change ((a, sz) :: X) with ([(a, sz)] ++ X).
    rewrite maps_subtract_all_app. rewrite (cut_forget_entry a sz c n Hx). rewrite (IH c n HX).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem maps_subtract_all_cuts_forget : forall KL X,
  all_good dlo dhi X ->
  maps_subtract_all X (maps_subtract KL dlo dhi) = maps_subtract_all X KL.
Proof.
  induction KL as [|[c n] KL IH]; intros X HX; [reflexivity|].
  cbn [maps_subtract]. rewrite maps_subtract_all_cuts_app.
  rewrite (cut_forget_one X c n HX).
  cbn [maps_subtract_all]. apply IH. apply maps_subtract_good. exact HX.
Qed.

End Forget.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ent_nonempty (x : word * word) : bool := (0 <? bv_unsigned (snd x)).

Lemma live_bytes_drop_empty : forall cuts Y,
  live_bytes (maps_subtract_all Y cuts) = live_bytes (maps_subtract_all (List.filter ent_nonempty Y) cuts).
Proof.
  intros cuts. induction Y as [|[a sz] Y IH]; [reflexivity|].
  assert (F : List.filter ent_nonempty ((a, sz) :: Y)
              = if (0 <? bv_unsigned sz) then (a, sz) :: List.filter ent_nonempty Y else List.filter ent_nonempty Y) by reflexivity.
  rewrite F. clear F.
  change (maps_subtract_all ((a, sz) :: Y) cuts) with (maps_subtract_all ([(a, sz)] ++ Y) cuts).
  rewrite maps_subtract_all_app, live_bytes_app. rewrite IH.
  destruct (0 <? bv_unsigned sz) eqn:E.
  - change (maps_subtract_all ((a, sz) :: List.filter ent_nonempty Y) cuts)
      with (maps_subtract_all ([(a, sz)] ++ List.filter ent_nonempty Y) cuts).
    rewrite maps_subtract_all_app, live_bytes_app. reflexivity.
  - apply Z.ltb_ge in E.
    pose proof (live_bytes_maps_subtract_all_le cuts [(a, sz)]) as H1. cbn [live_bytes] in H1.
    pose proof (live_bytes_nonneg (maps_subtract_all [(a, sz)] cuts)) as H2.
    pose proof (mremap_word_range sz). lia.
Qed.

(* [comment removed for export] *)
Theorem live_bytes_cuts_forget : forall dlo dhi KL X,
  0 <= dlo -> dlo <= dhi -> dhi < two_pow_64 ->
  (forall (b s : word), In (b, s) X ->
     bv_unsigned b + bv_unsigned s <= two_pow_64 /\ (bv_unsigned b + bv_unsigned s <= dlo \/ dhi <= bv_unsigned b)) ->
  live_bytes (maps_subtract_all X (maps_subtract KL dlo dhi)) = live_bytes (maps_subtract_all X KL).
Proof.
  intros dlo dhi KL X H0 H1 H2 HX.
  rewrite (live_bytes_drop_empty (maps_subtract KL dlo dhi) X).
  rewrite (live_bytes_drop_empty KL X).
  assert (G : all_good dlo dhi (List.filter ent_nonempty X)); [| rewrite (maps_subtract_all_cuts_forget dlo dhi H1 H2 KL _ G); reflexivity].
  intros [b s] Hin. apply List.filter_In in Hin as [Hin Hne]. unfold ent_nonempty in Hne. cbn [snd] in Hne.
  apply Z.ltb_lt in Hne. destruct (HX b s Hin) as [Hf Hm].
  split; [exact Hne | split; [exact Hf | exact Hm]].
Qed.
