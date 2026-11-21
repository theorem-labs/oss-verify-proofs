(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Definition aeq (a b : arr) : Prop := arr_len a = arr_len b /\ forall i, arr_get a i = arr_get b i.

Lemma aeq_len : forall a b, aeq a b -> arr_len a = arr_len b.
Proof. intros a b [L _]. exact L. Qed.
Lemma aeq_get : forall a b i, aeq a b -> arr_get a i = arr_get b i.
Proof. intros a b i [_ G]. apply G. Qed.
Lemma aeq_inb : forall a b i, aeq a b -> arr_inb a i = arr_inb b i.
Proof. intros a b i [L _]. unfold arr_inb. rewrite L. reflexivity. Qed.
Lemma aeq_set : forall a b i v, aeq a b -> aeq (arr_set a i v) (arr_set b i v).
Proof.
  intros a b i v H. split.
  - rewrite !arr_len_set. apply aeq_len. exact H.
  - intros j. rewrite !arr_get_set, (aeq_inb a b i H), (aeq_get a b j H). reflexivity.
Qed.
Lemma aeq_init_get : forall n (a : arr), arr_len a = n -> aeq a (arr_init n (arr_get a)).
Proof. intros n a H. split; [rewrite arr_len_init; exact H | intros i; rewrite arr_get_init; reflexivity]. Qed.

Ltac csplit := repeat match goal with |- _ /\ _ => split end.
Ltac fin_rel := cbv beta iota delta [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work fst snd];
                csplit; first [reflexivity | assumption | apply aeq_set; assumption].

Section Iter.
  Context {A B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop).
  Variables (step1 step2 : A -> A + B) (dflt1 dflt2 : A -> B).
  Hypothesis Hstep : forall x y, RA x y ->
    match step1 x, step2 y with
    | inl x', inl y' => RA x' y'
    | inr b, inr b' => RB b b'
    | _, _ => False
    end.
  Hypothesis Hdflt : forall x y, RA x y -> RB (dflt1 x) (dflt2 y).

  Lemma iterK_nat_rel : forall n x y, RA x y ->
    match iterK_nat n step1 x, iterK_nat n step2 y with
    | inl x', inl y' => RA x' y'
    | inr b, inr b' => RB b b'
    | _, _ => False
    end.
  Proof.
    induction n as [|n IH]; intros x y H; cbn [iterK_nat]; [exact H|].
    pose proof (Hstep x y H) as S. destruct (step1 x) as [x'|b]; destruct (step2 y) as [y'|b']; try contradiction.
    - apply IH. exact S.
    - exact S.
  Qed.

  Lemma iterZ_rel : forall n x y, RA x y -> RB (iterZ n step1 dflt1 x) (iterZ n step2 dflt2 y).
  Proof.
    intros n x y H. rewrite !iterZ_nat. pose proof (iterK_nat_rel (Z.to_nat n) x y H) as K.
    destruct (iterK_nat _ step1 x) as [x'|b]; destruct (iterK_nat _ step2 y) as [y'|b']; try contradiction.
    - apply Hdflt. exact K.
    - exact K.
  Qed.
End Iter.

Lemma loopZ_rel : forall {A} (R : A -> A -> Prop) n (step1 step2 : A -> bool * A) x y,
  (forall x y, R x y -> fst (step1 x) = fst (step2 y) /\ R (snd (step1 x)) (snd (step2 y))) ->
  R x y -> R (loopZ n step1 x) (loopZ n step2 y).
Proof.
  intros A R n step1 step2 x y Hs H. unfold loopZ.
  apply (iterZ_rel R R); [| intros; assumption | exact H].
  intros a b Hab. pose proof (Hs a b Hab) as [E S].
  destruct (step1 a) as [c a'], (step2 b) as [c' b']. simpl in E, S. subst c'. destruct c; exact S.
Qed.

Lemma forZ_rel : forall {A} (R : A -> A -> Prop) lo hi (body1 body2 : Z -> A -> A) x y,
  (forall i a b, R a b -> R (body1 i a) (body2 i b)) ->
  R x y -> R (forZ lo hi body1 x) (forZ lo hi body2 y).
Proof.
  intros A R lo hi body1 body2 x y Hb H. unfold forZ.
  set (R2 := fun p q : Z * A => fst p = fst q /\ R (snd p) (snd q)).
  assert (K : R2 (loopZ (hi - lo) (fun ia : Z * A => let '(i, a) := ia in if i <? hi then (true, (i + 1, body1 i a)) else (false, (i, a))) (lo, x))
                 (loopZ (hi - lo) (fun ia : Z * A => let '(i, a) := ia in if i <? hi then (true, (i + 1, body2 i a)) else (false, (i, a))) (lo, y))).
  { apply loopZ_rel; [| split; [reflexivity | exact H]].
    intros [i a] [j b] [E S]. unfold R2. simpl in E, S |- *. subst j.
    destruct (i <? hi); simpl; repeat split; try reflexivity; first [apply Hb; exact S | exact S]. }
  exact (proj2 K).
Qed.

Lemma forZ_ext : forall {A} lo hi (body1 body2 : Z -> A -> A) x,
  (forall i a, body1 i a = body2 i a) -> forZ lo hi body1 x = forZ lo hi body2 x.
Proof.
  intros A lo hi body1 body2 x Hb. apply (forZ_rel eq); [| reflexivity]. intros i a b ->. apply Hb.
Qed.

Lemma it_count_aeq : forall lens lens' ofs codes count, aeq lens lens' ->
  it_count lens ofs codes count = it_count lens' ofs codes count.
Proof.
  intros lens lens' ofs codes count H. unfold it_count. apply forZ_ext.
  intros sym cnt. cbv beta. rewrite (aeq_get lens lens' _ H). reflexivity.
Qed.

Lemma it_sort_aeq : forall lens lens' ofs codes offs work work', aeq lens lens' -> aeq work work' ->
  fst (it_sort lens ofs codes (offs, work)) = fst (it_sort lens' ofs codes (offs, work'))
  /\ aeq (snd (it_sort lens ofs codes (offs, work))) (snd (it_sort lens' ofs codes (offs, work'))).
Proof.
  intros lens lens' ofs codes offs work work' HL HW. unfold it_sort.
  match goal with |- fst (forZ _ _ ?b1 _) = fst (forZ _ _ ?b2 _) /\ _ =>
    apply (forZ_rel (fun p q : arr * arr => fst p = fst q /\ aeq (snd p) (snd q)) 0 codes b1 b2) end.
  - intros sym [o1 w1] [o2 w2] [E S]. cbn [fst snd] in E, S |- *. subst o2.
    rewrite (aeq_get lens lens' _ HL). destruct (negb _); cbn [fst snd]; [| split; [reflexivity | exact S]].
    split; [reflexivity | apply aeq_set; exact S].
  - split; [reflexivity | exact HW].
Qed.

Lemma it_base_aeq : forall ty w w' i, aeq w w' -> it_base ty w i = it_base ty w' i.
Proof. intros ty w w' i H. unfold it_base. destruct ty; try reflexivity. apply aeq_get. exact H. Qed.
Lemma it_extra_aeq : forall ty w w' i, aeq w w' -> it_extra ty w i = it_extra ty w' i.
Proof. intros ty w w' i H. unfold it_extra. destruct ty; try reflexivity. apply aeq_get. exact H. Qed.

Lemma it_fill_aeq : forall here incr huff drop next fill t t', aeq t t' ->
  aeq (it_fill here incr huff drop next fill t) (it_fill here incr huff drop next fill t').
Proof.
  intros here incr huff drop next fill t t' H. unfold it_fill.
  match goal with |- aeq (snd (loopZ _ ?s1 _)) (snd (loopZ _ ?s2 _)) =>
    apply (proj2 (A := fst (loopZ fill s1 (fill, t)) = fst (loopZ fill s2 (fill, t'))));
    apply (loopZ_rel (fun p q : Z * arr => fst p = fst q /\ aeq (snd p) (snd q))) end.
  - intros [f1 t1] [f2 t2] [E S]. cbn [fst snd] in E, S |- *. subst f2.
    destruct (negb _); cbn [fst snd]; (split; [reflexivity|]); (split; [reflexivity | apply aeq_set; exact S]).
  - split; [reflexivity | exact H].
Qed.

Definition xrel (x x' : ItCtx) : Prop :=
  x_ty x' = x_ty x /\ aeq (x_lens x) (x_lens x') /\ x_lens_ofs x' = x_lens_ofs x /\ x_table x' = x_table x
  /\ x_root x' = x_root x /\ x_max x' = x_max x /\ x_mask x' = x_mask x.
Definition strel (s s' : ItSt) : Prop :=
  t_huff s' = t_huff s /\ t_sym s' = t_sym s /\ t_len s' = t_len s /\ t_next s' = t_next s /\ t_curr s' = t_curr s
  /\ t_drop s' = t_drop s /\ t_low s' = t_low s /\ t_used s' = t_used s /\ t_min s' = t_min s /\ t_count s' = t_count s
  /\ aeq (t_tbl s) (t_tbl s') /\ aeq (t_work s) (t_work s').

Lemma it_step_rel : forall x x' s s', xrel x x' -> strel s s' ->
  match it_step x s, it_step x' s' with
  | ItCont a, ItCont b | ItBreak a, ItBreak b | ItFail a, ItFail b => strel a b
  | _, _ => False
  end.
Proof.
  intros x x' s s' (Xty & Xl & Xo & Xt & Xr & Xm & Xk) (Sh & Ss & Sl & Sn & Sc & Sd & Sw & Su & Si & Sct & St & Swk).
  unfold it_step.
  rewrite ?Xty, ?Xo, ?Xt, ?Xr, ?Xm, ?Xk, ?Sh, ?Ss, ?Sl, ?Sn, ?Sc, ?Sd, ?Sw, ?Su, ?Si, ?Sct.
  rewrite <- (aeq_get _ _ (t_sym s) Swk).
  rewrite <- (it_extra_aeq (x_ty x) _ _ (arr_get (t_work s) (t_sym s) - it_match (x_ty x)) Swk).
  rewrite <- (it_base_aeq (x_ty x) _ _ (arr_get (t_work s) (t_sym s) - it_match (x_ty x)) Swk).
  rewrite <- (aeq_get _ _ (wrap32 (t_sym s + 1)) Swk).
  rewrite <- (aeq_get (x_lens x) (x_lens x') _ Xl).
  destruct (if arr_get (t_work s) (t_sym s) + 1 <? it_match (x_ty x) then _ else _) as [hop hval].
  set (TB := it_fill _ _ _ _ _ _ (t_tbl s)). set (TB' := it_fill _ _ _ _ _ _ (t_tbl s')).
  assert (ATB : aeq TB TB') by (subst TB TB'; apply it_fill_aeq; exact St).
  clearbody TB TB'. unfold strel.
  destruct ((wrap16 (arr_get (t_count s) (t_len s) - 1) =? 0) && (t_len s =? x_max x)); [fin_rel|].
  destruct ((x_root x <? _) && negb _); [| fin_rel].
  destruct (it_not_enough _ _); fin_rel.
Qed.

Lemma it_loop_rel : forall x x' codes s s', xrel x x' -> strel s s' ->
  match it_loop x codes s, it_loop x' codes s' with
  | inl a, inl b | inr a, inr b => strel a b
  | _, _ => False
  end.
Proof.
  intros x x' codes s s' HX HS. unfold it_loop.
  apply (iterZ_rel strel (fun u v : ItSt + ItSt => match u, v with inl a, inl b | inr a, inr b => strel a b | _, _ => False end)).
  - intros a b Hab. pose proof (it_step_rel x x' a b HX Hab) as K.
    destruct (it_step x a); destruct (it_step x' b); try contradiction; exact K.
  - intros a b Hab. exact Hab.
  - exact HS.
Qed.

Theorem inflate_table_aeq : forall ty lens lens' ofs codes tbl tbl' table bits work work',
  aeq lens lens' -> aeq tbl tbl' -> aeq work work' ->
  let '(r, t, n, b, w) := inflate_table ty lens ofs codes tbl table bits work in
  let '(r', t', n', b', w') := inflate_table ty lens' ofs codes tbl' table bits work' in
  r' = r /\ n' = n /\ b' = b /\ aeq t t' /\ aeq w w'.
Proof.
  intros ty lens lens' ofs codes tbl tbl' table bits work work' HL HT HW.
  unfold inflate_table.
  rewrite <- (it_count_aeq lens lens' ofs codes _ HL).
  set (count := it_count lens ofs codes _).
  destruct (it_find_max count =? 0).
  { cbv beta iota delta [fst snd]. csplit; try reflexivity; [do 2 apply aeq_set; exact HT | exact HW]. }
  destruct (it_left_check count) as [lft|]; [| csplit; try reflexivity; assumption].
  destruct ((0 <? lft) && _); [csplit; try reflexivity; assumption|].
  pose proof (it_sort_aeq lens lens' ofs codes (it_offs count (arr_make 16 0)) work work' HL HW) as [_ SW].
  destruct (it_sort lens ofs codes _) as [o1 w1]. destruct (it_sort lens' ofs codes _) as [o2 w2]. cbn [fst snd] in SW.
  destruct (it_not_enough ty _); [csplit; try reflexivity; assumption|].
  match goal with |- context [it_loop (mkItCtx ty lens ?o ?tb ?r ?m ?k) codes ?s] =>
    match goal with |- context [it_loop (mkItCtx ty lens' o tb r m k) codes ?s'] =>
      pose proof (it_loop_rel (mkItCtx ty lens o tb r m k) (mkItCtx ty lens' o tb r m k) codes s s') as K end end.
  lazymatch type of K with ?P -> ?Q -> _ =>
    assert (HX : P) by (unfold xrel; cbn [x_ty x_lens x_lens_ofs x_table x_root x_max x_mask]; csplit; try reflexivity; exact HL);
    assert (HS : Q) by (unfold strel; cbn [t_huff t_sym t_len t_next t_curr t_drop t_low t_used t_min t_count t_tbl t_work]; csplit; try reflexivity; assumption) end.
  specialize (K HX HS).
  destruct (it_loop _ codes _) as [a|a]; destruct (it_loop _ codes _) as [b|b]; try contradiction;
    destruct K as (Kh & Ks & Kl & Kn & Kc & Kd & Kw & Ku & Ki & Kct & Kt & Kwk).
  - rewrite Kh, Kn, Kl, Kd, Ku. destruct (negb (t_huff a =? 0)); csplit; try reflexivity; try assumption.
    apply aeq_set. exact Kt.
  - csplit; try reflexivity; assumption.
Qed.
