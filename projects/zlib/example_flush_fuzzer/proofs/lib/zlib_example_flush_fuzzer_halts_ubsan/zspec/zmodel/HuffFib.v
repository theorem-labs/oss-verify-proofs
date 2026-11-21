(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import HuffTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint fib (n : nat) : Z :=
  match n with O => 0 | S n' => match n' with O => 1 | S n'' => fib n' + fib n'' end end.

Lemma fib_SS : forall n, fib (S (S n)) = fib (S n) + fib n.
Proof. intros n. reflexivity. Qed.

Lemma fib_nonneg : forall n, 0 <= fib n /\ 0 <= fib (S n).
Proof. induction n as [|n IH]; [cbn; lia|]. rewrite fib_SS. lia. Qed.

Lemma fib_mono_S : forall n, fib n <= fib (S n).
Proof. intros [|n]; [cbn; lia|]. rewrite fib_SS. pose proof (fib_nonneg n). lia. Qed.

Lemma fib_mono : forall m n, (m <= n)%nat -> fib m <= fib n.
Proof. intros m n H. induction H; [lia|]. pose proof (fib_mono_S m0). lia. Qed.

Definition fibZ (z : Z) : Z := fib (Z.to_nat z).

Lemma fibZ_0 : fibZ 0 = 0. Proof. reflexivity. Qed.
Lemma fibZ_1 : fibZ 1 = 1. Proof. reflexivity. Qed.
Lemma fibZ_2 : fibZ 2 = 1. Proof. reflexivity. Qed.
Lemma fibZ_rec : forall z, 0 <= z -> fibZ (z + 2) = fibZ (z + 1) + fibZ z.
Proof.
  intros z Hz. unfold fibZ. replace (Z.to_nat (z + 2)) with (S (S (Z.to_nat z))) by lia.
  replace (Z.to_nat (z + 1)) with (S (Z.to_nat z)) by lia. apply fib_SS.
Qed.
Lemma fibZ_nonneg : forall z, 0 <= fibZ z.
Proof. intros. unfold fibZ. apply (proj1 (fib_nonneg _)). Qed.
Lemma fibZ_mono : forall a b, a <= b -> fibZ a <= fibZ b.
Proof. intros. unfold fibZ. apply fib_mono. lia. Qed.


Definition fibok (t : htree) : Prop :=
  forall e, In e (hprof 0 t) -> fibZ (ed e + 1) * ew e + fibZ (ed e) <= hw t.

Fixpoint fibher (t : htree) : Prop :=
  fibok t /\ match t with HL _ _ => True | HN l r => fibher l /\ fibher r end.

Lemma fibher_ok : forall t, fibher t -> fibok t.
Proof. intros [| ] H; cbn in H; tauto. Qed.

Lemma hprof_shift : forall d t, hprof d t = map (fun e => E (ew e) (ea e) (ed e + d)) (hprof 0 t).
Proof.
  intros d t. revert d. induction t; intros d; cbn.
  - reflexivity.
  - rewrite (IHt1 (d + 1)), (IHt2 (d + 1)), (IHt1 1), (IHt2 1), !map_app, !map_map. cbn.
    f_equal; apply map_ext; intros e; f_equal; lia.
Qed.

Lemma in_hprof1 : forall t e, In e (hprof 1 t) -> exists e0, In e0 (hprof 0 t) /\ ew e = ew e0 /\ ed e = ed e0 + 1.
Proof.
  intros t e Hin. rewrite hprof_shift in Hin. apply in_map_iff in Hin. destruct Hin as (e0 & <- & Hin).
  exists e0. cbn. auto.
Qed.

Definition finv (b : Z) (F : list htree) : Prop :=
  forall t, In t F ->
    hwmin 1 t /\ b <= hw t /\ fibher t /\ match t with HL _ _ => True | HN l r => hw l <= b /\ hw r <= b end.

Lemma finv_perm : forall b F F', Permutation F F' -> finv b F -> finv b F'.
Proof. intros b F F' P I t Ht. apply I. apply (Permutation_in _ (Permutation_sym P)). exact Ht. Qed.

Lemma fibok_merge : forall b t1 t2,
  hwmin 1 t1 -> hwmin 1 t2 -> fibher t1 -> fibher t2 ->
  match t1 with HL _ _ => True | HN l r => hw l <= b /\ hw r <= b end ->
  match t2 with HL _ _ => True | HN l r => hw l <= b /\ hw r <= b end ->
  b <= hw t1 -> b <= hw t2 ->
  fibok (HN t1 t2).
Proof.
  intros b t1 t2 M1 M2 F1 F2 C1 C2 B1 B2 e Hin. cbn [hprof hw] in Hin |- *. rewrite Z.add_0_l in Hin.
  pose proof (hwmin_hw 1 t1 ltac:(lia) M1) as W1. pose proof (hwmin_hw 1 t2 ltac:(lia) M2) as W2.
  assert (G : forall u v, hwmin 1 u -> fibher u ->
             match u with HL _ _ => True | HN l r => hw l <= b /\ hw r <= b end ->
             b <= hw v -> 1 <= hw v ->
             forall e, In e (hprof 1 u) -> fibZ (ed e + 1) * ew e + fibZ (ed e) <= hw u + hw v).
  { clear. intros u v Mu Fu Cu Bv Wv e Hin.
    destruct (in_hprof1 u e Hin) as (e0 & Hin0 & We & De).
    pose proof (fibher_ok u Fu e0 Hin0) as K0.
    pose proof (hprof_dep 0 u e0 Hin0) as D0.
    destruct u as [w a|l r].
    - cbn in Hin0. destruct Hin0 as [<-|[]]. cbn in *. rewrite De, We. change (fibZ 2 * w + fibZ 1 <= w + hw v). rewrite fibZ_2, fibZ_1. lia.
    -
      cbn [hprof] in Hin0. rewrite Z.add_0_l in Hin0. apply in_app_iff in Hin0.
      cbn [fibher] in Fu. destruct Fu as (_ & Fl & Fr). destruct Cu as [Cl Cr].
      cbn [hwmin] in Mu. destruct Mu as [Ml Mr].
      assert (K1 : exists c, hw c <= b /\ hwmin 1 c /\ exists e1, In e1 (hprof 0 c) /\ ew e0 = ew e1 /\ ed e0 = ed e1 + 1 /\ fibok c).
      { destruct Hin0 as [Hin0|Hin0].
        + exists l. split; [exact Cl|]. split; [exact Ml|]. destruct (in_hprof1 l e0 Hin0) as (e1 & A1 & A2 & A3). exists e1. repeat split; auto. apply fibher_ok, Fl.
        + exists r. split; [exact Cr|]. split; [exact Mr|]. destruct (in_hprof1 r e0 Hin0) as (e1 & A1 & A2 & A3). exists e1. repeat split; auto. apply fibher_ok, Fr. }
      destruct K1 as (c & Hc & Mc & e1 & Hin1 & We1 & De1 & Kc).
      specialize (Kc e1 Hin1). pose proof (hprof_dep 0 c e1 Hin1) as D1.
      rewrite De, We, De1, We1 in *.
      replace (ed e1 + 1 + 1 + 1) with ((ed e1 + 1) + 2) by lia.
      rewrite fibZ_rec by lia. replace (ed e1 + 1 + 1) with (ed e1 + 2) in * by lia. rewrite fibZ_rec in * by lia.
      pose proof (fibZ_nonneg (ed e1)). pose proof (fibZ_nonneg (ed e1 + 1)).
      assert (0 <= ew e1). { pose proof (hwmin_prof 1 0 c e1 Mc Hin1). lia. }
      nia. }
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - apply (G t1 t2); auto; lia.
  - rewrite (Z.add_comm (hw t1) (hw t2)). apply (G t2 t1); auto; lia.
Qed.

Lemma finv_step : forall b F F', finv b F -> hstep F F' -> exists b', finv b' F'.
Proof.
  intros b F F' I HS. destruct HS as [F t1 t2 R PF Hmin].
  apply (finv_perm _ _ _ PF) in I.
  destruct (I t1 ltac:(cbn; auto)) as (M1 & B1 & F1 & C1).
  destruct (I t2 ltac:(cbn; auto)) as (M2 & B2 & F2 & C2).
  exists (Z.max (hw t1) (hw t2)). intros t [<-|Ht].
  - split; [cbn; auto|]. pose proof (hwmin_hw 1 t1 ltac:(lia) M1). pose proof (hwmin_hw 1 t2 ltac:(lia) M2).
    split; [cbn; lia|]. split; [|lia].
    cbn [fibher]. split; [|auto]. eapply (fibok_merge b); eauto.
  - destruct (I t ltac:(cbn; auto)) as (Mt & Bt & Ft & Ct). specialize (Hmin t Ht).
    split; [exact Mt|]. split; [lia|]. split; [exact Ft|]. destruct t; [exact Logic.I|]. lia.
Qed.

Lemma finv_leaves : forall F, leaf_forest F -> (forall t, In t F -> 1 <= hw t) -> finv 0 F.
Proof.
  intros F HL HW t Ht. specialize (HL t Ht). specialize (HW t Ht). destruct t as [w a|]; [|destruct HL].
  cbn in *. split; [lia|]. split; [lia|]. split; [|exact I]. split; [|exact I].
  intros e [<-|[]]. change (fibZ 1 * w + fibZ 0 <= w). rewrite fibZ_1, fibZ_0. lia.
Qed.


Theorem hbuild_fib : forall F T, hbuild F T -> leaf_forest F -> (forall t, In t F -> 1 <= hw t) ->
  forall e, In e (hprof 0 T) -> fibZ (ed e + 1) * ew e + fibZ (ed e) <= hw T.
Proof.
  intros F T HB HL HW.
  assert (G : forall b, finv b F -> fibok T).
  { clear HL HW. induction HB as [T|F F' T HS HB IH]; intros b I.
    - apply fibher_ok. apply (I T). now left.
    - destruct (finv_step b F F' I HS) as (b' & I'). exact (IH b' I'). }
  exact (G 0 (finv_leaves F HL HW)).
Qed.

Theorem hbuild_depth_bound : forall F T h, hbuild F T -> leaf_forest F -> (forall t, In t F -> 1 <= hw t) ->
  hw T < fibZ (h + 3) -> forall e, In e (hprof 0 T) -> ed e <= h.
Proof.
  intros F T h HB HL HW Hh e He.
  pose proof (hbuild_fib F T HB HL HW e He) as B.
  pose proof (hprof_dep 0 T e He) as D.
  assert (W : 1 <= ew e).
  { pose proof (Permutation_in (ew e) (hbuild_leaves_w F T HB HL) ltac:(apply in_map; exact He)) as Hin.
    apply in_map_iff in Hin. destruct Hin as (t & <- & Ht). apply HW, Ht. }
  destruct (Z_le_gt_dec (ed e) h); [assumption|]. exfalso.
  assert (fibZ (h + 3) <= fibZ (ed e + 2)) by (apply fibZ_mono; lia).
  rewrite fibZ_rec in H by lia. pose proof (fibZ_nonneg (ed e + 1)). nia.
Qed.

Lemma hheight_attained : forall d t, exists e, In e (hprof d t) /\ ed e = d + hheight t.
Proof.
  intros d t. revert d. induction t; intros d; cbn.
  - exists (E w a d). split; [now left| cbn; lia].
  - destruct (Z_le_gt_dec (hheight t2) (hheight t1)).
    + destruct (IHt1 (d + 1)) as (e & He & De). exists e. split; [apply in_app_iff; now left| lia].
    + destruct (IHt2 (d + 1)) as (e & He & De). exists e. split; [apply in_app_iff; now right| lia].
Qed.


