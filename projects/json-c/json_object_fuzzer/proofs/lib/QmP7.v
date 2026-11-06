(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh QKTr QDw3 QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QKTr.
Import QDw3 QNwL.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma list_set_length {A} : forall (l : list A) i v, length (list_set l i v) = length l.
Proof. induction l; intros [|i] v; cbn; auto. Qed.

Lemma nth_error_list_set_eq {A} : forall (l : list A) i v, (i < length l)%nat -> nth_error (list_set l i v) i = Some v.
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. all: apply IHl; lia. Qed.

Lemma nth_error_list_set_ne {A} : forall (l : list A) i j v, i <> j -> nth_error (list_set l i v) j = nth_error l j.
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.

Lemma tag_at_Some_lt : forall G c i t, tag_at G c i = Some t -> 0 <= i < ncarved G c.
Proof.
intros G c i t H. unfold tag_at, ncarved in *. destruct (Z.ltb_spec i 0); [discriminate|].
assert (Z.to_nat i < length (G c))%nat by (apply nth_error_Some; rewrite H; discriminate). lia.
Qed.

Lemma tag_at_None_ge : forall G c i, ncarved G c <= i -> tag_at G c i = None.
Proof.
intros G c i H. unfold tag_at, ncarved in *. destruct (Z.ltb_spec i 0); [reflexivity|].
apply nth_error_None. lia.
Qed.

Lemma gset_eq : forall c l G, gset c l G c = l.
Proof. intros. unfold gset. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma gset_ne : forall c c' l G, c' <> c -> gset c l G c' = G c'.
Proof. intros c c' l G H. unfold gset. destruct (Z.eqb_spec c' c); [lia| reflexivity]. Qed.

Lemma set_tag_other_class : forall c i t G c', c' <> c -> set_tag c i t G c' = G c'.
Proof. intros. unfold set_tag. apply gset_ne. assumption. Qed.
Lemma set_tag_class : forall c i t G, set_tag c i t G c = list_set (G c) (Z.to_nat i) t.
Proof. intros. unfold set_tag. apply gset_eq. Qed.

Lemma ncarved_set_tag : forall c i t G c', ncarved (set_tag c i t G) c' = ncarved G c'.
Proof.
intros. unfold ncarved. destruct (Z.eq_dec c' c) as [->|NE].
- rewrite set_tag_class, list_set_length. reflexivity.
- rewrite set_tag_other_class by exact NE. reflexivity.
Qed.

Lemma same_len_set_tag : forall c i t G, same_len G (set_tag c i t G).
Proof. intros c i t G c'. pose proof (ncarved_set_tag c i t G c') as H. unfold ncarved in H. lia. Qed.

Lemma tag_at_set_tag_eq : forall G c i t t0, tag_at G c i = Some t0 -> tag_at (set_tag c i t G) c i = Some t.
Proof.
intros G c i t t0 H. pose proof (tag_at_Some_lt _ _ _ _ H) as [I1 I2]. unfold ncarved in I2.
unfold tag_at in *. destruct (Z.ltb_spec i 0); [lia|]. rewrite set_tag_class. apply nth_error_list_set_eq. lia.
Qed.

Lemma tag_at_set_tag_ne : forall G c i t c' i', 0 <= i -> (c' <> c \/ i' <> i) -> tag_at (set_tag c i t G) c' i' = tag_at G c' i'.
Proof.
intros G c i t c' i' Hi H. unfold tag_at. destruct (Z.ltb_spec i' 0); [reflexivity|].
destruct (Z.eq_dec c' c) as [->|NE].
- rewrite set_tag_class. destruct H as [H|H]; [lia|]. apply nth_error_list_set_ne. lia.
- rewrite set_tag_other_class by exact NE. reflexivity.
Qed.

Lemma same_tags_set_tag : forall f G c i t t0,
tag_at G c i = Some t0 -> f t0 = false -> f t = false -> same_tags f G (set_tag c i t G).
Proof.
intros f G c i t t0 Ht F0 F1 c' i' t' Hf. pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I1 _].
destruct (Z.eq_dec c' c) as [->|NE]; [destruct (Z.eq_dec i' i) as [->|NI]|].
- rewrite (tag_at_set_tag_eq _ _ _ t _ Ht), Ht. split; intros E; inversion E; subst; congruence.
- rewrite tag_at_set_tag_ne by lia. tauto.
- rewrite tag_at_set_tag_ne by lia. tauto.
Qed.

Lemma count_tag_cons : forall f t l, count_tag f (t :: l) = (if f t then 1 else 0) + count_tag f l.
Proof.
intros f t l. unfold count_tag. rewrite list.filter_cons. destruct (decide (f t)) as [Y|N]; destruct (f t);
[| destruct Y | exfalso; apply N; exact I |]; cbn [length]; lia.
Qed.
Lemma count_tag_app : forall f l1 l2, count_tag f (l1 ++ l2) = count_tag f l1 + count_tag f l2.
Proof. intros f l1 l2. unfold count_tag. rewrite list.filter_app, length_app. lia. Qed.
Lemma count_tag_repeat : forall f t n, count_tag f (repeat t n) = if f t then Z.of_nat n else 0.
Proof.
intros f t n. induction n as [|n IH]; [cbn; destruct (f t); reflexivity|].
cbn [repeat]. rewrite count_tag_cons, IH. destruct (f t); lia.
Qed.

Lemma count_tag_list_set : forall f l i t t0,
nth_error l i = Some t0 -> count_tag f (list_set l i t) = count_tag f l - (if f t0 then 1 else 0) + (if f t then 1 else 0).
Proof.
induction l as [|x l IH]; intros [|i] t t0 H; cbn in H; try discriminate.
- inversion H; subst. cbn [list_set]. rewrite !count_tag_cons. lia.
- cbn [list_set]. rewrite !count_tag_cons, (IH i t t0 H). lia.
Qed.

Lemma count_tag_set_tag : forall f G c i t t0,
tag_at G c i = Some t0 ->
count_tag f (set_tag c i t G c) = count_tag f (G c) - (if f t0 then 1 else 0) + (if f t then 1 else 0).
Proof.
intros f G c i t t0 H. rewrite set_tag_class. apply count_tag_list_set.
unfold tag_at in H. destruct (Z.ltb_spec i 0); [discriminate| exact H].
Qed.

Lemma count_tag_ext : forall f l l',
length l = length l' -> (forall i t, f t = true -> (nth_error l i = Some t <-> nth_error l' i = Some t)) ->
count_tag f l = count_tag f l'.
Proof.
induction l as [|x l IH]; intros [|y l'] L E; cbn in L; [reflexivity| lia| lia|].
rewrite !count_tag_cons. rewrite (IH l'); [| lia|].
- destruct (f x) eqn:FX; destruct (f y) eqn:FY; try lia.
+ pose proof (proj1 (E 0%nat x FX) eq_refl) as K. cbn in K. inversion K; subst. congruence.
+ pose proof (proj2 (E 0%nat y FY) eq_refl) as K. cbn in K. inversion K; subst. congruence.
- intros i t Ft. exact (E (S i) t Ft).
Qed.

Lemma count_tag_same : forall f G G' c, same_len G G' -> same_tags f G G' -> count_tag f (G c) = count_tag f (G' c).
Proof.
intros f G G' c SL ST. apply count_tag_ext; [apply SL|]. intros i t Ft.
specialize (ST c (Z.of_nat i) t Ft). unfold tag_at in ST. destruct (Z.ltb_spec (Z.of_nat i) 0); [lia|].
rewrite Nat2Z.id in ST. exact ST.
Qed.

Definition gappend (c : Z) (l : list stag) (G : ghost) : ghost := gset c (G c ++ l) G.

Lemma tag_at_gappend_old : forall G c l c' i, i < ncarved G c' -> tag_at (gappend c l G) c' i = tag_at G c' i.
Proof.
intros G c l c' i Hi. unfold tag_at, gappend, ncarved in *. destruct (Z.ltb_spec i 0); [reflexivity|].
destruct (Z.eq_dec c' c) as [->|NE]; [rewrite gset_eq| rewrite gset_ne by exact NE; reflexivity].
apply nth_error_app1. lia.
Qed.

Lemma tag_at_gappend_new : forall G c l i, ncarved G c <= i -> tag_at (gappend c l G) c i = nth_error l (Z.to_nat (i - ncarved G c)).
Proof.
intros G c l i Hi. pose proof Hi as Hi'. unfold tag_at, gappend, ncarved in *. destruct (Z.ltb_spec i 0); [lia|].
rewrite gset_eq, nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma tag_at_gappend_Some_old : forall G c l c' i t, tag_at G c' i = Some t -> tag_at (gappend c l G) c' i = Some t.
Proof. intros G c l c' i t H. rewrite tag_at_gappend_old; [exact H|]. exact (proj2 (tag_at_Some_lt _ _ _ _ H)). Qed.

Lemma ncarved_gappend : forall G c l c', ncarved (gappend c l G) c' = ncarved G c' + (if c' =? c then Z.of_nat (length l) else 0).
Proof.
intros G c l c'. unfold ncarved, gappend. destruct (Z.eqb_spec c' c) as [->|NE].
- rewrite gset_eq, length_app. lia.
- rewrite gset_ne by exact NE. lia.
Qed.

Lemma gappend_other_class : forall G c l c', c' <> c -> gappend c l G c' = G c'.
Proof. intros. unfold gappend. apply gset_ne. assumption. Qed.
Lemma gappend_class : forall G c l, gappend c l G c = G c ++ l.
Proof. intros. unfold gappend. apply gset_eq. Qed.

Lemma same_tags_gappend : forall f G c l, Forall (fun t => f t = false) l -> same_tags f G (gappend c l G).
Proof.
intros f G c l Hl c' i t Ft. destruct (Z.lt_ge_cases i (ncarved G c')) as [LT|GE].
- rewrite tag_at_gappend_old by exact LT. tauto.
- rewrite (tag_at_None_ge G c' i GE). destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite tag_at_gappend_new by exact GE. split; [discriminate|]. intros H.
apply nth_error_In in H. exfalso. pose proof (proj1 (Forall_forall _ _) Hl t H) as K. cbn in K. congruence.
+ unfold tag_at, gappend. destruct (Z.ltb_spec i 0); [tauto|]. rewrite gset_ne by exact NE.
rewrite (proj2 (nth_error_None _ _)); [tauto|]. unfold ncarved in GE. lia.
Qed.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Q6sh QKTr.
Import QWRO QFQR.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Lemma list_set_length {A} : forall (l : list A) i v, length (list_set l i v) = length l.
Proof. induction l; intros [|i] v; cbn; auto. Qed.

Lemma nth_error_list_set_eq {A} : forall (l : list A) i v, (i < length l)%nat -> nth_error (list_set l i v) i = Some v.
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. all: apply IHl; lia. Qed.

Lemma nth_error_list_set_ne {A} : forall (l : list A) i j v, i <> j -> nth_error (list_set l i v) j = nth_error l j.
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.

Lemma tag_at_Some_lt : forall G c i t, tag_at G c i = Some t -> 0 <= i < ncarved G c.
Proof.
intros G c i t H. unfold tag_at, ncarved in *. destruct (Z.ltb_spec i 0); [discriminate|].
assert (Z.to_nat i < length (G c))%nat by (apply nth_error_Some; rewrite H; discriminate). lia.
Qed.

Lemma tag_at_None_ge : forall G c i, ncarved G c <= i -> tag_at G c i = None.
Proof.
intros G c i H. unfold tag_at, ncarved in *. destruct (Z.ltb_spec i 0); [reflexivity|].
apply nth_error_None. lia.
Qed.

Lemma gset_eq : forall c l G, gset c l G c = l.
Proof. intros. unfold gset. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma gset_ne : forall c c' l G, c' <> c -> gset c l G c' = G c'.
Proof. intros c c' l G H. unfold gset. destruct (Z.eqb_spec c' c); [lia| reflexivity]. Qed.

Lemma set_tag_other_class : forall c i t G c', c' <> c -> set_tag c i t G c' = G c'.
Proof. intros. unfold set_tag. apply gset_ne. assumption. Qed.
Lemma set_tag_class : forall c i t G, set_tag c i t G c = list_set (G c) (Z.to_nat i) t.
Proof. intros. unfold set_tag. apply gset_eq. Qed.

Lemma ncarved_set_tag : forall c i t G c', ncarved (set_tag c i t G) c' = ncarved G c'.
Proof.
intros. unfold ncarved. destruct (Z.eq_dec c' c) as [->|NE].
- rewrite set_tag_class, list_set_length. reflexivity.
- rewrite set_tag_other_class by exact NE. reflexivity.
Qed.

Lemma same_len_set_tag : forall c i t G, same_len G (set_tag c i t G).
Proof. intros c i t G c'. pose proof (ncarved_set_tag c i t G c') as H. unfold ncarved in H. lia. Qed.

Lemma tag_at_set_tag_eq : forall G c i t t0, tag_at G c i = Some t0 -> tag_at (set_tag c i t G) c i = Some t.
Proof.
intros G c i t t0 H. pose proof (tag_at_Some_lt _ _ _ _ H) as [I1 I2]. unfold ncarved in I2.
unfold tag_at in *. destruct (Z.ltb_spec i 0); [lia|]. rewrite set_tag_class. apply nth_error_list_set_eq. lia.
Qed.

Lemma tag_at_set_tag_ne : forall G c i t c' i', 0 <= i -> (c' <> c \/ i' <> i) -> tag_at (set_tag c i t G) c' i' = tag_at G c' i'.
Proof.
intros G c i t c' i' Hi H. unfold tag_at. destruct (Z.ltb_spec i' 0); [reflexivity|].
destruct (Z.eq_dec c' c) as [->|NE].
- rewrite set_tag_class. destruct H as [H|H]; [lia|]. apply nth_error_list_set_ne. lia.
- rewrite set_tag_other_class by exact NE. reflexivity.
Qed.

Lemma same_tags_set_tag : forall f G c i t t0,
tag_at G c i = Some t0 -> f t0 = false -> f t = false -> same_tags f G (set_tag c i t G).
Proof.
intros f G c i t t0 Ht F0 F1 c' i' t' Hf. pose proof (tag_at_Some_lt _ _ _ _ Ht) as [I1 _].
destruct (Z.eq_dec c' c) as [->|NE]; [destruct (Z.eq_dec i' i) as [->|NI]|].
- rewrite (tag_at_set_tag_eq _ _ _ t _ Ht), Ht. split; intros E; inversion E; subst; congruence.
- rewrite tag_at_set_tag_ne by lia. tauto.
- rewrite tag_at_set_tag_ne by lia. tauto.
Qed.

Lemma count_tag_cons : forall f t l, count_tag f (t :: l) = (if f t then 1 else 0) + count_tag f l.
Proof.
intros f t l. unfold count_tag. rewrite list.filter_cons. destruct (decide (f t)) as [Y|N]; destruct (f t);
[| destruct Y | exfalso; apply N; exact I |]; cbn [length]; lia.
Qed.
Lemma count_tag_app : forall f l1 l2, count_tag f (l1 ++ l2) = count_tag f l1 + count_tag f l2.
Proof. intros f l1 l2. unfold count_tag. rewrite list.filter_app, length_app. lia. Qed.
Lemma count_tag_repeat : forall f t n, count_tag f (repeat t n) = if f t then Z.of_nat n else 0.
Proof.
intros f t n. induction n as [|n IH]; [cbn; destruct (f t); reflexivity|].
cbn [repeat]. rewrite count_tag_cons, IH. destruct (f t); lia.
Qed.

Lemma count_tag_list_set : forall f l i t t0,
nth_error l i = Some t0 -> count_tag f (list_set l i t) = count_tag f l - (if f t0 then 1 else 0) + (if f t then 1 else 0).
Proof.
induction l as [|x l IH]; intros [|i] t t0 H; cbn in H; try discriminate.
- inversion H; subst. cbn [list_set]. rewrite !count_tag_cons. lia.
- cbn [list_set]. rewrite !count_tag_cons, (IH i t t0 H). lia.
Qed.

Lemma count_tag_set_tag : forall f G c i t t0,
tag_at G c i = Some t0 ->
count_tag f (set_tag c i t G c) = count_tag f (G c) - (if f t0 then 1 else 0) + (if f t then 1 else 0).
Proof.
intros f G c i t t0 H. rewrite set_tag_class. apply count_tag_list_set.
unfold tag_at in H. destruct (Z.ltb_spec i 0); [discriminate| exact H].
Qed.

Lemma count_tag_ext : forall f l l',
length l = length l' -> (forall i t, f t = true -> (nth_error l i = Some t <-> nth_error l' i = Some t)) ->
count_tag f l = count_tag f l'.
Proof.
induction l as [|x l IH]; intros [|y l'] L E; cbn in L; [reflexivity| lia| lia|].
rewrite !count_tag_cons. rewrite (IH l'); [| lia|].
- destruct (f x) eqn:FX; destruct (f y) eqn:FY; try lia.
+ pose proof (proj1 (E 0%nat x FX) eq_refl) as K. cbn in K. inversion K; subst. congruence.
+ pose proof (proj2 (E 0%nat y FY) eq_refl) as K. cbn in K. inversion K; subst. congruence.
- intros i t Ft. exact (E (S i) t Ft).
Qed.

Lemma count_tag_same : forall f G G' c, same_len G G' -> same_tags f G G' -> count_tag f (G c) = count_tag f (G' c).
Proof.
intros f G G' c SL ST. apply count_tag_ext; [apply SL|]. intros i t Ft.
specialize (ST c (Z.of_nat i) t Ft). unfold tag_at in ST. destruct (Z.ltb_spec (Z.of_nat i) 0); [lia|].
rewrite Nat2Z.id in ST. exact ST.
Qed.

Definition gappend (c : Z) (l : list stag) (G : ghost) : ghost := gset c (G c ++ l) G.

Lemma tag_at_gappend_old : forall G c l c' i, i < ncarved G c' -> tag_at (gappend c l G) c' i = tag_at G c' i.
Proof.
intros G c l c' i Hi. unfold tag_at, gappend, ncarved in *. destruct (Z.ltb_spec i 0); [reflexivity|].
destruct (Z.eq_dec c' c) as [->|NE]; [rewrite gset_eq| rewrite gset_ne by exact NE; reflexivity].
apply nth_error_app1. lia.
Qed.

Lemma tag_at_gappend_new : forall G c l i, ncarved G c <= i -> tag_at (gappend c l G) c i = nth_error l (Z.to_nat (i - ncarved G c)).
Proof.
intros G c l i Hi. pose proof Hi as Hi'. unfold tag_at, gappend, ncarved in *. destruct (Z.ltb_spec i 0); [lia|].
rewrite gset_eq, nth_error_app2 by lia. f_equal. lia.
Qed.

Lemma tag_at_gappend_Some_old : forall G c l c' i t, tag_at G c' i = Some t -> tag_at (gappend c l G) c' i = Some t.
Proof. intros G c l c' i t H. rewrite tag_at_gappend_old; [exact H|]. exact (proj2 (tag_at_Some_lt _ _ _ _ H)). Qed.

Lemma ncarved_gappend : forall G c l c', ncarved (gappend c l G) c' = ncarved G c' + (if c' =? c then Z.of_nat (length l) else 0).
Proof.
intros G c l c'. unfold ncarved, gappend. destruct (Z.eqb_spec c' c) as [->|NE].
- rewrite gset_eq, length_app. lia.
- rewrite gset_ne by exact NE. lia.
Qed.

Lemma gappend_other_class : forall G c l c', c' <> c -> gappend c l G c' = G c'.
Proof. intros. unfold gappend. apply gset_ne. assumption. Qed.
Lemma gappend_class : forall G c l, gappend c l G c = G c ++ l.
Proof. intros. unfold gappend. apply gset_eq. Qed.

Lemma same_tags_gappend : forall f G c l, Forall (fun t => f t = false) l -> same_tags f G (gappend c l G).
Proof.
intros f G c l Hl c' i t Ft. destruct (Z.lt_ge_cases i (ncarved G c')) as [LT|GE].
- rewrite tag_at_gappend_old by exact LT. tauto.
- rewrite (tag_at_None_ge G c' i GE). destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite tag_at_gappend_new by exact GE. split; [discriminate|]. intros H.
apply nth_error_In in H. exfalso. pose proof (proj1 (Forall_forall _ _) Hl t H) as K. cbn in K. congruence.
+ unfold tag_at, gappend. destruct (Z.ltb_spec i 0); [tauto|]. rewrite gset_ne by exact NE.
rewrite (proj2 (nth_error_None _ _)); [tauto|]. unfold ncarved in GE. lia.
Qed.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q61C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q61C. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWRO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWRO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4g.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4g. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation mem := (word -> option byte) (only parsing).

Lemma KHI_eq : KHI = 0x10007fff8000. Proof. reflexivity. Qed.
Lemma SH_eq : forall a, SH a = a / 8 + 0x7fff8000. Proof. reflexivity. Qed.
Lemma SH_KHI : SH KHI = 0x2008fff7000. Proof. reflexivity. Qed.

Lemma SH_band {BAND : Band} : 0x10006fef8000 <= SH band_lo <= 0x10007ff78000.
Proof. rewrite SH_eq. pose proof band_lo_range. Z.div_mod_to_equations. lia. Qed.
Lemma SH_247 : SH (2^47) = KHI. Proof. reflexivity. Qed.

Definition musl_zone (x : Z) : Prop :=
(0x0ecd40 <= x < 0x0ecf18) \/ (0x645ca0 <= x < 0x6460b0).

Ltac lits := rewrite ?KHI_eq in *.

Ltac fin :=
unfold iv_disjoint, in_iv, musl_zone, a_client_data, A_ERRNO, A_INSTANCE, prim_lo, prim_hi, ptrarr_lo, ptrarr_hi, region_info, A_FS_MAP_SIZE, kPage, kSecUserOff,
a_ro_lo, a_data_hi, kLowEnd in *;
cbn [fst snd] in *; lits; lia.

Lemma kconsts : kRegionSize = 2^32 /\ kFreeArrayOffset = 0xE0000000 /\ kFreeArraySize = 0x20000000
/\ kNumClasses = 32 /\ kPage = 4096 /\ kSecUserOff = 0x1800 /\ kUserMapSize = 0x40000 /\ kMaxSize = 65536.
Proof. repeat split; reflexivity. Qed.

Lemma in_sh_bounds : forall lo len x, lo mod 8 = 0 -> 0 <= len -> in_sh (lo, len) x ->
SH lo <= x < SH (lo + len).
Proof.
intros lo len x Hal Hlen [H1 H2]. cbn [fst snd] in *. rewrite !SH_eq in *.
Z.div_mod_to_equations. lia.
Qed.

Lemma SH_mono : forall a b, a <= b -> SH a <= SH b.
Proof. intros a b H. rewrite !SH_eq. Z.div_mod_to_equations. lia. Qed.

Lemma in_sh_disjoint : forall lo1 len1 lo2 len2 x,
lo1 mod 8 = 0 -> lo2 mod 8 = 0 -> 0 <= len1 -> 0 <= len2 ->
(lo1 + len1 <= lo2 \/ lo2 + len2 <= lo1) ->
in_sh (lo1, len1) x -> in_sh (lo2, len2) x -> False.
Proof.
intros lo1 len1 lo2 len2 x A1 A2 L1 L2 D H1 H2.
apply in_sh_bounds in H1; [|assumption|assumption]. apply in_sh_bounds in H2; [|assumption|assumption].
rewrite !SH_eq in *. Z.div_mod_to_equations. lia.
Qed.

Lemma in_sh_heap {BAND : Band} : forall lo len x, lo mod 8 = 0 -> 0 <= len -> KHI <= lo -> lo + len <= band_lo ->
in_sh (lo, len) x -> 0x2008fff7000 <= x < SH band_lo.
Proof.
intros lo len x A L K C H. apply in_sh_bounds in H; [|assumption|assumption].
pose proof (SH_mono KHI lo K). pose proof (SH_mono (lo + len) band_lo C).
rewrite SH_KHI in *. lia.
Qed.

Lemma in_sh_band {BAND : Band} : forall lo len x, lo mod 8 = 0 -> 0 <= len -> lowhigh lo len -> lo + len <= band_lo ->
in_sh (lo, len) x -> kLowEnd <= x < KHI.
Proof.
intros lo len x A L K C H. apply in_sh_bounds in H; [|assumption|assumption].
pose proof (SH_mono (lo + len) band_lo C). pose proof SH_band. unfold kLowEnd, KHI in *. rewrite !SH_eq in *.
Z.div_mod_to_equations. lia.
Qed.

Lemma in_sh_sub : forall lo len lo' len' x,
lo mod 8 = 0 -> lo' mod 8 = 0 -> lo <= lo' -> lo' + len' <= lo + len ->
in_sh (lo', len') x -> in_sh (lo, len) x.
Proof.
intros lo len lo' len' x A A' B C [H1 H2]. cbn [fst snd] in *. split; cbn [fst snd]; rewrite !SH_eq in *;
Z.div_mod_to_equations; lia.
Qed.

Lemma class_size_facts : forall c, 1 <= c <= 31 -> 32 <= class_size c <= 98304 /\ class_size c mod 32 = 0.
Proof.
intros c Hc.
assert (H : forallb (fun c => (32 <=? class_size c) && (class_size c <=? 98304) && (class_size c mod 32 =? 0))
(map Z.of_nat (seq 1 31)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H c).
assert (Hin : In c (map Z.of_nat (seq 1 31))).
{ apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
specialize (H Hin). apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.eqb_eq in H3. lia.
Qed.

Section Geometry.
Context {BAND : Band}.
Variable RE : aentry.
Let L := ae_L RE.

Lemma reg_beg_eq : forall c, reg_beg L c = al_space_beg L + c * 2^32.
Proof. intros c. reflexivity. Qed.
Lemma fa_beg_eq : forall c, fa_beg L c = al_space_beg L + c * 2^32 + 0xE0000000.
Proof. intros c. reflexivity. Qed.
Lemma slot_beg_eq : forall c i, slot_beg RE c i = al_space_beg L + c * 2^32 + i * class_size c.
Proof. intros c i. reflexivity. Qed.

Lemma reg_beg_align : forall X c, rlay_ok RE X -> reg_beg L c mod 8 = 0 /\ reg_beg L c mod 16 = 0 /\ fa_beg L c mod 8 = 0.
Proof.
intros X c RL. destruct RL as (_ & _ & _ & _ & _ & P0 & _). unfold prim_lo in P0. fold L in P0.
rewrite reg_beg_eq, fa_beg_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma slot_beg_align : forall X c i, rlay_ok RE X -> 1 <= c <= 31 -> slot_beg RE c i mod 16 = 0 /\ slot_beg RE c i mod 8 = 0.
Proof.
intros X c i RL Hc. destruct RL as (_ & _ & _ & _ & _ & P0 & _). unfold prim_lo in P0. fold L in P0.
pose proof (class_size_facts c Hc) as [_ M]. rewrite slot_beg_eq.
Z.div_mod_to_equations. nia.
Qed.
End Geometry.

Section GCons.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB FS G RE X.

Lemma gc_rlay : rlay_ok RE X. Proof. exact (proj1 GC). Qed.
Lemma gc_blocks : forall p A n, In (p, A, n) LB -> live_prim RE G p A n \/ live_sec a p A n.
Proof. intros p A n H. exact (proj1 (proj1 (proj2 GC) p A n H)). Qed.
Lemma gc_block_small : forall p A n, In (p, A, n) LB -> n <= 2^26.
Proof. intros p A n H. exact (proj2 (proj1 (proj2 GC) p A n H)). Qed.
Lemma gc_nodup : List.NoDup (map ablk_id LB). Proof. exact (proj1 (proj2 (proj2 GC))). Qed.
Lemma gc_live_tags' : forall c i p, tag_at G c i = Some (TLive p) -> exists id n A, p = APrim id n /\ In (p, A, n) LB /\ class_of n = c.
Proof. exact (proj1 (proj2 (proj2 (proj2 GC)))). Qed.

Lemma gc_quar_tags : forall c i p, tag_at G c i = Some (TQuar p) -> aptr_cls p = c /\ from_primary (aptr_req p) = true.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 GC))))). Qed.
Lemma gc_classes : forall c, G c <> [] -> 1 <= c < kNumClasses /\ ncarved G c * class_size c = c_alloc_user (cls a c).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 GC)))))). Qed.
Lemma gc_bounds : forall c, 1 <= c < kNumClasses -> 0 <= c_alloc_user (cls a c) <= c_mapped_user (cls a c)
/\ c_mapped_user (cls a c) <= kFreeArrayOffset /\ c_mapped_user (cls a c) mod kUserMapSize = 0.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC))))))). Qed.
Lemma gc_unique : forall c i c' i' p t t', tag_at G c i = Some t -> tag_at G c' i' = Some t' -> holds p t = true -> holds p t' = true ->
c = c' /\ i = i'.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC)))))))). Qed.

Lemma gc_sec : Forall (sec_ok RE X) (as_reg a).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC)))))))))). Qed.
Lemma gc_sec_disj : pairwise_disjoint (map (fun e => (se_beg e, se_size e)) (as_reg a)).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC))))))))))). Qed.
Lemma gc_sec_nodup : List.NoDup (map se_beg (as_reg a)).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC)))))))))))). Qed.
Lemma gc_ff_range : forall f, In f FS -> fframe_rangeA RE (ff_cls f) (ff_addr f).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC))))))))))))). Qed.
Lemma gc_ff_disj : forall f1 f2, In f1 FS -> In f2 FS -> ff_addr f1 <> ff_addr f2 ->
ff_addr f1 + ff_size (ff_cls f1) <= ff_addr f2 \/ ff_addr f2 + ff_size (ff_cls f2) <= ff_addr f1.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 GC))))))))))))). Qed.

Let L := ae_L RE.

Lemma tag_slot : forall c i t, tag_at G c i = Some t ->
1 <= c <= 31 /\ 0 <= i /\ i + 1 <= ncarved G c
/\ reg_beg L c <= slot_beg RE c i
/\ slot_beg RE c i + class_size c <= reg_beg L c + c_alloc_user (cls a c)
/\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset
/\ 32 <= class_size c /\ class_size c mod 32 = 0
/\ slot_beg RE c i mod 16 = 0.
Proof.
intros c i t Ht. unfold tag_at in Ht. destruct (Z.ltb_spec i 0) as [Hi|Hi]; [discriminate|].
assert (NE : G c <> []) by (intros E; rewrite E in Ht; destruct (Z.to_nat i); discriminate).
destruct (gc_classes c NE) as [Hc Hcarve]. pose proof kconsts as (_ & _ & _ & K32 & _). rewrite K32 in Hc.
destruct (gc_bounds c ltac:(rewrite K32; lia)) as (B1 & B2 & B3).
pose proof (class_size_facts c ltac:(lia)) as [S1 S2].
assert (Hlen : (Z.to_nat i < length (G c))%nat) by (apply (proj1 (nth_error_Some (G c) (Z.to_nat i))); rewrite Ht; discriminate).
unfold ncarved in *.
pose proof (slot_beg_align RE X c i gc_rlay ltac:(lia)) as [AL _].
unfold slot_beg in AL |- *. change (ae_L RE) with L in AL |- *.
assert (i + 1 <= Z.of_nat (length (G c))) by lia.
repeat split; try lia; try nia.
Qed.

Lemma slots_disjoint : forall c i t c' i' t', tag_at G c i = Some t -> tag_at G c' i' = Some t' ->
(c <> c' \/ i <> i') ->
slot_beg RE c i + class_size c <= slot_beg RE c' i' \/ slot_beg RE c' i' + class_size c' <= slot_beg RE c i.
Proof.
intros c i t c' i' t' Ht Ht' NE.
pose proof (tag_slot c i t Ht) as (C1 & I1 & N1 & R1 & R2 & B1 & B2 & S1 & S2 & _).
pose proof (tag_slot c' i' t' Ht') as (C1' & I1' & N1' & R1' & R2' & B1' & B2' & S1' & S2' & _).
pose proof kconsts as (_ & KO & _).
destruct (Z.eq_dec c c') as [<-|NC].
- assert (i <> i') by lia. unfold slot_beg. fold L. nia.
- rewrite reg_beg_eq in *. fold L in R1, R2, R1', R2'. rewrite KO in *.
assert (c + 1 <= c' \/ c' + 1 <= c) as [D|D] by lia; nia.
Qed.
End GCons.

Lemma sec_req_facts : forall n, 0 <= n -> from_primary n = false -> rz_size n = 2048 /\ 64513 <= n.
Proof.
intros n Hn HP. unfold from_primary in HP. apply Z.leb_gt in HP. pose proof kconsts as (_ & _ & _ & _ & _ & _ & _ & KM). rewrite KM in HP.
destruct (Z.le_gt_cases n 64512) as [LE|GT].
- exfalso. unfold needed in HP.
assert (R : rz_size n <= 1024).
{ unfold rz_size.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); lia. }
pose proof (round_up_8 (Z.max n 8) ltac:(lia)) as [A B].
assert (round_up (Z.max n 8) 8 <= 64512) by (unfold round_up in *; Z.div_mod_to_equations; lia). lia.
- split; [|lia]. unfold rz_size.
destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); [lia|]. reflexivity.
Qed.

Lemma sec_map_size_ge : forall n, 0 <= n -> from_primary n = false -> n + 8192 <= sec_map_size n /\ sec_map_size n mod 4096 = 0.
Proof.
intros n Hn HP. destruct (sec_req_facts n Hn HP) as [RZ GE]. unfold sec_map_size.
pose proof (needed_facts n Hn) as (N1 & _). rewrite RZ in *.
pose proof kconsts as (_ & _ & _ & _ & KP & _). rewrite KP.
pose proof (round_up_ge (needed n + 2048) 4096 ltac:(lia)) as (U1 & U2 & U3).
split; [lia|]. rewrite Z.add_mod, U3 by lia. reflexivity.
Qed.

Section GCons2.
Context {BAND : Band}.
Variables (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB FS G RE X.
Let L := ae_L RE.

Lemma sec_entry_facts : forall e, In e (as_reg a) -> sec_ok RE X e.
Proof. intros e He. exact (proj1 (List.Forall_forall _ _) (gc_sec a LB FS G RE X GC) e He). Qed.

Definition blk_container (p : aptr) (A n lo hi : Z) : Prop :=
lo + 16 <= A /\ A + Z.max n 1 <= hi /\ lo mod 16 = 0 /\ lowhigh lo (hi - lo) /\ hi <= band_lo.

Lemma live_block_geom : forall p A n, In (p, A, n) LB ->
0 <= n /\ A mod 16 = 0 /\
( (exists c i, tag_at G c i = Some (TLive p) /\ aptr_cls p = c /\ p = APrim (match p with APrim id _ => id | _ => 0%N end) n
/\ A = slot_beg RE c i + rz_size n
/\ blk_container p A n (slot_beg RE c i) (slot_beg RE c i + class_size c))
\/ (exists e, In e (as_reg a) /\ p = ASec (se_beg e) n /\ se_req e = n /\ A = se_beg e + kSecUserOff
/\ blk_container p A n (se_beg e + kPage) (se_beg e + se_size e)) ).
Proof.
intros p A n Hin. pose proof (gc_rlay a LB FS G RE X GC) as RL.
destruct (gc_blocks a LB FS G RE X GC p A n Hin) as [(id & i & -> & Hn & HP & Ht & Hi & HA)|(mb & -> & Hn & HP & He & HA)].
- pose proof (tag_slot a LB FS G RE X GC _ _ _ Ht) as (C1 & I1 & N1 & R1 & R2 & B1 & B2 & S1 & S2 & AL).
pose proof (class_of_facts n Hn HP) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbv zeta in Q1, Q2, Q3, Q4.
pose proof (rz_size_range n) as [Z1 Z2]. unfold prim_user in HA.
destruct RL as (_ & _ & _ & _ & _ & P0 & P1 & P2 & _). unfold prim_lo, prim_hi in *. change (ae_L RE) with L in P0, P1, P2.
pose proof kconsts as (_ & KO & _). rewrite reg_beg_eq in R1, R2. fold L in R1, R2.
split; [lia|]. split; [subst A; Z.div_mod_to_equations; lia|].
left. exists (class_of n), i. split; [exact Ht|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HA|].
unfold blk_container. lits. unfold used_size in *. repeat split; try lia; try nia.
- pose proof (sec_entry_facts _ He) as (E1 & E2 & E3 & E4 & E5 & E6 & _). cbn [se_beg se_size se_req] in *.
pose proof (sec_map_size_ge n Hn HP) as [M1 M2]. pose proof kconsts as (_ & _ & _ & _ & KP & KU & _).
split; [lia|]. split; [subst A; rewrite KU; Z.div_mod_to_equations; lia|].
right. exists (mkSec mb (sec_map_size n) n). cbn [se_beg se_size se_req].
split; [exact He|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HA|].
unfold blk_container. lits. rewrite KP, KU in *. repeat split; first [lia | Z.div_mod_to_equations; lia].
Qed.
End GCons2.

Lemma pairwise_disjoint_In : forall l x y, pairwise_disjoint l -> In x l -> In y l -> x <> y -> iv_disjoint x y.
Proof.
induction l as [|z l IH]; intros x y PD Hx Hy NE; [destruct Hx|].
destruct PD as [F PD]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
- congruence.
- exact (proj1 (List.Forall_forall _ _) F y Hy).
- pose proof (proj1 (List.Forall_forall _ _) F x Hx) as D. unfold iv_disjoint in *. lia.
- apply IH; assumption.
Qed.

Lemma pairwise_disjoint_map_In : forall {A} (f : A -> Z * Z) l x y,
pairwise_disjoint (map f l) -> In x l -> In y l -> f x <> f y -> iv_disjoint (f x) (f y).
Proof.
intros A f l x y PD Hx Hy NE. apply (pairwise_disjoint_In (map f l)); try assumption; apply in_map; assumption.
Qed.

Lemma NoDup_map_In_inj : forall {A B} (g : A -> B) l x y,
List.NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
induction l as [|z l IH]; intros x y ND Hx Hy E; [destruct Hx|].
cbn in ND. inversion ND as [|z' l' NI ND']; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- reflexivity.
- exfalso. apply NI. rewrite E. apply in_map. exact Hy.
- exfalso. apply NI. rewrite <- E. apply in_map. exact Hx.
- apply IH; assumption.
Qed.

Definition fp_img : list (Z * Z) :=
rtconst_img ++ [ (A_INSTANCE + 104, 624); (A_INSTANCE + 728, 64); (A_INSTANCE + 816, 2800);
(0x0f33c0, 0x81038); (0x181c48, 4); (0x1c4088, 0x450028);
(A_ERRNO, 4); (0x174420, 1) ].

Definition client_ivs : list (Z * Z) :=
[ (0x0ec920, 0x0ecd40); (0x0ecd40, 0x0eeb00); (0x0eeb08, 0x0eeb58); (0x184058, 0x184068); (0x614800, 0x624810); (0x624810, 0x624840); (0x624840, 0x625450); (0x625450, 0x62547c); (0x625480, 0x6254c8); (0x6254d0, 0x625518); (0x625558, 0x645560); (0x645568, 0x6457e0); (0x6457e8, 0x6458a0); (0x6458a0, 0x646940); (0x646db8, 0x646dbc); (0x7fffa000, 0x800c0e00);
(0x0ecd40, 0x0ecf18); (0x645ca0, 0x6460b0) ].

Local Ltac in_pick k := lazymatch k with O => left; reflexivity | S ?k' => right; in_pick k' end.
Local Ltac civ F2 k := let H := fresh "CI" in pose proof (F2 _ ltac:(in_pick k)) as H; cbn [fst snd] in H;
apply orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H; lia.

Lemma fp_img_ok : forall x, in_ivs fp_img x -> 0x10000 <= x < 0x647000 /\ ~ a_client_data x /\ ~ musl_zone x.
Proof.
intros x (iv & Hin & [H1 H2]).
assert (F : forallb (fun iv => (0x10000 <=? fst iv) && (fst iv + snd iv <=? 0x647000)
&& forallb (fun c => (fst iv + snd iv <=? fst c) || (snd c <=? fst iv)) client_ivs) fp_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F. specialize (F iv Hin). apply andb_prop in F as [F1 F2]. apply andb_prop in F1 as [F0 F1].
apply Z.leb_le in F0. apply Z.leb_le in F1.
rewrite forallb_forall in F2.
split; [lia|]. split.
- unfold a_client_data. intros CD.
destruct CD as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]];
[civ F2 0%nat| civ F2 1%nat| civ F2 2%nat| civ F2 3%nat| civ F2 4%nat| civ F2 5%nat| civ F2 6%nat| civ F2 7%nat| civ F2 8%nat| civ F2 9%nat| civ F2 10%nat| civ F2 11%nat| civ F2 12%nat| civ F2 13%nat| civ F2 14%nat| civ F2 15%nat].
- unfold musl_zone. intros [C|C]; [civ F2 16%nat| civ F2 17%nat].
Qed.

Definition czone {BAND : Band} (LB0 : list ablock) (RE : aentry) (x : Z) : Prop :=
band_lo <= x
\/ a_client_data x
\/ in_live_user LB0 x
\/ in_iv (ae_fs_base RE, A_FS_MAP_SIZE) x
\/ in_sh (ae_fs_base RE, A_FS_MAP_SIZE) x
\/ (SH band_lo <= x < KHI)
\/ musl_zone x.

Section Zones.
Context {BAND : Band}.
Variables (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay).
Hypothesis GC : gcons a LB0 FS0 G RE X.
Local Notation CZ := (czone LB0 RE).

Lemma rl_objs : forall o, In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ (lowhigh (fst o) (snd o) /\ off_hull (fst o) (snd o)) /\ fst o + snd o <= band_lo
/\ iv_disjoint o (prim_lo RE, 2^37 + 0x1000) /\ iv_disjoint o (ptrarr_lo RE, 0x800000).
Proof.
intros o Ho. destruct (gc_rlay a LB0 FS0 G RE X GC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _).
exact (proj1 (List.Forall_forall _ _) F o Ho).
Qed.

Lemma rl_objs_lia : forall o, In o (rlay_objs RE X) ->
fst o mod 4096 = 0 /\ appr_lia (fst o) (snd o) /\ fst o + snd o <= band_lo
/\ iv_disjoint o (prim_lo RE, 2^37 + 0x1000) /\ iv_disjoint o (ptrarr_lo RE, 0x800000).
Proof.
intros o Ho. destruct (rl_objs o Ho) as (A1 & A2 & A3 & A4 & A5).
assert (N : 0 <= snd o) by (clear - Ho; unfold rlay_objs in Ho; repeat destruct Ho as [Ho|Ho]; try destruct Ho; subst; cbn; unfold A_FS_MAP_SIZE; lia).
split; [exact A1|]. split; [apply appr_to_lia; [exact N| lia| exact A2]|]. split; [exact A3|]. split; assumption.
Qed.
Lemma rl_objs_disj : forall o1 o2, In o1 (rlay_objs RE X) -> In o2 (rlay_objs RE X) -> o1 <> o2 -> iv_disjoint o1 o2.
Proof.
intros o1 o2 H1 H2 NE. destruct (gc_rlay a LB0 FS0 G RE X GC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PD).
apply (pairwise_disjoint_In _ _ _ PD H1 H2 NE).
Qed.
Lemma rl_prim : prim_lo RE mod 0x10000 = 0 /\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo
/\ ptrarr_lo RE mod 4096 = 0 /\ (lowhigh (ptrarr_lo RE) 0x800000 /\ off_hull (ptrarr_lo RE) 0x800000) /\ ptrarr_hi RE <= band_lo
/\ iv_disjoint (prim_lo RE, 2^37 + 0x1000) (ptrarr_lo RE, 0x800000).
Proof. destruct (gc_rlay a LB0 FS0 G RE X GC) as (_ & _ & _ & _ & _ & P0 & P1 & P2 & Q0 & Q1 & Q2 & [D _] & _). exact (conj P0 (conj P1 (conj P2 (conj Q0 (conj Q1 (conj Q2 D)))))). Qed.

Lemma fs_obj : In (ae_fs_base RE, A_FS_MAP_SIZE) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma T_obj : In (rl_T X, 0x1000) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma ctx_obj : In (rl_ctx X, 0x10000) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma dn_obj : In (rl_dn X, 0x100000) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma ssb_obj : In (rl_ssb X, 0x800000) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma dtls_obj : In (rl_dtls X, 0x1000) (rlay_objs RE X). Proof. cbn. tauto. Qed.
Lemma obj_ne_fs : forall b n, n <> A_FS_MAP_SIZE -> (b, n) <> (ae_fs_base RE, A_FS_MAP_SIZE).
Proof. intros b n NE E. apply NE. exact (f_equal snd E). Qed.

Lemma sec_facts : forall e, In e (as_reg a) -> sec_ok RE X e.
Proof. intros e He. exact (proj1 (List.Forall_forall _ _) (gc_sec a LB0 FS0 G RE X GC) e He). Qed.

Lemma sec_same : forall e e' x, In e (as_reg a) -> In e' (as_reg a) ->
se_beg e <= x < se_beg e + se_size e -> se_beg e' <= x < se_beg e' + se_size e' -> e = e'.
Proof.
intros e e' x He He' Hx Hx'.
destruct (decide (se_beg e = se_beg e')) as [E|NE].
- exact (NoDup_map_In_inj se_beg (as_reg a) e e' (gc_sec_nodup a LB0 FS0 G RE X GC) He He' E).
- exfalso. pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg a) e e'
(gc_sec_disj a LB0 FS0 G RE X GC) He He' ltac:(intros EQ; apply NE; exact (f_equal fst EQ))) as D.
unfold iv_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma region_in_prim : forall c, 1 <= c <= 31 ->
prim_lo RE <= reg_beg (ae_L RE) c /\ fa_beg (ae_L RE) c = reg_beg (ae_L RE) c + kFreeArrayOffset
/\ fa_beg (ae_L RE) c + kFreeArraySize <= prim_lo RE + 2^37 /\ reg_beg (ae_L RE) c = prim_lo RE + c * 2^32.
Proof.
intros c Hc. unfold prim_lo. rewrite reg_beg_eq, fa_beg_eq. pose proof kconsts as (_ & KO & KS & _). rewrite KO, KS. lia.
Qed.

Lemma slot_prim : forall c i t, tag_at G c i = Some t ->
prim_lo RE <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= prim_hi RE /\ slot_beg RE c i mod 8 = 0 /\ slot_beg RE c i mod 16 = 0
/\ 1 <= c <= 31 /\ reg_beg (ae_L RE) c <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + kFreeArrayOffset
/\ 32 <= class_size c /\ class_size c mod 32 = 0.
Proof.
intros c i t Ht. pose proof (tag_slot a LB0 FS0 G RE X GC c i t Ht) as (C1 & I1 & N1 & R1 & R2 & B1 & B2 & S1 & S2 & AL).
pose proof (region_in_prim c C1) as (Q1 & Q2 & Q3 & Q4). pose proof kconsts as (_ & KO & KS & _).
unfold prim_hi. unfold prim_lo in *. repeat split; try lia.
Qed.

Lemma live_user_where : forall x, in_live_user LB0 x ->
exists p A n, In (p, A, n) LB0 /\ A <= x < A + n /\
( (exists c i, tag_at G c i = Some (TLive p) /\ slot_beg RE c i + 16 <= A /\ A + n <= slot_beg RE c i + class_size c)
\/ (exists e, In e (as_reg a) /\ sec_live LB0 e /\ se_beg e + kPage + 16 <= A /\ A + n <= se_beg e + se_size e) ).
Proof.
intros x (b & Hb & Hx). destruct b as [[p A] n]. cbn [ablk_addr ablk_size fst snd] in Hx.
exists p, A, n. split; [exact Hb|]. split; [lia|].
destruct (live_block_geom a LB0 FS0 G RE X GC p A n Hb) as (Hn & AL & [(c & i & Ht & Hc & Hp & HA & CT)|(e & He & Hp & Hr & HA & CT)]);
unfold blk_container in CT.
- left. exists c, i. split; [exact Ht|]. lia.
- right. exists e. split; [exact He|]. split; [exists A; subst p; rewrite Hr; exact Hb|]. lia.
Qed.

Lemma live_user_heap : forall x, in_live_user LB0 x -> ((0 < x < kLowEnd /\ (x < 0x10000 \/ 0x647000 <= x)) \/ KHI <= x) /\ x < band_lo.
Proof.
intros x LU. destruct (live_user_where x LU) as (p & A & n & Hb & Hx & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
- pose proof (slot_prim c i _ Ht) as (P1 & P2 & _). pose proof rl_prim as (_ & K & CE & _). fin.
- pose proof (sec_facts e He) as (E1 & [E2 E2'] & E3 & _). unfold a_ro_lo, a_data_hi, kLowEnd in *. fin.
Qed.

Lemma live_user_prim : forall x, in_live_user LB0 x -> prim_lo RE <= x < prim_hi RE ->
exists c i p, tag_at G c i = Some (TLive p) /\ slot_beg RE c i + 16 <= x < slot_beg RE c i + class_size c.
Proof.
intros x LU Hx. destruct (live_user_where x LU) as (p & A & n & Hb & HA & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
- exists c, i, p. split; [exact Ht| lia].
- exfalso. pose proof (sec_facts e He) as (_ & _ & _ & _ & _ & _ & DP & _). fin.
Qed.

Lemma live_user_sec : forall e x, in_live_user LB0 x -> In e (as_reg a) -> se_beg e <= x < se_beg e + se_size e ->
sec_live LB0 e /\ se_beg e + kPage + 16 <= x.
Proof.
intros e x LU He Hx. destruct (live_user_where x LU) as (p & A & n & Hb & HA & [(c & i & Ht & S1 & S2)|(e' & He' & HL & S1 & S2)]).
- exfalso. pose proof (slot_prim c i _ Ht) as (P1 & P2 & _). pose proof (sec_facts e He) as (_ & _ & _ & _ & _ & _ & DP & _). fin.
- assert (e' = e) as -> by (apply (sec_same e' e x He' He); [|exact Hx]; pose proof kconsts as (_ & _ & _ & _ & KP & _); lia).
split; [exact HL| lia].
Qed.

Lemma live_user_in_slot : forall c i t x, tag_at G c i = Some t ->
slot_beg RE c i <= x < slot_beg RE c i + class_size c -> in_live_user LB0 x -> exists p, t = TLive p.
Proof.
intros c i t x Ht Hx LU. pose proof (slot_prim c i t Ht) as (P1 & P2 & _).
destruct (live_user_prim x LU ltac:(lia)) as (c' & i' & p & Ht' & Hx').
destruct (decide (c = c' /\ i = i')) as [[-> ->]|NE].
- rewrite Ht in Ht'. inversion Ht'. exists p. reflexivity.
- exfalso. pose proof (slots_disjoint a LB0 FS0 G RE X GC c i t c' i' _ Ht Ht' ltac:(lia)). lia.
Qed.

Lemma cz_img : forall x, in_ivs fp_img x -> CZ x -> False.
Proof.
intros x HI [C|[C|[C|[C|[C|[C|C]]]]]]; destruct (fp_img_ok x HI) as (H1 & H2 & H3);
pose proof (rl_objs _ fs_obj) as (AL & K & CE & _); cbn [fst snd] in AL, K, CE.
- fin. - fin.
- apply live_user_heap in C. fin.
- fin.
- apply in_sh_band in C; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
- pose proof SH_band. fin.
- exact (H3 C).
Qed.

Lemma cz_obj : forall o x, In o (rlay_objs RE X) -> o <> (ae_fs_base RE, A_FS_MAP_SIZE) -> in_iv o x -> CZ x -> False.
Proof.
intros o x Ho NE [O1 O2] [C|[C|[C|[C|[C|[C|C]]]]]]; pose proof (rl_objs o Ho) as (OA & OK & OC & OP & OQ);
pose proof (rl_objs _ fs_obj) as (AL & K & CE & _); cbn [fst snd] in AL, K, CE.
- fin. - fin.
- destruct (live_user_where x C) as (p & A & n & Hb & Hx & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
+ pose proof (slot_prim c i _ Ht) as (P1 & P2 & _). fin.
+ destruct (sec_facts e He) as (_ & _ & _ & _ & _ & _ & _ & _ & F). pose proof (proj1 (List.Forall_forall _ _) F o Ho) as D. fin.
- pose proof (rl_objs_disj _ _ Ho fs_obj NE) as D. fin.
- apply in_sh_band in C; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
- pose proof SH_band. fin.
- fin.
Qed.

Lemma cz_ptr : forall x, ptrarr_lo RE <= x < ptrarr_hi RE -> CZ x -> False.
Proof.
intros x Hx [C|[C|[C|[C|[C|[C|C]]]]]]; pose proof rl_prim as (P0 & P1 & P2 & Q0 & Q1 & Q2 & D);
pose proof (rl_objs _ fs_obj) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
- fin. - fin.
- destruct (live_user_where x C) as (p & A & n & Hb & Hx' & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
+ pose proof (slot_prim c i _ Ht) as (R1 & R2 & _). fin.
+ destruct (sec_facts e He) as (_ & _ & _ & _ & _ & _ & _ & DQ' & _). fin.
- fin.
- apply in_sh_band in C; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
- pose proof SH_band. fin.
- fin.
Qed.

Lemma cz_prim : forall x, prim_lo RE <= x < prim_hi RE -> ~ in_live_user LB0 x -> CZ x -> False.
Proof.
intros x Hx NU [C|[C|[C|[C|[C|[C|C]]]]]]; pose proof rl_prim as (P0 & P1 & P2 & Q0 & Q1 & Q2 & D);
pose proof (rl_objs _ fs_obj) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
- fin. - fin.
- exact (NU C).
- fin.
- apply in_sh_band in C; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
- pose proof SH_band. fin.
- fin.
Qed.

Lemma cz_sec : forall e x, In e (as_reg a) -> se_beg e <= x < se_beg e + se_size e -> ~ in_live_user LB0 x -> CZ x -> False.
Proof.
intros e x He Hx NU [C|[C|[C|[C|[C|[C|C]]]]]]; pose proof (sec_facts e He) as (E1 & E2 & E3 & _ & _ & _ & E7 & E8 & E9);
pose proof (rl_objs _ fs_obj) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
- fin. - fin.
- exact (NU C).
- pose proof (proj1 (List.Forall_forall _ _) E9 _ fs_obj) as D. fin.
- apply in_sh_band in C; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
- pose proof SH_band. fin.
- fin.
Qed.

Lemma cz_sh : forall lo len x, lo mod 8 = 0 -> 0 <= len -> (lowhigh lo len /\ off_hull lo len) -> lo + len <= band_lo ->
iv_disjoint (lo, len) (ae_fs_base RE, A_FS_MAP_SIZE) ->
in_sh (lo, len) x -> CZ x -> False.
Proof.
intros lo len x AL0 L0 K0 CE0 DJ Hs [C|[C|[C|[C|[C|[C|C]]]]]]; pose proof (in_sh_band lo len x AL0 L0 (proj1 K0) CE0 Hs) as B;
pose proof (in_sh_bounds lo len x AL0 L0 Hs) as B2; pose proof (SH_mono (lo + len) band_lo CE0) as B3;
rewrite !SH_eq in B2, B3; pose proof K0 as [K0a K0b];
pose proof (rl_objs _ fs_obj) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
- fin.
-
clear -C B B2 K0a K0b. unfold a_client_data, iv_disjoint, a_ro_lo, a_data_hi, kLowEnd, KHI in *. cbn [fst snd] in *.
Z.div_mod_to_equations. lia.
- apply live_user_heap in C. clear -C B. unfold kLowEnd, KHI in *. lia.
- clear -C B K. unfold in_iv, kLowEnd, KHI, A_FS_MAP_SIZE in *. cbn [fst snd] in *. lia.
- eapply (in_sh_disjoint lo len (ae_fs_base RE) A_FS_MAP_SIZE x); try assumption;
[Z.div_mod_to_equations; lia| unfold A_FS_MAP_SIZE; lia].
- clear -C B2 B3. rewrite SH_eq in C. lia.
- fin.
Qed.

Lemma cz_sh_prim : forall lo len x, lo mod 8 = 0 -> 0 <= len -> prim_lo RE <= lo -> lo + len <= prim_hi RE ->
in_sh (lo, len) x -> CZ x -> False.
Proof.
intros lo len x AL L0 P1 P2 Hs C. pose proof rl_prim as (Q0 & Q1 & Q2 & _).
pose proof (rl_objs _ fs_obj) as (_ & _ & _ & DP & _).
eapply (cz_sh lo len x); try eassumption; try fin.
Qed.

Lemma cz_sh_sec : forall e lo len x, In e (as_reg a) -> lo mod 8 = 0 -> 0 <= len -> se_beg e <= lo -> lo + len <= se_beg e + se_size e ->
in_sh (lo, len) x -> CZ x -> False.
Proof.
intros e lo len x He AL L0 P1 P2 Hs C. pose proof (sec_facts e He) as (E1 & E2 & E3 & _ & _ & _ & E7 & E8 & E9).
pose proof (proj1 (List.Forall_forall _ _) E9 _ fs_obj) as DQ.
eapply (cz_sh lo len x); try eassumption; try fin.
Qed.

Lemma rtconst_img_ok : forall x, in_ivs rtconst_img x -> 0x10000 <= x < 0x647000 /\ ~ (0x614810 <= x < 0x624811).
Proof.
intros x (iv & Hin & [H1 H2]).
assert (F : forallb (fun iv => (0x10000 <=? fst iv) && (fst iv + snd iv <=? 0x647000) && ((fst iv + snd iv <=? 0x614810) || (0x624811 <=? fst iv))) rtconst_img = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in F. specialize (F iv Hin). apply andb_prop in F as [F1 F2]. apply andb_prop in F1 as [F0 F1].
apply Z.leb_le in F0. apply Z.leb_le in F1.
apply orb_prop in F2. destruct F2 as [F2|F2]; apply Z.leb_le in F2; lia.
Qed.

Ltac fp_img_mem H := eapply cz_img; [| eassumption]; eexists; split; [| exact H]; cbn; unfold A_INSTANCE; cbn; tauto.

Lemma fp_RTconst_cz : forall x, fp_RTconst RE X x -> CZ x -> False.
Proof.
intros x [H|[H|[H|H]]] C.
- eapply cz_img; [|exact C]. destruct H as (iv & Hin & Hx). exists iv. split; [apply in_app_iff; left; exact Hin| exact Hx].
- eapply (cz_obj _ x T_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. destruct H; split; cbn [fst snd] in *; lia.
- eapply (cz_obj _ x ctx_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. destruct H; split; cbn [fst snd] in *; lia.
- eapply (cz_obj _ x dtls_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| exact H | exact C].
Qed.

Lemma fp_RDepot_cz : forall x, fp_RDepot RE X x -> CZ x -> False.
Proof.
intros x [H|[H|[H|H]]] C.
- fp_img_mem H.
- eapply (cz_obj _ x dn_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| exact H | exact C].
- eapply (cz_obj _ x ssb_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| exact H | exact C].
- eapply (cz_obj _ x T_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. split; cbn [fst snd]; lia.
Qed.

Lemma fp_RPrim_cz : forall x, fp_RPrim G RE X x -> CZ x -> False.
Proof.
intros x [H|[H|[H|[H|[[H NS]|[H NS]]]]]] C; pose proof rl_prim as (P0 & P1 & P2 & _); pose proof kconsts as (_ & KO & KS & K32 & _).
-  destruct H as [H1 H2]. cbn [fst snd] in *.
eapply (cz_prim x); [fin| |exact C]. intros LU.
destruct (live_user_prim x LU ltac:(fin)) as (c & i & p & Ht & Hx).
pose proof (slot_prim c i _ Ht) as (_ & _ & _ & _ & C1 & R1 & R2 & _). pose proof (region_in_prim c C1) as (Q1 & Q2 & Q3 & Q4). fin.
- eapply (cz_obj _ x T_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. destruct H; split; cbn [fst snd] in *; lia.
-  destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
eapply (cz_prim x); [fin| |exact C]. intros LU.
destruct (live_user_prim x LU ltac:(fin)) as (c' & i' & p & Ht & Hx').
pose proof (slot_prim c' i' _ Ht) as (_ & _ & _ & _ & C1 & R1 & R2 & _). pose proof (region_in_prim c' C1) as (Q1' & Q2' & Q3' & Q4').
rewrite KO, KS in *. assert (c = c' \/ c + 1 <= c' \/ c' + 1 <= c) as [->|[D|D]] by lia; fin.
-  destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
pose proof (reg_beg_align RE X c (gc_rlay a LB0 FS0 G RE X GC)) as (_ & _ & FAL).
eapply (cz_sh_prim (fa_beg (ae_L RE) c) kFreeArraySize x); try eassumption; fin.
-  destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
eapply (cz_prim x); [fin| |exact C]. intros LU.
destruct (live_user_prim x LU ltac:(fin)) as (c' & i' & p & Ht & Hx').
apply NS. exists c', i', (TLive p). split; [exact Ht|]. split; [reflexivity|]. split; cbn [fst snd]; lia.
-  destruct H as (c & Hc & Hx). rewrite K32 in Hc. pose proof (region_in_prim c ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
pose proof (reg_beg_align RE X c (gc_rlay a LB0 FS0 G RE X GC)) as (RAL & _).
eapply (cz_sh_prim (reg_beg (ae_L RE) c) kFreeArrayOffset x); try eassumption; fin.
Qed.

Lemma fp_RChunks_cz : forall x, fp_RChunks a LB0 G RE X x -> CZ x -> False.
Proof.
intros x [[[H|H] NU]|[H|H]] C; pose proof kconsts as (_ & KO & KS & K32 & KP & _).
- destruct H as (c & i & t & Ht & _ & Hx). pose proof (slot_prim c i t Ht) as (P1 & P2 & _).
eapply (cz_prim x); [destruct Hx; fin| exact NU| exact C].
- destruct H as (e & He & _ & Hx). eapply (cz_sec e x He); [fin| exact NU| exact C].
- destruct H as (c & i & t & Ht & _ & Hx). pose proof (slot_prim c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
eapply (cz_sh_prim (slot_beg RE c i) (class_size c) x); try eassumption; lia.
- destruct H as (e & He & _ & Hx). pose proof (sec_facts e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1, M2.
eapply (cz_sh_sec e (se_beg e + kPage) (se_size e - kPage) x); try eassumption; fin.
Qed.

Lemma fp_RSec_cz : forall x, fp_RSec a RE X x -> CZ x -> False.
Proof.
intros x [H|[H|[H|H]]] C; pose proof kconsts as (_ & KO & KS & K32 & KP & _).
- fp_img_mem H.
- eapply (cz_ptr x); [fin| exact C].
- destruct H as (e & He & Hx). pose proof (sec_facts e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1, M2.
eapply (cz_sec e x He); [fin| | exact C]. intros LU.
destruct (live_user_sec e x LU He ltac:(fin)) as [_ B]. fin.
- destruct H as (e & He & Hx). pose proof (sec_facts e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1, M2.
eapply (cz_sh_sec e (se_beg e) kPage x); try eassumption; fin.
Qed.

Lemma fp_RQuar_cz : forall x, fp_RQuar a LB0 G RE X x -> CZ x -> False.
Proof.
intros x [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]] C; pose proof kconsts as (_ & KO & KS & K32 & KP & _).
- eapply (cz_obj _ x T_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. destruct H; split; cbn [fst snd] in *; lia.
- fp_img_mem H.
- fp_img_mem H.
- fp_img_mem H.
- fp_img_mem H.
- destruct H as (c & i & t & Ht & Hq & Hx). pose proof (slot_prim c i t Ht) as (P1 & P2 & _).
eapply (cz_prim x); [destruct Hx; fin| | exact C]. intros LU.
destruct (live_user_in_slot c i t x Ht ltac:(destruct Hx; cbn [fst snd] in *; lia) LU) as [p ->]. discriminate.
- destruct H as (c & i & t & Ht & _ & Hx). pose proof (slot_prim c i t Ht) as (P1 & P2 & P3 & _ & _ & _ & _ & SZ & _).
eapply (cz_sh_prim (slot_beg RE c i) (class_size c) x); try eassumption; lia.
- destruct H as (e & He & NL & Hx). pose proof (sec_facts e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
eapply (cz_sec e x He); [fin| | exact C]. intros LU.
destruct (live_user_sec e x LU He ltac:(fin)) as [HL _]. exact (NL HL).
- destruct H as (e & He & _ & Hx). pose proof (sec_facts e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. rewrite <- E4 in M1, M2.
eapply (cz_sh_sec e (se_beg e + kPage) (se_size e - kPage) x); try eassumption; fin.
Qed.

Lemma fp_RStats_cz : forall x, fp_RStats RE X x -> CZ x -> False.
Proof.
intros x [H|[H|H]] C.
- eapply (cz_obj _ x T_obj); [apply obj_ne_fs; unfold A_FS_MAP_SIZE; lia| | exact C]. destruct H; split; cbn [fst snd] in *; lia.
- fp_img_mem H.
- subst x. eapply cz_img; [|exact C]. exists (0x174420, 1). split; [cbn; unfold A_INSTANCE, A_ERRNO; cbn; tauto|]. split; cbn [fst snd]; lia.
Qed.

Lemma fp_RFake_zone : forall FS x, fp_RFake FS RE X x -> in_iv (ae_fs_base RE, A_FS_MAP_SIZE) x \/ in_sh (ae_fs_base RE, A_FS_MAP_SIZE) x.
Proof. intros FS x [[H _]|[H _]]; [left|right]; exact H. Qed.

Lemma frame_shadow_where : forall x, in_fframe_shadow FS0 x -> in_sh (ae_fs_base RE, A_FS_MAP_SIZE) x.
Proof.
intros x (f & Hf & Hx). pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf) as (R1 & R2 & R3 & R4 & R5).
pose proof (rl_objs _ fs_obj) as (AL & _). cbn [fst] in AL.
eapply (in_sh_sub _ _ (ff_addr f) (ff_size (ff_cls f))); try (unfold A_FS_MAP_SIZE; lia). exact Hx.
Qed.

Lemma client_czone : forall LB FS iv x, Permutation LB LB0 -> Permutation FS FS0 ->
aclient_write_okA a_alayout LB FS iv -> fst iv <= x < snd iv -> CZ x.
Proof.
intros LB FS iv x PB PF CW Hx. unfold czone.
destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1 C2]]]]]].
- left; lia.
- right; left. specialize (C x Hx). cbn [ala_client_data a_alayout] in C. exact C.
- do 2 right; left. exists b. split; [eapply Permutation_in; [exact PB| exact Hb]| lia].
- do 3 right; left. assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5). split; cbn [fst snd]; unfold A_FS_MAP_SIZE; lia.
- do 4 right; left. apply frame_shadow_where. exists f. split; [eapply Permutation_in; [exact PF| exact Hf]| lia].
- do 5 right. rewrite SH_247 in C2. lia.
Qed.

Lemma fp_RFake_client : forall LB FS iv x, Permutation LB LB0 -> Permutation FS FS0 ->
aclient_write_okA a_alayout LB FS iv -> fst iv <= x < snd iv -> fp_RFake FS0 RE X x -> False.
Proof.
intros LB FS iv x PB PF CW Hx FP. pose proof (rl_objs _ fs_obj) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
destruct FP as [[H NB]|[H NS]].
- destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1 C2]]]]]].
+ fin. + specialize (C x Hx). cbn [ala_client_data a_alayout] in C. unfold a_client_data in C. clear -C H K. fin.
+ assert (LU : in_live_user LB0 x) by (exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| lia]).
destruct (live_user_where x LU) as (p & A & n & Hb' & Hx' & [(c & i & Ht & S1 & S2)|(e & He & _ & S1 & S2)]).
* pose proof (slot_prim c i _ Ht) as (P1 & P2 & _). fin.
* destruct (sec_facts e He) as (_ & _ & _ & _ & _ & _ & _ & _ & F). pose proof (proj1 (List.Forall_forall _ _) F _ fs_obj) as D. fin.
+ apply NB. exists f. split; [eapply Permutation_in; [exact PF| exact Hf]| lia].
+ assert (SHD : in_fframe_shadow FS0 x) by (exists f; split; [eapply Permutation_in; [exact PF| exact Hf]| lia]).
apply frame_shadow_where in SHD. apply in_sh_band in SHD; [fin| lia| unfold A_FS_MAP_SIZE; lia| exact (proj1 K)| exact CE].
+ rewrite SH_247 in C2. pose proof SH_band. fin.
- pose proof (in_sh_band (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear -AL; Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) (proj1 K) CE H) as B.
pose proof (in_sh_bounds (ae_fs_base RE) A_FS_MAP_SIZE x ltac:(clear -AL; Z.div_mod_to_equations; lia) ltac:(unfold A_FS_MAP_SIZE; lia) H) as SB2.
pose proof (SH_mono (ae_fs_base RE + A_FS_MAP_SIZE) band_lo CE) as SB3. rewrite !SH_eq in SB2, SB3. pose proof K as [Ka Kb].
destruct CW as [C|[C|[(b & Hb & B1 & B2)|[(f & Hf & F1 & F2)|[(f & Hf & F1 & F2)|[C1 C2]]]]]].
+ clear -C Hx SB2 SB3. lia.
+ specialize (C x Hx). cbn [ala_client_data a_alayout] in C. clear -C SB2 Ka Kb.
unfold a_client_data, iv_disjoint, a_ro_lo, a_data_hi, kLowEnd, KHI, A_FS_MAP_SIZE in *. cbn [fst snd] in *.
Z.div_mod_to_equations. lia.
+ assert (LU : in_live_user LB0 x) by (exists b; split; [eapply Permutation_in; [exact PB| exact Hb]| lia]).
apply live_user_heap in LU. clear -LU B. unfold kLowEnd, KHI in *. lia.
+ assert (Hf0 : In f FS0) by (eapply Permutation_in; [exact PF| exact Hf]).
pose proof (gc_ff_range a LB0 FS0 G RE X GC f Hf0) as (R1 & R2 & R3 & R4 & R5). clear -R4 F1 F2 Hx B.
unfold kLowEnd, KHI in *. lia.
+ apply NS. exists f. split; [eapply Permutation_in; [exact PF| exact Hf]| lia].
+ clear -C1 C2 Hx SB2 SB3. rewrite SH_247 in C2. rewrite SH_eq in C1. lia.
Qed.
End Zones.

Lemma Permutation_filter {A} (f : A -> bool) : forall l l', Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
intros l l' P. induction P as [|x l l' P IH|x y l|l l' l'' P1 IH1 P2 IH2].
- constructor.
- cbn. destruct (f x); [apply perm_skip; exact IH| exact IH].
- cbn. destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
- eapply Permutation_trans; eassumption.
Qed.

Lemma outside_intro : forall W x, (forall lo hi, In (lo, hi) W -> ~ (lo <= x < hi)) -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|].
split; [apply H; left; reflexivity|]. apply IH. intros lo' hi' Hin. apply H. right; exact Hin.
Qed.

Lemma gcons_ff_sub {BAND : Band} : forall a LB FS FS' G RE X,
gcons a LB FS G RE X -> (forall f, In f FS' -> In f FS) -> gcons a LB FS' G RE X.
Proof.
intros a LB FS FS' G RE X GC SUB.
destruct GC as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A8b & A9 & A10 & A11 & A12 & A13).
repeat (split; [assumption|]). split.
- intros f Hf. apply A12. apply SUB. exact Hf.
- intros f1 f2 H1 H2 NE. apply A13; [apply SUB; exact H1| apply SUB; exact H2| exact NE].
Qed.

Section ARunDef.
Context {BAND : Band}.
Variable C : arun_components.

Definition ARUN (s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (m : mem) : Prop :=
exists X G LB0 FS0,
Permutation LB LB0 /\ Permutation FS FS0 /\ gcons (ps_a s) LB0 FS0 G RE X
/\ ac_RTconst C RE X m /\ ac_RStats C RE X m /\ ac_RPrim C (ps_a s) G RE X m
/\ ac_RChunks C (ps_a s) LB0 G RE X m /\ ac_RSec C (ps_a s) LB0 RE X m /\ ac_RQuar C (ps_a s) LB0 G RE X m
/\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Definition ARUNX (a : AState) (LB0 : list ablock) (FS0 : list fframe) (G : ghost) (RE : aentry) (X : rlay) (m : mem) : Prop :=
gcons a LB0 FS0 G RE X
/\ ac_RTconst C RE X m /\ ac_RStats C RE X m /\ ac_RPrim C a G RE X m
/\ ac_RChunks C a LB0 G RE X m /\ ac_RSec C a LB0 RE X m /\ ac_RQuar C a LB0 G RE X m
/\ ac_RDepot C RE X m /\ ac_RFake C FS0 RE X m.

Lemma ARUN_open : forall s LB FS RE m, ARUN s LB FS RE m ->
exists X G LB0 FS0, Permutation LB LB0 /\ Permutation FS FS0 /\ ARUNX (ps_a s) LB0 FS0 G RE X m.
Proof. intros s LB FS RE m (X & G & LB0 & FS0 & PB & PF & H). exists X, G, LB0, FS0. split; [exact PB|]. split; [exact PF|]. exact H. Qed.

Lemma ARUN_close : forall s LB FS RE m X G LB0 FS0,
Permutation LB LB0 -> Permutation FS FS0 -> ARUNX (ps_a s) LB0 FS0 G RE X m -> ARUN s LB FS RE m.
Proof. intros s LB FS RE m X G LB0 FS0 PB PF H. exists X, G, LB0, FS0. split; [exact PB|]. split; [exact PF|]. exact H. Qed.

Lemma ARUN_ext : forall s s' LB FS RE m, ARUN s LB FS RE m -> ps_a s' = ps_a s -> ARUN s' LB FS RE m.
Proof. intros s s' LB FS RE m H E. unfold ARUN in *. rewrite E. exact H. Qed.

Lemma ARUN_perm : forall s LB LB' FS FS' RE m, ARUN s LB FS RE m -> Permutation LB LB' -> Permutation FS FS' -> ARUN s LB' FS' RE m.
Proof.
intros s LB LB' FS FS' RE m (X & G & LB0 & FS0 & PB & PF & H) P1 P2. exists X, G, LB0, FS0.
split; [eapply Permutation_trans; [apply Permutation_sym; exact P1| exact PB]|].
split; [eapply Permutation_trans; [apply Permutation_sym; exact P2| exact PF]|]. exact H.
Qed.

Lemma ARUNX_agree : forall a LB0 FS0 G RE X m m',
ARUNX a LB0 FS0 G RE X m -> wmono asegs m m' ->
agree_on asegs (fp_RTconst RE X) m m' -> agree_on asegs (fp_RStats RE X) m m' -> agree_on asegs (fp_RPrim G RE X) m m' ->
agree_on asegs (fp_RChunks a LB0 G RE X) m m' -> agree_on asegs (fp_RSec a RE X) m m' ->
agree_on asegs (fp_RQuar a LB0 G RE X) m m' -> agree_on asegs (fp_RDepot RE X) m m' ->
agree_on asegs (fp_RFake FS0 RE X) m m' ->
ARUNX a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) WM A1 A2 A3 A4 A5 A6 A7 A8.
split; [exact GC|].
split; [eapply (ac_RTconst_frame C); [exact R1| exact WM| exact A1]|].
split; [eapply (ac_RStats_frame C); [exact R2| exact WM| exact A2]|].
split; [eapply (ac_RPrim_frame C); [exact R3| exact WM| exact A3]|].
split; [eapply (ac_RChunks_frame C); [exact R4| exact WM| exact A4]|].
split; [eapply (ac_RSec_frame C); [exact R5| exact WM| exact A5]|].
split; [eapply (ac_RQuar_frame C); [exact R6| exact WM| exact A6]|].
split; [eapply (ac_RDepot_frame C); [exact R7| exact WM| exact A7]|].
eapply (ac_RFake_frame C); [exact R8| exact WM| exact A8].
Qed.

Lemma ARUNX_munch : forall a LB0 FS0 G RE X m m' W,
ARUNX a LB0 FS0 G RE X m -> munch W m m' -> wmono asegs m m' ->
(forall lo hi x, In (lo, hi) W -> lo <= x < hi -> czone LB0 RE x /\ ~ fp_RFake FS0 RE X x) ->
ARUNX a LB0 FS0 G RE X m'.
Proof.
intros a LB0 FS0 G RE X m m' W AX MU WM HW. pose proof (proj1 AX) as GC.
assert (AG : forall P : Z -> Prop, (forall x, P x -> czone LB0 RE x -> False) -> agree_on asegs P m m').
{ intros P HP. eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro.
intros lo hi Hin Hx. destruct (HW lo hi x Hin Hx) as [CZ _]. exact (HP x Px CZ). }
eapply ARUNX_agree; [exact AX| exact WM| ..].
- apply AG. intros x. apply (fp_RTconst_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RStats_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RPrim_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RChunks_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RSec_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RQuar_cz a LB0 FS0 G RE X GC).
- apply AG. intros x. apply (fp_RDepot_cz a LB0 FS0 G RE X GC).
- eapply agree_on_of_munch; [exact MU| exact WM|]. intros x Px _. apply outside_intro.
intros lo hi Hin Hx. destruct (HW lo hi x Hin Hx) as [_ NF]. exact (NF Px).
Qed.

Lemma ARUN_frame : forall s LB FS RE m m' W,
ARUN s LB FS RE m -> munch W m m' -> wmono asegs m m' -> Forall (aclient_write_okA a_alayout LB FS) W ->
ARUN s LB FS RE m'.
Proof.
intros s LB FS RE m m' W AR MU WM FW. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
eapply ARUN_close; [exact PB| exact PF|]. eapply ARUNX_munch; [exact AX| exact MU| exact WM|].
intros lo hi x Hin Hx. pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW.
split.
- eapply (client_czone _ _ _ _ _ _ (proj1 AX) LB FS (lo, hi) x PB PF CW). cbn [fst snd]. lia.
- intros FP. eapply (fp_RFake_client _ _ _ _ _ _ (proj1 AX) LB FS (lo, hi) x PB PF CW); [cbn [fst snd]; lia| exact FP].
Qed.

Lemma ARUN_block_range : forall s LB FS RE m b, ARUN s LB FS RE m -> In b LB -> ablock_rangeA (ablk_addr b) (ablk_size b).
Proof.
intros s LB FS RE m [[p A] n] AR Hb. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. cbn [ablk_addr ablk_size fst snd].
assert (Hb0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hb]).
pose proof kconsts as (_ & KO & KS & K32 & KP & KU & _).
destruct (live_block_geom _ _ _ _ _ _ GC p A n Hb0) as (Hn & AL & [(c & i & Ht & _ & _ & _ & CT)|(e & He & _ & Hr & HA & CT)]);
unfold blk_container in CT; unfold ablock_rangeA.
- pose proof (slot_prim _ _ _ _ _ _ GC c i _ Ht) as (P1 & P2 & _ & _ & C1 & R1 & R2 & _). pose proof (rl_prim _ _ _ _ _ _ GC) as (_ & PK & PH & _).
pose proof (region_in_prim RE c C1) as (Q1 & Q2 & Q3 & Q4). rewrite KO, KS in *. fin.
- pose proof (sec_entry_facts _ _ _ _ _ _ GC e He) as (E1 & E2 & E3 & E4 & E5 & E6 & _).
pose proof (sec_map_size_ge (se_req e) ltac:(lia) E5) as [M1 M2]. pose proof (sec_req_facts (se_req e) ltac:(lia) E5) as [_ GE].
rewrite <- E4 in M1. subst n. fin.
Qed.

Lemma ARUN_block_small : forall s LB FS RE m b, ARUN s LB FS RE m -> In b LB -> ablk_size b <= 2^26.
Proof.
intros s LB FS RE m [[p A] n] AR Hb. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
cbn [ablk_size snd]. apply (gc_block_small _ _ _ _ _ _ (proj1 AX) p A n). eapply Permutation_in; [exact PB| exact Hb].
Qed.

Lemma ARUN_blocks_disjoint : forall s LB FS RE m b1 b2,
ARUN s LB FS RE m -> In b1 LB -> In b2 LB -> ablk_id b1 <> ablk_id b2 ->
ablk_addr b1 + Z.max (ablk_size b1) 1 <= ablk_addr b2 \/ ablk_addr b2 + Z.max (ablk_size b2) 1 <= ablk_addr b1.
Proof.
intros s LB FS RE m [[p1 A1] n1] [[p2 A2] n2] AR H1 H2 NE. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. cbn [ablk_addr ablk_size ablk_id fst snd] in *.
assert (H10 : In (p1, A1, n1) LB0) by (eapply Permutation_in; [exact PB| exact H1]).
assert (H20 : In (p2, A2, n2) LB0) by (eapply Permutation_in; [exact PB| exact H2]).
pose proof kconsts as (_ & KO & KS & K32 & KP & _).
destruct (live_block_geom _ _ _ _ _ _ GC p1 A1 n1 H10) as (Hn1 & AL1 & [(c1 & i1 & T1 & _ & P1 & _ & CT1)|(e1 & E1 & P1 & R1 & _ & CT1)]);
destruct (live_block_geom _ _ _ _ _ _ GC p2 A2 n2 H20) as (Hn2 & AL2 & [(c2 & i2 & T2 & _ & P2 & _ & CT2)|(e2 & E2 & P2 & R2 & _ & CT2)]);
unfold blk_container in CT1, CT2.
-
destruct (decide (c1 = c2 /\ i1 = i2)) as [[-> ->]|NS].
+ exfalso. rewrite T1 in T2. inversion T2. subst. apply NE. reflexivity.
+ pose proof (slots_disjoint _ _ _ _ _ _ GC c1 i1 _ c2 i2 _ T1 T2 ltac:(lia)). lia.
-
pose proof (slot_prim _ _ _ _ _ _ GC c1 i1 _ T1) as (Q1 & Q2 & _).
pose proof (sec_entry_facts _ _ _ _ _ _ GC e2 E2) as (_ & _ & _ & _ & _ & _ & DP & _). fin.
- pose proof (slot_prim _ _ _ _ _ _ GC c2 i2 _ T2) as (Q1 & Q2 & _).
pose proof (sec_entry_facts _ _ _ _ _ _ GC e1 E1) as (_ & _ & _ & _ & _ & _ & DP & _). fin.
-
destruct (decide (se_beg e1 = se_beg e2)) as [EQ|NEQ].
+ exfalso. pose proof (NoDup_map_In_inj se_beg (as_reg (ps_a s)) e1 e2 (gc_sec_nodup _ _ _ _ _ _ GC) E1 E2 EQ) as ->.
apply NE. subst. congruence.
+ pose proof (pairwise_disjoint_map_In (fun e => (se_beg e, se_size e)) (as_reg (ps_a s)) e1 e2
(gc_sec_disj _ _ _ _ _ _ GC) E1 E2 ltac:(intros EQ; apply NEQ; exact (f_equal fst EQ))) as D. fin.
Qed.

Lemma ARUN_blocks_nodup : forall s LB FS RE m, ARUN s LB FS RE m -> List.NoDup (map ablk_id LB).
Proof.
intros s LB FS RE m AR. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PB|]. exact (gc_nodup _ _ _ _ _ _ (proj1 AX)).
Qed.

Lemma ARUN_block_shadow : forall s LB FS RE m p A n, ARUN s LB FS RE m -> In (p, A, n) LB -> blk_shadow asegs m A n.
Proof.
intros s LB FS RE m p A n AR Hb. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & _ & _ & _ & RC & _). eapply (ac_RChunks_shadow C); [exact GC| exact RC|].
eapply Permutation_in; [exact PB| exact Hb].
Qed.

Lemma ARUN_fframe_range : forall s LB FS RE m f, ARUN s LB FS RE m -> In f FS -> fframe_rangeA RE (ff_cls f) (ff_addr f).
Proof.
intros s LB FS RE m f AR Hf. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
apply (gc_ff_range _ _ _ _ _ _ (proj1 AX)). eapply Permutation_in; [exact PF| exact Hf].
Qed.

Lemma ARUN_fframes_disjoint : forall s LB FS RE m f1 f2,
ARUN s LB FS RE m -> In f1 FS -> In f2 FS -> ff_addr f1 <> ff_addr f2 ->
ff_addr f1 + ff_size (ff_cls f1) <= ff_addr f2 \/ ff_addr f2 + ff_size (ff_cls f2) <= ff_addr f1.
Proof.
intros s LB FS RE m f1 f2 AR H1 H2 NE. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
apply (gc_ff_disj _ _ _ _ _ _ (proj1 AX)); [eapply Permutation_in; [exact PF| exact H1]| eapply Permutation_in; [exact PF| exact H2]| exact NE].
Qed.

Lemma ARUN_fframe_block_disjoint : forall s LB FS RE m f b,
ARUN s LB FS RE m -> In f FS -> In b LB ->
ff_addr f + ff_size (ff_cls f) <= ablk_addr b \/ ablk_addr b + ablk_size b <= ff_addr f.
Proof.
intros s LB FS RE m f [[p A] n] AR Hf Hb. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. cbn [ablk_addr ablk_size fst snd].
pose proof (gc_ff_range _ _ _ _ _ _ GC f ltac:(eapply Permutation_in; [exact PF| exact Hf])) as (R1 & R2 & R3 & R4 & R5).
assert (Hb0 : In (p, A, n) LB0) by (eapply Permutation_in; [exact PB| exact Hb]).
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CE & DP & DQ); cbn [fst snd] in AL, K, CE.
destruct (live_block_geom _ _ _ _ _ _ GC p A n Hb0) as (Hn & ALB & [(c & i & T1 & _ & _ & _ & CT)|(e & E1 & _ & _ & _ & CT)]);
unfold blk_container in CT.
- pose proof (slot_prim _ _ _ _ _ _ GC c i _ T1) as (Q1 & Q2 & _). fin.
- destruct (sec_entry_facts _ _ _ _ _ _ GC e E1) as (_ & _ & _ & _ & _ & _ & _ & _ & F).
pose proof (proj1 (List.Forall_forall _ _) F _ (fs_obj RE X)) as D. fin.
Qed.

Lemma ARUN_entry_facts : forall s LB FS RE m, ARUN s LB FS RE m ->
ae_sp0 RE - 0xa0 <= ae_stack_top RE < ae_sp0 RE + 0x8000 /\ ae_stack_top RE mod 4096 = 0
/\ appr (ae_fs_base RE) 0xb09000 /\ ae_fs_base RE + 0xb09000 <= band_lo
/\ band_lo + 0x800000 <= ae_sp0 RE
/\ ae_sp0 RE <= 0x800000000000.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof (proj1 AX) as GC. destruct (gc_rlay _ _ _ _ _ _ GC) as (E1 & E2 & E3 & E4 & _).
change (2^47) with 0x800000000000 in E4.
pose proof (rl_objs _ _ _ _ _ _ GC _ (fs_obj RE X)) as (AL & K & CE & _); cbn [fst snd] in AL, K, CE.
unfold A_FS_MAP_SIZE in *. repeat split; try assumption; try lia.
Qed.

Lemma ARUN_shadow_base : forall s LB FS RE m, ARUN s LB FS RE m -> shadow_base asegs m.
Proof.
intros s LB FS RE m AR. destruct (ARUN_open _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
exact (ac_RTconst_shadow C RE X m (proj1 (proj2 AX))).
Qed.

End ARunDef.
