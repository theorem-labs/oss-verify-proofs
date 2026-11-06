(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

Lemma is_prefix_app_r {A} : forall (l m a : list A),
  is_prefix a l -> is_prefix a (l ++ m).
Proof.
  induction l as [|x l IH]; intros m a H.
  - destruct a; [apply is_prefix_nil | cbn in H; contradiction].
  - destruct a as [|y a]; cbn in *; [exact I|].
    destruct H as [-> H]. split; [reflexivity | apply IH; exact H].
Qed.

Lemma is_prefix_app_split {A} : forall (l a b : list A),
  is_prefix b (l ++ a) ->
  is_prefix b l \/ exists b', b = l ++ b' /\ is_prefix b' a.
Proof.
  induction l as [|x l IH]; intros a b H.
  - right. exists b. split; [reflexivity | exact H].
  - destruct b as [|y b]; cbn in H; [left; exact I|].
    destruct H as [-> H]. destruct (IH a b H) as [Hp | (b' & -> & Hp)].
    + left. cbn. split; [reflexivity | exact Hp].
    + right. exists b'. split; [reflexivity | exact Hp].
Qed.

Lemma is_prefix_nil_r {A} : forall (a : list A), is_prefix a [] -> a = [].
Proof. destruct a; cbn; [reflexivity | contradiction]. Qed.

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn;
    [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TSet := list event -> Prop.

Definition t_eq (T T' : TSet) : Prop := forall tr, T tr <-> T' tr.

Lemma t_eq_refl : forall T, t_eq T T.
Proof. intros T tr. split; intro H; exact H. Qed.
Lemma t_eq_sym : forall T T', t_eq T T' -> t_eq T' T.
Proof. intros T T' H tr. split; intro Ht; apply H; exact Ht. Qed.
Lemma t_eq_trans : forall T1 T2 T3, t_eq T1 T2 -> t_eq T2 T3 -> t_eq T1 T3.
Proof.
  intros T1 T2 T3 H12 H23 tr. split; intro Ht.
  - apply H23, H12, Ht.
  - apply H12, H23, Ht.
Qed.

(* [comment removed for export] *)
Definition t_nil : TSet := fun tr => tr = [].

(* [comment removed for export] *)
Definition t_emit (evs : list event) (T : TSet) : TSet :=
  fun tr => is_prefix tr evs \/ exists tr', tr = evs ++ tr' /\ T tr'.

(* [comment removed for export] *)
Definition t_alt {I : Type} (f : I -> TSet) : TSet := fun tr => exists i, f i tr.

(* [comment removed for export] *)
Definition t_alt2 (A B : TSet) : TSet := fun tr => A tr \/ B tr.
Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).

(* [comment removed for export] *)
Definition t_exit (code : word) (fs : Fs.Fs) : TSet :=
  t_emit [ExitEv code fs] t_nil.

(* [comment removed for export] *)
Definition wr_index (buf : list byte) : Type :=
  {n : nat | (1 <= n)%nat /\ (n <= length buf)%nat}.

Definition wr_full (buf : list byte) (Hnb : (1 <= length buf)%nat)
    : wr_index buf :=
  exist _ (length buf) (conj Hnb (Nat.le_refl _)).

(* [comment removed for export] *)
Definition t_write_ch (ch : word) (buf : list byte) (T : TSet) : TSet :=
  t_alt (fun i : wr_index buf =>
           t_emit (map (WriteEv ch) (firstn (proj1_sig i) buf)) T).

Definition t_writes_ch_pick (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (t_write_ch ch) T bufs.

(* [comment removed for export] *)
Definition t_writes_ch (ch : word) (bufs : list (list byte)) (T : TSet) : TSet :=
  fold_right (fun buf acc => t_emit (map (WriteEv ch) buf) acc) T bufs.

Lemma t_writes_ch_cons : forall ch buf bufs T,
  t_writes_ch ch (buf :: bufs) T
  = t_emit (map (WriteEv ch) buf) (t_writes_ch ch bufs T).
Proof. reflexivity. Qed.

Lemma t_writes_ch_nil : forall ch T, t_writes_ch ch [] T = T.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_eq : forall T, T [] -> t_eq (t_emit [] T) T.
Proof.
  intros T H0 tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [apply is_prefix_nil_r in Hp; subst tr; exact H0 | exact HT].
  - intro HT. right. exists tr. split; [reflexivity | exact HT].
Qed.

Lemma t_emit_has_nil : forall e T, t_emit e T [].
Proof. intros e T. left. apply is_prefix_nil. Qed.

Lemma t_nil_has_nil : t_nil []. Proof. reflexivity. Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof. intros A B H. left. exact H. Qed.

Lemma t_alt2_has_nil_r : forall A B : TSet, B [] -> t_alt2 A B [].
Proof. intros A B H. right. exact H. Qed.

Lemma t_alt_has_nil : forall (I : Type) (f : I -> TSet) (i : I), f i [] -> t_alt f [].
Proof. intros I f i H. exists i. exact H. Qed.

Lemma t_writes_ch_has_nil : forall ch bufs T, T [] -> t_writes_ch ch bufs T [].
Proof.
  intros ch [|b bs] T HT; cbn [t_writes_ch fold_right];
    [exact HT | apply t_emit_has_nil].
Qed.

Lemma t_alt_unit : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

Lemma t_alt_const : forall (I : Type) (i0 : I) (T : TSet),
  t_eq (t_alt (fun _ : I => T)) T.
Proof.
  intros I i0 T tr. split; [intros [_ H]; exact H | intro H; exists i0; exact H].
Qed.

Lemma t_alt_emit_nil : forall (I : Type) (f : I -> TSet),
  (forall i, f i []) -> t_eq (t_alt (fun i => t_emit [] (f i))) (t_alt f).
Proof.
  intros I f H tr. split.
  - intros [i Hi]. exists i. exact (proj1 (t_emit_nil_eq (f i) (H i) tr) Hi).
  - intros [i Hi]. exists i. exact (proj2 (t_emit_nil_eq (f i) (H i) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma t_alt_as_alt2 : forall (IA IB : Type) (f : IA + IB -> TSet),
  t_eq (t_alt f) (t_alt2 (t_alt (fun a => f (inl a))) (t_alt (fun b => f (inr b)))).
Proof.
  intros IA IB f tr. unfold t_alt, t_alt2. split.
  - intros [[a | b] H]; [left; exists a; exact H | right; exists b; exact H].
  - intros [[a H] | [b H]]; [exists (inl a); exact H | exists (inr b); exact H].
Qed.

Lemma t_emit_app : forall (a b : list event) (T : TSet),
  t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. split; [reflexivity | exact HT].
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. split; [rewrite app_assoc; reflexivity | exact HT].
Qed.

Lemma t_emit_congr : forall (e : list event) (T T' : TSet),
  t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)];
      [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
  - intros [Hp | (tr' & -> & HT)];
      [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.

Lemma t_emit_app3 : forall (a b c : list event) (T : TSet),
  t_eq (t_emit a (t_emit b (t_emit c T))) (t_emit (a ++ b ++ c) T).
Proof.
  intros a b c T. apply t_eq_sym.
  eapply t_eq_trans; [apply t_emit_app|].
  apply t_emit_congr. apply t_emit_app.
Qed.

Lemma t_alt_congr : forall (I : Type) (f g : I -> TSet),
  (forall i, t_eq (f i) (g i)) -> t_eq (t_alt f) (t_alt g).
Proof.
  intros I f g H tr. unfold t_alt. split; intros [i Hi]; exists i; apply (H i); exact Hi.
Qed.

Lemma t_alt2_congr : forall A A' B B' : TSet,
  t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
  intros A A' B B' HA HB tr. unfold t_alt2.
  split; (intros [H | H]; [left; apply HA | right; apply HB]; exact H).
Qed.

Lemma t_alt2_comm : forall A B : TSet, t_eq (t_alt2 A B) (t_alt2 B A).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.

Lemma t_alt2_idem : forall A : TSet, t_eq (t_alt2 A A) A.
Proof. intros A tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_idem : forall A : TSet, t_eq (t_alt3 A A A) A.
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.

Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.

Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [-> | HT]; [exact H0 | exact HT].
  - intro HT. right. exact HT.
Qed.

Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [HT | ->]; [exact HT | exact H0].
  - intro HT. left. exact HT.
Qed.

(* [comment removed for export] *)
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
  intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
  - intros [[Hp | (tr' & -> & ->)] | H].
    + left. exact Hp.
    + right. exists []. split; [reflexivity | exact H0].
    + exact H.
  - intros H. right. exact H.
Qed.

(* [comment removed for export] *)
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
  intros e A B tr. unfold t_emit, t_alt2. split.
  - intros [Hp | (tr' & -> & [HA | HB])].
    + left. left. exact Hp.
    + left. right. exists tr'. auto.
    + right. right. exists tr'. auto.
  - intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
    + left. exact Hp.
    + right. exists tr'. auto.
    + left. exact Hp.
    + right. exists tr'. auto.
Qed.

Lemma t_emit_alt_distr : forall (I : Type) (i0 : I) (e : list event) (f : I -> TSet),
  t_eq (t_emit e (t_alt f)) (t_alt (fun i => t_emit e (f i))).
Proof.
  intros I i0 e f tr. unfold t_emit, t_alt. split.
  - intros [Hp | (tr' & -> & (i & Hi))].
    + exists i0. left. exact Hp.
    + exists i. right. exists tr'. auto.
  - intros (i & [Hp | (tr' & -> & Hi)]).
    + left. exact Hp.
    + right. exists tr'. split; [reflexivity | exists i; exact Hi].
Qed.

(* [comment removed for export] *)
Lemma t_alt_wall : forall (ch : word) (rest : list byte) (T : TSet),
  T [] -> (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T HT Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

(* [comment removed for export] *)

Definition pclosed (T : TSet) : Prop :=
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.

Lemma pclosed_nil : pclosed t_nil.
Proof.
  intros tr tr' H Hp. unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
Qed.

Lemma pclosed_emit : forall e T, pclosed T -> pclosed (t_emit e T).
Proof.
  intros e T HT tr tr' [Hpre | (tr0 & -> & HT0)] Hp.
  - left. eapply is_prefix_trans; eauto.
  - apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
    + left. exact Hp.
    + right. exists tr0'. split; [reflexivity | eapply HT; eauto].
Qed.

Lemma pclosed_alt : forall (I : Type) (f : I -> TSet),
  (forall i, pclosed (f i)) -> pclosed (t_alt f).
Proof. intros I f H tr tr' [i Hi] Hp. exists i. eapply H; eauto. Qed.

Lemma pclosed_alt2 : forall A B, pclosed A -> pclosed B -> pclosed (t_alt2 A B).
Proof.
  intros A B HA HB tr tr' [H | H] Hp; [left; eapply HA | right; eapply HB]; eauto.
Qed.

Lemma pclosed_exit : forall code fs, pclosed (t_exit code fs).
Proof. intros. apply pclosed_emit, pclosed_nil. Qed.

Lemma pclosed_t_eq : forall T T', t_eq T T' -> pclosed T -> pclosed T'.
Proof. intros T T' Heq H tr tr' HT Hp. apply Heq. eapply H; [apply Heq; exact HT | exact Hp]. Qed.

(* [comment removed for export] *)
Lemma pclosed_has_nil : forall T tr, pclosed T -> T tr -> T [].
Proof. intros T tr H HT. eapply H; [exact HT | apply is_prefix_nil]. Qed.
