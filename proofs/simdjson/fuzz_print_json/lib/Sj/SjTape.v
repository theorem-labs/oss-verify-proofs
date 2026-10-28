(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition t_root : Z := 114.
Definition t_arr : Z := 91.       Definition t_arr_end : Z := 93.
Definition t_obj : Z := 123.      Definition t_obj_end : Z := 125.
Definition t_str : Z := 34.
Definition t_i64 : Z := 108.      Definition t_u64 : Z := 117.         Definition t_dbl : Z := 100.
Definition t_true : Z := 116.     Definition t_false : Z := 102.       Definition t_null : Z := 110.

Definition CNT_MAX : Z := 16777215.
Definition TAPE_MAX_DEPTH : nat := 1024.

Definition tword (t v : Z) : Z := t * 2^56 + v.
Definition cword (t nxt cv : Z) : Z := tword t (nxt + cv * 2^32).

Definition ttype (w : Z) : Z := w / 2^56.
Definition tval (w : Z) : Z := w mod 2^56.
Definition tnext (w : Z) : Z := w mod 2^32.
Definition tcount (w : Z) : Z := (w / 2^32) mod 2^24.

Lemma ttype_tword : forall t v, 0 <= v < 2^56 -> ttype (tword t v) = t.
Proof. intros t v H. unfold ttype, tword. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. Qed.

Lemma tval_tword : forall t v, 0 <= v < 2^56 -> tval (tword t v) = v.
Proof.
  intros t v H. unfold tval, tword. rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. exact H.
Qed.

Lemma cword_pay_range : forall nxt cv, 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX -> 0 <= nxt + cv * 2^32 < 2^56.
Proof. intros nxt cv H1 H2. unfold CNT_MAX in *. lia. Qed.

Lemma ttype_cword : forall t nxt cv, 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX -> ttype (cword t nxt cv) = t.
Proof. intros. unfold cword. apply ttype_tword. apply cword_pay_range; assumption. Qed.

Lemma tnext_cword : forall t nxt cv, 0 <= nxt < 2^32 -> tnext (cword t nxt cv) = nxt.
Proof.
  intros t nxt cv H. unfold tnext, cword, tword.
  replace (t * 2^56 + (nxt + cv * 2^32)) with (nxt + (t * 2^24 + cv) * 2^32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. exact H.
Qed.

Lemma tcount_cword : forall t nxt cv, 0 <= nxt < 2^32 -> 0 <= cv <= CNT_MAX -> tcount (cword t nxt cv) = cv.
Proof.
  intros t nxt cv H1 H2. unfold tcount, cword, tword, CNT_MAX in *.
  replace (t * 2^56 + (nxt + cv * 2^32)) with (nxt + (t * 2^24 + cv) * 2^32) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small nxt) by lia.
  replace (0 + (t * 2^24 + cv)) with (cv + t * 2^24) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Definition ck_exact (c cv : Z) : Prop := cv = Z.min c CNT_MAX.
Definition ck_any (c cv : Z) : Prop := 0 <= cv <= CNT_MAX.

Inductive tiles (P : Z -> Z -> Prop) : Z -> Z -> Z -> Prop :=
| tiles_nil : forall i, tiles P i i 0
| tiles_cons : forall i j e c, P i j -> tiles P j e c -> tiles P i e (c + 1).

Lemma tiles_snoc : forall P i j e c, tiles P i j c -> P j e -> tiles P i e (c + 1).
Proof.
  intros P i j e c H. induction H as [i|i j0 e0 c0 Hp Ht IH]; intros Hl.
  - replace (0 + 1) with (0 + 1) by lia. apply (tiles_cons P i e e 0 Hl). apply tiles_nil.
  - apply (tiles_cons P i j0 e (c0 + 1) Hp). apply IH. exact Hl.
Qed.

Lemma tiles_impl : forall (P Q : Z -> Z -> Prop) i e c,
  (forall a b, i <= a -> b <= e -> P a b -> Q a b) -> (forall a b, P a b -> a < b) -> tiles P i e c -> tiles Q i e c.
Proof.
  intros P Q i e c HPQ Hlt H. revert HPQ. induction H as [i|i j e c Hp Ht IH]; intros HPQ.
  - apply tiles_nil.
  - assert (Hje : j <= e).
    { clear - Ht Hlt. induction Ht as [|a b e c Hp _ IH]; [lia|]. pose proof (Hlt _ _ Hp). lia. }
    pose proof (Hlt _ _ Hp).
    apply (tiles_cons Q i j e c); [apply HPQ; [lia|exact Hje|exact Hp]|]. apply IH. intros a b Ha Hb. apply HPQ; lia.
Qed.

Section Progress.
  Variable P : Z -> Z -> Prop.
  Hypothesis Plt : forall i j, P i j -> i < j.

  Lemma tiles_le : forall i e c, tiles P i e c -> i <= e /\ 0 <= c <= e - i.
  Proof using Plt. intros i e c H. induction H as [|i j e c Hp _ IH]; [lia|]. specialize (Plt _ _ Hp). lia. Qed.

  Lemma tiles_next : forall i e c, tiles P i e c -> i <> e ->
    exists j, P i j /\ j <= e /\ tiles P j e (c - 1).
  Proof using Plt.
    intros i e c H Hne. destruct H as [|i j e c Hp Ht]; [congruence|].
    exists j. split; [exact Hp|]. split; [apply (tiles_le _ _ _ Ht)|]. replace (c + 1 - 1) with c by lia. exact Ht.
  Qed.

  Lemma tiles_end : forall e c, tiles P e e c -> c = 0.
  Proof using Plt. intros e c H. pose proof (tiles_le _ _ _ H). lia. Qed.
End Progress.

Section Tape.
  Variable T : Z -> Z.
  Variable S : Z -> Z.
  Variable sn : Z.
  Variable CK : Z -> Z -> Prop.

  Definition le32 (o : Z) : Z := S o + 2^8 * S (o + 1) + 2^16 * S (o + 2) + 2^24 * S (o + 3).

  Definition str_at (o l : Z) : Prop :=
    0 <= o /\ 0 <= l /\ o + l + 5 <= sn /\ le32 o = l /\ S (o + 4 + l) = 0.

  Definition is_str (i : Z) : Prop := exists o l, T i = tword t_str o /\ str_at o l.

  Definition scalar (i j : Z) : Prop :=
    (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0)) \/
    (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0)) \/
    (j = i + 1 /\ is_str i).

  Definition field (P : Z -> Z -> Prop) (i j : Z) : Prop := is_str i /\ P (i + 1) j.

  Definition container (P : Z -> Z -> Prop) (i j : Z) : Prop :=
    exists e c cv, j = e + 1 /\ CK c cv /\
      ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tiles P (i + 1) e c) \/
       (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tiles (field P) (i + 1) e c)).

  Fixpoint elem (d : nat) (i j : Z) : Prop :=
    scalar i j \/ match d with O => False | Datatypes.S d' => container (elem d') i j end.

  Definition tape_wf (n : Z) : Prop :=
    2 < n < 2^32 /\ 0 <= sn < 2^56 /\
    T 0 = tword t_root n /\ T (n - 1) = tword t_root 0 /\ elem TAPE_MAX_DEPTH 1 (n - 1).

  Lemma scalar_lt : forall i j, scalar i j -> i < j.
  Proof. intros i j [[-> _]|[[-> _]|[-> _]]]; lia. Qed.

  Lemma field_lt : forall (P : Z -> Z -> Prop), (forall i j, P i j -> i < j) -> forall i j, field P i j -> i < j.
  Proof. intros P HP i j [_ H]. specialize (HP _ _ H). lia. Qed.

  Lemma elem_lt : forall d i j, elem d i j -> i < j.
  Proof.
    induction d as [|d IH]; intros i j H; cbn [elem] in H.
    - destruct H as [H|[]]. apply scalar_lt; exact H.
    - destruct H as [H|(e & c & cv & -> & _ & [(_ & _ & Ht)|(_ & _ & Ht)])].
      + apply scalar_lt; exact H.
      + pose proof (tiles_le _ IH _ _ _ Ht). lia.
      + pose proof (tiles_le _ (field_lt _ IH) _ _ _ Ht). lia.
  Qed.

  Lemma elem_scalar : forall d i j, scalar i j -> elem d i j.
  Proof. intros [|d] i j H; cbn [elem]; left; exact H. Qed.

  Lemma elem_S : forall d i j, elem d i j -> elem (Datatypes.S d) i j.
  Proof.
    induction d as [|d IH]; intros i j H.
    - destruct H as [H|[]]. apply elem_scalar; exact H.
    - cbn [elem] in H. destruct H as [H|(e & c & cv & -> & Hck & Hc)]; [apply elem_scalar; exact H|].
      change (scalar i (e + 1) \/ container (elem (Datatypes.S d)) i (e + 1)). right.
      exists e, c, cv. split; [reflexivity|]. split; [exact Hck|].
      destruct Hc as [(H1 & H2 & Ht)|(H1 & H2 & Ht)]; [left|right]; (split; [exact H1|]); (split; [exact H2|]).
      + eapply tiles_impl; [| |exact Ht]; [intros a b _ _; apply IH | apply elem_lt].
      + eapply tiles_impl; [| |exact Ht]; [intros a b _ _ [Hs Hp]; split; [exact Hs|apply IH; exact Hp] | apply field_lt, elem_lt].
  Qed.

  Lemma elem_mono : forall d d' i j, (d <= d')%nat -> elem d i j -> elem d' i j.
  Proof. intros d d' i j Hle H. induction Hle as [|d' _ IH]; [exact H|]. apply elem_S; exact IH. Qed.

  Lemma elem_array : forall d i e c cv, CK c cv -> T i = cword t_arr (e + 1) cv -> T e = tword t_arr_end i ->
    tiles (elem d) (i + 1) e c -> elem (Datatypes.S d) i (e + 1).
  Proof. intros. cbn [elem]. right. exists e, c, cv. split; [reflexivity|]. split; [assumption|]. left. auto. Qed.

  Lemma elem_object : forall d i e c cv, CK c cv -> T i = cword t_obj (e + 1) cv -> T e = tword t_obj_end i ->
    tiles (field (elem d)) (i + 1) e c -> elem (Datatypes.S d) i (e + 1).
  Proof. intros. cbn [elem]. right. exists e, c, cv. split; [reflexivity|]. split; [assumption|]. right. auto. Qed.

  Hypothesis CK_range : forall c cv, CK c cv -> 0 <= cv <= CNT_MAX.
  Hypothesis Hsn : sn < 2^56.

  Lemma str_at_bounds : forall o l, str_at o l -> 0 <= o /\ 0 <= l /\ o + 4 + l < sn /\ le32 o = l /\ o < 2^56.
  Proof using Hsn. intros o l (H1 & H2 & H3 & H4 & _). lia. Qed.

  Lemma is_str_read : forall i, is_str i ->
    ttype (T i) = t_str /\ exists l, str_at (tval (T i)) l.
  Proof using Hsn.
    intros i (o & l & E & Hs). pose proof (str_at_bounds _ _ Hs) as (? & ? & ? & ? & ?). rewrite E.
    rewrite ttype_tword, tval_tword by lia. split; [reflexivity|]. exists l. exact Hs.
  Qed.

  Definition ty (i : Z) : Z := ttype (T i).

  Inductive elem_view (d : nat) (i j : Z) : Prop :=
  | ev_atom : (ty i = t_true \/ ty i = t_false \/ ty i = t_null) -> j = i + 1 -> elem_view d i j
  | ev_num : (ty i = t_i64 \/ ty i = t_u64 \/ ty i = t_dbl) -> j = i + 2 -> elem_view d i j
  | ev_str : ty i = t_str -> j = i + 1 -> is_str i -> elem_view d i j
  | ev_arr : forall d' e c, d = Datatypes.S d' -> ty i = t_arr -> j = e + 1 -> tnext (T i) = e + 1 -> T e = tword t_arr_end i ->
      tiles (elem d') (i + 1) e c -> elem_view d i j
  | ev_obj : forall d' e c, d = Datatypes.S d' -> ty i = t_obj -> j = e + 1 -> tnext (T i) = e + 1 -> T e = tword t_obj_end i ->
      tiles (field (elem d')) (i + 1) e c -> elem_view d i j.

  Lemma scalar_view : forall d i j, scalar i j -> elem_view d i j.
  Proof using Hsn.
    intros d i j [[-> H]|[[-> H]|[-> H]]].
    - apply ev_atom; [|reflexivity]. unfold ty. destruct H as [E|[E|E]]; rewrite E, ttype_tword by lia; auto.
    - apply ev_num; [|reflexivity]. unfold ty. destruct H as [E|[E|E]]; rewrite E, ttype_tword by lia; auto.
    - apply ev_str; [|reflexivity|exact H]. apply is_str_read; exact H.
  Qed.

  Lemma elem_view_of : forall d i j, elem d i j -> 0 <= i -> j < 2^32 -> elem_view d i j.
  Proof using CK_range Hsn.
    intros [|d] i j H Hi Hj; cbn [elem] in H.
    - destruct H as [H|[]]. apply scalar_view; exact H.
    - destruct H as [H|(e & c & cv & -> & Hck & Hc)]; [apply scalar_view; exact H|].
      pose proof (CK_range _ _ Hck) as Hcv.
      destruct Hc as [(H1 & H2 & Ht)|(H1 & H2 & Ht)].
      + pose proof (tiles_le _ (elem_lt d) _ _ _ Ht).
        eapply (ev_arr _ _ _ d e c); try reflexivity; try assumption.
        * unfold ty. rewrite H1. apply ttype_cword; lia.
        * rewrite H1. apply tnext_cword; lia.
      + pose proof (tiles_le _ (field_lt _ (elem_lt d)) _ _ _ Ht).
        eapply (ev_obj _ _ _ d e c); try reflexivity; try assumption.
        * unfold ty. rewrite H1. apply ttype_cword; lia.
        * rewrite H1. apply tnext_cword; lia.
  Qed.

  Definition after (i : Z) : Z :=
    if (ty i =? t_arr) || (ty i =? t_obj) then tnext (T i)
    else if (ty i =? t_i64) || (ty i =? t_u64) || (ty i =? t_dbl) then i + 2
    else i + 1.

  Lemma elem_after : forall d i j, elem d i j -> 0 <= i -> j < 2^32 -> after i = j.
  Proof using CK_range Hsn.
    intros d i j H Hi Hj. destruct (elem_view_of _ _ _ H Hi Hj) as [Ht ->|Ht ->|Ht -> _|d' e c _ Ht -> Hn _ _|d' e c _ Ht -> Hn _ _];
      unfold after; unfold t_arr, t_obj, t_i64, t_u64, t_dbl, t_true, t_false, t_null, t_str in *.
    - destruct Ht as [E|[E|E]]; rewrite E; reflexivity.
    - destruct Ht as [E|[E|E]]; rewrite E; reflexivity.
    - rewrite Ht; reflexivity.
    - rewrite Ht; cbn. exact Hn.
    - rewrite Ht; cbn. exact Hn.
  Qed.

  Lemma array_iter : forall d' it e c, tiles (elem d') it e c -> it <> e -> 0 <= it -> e < 2^32 ->
    exists j, elem d' it j /\ it < j <= e /\ after it = j /\ tiles (elem d') j e (c - 1).
  Proof using CK_range Hsn.
    intros d' it e c Ht Hne Hi He. destruct (tiles_next _ (elem_lt d') _ _ _ Ht Hne) as (j & Hel & Hje & Hr).
    exists j. pose proof (elem_lt _ _ _ Hel). repeat split; try assumption; try lia.
    apply (elem_after d'); [exact Hel|lia|lia].
  Qed.

  Lemma object_iter : forall d' it e c, tiles (field (elem d')) it e c -> it <> e -> 0 <= it -> e < 2^32 ->
    exists j, is_str it /\ elem d' (it + 1) j /\ it + 1 < j <= e /\ after (it + 1) = j /\ tiles (field (elem d')) j e (c - 1).
  Proof using CK_range Hsn.
    intros d' it e c Ht Hne Hi He.
    destruct (tiles_next _ (field_lt _ (elem_lt d')) _ _ _ Ht Hne) as (j & [Hs Hel] & Hje & Hr).
    exists j. pose proof (elem_lt _ _ _ Hel). repeat split; try assumption; try lia.
    apply (elem_after d'); [exact Hel|lia|lia].
  Qed.

  Lemma tape_wf_root : forall n, tape_wf n -> elem TAPE_MAX_DEPTH 1 (n - 1) /\ 2 < n < 2^32.
  Proof. intros n (H1 & _ & _ & _ & H5). split; assumption. Qed.
End Tape.

Section Ext.
  Variables (T T' S S' : Z -> Z) (sn sn' : Z) (CK : Z -> Z -> Prop).
  Hypothesis HS : forall y, 0 <= y < sn -> S' y = S y.
  Hypothesis Hsn : sn <= sn'.

  Lemma str_at_ext : forall o l, str_at S sn o l -> str_at S' sn' o l.
  Proof using HS Hsn.
    intros o l (H1 & H2 & H3 & H4 & H5). unfold str_at, le32 in *.
    rewrite !HS by lia. repeat split; try assumption; lia.
  Qed.

  Lemma is_str_ext : forall i, T' i = T i -> is_str T S sn i -> is_str T' S' sn' i.
  Proof using HS Hsn. intros i E (o & l & H1 & H2). exists o, l. split; [congruence|apply str_at_ext; exact H2]. Qed.

  Lemma scalar_ext : forall i j, (forall x, i <= x < j -> T' x = T x) -> scalar T S sn i j -> scalar T' S' sn' i j.
  Proof using HS Hsn.
    intros i j HT H. assert (E : j = i + 1 \/ j = i + 2) by (destruct H as [[-> _]|[[-> _]|[-> _]]]; lia).
    assert (Ei : T' i = T i) by (apply HT; lia). unfold scalar in *. rewrite Ei.
    destruct H as [H|[H|[H1 H2]]]; [left; exact H|right; left; exact H|right; right].
    split; [exact H1|]. apply is_str_ext; assumption.
  Qed.

  Lemma elem_ext : forall d i j, (forall x, i <= x < j -> T' x = T x) -> elem T S sn CK d i j -> elem T' S' sn' CK d i j.
  Proof using HS Hsn.
    induction d as [|d IH]; intros i j HT H; cbn [elem] in *.
    - destruct H as [H|[]]. left. apply scalar_ext; assumption.
    - destruct H as [H|(e & c & cv & -> & Hck & Hc)]; [left; apply scalar_ext; assumption|]. right.
      exists e, c, cv. split; [reflexivity|]. split; [exact Hck|].
      destruct Hc as [(H1 & H2 & Ht)|(H1 & H2 & Ht)].
      + pose proof (tiles_le _ (elem_lt T S sn CK d) _ _ _ Ht).
        left. rewrite !HT by lia. split; [exact H1|]. split; [exact H2|].
        eapply tiles_impl; [| |exact Ht]; [|apply elem_lt]. intros a b Ha Hb Hel. apply IH; [|exact Hel]. intros x Hx. apply HT. lia.
      + pose proof (tiles_le _ (field_lt T S sn _ (elem_lt T S sn CK d)) _ _ _ Ht).
        right. rewrite !HT by lia. split; [exact H1|]. split; [exact H2|].
        eapply tiles_impl; [| |exact Ht]; [|apply field_lt; apply elem_lt]. intros a b Ha Hb [Hs Hel].
        pose proof (elem_lt _ _ _ _ _ _ _ Hel).
        split; [apply is_str_ext; [apply HT; lia|exact Hs]|]. apply IH; [|exact Hel]. intros x Hx. apply HT. lia.
  Qed.
End Ext.
