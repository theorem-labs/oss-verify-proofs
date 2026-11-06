(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record StrictWeakOrder {K : Type} (lt : K → K → bool) : Prop := {
  swo_asym : ∀ a b, lt a b = true → lt b a = false ;
  (* [comment removed for export] *)
  swo_neg_trans : ∀ a b c, lt a b = false → lt b c = false → lt a c = false
}.
Arguments swo_asym {K lt} _ a b.
Arguments swo_neg_trans {K lt} _ a b c.

(* [comment removed for export] *)
Definition eqv {K : Type} (lt : K → K → bool) (a b : K) : bool := negb (lt a b) && negb (lt b a).

Section SWOFacts.
  Context {K : Type} (lt : K → K → bool) (SWO : StrictWeakOrder lt).

  Lemma swo_irrefl a : lt a a = false.
  Proof. destruct (lt a a) eqn:E; [|done]. by rewrite (swo_asym SWO a a E) in E. Qed.

  Lemma swo_trans a b c : lt a b = true → lt b c = true → lt a c = true.
  Proof.
    intros H1 H2. destruct (lt a c) eqn:E; [done|]. exfalso.
    pose proof (swo_asym SWO _ _ H1) as H1'. pose proof (swo_asym SWO _ _ H2) as H2'.
    (* [comment removed for export] *)
    pose proof (swo_neg_trans SWO b a c H1' E) as X. by rewrite X in H2.
  Qed.

  (* [comment removed for export] *)
  Lemma swo_lt_le k x y : lt k x = true → lt y x = false → lt k y = true.
  Proof.
    intros H1 H2. destruct (lt k y) eqn:E; [done|]. exfalso.
    pose proof (swo_neg_trans SWO k y x E H2) as X. by rewrite X in H1.
  Qed.

  (* [comment removed for export] *)
  Lemma swo_le_lt k x y : lt y k = true → lt y x = false → lt x k = true.
  Proof.
    intros H1 H2. destruct (lt x k) eqn:E; [done|]. exfalso.
    pose proof (swo_neg_trans SWO y x k H2 E) as X. by rewrite X in H1.
  Qed.

  Lemma eqv_refl a : eqv lt a a = true.
  Proof. unfold eqv. by rewrite swo_irrefl. Qed.
  Lemma eqv_sym a b : eqv lt a b = eqv lt b a.
  Proof. unfold eqv. apply andb_comm. Qed.
  Lemma eqv_true a b : eqv lt a b = true ↔ lt a b = false ∧ lt b a = false.
  Proof. unfold eqv. rewrite andb_true_iff, !negb_true_iff. done. Qed.
  Lemma eqv_false a b : eqv lt a b = false ↔ lt a b = true ∨ lt b a = true.
  Proof.
    unfold eqv. rewrite andb_false_iff, !negb_false_iff. done.
  Qed.
  Lemma eqv_trans a b c : eqv lt a b = true → eqv lt b c = true → eqv lt a c = true.
  Proof.
    rewrite !eqv_true. intros [H1 H2] [H3 H4]. split.
    - exact (swo_neg_trans SWO _ _ _ H1 H3).
    - exact (swo_neg_trans SWO _ _ _ H4 H2).
  Qed.
  (* [comment removed for export] *)
  Lemma lt_eqv_l a b c : eqv lt a b = true → lt a c = lt b c.
  Proof.
    rewrite eqv_true. intros [H1 H2].
    destruct (lt b c) eqn:E.
    - by apply (swo_le_lt c a b).
    - by apply (swo_neg_trans SWO a b c).
  Qed.
  Lemma lt_eqv_r a b c : eqv lt a b = true → lt c a = lt c b.
  Proof.
    rewrite eqv_true. intros [H1 H2].
    destruct (lt c b) eqn:E.
    - by apply (swo_lt_le c b a).
    - by apply (swo_neg_trans SWO c b a).
  Qed.
End SWOFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Order.
  Context {K : Type} (lt : K → K → bool) (SWO : StrictWeakOrder lt).
  (* [comment removed for export] *)
  Context (key : Z → K).

  (* [comment removed for export] *)
  Fixpoint sorted (S : list Z) : Prop :=
    match S with
    | [] => True
    | a :: S' => (∀ b, b ∈ S' → lt (key b) (key a) = false) ∧ sorted S'
    end.

  Lemma sorted_app A B :
    sorted (A ++ B) ↔ sorted A ∧ sorted B ∧ (∀ a b, a ∈ A → b ∈ B → lt (key b) (key a) = false).
  Proof.
    induction A as [|x A IH]; cbn.
    - split; [intros H; repeat split; auto; set_solver| tauto].
    - rewrite IH. split.
      + intros (Hx & HA & HB & HAB). repeat split; auto.
        * intros b Hb. apply Hx. set_solver.
        * intros a b Ha Hb. rewrite elem_of_cons in Ha. destruct Ha as [->|Ha]; [apply Hx; set_solver|by apply HAB].
      + intros ((Hx & HA) & HB & HAB). repeat split; auto.
        * intros b Hb. rewrite elem_of_app in Hb. destruct Hb as [Hb|Hb]; [by apply Hx|apply HAB; set_solver].
        * intros a b Ha Hb. apply HAB; set_solver.
  Qed.

  (* [comment removed for export] *)
  Definition cmpU (k : K) : Z → bool := λ x, lt k (key x).        (* [comment removed for export] *)
  Definition cmpL (k : K) : Z → bool := λ x, lt (key x) k.        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Fixpoint ub_prefix (k : K) (S : list Z) : list Z :=       (* [comment removed for export] *)
    match S with [] => [] | x :: S' => if lt k (key x) then [] else x :: ub_prefix k S' end.
  Fixpoint ub_suffix (k : K) (S : list Z) : list Z :=
    match S with [] => [] | x :: S' => if lt k (key x) then x :: S' else ub_suffix k S' end.
  Fixpoint lb_prefix (k : K) (S : list Z) : list Z :=       (* [comment removed for export] *)
    match S with [] => [] | x :: S' => if lt (key x) k then x :: lb_prefix k S' else [] end.
  Fixpoint lb_suffix (k : K) (S : list Z) : list Z :=
    match S with [] => [] | x :: S' => if lt (key x) k then lb_suffix k S' else x :: S' end.

  Lemma ub_split k S : S = ub_prefix k S ++ ub_suffix k S.
  Proof. induction S as [|x S IH]; cbn; [done|]. destruct (lt k (key x)); cbn; [done|]. by rewrite <-IH. Qed.
  Lemma lb_split k S : S = lb_prefix k S ++ lb_suffix k S.
  Proof. induction S as [|x S IH]; cbn; [done|]. destruct (lt (key x) k); cbn; [|done]. by rewrite <-IH. Qed.

  Lemma ub_prefix_false k S : all_false (cmpU k) (ub_prefix k S).
  Proof.
    unfold all_false, cmpU. induction S as [|x S IH]; cbn; [set_solver|].
    destruct (lt k (key x)) eqn:E; [set_solver|]. intros y Hy. rewrite elem_of_cons in Hy.
    destruct Hy as [->|Hy]; auto.
  Qed.
  Lemma lb_prefix_true k S : all_true (cmpL k) (lb_prefix k S).
  Proof.
    unfold all_true, cmpL. induction S as [|x S IH]; cbn; [set_solver|].
    destruct (lt (key x) k) eqn:E; [|set_solver]. intros y Hy. rewrite elem_of_cons in Hy.
    destruct Hy as [->|Hy]; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma ub_suffix_true k S : sorted S → all_true (cmpU k) (ub_suffix k S).
  Proof.
    unfold all_true, cmpU. induction S as [|x S IH]; cbn; [set_solver|].
    intros [Hx HS]. destruct (lt k (key x)) eqn:E; [|auto].
    intros y Hy. rewrite elem_of_cons in Hy. destruct Hy as [->|Hy]; [done|].
    apply (swo_lt_le lt SWO k (key x) (key y) E). by apply Hx.
  Qed.
  Lemma lb_suffix_false k S : sorted S → all_false (cmpL k) (lb_suffix k S).
  Proof.
    unfold all_false, cmpL. induction S as [|x S IH]; cbn; [set_solver|].
    intros [Hx HS]. destruct (lt (key x) k) eqn:E; [auto|].
    intros y Hy. rewrite elem_of_cons in Hy. destruct Hy as [->|Hy]; [done|].
    destruct (lt (key y) k) eqn:E2; [|done]. exfalso.
    pose proof (swo_le_lt lt SWO k (key x) (key y) E2 (Hx y Hy)) as X. by rewrite X in E.
  Qed.

  (* [comment removed for export] *)
  Lemma ub_suffix_in k S x : sorted S → x ∈ S → (x ∈ ub_suffix k S ↔ lt k (key x) = true).
  Proof.
    intros HS Hx. split.
    - intros H. by apply (ub_suffix_true k S HS).
    - intros H. rewrite (ub_split k S), elem_of_app in Hx. destruct Hx as [Hx|Hx]; [|done].
      pose proof (ub_prefix_false k S x Hx) as X. unfold cmpU in X. by rewrite X in H.
  Qed.
  Lemma ub_prefix_in k S x : sorted S → x ∈ S → (x ∈ ub_prefix k S ↔ lt k (key x) = false).
  Proof.
    intros HS Hx. split.
    - intros H. by apply (ub_prefix_false k S).
    - intros H. rewrite (ub_split k S), elem_of_app in Hx. destruct Hx as [Hx|Hx]; [done|].
      pose proof (ub_suffix_true k S HS x Hx) as X. unfold cmpU in X. by rewrite X in H.
  Qed.
  Lemma lb_prefix_in k S x : sorted S → x ∈ S → (x ∈ lb_prefix k S ↔ lt (key x) k = true).
  Proof.
    intros HS Hx. split.
    - intros H. by apply (lb_prefix_true k S).
    - intros H. rewrite (lb_split k S), elem_of_app in Hx. destruct Hx as [Hx|Hx]; [done|].
      pose proof (lb_suffix_false k S HS x Hx) as X. unfold cmpL in X. by rewrite X in H.
  Qed.
  Lemma lb_suffix_in k S x : sorted S → x ∈ S → (x ∈ lb_suffix k S ↔ lt (key x) k = false).
  Proof.
    intros HS Hx. split.
    - intros H. by apply (lb_suffix_false k S HS).
    - intros H. rewrite (lb_split k S), elem_of_app in Hx. destruct Hx as [Hx|Hx]; [|done].
      pose proof (lb_prefix_true k S x Hx) as X. unfold cmpL in X. by rewrite X in H.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem ubT_sorted k T y :
    sorted (inorder T) → ubT (cmpU k) T y = lhead y (ub_suffix k (inorder T)).
  Proof.
    intros HS. apply (ubT_split (cmpU k) T y (ub_prefix k (inorder T)));
      [apply ub_split|apply ub_prefix_false|by apply ub_suffix_true].
  Qed.

  Theorem lbT_sorted k T y :
    sorted (inorder T) → lbT (cmpL k) T y = lhead y (lb_suffix k (inorder T)).
  Proof.
    intros HS. apply (lbT_split (cmpL k) T y (lb_prefix k (inorder T)));
      [apply lb_split|apply lb_prefix_true|by apply lb_suffix_false].
  Qed.

  (* [comment removed for export] *)
  Theorem upper_bound_sorted k h S ns fuel :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    upper_bound fuel (cmpU k) ns h = Some (lhead h (ub_suffix k S)).
  Proof.
    intros (T & <- & HR) HS Hf. rewrite (upper_bound_spec (cmpU k) h T ns fuel HR).
    - f_equal. by apply ubT_sorted.
    - apply theight_le_tsize || (etransitivity; [apply theight_le_tsize|done]).
  Qed.

  Theorem lower_bound_sorted k h S ns fuel :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    lower_bound fuel (cmpL k) ns h = Some (lhead h (lb_suffix k S)).
  Proof.
    intros (T & <- & HR) HS Hf. rewrite (lower_bound_spec (cmpL k) h T ns fuel HR).
    - f_equal. by apply lbT_sorted.
    - apply theight_le_tsize || (etransitivity; [apply theight_le_tsize|done]).
  Qed.

  (* [comment removed for export] *)
  Theorem upper_bound_loop_sorted k h S ns fuel root :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    get_parent ns h = Some root →
    upper_bound_loop fuel (cmpU k) ns root h = Some (lhead h (ub_suffix k S)).
  Proof.
    intros HR HS Hf Hroot. pose proof (upper_bound_sorted k h S ns fuel HR HS Hf) as X.
    unfold upper_bound in X. rewrite Hroot in X. exact X.
  Qed.
  Theorem lower_bound_loop_sorted k h S ns fuel root :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    get_parent ns h = Some root →
    lower_bound_loop fuel (cmpL k) ns root h = Some (lhead h (lb_suffix k S)).
  Proof.
    intros HR HS Hf Hroot. pose proof (lower_bound_sorted k h S ns fuel HR HS Hf) as X.
    unfold lower_bound in X. rewrite Hroot in X. exact X.
  Qed.

  (* [comment removed for export] *)
  Definition has_eqv (k : K) (S : list Z) : Prop := ∃ x, x ∈ S ∧ eqv lt k (key x) = true.

  (* [comment removed for export] *)
  Lemma lb_suffix_head_eqv k S :
    sorted S →
    match lb_suffix k S with
    | [] => ¬ has_eqv k S
    | y :: _ => if lt k (key y) then ¬ has_eqv k S else eqv lt k (key y) = true
    end.
  Proof.
    intros HS. pose proof (lb_split k S) as E.
    assert (HP : ∀ x, x ∈ lb_prefix k S → eqv lt k (key x) = false).
    { intros x Hx. rewrite (eqv_false lt). right. by apply (lb_prefix_true k S). }
    destruct (lb_suffix k S) as [|y B] eqn:EB.
    - rewrite app_nil_r in E. intros (x & Hx & Hex). rewrite E in Hx. by rewrite (HP x Hx) in Hex.
    - assert (Hy : lt (key y) k = false).
      { apply (lb_suffix_false k S HS). rewrite EB. set_solver. }
      destruct (lt k (key y)) eqn:Hky.
      + intros (x & Hx & Hex). rewrite E, elem_of_app in Hx. destruct Hx as [Hx|Hx].
        * by rewrite (HP x Hx) in Hex.
        * (* [comment removed for export] *)
          assert (Hyx : lt (key x) (key y) = false).
          { rewrite elem_of_cons in Hx. destruct Hx as [->|Hx]; [apply (swo_irrefl lt SWO)|].
            rewrite E in HS. apply sorted_app in HS. destruct HS as (_ & [Hy' _] & _). by apply Hy'. }
          pose proof (swo_lt_le lt SWO k (key y) (key x) Hky Hyx) as X.
          apply (eqv_true lt) in Hex. destruct Hex as [Hex _]. by rewrite Hex in X.
      + apply (eqv_true lt). done.
  Qed.

  Theorem findT_sorted k T h :
    sorted (inorder T) → NoDup (h :: inorder T) →
    let r := findT (cmpL k) (cmpU k) T h in
    (r = h ∧ ¬ has_eqv k (inorder T))
    ∨ (∃ B, lb_suffix k (inorder T) = r :: B ∧ r ∈ inorder T ∧ r ≠ h ∧ eqv lt k (key r) = true
            ∧ (∀ x, x ∈ lb_prefix k (inorder T) → lt (key x) k = true)).
  Proof.
    intros HS N. cbn zeta. unfold findT. rewrite (lbT_sorted k T h HS).
    pose proof (lb_suffix_head_eqv k (inorder T) HS) as X.
    destruct (lb_suffix k (inorder T)) as [|y B] eqn:EB; cbn [lhead].
    - left. rewrite Z.eqb_refl. done.
    - assert (Hy : y ∈ inorder T) by (rewrite (lb_split k (inorder T)), EB; set_solver).
      assert (Hyh : y ≠ h) by (intros ->; apply NoDup_cons in N; tauto).
      rewrite (Zeqb_ne _ _ Hyh). unfold cmpU. destruct (lt k (key y)) eqn:Hky.
      + left. done.
      + right. exists B. repeat split; auto. apply lb_prefix_true.
  Qed.

  (* [comment removed for export] *)
  Theorem find_sorted k h S ns fuel :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    ∃ r, find fuel (cmpL k) (cmpU k) ns h = Some r ∧
      ((r = h ∧ ¬ has_eqv k S)
       ∨ (∃ B, lb_suffix k S = r :: B ∧ r ∈ S ∧ r ≠ h ∧ eqv lt k (key r) = true
               ∧ (∀ x, x ∈ lb_prefix k S → lt (key x) k = true))).
  Proof.
    intros (T & <- & HR) HS Hf. exists (findT (cmpL k) (cmpU k) T h). split.
    - apply find_spec; [done|]. etransitivity; [apply theight_le_tsize|done].
    - apply findT_sorted; [done|]. exact (nd_cons_tl _ _ (rep_N _ _ _ HR)).
  Qed.

  Corollary find_is_header_iff k h S ns fuel r :
    rb_rep h S ns → sorted S → (length S <= fuel)%nat →
    find fuel (cmpL k) (cmpU k) ns h = Some r →
    (r = h ↔ ¬ has_eqv k S).
  Proof.
    intros HR HS Hf Hr. destruct (find_sorted k h S ns fuel HR HS Hf) as (r' & Hr' & X).
    rewrite Hr in Hr'. injection Hr' as <-.
    destruct X as [[-> Hn]|(B & EB & Hin & Hne & Heq & _)]; [tauto|].
    split; [done|]. intros Hn. exfalso. apply Hn. by exists r.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem sorted_insert_ub k S n :
    sorted S → key n = k →
    sorted (ub_prefix k S ++ n :: ub_suffix k S).
  Proof.
    intros HS Hk. pose proof HS as HS'. rewrite (ub_split k S) in HS'.
    apply sorted_app in HS'. destruct HS' as (HA & HB & HAB).
    apply sorted_app. split; [done|]. split.
    - cbn. split; [|done]. intros b Hb. rewrite Hk.
      apply (swo_asym SWO). by apply (ub_suffix_true k S HS).
    - intros a b Ha Hb. rewrite elem_of_cons in Hb. destruct Hb as [->|Hb]; [|by apply HAB].
      rewrite Hk. by apply (ub_prefix_false k S).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem ub_begin_no_eqv k S :
    sorted S → ub_prefix k S = [] → ¬ has_eqv k S.
  Proof.
    intros HS HA (x & Hx & Hex). rewrite (ub_split k S), HA in Hx. cbn in Hx.
    pose proof (ub_suffix_true k S HS x Hx) as X. unfold cmpU in X.
    apply (eqv_true lt) in Hex. destruct Hex as [H _]. by rewrite H in X.
  Qed.

  (* [comment removed for export] *)
  Theorem ub_prev_no_eqv k S A' last :
    sorted S → ub_prefix k S = A' ++ [last] → eqv lt k (key last) = false → ¬ has_eqv k S.
  Proof.
    intros HS HA Hlast (x & Hx & Hex).
    rewrite (ub_split k S), elem_of_app in Hx. destruct Hx as [Hx|Hx].
    - (* [comment removed for export] *)
      assert (Hkl : lt k (key last) = false).
      { apply (ub_prefix_false k S). rewrite HA. set_solver. }
      assert (Hlk : lt (key last) k = true).
      { apply (eqv_false lt) in Hlast. destruct Hlast as [H|H]; [by rewrite H in Hkl|done]. }
      assert (Hxl : lt (key last) (key x) = false).
      { rewrite HA, elem_of_app in Hx. destruct Hx as [Hx|Hx].
        - pose proof HS as HS2. rewrite (ub_split k S), HA, <-app_assoc in HS2.
          apply sorted_app in HS2. destruct HS2 as (_ & _ & HAB). apply HAB; [done|set_solver].
        - assert (x = last) as -> by set_solver. apply (swo_irrefl lt SWO). }
      pose proof (swo_le_lt lt SWO k (key x) (key last) Hlk Hxl) as X.
      apply (eqv_true lt) in Hex. destruct Hex as [_ H]. by rewrite H in X.
    - pose proof (ub_suffix_true k S HS x Hx) as X. unfold cmpU in X.
      apply (eqv_true lt) in Hex. destruct Hex as [H _]. by rewrite H in X.
  Qed.

  (* [comment removed for export] *)
  Theorem ub_prev_eqv k S A' last x :
    sorted S → ub_prefix k S = A' ++ [last] → x ∈ S → eqv lt k (key x) = true → x ∈ ub_prefix k S.
  Proof.
    intros HS HA Hx Hex. apply (ub_prefix_in k S x HS Hx).
    apply (eqv_true lt) in Hex. tauto.
  Qed.

End Order.

Arguments sorted {K} lt key S.
Arguments cmpU {K} lt key k x /.
Arguments cmpL {K} lt key k x /.
