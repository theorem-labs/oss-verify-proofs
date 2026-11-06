(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma obind_Some {A B} (v : A) (k : A → option B) : (x ← Some v ; k x) = k v.
Proof. reflexivity. Qed.
Lemma obind_None {A B} (k : A → option B) : (x ← @None A ; k x) = None.
Proof. reflexivity. Qed.
Lemma obind_assoc {A B C} (m : option A) (k : A -> option B) (k2 : B -> option C) :
  (y ← (x ← m ; k x) ; k2 y) = (x ← m ; y ← k x ; k2 y).
Proof. by destruct m. Qed.

Lemma load_Some ns a off nd : ns !! a = Some nd → load ns a off = Some (get_field off nd).
Proof. intros H. unfold load. by rewrite H. Qed.
Lemma store_Some ns a off v nd : ns !! a = Some nd → store ns a off v = Some (<[a := set_field off v nd]> ns).
Proof. intros H. unfold store. by rewrite H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oloop_S {X R} n (body : X → option (X + R)) x :
  oloop (S n) body x = (s ← body x ; match s with inl x' => oloop n body x' | inr r => Some r end).
Proof. reflexivity. Qed.

Lemma oloop_mono {X R} n m (body : X → option (X + R)) x r :
  oloop n body x = Some r → (n <= m)%nat → oloop m body x = Some r.
Proof.
  revert m x; induction n as [|n IH]; intros m x H Hle; cbn in H; [congruence|].
  destruct m as [|m]; [lia|]. rewrite oloop_S.
  destruct (body x) as [[x'|r']|]; cbn in *; [|congruence|congruence].
  apply IH; [done|lia].
Qed.

(* [comment removed for export] *)
Lemma oloop_inv {X R} (body : X → option (X + R)) (I : X → Prop) (Q : R → Prop) (m : X → nat) :
  (∀ x, I x → ∃ s, body x = Some s ∧
        match s with inl x' => I x' ∧ (m x' < m x)%nat | inr r => Q r end) →
  ∀ n x, I x → (m x < n)%nat → ∃ r, oloop n body x = Some r ∧ Q r.
Proof.
  intros Hstep n. induction n as [|n IH]; intros x Hx Hm; [lia|].
  rewrite oloop_S. destruct (Hstep x Hx) as (s & -> & Hs). cbn.
  destruct s as [x'|r].
  - destruct Hs as [Hx' Hlt]. apply IH; [done|lia].
  - eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_app_l {A} (x : A) l1 l2 : x ∈ l1 → x ∈ l1 ++ l2.
Proof. set_solver. Qed.
Lemma in_app_r {A} (x : A) l1 l2 : x ∈ l2 → x ∈ l1 ++ l2.
Proof. set_solver. Qed.

Ltac solve_in :=
  first
  [ assumption
  | apply list_elem_of_here
  | apply list_elem_of_further; solve_in
  | apply in_app_l; solve_in
  | apply in_app_r; solve_in ].

Lemma nd_cons_neq (x : Z) L b : NoDup (x :: L) → b ∈ L → x ≠ b.
Proof. intros N Hb ->. apply NoDup_cons in N. tauto. Qed.
Lemma nd_cons_neq' (x : Z) L b : NoDup (x :: L) → b ∈ L → b ≠ x.
Proof. intros N Hb ->. apply NoDup_cons in N. tauto. Qed.
Lemma nd_app_neq (X Y : list Z) a b : NoDup (X ++ Y) → a ∈ X → b ∈ Y → a ≠ b.
Proof. intros N Ha Hb ->. apply NoDup_app in N. destruct N as (_ & D & _). by apply (D b). Qed.
Lemma nd_app_neq' (X Y : list Z) a b : NoDup (X ++ Y) → a ∈ X → b ∈ Y → b ≠ a.
Proof. intros N Ha Hb ->. apply NoDup_app in N. destruct N as (_ & D & _). by apply (D a). Qed.
Lemma nd_cons_tl (x : Z) L : NoDup (x :: L) → NoDup L.
Proof. intros N. apply NoDup_cons in N. tauto. Qed.
Lemma nd_app_tl (X Y : list Z) : NoDup (X ++ Y) → NoDup Y.
Proof. intros N. apply NoDup_app in N. tauto. Qed.
Lemma nd_app_hd (X Y : list Z) : NoDup (X ++ Y) → NoDup X.
Proof. intros N. apply NoDup_app in N. tauto. Qed.
Lemma nd_cons_notin (x : Z) L : NoDup (x :: L) → x ∉ L.
Proof. intros N. apply NoDup_cons in N. tauto. Qed.
Lemma nd_app_notin (X Y : list Z) a : NoDup (X ++ Y) → a ∈ X → a ∉ Y.
Proof. intros N Ha. apply NoDup_app in N. destruct N as (_ & D & _). by apply D. Qed.
Lemma nd_app_notin' (X Y : list Z) a : NoDup (X ++ Y) → a ∈ Y → a ∉ X.
Proof. intros N Ha Hx. apply NoDup_app in N. destruct N as (_ & D & _). by apply (D a). Qed.

(* [comment removed for export] *)
Ltac nd_neq_with N :=
  first
  [ apply (nd_cons_neq _ _ _ N); solve_in
  | apply (nd_cons_neq' _ _ _ N); solve_in
  | eapply (nd_app_neq _ _ _ _ N); solve_in
  | eapply (nd_app_neq' _ _ _ _ N); solve_in
  | nd_neq_with (nd_cons_tl _ _ N)
  | nd_neq_with (nd_app_tl _ _ N) ].

(* [comment removed for export] *)
Ltac nd_notin_with N :=
  first
  [ apply (nd_cons_notin _ _ N)
  | eapply (nd_app_notin _ _ _ N); solve_in
  | eapply (nd_app_notin' _ _ _ N); solve_in
  | let H := fresh in intros H; eapply (nd_app_neq _ _ _ _ N); [solve_in|solve_in|reflexivity]
  | nd_notin_with (nd_cons_tl _ _ N)
  | nd_notin_with (nd_app_tl _ _ N) ].

(* [comment removed for export] *)
Ltac norm_list_in N :=
  repeat (rewrite inorder_plug in N || rewrite <-app_assoc in N || rewrite <-app_comm_cons in N);
  cbn [inorder app lfr rfr] in N;
  repeat (rewrite <-app_assoc in N); cbn [app] in N;
  repeat (rewrite <-app_assoc in N; cbn [app] in N).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac unfold_prims :=
  unfold get_parent, get_left, get_right, get_color, set_parent, set_left, set_right, set_color,
         load, store.

Ltac red_binds :=
  cbn [mbind option_bind fmap option_fmap option_map get_field set_field
       OFF_PARENT OFF_LEFT OFF_RIGHT OFF_COLOR Z.eqb Pos.eqb fst snd].

Lemma Zeqb_refl' (a : Z) : (a =? a) = true. Proof. apply Z.eqb_refl. Qed.
Lemma Zeqb_ne (a b : Z) : a ≠ b → (a =? b) = false. Proof. intros; by apply Z.eqb_neq. Qed.

(* [comment removed for export] *)
Ltac simp_lookup_with tac :=
  repeat first
  [ rewrite lookup_insert_eq
  | rewrite lookup_insert_ne by tac
  | match goal with H : ?m !! ?a = Some _ |- context [?m !! ?a] => rewrite H end ].

(* [comment removed for export] *)
Ltac norm_app := repeat (rewrite <-app_assoc || rewrite <-app_comm_cons); cbn [app];
  repeat (rewrite <-app_assoc; cbn [app]).
Ltac norm_app_in H := repeat (rewrite <-app_assoc in H || rewrite <-app_comm_cons in H); cbn [app] in H;
  repeat (rewrite <-app_assoc in H; cbn [app] in H).
Ltac list_eq := norm_app; reflexivity.

(* [comment removed for export] *)
Lemma NoDup_insert_mid (A B : list Z) x : NoDup (A ++ B) → x ∉ A ++ B → NoDup (A ++ x :: B).
Proof.
  intros N Hx. rewrite NoDup_app in N. destruct N as (NA & D & NB).
  apply NoDup_app. repeat split; [done| |].
  - intros y Hy Hy2. rewrite elem_of_cons in Hy2. destruct Hy2 as [->|Hy2]; [set_solver|by apply (D y)].
  - apply NoDup_cons. split; [set_solver|done].
Qed.

Lemma NoDup_insert_mid' (L0 L A B : list Z) x :
  NoDup L0 → L0 = A ++ B → x ∉ L0 → L = A ++ x :: B → NoDup L.
Proof. intros N -> Hx ->. by apply NoDup_insert_mid. Qed.

Lemma neq_irrefl_False (a : Z) : a ≠ a → False.
Proof. intros H. by apply H. Qed.

(* [comment removed for export] *)
Ltac nd_notin N :=
  match goal with |- ?x ∉ _ =>
    let Hin := fresh "Hin" in intros Hin; apply (neq_irrefl_False x); nd_neq_with N end.

