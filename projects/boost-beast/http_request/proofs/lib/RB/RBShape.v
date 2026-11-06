(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tree := Leaf | Node (l : tree) (a : Z) (r : tree).

Fixpoint inorder (t : tree) : list Z :=
  match t with Leaf => [] | Node l a r => inorder l ++ a :: inorder r end.

Definition troot (t : tree) : Z := match t with Leaf => 0 | Node _ a _ => a end.

Fixpoint theight (t : tree) : nat :=
  match t with Leaf => O | Node l _ r => S (Nat.max (theight l) (theight r)) end.

Definition tsize (t : tree) : nat := length (inorder t).

Lemma theight_le_tsize t : (theight t <= tsize t)%nat.
Proof.
  unfold tsize; induction t as [|l IHl a r IHr]; cbn; [lia|].
  rewrite length_app; cbn. lia.
Qed.

Definition lhead (d : Z) (l : list Z) : Z := match l with [] => d | x :: _ => x end.
Definition llast (d : Z) (l : list Z) : Z := List.last l d.
Arguments llast : simpl never.

(* [comment removed for export] *)
Definition tmin (h : Z) (t : tree) : Z := lhead h (inorder t).
Definition tmax (h : Z) (t : tree) : Z := llast h (inorder t).

Lemma last_cons_indep (x : Z) l d d' : List.last (x :: l) d = List.last (x :: l) d'.
Proof. revert x; induction l as [|y l IH]; intros x; cbn; [done|]. apply IH. Qed.

Lemma llast_app_cons d l1 x l2 : llast d (l1 ++ x :: l2) = llast x l2.
Proof.
  unfold llast. induction l1 as [|y l1 IH]; cbn.
  - destruct l2 as [|z l2]; [done|]. apply last_cons_indep.
  - rewrite <-IH. destruct (l1 ++ x :: l2) eqn:E; [|reflexivity]. destruct l1; inversion E.
Qed.

Lemma llast_in d l : l ≠ [] → llast d l ∈ l.
Proof.
  unfold llast. induction l as [|x l IH]; cbn; [congruence|]. intros _.
  destruct l as [|y l']; [set_solver|]. assert (HH : y :: l' ≠ []) by congruence.
  specialize (IH HH). set_solver.
Qed.

Lemma lhead_in d l : l ≠ [] → lhead d l ∈ l.
Proof. destruct l; cbn; [congruence|set_solver]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint tree_at (ns : NS) (t : tree) (par : Z) : Prop :=
  match t with
  | Leaf => True
  | Node l a r =>
      exists nd, ns !! a = Some nd /\ n_par nd = par /\ n_lft nd = troot l /\ n_rgt nd = troot r
                 /\ tree_at ns l a /\ tree_at ns r a
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ctx := Top | GoL (a : Z) (sib : tree) (up : ctx) | GoR (sib : tree) (a : Z) (up : ctx).

Fixpoint plug (c : ctx) (t : tree) : tree :=
  match c with
  | Top => t
  | GoL a s up => plug up (Node t a s)
  | GoR s a up => plug up (Node s a t)
  end.

(* [comment removed for export] *)
Definition ctx_node (h : Z) (c : ctx) : Z :=
  match c with Top => h | GoL a _ _ => a | GoR _ a _ => a end.

Fixpoint cdepth (c : ctx) : nat :=
  match c with Top => O | GoL _ _ up | GoR _ _ up => S (cdepth up) end.

(* [comment removed for export] *)
Fixpoint lfr (c : ctx) : list Z :=
  match c with Top => [] | GoL a s up => lfr up | GoR s a up => lfr up ++ inorder s ++ [a] end.
Fixpoint rfr (c : ctx) : list Z :=
  match c with Top => [] | GoL a s up => a :: inorder s ++ rfr up | GoR s a up => rfr up end.

Lemma inorder_plug c t : inorder (plug c t) = lfr c ++ inorder t ++ rfr c.
Proof.
  revert t; induction c as [|a s up IH|s a up IH]; intros t; cbn.
  - by rewrite app_nil_r.
  - rewrite IH. cbn. by rewrite <-app_assoc.
  - rewrite IH. cbn. by rewrite <-!app_assoc.
Qed.

(* [comment removed for export] *)
Fixpoint cnodes (c : ctx) : list Z :=
  match c with
  | Top => []
  | GoL a s up => a :: inorder s ++ cnodes up
  | GoR s a up => a :: inorder s ++ cnodes up
  end.

Lemma cnodes_perm c : cnodes c ≡ₚ lfr c ++ rfr c.
Proof.
  induction c as [|a s up IH|s a up IH]; cbn; [done| |].
  - rewrite IH. etransitivity; [|apply Permutation_app_comm]. cbn. rewrite <-app_assoc.
    apply Permutation_cons; [done|]. apply Permutation_app_head, Permutation_app_comm.
  - rewrite IH. symmetry. rewrite <-!app_assoc. cbn [app]. rewrite app_assoc.
    etransitivity; [symmetry; apply Permutation_middle|]. apply Permutation_cons; [done|].
    rewrite (app_assoc (inorder s)). apply Permutation_app_tail, Permutation_app_comm.
Qed.

Lemma plug_nodes_perm c t : inorder (plug c t) ≡ₚ inorder t ++ cnodes c.
Proof.
  rewrite inorder_plug, cnodes_perm. rewrite app_assoc.
  rewrite (Permutation_app_comm (lfr c)). by rewrite app_assoc.
Qed.

(* [comment removed for export] *)
Fixpoint ccomp (ci co : ctx) : ctx :=
  match ci with
  | Top => co
  | GoL a s up => GoL a s (ccomp up co)
  | GoR s a up => GoR s a (ccomp up co)
  end.

Lemma plug_ccomp ci co t : plug (ccomp ci co) t = plug co (plug ci t).
Proof. revert t; induction ci; intros t; cbn; auto. Qed.

Lemma ctx_node_ccomp h ci co : ci ≠ Top → ctx_node h (ccomp ci co) = ctx_node h ci.
Proof. destruct ci; cbn; congruence. Qed.

Lemma cdepth_ccomp ci co : cdepth (ccomp ci co) = (cdepth ci + cdepth co)%nat.
Proof. induction ci; cbn; lia. Qed.

(* [comment removed for export] *)
Fixpoint allR (c : ctx) : Prop :=
  match c with Top => True | GoL _ _ _ => False | GoR _ _ up => allR up end.

Lemma rfr_allR c : allR c → rfr c = [].
Proof. induction c; cbn; tauto. Qed.

Lemma rfr_ccomp ci co : rfr (ccomp ci co) = rfr ci ++ rfr co.
Proof. induction ci as [|a s up IH|s a up IH]; cbn; [done| |]; rewrite IH; [|done]. by rewrite app_assoc. Qed.

Lemma lfr_ccomp ci co : lfr (ccomp ci co) = lfr co ++ lfr ci.
Proof.
  induction ci as [|a s up IH|s a up IH]; cbn; [by rewrite app_nil_r|done|].
  rewrite IH. by rewrite !app_assoc.
Qed.

(* [comment removed for export] *)
Fixpoint ctx_at (ns : NS) (h : Z) (c : ctx) (foc : Z) : Prop :=
  match c with
  | Top => exists hd, ns !! h = Some hd /\ n_par hd = foc
  | GoL a s up =>
      exists nd, ns !! a = Some nd /\ n_par nd = ctx_node h up /\ n_lft nd = foc /\ n_rgt nd = troot s
                 /\ tree_at ns s a /\ ctx_at ns h up a
  | GoR s a up =>
      exists nd, ns !! a = Some nd /\ n_par nd = ctx_node h up /\ n_lft nd = troot s /\ n_rgt nd = foc
                 /\ tree_at ns s a /\ ctx_at ns h up a
  end.

(* [comment removed for export] *)
Definition top_at (ns : NS) (h : Z) (T : tree) : Prop :=
  (exists hd, ns !! h = Some hd /\ n_par hd = troot T) /\ tree_at ns T h.

Lemma top_at_plug ns h c t :
  top_at ns h (plug c t) <-> ctx_at ns h c (troot t) /\ tree_at ns t (ctx_node h c).
Proof.
  unfold top_at. revert t; induction c as [|a s up IH|s a up IH]; intros t; cbn.
  - tauto.
  - rewrite IH. cbn. split.
    + intros (Hc & nd & Ha & Hp & Hl & Hr & Ht & Hs). split; [|done]. exists nd. repeat split; auto.
    + intros ((nd & Ha & Hp & Hl & Hr & Hs & Hc) & Ht). split; [done|]. exists nd; repeat split; auto.
  - rewrite IH. cbn. split.
    + intros (Hc & nd & Ha & Hp & Hl & Hr & Hs & Ht). split; [|done]. exists nd. repeat split; auto.
    + intros ((nd & Ha & Hp & Hl & Hr & Hs & Hc) & Ht). split; [done|]. exists nd; repeat split; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition links (nd : node) : Z * Z * Z := (n_par nd, n_lft nd, n_rgt nd).

(* [comment removed for export] *)
Definition lagree (X : list Z) (ns ns' : NS) : Prop :=
  forall a, a ∈ X -> links <$> (ns' !! a) = links <$> (ns !! a).

Lemma lagree_weaken X Y ns ns' : lagree Y ns ns' → (∀ a, a ∈ X → a ∈ Y) → lagree X ns ns'.
Proof. unfold lagree; eauto. Qed.

Lemma lagree_refl X ns : lagree X ns ns.
Proof. by intros a _. Qed.

Lemma lagree_trans X ns1 ns2 ns3 : lagree X ns1 ns2 → lagree X ns2 ns3 → lagree X ns1 ns3.
Proof. intros H1 H2 a Ha. by rewrite H2, H1. Qed.

Lemma lagree_lookup X ns ns' a nd :
  lagree X ns ns' → a ∈ X → ns !! a = Some nd →
  exists nd', ns' !! a = Some nd' /\ n_par nd' = n_par nd /\ n_lft nd' = n_lft nd /\ n_rgt nd' = n_rgt nd.
Proof.
  intros HL Ha Hnd. specialize (HL a Ha). rewrite Hnd in HL. cbn in HL.
  destruct (ns' !! a) as [nd'|]; cbn in HL; [|congruence].
  exists nd'. unfold links in HL. inversion HL. auto.
Qed.

Lemma tree_at_frame ns ns' t p : lagree (inorder t) ns ns' → tree_at ns t p → tree_at ns' t p.
Proof.
  revert p; induction t as [|l IHl a r IHr]; intros p HL; cbn; [done|].
  intros (nd & Ha & Hp & Hlf & Hrg & Hl & Hr).
  destruct (lagree_lookup _ _ _ a nd HL) as (nd' & Ha' & E1 & E2 & E3); [set_solver|done|].
  exists nd'. rewrite E1, E2, E3. repeat split; auto.
  - apply IHl; [|done]. eapply lagree_weaken; [done|set_solver].
  - apply IHr; [|done]. eapply lagree_weaken; [done|set_solver].
Qed.

Lemma ctx_at_frame ns ns' h c f : lagree (h :: cnodes c) ns ns' → ctx_at ns h c f → ctx_at ns' h c f.
Proof.
  revert f; induction c as [|a s up IH|s a up IH]; intros f HL; cbn.
  - intros (hd & Hh & Hp). destruct (lagree_lookup _ _ _ h hd HL) as (hd' & Hh' & E1 & _); [set_solver|done|].
    exists hd'. rewrite E1. auto.
  - intros (nd & Ha & Hp & Hlf & Hrg & Hs & Hc).
    destruct (lagree_lookup _ _ _ a nd HL) as (nd' & Ha' & E1 & E2 & E3); [set_solver|done|].
    exists nd'. rewrite E1, E2, E3. repeat split; auto.
    + eapply tree_at_frame; [|done]. eapply lagree_weaken; [done|set_solver].
    + apply IH; [|done]. eapply lagree_weaken; [done|set_solver].
  - intros (nd & Ha & Hp & Hlf & Hrg & Hs & Hc).
    destruct (lagree_lookup _ _ _ a nd HL) as (nd' & Ha' & E1 & E2 & E3); [set_solver|done|].
    exists nd'. rewrite E1, E2, E3. repeat split; auto.
    + eapply tree_at_frame; [|done]. eapply lagree_weaken; [done|set_solver].
    + apply IH; [|done]. eapply lagree_weaken; [done|set_solver].
Qed.

(* [comment removed for export] *)
Lemma lagree_set_col X ns a nd v : ns !! a = Some nd → lagree X ns (<[a := set_col v nd]> ns).
Proof.
  intros Ha b _. destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert_eq, Ha. by destruct nd.
  - by rewrite lookup_insert_ne.
Qed.

(* [comment removed for export] *)
Lemma lagree_insert_notin X ns a nd : a ∉ X → lagree X ns (<[a := nd]> ns).
Proof. intros Hn b Hb. rewrite lookup_insert_ne; [done|set_solver]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma troot_in t : t ≠ Leaf → troot t ∈ inorder t.
Proof. destruct t; cbn; [congruence|set_solver]. Qed.

Lemma troot_cases t : t = Leaf ∧ troot t = 0 ∨ t ≠ Leaf ∧ troot t ∈ inorder t.
Proof. destruct t; cbn; [left; auto|right; split; [congruence|set_solver]]. Qed.

Lemma inorder_nil t : inorder t = [] ↔ t = Leaf.
Proof. destruct t; cbn; split; try congruence. intros H. destruct (inorder t1); inversion H. Qed.

Lemma tree_at_root_lookup ns l a r p :
  tree_at ns (Node l a r) p → exists nd, ns !! a = Some nd ∧ n_par nd = p ∧ n_lft nd = troot l ∧ n_rgt nd = troot r.
Proof. cbn. intros (nd & ? & ? & ? & ? & _). eauto. Qed.

(* [comment removed for export] *)
Lemma tree_at_lookup ns t p a : tree_at ns t p → a ∈ inorder t → is_Some (ns !! a).
Proof.
  revert p; induction t as [|l IHl b r IHr]; intros p; cbn; [set_solver|].
  intros (nd & Hb & _ & _ & _ & Hl & Hr) Ha. rewrite elem_of_app, elem_of_cons in Ha.
  destruct Ha as [Ha|[->|Ha]]; [by eapply IHl| by rewrite Hb | by eapply IHr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma decomp_node T a : a ∈ inorder T → exists c l r, T = plug c (Node l a r).
Proof.
  induction T as [|l IHl b r IHr]; cbn; [set_solver|].
  rewrite elem_of_app, elem_of_cons. intros [Ha|[->|Ha]].
  - destruct (IHl Ha) as (c & l' & r' & E).
    exists (ccomp c (GoL b r Top)), l', r'. by rewrite plug_ccomp, <-E.
  - by exists Top, l, r.
  - destruct (IHr Ha) as (c & l' & r' & E).
    exists (ccomp c (GoR l b Top)), l', r'. by rewrite plug_ccomp, <-E.
Qed.

(* [comment removed for export] *)
Lemma decomp_node_in c0 T a : a ∈ inorder T → exists c l r, plug c0 T = plug c (Node l a r) ∧
   lfr c ++ inorder l ++ a :: inorder r ++ rfr c = lfr c0 ++ inorder T ++ rfr c0.
Proof.
  intros Ha. destruct (decomp_node T a Ha) as (c & l & r & ->).
  exists (ccomp c c0), l, r. rewrite plug_ccomp. split; [done|].
  rewrite lfr_ccomp, rfr_ccomp, inorder_plug. cbn. by rewrite <-!app_assoc.
Qed.

(* [comment removed for export] *)
Lemma decomp_max t : t ≠ Leaf → exists c lm, t = plug c (Node lm (tmax 0 t) Leaf) ∧ allR c.
Proof.
  induction t as [|l IHl a r IHr]; [congruence|intros _].
  destruct r as [|rl b rr].
  - exists Top, l. cbn. split; [|done]. unfold tmax. cbn. by rewrite llast_app_cons.
  - destruct IHr as (c & lm & E & HR); [congruence|].
    exists (ccomp c (GoR l a Top)), lm. rewrite plug_ccomp. cbn.
    replace (tmax 0 (Node l a (Node rl b rr))) with (tmax 0 (Node rl b rr)).
    + rewrite <-E. split; [done|]. clear -HR. induction c; cbn in *; tauto.
    + unfold tmax. cbn. by rewrite !llast_app_cons.
Qed.

Lemma tmax_indep h h' t : t ≠ Leaf → tmax h t = tmax h' t.
Proof. destruct t; cbn; [congruence|]. intros _. unfold tmax; cbn. by rewrite !llast_app_cons. Qed.

Lemma tmin_indep h h' t : t ≠ Leaf → tmin h t = tmin h' t.
Proof.
  destruct t as [|l a r]; cbn; [congruence|]. intros _. unfold tmin; cbn.
  destruct (inorder l); reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint allL (c : ctx) : Prop :=
  match c with Top => True | GoR _ _ _ => False | GoL _ _ up => allL up end.

Lemma lfr_allL c : allL c → lfr c = [].
Proof. induction c; cbn; tauto. Qed.

Lemma decomp_min t : t ≠ Leaf → exists c rm, t = plug c (Node Leaf (tmin 0 t) rm) ∧ allL c.
Proof.
  induction t as [|l IHl a r IHr]; [congruence|intros _].
  destruct l as [|ll b lr].
  - exists Top, r. cbn. split; done.
  - destruct IHl as (c & rm & E & HL); [congruence|].
    exists (ccomp c (GoL a r Top)), rm. rewrite plug_ccomp. cbn.
    replace (tmin 0 (Node (Node ll b lr) a r)) with (tmin 0 (Node ll b lr)).
    + rewrite <-E. split; [done|]. clear -HL. induction c; cbn in *; tauto.
    + unfold tmin. cbn. rewrite <-app_assoc. cbn. by destruct (inorder ll).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rb_repT (h : Z) (T : tree) (ns : NS) : Prop :=
  (exists hd, ns !! h = Some hd /\ n_par hd = troot T /\ n_lft hd = tmin h T /\ n_rgt hd = tmax h T)
  /\ tree_at ns T h
  /\ NoDup (0 :: h :: inorder T).

(* [comment removed for export] *)
Definition dom_exact (h : Z) (T : tree) (ns : NS) : Prop :=
  forall a, is_Some (ns !! a) <-> a = h \/ a ∈ inorder T.

(* [comment removed for export] *)
Definition col_ok (nd : node) : Prop := n_col nd = RED \/ n_col nd = BLACK.
Definition cols_ok (X : list Z) (ns : NS) : Prop :=
  forall a nd, ns !! a = Some nd -> a ∉ X -> col_ok nd.

Definition rb_okT (h : Z) (T : tree) (ns : NS) : Prop :=
  rb_repT h T ns /\ dom_exact h T ns /\ cols_ok [] ns.

(* [comment removed for export] *)
Definition rb_ok (h : Z) (S : list Z) (ns : NS) : Prop :=
  exists T, inorder T = S /\ rb_okT h T ns.

(* [comment removed for export] *)
Definition rb_rep (h : Z) (S : list Z) (ns : NS) : Prop :=
  exists T, inorder T = S /\ rb_repT h T ns.

Lemma rb_ok_rep h S ns : rb_ok h S ns → rb_rep h S ns.
Proof. intros (T & HS & HR & _). by exists T. Qed.

Lemma rb_rep_nodup h S ns : rb_rep h S ns → NoDup (0 :: h :: S).
Proof. by intros (T & <- & _ & _ & N). Qed.

Lemma rb_ok_dom h S ns a : rb_ok h S ns → is_Some (ns !! a) ↔ a = h ∨ a ∈ S.
Proof. intros (T & <- & _ & D & _). apply D. Qed.

(* [comment removed for export] *)
Lemma rb_okT_empty h col :
  h ≠ 0 → col = RED ∨ col = BLACK → rb_okT h Leaf {[ h := mkNode 0 h h col ]}.
Proof.
  intros Hh Hc. repeat split; cbn.
  - exists (mkNode 0 h h col). by rewrite lookup_singleton_eq.
  - apply NoDup_cons. split; [set_solver|]. apply NoDup_cons. split; [set_solver|]. constructor.
  - intros Hs. left. destruct (decide (a = h)) as [->|Hne]; [done|].
    rewrite lookup_singleton_ne in Hs; [by inversion Hs|done].
  - intros [->|Hin]; [by rewrite lookup_singleton_eq|set_solver].
  - intros a nd Ha _. destruct (decide (a = h)) as [->|Hne].
    + rewrite lookup_singleton_eq in Ha. inversion Ha; subst. exact Hc.
    + by rewrite lookup_singleton_ne in Ha.
Qed.

Lemma rb_ok_empty h : h ≠ 0 → rb_ok h [] {[ h := init_header_node h ]}.
Proof. intros Hh. exists Leaf. split; [done|]. apply rb_okT_empty; [done|by left]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lhead_app d (l1 l2 : list Z) : lhead d (l1 ++ l2) = lhead (lhead d l2) l1.
Proof. by destruct l1. Qed.
Lemma llast_cons d x (l : list Z) : llast d (x :: l) = llast x l.
Proof. unfold llast. cbn. destruct l; [done|]. apply last_cons_indep. Qed.
Lemma llast_nil (d : Z) : llast d [] = d.
Proof. reflexivity. Qed.
Lemma llast_cons_indep (d d' x : Z) l : llast d (x :: l) = llast d' (x :: l).
Proof. by rewrite !llast_cons. Qed.
Lemma llast_app d (l1 l2 : list Z) : llast d (l1 ++ l2) = llast (llast d l1) l2.
Proof.
  destruct l2 as [|x l2]; [by rewrite app_nil_r|]. by rewrite llast_app_cons, llast_cons.
Qed.
Lemma tmin_plug h c t : tmin h (plug c t) = lhead (lhead (lhead h (rfr c)) (inorder t)) (lfr c).
Proof. unfold tmin. by rewrite inorder_plug, !lhead_app. Qed.
Lemma tmax_plug h c t : tmax h (plug c t) = llast (llast (llast h (lfr c)) (inorder t)) (rfr c).
Proof. unfold tmax. by rewrite inorder_plug, !llast_app. Qed.

