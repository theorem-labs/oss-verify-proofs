(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma parent_in ns t p a nd :
  tree_at ns t p → a ∈ inorder t → ns !! a = Some nd →
  (a = troot t ∧ n_par nd = p) ∨ n_par nd ∈ inorder t.
Proof.
  revert p; induction t as [|l IHl b r IHr]; intros p; cbn; [set_solver|].
  intros (ndb & Hb & Hp & _ & _ & Hl & Hr) Ha Hnd.
  rewrite elem_of_app, elem_of_cons in Ha. destruct Ha as [Ha|[->|Ha]].
  - destruct (IHl _ Hl Ha Hnd) as [[_ E]|E]; right; [rewrite E|]; set_solver.
  - rewrite Hb in Hnd. inversion Hnd; subst. left; auto.
  - destruct (IHr _ Hr Ha Hnd) as [[_ E]|E]; right; [rewrite E|]; set_solver.
Qed.

Lemma ctx_node_in h c : ctx_node h c = h ∨ ctx_node h c ∈ cnodes c.
Proof. destruct c; cbn; [by left|right; set_solver|right; set_solver]. Qed.

Lemma ctx_at_node_lookup ns h c f : ctx_at ns h c f → is_Some (ns !! ctx_node h c).
Proof. destruct c; cbn; intros (nd & -> & _); done. Qed.

Lemma tmin_in h t : t ≠ Leaf → tmin h t ∈ inorder t.
Proof. intros Ht. unfold tmin. apply lhead_in. by intros E%inorder_nil. Qed.
Lemma tmax_in h t : t ≠ Leaf → tmax h t ∈ inorder t.
Proof. intros Ht. unfold tmax. apply llast_in. by intros E%inorder_nil. Qed.
Lemma tmin_leaf h : tmin h Leaf = h. Proof. done. Qed.
Lemma tmax_leaf h : tmax h Leaf = h. Proof. done. Qed.

Section WithRep.
  Context (h : Z) (T : tree) (ns : NS).

  Lemma rep_N : rb_repT h T ns → NoDup (0 :: h :: inorder T).  Proof. intros HR; exact (proj2 (proj2 HR)). Qed.
  Lemma rep_h_ne0 : rb_repT h T ns → h ≠ 0.  Proof. intros HR%rep_N. nd_neq_with HR. Qed.
  Lemma rep_node_ne0 a : rb_repT h T ns → a ∈ inorder T → a ≠ 0.  Proof. intros HR%rep_N ?; nd_neq_with HR. Qed.
  Lemma rep_node_neh a : rb_repT h T ns → a ∈ inorder T → a ≠ h.  Proof. intros HR%rep_N ?; nd_neq_with HR. Qed.
  Lemma rep_nodup : rb_repT h T ns → NoDup (inorder T).  Proof. intros HR%rep_N. exact (nd_cons_tl _ _ (nd_cons_tl _ _ HR)). Qed.
  Lemma rep_hd : rb_repT h T ns → exists hd, ns !! h = Some hd /\ n_par hd = troot T /\ n_lft hd = tmin h T /\ n_rgt hd = tmax h T.
  Proof. intros HR; exact (proj1 HR). Qed.
  Lemma rep_tree : rb_repT h T ns → tree_at ns T h.  Proof. intros HR; exact (proj1 (proj2 HR)). Qed.
  Lemma rep_top : rb_repT h T ns → top_at ns h T.
  Proof. intros HR. split; [|by apply rep_tree]. destruct (rep_hd HR) as (hd & ? & ? & _); eauto. Qed.

  Lemma rep_troot_0 : rb_repT h T ns → troot T = 0 ↔ T = Leaf.
  Proof.
    intros HR. split; [|by intros ->]. intros E. destruct (troot_cases T) as [[? _]|[_ Hin]]; [done|].
    exfalso. by apply (rep_node_ne0 (troot T) HR Hin).
  Qed.

  Lemma sub_troot_0 t : rb_repT h T ns → (∀ a, a ∈ inorder t → a ∈ inorder T) → troot t = 0 ↔ t = Leaf.
  Proof.
    intros HR Hsub. split; [|by intros ->]. intros E. destruct (troot_cases t) as [[? _]|[_ Hin]]; [done|].
    exfalso. apply (rep_node_ne0 (troot t) HR); [by apply Hsub|done].
  Qed.
End WithRep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem is_header_header h T ns : rb_repT h T ns → is_header ns h = Some true.
Proof.
  intros HR. pose proof (rep_N _ _ _ HR) as N.
  destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & Hl & Hr).
  unfold is_header. unfold_prims. rewrite Hh. red_binds. rewrite Hp.
  destruct (troot_cases T) as [[HT E0]|[HT Hrt]]; [by rewrite E0|].
  rewrite (Zeqb_ne (troot T) 0) by nd_neq_with N. rewrite Hl, Hr.
  pose proof (tmin_in h T HT) as Hmin. pose proof (tmax_in h T HT) as Hmax.
  rewrite (Zeqb_ne (tmin h T) 0) by nd_neq_with N.
  rewrite (Zeqb_ne (tmax h T) 0) by nd_neq_with N.
  destruct (Z.eqb_spec (tmin h T) (tmax h T)) as [E|NE]; [done|].
  destruct (tree_at_lookup ns T h (tmin h T) (rep_tree _ _ _ HR) Hmin) as [ndm Hndm].
  rewrite Hndm. red_binds.
  destruct (Z.eqb_spec (n_par ndm) h) as [Em|NEm]; cbn; [|done].
  destruct (tree_at_lookup ns T h (tmax h T) (rep_tree _ _ _ HR) Hmax) as [ndx Hndx].
  rewrite Hndx. red_binds.
  destruct (Z.eqb_spec (n_par ndx) h) as [Ex|NEx]; cbn; [|done].
  exfalso.
  destruct (parent_in ns T h _ _ (rep_tree _ _ _ HR) Hmin Hndm) as [[E1 _]|E1];
    [|rewrite Em in E1; by apply (rep_node_neh _ _ _ h HR)].
  destruct (parent_in ns T h _ _ (rep_tree _ _ _ HR) Hmax Hndx) as [[E2 _]|E2];
    [|rewrite Ex in E2; by apply (rep_node_neh _ _ _ h HR)].
  congruence.
Qed.

Theorem is_header_node h T ns a : rb_repT h T ns → a ∈ inorder T → is_header ns a = Some false.
Proof.
  intros HR Ha. pose proof (rep_N _ _ _ HR) as N.
  destruct (decomp_node T a Ha) as (c & l & r & ET).
  pose proof (rep_top _ _ _ HR) as HT. rewrite ET in HT. apply top_at_plug in HT as [HC Ht].
  cbn in Ht. destruct Ht as (nd & Hnd & Hp & Hl & Hr & Htl & Htr).
  rewrite ET in N. norm_list_in N.
  unfold is_header. unfold_prims. rewrite Hnd. red_binds. rewrite Hp, Hl, Hr.
  assert (Hpar : ctx_node h c ≠ 0).
  { destruct c as [|b s up|s b up]; cbn in *; nd_neq_with N. }
  rewrite (Zeqb_ne _ _ Hpar).
  destruct (troot_cases l) as [[-> El]|[Hl0 Hlin]]; [done|].
  rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N.
  destruct (troot_cases r) as [[-> Er]|[Hr0 Hrin]]; [done|].
  rewrite (Zeqb_ne (troot r) 0) by nd_neq_with N.
  rewrite (Zeqb_ne (troot l) (troot r)) by nd_neq_with N.
  destruct l as [|ll la lr]; [done|]. cbn in Htl. destruct Htl as (ndl & Hndl & Hpl & _). cbn. rewrite Hndl. red_binds.
  rewrite Hpl, Z.eqb_refl. cbn.
  destruct r as [|rl ra rr]; [done|]. cbn in Htr. destruct Htr as (ndr & Hndr & Hpr & _). cbn. rewrite Hndr. red_binds.
  by rewrite Hpr, Z.eqb_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maximum_step_eq ns n nd : ns !! n = Some nd →
  maximum_step ns n = Some (if n_rgt nd =? 0 then inr n else inl (n_rgt nd)).
Proof. intros H. unfold maximum_step. unfold_prims. rewrite H. by red_binds. Qed.
Lemma minimum_step_eq ns n nd : ns !! n = Some nd →
  minimum_step ns n = Some (if n_lft nd =? 0 then inr n else inl (n_lft nd)).
Proof. intros H. unfold minimum_step. unfold_prims. rewrite H. by red_binds. Qed.

Lemma maximum_spec ns t p N0 fuel :
  tree_at ns t p → t ≠ Leaf → NoDup (0 :: N0 ++ inorder t) → (theight t <= fuel)%nat →
  maximum fuel ns (troot t) = Some (tmax 0 t).
Proof.
  unfold maximum. revert p N0 fuel. induction t as [|l IHl a r IHr]; intros p N0 fuel Ht Hne N Hf; [done|].
  cbn in Ht. destruct Ht as (nd & Ha & Hp & Hl & Hr & Htl & Htr).
  destruct fuel as [|fuel]; [cbn in Hf; lia|].
  rewrite oloop_S. cbn [troot]. rewrite (maximum_step_eq _ _ _ Ha). red_binds.
  rewrite Hr. destruct (troot_cases r) as [[-> Er]|[Hr0 Hrin]].
  - cbn. unfold tmax. cbn. by rewrite llast_app_cons.
  - norm_list_in N. rewrite (Zeqb_ne (troot r) 0) by nd_neq_with N.
    rewrite (tmax_indep 0 a (Node l a r)) by done.
    unfold tmax. cbn [inorder]. rewrite llast_app_cons. change (llast a (inorder r)) with (tmax a r).
    rewrite <-(tmax_indep 0 a r) by done.
    apply (IHr a (N0 ++ inorder l ++ [a])); [done|done| |cbn in Hf; lia].
    by repeat (rewrite <-app_assoc; cbn).
Qed.

Lemma minimum_spec ns t p N0 fuel :
  tree_at ns t p → t ≠ Leaf → NoDup (0 :: N0 ++ inorder t) → (theight t <= fuel)%nat →
  minimum fuel ns (troot t) = Some (tmin 0 t).
Proof.
  unfold minimum. revert p N0 fuel. induction t as [|l IHl a r IHr]; intros p N0 fuel Ht Hne N Hf; [done|].
  cbn in Ht. destruct Ht as (nd & Ha & Hp & Hl & Hr & Htl & Htr).
  destruct fuel as [|fuel]; [cbn in Hf; lia|].
  rewrite oloop_S. cbn [troot]. rewrite (minimum_step_eq _ _ _ Ha). red_binds.
  rewrite Hl. destruct (troot_cases l) as [[-> El]|[Hl0 Hlin]].
  - done.
  - norm_list_in N. rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N.
    rewrite (tmin_indep 0 a (Node l a r)) by done.
    unfold tmin. cbn [inorder].
    transitivity (Some (lhead a (inorder l))).
    2:{ destruct (inorder l) eqn:E; [by apply inorder_nil in E|done]. }
    change (lhead a (inorder l)) with (tmin a l). rewrite <-(tmin_indep 0 a l) by done.
    apply (IHl a N0); [done|done| |cbn in Hf; lia].
    apply (nd_app_hd _ (a :: inorder r)). cbn. rewrite <-app_assoc. exact N.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cdepth_theight c t : (cdepth c + theight t <= theight (plug c t))%nat.
Proof.
  revert t; induction c as [|a s up IH|s a up IH]; intros t; cbn; [lia| |];
  (etransitivity; [|apply IH]); cbn; lia.
Qed.

Lemma prev_climb_step_eq ns cur ndc ndx :
  ns !! cur = Some ndc → ns !! (n_par ndc) = Some ndx →
  prev_climb_step ns cur = Some (if cur =? n_lft ndx then inl (n_par ndc) else inr (n_par ndc)).
Proof. intros H1 H2. unfold prev_climb_step. unfold_prims. rewrite H1. red_binds. rewrite H2. by red_binds. Qed.

(* [comment removed for export] *)
Fixpoint lprev (d : Z) (S : list Z) (a : Z) : Z :=
  match S with [] => d | x :: S' => if x =? a then d else lprev x S' a end.

Lemma lprev_app_hit d A b a B : NoDup (A ++ b :: a :: B) → lprev d (A ++ b :: a :: B) a = b.
Proof.
  revert d. induction A as [|x A IH]; intros d N; cbn.
  - rewrite (Zeqb_ne b a) by nd_neq_with N. by rewrite Z.eqb_refl.
  - rewrite (Zeqb_ne x a) by nd_neq_with N. apply IH. exact (nd_cons_tl _ _ N).
Qed.

Lemma lprev_first d a B : lprev d (a :: B) a = d.
Proof. cbn. by rewrite Z.eqb_refl. Qed.

(* [comment removed for export] *)
Lemma pred_unique (A1 B1 A2 B2 : list Z) (a b1 b2 : Z) :
  NoDup (A1 ++ b1 :: a :: B1) → A1 ++ b1 :: a :: B1 = A2 ++ b2 :: a :: B2 → b1 = b2.
Proof.
  intros N E.
  transitivity (lprev 0 (A1 ++ b1 :: a :: B1) a); [symmetry; by apply lprev_app_hit|].
  rewrite E. apply lprev_app_hit. by rewrite <-E.
Qed.

Lemma split_not_first (S : list Z) a d :
  a ∈ S → a ≠ lhead d S → exists A b B, S = A ++ b :: a :: B.
Proof.
  destruct S as [|x S]; [set_solver|]. cbn. intros Ha Hne.
  rewrite elem_of_cons in Ha. destruct Ha as [->|Ha]; [done|].
  clear Hne. revert x. induction S as [|y S IH]; intros x; [set_solver|].
  rewrite elem_of_cons in Ha. destruct Ha as [->|Ha].
  - by exists [], x, S.
  - destruct (IH Ha y) as (A & b & B & E). exists (x :: A), b, B. cbn. by rewrite E.
Qed.

Theorem prev_node_header h T ns fuel :
  rb_repT h T ns → prev_node fuel ns h = Some (tmax h T).
Proof.
  intros HR. unfold prev_node. rewrite (is_header_header _ _ _ HR). red_binds.
  destruct (rep_hd _ _ _ HR) as (hd & Hh & _ & _ & Hr). unfold_prims. rewrite Hh. red_binds. by rewrite Hr.
Qed.

Lemma list_snoc_or_nil (l : list Z) : l = [] ∨ exists l' x, l = l' ++ [x].
Proof.
  induction l as [|y l IH]; [by left|right].
  destruct IH as [->|(l' & x & ->)]; [by exists [], y|by exists (y :: l'), x].
Qed.

Theorem prev_node_node h T ns fuel A b a B :
  rb_repT h T ns → inorder T = A ++ b :: a :: B → (theight T <= fuel)%nat →
  prev_node fuel ns a = Some b.
Proof.
  intros HR HS Hf. pose proof (rep_N _ _ _ HR) as N.
  assert (Ha : a ∈ inorder T) by (rewrite HS; set_solver).
  assert (NAB : NoDup (A ++ b :: a :: B)) by (rewrite <-HS; exact (nd_cons_tl _ _ (nd_cons_tl _ _ N))).
  unfold prev_node. rewrite (is_header_node _ _ _ _ HR Ha). red_binds.
  destruct (decomp_node T a Ha) as (c & l & r & ET).
  pose proof (rep_top _ _ _ HR) as HT. rewrite ET in HT. apply top_at_plug in HT as [HC Ht].
  pose proof Ht as Ht'. cbn in Ht. destruct Ht as (nd & Hnd & Hp & Hl & Hr & Htl & Htr).
  unfold_prims. rewrite Hnd. red_binds. rewrite Hl.
  pose proof (cdepth_theight c (Node l a r)) as Hd. rewrite <-ET in Hd. cbn in Hd.
  destruct (troot_cases l) as [[-> El]|[Hl0 Hlin]].
  - (* [comment removed for export] *) cbn.
    (* [comment removed for export] *)
    assert (CL : ∀ n c' t' cur, T = plug c' t' → t' ≠ Leaf → cur = troot t' →
              lhead 0 (inorder t') = a → (cdepth c' < n)%nat →
              oloop n (prev_climb_step ns) cur = Some b).
    { induction n as [|n IH]; intros c' t' cur ET' Ht'0 Hcur Hfirst Hn; [lia|].
      rewrite oloop_S.
      pose proof (rep_top _ _ _ HR) as HT2. rewrite ET' in HT2. apply top_at_plug in HT2 as [HC2 Ht2].
      destruct t' as [|l' x r']; [done|]. cbn in Hcur. subst cur.
      cbn in Ht2. destruct Ht2 as (ndx & Hx & Hpx & _).
      pose proof N as N2. rewrite ET' in N2. norm_list_in N2.
      destruct c' as [|u s up|s u up]; cbn in Hpx, HC2.
      + (* [comment removed for export] *)
        exfalso. cbn in ET'. pose proof N as N3. rewrite HS in N3. rewrite ET' in HS. rewrite HS in Hfirst.
        destruct A as [|a0 A']; cbn in Hfirst.
        { enough (b ≠ a) by tauto. nd_neq_with N3. }
        subst a0. cbn in N3. clear -N3. apply NoDup_cons in N3 as [_ N3]. apply NoDup_cons in N3 as [_ N3].
        apply NoDup_cons in N3 as [X _]. apply X. set_solver.
      + destruct HC2 as (ndu & Hu & Hpu & Hlu & Hru & Hs & HCup).
        rewrite (prev_climb_step_eq ns x ndx ndu Hx) by (by rewrite Hpx). rewrite Hpx, Hlu, Z.eqb_refl. cbn.
        apply (IH up (Node (Node l' x r') u s)); [done|done|done| |cbn in Hn; lia].
        cbn. rewrite <-app_assoc. cbn in Hfirst |- *. by destruct (inorder l').
      + destruct HC2 as (ndu & Hu & Hpu & Hlu & Hru & Hs & HCup).
        rewrite (prev_climb_step_eq ns x ndx ndu Hx) by (by rewrite Hpx). rewrite Hpx, Hlu.
        rewrite (Zeqb_ne x (troot s)).
        2:{ destruct (troot_cases s) as [[-> Es]|[Hs0 Hsin]]; [cbn; nd_neq_with N2|nd_neq_with N2]. }
        cbn. f_equal.
        (* [comment removed for export] *)
        cbn in ET'. rewrite ET', inorder_plug in HS. cbn in HS. cbn in Hfirst.
        destruct (inorder l' ++ x :: inorder r') as [|a0 rest] eqn:EN.
        { exfalso. destruct (inorder l'); inversion EN. }
        cbn in Hfirst. subst a0.
        assert (E : (lfr up ++ inorder s) ++ u :: a :: (rest ++ rfr up) = A ++ b :: a :: B).
        { rewrite <-HS. list_eq. }
        exact (eq_sym (pred_unique _ _ _ _ _ _ _ NAB (eq_sym E))). }
    apply (CL fuel c (Node Leaf a r) a); [done|done|done|done|lia].
  - (* [comment removed for export] *)
    pose proof N as N2. rewrite ET in N2. norm_list_in N2.
    rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N2. cbn.
    rewrite (maximum_spec ns l a (h :: lfr c) fuel Htl Hl0); [| |cbn in Hf; lia].
    2:{ apply (nd_app_hd _ (a :: inorder r ++ rfr c)). cbn. rewrite <-app_assoc. exact N2. }
    f_equal.
    rewrite ET, inorder_plug in HS. cbn in HS.
    assert (HL : inorder l ≠ []) by (intros EL%inorder_nil; done).
    destruct (list_snoc_or_nil (inorder l)) as [EL|(L & m0 & EL)].
    + done.
    + unfold tmax. rewrite EL. rewrite llast_app_cons. cbn.
      rewrite EL in HS.
      assert (E : (lfr c ++ L) ++ m0 :: a :: (inorder r ++ rfr c) = A ++ b :: a :: B).
      { rewrite <-HS. list_eq. }
      first [exact (pred_unique _ _ _ _ _ _ _ NAB (eq_sym E)) | exact (eq_sym (pred_unique _ _ _ _ _ _ _ NAB (eq_sym E)))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ubT (cmpU : Z → bool) (t : tree) (y : Z) : Z :=
  match t with
  | Leaf => y
  | Node l a r => if cmpU a then ubT cmpU l a else ubT cmpU r y
  end.

Fixpoint lbT (cmpL : Z → bool) (t : tree) (y : Z) : Z :=
  match t with
  | Leaf => y
  | Node l a r => if cmpL a then lbT cmpL r y else lbT cmpL l a
  end.

Lemma upper_bound_step_eq cmpU ns x y nd : ns !! x = Some nd →
  upper_bound_step cmpU ns (x, y) =
    Some (let x' := (if cmpU x then n_lft nd else n_rgt nd) in
          let y' := (if cmpU x then x else y) in
          if x' =? 0 then inr y' else inl (x', y')).
Proof. intros H. unfold upper_bound_step, load. rewrite H. red_binds. by destruct (cmpU x). Qed.

Lemma lower_bound_step_eq cmpL ns x y nd : ns !! x = Some nd →
  lower_bound_step cmpL ns (x, y) =
    Some (let x' := (if cmpL x then n_rgt nd else n_lft nd) in
          let y' := (if cmpL x then y else x) in
          if x' =? 0 then inr y' else inl (x', y')).
Proof. intros H. unfold lower_bound_step, load. rewrite H. red_binds. by destruct (cmpL x). Qed.

(* [comment removed for export] *)
Lemma upper_bound_oloop cmpU ns t p y N0 fuel :
  tree_at ns t p → t ≠ Leaf → NoDup (0 :: N0 ++ inorder t) → (theight t <= fuel)%nat →
  oloop fuel (upper_bound_step cmpU ns) (troot t, y) = Some (ubT cmpU t y).
Proof.
  revert p y N0 fuel. induction t as [|l IHl a r IHr]; intros p y N0 fuel Ht Hne N Hf; [done|].
  cbn in Ht. destruct Ht as (nd & Ha & Hp & Hl & Hr & Htl & Htr).
  destruct fuel as [|fuel]; [cbn in Hf; lia|].
  rewrite oloop_S. cbn [troot]. rewrite (upper_bound_step_eq _ _ _ _ _ Ha). cbn [ubT].
  destruct (cmpU a); cbn zeta.
  - rewrite Hl. destruct (troot_cases l) as [[-> El]|[Hl0 Hlin]]; [done|].
    norm_list_in N. rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N. cbn.
    apply (IHl a a N0); [done|done| |cbn in Hf; lia].
    apply (nd_app_hd _ (a :: inorder r)). cbn. rewrite <-app_assoc. exact N.
  - rewrite Hr. destruct (troot_cases r) as [[-> Er]|[Hr0 Hrin]]; [done|].
    norm_list_in N. rewrite (Zeqb_ne (troot r) 0) by nd_neq_with N. cbn.
    apply (IHr a y (N0 ++ inorder l ++ [a])); [done|done| |cbn in Hf; lia].
    by repeat (rewrite <-app_assoc; cbn).
Qed.

Lemma lower_bound_oloop cmpL ns t p y N0 fuel :
  tree_at ns t p → t ≠ Leaf → NoDup (0 :: N0 ++ inorder t) → (theight t <= fuel)%nat →
  oloop fuel (lower_bound_step cmpL ns) (troot t, y) = Some (lbT cmpL t y).
Proof.
  revert p y N0 fuel. induction t as [|l IHl a r IHr]; intros p y N0 fuel Ht Hne N Hf; [done|].
  cbn in Ht. destruct Ht as (nd & Ha & Hp & Hl & Hr & Htl & Htr).
  destruct fuel as [|fuel]; [cbn in Hf; lia|].
  rewrite oloop_S. cbn [troot]. rewrite (lower_bound_step_eq _ _ _ _ _ Ha). cbn [lbT].
  destruct (cmpL a); cbn zeta.
  - rewrite Hr. destruct (troot_cases r) as [[-> Er]|[Hr0 Hrin]]; [done|].
    norm_list_in N. rewrite (Zeqb_ne (troot r) 0) by nd_neq_with N. cbn.
    apply (IHr a y (N0 ++ inorder l ++ [a])); [done|done| |cbn in Hf; lia].
    by repeat (rewrite <-app_assoc; cbn).
  - rewrite Hl. destruct (troot_cases l) as [[-> El]|[Hl0 Hlin]]; [done|].
    norm_list_in N. rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N. cbn.
    apply (IHl a a N0); [done|done| |cbn in Hf; lia].
    apply (nd_app_hd _ (a :: inorder r)). cbn. rewrite <-app_assoc. exact N.
Qed.

(* [comment removed for export] *)
Theorem upper_bound_loop_spec cmpU h T ns y fuel :
  rb_repT h T ns → (theight T <= fuel)%nat →
  upper_bound_loop fuel cmpU ns (troot T) y = Some (ubT cmpU T y).
Proof.
  intros HR Hf. unfold upper_bound_loop.
  destruct (troot_cases T) as [[-> E]|[HT Hin]]; [done|].
  rewrite (Zeqb_ne _ _ (rep_node_ne0 _ _ _ _ HR Hin)).
  apply (upper_bound_oloop cmpU ns T h y [h]); [by apply rep_tree|done|exact (rep_N _ _ _ HR)|done].
Qed.

Theorem lower_bound_loop_spec cmpL h T ns y fuel :
  rb_repT h T ns → (theight T <= fuel)%nat →
  lower_bound_loop fuel cmpL ns (troot T) y = Some (lbT cmpL T y).
Proof.
  intros HR Hf. unfold lower_bound_loop.
  destruct (troot_cases T) as [[-> E]|[HT Hin]]; [done|].
  rewrite (Zeqb_ne _ _ (rep_node_ne0 _ _ _ _ HR Hin)).
  apply (lower_bound_oloop cmpL ns T h y [h]); [by apply rep_tree|done|exact (rep_N _ _ _ HR)|done].
Qed.

Theorem upper_bound_spec cmpU h T ns fuel :
  rb_repT h T ns → (theight T <= fuel)%nat →
  upper_bound fuel cmpU ns h = Some (ubT cmpU T h).
Proof.
  intros HR Hf. unfold upper_bound. destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & _).
  unfold_prims. rewrite Hh. red_binds. rewrite Hp. by apply (upper_bound_loop_spec cmpU h).
Qed.

Theorem lower_bound_spec cmpL h T ns fuel :
  rb_repT h T ns → (theight T <= fuel)%nat →
  lower_bound fuel cmpL ns h = Some (lbT cmpL T h).
Proof.
  intros HR Hf. unfold lower_bound. destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & _).
  unfold_prims. rewrite Hh. red_binds. rewrite Hp. by apply (lower_bound_loop_spec cmpL h).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ubT_in cmpU t y : ubT cmpU t y = y ∨ ubT cmpU t y ∈ inorder t.
Proof.
  revert y; induction t as [|l IHl a r IHr]; intros y; cbn; [by left|].
  destruct (cmpU a).
  - destruct (IHl a) as [->|H]; right; set_solver.
  - destruct (IHr y) as [->|H]; [by left|right; set_solver].
Qed.

Lemma lbT_in cmpL t y : lbT cmpL t y = y ∨ lbT cmpL t y ∈ inorder t.
Proof.
  revert y; induction t as [|l IHl a r IHr]; intros y; cbn; [by left|].
  destruct (cmpL a).
  - destruct (IHr y) as [->|H]; [by left|right; set_solver].
  - destruct (IHl a) as [->|H]; right; set_solver.
Qed.

(* [comment removed for export] *)
Definition all_false (f : Z → bool) (l : list Z) : Prop := ∀ x, x ∈ l → f x = false.
Definition all_true  (f : Z → bool) (l : list Z) : Prop := ∀ x, x ∈ l → f x = true.

Lemma split_app_cases (A B C D : list Z) :
  A ++ B = C ++ D →
  (exists E, A = C ++ E ∧ D = E ++ B) ∨ (exists E, C = A ++ E ∧ B = E ++ D).
Proof.
  revert C. induction A as [|x A IH]; intros C E.
  - right. exists C. split; [done|]. exact E.
  - destruct C as [|z C].
    + left. exists (x :: A). split; [done|]. cbn in E. by rewrite <-E.
    + cbn in E. injection E as -> E'. destruct (IH C E') as [(F & -> & ->)|(F & -> & ->)].
      * left. by exists F.
      * right. by exists F.
Qed.

Lemma ubT_split cmpU t : ∀ y A B,
  inorder t = A ++ B → all_false cmpU A → all_true cmpU B →
  ubT cmpU t y = lhead y B.
Proof.
  induction t as [|l IHl a r IHr]; intros y A B E HA HB; cbn in E |- *.
  - destruct A; [|done]. destruct B; [done|done].
  - destruct (split_app_cases _ _ _ _ E) as [(F & EA & EB)|(F & EA & EB)].
    + (* [comment removed for export] *)
      rewrite (HB a) by (rewrite EB; set_solver).
      rewrite (IHl a A F); [|done|done|intros x Hx; apply HB; rewrite EB; set_solver].
      rewrite EB. by destruct F.
    + (* [comment removed for export] *)
      destruct F as [|f F].
      * cbn in EB. subst B. rewrite app_nil_r in EA. subst A.
        rewrite (HB a) by set_solver. cbn.
        apply (IHl a (inorder l) []); [by rewrite app_nil_r|done|intros ? Hx; inversion Hx].
      * cbn in EB. injection EB as <- EB. subst A.
        rewrite (HA a) by set_solver.
        apply (IHr y F B); [done| |done]. intros x Hx. apply HA. set_solver.
Qed.

Lemma lbT_split cmpL t : ∀ y A B,
  inorder t = A ++ B → all_true cmpL A → all_false cmpL B →
  lbT cmpL t y = lhead y B.
Proof.
  induction t as [|l IHl a r IHr]; intros y A B E HA HB; cbn in E |- *.
  - destruct A; [|done]. destruct B; [done|done].
  - destruct (split_app_cases _ _ _ _ E) as [(F & EA & EB)|(F & EA & EB)].
    + rewrite (HB a) by (rewrite EB; set_solver).
      rewrite (IHl a A F); [|done|done|intros x Hx; apply HB; rewrite EB; set_solver].
      rewrite EB. by destruct F.
    + destruct F as [|f F].
      * cbn in EB. subst B. rewrite app_nil_r in EA. subst A.
        rewrite (HB a) by set_solver. cbn.
        apply (IHl a (inorder l) []); [by rewrite app_nil_r|done|intros ? Hx; inversion Hx].
      * cbn in EB. injection EB as <- EB. subst A.
        rewrite (HA a) by set_solver.
        apply (IHr y F B); [done| |done]. intros x Hx. apply HA. set_solver.
Qed.

(* [comment removed for export] *)
Definition findT (cmpL cmpU : Z → bool) (T : tree) (h : Z) : Z :=
  let y := lbT cmpL T h in
  if y =? h then h else if cmpU y then h else y.

Theorem find_spec cmpL cmpU h T ns fuel :
  rb_repT h T ns → (theight T <= fuel)%nat →
  find fuel cmpL cmpU ns h = Some (findT cmpL cmpU T h).
Proof.
  intros HR Hf. unfold find, findT. destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & _).
  unfold_prims. rewrite Hh. red_binds. rewrite Hp.
  rewrite (lower_bound_loop_spec cmpL h) by done. red_binds.
  destruct (lbT cmpL T h =? h); [done|]. by destruct (cmpU _).
Qed.

Lemma findT_in cmpL cmpU T h : findT cmpL cmpU T h = h ∨ (findT cmpL cmpU T h ∈ inorder T ∧ findT cmpL cmpU T h ≠ h).
Proof.
  unfold findT. destruct (Z.eqb_spec (lbT cmpL T h) h) as [E|NE]; [by left|].
  destruct (cmpU _); [by left|]. right. destruct (lbT_in cmpL T h); [done|]. auto.
Qed.

(* [comment removed for export] *)
Lemma theight_le_length T S : inorder T = S → (theight T <= length S)%nat.
Proof. intros <-. apply theight_le_tsize. Qed.

(* [comment removed for export] *)

Corollary upper_bound_some cmpU h S ns fuel :
  rb_rep h S ns → (length S <= fuel)%nat →
  exists y, upper_bound fuel cmpU ns h = Some y ∧ (y = h ∨ y ∈ S).
Proof.
  intros (T & <- & HR) Hf. exists (ubT cmpU T h). split.
  - apply upper_bound_spec; [done|]. etransitivity; [apply theight_le_tsize|done].
  - apply ubT_in.
Qed.

Corollary lower_bound_some cmpL h S ns fuel :
  rb_rep h S ns → (length S <= fuel)%nat →
  exists y, lower_bound fuel cmpL ns h = Some y ∧ (y = h ∨ y ∈ S).
Proof.
  intros (T & <- & HR) Hf. exists (lbT cmpL T h). split.
  - apply lower_bound_spec; [done|]. etransitivity; [apply theight_le_tsize|done].
  - apply lbT_in.
Qed.

Corollary find_some cmpL cmpU h S ns fuel :
  rb_rep h S ns → (length S <= fuel)%nat →
  exists y, find fuel cmpL cmpU ns h = Some y ∧ (y = h ∨ (y ∈ S ∧ y ≠ h)).
Proof.
  intros (T & <- & HR) Hf. exists (findT cmpL cmpU T h). split.
  - apply find_spec; [done|]. etransitivity; [apply theight_le_tsize|done].
  - apply findT_in.
Qed.

(* [comment removed for export] *)
Theorem prev_node_spec h S ns fuel A B :
  rb_rep h S ns → S = A ++ B → A ≠ [] → (length S <= fuel)%nat →
  prev_node fuel ns (lhead h B) = Some (llast h A).
Proof.
  intros (T & HS & HR) -> HA Hf.
  destruct (list_snoc_or_nil A) as [->|(A' & b & ->)]; [done|].
  rewrite llast_app_cons. cbn. destruct B as [|a B]; cbn.
  - rewrite app_nil_r in HS. rewrite (prev_node_header h T ns fuel HR). f_equal.
    unfold tmax. rewrite HS. by rewrite llast_app_cons.
  - apply (prev_node_node h T ns fuel A' b a B HR); [by rewrite HS, <-app_assoc|].
    etransitivity; [apply theight_le_tsize|]. unfold tsize. by rewrite HS.
Qed.

Theorem is_header_spec h S ns a :
  rb_rep h S ns → (a = h ∨ a ∈ S) → is_header ns a = Some (a =? h).
Proof.
  intros (T & <- & HR) [->|Ha].
  - rewrite Z.eqb_refl. by apply (is_header_header h T).
  - rewrite (Zeqb_ne a h) by (by apply (rep_node_neh h T ns)). by apply (is_header_node h T).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ctx_node_in_plug h c t : ctx_node h c = h ∨ ctx_node h c ∈ inorder (plug c t).
Proof.
  destruct (ctx_node_in h c) as [E|Hin]; [by left|right].
  rewrite plug_nodes_perm. set_solver.
Qed.

Theorem rb_rep_closed h S ns x nd :
  rb_rep h S ns → x ∈ S → ns !! x = Some nd →
  (n_lft nd = 0 ∨ n_lft nd ∈ S) ∧ (n_rgt nd = 0 ∨ n_rgt nd ∈ S) ∧ (n_par nd = h ∨ n_par nd ∈ S)
  ∧ n_par nd ≠ 0 ∧ x ≠ 0 ∧ x ≠ h.
Proof.
  intros (T & <- & HR) Hx Hnd. pose proof (rep_N _ _ _ HR) as N.
  destruct (decomp_node T x Hx) as (c & l & r & ET).
  pose proof (rep_top _ _ _ HR) as HT. rewrite ET in HT. apply top_at_plug in HT as [HC Ht].
  cbn in Ht. destruct Ht as (nd' & Hnd' & Hp & Hl & Hr & _ & _). rewrite Hnd in Hnd'. injection Hnd' as <-.
  rewrite Hp, Hl, Hr. split_and!.
  - destruct (troot_cases l) as [[-> _]|[_ Hin]]; [by left|right]. rewrite ET, plug_nodes_perm. set_solver.
  - destruct (troot_cases r) as [[-> _]|[_ Hin]]; [by left|right]. rewrite ET, plug_nodes_perm. set_solver.
  - rewrite ET. apply ctx_node_in_plug.
  - destruct (ctx_node_in_plug h c (Node l x r)) as [E|Hin].
    + rewrite E. nd_neq_with N.
    + rewrite <-ET in Hin. nd_neq_with N.
  - nd_neq_with N.
  - nd_neq_with N.
Qed.

Theorem rb_rep_header h S ns hd :
  rb_rep h S ns → ns !! h = Some hd →
  (n_par hd = 0 ↔ S = []) ∧ (n_par hd = 0 ∨ n_par hd ∈ S)
  ∧ n_lft hd = lhead h S ∧ n_rgt hd = llast h S
  ∧ (S ≠ [] → n_lft hd ∈ S ∧ n_rgt hd ∈ S) ∧ h ≠ 0.
Proof.
  intros (T & <- & HR) Hh. pose proof (rep_N _ _ _ HR) as N.
  destruct (rep_hd _ _ _ HR) as (hd' & Hh' & Hp & Hl & Hr). rewrite Hh in Hh'. injection Hh' as <-.
  rewrite Hp, Hl, Hr. split_and!.
  - rewrite (rep_troot_0 _ _ _ HR). by rewrite <-inorder_nil.
  - destruct (troot_cases T) as [[-> _]|[_ Hin]]; auto.
  - done.
  - done.
  - intros HS. assert (HT : T ≠ Leaf) by (intros ->; by apply HS).
    split; [by apply tmin_in|by apply tmax_in].
  - nd_neq_with N.
Qed.
