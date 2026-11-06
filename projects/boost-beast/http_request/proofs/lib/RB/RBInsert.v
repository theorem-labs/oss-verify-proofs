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

Definition samedom (ns ns' : NS) : Prop := ∀ b, is_Some (ns' !! b) ↔ is_Some (ns !! b).

Lemma samedom_refl ns : samedom ns ns.  Proof. done. Qed.
Lemma samedom_trans ns1 ns2 ns3 : samedom ns1 ns2 → samedom ns2 ns3 → samedom ns1 ns3.
Proof. intros A B b. rewrite (B b). apply A. Qed.
Lemma samedom_insert ns a nd : is_Some (ns !! a) → samedom ns (<[a := nd]> ns).
Proof.
  intros Ha b. destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert_eq. split; auto.
  - by rewrite lookup_insert_ne.
Qed.
Lemma samedom_insert' ns ns0 a nd nd0 : ns !! a = Some nd0 → samedom ns0 ns → samedom ns0 (<[a := nd]> ns).
Proof. intros. eapply samedom_trans; [done|apply samedom_insert]. by eexists. Qed.

Lemma dom_exact_same h T T' ns ns' :
  dom_exact h T ns → samedom ns ns' → (∀ a, a ∈ inorder T' ↔ a ∈ inorder T) → dom_exact h T' ns'.
Proof. intros D S P a. rewrite (S a), (D a), (P a). done. Qed.

Lemma cols_ok_insert X ns a nd nd' :
  cols_ok X ns → ns !! a = Some nd → (n_col nd' = n_col nd ∨ col_ok nd' ∨ a ∈ X) →
  cols_ok X (<[a := nd']> ns).
Proof.
  intros C Ha Hc b ndb Hb Hnx. destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert_eq in Hb. injection Hb as <-.
    destruct Hc as [E|[E|E]]; [|done|done]. unfold col_ok. rewrite E. by apply (C b nd).
  - rewrite lookup_insert_ne in Hb by done. by apply (C b ndb).
Qed.

Lemma cols_ok_weaken X Y ns : cols_ok X ns → (∀ a, a ∈ X → a ∈ Y) → cols_ok Y ns.
Proof. intros C HXY b nd Hb Hn. apply (C b nd Hb). intros Hx. apply Hn. by apply HXY. Qed.

(* [comment removed for export] *)
Definition lagree_but (D : list Z) (ns ns' : NS) : Prop :=
  ∀ b, b ∉ D → links <$> (ns' !! b) = links <$> (ns !! b).

Lemma lagree_but_lagree D X ns ns' : lagree_but D ns ns' → (∀ x, x ∈ X → x ∉ D) → lagree X ns ns'.
Proof. intros L HX b Hb. apply L. by apply HX. Qed.
Lemma lagree_but_refl D ns : lagree_but D ns ns.  Proof. done. Qed.
Lemma lagree_but_insert D ns ns0 a nd :
  lagree_but D ns0 ns → a ∈ D → lagree_but D ns0 (<[a := nd]> ns).
Proof. intros L Ha b Hb. rewrite lookup_insert_ne; [by apply L|set_solver]. Qed.
Lemma lagree_but_insert_col D ns ns0 a nd v :
  lagree_but D ns0 ns → ns !! a = Some nd → lagree_but D ns0 (<[a := set_col v nd]> ns).
Proof.
  intros L Ha b Hb. destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert_eq. rewrite <-(L b Hb), Ha. by destruct nd.
  - rewrite lookup_insert_ne by done. by apply L.
Qed.
Lemma lagree_but_weaken D D' ns ns' : lagree_but D ns ns' → (∀ x, x ∈ D → x ∈ D') → lagree_but D' ns ns'.
Proof. intros L H b Hb. apply L. intros Hd. apply Hb. by apply H. Qed.

(* [comment removed for export] *)
Lemma ctx_at_frame' ns ns' h c f :
  lagree (cnodes c) ns ns' →
  (∀ hd, ns !! h = Some hd → ∃ hd', ns' !! h = Some hd' ∧ n_par hd' = n_par hd) →
  ctx_at ns h c f → ctx_at ns' h c f.
Proof.
  revert f; induction c as [|a s up IH|s a up IH]; intros f HL Hh; cbn.
  - intros (hd & Hhd & Hp). destruct (Hh hd Hhd) as (hd' & -> & E). exists hd'. by rewrite E.
  - intros (nd & Ha & Hp & Hlf & Hrg & Hs & Hc).
    destruct (lagree_lookup _ _ _ a nd HL) as (nd' & Ha' & E1 & E2 & E3); [set_solver|done|].
    exists nd'. rewrite E1, E2, E3. repeat split; auto.
    + eapply tree_at_frame; [|done]. eapply lagree_weaken; [done|set_solver].
    + apply IH; [| done|done]. eapply lagree_weaken; [done|set_solver].
  - intros (nd & Ha & Hp & Hlf & Hrg & Hs & Hc).
    destruct (lagree_lookup _ _ _ a nd HL) as (nd' & Ha' & E1 & E2 & E3); [set_solver|done|].
    exists nd'. rewrite E1, E2, E3. repeat split; auto.
    + eapply tree_at_frame; [|done]. eapply lagree_weaken; [done|set_solver].
    + apply IH; [| done|done]. eapply lagree_weaken; [done|set_solver].
Qed.

(* [comment removed for export] *)
Lemma troot_plug c t t' : troot t = troot t' → troot (plug c t) = troot (plug c t').
Proof.
  revert t t'; induction c as [|a s up IH|s a up IH]; intros t t' E; cbn; [done| |]; by apply IH.
Qed.
Lemma troot_plug_ne c t t' : c ≠ Top → troot (plug c t) = troot (plug c t').
Proof.
  revert t t'; induction c as [|a s up IH|s a up IH]; intros t t' Hc; cbn; [done| |];
  (destruct up; [done| |]); apply IH; done.
Qed.

(* [comment removed for export] *)
Lemma get_parent_eq ns a nd : ns !! a = Some nd → get_parent ns a = Some (n_par nd).
Proof. intros H. unfold get_parent, load. by rewrite H. Qed.
Lemma get_left_eq ns a nd : ns !! a = Some nd → get_left ns a = Some (n_lft nd).
Proof. intros H. unfold get_left, load. by rewrite H. Qed.
Lemma get_right_eq ns a nd : ns !! a = Some nd → get_right ns a = Some (n_rgt nd).
Proof. intros H. unfold get_right, load. by rewrite H. Qed.
Lemma get_color_eq ns a nd : ns !! a = Some nd → get_color ns a = Some (n_col nd).
Proof. intros H. unfold get_color, load. by rewrite H. Qed.
Lemma set_parent_eq ns a v nd : ns !! a = Some nd → set_parent ns a v = Some (<[a := set_par v nd]> ns).
Proof. intros H. unfold set_parent, store. by rewrite H. Qed.
Lemma set_left_eq ns a v nd : ns !! a = Some nd → set_left ns a v = Some (<[a := set_lft v nd]> ns).
Proof. intros H. unfold set_left, store. by rewrite H. Qed.
Lemma set_right_eq ns a v nd : ns !! a = Some nd → set_right ns a v = Some (<[a := set_rgt v nd]> ns).
Proof. intros H. unfold set_right, store. by rewrite H. Qed.
Lemma set_color_eq ns a v nd : ns !! a = Some nd → set_color ns a v = Some (<[a := set_col v nd]> ns).
Proof. intros H. unfold set_color, store. by rewrite H. Qed.

(* [comment removed for export] *)
Ltac solve_lookup tac :=
  repeat first
  [ rewrite lookup_insert_eq
  | rewrite lookup_insert_ne by tac ];
  first [ eassumption | reflexivity ].

(* [comment removed for export] *)
Ltac solve_notin :=
  first
  [ apply not_elem_of_nil
  | apply (proj2 (not_elem_of_cons _ _ _)); split; [done|solve_notin] ].

(* [comment removed for export] *)
Ltac solve_in_small := first [ apply list_elem_of_here | apply list_elem_of_further; solve_in_small ].

(* [comment removed for export] *)
Ltac ev tac :=
  first
  [ erewrite get_parent_eq by solve_lookup tac
  | erewrite get_left_eq by solve_lookup tac
  | erewrite get_right_eq by solve_lookup tac
  | erewrite get_color_eq by solve_lookup tac
  | erewrite set_parent_eq by solve_lookup tac
  | erewrite set_left_eq by solve_lookup tac
  | erewrite set_right_eq by solve_lookup tac
  | erewrite set_color_eq by solve_lookup tac ];
  cbn [mbind option_bind n_par n_lft n_rgt n_col set_par set_lft set_rgt set_col].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rb_repT_ext h T ns n ndn :
  rb_repT h T ns → n ≠ h → n ∉ inorder T → rb_repT h T (<[n := ndn]> ns).
Proof.
  intros (Hhd & Ht & N) Hnh Hn. repeat split.
  - destruct Hhd as (hd & Hh & E). exists hd. by rewrite lookup_insert_ne.
  - eapply tree_at_frame; [|done]. apply lagree_insert_notin. done.
  - done.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section insert_commit.
  Context (h : Z).

  (* [comment removed for export] *)
  Lemma insert_commit_header ns n ndn :
    rb_repT h Leaf ns → ns !! n = Some ndn → n ≠ 0 → n ≠ h →
    ∃ ns', insert_commit ns h n true h = Some ns'
      ∧ rb_repT h (Node Leaf n Leaf) ns'
      ∧ samedom ns ns'
      ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros HR Hn Hn0 Hnh. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & Hl & Hr). cbn in Hp, Hl, Hr.
    assert (Hh0 : h ≠ 0) by nd_neq_with N.
    unfold insert_commit. rewrite (Zeqb_ne h 0) by done. rewrite Z.eqb_refl.
    ev done. ev done. ev done. rewrite !insert_insert_eq.
    ev done. ev done. ev done. rewrite !insert_insert_eq.
    eexists. split; [reflexivity|]. split; [|split].
    - repeat split; cbn [tree_at troot inorder tmin tmax lhead llast List.last app n_par n_lft n_rgt set_par set_lft set_rgt].
      + eexists. rewrite lookup_insert_ne by done. rewrite lookup_insert_eq. split; [reflexivity|]. done.
      + eexists. rewrite lookup_insert_eq. split; [reflexivity|]. done.
      + apply NoDup_cons. split; [set_solver|]. apply NoDup_cons. split; [set_solver|].
        apply NoDup_cons. split; [set_solver|]. constructor.
    - eapply samedom_insert'; [by rewrite lookup_insert_ne, Hn|]. apply samedom_insert. by rewrite Hh.
    - intros X C. apply cols_ok_insert with (nd := ndn); [|by rewrite lookup_insert_ne|by left].
      apply cols_ok_insert with (nd := hd); [done|done|by left].
  Qed.

  (* [comment removed for export] *)
  Lemma insert_commit_left c a r ns n ndn :
    let T := plug c (Node Leaf a r) in
    let T' := plug c (Node (Node Leaf n Leaf) a r) in
    rb_repT h T ns → ns !! n = Some ndn → n ≠ 0 → n ≠ h → n ∉ inorder T →
    ∃ ns', insert_commit ns h n true a = Some ns'
      ∧ rb_repT h T' ns'
      ∧ samedom ns ns'
      ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' HR Hn Hn0 Hnh Hnin. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. apply top_at_plug in HT as [HC Ha]. cbn in Ha.
    destruct Ha as (nda & Hnda & Hpa & Hla & Hra & _ & Htr).
    pose proof N as N2. subst T. norm_list_in N2.
    assert (Ha0 : a ≠ 0) by nd_neq_with N2. assert (Hah : a ≠ h) by nd_neq_with N2.
    rewrite inorder_plug in Hnin. cbn in Hnin.
    assert (Hna : n ≠ a) by (intros ->; apply Hnin; set_solver).
    assert (Hh0 : h ≠ 0) by nd_neq_with N2.
    unfold insert_commit. rewrite (Zeqb_ne a 0), (Zeqb_ne a h) by done. cbn match.
    ev done. ev done. rewrite Hl.
    rewrite tmin_plug. cbn [inorder app lhead].
    (* [comment removed for export] *)
    assert (Hctx : ∀ x, x ∈ cnodes c → x ≠ a ∧ x ≠ h ∧ x ≠ n).
    { intros x Hx. rewrite cnodes_perm, elem_of_app in Hx. destruct Hx as [Hx|Hx].
      - repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver].
      - repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver]. }
    assert (Hr3 : ∀ x, x ∈ inorder r → x ≠ a ∧ x ≠ h ∧ x ≠ n).
    { intros x Hx. repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver]. }
    (* [comment removed for export] *)
    match goal with |- context [if ?cnd then _ else _] =>
      assert (HM : ∃ ns2, (if cnd then set_left (<[a:=set_lft n nda]> ns) h n
                           else Some (<[a:=set_lft n nda]> ns)) = Some ns2
              ∧ (ns2 = <[a:=set_lft n nda]> ns ∨ ns2 = <[h := set_lft n hd]> (<[a:=set_lft n nda]> ns))
              ∧ (∃ hd2, ns2 !! h = Some hd2 ∧ n_par hd2 = n_par hd ∧ n_rgt hd2 = n_rgt hd
                        ∧ n_lft hd2 = lhead n (lfr c))) end.
    { destruct (lfr c) as [|f F] eqn:EL; cbn [lhead].
      - rewrite Z.eqb_refl. ev done. eexists. split; [reflexivity|]. split; [by right|].
        eexists. rewrite lookup_insert_eq. split; [reflexivity|]. done.
      - rewrite (Zeqb_ne a f) by nd_neq_with N2. eexists. split; [reflexivity|]. split; [by left|].
        exists hd. rewrite lookup_insert_ne by done. split; [done|]. repeat split. rewrite Hl, tmin_plug, EL. done. }
    destruct HM as (ns2 & -> & Hns2 & (hd2 & Hh2 & Hp2 & Hr2 & Hl2)). cbn [mbind option_bind].
    assert (Hn2 : ns2 !! n = Some ndn).
    { destruct Hns2 as [-> | ->]; by solve_lookup done. }
    assert (Ha2 : ns2 !! a = Some (set_lft n nda)).
    { destruct Hns2 as [-> | ->]; by solve_lookup done. }
    assert (L2 : lagree_but [a; h] ns ns2).
    { destruct Hns2 as [-> | ->]; repeat (apply lagree_but_insert; [|solve_in_small]); apply lagree_but_refl. }
    assert (D2 : samedom ns ns2).
    { destruct Hns2 as [-> | ->]; repeat (eapply samedom_insert'; [by solve_lookup done|]); apply samedom_refl. }
    assert (C2 : ∀ X, cols_ok X ns → cols_ok X ns2).
    { intros X C. destruct Hns2 as [-> | ->];
        repeat (eapply cols_ok_insert; [|by solve_lookup done|by left]); exact C. }
    clear Hns2.
    ev done. ev done. ev done. rewrite !insert_insert_eq. cbn [set_lft set_rgt set_par n_par n_lft n_rgt n_col].
    eexists. split; [reflexivity|].
    set (ns' := <[n:=_]> ns2).
    assert (L' : lagree_but [a; h; n] ns ns').
    { apply lagree_but_insert; [|solve_in_small]. eapply lagree_but_weaken; [exact L2|]. intros x Hx.
      clear -Hx. set_solver. }
    split; [|split].
    - (* [comment removed for export] *)
      repeat split.
      + exists hd2. subst ns'. rewrite lookup_insert_ne by done. split; [done|].
        rewrite Hp2, Hr2, Hl2, Hp, Hr. repeat split.
        * unfold T'. by apply troot_plug.
        * unfold T'. rewrite tmin_plug. by cbn.
        * unfold T'. rewrite !tmax_plug. by cbn.
      + unfold T'. apply (proj2 (top_at_plug ns' h c (Node (Node Leaf n Leaf) a r))). split.
        * cbn [troot]. eapply ctx_at_frame'; [| |exact HC].
          -- eapply lagree_but_lagree; [exact L'|]. intros x Hx. destruct (Hctx x Hx) as (?&?&?). solve_notin.
          -- intros hd0 Hhd0. rewrite Hh in Hhd0. injection Hhd0 as <-. exists hd2.
             subst ns'. rewrite lookup_insert_ne by done. by rewrite Hp2.
        * cbn [tree_at troot]. exists (set_lft n nda). subst ns'. rewrite lookup_insert_ne by done.
          split; [done|]. cbn [n_par n_lft n_rgt set_lft]. rewrite Hpa, Hra. repeat split.
          -- eexists. rewrite lookup_insert_eq. split; [reflexivity|]. cbn [n_par n_lft n_rgt set_lft set_rgt set_par]. repeat split; done.
          -- eapply tree_at_frame; [|exact Htr]. eapply lagree_but_lagree; [exact L'|].
             intros x Hx. destruct (Hr3 x Hx) as (?&?&?). solve_notin.
      + unfold T'. rewrite inorder_plug. cbn [inorder].
        apply (NoDup_insert_mid' _ _ (0 :: h :: lfr c) (a :: inorder r ++ rfr c) n N2);
          [list_eq| clear -Hnin Hn0 Hnh; set_solver | list_eq].
    - subst ns'. eapply samedom_insert'; [exact Hn2|done].
    - intros X C. subst ns'. eapply cols_ok_insert; [by apply C2|exact Hn2|by left].
  Qed.

  (* [comment removed for export] *)
  Lemma insert_commit_right c l a ns n ndn :
    let T := plug c (Node l a Leaf) in
    let T' := plug c (Node l a (Node Leaf n Leaf)) in
    rb_repT h T ns → ns !! n = Some ndn → n ≠ 0 → n ≠ h → n ∉ inorder T →
    ∃ ns', insert_commit ns h n false a = Some ns'
      ∧ rb_repT h T' ns'
      ∧ samedom ns ns'
      ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' HR Hn Hn0 Hnh Hnin. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. apply top_at_plug in HT as [HC Ha]. cbn in Ha.
    destruct Ha as (nda & Hnda & Hpa & Hla & Hra & Htl & _).
    pose proof N as N2. subst T. norm_list_in N2.
    assert (Ha0 : a ≠ 0) by nd_neq_with N2. assert (Hah : a ≠ h) by nd_neq_with N2.
    rewrite inorder_plug in Hnin. cbn in Hnin. rewrite <-app_assoc in Hnin. cbn in Hnin.
    assert (Hna : n ≠ a) by (intros ->; apply Hnin; set_solver).
    assert (Hh0 : h ≠ 0) by nd_neq_with N2.
    unfold insert_commit. rewrite (Zeqb_ne a 0), (Zeqb_ne a h) by done. cbn match.
    ev done. ev done. rewrite Hr.
    rewrite tmax_plug. cbn [inorder]. rewrite llast_app_cons, llast_nil.
    assert (Hctx : ∀ x, x ∈ cnodes c → x ≠ a ∧ x ≠ h ∧ x ≠ n).
    { intros x Hx. rewrite cnodes_perm, elem_of_app in Hx. destruct Hx as [Hx|Hx].
      - repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver].
      - repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver]. }
    assert (Hl3 : ∀ x, x ∈ inorder l → x ≠ a ∧ x ≠ h ∧ x ≠ n).
    { intros x Hx. repeat split; [nd_neq_with N2|nd_neq_with N2|intros ->; apply Hnin; set_solver]. }
    (* [comment removed for export] *)
    match goal with |- context [if ?cnd then _ else _] =>
      assert (HM : ∃ ns2, (if cnd then set_right (<[a:=set_rgt n nda]> ns) h n
                           else Some (<[a:=set_rgt n nda]> ns)) = Some ns2
              ∧ (ns2 = <[a:=set_rgt n nda]> ns ∨ ns2 = <[h := set_rgt n hd]> (<[a:=set_rgt n nda]> ns))
              ∧ (∃ hd2, ns2 !! h = Some hd2 ∧ n_par hd2 = n_par hd ∧ n_lft hd2 = n_lft hd
                        ∧ n_rgt hd2 = llast n (rfr c))) end.
    { destruct (rfr c) as [|f F] eqn:EL.
      - rewrite llast_nil. rewrite Z.eqb_refl. ev done. eexists. split; [reflexivity|]. split; [by right|].
        eexists. rewrite lookup_insert_eq. split; [reflexivity|]. done.
      - rewrite (Zeqb_ne a (llast a (f :: F))).
        2:{ assert (Hin : llast a (f :: F) ∈ f :: F) by (apply llast_in; done). nd_neq_with N2. }
        eexists. split; [reflexivity|]. split; [by left|].
        exists hd. rewrite lookup_insert_ne by done. split; [done|]. repeat split.
        rewrite Hr, tmax_plug, EL. cbn [inorder]. apply llast_cons_indep || (rewrite !llast_cons; reflexivity). }
    destruct HM as (ns2 & -> & Hns2 & (hd2 & Hh2 & Hp2 & Hl2 & Hr2)). cbn [mbind option_bind].
    assert (Hn2 : ns2 !! n = Some ndn).
    { destruct Hns2 as [-> | ->]; by solve_lookup done. }
    assert (Ha2 : ns2 !! a = Some (set_rgt n nda)).
    { destruct Hns2 as [-> | ->]; by solve_lookup done. }
    assert (L2 : lagree_but [a; h] ns ns2).
    { destruct Hns2 as [-> | ->]; repeat (apply lagree_but_insert; [|solve_in_small]); apply lagree_but_refl. }
    assert (D2 : samedom ns ns2).
    { destruct Hns2 as [-> | ->]; repeat (eapply samedom_insert'; [by solve_lookup done|]); apply samedom_refl. }
    assert (C2 : ∀ X, cols_ok X ns → cols_ok X ns2).
    { intros X C. destruct Hns2 as [-> | ->];
        repeat (eapply cols_ok_insert; [|by solve_lookup done|by left]); exact C. }
    clear Hns2.
    ev done. ev done. ev done. rewrite !insert_insert_eq. cbn [set_lft set_rgt set_par n_par n_lft n_rgt n_col].
    eexists. split; [reflexivity|].
    set (ns' := <[n:=_]> ns2).
    assert (L' : lagree_but [a; h; n] ns ns').
    { apply lagree_but_insert; [|solve_in_small]. eapply lagree_but_weaken; [exact L2|]. intros x Hx.
      clear -Hx. set_solver. }
    split; [|split].
    - (* [comment removed for export] *)
      repeat split.
      + exists hd2. subst ns'. rewrite lookup_insert_ne by done. split; [done|].
        rewrite Hp2, Hr2, Hl2, Hp, Hl. repeat split.
        * unfold T'. by apply troot_plug.
        * unfold T'. rewrite !tmin_plug. cbn [inorder]. rewrite !lhead_app. by cbn.
        * unfold T'. rewrite tmax_plug. cbn [inorder]. rewrite llast_app. by cbn.
      + unfold T'. apply (proj2 (top_at_plug ns' h c (Node l a (Node Leaf n Leaf)))). split.
        * cbn [troot]. eapply ctx_at_frame'; [| |exact HC].
          -- eapply lagree_but_lagree; [exact L'|]. intros x Hx. destruct (Hctx x Hx) as (?&?&?). solve_notin.
          -- intros hd0 Hhd0. rewrite Hh in Hhd0. injection Hhd0 as <-. exists hd2.
             subst ns'. rewrite lookup_insert_ne by done. by rewrite Hp2.
        * cbn [tree_at troot]. exists (set_rgt n nda). subst ns'. rewrite lookup_insert_ne by done.
          split; [done|]. cbn [n_par n_lft n_rgt set_rgt]. rewrite Hpa, Hla. repeat split.
          -- eapply tree_at_frame; [|exact Htl]. eapply lagree_but_lagree; [exact L'|].
             intros x Hx. destruct (Hl3 x Hx) as (?&?&?). solve_notin.
          -- eexists. rewrite lookup_insert_eq. split; [reflexivity|]. cbn [n_par n_lft n_rgt set_lft set_rgt set_par]. repeat split; done.
      + unfold T'. rewrite inorder_plug. cbn [inorder].
        apply (NoDup_insert_mid' _ _ (0 :: h :: lfr c ++ inorder l ++ [a]) (rfr c) n N2);
          [list_eq| clear -Hnin Hn0 Hnh; set_solver | list_eq].
    - subst ns'. eapply samedom_insert'; [exact Hn2|done].
    - intros X C. subst ns'. eapply cols_ok_insert; [by apply C2|exact Hn2|by left].
  Qed.
End insert_commit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma split_unique (A1 B1 A2 B2 : list Z) x :
  NoDup (A1 ++ x :: B1) → A1 ++ x :: B1 = A2 ++ x :: B2 → A1 = A2 ∧ B1 = B2.
Proof.
  revert A2. induction A1 as [|y A1 IH]; intros [|z A2] N E; cbn in *.
  - by injection E.
  - injection E as -> ->. exfalso. apply NoDup_cons in N as [N _]. apply N. set_solver.
  - injection E as -> E'. exfalso. apply NoDup_cons in N as [N _]. apply N. set_solver.
  - injection E as -> E'. apply NoDup_cons in N as [_ N]. destruct (IH A2 N E') as [-> ->]. done.
Qed.

Lemma lhead_indep_ne (d : Z) l : l ≠ [] → ∀ d', lhead d l = lhead d' l.
Proof. by destruct l. Qed.

Theorem insert_before_check_spec h T ns fuel A B :
  rb_repT h T ns → inorder T = A ++ B → (theight T <= fuel)%nat →
  ∃ ll nd, insert_before_check fuel ns h (lhead h B) = Some (ll, nd) ∧
    ( (T = Leaf ∧ ll = true ∧ nd = h)
    ∨ (ll = true ∧ ∃ c r, T = plug c (Node Leaf nd r) ∧ lfr c = A ∧ nd :: inorder r ++ rfr c = B)
    ∨ (ll = false ∧ ∃ c l, T = plug c (Node l nd Leaf) ∧ lfr c ++ inorder l ++ [nd] = A ∧ rfr c = B) ).
Proof.
  intros HR HS Hf. pose proof (rep_N _ _ _ HR) as N.
  destruct (rep_hd _ _ _ HR) as (hd & Hh & Hp & Hl & Hr).
  unfold insert_before_check.
  rewrite (get_left_eq ns h hd Hh), (get_parent_eq ns h hd Hh). cbn [mbind option_bind]. rewrite Hl, Hp.
  destruct (troot_cases T) as [[-> E0]|[HT Hrt]].
  - (* [comment removed for export] *)
    cbn in HS. destruct A; [|done]. destruct B; [|done]. cbn [lhead tmin inorder].
    rewrite (Z.eqb_refl h). cbn [mbind option_bind]. cbn [troot Z.eqb].
    eexists _, _. split; [reflexivity|]. left. done.
  - assert (Hrt0 : troot T ≠ 0) by nd_neq_with N.
    pose proof (tmin_in h T HT) as Hmin.
    destruct B as [|pos B'].
    + (* [comment removed for export] *)
      cbn [lhead]. rewrite (Zeqb_ne h (tmin h T)) by nd_neq_with N.
      rewrite (prev_node_header h T ns fuel HR). cbn [mbind option_bind].
      rewrite (Zeqb_ne _ _ Hrt0). rewrite (get_left_eq ns h hd Hh). cbn [mbind option_bind]. rewrite Hl.
      rewrite (Zeqb_ne (tmin h T) 0) by nd_neq_with N.
      eexists _, _. split; [reflexivity|]. right; right. split; [done|].
      destruct (decomp_max T HT) as (c & lm & ET & HRc).
      exists c, lm. rewrite (tmax_indep 0 h T HT) in ET. split; [done|].
      rewrite app_nil_r in HS. rewrite <-HS. rewrite (rfr_allR c HRc). split; [|done].
      rewrite ET at 2. rewrite inorder_plug. cbn [inorder]. rewrite (rfr_allR c HRc). by rewrite <-!app_assoc.
    + cbn [lhead].
      assert (Hpos : pos ∈ inorder T) by (rewrite HS; set_solver).
      destruct (decomp_node T pos Hpos) as (c & l & r & ET).
      pose proof HS as HS2. rewrite ET, inorder_plug in HS2. cbn [inorder] in HS2.
      assert (EAB : lfr c ++ inorder l = A ∧ inorder r ++ rfr c = B').
      { apply (split_unique _ _ _ _ pos); [|by rewrite <-!app_assoc in HS2 |- *].
        rewrite <-app_assoc. cbn. rewrite app_assoc.
        pose proof N as N2. rewrite ET in N2. norm_list_in N2. apply nd_cons_tl, nd_cons_tl in N2.
        by rewrite <-!app_assoc. }
      destruct EAB as [EA EB].
      pose proof (rep_top _ _ _ HR) as HT2. rewrite ET in HT2. apply top_at_plug in HT2 as [HC Ht].
      cbn in Ht. destruct Ht as (ndp & Hndp & Hpp & Hlp & Hrp & Htl & Htr).
      pose proof N as N2. rewrite ET in N2. norm_list_in N2.
      destruct A as [|a0 A'].
      * (* [comment removed for export] *)
        assert (El : l = Leaf).
        { destruct (lfr c); [|done]. cbn in EA. by apply inorder_nil. }
        subst l. cbn in EA.
        assert (Emin : tmin h T = pos).
        { unfold tmin. rewrite HS. done. }
        rewrite Emin, (Z.eqb_refl pos). cbn [mbind option_bind].
        rewrite (Zeqb_ne _ _ Hrt0).
        rewrite (get_left_eq ns pos ndp Hndp). cbn [mbind option_bind]. rewrite Hlp. cbn [troot Z.eqb].
        eexists _, _. split; [reflexivity|]. right; left. split; [done|].
        exists c, r. rewrite app_nil_r in EA. rewrite EB. done.
      * (* [comment removed for export] *)
        assert (Emin : tmin h T = a0).
        { unfold tmin. rewrite HS. done. }
        rewrite Emin. rewrite (Zeqb_ne pos a0).
        2:{ pose proof N as N3. rewrite HS in N3. nd_neq_with N3. }
        destruct (list_snoc_or_nil (a0 :: A')) as [E|(A'' & b & EA2)]; [done|].
        rewrite (prev_node_node h T ns fuel A'' b pos B' HR); [|by rewrite HS, EA2, <-app_assoc|done].
        cbn [mbind option_bind].
        rewrite (Zeqb_ne _ _ Hrt0).
        rewrite (get_left_eq ns pos ndp Hndp). cbn [mbind option_bind]. rewrite Hlp.
        destruct (troot_cases l) as [[-> El0]|[Hl0 Hlrt]].
        -- cbn [troot Z.eqb]. eexists _, _. split; [reflexivity|]. right; left. split; [done|].
           exists c, r. cbn in EA. rewrite app_nil_r in EA. rewrite EB. done.
        -- rewrite (Zeqb_ne (troot l) 0) by nd_neq_with N2.
           eexists _, _. split; [reflexivity|]. right; right. split; [done|].
           destruct (decomp_max l Hl0) as (cl & ll & El & HRl).
           exists (ccomp cl (GoL pos r c)), ll.
           assert (Eb : b = tmax 0 l).
           { (* [comment removed for export] *)
             assert (E1 : llast h (a0 :: A') = b) by (rewrite EA2; apply llast_app_cons).
             rewrite <-E1, <-EA. unfold tmax. rewrite llast_app.
             destruct (inorder l) as [|i0 il] eqn:Eil; [by apply inorder_nil in Eil|]. apply llast_cons_indep. }
           rewrite Eb. split; [|split].
           ++ rewrite plug_ccomp. cbn [plug]. by rewrite <-El.
           ++ rewrite lfr_ccomp. cbn [lfr]. rewrite <-EA. rewrite El at 2.
              rewrite inorder_plug. cbn [inorder]. rewrite (rfr_allR cl HRl). by rewrite <-!app_assoc.
           ++ rewrite rfr_ccomp. cbn [rfr]. rewrite (rfr_allR cl HRl). rewrite EB. done.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem bst_insert_before_spec h T ns fuel A B n ndn :
  rb_repT h T ns → inorder T = A ++ B → ns !! n = Some ndn → n ≠ 0 → n ≠ h → n ∉ inorder T →
  (theight T <= fuel)%nat →
  ∃ c' ns', bst_insert_before fuel ns h (lhead h B) n = Some ns'
    ∧ inorder (plug c' (Node Leaf n Leaf)) = A ++ n :: B
    ∧ rb_repT h (plug c' (Node Leaf n Leaf)) ns'
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros HR HS Hn Hn0 Hnh Hnin Hf. unfold bst_insert_before.
  destruct (insert_before_check_spec h T ns fuel A B HR HS Hf) as (ll & nd & -> & Hcases).
  cbn [mbind option_bind].
  destruct Hcases as [(-> & -> & ->) | [(-> & c & r & ET & EA & EB) | (-> & c & l & ET & EA & EB)]].
  - destruct (insert_commit_header h ns n ndn HR Hn Hn0 Hnh) as (ns' & -> & HR' & D' & C').
    exists Top, ns'. cbn in HS |- *. split; [done|]. split; [|split; [exact HR'|split; [exact D'|exact C']]].
    destruct A; [|done]. destruct B; [done|done].
  - subst T. destruct (insert_commit_left h c nd r ns n ndn HR Hn Hn0 Hnh Hnin) as (ns' & -> & HR' & D' & C').
    exists (GoL nd r c), ns'. cbn [plug]. split; [done|]. split; [|split; [exact HR'|split; [exact D'|exact C']]].
    rewrite inorder_plug. cbn [inorder]. rewrite EA, <-EB. done.
  - subst T. destruct (insert_commit_right h c l nd ns n ndn HR Hn Hn0 Hnh Hnin) as (ns' & -> & HR' & D' & C').
    exists (GoR l nd c), ns'. cbn [plug]. split; [done|]. split; [|split; [exact HR'|split; [exact D'|exact C']]].
    rewrite inorder_plug. cbn [inorder]. rewrite <-EA, <-EB. by rewrite <-!app_assoc.
Qed.
