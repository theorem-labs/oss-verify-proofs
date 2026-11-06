(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe RBOrder RBInsert RBBalance DList.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lhead_prefix_nil (h : Z) S A B :
  S = A ++ B → NoDup (h :: S) → lhead h B = lhead h S → A = [].
Proof.
  intros -> N E. destruct A as [|a A]; [done|]. exfalso. cbn in E.
  destruct B as [|b B]; cbn in E.
  - subst a. apply NoDup_cons in N as [N _]. apply N. set_solver.
  - subst b. apply nd_cons_tl in N. cbn in N. apply NoDup_cons in N as [N _]. apply N. set_solver.
Qed.

Section insert_element.
  Context {K : Type} (lt : K → K → bool) (SWO : StrictWeakOrder lt) (key : Z → K).

  Local Notation "'ubA'" := (ub_prefix lt key) (at level 0).
  Local Notation "'ubB'" := (ub_suffix lt key) (at level 0).

  Theorem insert_element_ok (bf : Z) (S L : list Z) (ns : NS) (ls : LS) (e : Z)
          (nd0 : node) (ln0 : lnode) (k : K) (ieqE : Z → bool) (fuel : nat) :
    let h := bf in let hL := bf + 32 in let n := e + ELEM_TO_NODE in
    rb_ok h S ns → sorted lt key S → dl_ok hL L ls →
    (∀ x, x ∈ S → x - ELEM_TO_NODE ∈ L) →
    n ≠ 0 → n ≠ h → n ∉ S → e ≠ 0 → e ∉ hL :: L →
    key n = k →
    (∀ el, el + ELEM_TO_NODE ∈ S → ieqE el = eqv lt k (key (el + ELEM_TO_NODE))) →
    (length S < fuel)%nat →
    ∃ ns' ls' pth,
      insert_element fuel (cmpL lt key k) (cmpU lt key k) ieqE
                     (<[n := nd0]> ns) (<[e := ln0]> ls) bf e = Some (ns', ls', pth)
      ∧ rb_ok h (ubA k S ++ n :: ubB k S) ns'
      ∧ sorted lt key (ubA k S ++ n :: ubB k S)
      ∧ (∀ a, is_Some (ns' !! a) ↔ a = n ∨ is_Some (ns !! a))
      ∧ (∃ L', dl_ok hL L' ls' ∧ (∀ x, x ∈ ubA k S ++ n :: ubB k S → x - ELEM_TO_NODE ∈ L')
         ∧ match pth with
           | IE_begin   => ubA k S = [] ∧ ¬ has_eqv lt key k S ∧ L' = L ++ [e]
           | IE_newname => ubA k S ≠ [] ∧ ¬ has_eqv lt key k S ∧ L' = L ++ [e]
           | IE_dup     => ∃ A' lastn LA LB, ubA k S = A' ++ [lastn] ∧ eqv lt k (key lastn) = true
                            ∧ L = LA ++ (lastn - ELEM_TO_NODE) :: LB
                            ∧ L' = LA ++ (lastn - ELEM_TO_NODE) :: e :: LB
           end).
  Proof.
    intros h hL n HOK HS HDL HSL Hn0 Hnh HnS He0 HeL Hk Hieq Hf.
    pose proof HOK as (T & HTS & HR & HD & HC).
    assert (HR1 : rb_repT h T (<[n:=nd0]> ns)) by (apply rb_repT_ext; [done|done|by rewrite HTS]).
    assert (HRep1 : rb_rep h S (<[n:=nd0]> ns)) by (by exists T).
    pose proof (rep_N _ _ _ HR) as N. rewrite HTS in N.
    pose proof (ub_split lt key k S) as ES.
    assert (HSL' : ∀ x, x ∈ ubA k S ++ n :: ubB k S → x - ELEM_TO_NODE ∈ L ++ [e]).
    { intros x Hx. rewrite elem_of_app, elem_of_cons in Hx. rewrite elem_of_app, list_elem_of_singleton.
      destruct Hx as [Hx|[->|Hx]].
      - left. apply HSL. rewrite ES. set_solver.
      - right. subst n. unfold ELEM_TO_NODE. lia.
      - left. apply HSL. rewrite ES. set_solver. }
    pose proof (sorted_insert_ub lt SWO key k S n HS Hk) as HS'.
    unfold insert_element. cbn zeta. fold hL. fold n. fold h.
    rewrite (upper_bound_sorted lt SWO key k h S _ fuel HRep1 HS) by lia. cbn [mbind option_bind].
    destruct (rep_hd _ _ _ HR1) as (hd & Hh & _ & Hl & _).
    rewrite (get_left_eq _ _ _ Hh). cbn [mbind option_bind]. rewrite Hl. unfold tmin. rewrite HTS.
    (* [comment removed for export] *)
    assert (HASSERT : ¬ has_eqv lt key k S →
              assert_not_contains fuel (cmpL lt key k) (cmpU lt key k) (<[n:=nd0]> ns) (<[e:=ln0]> ls) h = Some tt).
    { intros Hne. unfold assert_not_contains, fields_find. cbn zeta.
      destruct (find_sorted lt SWO key k h S _ fuel HRep1 HS) as (r & -> & Hr); [lia|]. cbn [mbind option_bind].
      destruct Hr as [[-> _]|(B0 & _ & Hin & _ & Heqv & _)].
      { rewrite Z.eqb_refl. cbn [mbind option_bind]. by rewrite Z.eqb_refl. }
      exfalso. apply Hne. by exists r. }
    (* [comment removed for export] *)
    assert (HINS : ∃ ns', rb_insert_before fuel (<[n:=nd0]> ns) h (lhead h (ubB k S)) n = Some ns'
              ∧ rb_ok h (ubA k S ++ n :: ubB k S) ns' ∧ (∀ a, is_Some (ns' !! a) ↔ a = n ∨ is_Some (ns !! a))).
    { apply (rb_insert_before_ok h S ns fuel); auto. }
    destruct HINS as (ns' & Eins & HOK' & HD').
    destruct (Z.eqb_spec (lhead h (ubB k S)) (lhead h S)) as [Ebeg|Hnbeg].
    - (* [comment removed for export] *)
      assert (EA : ubA k S = []) by (eapply (lhead_prefix_nil h S); eauto; exact (nd_cons_tl _ _ N)).
      pose proof (ub_begin_no_eqv lt SWO key k S HS EA) as Hne.
      rewrite (HASSERT Hne). cbn [mbind option_bind]. rewrite Eins. cbn [mbind option_bind].
      destruct (push_back_ok hL L ls e ln0 HDL He0 HeL) as (ls' & -> & HDL').
      eexists _, _, _. split; [reflexivity|]. split_and!; auto.
      exists (L ++ [e]). split_and!; auto.
    - (* [comment removed for export] *)
      assert (HA : ubA k S ≠ []).
      { intros EA. apply Hnbeg. pose proof ES as ES2. rewrite EA in ES2. cbn in ES2. by rewrite <-ES2. }
      rewrite (prev_node_spec h S _ fuel (ubA k S) (ubB k S) HRep1 ES HA) by lia. cbn [mbind option_bind].
      destruct (list_snoc_or_nil (ubA k S)) as [?|(A' & lastn & EA)]; [done|].
      replace (llast h (ubA k S)) with lastn by (rewrite EA, llast_app_cons; done).
      assert (Hlast : lastn ∈ S) by (rewrite ES, EA; set_solver).
      rewrite (Zeqb_ne lastn 0) by nd_neq_with N.
      rewrite (Hieq (lastn - ELEM_TO_NODE)) by (by replace (lastn - ELEM_TO_NODE + ELEM_TO_NODE) with lastn by lia).
      replace (lastn - ELEM_TO_NODE + ELEM_TO_NODE) with lastn by lia.
      destruct (eqv lt k (key lastn)) eqn:Heqv; cbn [negb].
      + (* [comment removed for export] *)
        rewrite Eins. cbn [mbind option_bind].
        destruct (list_elem_of_split L (lastn - ELEM_TO_NODE)) as (LA & LB & EL); [by apply HSL|].
        destruct (link_after_last_ok hL L ls LA (lastn - ELEM_TO_NODE) LB e ln0 HDL EL He0 HeL) as (ls' & Elnk & HDL').
        rewrite obind_assoc in Elnk || idtac.
        eexists _, _, _. split.
        { destruct (iterator_to (<[e:=ln0]> ls) (lastn - ELEM_TO_NODE)) as [it|] eqn:Eit; cbn [mbind option_bind] in Elnk |- *; [|done].
          destruct (iter_next (<[e:=ln0]> ls) it) as [nx|] eqn:Enx; cbn [mbind option_bind] in Elnk |- *; [|done].
          rewrite Elnk. reflexivity. }
        split_and!; auto. eexists. split; [exact HDL'|]. split.
        { intros x Hx. pose proof (HSL' x Hx) as X.
          rewrite EL in X. revert X. clear. intros X. rewrite <-app_assoc in X. cbn in X. set_solver. }
        exists A', lastn, LA, LB. auto.
      + (* [comment removed for export] *)
        pose proof (ub_prev_no_eqv lt SWO key k S A' lastn HS EA Heqv) as Hne.
        rewrite (HASSERT Hne). cbn [mbind option_bind]. rewrite Eins. cbn [mbind option_bind].
        destruct (push_back_ok hL L ls e ln0 HDL He0 HeL) as (ls' & -> & HDL').
        eexists _, _, _. split; [reflexivity|]. split_and!; auto.
        exists (L ++ [e]). split_and!; auto.
  Qed.

  (* [comment removed for export] *)
  Theorem fields_find_ok (bf : Z) (S L : list Z) (ns : NS) (ls : LS) (k : K) (fuel : nat) :
    let h := bf in let hL := bf + 32 in
    rb_rep h S ns → sorted lt key S → dl_ok hL L ls →
    (∀ x, x ∈ S → x - ELEM_TO_NODE ∈ L) → (length S <= fuel)%nat →
    ∃ r, fields_find fuel (cmpL lt key k) (cmpU lt key k) ns ls bf = Some r
      ∧ ( (r = hL ∧ ¬ has_eqv lt key k S)
        ∨ (∃ y B, r = y - ELEM_TO_NODE ∧ r ∈ L ∧ lb_suffix lt key k S = y :: B ∧ y ∈ S
                 ∧ eqv lt k (key y) = true ∧ (∀ x, x ∈ lb_prefix lt key k S → lt (key x) k = true)) ).
  Proof.
    intros h hL HR HS HDL HSL Hf. unfold fields_find. cbn zeta. fold h hL.
    pose proof (rb_rep_nodup _ _ _ HR) as N.
    destruct (find_sorted lt SWO key k h S ns fuel HR HS Hf) as (r & -> & Hr). cbn [mbind option_bind].
    destruct Hr as [[-> Hne]|(B0 & EB & Hin & Hrh & Heqv & Hpre)].
    - rewrite Z.eqb_refl. exists hL. split; [done|by left].
    - rewrite (Zeqb_ne _ _ Hrh). rewrite (Zeqb_ne r 0) by nd_neq_with N.
      rewrite (iterator_to_spec hL L ls HDL) by (by apply HSL).
      eexists. split; [reflexivity|]. right. exists r, B0. split_and!; auto.
  Qed.
End insert_element.
