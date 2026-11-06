(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe RBInsert.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tree_at_root ns t p : tree_at ns t p → t ≠ Leaf →
  ∃ nd, ns !! troot t = Some nd ∧ n_par nd = p.
Proof. destruct t as [|l a r]; cbn; [done|]. intros (nd & ? & ? & _) _. eauto. Qed.

Lemma lagree_but_trans D ns1 ns2 ns3 : lagree_but D ns1 ns2 → lagree_but D ns2 ns3 → lagree_but D ns1 ns3.
Proof. intros A B b Hb. by rewrite (B b Hb), (A b Hb). Qed.

Lemma lagree_but_eq1 D ns ns' r :
  (∀ a, a ≠ r → ns' !! a = ns !! a) → r ∈ D → lagree_but D ns ns'.
Proof. intros E Hr b Hb. rewrite E; [done|]. intros ->. done. Qed.

Lemma samedom_eq1 ns ns' r nd nd' :
  (∀ a, a ≠ r → ns' !! a = ns !! a) → ns !! r = Some nd → ns' !! r = Some nd' → samedom ns ns'.
Proof.
  intros E H1 H2 b. destruct (decide (b = r)) as [->|Hne].
  - rewrite H1, H2. done.
  - by rewrite E.
Qed.

(* [comment removed for export] *)
Lemma repar_spec ns t oldp newp N0 N1 :
  tree_at ns t oldp → NoDup (0 :: N0 ++ inorder t ++ N1) →
  ∃ ns', (if troot t =? 0 then Some ns else set_parent ns (troot t) newp) = Some ns'
    ∧ tree_at ns' t newp
    ∧ (∀ a, a ≠ troot t → ns' !! a = ns !! a)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros Ht N. destruct t as [|l a r].
  - cbn. exists ns. repeat split; auto; done.
  - cbn in Ht. destruct Ht as (nd & Ha & Hp & Hl & Hr & Htl & Htr). cbn [troot].
    cbn [inorder] in N. norm_list_in N.
    rewrite (Zeqb_ne a 0) by nd_neq_with N.
    rewrite (set_parent_eq _ _ _ _ Ha). eexists. split; [reflexivity|].
    assert (E : ∀ b, b ≠ a → <[a:=set_par newp nd]> ns !! b = ns !! b).
    { intros b Hb. by rewrite lookup_insert_ne. }
    split_and?.
    + exists (set_par newp nd). rewrite lookup_insert_eq. split; [done|]. cbn. rewrite Hl, Hr.
      split_and?; [done|done|done| |].
      * eapply tree_at_frame; [|exact Htl]. intros b Hb. rewrite E; [done|]. nd_neq_with N.
      * eapply tree_at_frame; [|exact Htr]. intros b Hb. rewrite E; [done|]. nd_neq_with N.
    + exact E.
    + eapply samedom_insert'; [exact Ha|apply samedom_refl].
    + intros X C. eapply cols_ok_insert; [exact C|exact Ha|by left].
Qed.

(* [comment removed for export] *)
Lemma ctx_at_owner ns h c f :
  ctx_at ns h c f → ∃ nd, ns !! ctx_node h c = Some nd ∧
    match c with
    | Top => n_par nd = f
    | GoL _ s up => n_par nd = ctx_node h up ∧ n_lft nd = f ∧ n_rgt nd = troot s
    | GoR s _ up => n_par nd = ctx_node h up ∧ n_lft nd = troot s ∧ n_rgt nd = f
    end.
Proof. destruct c; cbn; intros (nd & ? & ?); exists nd; tauto. Qed.

(* [comment removed for export] *)
Lemma set_child_spec ns0 ns h c gp q nd3 N0 N1 :
  ctx_at ns0 h c gp →
  ns0 !! ctx_node h c = Some nd3 → ns !! ctx_node h c = Some nd3 →
  lagree (h :: cnodes c) ns0 ns →
  NoDup (0 :: h :: lfr c ++ N0 ++ gp :: N1 ++ rfr c) →
  ∃ ns', (if ctx_node h c =? h then set_parent ns h q
          else if n_lft nd3 =? gp then set_left ns (ctx_node h c) q
          else set_right ns (ctx_node h c) q) = Some ns'
    ∧ ctx_at ns' h c q
    ∧ (∀ a, a ≠ ctx_node h c → ns' !! a = ns !! a)
    ∧ (∀ hd, ns !! h = Some hd → ∃ hd', ns' !! h = Some hd' ∧ n_lft hd' = n_lft hd ∧ n_rgt hd' = n_rgt hd)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros HC H0 H3 HL N.
  destruct c as [|g3 s3 up3|s3 g3 up3]; cbn [ctx_node] in *; cbn [lfr rfr] in N; norm_list_in N.
  - rewrite Z.eqb_refl. rewrite (set_parent_eq _ _ _ _ H3). eexists. split; [reflexivity|].
    assert (E : ∀ b, b ≠ h → <[h:=set_par q nd3]> ns !! b = ns !! b) by (intros b Hb; by rewrite lookup_insert_ne).
    split_and?.
    + exists (set_par q nd3). by rewrite lookup_insert_eq.
    + exact E.
    + intros hd Hhd. rewrite H3 in Hhd. injection Hhd as <-. exists (set_par q nd3). by rewrite lookup_insert_eq.
    + eapply samedom_insert'; [exact H3|apply samedom_refl].
    + intros X C. eapply cols_ok_insert; [exact C|exact H3|by left].
  - cbn in HC. destruct HC as (nd & Hg & Hp & Hlf & Hrg & Hs & Hup). rewrite H0 in Hg. injection Hg as <-.
    rewrite (Zeqb_ne g3 h) by nd_neq_with N. rewrite Hlf, Z.eqb_refl.
    rewrite (set_left_eq _ _ _ _ H3). eexists. split; [reflexivity|].
    assert (E : ∀ b, b ≠ g3 → <[g3:=set_lft q nd3]> ns !! b = ns !! b) by (intros b Hb; by rewrite lookup_insert_ne).
    split_and?.
    + exists (set_lft q nd3). rewrite lookup_insert_eq. split; [done|]. cbn. rewrite Hp, Hrg.
      split_and?; [done|done|done| |].
      * eapply tree_at_frame; [|exact Hs]. intros b Hb. rewrite E; [apply HL; set_solver|nd_neq_with N].
      * eapply ctx_at_frame; [|exact Hup]. intros b Hb. rewrite E; [apply HL; clear -Hb; set_solver|].
        rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[Hb|Hb]]; nd_neq_with N.
    + exact E.
    + intros hd Hhd. exists hd. rewrite E; [done|nd_neq_with N].
    + eapply samedom_insert'; [exact H3|apply samedom_refl].
    + intros X C. eapply cols_ok_insert; [exact C|exact H3|by left].
  - cbn in HC. destruct HC as (nd & Hg & Hp & Hlf & Hrg & Hs & Hup). rewrite H0 in Hg. injection Hg as <-.
    rewrite (Zeqb_ne g3 h) by nd_neq_with N. rewrite Hlf.
    rewrite (Zeqb_ne (troot s3) gp).
    2:{ destruct (troot_cases s3) as [[-> E0]|[Hs0 Hin]]; [cbn; nd_neq_with N|nd_neq_with N]. }
    rewrite (set_right_eq _ _ _ _ H3). eexists. split; [reflexivity|].
    assert (E : ∀ b, b ≠ g3 → <[g3:=set_rgt q nd3]> ns !! b = ns !! b) by (intros b Hb; by rewrite lookup_insert_ne).
    split_and?.
    + exists (set_rgt q nd3). rewrite lookup_insert_eq. split; [done|]. cbn. rewrite Hp, Hlf.
      split_and?; [done|done|done| |].
      * eapply tree_at_frame; [|exact Hs]. intros b Hb. rewrite E; [apply HL; set_solver|nd_neq_with N].
      * eapply ctx_at_frame; [|exact Hup]. intros b Hb. rewrite E; [apply HL; clear -Hb; set_solver|].
        rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[Hb|Hb]]; nd_neq_with N.
    + exact E.
    + intros hd Hhd. exists hd. rewrite E; [done|nd_neq_with N].
    + eapply samedom_insert'; [exact H3|apply samedom_refl].
    + intros X C. eapply cols_ok_insert; [exact C|exact H3|by left].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rot_left_npf_spec ns sL pp tl p tr gp N0 N1 :
  tree_at ns (Node sL pp (Node tl p tr)) gp →
  NoDup (0 :: N0 ++ inorder sL ++ pp :: inorder tl ++ p :: inorder tr ++ N1) →
  ∃ ns' ndq, rb_rot_left_npf ns pp p = Some ns'
    ∧ (ns' !! p = Some ndq ∧ n_lft ndq = pp ∧ n_rgt ndq = troot tr
        ∧ tree_at ns' (Node sL pp tl) p ∧ tree_at ns' tr p)      (* [comment removed for export] *)
    ∧ (∀ a, a ≠ pp → a ≠ p → a ≠ troot tl → ns' !! a = ns !! a)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros Ht N. cbn in Ht.
  destruct Ht as (ndpp & Hpp & Hppp & Hppl & Hppr & HsL & (ndp & Hp & Hpp' & Hpl & Hpr & Htl & Htr)).
  assert (Hne : pp ≠ p) by nd_neq_with N.
  unfold rb_rot_left_npf.
  rewrite (get_left_eq _ _ _ Hp). cbn [mbind option_bind]. rewrite Hpl.
  rewrite (set_right_eq _ _ _ _ Hpp). cbn [mbind option_bind].
  destruct (repar_spec (<[pp:=set_rgt (troot tl) ndpp]> ns) tl p pp (N0 ++ inorder sL ++ [pp]) (p :: inorder tr ++ N1))
    as (ns2 & -> & Htl2 & E2 & D2 & C2).
  { eapply tree_at_frame; [|exact Htl]. apply lagree_insert_notin. nd_notin N. }
  { by repeat (rewrite <-app_assoc; cbn [app]). }
  cbn [mbind option_bind].
  assert (Htl0 : p ≠ troot tl ∧ pp ≠ troot tl).
  { destruct (troot_cases tl) as [[-> E0]|[? Hin]]; [cbn; split; nd_neq_with N|split; nd_neq_with N]. }
  destruct Htl0 as [Hptl Hpptl].
  assert (Hp2 : ns2 !! p = Some ndp) by (rewrite E2, lookup_insert_ne; done).
  assert (Hpp2 : ns2 !! pp = Some (set_rgt (troot tl) ndpp)) by (rewrite E2, lookup_insert_eq; done).
  rewrite (set_left_eq _ _ _ _ Hp2). cbn [mbind option_bind].
  erewrite set_parent_eq by (rewrite lookup_insert_ne by done; exact Hpp2).
  eexists _, _. split; [reflexivity|].
  set (ns' := <[pp:=_]> (<[p:=_]> ns2)).
  assert (E' : ∀ a, a ≠ pp → a ≠ p → a ≠ troot tl → ns' !! a = ns !! a).
  { intros a H1 H2 H3. subst ns'. rewrite lookup_insert_ne, lookup_insert_ne, E2, lookup_insert_ne; done. }
  split_and?.
  - subst ns'. rewrite lookup_insert_ne, lookup_insert_eq by done. done.
  - done.
  - exact Hpr.
  - cbn [tree_at]. eexists. split; [subst ns'; by rewrite lookup_insert_eq|]. cbn. rewrite Hppl. split_and?; [done|done|done| |].
    * eapply tree_at_frame; [|exact HsL]. intros b Hb. rewrite E'; [done|nd_neq_with N|nd_neq_with N|].
      destruct (troot_cases tl) as [[-> E0]|[? Hin]]; [cbn; nd_neq_with N|nd_neq_with N].
    * eapply tree_at_frame; [|exact Htl2]. intros b Hb. subst ns'.
      rewrite lookup_insert_ne, lookup_insert_ne; [done|nd_neq_with N|nd_neq_with N].
  - eapply tree_at_frame; [|exact Htr]. intros b Hb. rewrite E'; [done|nd_neq_with N|nd_neq_with N|].
    destruct (troot_cases tl) as [[-> E0]|[? Hin]]; [cbn; nd_neq_with N|nd_neq_with N].
  - exact E'.
  - eapply samedom_trans; [eapply samedom_insert'; [exact Hpp|apply samedom_refl]|].
    eapply samedom_trans; [exact D2|]. subst ns'.
    eapply samedom_insert'; [rewrite lookup_insert_ne by done; exact Hpp2|].
    eapply samedom_insert'; [exact Hp2|apply samedom_refl].
  - intros X C. subst ns'.
    eapply cols_ok_insert; [|rewrite lookup_insert_ne by done; exact Hpp2|by left].
    eapply cols_ok_insert; [|exact Hp2|by left].
    apply C2. eapply cols_ok_insert; [exact C|exact Hpp|by left].
Qed.

(* [comment removed for export] *)
Lemma rot_right_npf_spec ns tl p tr pp sR gp N0 N1 :
  tree_at ns (Node (Node tl p tr) pp sR) gp →
  NoDup (0 :: N0 ++ inorder tl ++ p :: inorder tr ++ pp :: inorder sR ++ N1) →
  ∃ ns' ndq, rb_rot_right_npf ns pp p = Some (ns', troot tl)
    ∧ (ns' !! p = Some ndq ∧ n_lft ndq = troot tl ∧ n_rgt ndq = pp
        ∧ tree_at ns' tl p ∧ tree_at ns' (Node tr pp sR) p)      (* [comment removed for export] *)
    ∧ (∀ a, a ≠ pp → a ≠ p → a ≠ troot tr → ns' !! a = ns !! a)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros Ht N. cbn in Ht.
  destruct Ht as (ndpp & Hpp & Hppp & Hppl & Hppr & (ndp & Hp & Hpp' & Hpl & Hpr & Htl & Htr) & HsR).
  assert (Hne : pp ≠ p) by nd_neq_with N.
  unfold rb_rot_right_npf.
  rewrite (get_right_eq _ _ _ Hp). cbn [mbind option_bind]. rewrite Hpr.
  rewrite (set_left_eq _ _ _ _ Hpp). cbn [mbind option_bind].
  destruct (repar_spec (<[pp:=set_lft (troot tr) ndpp]> ns) tr p pp (N0 ++ inorder tl ++ [p]) (pp :: inorder sR ++ N1))
    as (ns2 & -> & Htr2 & E2 & D2 & C2).
  { eapply tree_at_frame; [|exact Htr]. apply lagree_insert_notin. nd_notin N. }
  { by repeat (rewrite <-app_assoc; cbn [app]). }
  cbn [mbind option_bind].
  assert (Htr0 : p ≠ troot tr ∧ pp ≠ troot tr).
  { destruct (troot_cases tr) as [[-> E0]|[? Hin]]; [cbn; split; nd_neq_with N|split; nd_neq_with N]. }
  destruct Htr0 as [Hptr Hpptr].
  assert (Hp2 : ns2 !! p = Some ndp) by (rewrite E2, lookup_insert_ne; done).
  assert (Hpp2 : ns2 !! pp = Some (set_lft (troot tr) ndpp)) by (rewrite E2, lookup_insert_eq; done).
  rewrite (get_left_eq _ _ _ Hp2). cbn [mbind option_bind]. rewrite Hpl.
  rewrite (set_right_eq _ _ _ _ Hp2). cbn [mbind option_bind].
  erewrite set_parent_eq by (rewrite lookup_insert_ne by done; exact Hpp2). cbn [fst snd].
  eexists _, _. split; [reflexivity|].
  set (ns' := <[pp:=_]> (<[p:=_]> ns2)).
  assert (E' : ∀ a, a ≠ pp → a ≠ p → a ≠ troot tr → ns' !! a = ns !! a).
  { intros a H1 H2 H3. subst ns'. rewrite lookup_insert_ne, lookup_insert_ne, E2, lookup_insert_ne; done. }
  split_and?.
  - subst ns'. rewrite lookup_insert_ne, lookup_insert_eq by done. done.
  - exact Hpl.
  - done.
  - eapply tree_at_frame; [|exact Htl]. intros b Hb. rewrite E'; [done|nd_neq_with N|nd_neq_with N|].
    destruct (troot_cases tr) as [[-> E0]|[? Hin]]; [cbn; nd_neq_with N|nd_neq_with N].
  - cbn [tree_at]. eexists. split; [subst ns'; by rewrite lookup_insert_eq|]. cbn. rewrite Hppr. split_and?; [done|done|done| |].
    * eapply tree_at_frame; [|exact Htr2]. intros b Hb. subst ns'.
      rewrite lookup_insert_ne, lookup_insert_ne; [done|nd_neq_with N|nd_neq_with N].
    * eapply tree_at_frame; [|exact HsR]. intros b Hb. rewrite E'; [done|nd_neq_with N|nd_neq_with N|].
      destruct (troot_cases tr) as [[-> E0]|[? Hin]]; [cbn; nd_neq_with N|nd_neq_with N].
  - exact E'.
  - eapply samedom_trans; [eapply samedom_insert'; [exact Hpp|apply samedom_refl]|].
    eapply samedom_trans; [exact D2|]. subst ns'.
    eapply samedom_insert'; [rewrite lookup_insert_ne by done; exact Hpp2|].
    eapply samedom_insert'; [exact Hp2|apply samedom_refl].
  - intros X C. subst ns'.
    eapply cols_ok_insert; [|rewrite lookup_insert_ne by done; exact Hpp2|by left].
    eapply cols_ok_insert; [|exact Hp2|by left].
    apply C2. eapply cols_ok_insert; [exact C|exact Hpp|by left].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lagree_set_col' X ns a nd v : ns !! a = Some nd → lagree X ns (<[a := set_col v nd]> ns).
Proof. apply lagree_set_col. Qed.

(* [comment removed for export] *)
Lemma rotate_right_full_spec ns h up2 gp q QL QR unc ndg ndq :
  ctx_at ns h up2 gp →
  ns !! gp = Some ndg → n_par ndg = ctx_node h up2 → n_rgt ndg = troot unc → tree_at ns unc gp →
  ns !! q = Some ndq → n_lft ndq = troot QL → n_rgt ndq = troot QR → tree_at ns QL q → tree_at ns QR q →
  NoDup (0 :: h :: lfr up2 ++ inorder QL ++ q :: inorder QR ++ gp :: inorder unc ++ rfr up2) →
  ∃ ns', rb_rotate_right_full ns h gp q = Some ns'
    ∧ top_at ns' h (plug up2 (Node QL q (Node QR gp unc)))
    ∧ (∀ hd, ns !! h = Some hd → ∃ hd', ns' !! h = Some hd' ∧ n_lft hd' = n_lft hd ∧ n_rgt hd' = n_rgt hd)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros HC Hg Hgp Hgr Hunc Hq Hql Hqr HQL HQR N.
  set (g3 := ctx_node h up2) in *.
  destruct (ctx_at_owner ns h up2 gp HC) as (nd3 & H3 & H3f). fold g3 in H3.
  (* [comment removed for export] *)
  assert (HQRc : troot QR = 0 ∨ troot QR ∈ inorder QR) by (destruct (troot_cases QR) as [[_ ?]|[_ ?]]; auto).
  assert (Hg3c : g3 = h ∨ g3 ∈ lfr up2 ∨ g3 ∈ rfr up2).
  { destruct (ctx_node_in h up2) as [E|Hin]; [by left|right]. rewrite cnodes_perm, elem_of_app in Hin. exact Hin. }
  assert (Hgq : gp ≠ q) by nd_neq_with N.
  assert (HqQR : q ≠ troot QR) by (destruct HQRc as [->|?]; nd_neq_with N).
  assert (HgQR : gp ≠ troot QR) by (destruct HQRc as [->|?]; nd_neq_with N).
  assert (Hhq : h ≠ q) by nd_neq_with N.
  assert (Hhg : h ≠ gp) by nd_neq_with N.
  assert (HhQR : h ≠ troot QR) by (destruct HQRc as [->|?]; nd_neq_with N).
  assert (H3q : g3 ≠ q) by (destruct Hg3c as [->|[?|?]]; nd_neq_with N).
  assert (H3g : g3 ≠ gp) by (destruct Hg3c as [->|[?|?]]; nd_neq_with N).
  assert (H3QR : g3 ≠ troot QR).
  { destruct Hg3c as [->|[?|?]]; destruct HQRc as [E|?]; try rewrite E; nd_neq_with N. }
  (* [comment removed for export] *)
  unfold rb_rotate_right_full.
  rewrite (get_parent_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgp.
  rewrite (get_right_eq _ _ _ Hq). cbn [mbind option_bind]. rewrite Hqr.
  rewrite (get_left_eq _ _ _ H3). cbn [mbind option_bind].
  rewrite (set_left_eq _ _ _ _ Hg). cbn [mbind option_bind].
  destruct (repar_spec (<[gp:=set_lft (troot QR) ndg]> ns) QR q gp (h :: lfr up2 ++ inorder QL ++ [q]) (gp :: inorder unc ++ rfr up2))
    as (ns2 & -> & HQR2 & E2 & D2 & C2).
  { eapply tree_at_frame; [|exact HQR]. apply lagree_insert_notin. nd_notin N. }
  { cbn [app]. by repeat (rewrite <-app_assoc; cbn [app]). }
  cbn [mbind option_bind].
  assert (Hg2 : ns2 !! gp = Some (set_lft (troot QR) ndg)) by (rewrite E2, lookup_insert_eq; done).
  assert (Hq2 : ns2 !! q = Some ndq) by (rewrite E2, lookup_insert_ne; done).
  assert (H32 : ns2 !! g3 = Some nd3) by (rewrite E2, lookup_insert_ne; done).
  rewrite (set_parent_eq _ _ _ _ Hg2). cbn [mbind option_bind].
  erewrite set_parent_eq by (rewrite lookup_insert_ne by done; exact Hq2). cbn [mbind option_bind].
  erewrite set_right_eq by (by rewrite lookup_insert_eq). cbn [mbind option_bind].
  rewrite insert_insert_eq. cbn [set_par set_lft set_rgt n_par n_lft n_rgt n_col].
  set (ns5 := <[q:=_]> (<[gp:=_]> ns2)).
  assert (E5 : ∀ a, a ≠ q → a ≠ gp → a ≠ troot QR → ns5 !! a = ns !! a).
  { intros a ? ? ?. subst ns5. rewrite lookup_insert_ne, lookup_insert_ne, E2, lookup_insert_ne; done. }
  unfold rb_set_child_black.
  destruct (set_child_spec ns ns5 h up2 gp q nd3 (inorder QL ++ q :: inorder QR) (inorder unc) HC H3)
    as (ns6 & E6v & HC6 & E6 & Hh6 & D6 & C6).
  { rewrite E5; done. }
  { intros b Hb. rewrite E5; [done| | |].
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[?|?]]; nd_neq_with N.
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[?|?]]; nd_neq_with N.
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb.
      destruct Hb as [->|[?|?]]; destruct HQRc as [E|?]; try rewrite E; nd_neq_with N. }
  { by repeat (rewrite <-app_assoc; cbn [app]). }
  fold g3 in E6v. rewrite E6v. cbn [mbind option_bind].
  assert (Hq6 : ns6 !! q = Some (mkNode g3 (n_lft ndq) gp (n_col ndq))).
  { rewrite E6 by done. subst ns5. by rewrite lookup_insert_eq. }
  rewrite (set_color_eq _ _ _ _ Hq6). eexists. split; [reflexivity|].
  set (ns7 := <[q:=_]> ns6).
  assert (E72 : ∀ a, a ≠ q → a ≠ g3 → a ≠ gp → ns7 !! a = ns2 !! a).
  { intros a ? ? ?. subst ns7 ns5. rewrite lookup_insert_ne, E6, lookup_insert_ne, lookup_insert_ne; done. }
  assert (E7 : ∀ a, a ≠ q → a ≠ g3 → a ≠ gp → a ≠ troot QR → ns7 !! a = ns !! a).
  { intros a ? ? ? ?. rewrite E72, E2, lookup_insert_ne; done. }
  split_and?.
  - (* [comment removed for export] *)
    apply (proj2 (top_at_plug ns7 h up2 (Node QL q (Node QR gp unc)))). split.
    + cbn [troot]. eapply ctx_at_frame; [|exact HC6]. subst ns7. by apply lagree_set_col'.
    + cbn [tree_at troot]. eexists. split; [subst ns7; by rewrite lookup_insert_eq|]. cbn. rewrite Hql.
      split_and?; [done|done|done| |].
      * eapply tree_at_frame; [|exact HQL]. intros b Hb. rewrite E7; [done|nd_neq_with N| |nd_neq_with N|].
        -- destruct Hg3c as [->|[?|?]]; nd_neq_with N.
        -- destruct HQRc as [E|?]; [rewrite E|]; nd_neq_with N.
      * eexists. split.
        { subst ns7 ns5. rewrite lookup_insert_ne, E6, lookup_insert_ne, lookup_insert_eq; [reflexivity|done|done|done]. }
        cbn. rewrite Hgr. split_and?; [done|done|done| |].
        -- eapply tree_at_frame; [|exact HQR2]. intros b Hb. rewrite E72; [done|nd_neq_with N| |nd_neq_with N].
           destruct Hg3c as [->|[?|?]]; nd_neq_with N.
        -- eapply tree_at_frame; [|exact Hunc]. intros b Hb. rewrite E7; [done|nd_neq_with N| |nd_neq_with N|].
           ++ destruct Hg3c as [->|[?|?]]; nd_neq_with N.
           ++ destruct HQRc as [E|?]; [rewrite E|]; nd_neq_with N.
  - (* [comment removed for export] *)
    intros hd Hhd. destruct (Hh6 hd) as (hd6 & Hhd6 & El & Er); [by rewrite E5|].
    exists hd6. subst ns7. rewrite lookup_insert_ne by done. done.
  - (* [comment removed for export] *)
    eapply samedom_trans; [eapply samedom_insert'; [exact Hg|apply samedom_refl]|].
    eapply samedom_trans; [exact D2|].
    eapply samedom_trans; [|eapply samedom_trans; [exact D6|subst ns7; eapply samedom_insert'; [exact Hq6|apply samedom_refl]]].
    subst ns5. eapply samedom_insert'; [rewrite lookup_insert_ne by done; exact Hq2|].
    eapply samedom_insert'; [exact Hg2|apply samedom_refl].
  - (* [comment removed for export] *)
    intros X C. subst ns7. eapply cols_ok_insert; [|exact Hq6|right; left; by right].
    apply C6. subst ns5. eapply cols_ok_insert; [|rewrite lookup_insert_ne by done; exact Hq2|by left].
    eapply cols_ok_insert; [|exact Hg2|by left].
    apply C2. eapply cols_ok_insert; [exact C|exact Hg|by left].
Qed.

(* [comment removed for export] *)
Lemma rotate_left_full_spec ns h up2 gp q QL QR unc ndg ndq :
  ctx_at ns h up2 gp →
  ns !! gp = Some ndg → n_par ndg = ctx_node h up2 → n_lft ndg = troot unc → tree_at ns unc gp →
  ns !! q = Some ndq → n_lft ndq = troot QL → n_rgt ndq = troot QR → tree_at ns QL q → tree_at ns QR q →
  NoDup (0 :: h :: lfr up2 ++ inorder unc ++ gp :: inorder QL ++ q :: inorder QR ++ rfr up2) →
  ∃ ns', rb_rotate_left_full ns h gp q (troot QL) = Some ns'
    ∧ top_at ns' h (plug up2 (Node (Node unc gp QL) q QR))
    ∧ (∀ hd, ns !! h = Some hd → ∃ hd', ns' !! h = Some hd' ∧ n_lft hd' = n_lft hd ∧ n_rgt hd' = n_rgt hd)
    ∧ samedom ns ns'
    ∧ (∀ X, cols_ok X ns → cols_ok X ns').
Proof.
  intros HC Hg Hgp Hgl Hunc Hq Hql Hqr HQL HQR N.
  set (g3 := ctx_node h up2) in *.
  destruct (ctx_at_owner ns h up2 gp HC) as (nd3 & H3 & H3f). fold g3 in H3.
  assert (HQLc : troot QL = 0 ∨ troot QL ∈ inorder QL) by (destruct (troot_cases QL) as [[_ ?]|[_ ?]]; auto).
  assert (Hg3c : g3 = h ∨ g3 ∈ lfr up2 ∨ g3 ∈ rfr up2).
  { destruct (ctx_node_in h up2) as [E|Hin]; [by left|right]. rewrite cnodes_perm, elem_of_app in Hin. exact Hin. }
  assert (Hgq : gp ≠ q) by nd_neq_with N.
  assert (HqQL : q ≠ troot QL) by (destruct HQLc as [->|?]; nd_neq_with N).
  assert (HgQL : gp ≠ troot QL) by (destruct HQLc as [->|?]; nd_neq_with N).
  assert (Hhq : h ≠ q) by nd_neq_with N.
  assert (Hhg : h ≠ gp) by nd_neq_with N.
  assert (HhQL : h ≠ troot QL) by (destruct HQLc as [->|?]; nd_neq_with N).
  assert (H3q : g3 ≠ q) by (destruct Hg3c as [->|[?|?]]; nd_neq_with N).
  assert (H3g : g3 ≠ gp) by (destruct Hg3c as [->|[?|?]]; nd_neq_with N).
  assert (H3QL : g3 ≠ troot QL).
  { destruct Hg3c as [->|[?|?]]; destruct HQLc as [E|?]; try rewrite E; nd_neq_with N. }
  unfold rb_rotate_left_full.
  rewrite (get_parent_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgp.
  rewrite (get_left_eq _ _ _ H3). cbn [mbind option_bind].
  rewrite (set_right_eq _ _ _ _ Hg). cbn [mbind option_bind].
  destruct (repar_spec (<[gp:=set_rgt (troot QL) ndg]> ns) QL q gp (h :: lfr up2 ++ inorder unc ++ [gp]) (q :: inorder QR ++ rfr up2))
    as (ns2 & -> & HQL2 & E2 & D2 & C2).
  { eapply tree_at_frame; [|exact HQL]. apply lagree_insert_notin. nd_notin N. }
  { cbn [app]. by repeat (rewrite <-app_assoc; cbn [app]). }
  cbn [mbind option_bind].
  assert (Hg2 : ns2 !! gp = Some (set_rgt (troot QL) ndg)) by (rewrite E2, lookup_insert_eq; done).
  assert (Hq2 : ns2 !! q = Some ndq) by (rewrite E2, lookup_insert_ne; done).
  assert (H32 : ns2 !! g3 = Some nd3) by (rewrite E2, lookup_insert_ne; done).
  rewrite (set_parent_eq _ _ _ _ Hg2). cbn [mbind option_bind].
  erewrite set_parent_eq by (rewrite lookup_insert_ne by done; exact Hq2). cbn [mbind option_bind].
  erewrite set_left_eq by (by rewrite lookup_insert_eq). cbn [mbind option_bind].
  rewrite insert_insert_eq. cbn [set_par set_lft set_rgt n_par n_lft n_rgt n_col].
  set (ns5 := <[q:=_]> (<[gp:=_]> ns2)).
  assert (E5 : ∀ a, a ≠ q → a ≠ gp → a ≠ troot QL → ns5 !! a = ns !! a).
  { intros a ? ? ?. subst ns5. rewrite lookup_insert_ne, lookup_insert_ne, E2, lookup_insert_ne; done. }
  unfold rb_set_child_black.
  destruct (set_child_spec ns ns5 h up2 gp q nd3 (inorder unc) (inorder QL ++ q :: inorder QR) HC H3)
    as (ns6 & E6v & HC6 & E6 & Hh6 & D6 & C6).
  { rewrite E5; done. }
  { intros b Hb. rewrite E5; [done| | |].
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[?|?]]; nd_neq_with N.
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb. destruct Hb as [->|[?|?]]; nd_neq_with N.
    - rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb.
      destruct Hb as [->|[?|?]]; destruct HQLc as [E|?]; try rewrite E; nd_neq_with N. }
  { by repeat (rewrite <-app_assoc; cbn [app]). }
  fold g3 in E6v. rewrite E6v. cbn [mbind option_bind].
  assert (Hq6 : ns6 !! q = Some (mkNode g3 gp (n_rgt ndq) (n_col ndq))).
  { rewrite E6 by done. subst ns5. by rewrite lookup_insert_eq. }
  rewrite (set_color_eq _ _ _ _ Hq6). eexists. split; [reflexivity|].
  set (ns7 := <[q:=_]> ns6).
  assert (E72 : ∀ a, a ≠ q → a ≠ g3 → a ≠ gp → ns7 !! a = ns2 !! a).
  { intros a ? ? ?. subst ns7 ns5. rewrite lookup_insert_ne, E6, lookup_insert_ne, lookup_insert_ne; done. }
  assert (E7 : ∀ a, a ≠ q → a ≠ g3 → a ≠ gp → a ≠ troot QL → ns7 !! a = ns !! a).
  { intros a ? ? ? ?. rewrite E72, E2, lookup_insert_ne; done. }
  split_and?.
  - apply (proj2 (top_at_plug ns7 h up2 (Node (Node unc gp QL) q QR))). split.
    + cbn [troot]. eapply ctx_at_frame; [|exact HC6]. subst ns7. by apply lagree_set_col'.
    + cbn [tree_at troot]. eexists. split; [subst ns7; by rewrite lookup_insert_eq|]. cbn. rewrite Hqr.
      split_and?; [done|done|done| |].
      * eexists. split.
        { subst ns7 ns5. rewrite lookup_insert_ne, E6, lookup_insert_ne, lookup_insert_eq; [reflexivity|done|done|done]. }
        cbn. rewrite Hgl. split_and?; [done|done|done| |].
        -- eapply tree_at_frame; [|exact Hunc]. intros b Hb. rewrite E7; [done|nd_neq_with N| |nd_neq_with N|].
           ++ destruct Hg3c as [->|[?|?]]; nd_neq_with N.
           ++ destruct HQLc as [E|?]; [rewrite E|]; nd_neq_with N.
        -- eapply tree_at_frame; [|exact HQL2]. intros b Hb. rewrite E72; [done|nd_neq_with N| |nd_neq_with N].
           destruct Hg3c as [->|[?|?]]; nd_neq_with N.
      * eapply tree_at_frame; [|exact HQR]. intros b Hb. rewrite E7; [done|nd_neq_with N| |nd_neq_with N|].
        -- destruct Hg3c as [->|[?|?]]; nd_neq_with N.
        -- destruct HQLc as [E|?]; [rewrite E|]; nd_neq_with N.
  - intros hd Hhd. destruct (Hh6 hd) as (hd6 & Hhd6 & El & Er); [by rewrite E5|].
    exists hd6. subst ns7. rewrite lookup_insert_ne by done. done.
  - eapply samedom_trans; [eapply samedom_insert'; [exact Hg|apply samedom_refl]|].
    eapply samedom_trans; [exact D2|].
    eapply samedom_trans; [|eapply samedom_trans; [exact D6|subst ns7; eapply samedom_insert'; [exact Hq6|apply samedom_refl]]].
    subst ns5. eapply samedom_insert'; [rewrite lookup_insert_ne by done; exact Hq2|].
    eapply samedom_insert'; [exact Hg2|apply samedom_refl].
  - intros X C. subst ns7. eapply cols_ok_insert; [|exact Hq6|right; left; by right].
    apply C6. subst ns5. eapply cols_ok_insert; [|rewrite lookup_insert_ne by done; exact Hq2|by left].
    eapply cols_ok_insert; [|exact Hg2|by left].
    apply C2. eapply cols_ok_insert; [exact C|exact Hg|by left].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rb_repT_of_top (ns ns' : NS) h T T' hd :
  top_at ns' h T' → ns !! h = Some hd → n_lft hd = tmin h T → n_rgt hd = tmax h T →
  (∀ hd0, ns !! h = Some hd0 → ∃ hd', ns' !! h = Some hd' ∧ n_lft hd' = n_lft hd0 ∧ n_rgt hd' = n_rgt hd0) →
  inorder T' = inorder T → NoDup (0 :: h :: inorder T) → rb_repT h T' ns'.
Proof.
  intros [(hd1 & Hh1 & Hp1) Ht] Hh Hl Hr Hpres EI N.
  destruct (Hpres hd Hh) as (hd' & Hh' & El & Er). rewrite Hh1 in Hh'. injection Hh' as <-.
  split; [|split; [exact Ht|by rewrite EI]].
  exists hd1. split; [done|]. split; [done|]. unfold tmin, tmax in *. rewrite EI, El, Er. done.
Qed.

Section rb_final.
  Context (h : Z).

  Lemma rb_final_LL ns up2 t p pp sR gp unc :
    let T := plug up2 (Node (Node t pp sR) gp unc) in
    let T' := plug up2 (Node t pp (Node sR gp unc)) in
    troot t = p → t ≠ Leaf → rb_repT h T ns →
    ∃ ns', rb_final ns h p pp gp pp = Some ns'
      ∧ rb_repT h T' ns' ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' Hp Ht HR. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & _ & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. subst T. apply top_at_plug in HT as [HC Hgp].
    cbn [tree_at troot] in Hgp. destruct Hgp as (ndg & Hg & Hgpar & Hgl & Hgr & (ndpp & Hpp & Hpppar & Hppl & Hppr & Htt & HsR) & Hunc).
    pose proof N as N2. norm_list_in N2.
    unfold rb_final. rewrite (get_left_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hppl, Hp, !Z.eqb_refl.
    cbn [mbind option_bind].
    destruct (rotate_right_full_spec ns h up2 gp pp t sR unc ndg ndpp HC Hg Hgpar Hgr Hunc Hpp Hppl Hppr Htt HsR N2)
      as (ns' & -> & HT' & Hpres & D' & C').
    exists ns'. split; [done|]. split; [|by split].
    eapply (rb_repT_of_top ns ns' h (plug up2 (Node (Node t pp sR) gp unc))); eauto.
    unfold T'. rewrite !inorder_plug. cbn [inorder]. by repeat (rewrite <-app_assoc; cbn [app]).
  Qed.

  Lemma rb_final_LR ns up2 sL pp tl p tr gp unc :
    let T := plug up2 (Node (Node sL pp (Node tl p tr)) gp unc) in
    let T' := plug up2 (Node (Node sL pp tl) p (Node tr gp unc)) in
    rb_repT h T ns →
    ∃ ns', rb_final ns h p pp gp pp = Some ns'
      ∧ rb_repT h T' ns' ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' HR. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & _ & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. subst T. apply top_at_plug in HT as [HC Hgp].
    cbn [tree_at troot] in Hgp. destruct Hgp as (ndg & Hg & Hgpar & Hgl & Hgr & Hppt & Hunc).
    pose proof Hppt as Hppt'. destruct Hppt as (ndpp & Hpp & Hpppar & Hppl & Hppr & HsL & Ht).
    pose proof N as N2. norm_list_in N2.
    assert (HsLc : troot sL = 0 ∨ troot sL ∈ inorder sL) by (destruct (troot_cases sL) as [[_ ?]|[_ ?]]; auto).
    unfold rb_final. rewrite (get_left_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hppl, !Z.eqb_refl.
    rewrite (Zeqb_ne (troot sL) p) by (destruct HsLc as [->|?]; nd_neq_with N2).
    destruct (rot_left_npf_spec ns sL pp tl p tr gp (h :: lfr up2) (gp :: inorder unc ++ rfr up2) Hppt' N2)
      as (nsa & ndq & -> & (Hq & Hql & Hqr & HQL & HQR) & Ea & Da & Ca).
    cbn [mbind option_bind].
    assert (Htlc : troot tl = 0 ∨ troot tl ∈ inorder tl) by (destruct (troot_cases tl) as [[_ ?]|[_ ?]]; auto).
    assert (Hctx2 : ∀ b, b = h ∨ b ∈ lfr up2 ∨ b ∈ rfr up2 → b ≠ pp ∧ b ≠ p ∧ b ≠ troot tl).
    { intros b Hb. split_and!.
      - destruct Hb as [->|[?|?]]; nd_neq_with N2.
      - destruct Hb as [->|[?|?]]; nd_neq_with N2.
      - destruct Htlc as [E|Hin]; [rewrite E|]; destruct Hb as [->|[?|?]]; nd_neq_with N2. }
    destruct (rotate_right_full_spec nsa h up2 gp p (Node sL pp tl) tr unc ndg ndq) as (ns' & -> & HT' & Hpres & D' & C').
    - eapply ctx_at_frame; [|exact HC]. intros b Hb. rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb.
      destruct (Hctx2 b Hb) as (?&?&?). by rewrite Ea.
    - rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htlc as [->|?]; nd_neq_with N2].
    - done. - done.
    - eapply tree_at_frame; [|exact Hunc]. intros b Hb.
      rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htlc as [->|?]; nd_neq_with N2].
    - exact Hq. - exact Hql. - exact Hqr. - exact HQL. - exact HQR.
    - cbn [inorder]. norm_app. exact N2.
    - exists ns'. split; [done|]. split; [|split].
      + eapply (rb_repT_of_top ns ns' h (plug up2 (Node (Node sL pp (Node tl p tr)) gp unc))); eauto.
        * intros hd0 Hhd0. destruct (Hpres hd0) as (hd' & ? & ? & ?); [|by exists hd'].
          rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htlc as [->|?]; nd_neq_with N2].
        * unfold T'. rewrite !inorder_plug. cbn [inorder]. by repeat (rewrite <-app_assoc; cbn [app]).
      + eapply samedom_trans; eauto.
      + intros X C. apply C', Ca, C.
  Qed.

  Lemma rb_final_RR ns up2 unc gp sL pp t p :
    let T := plug up2 (Node unc gp (Node sL pp t)) in
    let T' := plug up2 (Node (Node unc gp sL) pp t) in
    troot t = p → t ≠ Leaf → rb_repT h T ns →
    ∃ ns', rb_final ns h p pp gp (troot unc) = Some ns'
      ∧ rb_repT h T' ns' ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' Hp Ht HR. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & _ & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. subst T. apply top_at_plug in HT as [HC Hgp].
    cbn [tree_at troot] in Hgp. destruct Hgp as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & (ndpp & Hpp & Hpppar & Hppl & Hppr & HsL & Htt)).
    pose proof N as N2. norm_list_in N2.
    assert (Huc : troot unc = 0 ∨ troot unc ∈ inorder unc) by (destruct (troot_cases unc) as [[_ ?]|[_ ?]]; auto).
    assert (HsLc : troot sL = 0 ∨ troot sL ∈ inorder sL) by (destruct (troot_cases sL) as [[_ ?]|[_ ?]]; auto).
    assert (Hpin : p ∈ inorder t) by (rewrite <-Hp; by apply troot_in).
    unfold rb_final. rewrite (get_left_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hppl.
    rewrite (Zeqb_ne pp (troot unc)) by (destruct Huc as [->|?]; nd_neq_with N2).
    rewrite (Zeqb_ne (troot sL) p) by (destruct HsLc as [->|?]; nd_neq_with N2).
    cbn [mbind option_bind].
    destruct (rotate_left_full_spec ns h up2 gp pp sL t unc ndg ndpp HC Hg Hgpar Hgl Hunc Hpp Hppl Hppr HsL Htt N2)
      as (ns' & -> & HT' & Hpres & D' & C').
    exists ns'. split; [done|]. split; [|by split].
    eapply (rb_repT_of_top ns ns' h (plug up2 (Node unc gp (Node sL pp t)))); eauto.
    unfold T'. rewrite !inorder_plug. cbn [inorder]. by repeat (rewrite <-app_assoc; cbn [app]).
  Qed.

  Lemma rb_final_RL ns up2 unc gp tl p tr pp sR :
    let T := plug up2 (Node unc gp (Node (Node tl p tr) pp sR)) in
    let T' := plug up2 (Node (Node unc gp tl) p (Node tr pp sR)) in
    rb_repT h T ns →
    ∃ ns', rb_final ns h p pp gp (troot unc) = Some ns'
      ∧ rb_repT h T' ns' ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns').
  Proof.
    intros T T' HR. pose proof (rep_N _ _ _ HR) as N.
    destruct (rep_hd _ _ _ HR) as (hd & Hh & _ & Hl & Hr).
    pose proof (rep_top _ _ _ HR) as HT. subst T. apply top_at_plug in HT as [HC Hgp].
    cbn [tree_at troot] in Hgp. destruct Hgp as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & Hppt).
    pose proof Hppt as Hppt'. destruct Hppt as (ndpp & Hpp & Hpppar & Hppl & Hppr & Ht & HsR).
    pose proof N as N2. norm_list_in N2.
    assert (Huc : troot unc = 0 ∨ troot unc ∈ inorder unc) by (destruct (troot_cases unc) as [[_ ?]|[_ ?]]; auto).
    unfold rb_final. rewrite (get_left_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hppl, !Z.eqb_refl.
    rewrite (Zeqb_ne pp (troot unc)) by (destruct Huc as [->|?]; nd_neq_with N2).
    destruct (rot_right_npf_spec ns tl p tr pp sR gp (h :: lfr up2 ++ inorder unc ++ [gp]) (rfr up2))
      as (nsa & ndq & Erot & (Hq & Hql & Hqr & HQL & HQR) & Ea & Da & Ca).
    { exact Hppt'. }
    { revert N2. clear. intros N2. by norm_app_in N2 || (cbn [app]; by repeat (rewrite <-app_assoc; cbn [app])). }
    rewrite Erot. cbn [mbind option_bind fst snd].
    assert (Htrc : troot tr = 0 ∨ troot tr ∈ inorder tr) by (destruct (troot_cases tr) as [[_ ?]|[_ ?]]; auto).
    assert (Hctx2 : ∀ b, b = h ∨ b ∈ lfr up2 ∨ b ∈ rfr up2 → b ≠ pp ∧ b ≠ p ∧ b ≠ troot tr).
    { intros b Hb. split_and!.
      - destruct Hb as [->|[?|?]]; nd_neq_with N2.
      - destruct Hb as [->|[?|?]]; nd_neq_with N2.
      - destruct Htrc as [E|Hin]; [rewrite E|]; destruct Hb as [->|[?|?]]; nd_neq_with N2. }
    destruct (rotate_left_full_spec nsa h up2 gp p tl (Node tr pp sR) unc ndg ndq) as (ns' & -> & HT' & Hpres & D' & C').
    - eapply ctx_at_frame; [|exact HC]. intros b Hb. rewrite elem_of_cons, cnodes_perm, elem_of_app in Hb.
      destruct (Hctx2 b Hb) as (?&?&?). by rewrite Ea.
    - rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htrc as [->|?]; nd_neq_with N2].
    - done. - done.
    - eapply tree_at_frame; [|exact Hunc]. intros b Hb.
      rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htrc as [->|?]; nd_neq_with N2].
    - exact Hq. - exact Hql. - exact Hqr. - exact HQL. - exact HQR.
    - cbn [inorder]. norm_app. exact N2.
    - exists ns'. split; [done|]. split; [|split].
      + eapply (rb_repT_of_top ns ns' h (plug up2 (Node unc gp (Node (Node tl p tr) pp sR)))); eauto.
        * intros hd0 Hhd0. destruct (Hpres hd0) as (hd' & ? & ? & ?); [|by exists hd'].
          rewrite Ea; [done|nd_neq_with N2|nd_neq_with N2|destruct Htrc as [->|?]; nd_neq_with N2].
        * unfold T'. rewrite !inorder_plug. cbn [inorder]. by repeat (rewrite <-app_assoc; cbn [app]).
      + eapply samedom_trans; eauto.
      + intros X C. apply C', Ca, C.
  Qed.
End rb_final.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rb_repT_setcol h T ns a nd v :
  rb_repT h T ns → ns !! a = Some nd → rb_repT h T (<[a := set_col v nd]> ns).
Proof.
  intros (Hhd & Ht & N) Ha. split; [|split; [|exact N]].
  - destruct Hhd as (hd & Hh & E). destruct (decide (a = h)) as [->|Hne].
    + rewrite Hh in Ha. injection Ha as <-. exists (set_col v hd). rewrite lookup_insert_eq. by destruct hd.
    + exists hd. by rewrite lookup_insert_ne.
  - eapply tree_at_frame; [|exact Ht]. by apply lagree_set_col.
Qed.

Lemma cols_ok_setcol X ns a nd v :
  cols_ok X ns → ns !! a = Some nd → (v = RED ∨ v = BLACK) → cols_ok X (<[a := set_col v nd]> ns).
Proof. intros C Ha Hv. eapply cols_ok_insert; [exact C|exact Ha|]. right; left. exact Hv. Qed.

Definition body_post (h : Z) (c : ctx) (t : tree) (ns : NS)
           (s : (NS * (Z * Z)) + NS) : Prop :=
  match s with
  | inl (ns', (p', pp')) => ∃ c' t', c' ≠ Top ∧ pp' = ctx_node h c' ∧ troot t' = p' ∧ t' ≠ Leaf
       ∧ rb_repT h (plug c' t') ns' ∧ inorder (plug c' t') = inorder (plug c t) ∧ (cdepth c' + 2 <= cdepth c)%nat
       ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns')
  | inr ns' => ∃ T', rb_repT h T' ns' ∧ inorder T' = inorder (plug c t) ∧ T' ≠ Leaf
       ∧ samedom ns ns' ∧ (∀ X, cols_ok X ns → cols_ok X ns')
  end.

Lemma plug_ne_leaf c t : t ≠ Leaf → plug c t ≠ Leaf.
Proof.
  intros Ht E. assert (X : inorder (plug c t) = []) by (by rewrite E).
  rewrite inorder_plug in X. apply app_nil in X as [_ X]. apply app_nil in X as [X _].
  by apply inorder_nil in X.
Qed.

Section rb_body.
  Context (h : Z).

  (* [comment removed for export] *)
  Lemma rb_body_spec_L up t pp sR ns p :
    troot t = p → t ≠ Leaf → rb_repT h (plug (GoL pp sR up) t) ns →
    ∃ s, rb_body h (ns, (p, pp)) = Some s ∧ body_post h (GoL pp sR up) t ns s.
  Proof.
    intros Hp Ht HR. pose proof (rep_N _ _ _ HR) as N.
    pose proof (rep_top _ _ _ HR) as HT. cbn [plug] in HT. apply top_at_plug in HT as [HC Hppt].
    cbn [tree_at troot] in Hppt. destruct Hppt as (ndpp & Hpp & Hpppar & Hppl & Hppr & Htt & HsR).
    unfold rb_body. rewrite (get_parent_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hpppar.
    destruct up as [|gp unc up2|unc gp up2]; cbn [ctx_node] in *.
    - (* [comment removed for export] *)
      rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
      exists (plug (GoL pp sR Top) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto].
    - (* [comment removed for export] *)
      pose proof N as N2. cbn [plug] in N2. norm_list_in N2.
      cbn in HC. destruct HC as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & HC2).
      rewrite (Zeqb_ne gp h) by nd_neq_with N2.
      rewrite (get_color_eq _ _ _ Hpp). cbn [mbind option_bind].
      destruct (Z.eqb_spec (n_col ndpp) BLACK) as [Eb|Hred].
      { eexists. split; [reflexivity|]. cbn [body_post].
        exists (plug (GoL pp sR (GoL gp unc up2)) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto]. }
      rewrite (get_left_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgl.
      rewrite (set_color_eq _ _ _ _ Hg). cbn [mbind option_bind]. rewrite Z.eqb_refl. cbn [negb].
      rewrite (get_right_eq (<[gp:=set_col RED ndg]> ns) gp (set_col RED ndg)) by (by rewrite lookup_insert_eq).
      cbn [mbind option_bind n_rgt set_col]. rewrite Hgr.
      set (ns1 := <[gp:=_]> ns).
      assert (HR1 : rb_repT h (plug (GoL pp sR (GoL gp unc up2)) t) ns1) by (by apply rb_repT_setcol).
      assert (D1 : samedom ns ns1) by (eapply samedom_insert'; [exact Hg|apply samedom_refl]).
      assert (C1 : ∀ X, cols_ok X ns → cols_ok X ns1) by (intros X C; apply cols_ok_setcol; [done|done|by left]).
      assert (HF : ∃ s, (ns2 ← rb_final ns1 h p pp gp pp ; Some (inr ns2)) = Some s ∧ body_post h (GoL pp sR (GoL gp unc up2)) t ns s).
      { destruct (rb_final_LL h ns1 up2 t p pp sR gp unc Hp Ht HR1) as (ns' & -> & HR' & D' & C').
        eexists. split; [reflexivity|]. cbn [body_post]. eexists. split_and?; [exact HR'| |by apply plug_ne_leaf| |].
        - cbn [plug]. rewrite !inorder_plug. cbn [inorder]. by norm_app.
        - eapply samedom_trans; eauto.
        - auto. }
      destruct unc as [|ul u ur].
      + (* [comment removed for export] *) cbn [troot Z.eqb]. exact HF.
      + cbn [troot]. cbn [tree_at] in Hunc. destruct Hunc as (ndu & Hu & Hupar & _ & _ & _).
        cbn [inorder] in N2. norm_list_in N2.
        rewrite (Zeqb_ne u 0) by nd_neq_with N2.
        assert (Hu1 : ns1 !! u = Some ndu) by (subst ns1; rewrite lookup_insert_ne; [done|nd_neq_with N2]).
        rewrite (get_color_eq _ _ _ Hu1). cbn [mbind option_bind].
        destruct (Z.eqb_spec (n_col ndu) RED) as [Hured|Hublk]; [|exact HF].
        (* [comment removed for export] *)
        clear HF. rewrite (set_color_eq _ _ _ _ Hu1). cbn [mbind option_bind].
        assert (Hpp2 : <[u:=set_col BLACK ndu]> ns1 !! pp = Some ndpp).
        { subst ns1. rewrite !lookup_insert_ne; [done|nd_neq_with N2|nd_neq_with N2]. }
        rewrite (set_color_eq _ _ _ _ Hpp2). cbn [mbind option_bind].
        erewrite get_parent_eq.
        2:{ subst ns1. rewrite lookup_insert_ne, lookup_insert_ne, lookup_insert_eq; [reflexivity|nd_neq_with N2|nd_neq_with N2]. }
        cbn [mbind option_bind n_par set_col]. rewrite Hgpar.
        set (ns3 := <[pp:=_]> (<[u:=_]> ns1)).
        assert (HR3 : rb_repT h (plug (GoL pp sR (GoL gp (Node ul u ur) up2)) t) ns3).
        { subst ns3. apply rb_repT_setcol; [|exact Hpp2]. by apply rb_repT_setcol. }
        assert (D3 : samedom ns ns3).
        { eapply samedom_trans; [exact D1|]. subst ns3. eapply samedom_insert'; [exact Hpp2|].
          eapply samedom_insert'; [exact Hu1|apply samedom_refl]. }
        assert (C3 : ∀ X, cols_ok X ns → cols_ok X ns3).
        { intros X C. subst ns3. apply cols_ok_setcol; [|done|by right]. apply cols_ok_setcol; [|done|by right]. by apply C1. }
        destruct up2 as [|g3 s3 up3|s3 g3 up3]; cbn [ctx_node].
        * rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
          eexists. split_and?; [exact HR3|done|by apply plug_ne_leaf|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoL g3 s3 up3), (Node (Node t pp sR) gp (Node ul u ur)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoR s3 g3 up3), (Node (Node t pp sR) gp (Node ul u ur)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
    - (* [comment removed for export] *)
      pose proof N as N2. cbn [plug] in N2. norm_list_in N2.
      cbn in HC. destruct HC as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & HC2).
      rewrite (Zeqb_ne gp h) by nd_neq_with N2.
      rewrite (get_color_eq _ _ _ Hpp). cbn [mbind option_bind].
      destruct (Z.eqb_spec (n_col ndpp) BLACK) as [Eb|Hred].
      { eexists. split; [reflexivity|]. cbn [body_post].
        exists (plug (GoL pp sR (GoR unc gp up2)) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto]. }
      rewrite (get_left_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgl.
      rewrite (set_color_eq _ _ _ _ Hg). cbn [mbind option_bind].
      assert (Huc : troot unc = 0 ∨ troot unc ∈ inorder unc) by (destruct (troot_cases unc) as [[_ ?]|[_ ?]]; auto).
      rewrite (Zeqb_ne pp (troot unc)) by (destruct Huc as [->|?]; nd_neq_with N2). cbn [negb mbind option_bind].
      set (ns1 := <[gp:=_]> ns).
      assert (HR1 : rb_repT h (plug (GoL pp sR (GoR unc gp up2)) t) ns1) by (by apply rb_repT_setcol).
      assert (D1 : samedom ns ns1) by (eapply samedom_insert'; [exact Hg|apply samedom_refl]).
      assert (C1 : ∀ X, cols_ok X ns → cols_ok X ns1) by (intros X C; apply cols_ok_setcol; [done|done|by left]).
      assert (HF : ∃ s, (ns2 ← rb_final ns1 h p pp gp (troot unc) ; Some (inr ns2)) = Some s ∧ body_post h (GoL pp sR (GoR unc gp up2)) t ns s).
      { destruct t as [|tl p' tr]; [done|]. cbn [troot] in Hp. subst p'.
        destruct (rb_final_RL h ns1 up2 unc gp tl p tr pp sR HR1) as (ns' & -> & HR' & D' & C').
        eexists. split; [reflexivity|]. cbn [body_post]. eexists. split_and?; [exact HR'| |by apply plug_ne_leaf| |].
        - cbn [plug]. rewrite !inorder_plug. cbn [inorder]. by norm_app.
        - eapply samedom_trans; eauto.
        - auto. }
      destruct unc as [|ul u ur].
      + cbn [troot Z.eqb]. exact HF.
      + cbn [troot]. cbn [tree_at] in Hunc. destruct Hunc as (ndu & Hu & Hupar & _ & _ & _).
        cbn [inorder] in N2. norm_list_in N2.
        rewrite (Zeqb_ne u 0) by nd_neq_with N2.
        assert (Hu1 : ns1 !! u = Some ndu) by (subst ns1; rewrite lookup_insert_ne; [done|nd_neq_with N2]).
        rewrite (get_color_eq _ _ _ Hu1). cbn [mbind option_bind].
        destruct (Z.eqb_spec (n_col ndu) RED) as [Hured|Hublk]; [|exact HF].
        clear HF. rewrite (set_color_eq _ _ _ _ Hu1). cbn [mbind option_bind].
        assert (Hpp2 : <[u:=set_col BLACK ndu]> ns1 !! pp = Some ndpp).
        { subst ns1. rewrite !lookup_insert_ne; [done|nd_neq_with N2|nd_neq_with N2]. }
        rewrite (set_color_eq _ _ _ _ Hpp2). cbn [mbind option_bind].
        erewrite get_parent_eq.
        2:{ subst ns1. rewrite lookup_insert_ne, lookup_insert_ne, lookup_insert_eq; [reflexivity|nd_neq_with N2|nd_neq_with N2]. }
        cbn [mbind option_bind n_par set_col]. rewrite Hgpar.
        set (ns3 := <[pp:=_]> (<[u:=_]> ns1)).
        assert (HR3 : rb_repT h (plug (GoL pp sR (GoR (Node ul u ur) gp up2)) t) ns3).
        { subst ns3. apply rb_repT_setcol; [|exact Hpp2]. by apply rb_repT_setcol. }
        assert (D3 : samedom ns ns3).
        { eapply samedom_trans; [exact D1|]. subst ns3. eapply samedom_insert'; [exact Hpp2|].
          eapply samedom_insert'; [exact Hu1|apply samedom_refl]. }
        assert (C3 : ∀ X, cols_ok X ns → cols_ok X ns3).
        { intros X C. subst ns3. apply cols_ok_setcol; [|done|by right]. apply cols_ok_setcol; [|done|by right]. by apply C1. }
        destruct up2 as [|g3 s3 up3|s3 g3 up3]; cbn [ctx_node].
        * rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
          eexists. split_and?; [exact HR3|done|by apply plug_ne_leaf|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoL g3 s3 up3), (Node (Node ul u ur) gp (Node t pp sR)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoR s3 g3 up3), (Node (Node ul u ur) gp (Node t pp sR)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
  Qed.
  (* [comment removed for export] *)
  Lemma rb_body_spec_R up sL t pp ns p :
    troot t = p → t ≠ Leaf → rb_repT h (plug (GoR sL pp up) t) ns →
    ∃ s, rb_body h (ns, (p, pp)) = Some s ∧ body_post h (GoR sL pp up) t ns s.
  Proof.
    intros Hp Ht HR. pose proof (rep_N _ _ _ HR) as N.
    pose proof (rep_top _ _ _ HR) as HT. cbn [plug] in HT. apply top_at_plug in HT as [HC Hppt].
    cbn [tree_at troot] in Hppt. destruct Hppt as (ndpp & Hpp & Hpppar & Hppl & Hppr & HsL & Htt).
    unfold rb_body. rewrite (get_parent_eq _ _ _ Hpp). cbn [mbind option_bind]. rewrite Hpppar.
    destruct up as [|gp unc up2|unc gp up2]; cbn [ctx_node] in *.
    - (* [comment removed for export] *)
      rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
      exists (plug (GoR sL pp Top) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto].
    - (* [comment removed for export] *)
      pose proof N as N2. cbn [plug] in N2. norm_list_in N2.
      cbn in HC. destruct HC as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & HC2).
      rewrite (Zeqb_ne gp h) by nd_neq_with N2.
      rewrite (get_color_eq _ _ _ Hpp). cbn [mbind option_bind].
      destruct (Z.eqb_spec (n_col ndpp) BLACK) as [Eb|Hred].
      { eexists. split; [reflexivity|]. cbn [body_post].
        exists (plug (GoR sL pp (GoL gp unc up2)) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto]. }
      rewrite (get_left_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgl.
      rewrite (set_color_eq _ _ _ _ Hg). cbn [mbind option_bind]. rewrite Z.eqb_refl. cbn [negb].
      rewrite (get_right_eq (<[gp:=set_col RED ndg]> ns) gp (set_col RED ndg)) by (by rewrite lookup_insert_eq).
      cbn [mbind option_bind n_rgt set_col]. rewrite Hgr.
      set (ns1 := <[gp:=_]> ns).
      assert (HR1 : rb_repT h (plug (GoR sL pp (GoL gp unc up2)) t) ns1) by (by apply rb_repT_setcol).
      assert (D1 : samedom ns ns1) by (eapply samedom_insert'; [exact Hg|apply samedom_refl]).
      assert (C1 : ∀ X, cols_ok X ns → cols_ok X ns1) by (intros X C; apply cols_ok_setcol; [done|done|by left]).
      assert (HF : ∃ s, (ns2 ← rb_final ns1 h p pp gp pp ; Some (inr ns2)) = Some s ∧ body_post h (GoR sL pp (GoL gp unc up2)) t ns s).
      { destruct t as [|tl p' tr]; [done|]. cbn [troot] in Hp. subst p'.
        destruct (rb_final_LR h ns1 up2 sL pp tl p tr gp unc HR1) as (ns' & -> & HR' & D' & C').
        eexists. split; [reflexivity|]. cbn [body_post]. eexists. split_and?; [exact HR'| |by apply plug_ne_leaf| |].
        - cbn [plug]. rewrite !inorder_plug. cbn [inorder]. by norm_app.
        - eapply samedom_trans; eauto.
        - auto. }
      destruct unc as [|ul u ur].
      + (* [comment removed for export] *) cbn [troot Z.eqb]. exact HF.
      + cbn [troot]. cbn [tree_at] in Hunc. destruct Hunc as (ndu & Hu & Hupar & _ & _ & _).
        cbn [inorder] in N2. norm_list_in N2.
        rewrite (Zeqb_ne u 0) by nd_neq_with N2.
        assert (Hu1 : ns1 !! u = Some ndu) by (subst ns1; rewrite lookup_insert_ne; [done|nd_neq_with N2]).
        rewrite (get_color_eq _ _ _ Hu1). cbn [mbind option_bind].
        destruct (Z.eqb_spec (n_col ndu) RED) as [Hured|Hublk]; [|exact HF].
        (* [comment removed for export] *)
        clear HF. rewrite (set_color_eq _ _ _ _ Hu1). cbn [mbind option_bind].
        assert (Hpp2 : <[u:=set_col BLACK ndu]> ns1 !! pp = Some ndpp).
        { subst ns1. rewrite !lookup_insert_ne; [done|nd_neq_with N2|nd_neq_with N2]. }
        rewrite (set_color_eq _ _ _ _ Hpp2). cbn [mbind option_bind].
        erewrite get_parent_eq.
        2:{ subst ns1. rewrite lookup_insert_ne, lookup_insert_ne, lookup_insert_eq; [reflexivity|nd_neq_with N2|nd_neq_with N2]. }
        cbn [mbind option_bind n_par set_col]. rewrite Hgpar.
        set (ns3 := <[pp:=_]> (<[u:=_]> ns1)).
        assert (HR3 : rb_repT h (plug (GoR sL pp (GoL gp (Node ul u ur) up2)) t) ns3).
        { subst ns3. apply rb_repT_setcol; [|exact Hpp2]. by apply rb_repT_setcol. }
        assert (D3 : samedom ns ns3).
        { eapply samedom_trans; [exact D1|]. subst ns3. eapply samedom_insert'; [exact Hpp2|].
          eapply samedom_insert'; [exact Hu1|apply samedom_refl]. }
        assert (C3 : ∀ X, cols_ok X ns → cols_ok X ns3).
        { intros X C. subst ns3. apply cols_ok_setcol; [|done|by right]. apply cols_ok_setcol; [|done|by right]. by apply C1. }
        destruct up2 as [|g3 s3 up3|s3 g3 up3]; cbn [ctx_node].
        * rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
          eexists. split_and?; [exact HR3|done|by apply plug_ne_leaf|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoL g3 s3 up3), (Node (Node sL pp t) gp (Node ul u ur)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoR s3 g3 up3), (Node (Node sL pp t) gp (Node ul u ur)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
    - (* [comment removed for export] *)
      pose proof N as N2. cbn [plug] in N2. norm_list_in N2.
      cbn in HC. destruct HC as (ndg & Hg & Hgpar & Hgl & Hgr & Hunc & HC2).
      rewrite (Zeqb_ne gp h) by nd_neq_with N2.
      rewrite (get_color_eq _ _ _ Hpp). cbn [mbind option_bind].
      destruct (Z.eqb_spec (n_col ndpp) BLACK) as [Eb|Hred].
      { eexists. split; [reflexivity|]. cbn [body_post].
        exists (plug (GoR sL pp (GoR unc gp up2)) t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto]. }
      rewrite (get_left_eq _ _ _ Hg). cbn [mbind option_bind]. rewrite Hgl.
      rewrite (set_color_eq _ _ _ _ Hg). cbn [mbind option_bind].
      assert (Huc : troot unc = 0 ∨ troot unc ∈ inorder unc) by (destruct (troot_cases unc) as [[_ ?]|[_ ?]]; auto).
      rewrite (Zeqb_ne pp (troot unc)) by (destruct Huc as [->|?]; nd_neq_with N2). cbn [negb mbind option_bind].
      set (ns1 := <[gp:=_]> ns).
      assert (HR1 : rb_repT h (plug (GoR sL pp (GoR unc gp up2)) t) ns1) by (by apply rb_repT_setcol).
      assert (D1 : samedom ns ns1) by (eapply samedom_insert'; [exact Hg|apply samedom_refl]).
      assert (C1 : ∀ X, cols_ok X ns → cols_ok X ns1) by (intros X C; apply cols_ok_setcol; [done|done|by left]).
      assert (HF : ∃ s, (ns2 ← rb_final ns1 h p pp gp (troot unc) ; Some (inr ns2)) = Some s ∧ body_post h (GoR sL pp (GoR unc gp up2)) t ns s).
      { destruct (rb_final_RR h ns1 up2 unc gp sL pp t p Hp Ht HR1) as (ns' & -> & HR' & D' & C').
        eexists. split; [reflexivity|]. cbn [body_post]. eexists. split_and?; [exact HR'| |by apply plug_ne_leaf| |].
        - cbn [plug]. rewrite !inorder_plug. cbn [inorder]. by norm_app.
        - eapply samedom_trans; eauto.
        - auto. }
      destruct unc as [|ul u ur].
      + cbn [troot Z.eqb]. exact HF.
      + cbn [troot]. cbn [tree_at] in Hunc. destruct Hunc as (ndu & Hu & Hupar & _ & _ & _).
        cbn [inorder] in N2. norm_list_in N2.
        rewrite (Zeqb_ne u 0) by nd_neq_with N2.
        assert (Hu1 : ns1 !! u = Some ndu) by (subst ns1; rewrite lookup_insert_ne; [done|nd_neq_with N2]).
        rewrite (get_color_eq _ _ _ Hu1). cbn [mbind option_bind].
        destruct (Z.eqb_spec (n_col ndu) RED) as [Hured|Hublk]; [|exact HF].
        clear HF. rewrite (set_color_eq _ _ _ _ Hu1). cbn [mbind option_bind].
        assert (Hpp2 : <[u:=set_col BLACK ndu]> ns1 !! pp = Some ndpp).
        { subst ns1. rewrite !lookup_insert_ne; [done|nd_neq_with N2|nd_neq_with N2]. }
        rewrite (set_color_eq _ _ _ _ Hpp2). cbn [mbind option_bind].
        erewrite get_parent_eq.
        2:{ subst ns1. rewrite lookup_insert_ne, lookup_insert_ne, lookup_insert_eq; [reflexivity|nd_neq_with N2|nd_neq_with N2]. }
        cbn [mbind option_bind n_par set_col]. rewrite Hgpar.
        set (ns3 := <[pp:=_]> (<[u:=_]> ns1)).
        assert (HR3 : rb_repT h (plug (GoR sL pp (GoR (Node ul u ur) gp up2)) t) ns3).
        { subst ns3. apply rb_repT_setcol; [|exact Hpp2]. by apply rb_repT_setcol. }
        assert (D3 : samedom ns ns3).
        { eapply samedom_trans; [exact D1|]. subst ns3. eapply samedom_insert'; [exact Hpp2|].
          eapply samedom_insert'; [exact Hu1|apply samedom_refl]. }
        assert (C3 : ∀ X, cols_ok X ns → cols_ok X ns3).
        { intros X C. subst ns3. apply cols_ok_setcol; [|done|by right]. apply cols_ok_setcol; [|done|by right]. by apply C1. }
        destruct up2 as [|g3 s3 up3|s3 g3 up3]; cbn [ctx_node].
        * rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn [body_post].
          eexists. split_and?; [exact HR3|done|by apply plug_ne_leaf|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoL g3 s3 up3), (Node (Node ul u ur) gp (Node sL pp t)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
        * cbn in HC2. destruct HC2 as (nd3 & H3 & _).
          pose proof N as N4. cbn [plug] in N4. norm_list_in N4.
          rewrite (Zeqb_ne g3 h) by nd_neq_with N4.
          eexists. split; [reflexivity|]. cbn [body_post].
          exists (GoR s3 g3 up3), (Node (Node ul u ur) gp (Node sL pp t)).
          split_and?; [done|done|done|done|exact HR3|done|cbn; lia|exact D3|exact C3].
  Qed.
End rb_body.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma oloop_inv_ghost {X R G} (body : X → option (X + R)) (I : G → X → Prop) (Q : R → Prop) (m : G → nat) :
  (∀ g x, I g x → ∃ s, body x = Some s ∧
        match s with inl x' => ∃ g', I g' x' ∧ (m g' < m g)%nat | inr r => Q r end) →
  ∀ n g x, I g x → (m g < n)%nat → ∃ r, oloop n body x = Some r ∧ Q r.
Proof.
  intros Hstep n. induction n as [|n IH]; intros g x Hx Hm; [lia|].
  rewrite oloop_S. destruct (Hstep g x Hx) as (s & -> & Hs). cbn.
  destruct s as [x'|r].
  - destruct Hs as (g' & Hx' & Hlt). apply (IH g'); [done|lia].
  - eauto.
Qed.

Lemma cols_ok_setcol_remove X ns a nd v :
  cols_ok (a :: X) ns → ns !! a = Some nd → (v = RED ∨ v = BLACK) → cols_ok X (<[a := set_col v nd]> ns).
Proof.
  intros C Ha Hv b ndb Hb Hnx. destruct (decide (a = b)) as [->|Hne].
  - rewrite lookup_insert_eq in Hb. injection Hb as <-. exact Hv.
  - rewrite lookup_insert_ne in Hb by done. apply (C b ndb Hb). rewrite not_elem_of_cons. by split.
Qed.

Section rebalance.
  Context (h : Z).

  Definition loop_inv (S0 : list Z) (ns0 : NS) (c : ctx) (st : NS * (Z * Z)) : Prop :=
    let '(ns, (p, pp)) := st in
    ∃ t, c ≠ Top ∧ pp = ctx_node h c ∧ troot t = p ∧ t ≠ Leaf ∧ rb_repT h (plug c t) ns
         ∧ inorder (plug c t) = S0 ∧ samedom ns0 ns ∧ (∀ X, cols_ok X ns0 → cols_ok X ns).

  Definition loop_post (S0 : list Z) (ns0 : NS) (ns' : NS) : Prop :=
    ∃ T', rb_repT h T' ns' ∧ inorder T' = S0 ∧ T' ≠ Leaf ∧ samedom ns0 ns' ∧ (∀ X, cols_ok X ns0 → cols_ok X ns').

  Lemma rb_loop_spec S0 ns0 fuel c st :
    loop_inv S0 ns0 c st → (cdepth c < fuel)%nat →
    ∃ ns', oloop fuel (rb_body h) st = Some ns' ∧ loop_post S0 ns0 ns'.
  Proof.
    apply (oloop_inv_ghost (rb_body h) (loop_inv S0 ns0) (loop_post S0 ns0) cdepth).
    clear c st. intros c [ns [p pp]] (t & Hc & Hpp & Hp & Ht & HR & HS & D & C).
    assert (HB : ∃ s, rb_body h (ns, (p, pp)) = Some s ∧ body_post h c t ns s).
    { destruct c as [|a sR up|sL a up]; [done| |]; cbn [ctx_node] in Hpp; subst a.
      - by apply rb_body_spec_L.
      - by apply rb_body_spec_R. }
    destruct HB as (s & -> & HP). exists s. split; [done|].
    destruct s as [[ns' [p' pp']]|ns']; cbn [body_post] in HP.
    - destruct HP as (c' & t' & Hc' & Hpp' & Hp' & Ht' & HR' & HS' & Hd & D' & C').
      exists c'. split; [|lia]. exists t'. split_and?; auto.
      + by rewrite HS'.
      + eapply samedom_trans; eauto.
    - destruct HP as (T' & HR' & HS' & HT' & D' & C').
      exists T'. split_and?; auto.
      + by rewrite HS'.
      + eapply samedom_trans; eauto.
  Qed.

  Theorem rebalance_spec c t ns p fuel :
    troot t = p → t ≠ Leaf → rb_repT h (plug c t) ns → (theight (plug c t) <= fuel)%nat →
    ∃ T' ns', rebalance_after_insertion fuel ns h p = Some ns'
      ∧ rb_repT h T' ns' ∧ inorder T' = inorder (plug c t)
      ∧ samedom ns ns' ∧ (∀ X, cols_ok (p :: X) ns → cols_ok X ns').
  Proof.
    intros Hp Ht HR Hf. pose proof (rep_N _ _ _ HR) as N.
    pose proof (rep_top _ _ _ HR) as HT. apply top_at_plug in HT as [HC Htt].
    destruct (tree_at_root _ _ _ Htt Ht) as (ndp & Hndp & Hppar). rewrite Hp in Hndp.
    unfold rebalance_after_insertion, rb_entry.
    rewrite (get_parent_eq _ _ _ Hndp). cbn [mbind option_bind]. rewrite Hppar.
    rewrite (set_color_eq _ _ _ _ Hndp). cbn [mbind option_bind].
    set (ns1 := <[p:=_]> ns).
    assert (HR1 : rb_repT h (plug c t) ns1) by (by apply rb_repT_setcol).
    assert (D1 : samedom ns ns1) by (eapply samedom_insert'; [exact Hndp|apply samedom_refl]).
    assert (C1 : ∀ X, cols_ok (p :: X) ns → cols_ok X ns1).
    { intros X CX. apply cols_ok_setcol_remove; [done|done|by left]. }
    (* [comment removed for export] *)
    assert (HL : ∃ ns2, match (if ctx_node h c =? h then inr () else inl (p, ctx_node h c))
                       with inl st => oloop fuel (rb_body h) (ns1, st) | inr _ => Some ns1 end = Some ns2
                 ∧ loop_post (inorder (plug c t)) ns1 ns2).
    { destruct (Z.eqb_spec (ctx_node h c) h) as [E|NE].
      - exists ns1. split; [done|]. exists (plug c t). split_and?; [done|done|by apply plug_ne_leaf|apply samedom_refl|auto].
      - apply (rb_loop_spec _ _ fuel c).
        + exists t. split_and?; auto; [|apply samedom_refl]. intros ->. by cbn in NE.
        + pose proof (cdepth_theight c t). destruct t; [done|]. cbn in *. lia. }
    destruct HL as (ns2 & -> & (T' & HR2 & HS2 & HT2 & D2 & C2)). cbn [mbind option_bind].
    (* [comment removed for export] *)
    unfold rb_end. destruct (rep_hd _ _ _ HR2) as (hd2 & Hh2 & Hp2 & _).
    rewrite (get_parent_eq _ _ _ Hh2). cbn [mbind option_bind]. rewrite Hp2.
    destruct (tree_at_root ns2 T' h (rep_tree _ _ _ HR2) HT2) as (ndr & Hr & _).
    rewrite (set_color_eq _ _ _ _ Hr). eexists T', _. split; [reflexivity|].
    split_and?.
    - by apply rb_repT_setcol.
    - done.
    - eapply samedom_trans; [exact D1|]. eapply samedom_trans; [exact D2|].
      eapply samedom_insert'; [exact Hr|apply samedom_refl].
    - intros X CX. apply cols_ok_setcol; [|done|by right]. apply C2. by apply C1.
  Qed.
End rebalance.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rb_insert_before_spec h T ns fuel A B n ndn :
  rb_repT h T ns → inorder T = A ++ B → ns !! n = Some ndn → n ≠ 0 → n ≠ h → n ∉ inorder T →
  (S (length (inorder T)) <= fuel)%nat →
  ∃ T' ns', rb_insert_before fuel ns h (lhead h B) n = Some ns'
    ∧ inorder T' = A ++ n :: B ∧ rb_repT h T' ns'
    ∧ samedom ns ns' ∧ (∀ X, cols_ok (n :: X) ns → cols_ok X ns').
Proof.
  intros HR HS Hn Hn0 Hnh Hnin Hf. unfold rb_insert_before.
  destruct (bst_insert_before_spec h T ns fuel A B n ndn HR HS Hn Hn0 Hnh Hnin) as (c' & ns1 & -> & HS1 & HR1 & D1 & C1).
  { pose proof (theight_le_tsize T). unfold tsize in *. lia. }
  cbn [mbind option_bind].
  destruct (rebalance_spec h c' (Node Leaf n Leaf) ns1 n fuel) as (T' & ns' & -> & HR' & HS' & D' & C'); [done|done|done| |].
  { pose proof (theight_le_tsize (plug c' (Node Leaf n Leaf))) as X. unfold tsize in X. rewrite HS1 in X.
    rewrite length_app in X. cbn in X. rewrite HS, length_app in Hf. lia. }
  exists T', ns'. split_and?; [done|by rewrite HS'|done|by eapply samedom_trans|].
  intros X CX. apply C', C1, CX.
Qed.

(* [comment removed for export] *)
Lemma pos_split h S pos :
  NoDup (h :: S) → (pos = h ∨ pos ∈ S) → ∃ A B, S = A ++ B ∧ pos = lhead h B.
Proof.
  intros N [->|Hin].
  - exists S, []. by rewrite app_nil_r.
  - destruct (list_elem_of_split S pos Hin) as (A & B & ->). exists A, (pos :: B). done.
Qed.

(* [comment removed for export] *)
Theorem rb_insert_before_ok h S ns fuel A B n ndn :
  rb_ok h S ns → S = A ++ B → n ≠ 0 → n ≠ h → n ∉ S → (length S < fuel)%nat →
  ∃ ns', rb_insert_before fuel (<[n := ndn]> ns) h (lhead h B) n = Some ns'
    ∧ rb_ok h (A ++ n :: B) ns'
    ∧ (∀ a, is_Some (ns' !! a) ↔ a = n ∨ is_Some (ns !! a)).
Proof.
  intros (T & HS & HR & HD & HCo) HAB Hn0 Hnh Hnin Hf. subst S.
  destruct (rb_insert_before_spec h T (<[n:=ndn]> ns) fuel A B n ndn) as (T' & ns' & -> & HS' & HR' & D' & C');
    [by apply rb_repT_ext|done|by rewrite lookup_insert_eq|done|done|done|lia|].
  exists ns'. split; [done|]. split.
  + exists T'. split; [done|]. split; [done|]. split.
      * intros a. rewrite (D' a). destruct (decide (a = n)) as [->|Hne].
        -- rewrite lookup_insert_eq. split; [intros _; right; rewrite HS'; set_solver|done].
        -- rewrite lookup_insert_ne by done. rewrite (HD a), HAB, HS'.
           rewrite !elem_of_app, elem_of_cons. naive_solver.
      * apply C'. intros b nd Hb Hbn. destruct (decide (b = n)) as [->|Hne]; [set_solver|].
        rewrite lookup_insert_ne in Hb by done. apply (HCo b nd Hb). set_solver.
    + intros a. rewrite (D' a). destruct (decide (a = n)) as [->|Hne].
      * rewrite lookup_insert_eq. split; auto.
      * rewrite lookup_insert_ne by done. naive_solver.
Qed.
