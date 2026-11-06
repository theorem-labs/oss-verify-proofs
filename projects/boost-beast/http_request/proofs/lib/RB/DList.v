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

(* [comment removed for export] *)
Fixpoint nxt_in (w : Z) (l : list Z) (x : Z) : Z :=
  match l with
  | [] => w
  | y :: l' => if y =? x then lhead w l' else nxt_in w l' x
  end.

Definition cnext (hL : Z) (L : list Z) (x : Z) : Z := nxt_in hL (hL :: L) x.
(* [comment removed for export] *)
Definition cprev (hL : Z) (L : list Z) (x : Z) : Z := lprev (llast hL L) (hL :: L) x.

Lemma nxt_in_split w P y Q : NoDup (P ++ y :: Q) → nxt_in w (P ++ y :: Q) y = lhead w Q.
Proof.
  induction P as [|z P IH]; intros N; cbn.
  - by rewrite Z.eqb_refl.
  - rewrite (Zeqb_ne z y) by nd_neq_with N. apply IH. exact (nd_cons_tl _ _ N).
Qed.

Lemma lprev_split d P y Q : NoDup (P ++ y :: Q) → lprev d (P ++ y :: Q) y = llast d P.
Proof.
  revert d. induction P as [|z P IH]; intros d N; cbn.
  - by rewrite Z.eqb_refl.
  - rewrite (Zeqb_ne z y) by nd_neq_with N. rewrite IH by exact (nd_cons_tl _ _ N).
    by rewrite llast_cons.
Qed.

Lemma cnext_char hL L P y Q : NoDup (hL :: L) → hL :: L = P ++ y :: Q → cnext hL L y = lhead hL Q.
Proof. intros N E. unfold cnext. rewrite E. apply nxt_in_split. by rewrite <-E. Qed.

Lemma cprev_char hL L P y Q : NoDup (hL :: L) → hL :: L = P ++ y :: Q → cprev hL L y = llast (llast hL L) P.
Proof.
  intros N E. unfold cprev. rewrite E in N. rewrite (lprev_split _ _ _ _ N) || (rewrite E; rewrite (lprev_split _ _ _ _ N)).
  done.
Qed.

(* [comment removed for export] *)
Lemma cnext_hd hL L : cnext hL L hL = lhead hL L.
Proof. unfold cnext. cbn. by rewrite Z.eqb_refl. Qed.
Lemma cprev_hd hL L : cprev hL L hL = llast hL L.
Proof. unfold cprev. cbn. by rewrite Z.eqb_refl. Qed.
Lemma cnext_at hL A x B : NoDup (hL :: A ++ x :: B) → cnext hL (A ++ x :: B) x = lhead hL B.
Proof. intros N. apply (cnext_char hL _ (hL :: A) x B N). done. Qed.
Lemma cprev_at hL A x B : NoDup (hL :: A ++ x :: B) → cprev hL (A ++ x :: B) x = llast hL A.
Proof.
  intros N. rewrite (cprev_char hL _ (hL :: A) x B N) by done. by rewrite llast_cons.
Qed.

(* [comment removed for export] *)
Lemma lhead_app_ne (d : Z) l1 l2 : l1 ≠ [] → lhead d (l1 ++ l2) = lhead d l1.
Proof. by destruct l1. Qed.
Lemma llast_ne (d d' : Z) l : l ≠ [] → llast d l = llast d' l.
Proof. destruct l; [done|]. intros _. apply last_cons_indep. Qed.
Lemma llast_app_ne (d : Z) l1 l2 : l2 ≠ [] → llast d (l1 ++ l2) = llast d l2.
Proof.
  intros H. destruct l2 as [|x l2]; [done|]. by rewrite llast_app_cons, llast_cons.
Qed.
Lemma llast_snoc (d : Z) l x : llast d (l ++ [x]) = x.
Proof. by rewrite llast_app_cons. Qed.

Lemma NoDup_remove_mid (P Q : list Z) t : NoDup (P ++ t :: Q) → NoDup (P ++ Q).
Proof.
  intros N. apply NoDup_app in N as (N1 & D & N2). apply NoDup_cons in N2 as [_ N2].
  apply NoDup_app. split_and!; [done| |done]. intros x Hx Hx2. apply (D x Hx). set_solver.
Qed.

Lemma cnext_insert_other hL A B t y :
  NoDup (hL :: A ++ t :: B) → y ∈ hL :: A ++ B → y ≠ llast hL A →
  cnext hL (A ++ t :: B) y = cnext hL (A ++ B) y.
Proof.
  intros N Hy Hne.
  assert (N0 : NoDup (hL :: A ++ B)) by exact (NoDup_remove_mid (hL :: A) B t N).
  destruct (list_elem_of_split _ _ Hy) as (P & Q & E).
  rewrite (cnext_char hL (A ++ B) P y Q N0 E).
  change (hL :: A ++ B) with ((hL :: A) ++ B) in E.
  destruct (split_app_cases _ _ _ _ E) as [(R & EA & EQ)|(R & EP & EB)].
  - destruct R as [|r R].
    + (* [comment removed for export] *)
      rewrite app_nil_r in EA. cbn in EQ. subst B.
      apply (cnext_char hL _ (P ++ [t]) y Q N). cbn. rewrite <-app_assoc. cbn. by rewrite <-EA.
    + (* [comment removed for export] *)
      cbn in EQ. injection EQ as <- EQ. subst Q.
      destruct R as [|r' R'].
      { exfalso. apply Hne. destruct P as [|p0 P']; cbn in EA.
        - injection EA as <- ->. done.
        - injection EA as -> ->. by rewrite llast_snoc. }
      rewrite (cnext_char hL (A ++ t :: B) P y ((r' :: R') ++ t :: B) N); [done|].
      cbn. change (hL :: A ++ t :: B) with ((hL :: A) ++ t :: B). rewrite EA. by rewrite <-app_assoc.
  - (* [comment removed for export] *)
    subst B P. apply (cnext_char hL _ ((hL :: A) ++ t :: R) y Q N). cbn. by rewrite <-app_assoc.
Qed.

Lemma cprev_insert_other hL A B t y :
  NoDup (hL :: A ++ t :: B) → y ∈ hL :: A ++ B → y ≠ lhead hL B →
  cprev hL (A ++ t :: B) y = cprev hL (A ++ B) y.
Proof.
  intros N Hy Hne.
  assert (N0 : NoDup (hL :: A ++ B)) by exact (NoDup_remove_mid (hL :: A) B t N).
  assert (HB : y = hL → B ≠ []) by (intros -> ->; by apply Hne).
  destruct (list_elem_of_split _ _ Hy) as (P & Q & E).
  rewrite (cprev_char hL (A ++ B) P y Q N0 E).
  change (hL :: A ++ B) with ((hL :: A) ++ B) in E.
  destruct (split_app_cases _ _ _ _ E) as [(R & EA & EQ)|(R & EP & EB)].
  - destruct R as [|r R].
    + (* [comment removed for export] *) exfalso. apply Hne. cbn in EQ. by rewrite <-EQ.
    + cbn in EQ. injection EQ as <- EQ. subst Q.
      rewrite (cprev_char hL (A ++ t :: B) P y (R ++ t :: B) N).
      2:{ cbn. change (hL :: A ++ t :: B) with ((hL :: A) ++ t :: B). rewrite EA. by rewrite <-app_assoc. }
      destruct P as [|p0 P'].
      * (* [comment removed for export] *) cbn in EA. injection EA as <- EA. cbn [llast List.last].
        rewrite !llast_app. destruct B; [|done]. exfalso. by apply HB.
      * by apply llast_ne.
  - subst B P. rewrite (cprev_char hL (A ++ t :: R ++ y :: Q) ((hL :: A) ++ t :: R) y Q N).
    2:{ cbn. by rewrite <-app_assoc. }
    destruct R as [|r R]; [exfalso; by apply Hne|].
    cbn. rewrite !llast_cons, !llast_app, !llast_cons. reflexivity.
Qed.

Lemma cnext_insert_prv hL A B t :
  NoDup (hL :: A ++ t :: B) → cnext hL (A ++ t :: B) (llast hL A) = t.
Proof.
  intros N. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)].
  - rewrite llast_nil. cbn [app]. apply cnext_hd.
  - rewrite llast_snoc. rewrite <-app_assoc. cbn [app]. apply cnext_at. by rewrite <-app_assoc in N.
Qed.

Lemma cprev_insert_nxt hL A B t :
  NoDup (hL :: A ++ t :: B) → cprev hL (A ++ t :: B) (lhead hL B) = t.
Proof.
  intros N. destruct B as [|b B]; cbn [lhead].
  - by rewrite cprev_hd, llast_snoc.
  - rewrite (cprev_char hL _ (hL :: A ++ [t]) b B N); [|cbn; by rewrite <-app_assoc].
    rewrite llast_cons. apply llast_snoc.
Qed.

Lemma cnext_pos hL A B : NoDup (hL :: A ++ B) → cnext hL (A ++ B) (llast hL A) = lhead hL B.
Proof.
  intros N. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)].
  - rewrite llast_nil. cbn [app]. apply cnext_hd.
  - rewrite llast_snoc. rewrite <-app_assoc. cbn [app]. apply cnext_at. by rewrite <-app_assoc in N.
Qed.
Lemma cprev_pos hL A B : NoDup (hL :: A ++ B) → cprev hL (A ++ B) (lhead hL B) = llast hL A.
Proof.
  intros N. destruct B as [|b B]; cbn [lhead].
  - by rewrite cprev_hd, app_nil_r.
  - by apply cprev_at.
Qed.
Lemma nxt_eq_prv hL A B : NoDup (hL :: A ++ B) → lhead hL B = llast hL A → A = [] ∧ B = [].
Proof.
  intros N E. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)]; destruct B as [|b B]; cbn in E.
  - done.
  - exfalso. rewrite llast_nil in E. subst b. cbn in N. apply NoDup_cons in N as [N _]. apply N. set_solver.
  - exfalso. rewrite llast_snoc in E. subst a. apply NoDup_cons in N as [N _]. apply N. set_solver.
  - exfalso. rewrite llast_snoc in E. subst b. apply nd_cons_tl in N. rewrite <-app_assoc in N. cbn in N.
    apply nd_app_tl in N. apply NoDup_cons in N as [N _]. apply N. set_solver.
Qed.

Lemma nxt_in_in w l x : nxt_in w l x = w ∨ nxt_in w l x ∈ l.
Proof.
  induction l as [|y l IH]; cbn; [by left|].
  destruct (y =? x).
  - destruct l; cbn; [by left|right; set_solver].
  - destruct IH as [IH|IH]; [by left|right; set_solver].
Qed.
Lemma lprev_in d l x : lprev d l x = d ∨ lprev d l x ∈ l.
Proof.
  revert d; induction l as [|y l IH]; intros d; cbn; [by left|].
  destruct (y =? x); [by left|]. destruct (IH y) as [E|H]; right; [rewrite E|]; set_solver.
Qed.
Lemma cnext_in hL L x : cnext hL L x ∈ hL :: L.
Proof. unfold cnext. destruct (nxt_in_in hL (hL :: L) x) as [E|H]; [rewrite E; set_solver|done]. Qed.
Lemma cprev_in hL L x : cprev hL L x ∈ hL :: L.
Proof.
  unfold cprev. destruct (lprev_in (llast hL L) (hL :: L) x) as [E|H]; [rewrite E|done].
  destruct (list_snoc_or_nil L) as [->|(L0 & a & ->)]; [set_solver|]. rewrite llast_app_cons. set_solver.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dl_ok (hL : Z) (L : list Z) (ls : LS) : Prop :=
  NoDup (0 :: hL :: L)
  ∧ (∀ a, is_Some (ls !! a) ↔ a ∈ hL :: L)
  ∧ (∀ x nd, x ∈ hL :: L → ls !! x = Some nd → l_next nd = cnext hL L x ∧ l_prev nd = cprev hL L x).

Lemma dl_ok_empty hL : hL ≠ 0 → dl_ok hL [] {[ hL := init_lheader_node hL ]}.
Proof.
  intros H. split_and!.
  - repeat (apply NoDup_cons; split; [set_solver|]). constructor.
  - intros a. destruct (decide (a = hL)) as [->|Hne].
    + rewrite lookup_singleton_eq. split; [set_solver|by eexists].
    + rewrite lookup_singleton_ne by done. split; [by intros [? ?]|set_solver].
  - intros x nd Hx Hnd. assert (x = hL) as -> by set_solver.
    rewrite lookup_singleton_eq in Hnd. injection Hnd as <-. cbn [l_next l_prev init_lheader_node].
    by rewrite cnext_hd, cprev_hd.
Qed.

Section facts.
  Context (hL : Z) (L : list Z) (ls : LS) (OK : dl_ok hL L ls).

  Lemma dl_N : NoDup (0 :: hL :: L).  Proof. exact (proj1 OK). Qed.
  Lemma dl_lookup x : x ∈ hL :: L → ∃ nd, ls !! x = Some nd ∧ l_next nd = cnext hL L x ∧ l_prev nd = cprev hL L x.
  Proof.
    intros Hx. destruct OK as (N & D & F). destruct (proj2 (D x) Hx) as [nd Hnd].
    exists nd. split; [done|]. by apply F.
  Qed.

  (* [comment removed for export] *)
  Lemma dl_next_hd : get_next ls hL = Some (lhead hL L).
  Proof.
    destruct (dl_lookup hL) as (nd & Hnd & Hn & _); [set_solver|].
    unfold get_next, lload. rewrite Hnd. cbn. by rewrite Hn, cnext_hd.
  Qed.
  Lemma dl_prev_hd : get_prev ls hL = Some (llast hL L).
  Proof.
    destruct (dl_lookup hL) as (nd & Hnd & _ & Hp); [set_solver|].
    unfold get_prev, lload. rewrite Hnd. cbn. by rewrite Hp, cprev_hd.
  Qed.
  Lemma dl_next A x B : L = A ++ x :: B → get_next ls x = Some (lhead hL B).
  Proof.
    intros E. destruct (dl_lookup x) as (nd & Hnd & Hn & _); [rewrite E; set_solver|].
    unfold get_next, lload. rewrite Hnd. cbn. rewrite Hn, E. f_equal. apply cnext_at.
    pose proof dl_N as N. rewrite E in N. exact (nd_cons_tl _ _ N).
  Qed.
  Lemma dl_prev A x B : L = A ++ x :: B → get_prev ls x = Some (llast hL A).
  Proof.
    intros E. destruct (dl_lookup x) as (nd & Hnd & _ & Hp); [rewrite E; set_solver|].
    unfold get_prev, lload. rewrite Hnd. cbn. rewrite Hp, E. f_equal. apply cprev_at.
    pose proof dl_N as N. rewrite E in N. exact (nd_cons_tl _ _ N).
  Qed.

  (* [comment removed for export] *)
  Lemma dl_prev_pos A B : L = A ++ B → get_prev ls (lhead hL B) = Some (llast hL A).
  Proof.
    intros E. destruct B as [|b B]; cbn.
    - rewrite app_nil_r in E. subst A. apply dl_prev_hd.
    - by apply (dl_prev A b B).
  Qed.
  Lemma dl_next_pos A B : L = A ++ B → get_next ls (llast hL A) = Some (lhead hL B).
  Proof.
    intros E. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)]; cbn.
    - cbn in E. subst B. apply dl_next_hd.
    - rewrite llast_snoc. apply (dl_next A0 a B). by rewrite E, <-app_assoc.
  Qed.

  (* [comment removed for export] *)
  Lemma iterator_to_spec e : e ∈ L → iterator_to ls e = Some e.
  Proof.
    intros He. destruct (list_elem_of_split _ _ He) as (A & B & E).
    unfold iterator_to. rewrite (dl_next A e B E). cbn.
    rewrite (Zeqb_ne (lhead hL B) 0); [done|].
    pose proof dl_N as N. rewrite E in N. destruct B; cbn; nd_neq_with N.
  Qed.

  Lemma dl_elem_ne0 x : x ∈ hL :: L → x ≠ 0.
  Proof. intros Hx. pose proof dl_N as N. apply NoDup_cons in N as [N _]. intros ->. by apply N. Qed.

  (* [comment removed for export] *)
  Lemma dl_closed x nd : x ∈ hL :: L → ls !! x = Some nd → l_next nd ∈ hL :: L ∧ l_prev nd ∈ hL :: L.
  Proof.
    intros Hx Hnd. destruct (dl_lookup x Hx) as (nd' & Hnd' & Hn & Hp). rewrite Hnd in Hnd'. injection Hnd' as <-.
    rewrite Hn, Hp. split; [apply cnext_in|apply cprev_in].
  Qed.
End facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lload_eq ls a off nd : ls !! a = Some nd → lload ls a off = Some (lget_field off nd).
Proof. intros H. unfold lload. by rewrite H. Qed.
Lemma lstore_eq ls a off v nd : ls !! a = Some nd → lstore ls a off v = Some (<[a := lset_field off v nd]> ls).
Proof. intros H. unfold lstore. by rewrite H. Qed.

(* [comment removed for export] *)
Theorem link_before_ok hL L ls A B this nd0 :
  dl_ok hL L ls → L = A ++ B → this ≠ 0 → this ∉ hL :: L →
  ∃ ls', link_before (<[this := nd0]> ls) (lhead hL B) this = Some ls'
    ∧ dl_ok hL (A ++ this :: B) ls'.
Proof.
  intros OK E Ht0 Hfresh. pose proof (dl_N _ _ _ OK) as N. destruct OK as (_ & D & F).
  set (nxt := lhead hL B). set (prv := llast hL A).
  assert (Hnxt : nxt ∈ hL :: L) by (subst nxt L; destruct B; set_solver).
  assert (Hprv : prv ∈ hL :: L).
  { subst prv L. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)]; [set_solver|]. rewrite llast_snoc. set_solver. }
  assert (Htn : this ≠ nxt) by (intros ->; by apply Hfresh).
  assert (Htp : this ≠ prv) by (intros ->; by apply Hfresh).
  destruct (proj2 (D nxt) Hnxt) as [ndn Hndn]. destruct (proj2 (D prv) Hprv) as [ndp Hndp].
  pose proof (F nxt ndn Hnxt Hndn) as [Hnn Hnp]. pose proof (F prv ndp Hprv Hndp) as [Hpn Hpp].
  assert (Eprv : cprev hL L nxt = prv).
  { subst nxt prv L. destruct B as [|b B]; cbn; [rewrite app_nil_r; apply cprev_hd|apply cprev_at; exact (nd_cons_tl _ _ N)]. }
  unfold link_before, get_prev, set_next, set_prev.
  rewrite (lload_eq (<[this:=nd0]> ls) nxt OFF_PREV ndn) by (by rewrite lookup_insert_ne).
  cbn [mbind option_bind lget_field OFF_PREV OFF_NEXT Z.eqb]. rewrite Hnp, Eprv.
  rewrite (lstore_eq _ this OFF_NEXT nxt nd0) by (by rewrite lookup_insert_eq). cbn [mbind option_bind].
  rewrite insert_insert_eq.
  erewrite (lstore_eq _ this OFF_PREV prv) by (by rewrite lookup_insert_eq). cbn [mbind option_bind].
  rewrite insert_insert_eq. cbn [lset_field OFF_PREV OFF_NEXT Z.eqb l_set_next l_set_prev l_next l_prev].
  erewrite (lstore_eq _ nxt OFF_PREV this) by (rewrite lookup_insert_ne by done; exact Hndn). cbn [mbind option_bind].
  cbn [lset_field OFF_PREV OFF_NEXT Z.eqb l_set_next l_set_prev l_next l_prev].
  (* [comment removed for export] *)
  set (ls3 := <[nxt:=_]> (<[this:=_]> ls)).
  assert (Hp3 : ∃ ndp3, ls3 !! prv = Some ndp3 ∧ l_prev ndp3 = (if decide (prv = nxt) then this else cprev hL L prv)).
  { subst ls3. destruct (decide (prv = nxt)) as [Epn|NE].
    - rewrite Epn. eexists. rewrite lookup_insert_eq. split; [reflexivity|]. done.
    - exists ndp. rewrite !lookup_insert_ne by done. by split. }
  destruct Hp3 as (ndp3 & Hndp3 & Hp3v).
  rewrite (lstore_eq _ prv OFF_NEXT this ndp3 Hndp3). eexists. split; [reflexivity|].
  cbn [lset_field OFF_PREV OFF_NEXT Z.eqb l_set_next l_set_prev l_next l_prev].
  set (ls4 := <[prv:=_]> ls3).
  assert (N' : NoDup (0 :: hL :: A ++ this :: B)).
  { apply (NoDup_insert_mid' _ _ (0 :: hL :: A) B this N); [by rewrite E| |done].
    clear -Hfresh Ht0. set_solver. }
  split_and!.
  - exact N'.
  - intros a. subst ls4 ls3.
    destruct (decide (a = prv)) as [->|?]; [rewrite lookup_insert_eq; split; [intros _|by eexists]|rewrite lookup_insert_ne by done].
    { rewrite E in Hprv. clear -Hprv. set_solver. }
    destruct (decide (a = nxt)) as [->|?]; [rewrite lookup_insert_eq; split; [intros _|by eexists]|rewrite lookup_insert_ne by done].
    { rewrite E in Hnxt. clear -Hnxt. set_solver. }
    destruct (decide (a = this)) as [->|?]; [rewrite lookup_insert_eq; split; [intros _; set_solver|by eexists]|rewrite lookup_insert_ne by done].
    rewrite (D a), E. clear -n n0 n1. set_solver.
  - intros x nd Hx. subst ls4 ls3.
    pose proof (nd_cons_tl _ _ N') as N1.
    destruct (decide (x = prv)) as [->|NEp].
    { rewrite lookup_insert_eq. intros [= <-]. cbn [l_next l_prev l_set_next l_set_prev]. split.
      - symmetry. apply cnext_insert_prv. exact N1.
      - rewrite Hp3v. destruct (decide (prv = nxt)) as [Epn|NE].
        + rewrite Epn. symmetry. apply cprev_insert_nxt. exact N1.
        + rewrite cprev_insert_other; [by rewrite <-E|done|by rewrite <-E|done]. }
    rewrite lookup_insert_ne by done.
    destruct (decide (x = nxt)) as [->|NEn].
    { rewrite lookup_insert_eq. intros [= <-]. cbn [l_next l_prev l_set_next l_set_prev]. split.
      - rewrite Hnn. rewrite cnext_insert_other; [by rewrite E|done|by rewrite <-E|done].
      - symmetry. apply cprev_insert_nxt. exact N1. }
    rewrite lookup_insert_ne by done.
    destruct (decide (x = this)) as [->|NEt].
    { rewrite lookup_insert_eq. intros [= <-]. cbn [l_next l_prev l_set_next l_set_prev]. split.
      - symmetry. apply cnext_at. exact N1.
      - symmetry. apply cprev_at. exact N1. }
    rewrite lookup_insert_ne by done. intros Hnd.
    assert (Hx' : x ∈ hL :: L) by (rewrite E; clear -Hx NEt; set_solver).
    destruct (F x nd Hx' Hnd) as [-> ->]. rewrite E. split.
    + symmetry. apply cnext_insert_other; [done|by rewrite <-E|done].
    + symmetry. apply cprev_insert_other; [done|by rewrite <-E|done].
Qed.

Corollary push_back_ok hL L ls this nd0 :
  dl_ok hL L ls → this ≠ 0 → this ∉ hL :: L →
  ∃ ls', push_back (<[this := nd0]> ls) hL this = Some ls' ∧ dl_ok hL (L ++ [this]) ls'.
Proof.
  intros OK Ht0 Hf. unfold push_back.
  destruct (link_before_ok hL L ls L [] this nd0 OK) as (ls' & H & OK'); [by rewrite app_nil_r|done|done|].
  exists ls'. by split.
Qed.

(* [comment removed for export] *)
Corollary link_after_last_ok hL L ls A last B this nd0 :
  dl_ok hL L ls → L = A ++ last :: B → this ≠ 0 → this ∉ hL :: L →
  ∃ ls', (it ← iterator_to (<[this := nd0]> ls) last ;
          nxt ← iter_next (<[this := nd0]> ls) it ;
          link_before (<[this := nd0]> ls) nxt this) = Some ls'
    ∧ dl_ok hL (A ++ last :: this :: B) ls'.
Proof.
  intros OK E Ht0 Hf.
  assert (Hlt : last ≠ this) by (intros ->; apply Hf; rewrite E; set_solver).
  assert (IT : iterator_to (<[this:=nd0]> ls) last = Some last).
  { unfold iterator_to, get_next, lload in *. rewrite lookup_insert_ne by done.
    pose proof (iterator_to_spec hL L ls OK last) as X. unfold iterator_to, get_next, lload in X.
    apply X. rewrite E. set_solver. }
  rewrite IT. cbn [mbind option_bind].
  assert (NX : iter_next (<[this:=nd0]> ls) last = Some (lhead hL B)).
  { unfold iter_next, get_next, lload. rewrite lookup_insert_ne by done.
    pose proof (dl_next hL L ls OK A last B E) as X. unfold get_next, lload in X. exact X. }
  rewrite NX. cbn [mbind option_bind].
  destruct (link_before_ok hL L ls (A ++ [last]) B this nd0 OK) as (ls' & H & OK'); [by rewrite E, <-app_assoc|done|done|].
  exists ls'. rewrite <-app_assoc in OK'. by split.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem unlink_ok hL L ls A x B :
  dl_ok hL L ls → L = A ++ x :: B →
  ∃ ls', unlink ls x = Some (ls', lhead hL B) ∧ dl_ok hL (A ++ B) (delete x ls').
Proof.
  intros OK E. pose proof (dl_N _ _ _ OK) as N. destruct OK as (_ & D & F).
  set (nxt := lhead hL B). set (prv := llast hL A).
  assert (Hx : x ∈ hL :: L) by (rewrite E; set_solver).
  assert (Hnxt : nxt ∈ hL :: A ++ B) by (subst nxt; destruct B; set_solver).
  assert (Hprv : prv ∈ hL :: A ++ B).
  { subst prv. destruct (list_snoc_or_nil A) as [->|(A0 & a & ->)]; [set_solver|]. rewrite llast_snoc. set_solver. }
  rewrite E in N.
  assert (Hxn : x ≠ nxt) by (subst nxt; destruct B; cbn; nd_neq_with N).
  assert (Hxp : x ≠ prv).
  { subst prv. destruct (list_snoc_or_nil A) as [EA|(A0 & a & EA)]; rewrite EA in N |- *; cbn; [nd_neq_with N|].
    rewrite llast_snoc. rewrite <-app_assoc in N. nd_neq_with N. }
  rewrite <-E in N.
  destruct (proj2 (D x) Hx) as [ndx Hndx]. pose proof (F x ndx Hx Hndx) as [Hxn' Hxp'].
  rewrite E in Hxn', Hxp'. rewrite cnext_at in Hxn' by (rewrite <-E; exact (nd_cons_tl _ _ N)).
  rewrite cprev_at in Hxp' by (rewrite <-E; exact (nd_cons_tl _ _ N)).
  assert (Hnxt' : nxt ∈ hL :: L) by (rewrite E; clear -Hnxt; set_solver).
  assert (Hprv' : prv ∈ hL :: L) by (rewrite E; clear -Hprv; set_solver).
  destruct (proj2 (D nxt) Hnxt') as [ndn Hndn]. destruct (proj2 (D prv) Hprv') as [ndp Hndp].
  unfold unlink, get_next, get_prev, set_next, set_prev.
  rewrite (lload_eq _ _ _ _ Hndx), (lload_eq _ _ _ _ Hndx). cbn [mbind option_bind lget_field OFF_PREV OFF_NEXT Z.eqb].
  rewrite Hxn', Hxp'. fold nxt prv.
  rewrite (lstore_eq _ _ _ _ _ Hndp). cbn [mbind option_bind].
  assert (Hn1 : ∃ ndn1, <[prv:=lset_field OFF_NEXT nxt ndp]> ls !! nxt = Some ndn1
                 ∧ l_next ndn1 = (if decide (nxt = prv) then nxt else cnext hL L nxt)).
  { destruct (decide (nxt = prv)) as [Enp|NE].
    - rewrite <-Enp. eexists. rewrite lookup_insert_eq. split; [reflexivity|]. done.
    - exists ndn. rewrite lookup_insert_ne by done. split; [done|]. by apply (F nxt). }
  destruct Hn1 as (ndn1 & Hndn1 & Hn1v).
  rewrite (lstore_eq _ _ _ _ _ Hndn1). cbn [mbind option_bind]. eexists. split; [reflexivity|].
  cbn [lset_field OFF_PREV OFF_NEXT Z.eqb l_set_next l_set_prev l_next l_prev].
  pose proof (NoDup_remove_mid (0 :: hL :: A) B x) as N'. cbn in N'. specialize (N' ltac:(by rewrite <-E)).
  split_and!.
  - exact N'.
  - intros a. destruct (decide (a = x)) as [->|NEx].
    { rewrite lookup_delete_eq. split; [by intros [? ?]|]. intros Ha. exfalso.
      rewrite E in N. apply (neq_irrefl_False x).
      apply elem_of_cons in Ha as [->|Ha]; [nd_neq_with N|].
      apply elem_of_app in Ha as [Ha|Ha]; nd_neq_with N. }
    rewrite lookup_delete_ne by done.
    destruct (decide (a = nxt)) as [->|?]; [rewrite lookup_insert_eq; split; [done|by eexists]|rewrite lookup_insert_ne by done].
    destruct (decide (a = prv)) as [->|?]; [rewrite lookup_insert_eq; split; [done|by eexists]|rewrite lookup_insert_ne by done].
    rewrite (D a), E. clear -NEx. set_solver.
  - intros y nd Hy. destruct (decide (y = x)) as [->|NEx].
    { exfalso. rewrite E in N. apply (neq_irrefl_False x).
      apply elem_of_cons in Hy as [->|Hy]; [nd_neq_with N|].
      apply elem_of_app in Hy as [Hy|Hy]; nd_neq_with N. }
    rewrite lookup_delete_ne by done.
    assert (Hy' : y ∈ hL :: L) by (rewrite E; clear -Hy; set_solver).
    pose proof (nd_cons_tl _ _ N) as N1. rewrite E in N1. pose proof (nd_cons_tl _ _ N') as N1'.
    destruct (decide (y = nxt)) as [->|NEn].
    { rewrite lookup_insert_eq. intros [= <-]. cbn [l_next l_prev l_set_next l_set_prev]. split.
      - rewrite Hn1v. destruct (decide (nxt = prv)) as [Enp|NE].
        + destruct (nxt_eq_prv hL A B N1' Enp) as [-> ->]. subst nxt. cbn [lhead app]. by rewrite cnext_hd.
        + rewrite E. apply cnext_insert_other; [done|done|done].
      - subst prv nxt. symmetry. by apply cprev_pos. }
    rewrite lookup_insert_ne by done.
    destruct (decide (y = prv)) as [->|NEp].
    { rewrite lookup_insert_eq. intros [= <-]. cbn [l_next l_prev l_set_next l_set_prev]. split.
      - subst prv nxt. symmetry. by apply cnext_pos.
      - destruct (F prv ndp Hprv' Hndp) as [_ ->]. rewrite E. apply cprev_insert_other; [done|done|done]. }
    rewrite lookup_insert_ne by done. intros Hnd.
    destruct (F y nd Hy' Hnd) as [-> ->]. rewrite E. split.
    + apply cnext_insert_other; [done|done|done].
    + apply cprev_insert_other; [done|done|done].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem iterate_spec hL L ls fuel :
  dl_ok hL L ls → (length L < fuel)%nat → iterate fuel ls hL = Some L.
Proof.
  intros OK Hf. pose proof (dl_N _ _ _ OK) as N. unfold iterate.
  rewrite (dl_next_hd hL L ls OK). cbn [mbind option_bind].
  destruct (oloop_inv (iter_step ls hL)
              (λ st, ∃ R, L = rev (snd st) ++ R ∧ fst st = lhead hL R)
              (λ r, r = L)
              (λ st, length L - length (snd st))%nat) with (n := fuel) (x := (lhead hL L, @nil Z))
    as (r & -> & ->); [|by exists L|cbn; lia|done].
  intros [it acc] (R & EL & Eit). cbn [fst snd] in *. unfold iter_step.
  destruct R as [|r R].
  - cbn in Eit. subst it. rewrite Z.eqb_refl. eexists. split; [reflexivity|]. cbn.
    by rewrite EL, app_nil_r.
  - cbn in Eit. subst it. rewrite (Zeqb_ne r hL) by (rewrite EL in N; nd_neq_with N).
    rewrite (dl_next hL L ls OK (rev acc) r R EL). cbn [mbind option_bind].
    eexists. split; [reflexivity|]. cbn [fst snd]. split.
    + exists R. split; [|done]. cbn. by rewrite <-app_assoc.
    + assert (length (rev acc ++ r :: R) = length L) by (by rewrite <-EL).
      rewrite length_app in H. cbn in H |- *. rewrite length_rev in H. lia.
Qed.
