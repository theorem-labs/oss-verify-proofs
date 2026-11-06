(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_List.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition q_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition q_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => q_link st0 g head
  | None => q_single st0 h g
  end.

#[using="Type"] Lemma queue_eq {R} h g st0 (k : mstate -> M R) bail :
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (queue_st h g st0).
Proof.
  intros Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold queue_st, q_link, q_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition fm_st (st : mstate) (g : aptr) : mstate := queue_st LFree g (put_meta g meta0 st).

#[using="Type"] Lemma free_meta_eq {R} st g (k : mstate -> M R) bail : free_meta g st k bail = k (fm_st st g).
Proof. unfold free_meta, fm_st. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity. Qed.

(* [comment removed for export] *)
Definition data_of (r : meta) : meta := m_set_prev None (m_set_next None r).

#[using="Type"] Lemma data_of_eq r r' :
  data_of r = data_of r' <->
  (m_mem r = m_mem r' /\ m_avail r = m_avail r' /\ m_freed r = m_freed r' /\ m_last_idx r = m_last_idx r'
   /\ m_freeable r = m_freeable r' /\ m_sizeclass r = m_sizeclass r' /\ m_maplen r = m_maplen r').
Proof.
  destruct r, r'; unfold data_of; cbn; split.
  - intros H. inversion H. repeat split; reflexivity.
  - intros (-> & -> & -> & -> & -> & -> & ->). reflexivity.
Qed.

#[using="Type"] Lemma data_of_set_prev v r : data_of (m_set_prev v r) = data_of r. Proof. reflexivity. Qed.
#[using="Type"] Lemma data_of_set_next v r : data_of (m_set_next v r) = data_of r. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_stride_data r r' : data_of r = data_of r' -> get_stride r = get_stride r'.
Proof. intros H. apply data_of_eq in H. unfold get_stride. destruct H as (_ & _ & _ & -> & _ & -> & ->). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LINKED.
Variable st : mstate.
Local Notation R := (MR st).

#[using="Type"] Lemma linked_cons2 x y t : linked st (x :: y :: t) <-> m_next (R x) = Some y /\ m_prev (R y) = Some x /\ linked st (y :: t).
Proof. cbn. tauto. Qed.

#[using="Type"] Lemma linked_app x l1 l2 : linked st (l1 ++ x :: l2) <-> linked st (l1 ++ [x]) /\ linked st (x :: l2).
Proof.
  induction l1 as [|a l1 IH]; cbn.
  - tauto.
  - destruct l1 as [|b l1']; cbn in *.
    + tauto.
    + rewrite IH. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma linked_next l : linked st l -> forall k x y, nth_error l k = Some x -> nth_error l (S k) = Some y -> m_next (R x) = Some y /\ m_prev (R y) = Some x.
Proof.
  induction l as [|a l IH]; intros Hl k x y Hx Hy; [destruct k; discriminate|].
  destruct l as [|b l']; [destruct k; cbn in Hy; [discriminate| destruct k; discriminate]|].
  destruct Hl as (Hn & Hp & Hl'). destruct k as [|k]; cbn in Hx, Hy.
  - inversion Hx; inversion Hy; subst. auto.
  - eapply IH; eauto.
Qed.

#[using="Type"] Lemma linked_In_next l x : linked st l -> In x (removelast l) -> exists y, In y l /\ m_next (R x) = Some y /\ m_prev (R y) = Some x.
Proof.
  induction l as [|a l IH]; intros Hl Hin; [destruct Hin|].
  destruct l as [|b l']; [destruct Hin|].
  destruct Hl as (Hn & Hp & Hl'). cbn [removelast] in Hin. destruct Hin as [<-|Hin].
  - exists b. cbn. auto.
  - destruct (IH Hl' Hin) as (y & Hy & H1 & H2). exists y. split; [right; exact Hy| auto].
Qed.
End LINKED.

(* [comment removed for export] *)
#[using="Type"] Lemma linked_ext st st' l :
  (forall x, In x (removelast l) -> m_next (MR st' x) = m_next (MR st x)) ->
  (forall x, In x (tl l) -> m_prev (MR st' x) = m_prev (MR st x)) ->
  linked st l -> linked st' l.
Proof.
  induction l as [|a l IH]; intros Hn Hp Hl; [exact I|].
  destruct l as [|b l']; [exact I|].
  destruct Hl as (H1 & H2 & Hl'). cbn [linked]. split; [|split].
  - rewrite Hn; [exact H1|]. cbn. destruct l'; [left; reflexivity| left; reflexivity].
  - rewrite Hp; [exact H2|]. left. reflexivity.
  - apply IH; [| | exact Hl'].
    + intros x Hx. apply Hn. cbn [removelast]. destruct l' as [|c l'']; [destruct Hx| right; exact Hx].
    + intros x Hx. apply Hp. right. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record lists_ok (st : mstate) (LS : lhead -> list aptr) : Prop := mkLO {
  lo_head : forall h, get_head st h = head_of (LS h);
  lo_dll : forall h, dll st (LS h);
  lo_nodup : forall h, NoDup (LS h);
  lo_disj : forall h1 h2 m, In m (LS h1) -> In m (LS h2) -> h1 = h2;
  lo_link : forall m, ((exists h, In m (LS h)) <-> m_next (MR st m) <> None)
                      /\ (m_next (MR st m) = None -> m_prev (MR st m) = None)
}.
End WithCeil.


#[export] Instance lhead_eq_dec : EqDecision lhead.
Proof. intros [a|] [b|]; try (right; discriminate); try (left; reflexivity).
  destruct (decide (a = b)) as [->|NE]; [left; reflexivity| right; congruence]. Defined.
Section WithCeil.
Context {CE : CEIL}.

Definition fupd (LS : lhead -> list aptr) (h : lhead) (l : list aptr) : lhead -> list aptr :=
  fun h' => if decide (h' = h) then l else LS h'.

#[using="Type"] Lemma fupd_eq LS h l : fupd LS h l h = l.
Proof. unfold fupd. destruct (decide (h = h)); [reflexivity| congruence]. Qed.
#[using="Type"] Lemma fupd_ne LS h l h' : h' <> h -> fupd LS h l h' = LS h'.
Proof. intros NE. unfold fupd. destruct (decide (h' = h)); [congruence| reflexivity]. Qed.

(* [comment removed for export] *)
Section FACTS.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.
Local Notation R := (MR st).

#[using="LO"] Lemma lists_next_in h x : In x (LS h) -> exists y, In y (LS h) /\ m_next (R x) = Some y /\ m_prev (R y) = Some x.
Proof.
  intros Hin. pose proof (lo_dll _ _ LO h) as D. destruct (LS h) as [|a l] eqn:E; [destruct Hin|].
  cbn [dll] in D. destruct (linked_In_next st _ x D) as (y & Hy & H1 & H2).
  - rewrite removelast_app by discriminate. cbn. rewrite app_nil_r. exact Hin.
  - exists y. split; [|auto]. apply in_app_iff in Hy. destruct Hy as [Hy|[<-|[]]]; [exact Hy| left; reflexivity].
Qed.

#[using="LO"] Lemma lists_prev_in h x : In x (LS h) -> exists y, In y (LS h) /\ m_prev (R x) = Some y /\ m_next (R y) = Some x.
Proof.
  intros Hin. pose proof (lo_dll _ _ LO h) as D. destruct (LS h) as [|a l] eqn:E; [destruct Hin|].
  cbn [dll app] in D.
  (* [comment removed for export] *)
  assert (H : forall l1 l2, a :: l ++ [a] = l1 ++ x :: l2 -> l1 <> [] -> exists y, In y (a :: l) /\ m_prev (R x) = Some y /\ m_next (R y) = Some x).
  { intros l1 l2 Heq Hne. destruct (@exists_last _ l1 Hne) as (l0 & y & ->).
    rewrite <- app_assoc in Heq. cbn in Heq. rewrite Heq in D.
    apply linked_app in D as [_ D]. destruct D as (H1 & H2 & _). exists y. split; [|auto].
    assert (Hy : In y (a :: l ++ [a])) by (rewrite Heq; apply in_app_iff; right; left; reflexivity).
    cbn in Hy. destruct Hy as [<-|Hy]; [left; reflexivity|]. apply in_app_iff in Hy. destruct Hy as [Hy|[<-|[]]]; [right; exact Hy| left; reflexivity]. }
  destruct Hin as [Exa|Hin].
  - subst x. apply (H (a :: l) []); [| discriminate]. cbn. reflexivity.
  - destruct (in_split _ _ Hin) as (l1 & l2 & ->). apply (H (a :: l1) (l2 ++ [a])). { cbn. rewrite <- app_assoc. reflexivity. } discriminate.
Qed.

#[using="LO"] Lemma lists_in_next_some h x : In x (LS h) -> m_next (R x) <> None.
Proof. intros Hin. destruct (lists_next_in h x Hin) as (y & _ & -> & _). discriminate. Qed.

#[using="LO"] Lemma lists_notin m : m_next (R m) = None -> forall h, ~ In m (LS h).
Proof. intros Hn h Hin. exact (lists_in_next_some h m Hin Hn). Qed.

#[using="LO"] Lemma lists_head_prev h a l : LS h = a :: l -> m_prev (R a) = Some (List.last l a) /\ m_next (R (List.last l a)) = Some a.
Proof.
  intros E. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D.
  destruct l as [|b l'].
  - cbn in D |- *. tauto.
  - destruct (@exists_last _ (b :: l') ltac:(discriminate)) as (l0 & y & Ey). rewrite Ey in D |- *.
    rewrite last_last.
    replace ((a :: l0 ++ [y]) ++ [a]) with ((a :: l0) ++ y :: [a]) in D by (cbn; rewrite <- app_assoc; reflexivity).
    apply (linked_app st y (a :: l0) [a]) in D as [_ D]. cbn in D. tauto.
Qed.

#[using="LO"] Lemma lists_singleton h a l : LS h = a :: l -> (m_next (R a) = Some a <-> l = []).
Proof.
  intros E. split.
  - intros Hn. destruct l as [|b l']; [reflexivity|]. exfalso.
    pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll app] in D. destruct D as (H1 & _). rewrite Hn in H1. inversion H1; subst.
    pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND. apply NoDup_cons in ND as [NI _]. apply NI. apply list_elem_of_In. left. congruence.
  - intros ->. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn in D. tauto.
Qed.
End FACTS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

(* [comment removed for export] *)
Section DEQUEUE.
Variables (h : lhead) (m : aptr) (st : mstate).
Let mr := MR st m.
Let st' := dequeue h m st.

(* [comment removed for export] *)
Let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end.
Let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end.
Let st3 := if negb (optr_eqb (m_next mr) (Some m))
           then (if optr_eqb (get_head st2 h) (Some m) then set_head h (m_next mr) st2 else st2)
           else set_head h None st.

#[using="Type"] Lemma dequeue_unfold : st' = upd_meta m (fun r => m_set_prev None (m_set_next None r)) st3.
Proof. reflexivity. Qed.

#[using="h"] Lemma st1_R x : MR st1 x = if optr_eqb (m_prev mr) (Some x) then m_set_next (m_next mr) (MR st x) else MR st x.
Proof.
  subst st1. unfold MR. destruct (m_prev mr) as [p|]; cbn [optr_eqb]; [|reflexivity].
  rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x p) as [E|NE]; destruct (aptr_eqb_spec p x) as [E2|NE2]; subst; try reflexivity; congruence.
Qed.

#[using="h"] Lemma st2_R x : MR st2 x = if optr_eqb (m_next mr) (Some x) then m_set_prev (m_prev mr) (MR st1 x) else MR st1 x.
Proof.
  subst st2. unfold MR. destruct (m_next mr) as [q|]; cbn [optr_eqb]; [|reflexivity].
  rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x q) as [E|NE]; destruct (aptr_eqb_spec q x) as [E2|NE2]; subst; try reflexivity; congruence.
Qed.

#[using="Type"] Lemma st3_R x : MR st3 x = if optr_eqb (m_next mr) (Some m) then MR st x else MR st2 x.
Proof.
  subst st3. unfold MR. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
  - rewrite get_meta_rec_set_head. reflexivity.
  - destruct (optr_eqb (get_head st2 h) (Some m)); rewrite ?get_meta_rec_set_head; reflexivity.
Qed.

#[using="mr st1 st2 st3"] Lemma dequeue_data x : data_of (MR st' x) = data_of (MR st x).
Proof.
  rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
  assert (D3 : forall y, data_of (MR st3 y) = data_of (MR st y)).
  { intros y. rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
    rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some y)); destruct (optr_eqb (m_prev mr) (Some y)); reflexivity. }
  destruct (aptr_eqb_spec x m) as [->|NE]; [|apply D3].
  rewrite data_of_set_prev, data_of_set_next. apply D3.
Qed.

#[using="st1 st2 st3"] Lemma dequeue_next x : m_next (MR st' x) =
  if aptr_eqb x m then None
  else if optr_eqb (m_next mr) (Some m) then m_next (MR st x)
  else if optr_eqb (m_prev mr) (Some x) then m_next mr else m_next (MR st x).
Proof.
  rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
  destruct (aptr_eqb_spec x m) as [->|NE]; [reflexivity|].
  rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
  rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some x)); destruct (optr_eqb (m_prev mr) (Some x)); reflexivity.
Qed.

#[using="st1 st2 st3"] Lemma dequeue_prev x : m_prev (MR st' x) =
  if aptr_eqb x m then None
  else if optr_eqb (m_next mr) (Some m) then m_prev (MR st x)
  else if optr_eqb (m_next mr) (Some x) then m_prev mr else m_prev (MR st x).
Proof.
  rewrite dequeue_unfold. unfold MR at 1. rewrite get_meta_rec_upd. fold (MR st3 x). fold (MR st3 m).
  destruct (aptr_eqb_spec x m) as [->|NE]; [reflexivity|].
  rewrite st3_R. destruct (optr_eqb (m_next mr) (Some m)); [reflexivity|].
  rewrite st2_R, st1_R. destruct (optr_eqb (m_next mr) (Some x)); destruct (optr_eqb (m_prev mr) (Some x)); reflexivity.
Qed.

#[using="h"] Lemma get_head_st2 h' : get_head st2 h' = get_head st h'.
Proof.
  subst st2 st1. destruct (m_next mr); destruct (m_prev mr); rewrite ?get_head_upd_meta; reflexivity.
Qed.

#[using="st1 st2 st3"] Lemma dequeue_head h' : get_head st' h' =
  if decide (h' = h) then
    (if optr_eqb (m_next mr) (Some m) then None
     else if optr_eqb (get_head st h) (Some m) then m_next mr else get_head st h)
  else get_head st h'.
Proof.
  rewrite dequeue_unfold. rewrite get_head_upd_meta. subst st3.
  destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
  - destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head| apply get_head_set_head_other; exact NE].
  - rewrite get_head_st2. destruct (optr_eqb (get_head st h) (Some m)).
    + destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head| rewrite get_head_set_head_other by exact NE; apply get_head_st2].
    + destruct (decide (h' = h)) as [->|NE]; apply get_head_st2.
Qed.

#[using="Type"] Lemma set_head_metas hh v s : s_metas (set_head hh v s) = s_metas s.
Proof. destruct hh; reflexivity. Qed.

#[using="st1 st2 st3"] Lemma dequeue_keys x : s_metas st' !! x <> None ->
  s_metas st !! x <> None \/ x = m \/ m_prev mr = Some x \/ m_next mr = Some x.
Proof.
  rewrite dequeue_unfold. rewrite lookup_metas_upd.
  destruct (aptr_eqb_spec x m) as [->|NE]; [intros _; right; left; reflexivity|].
  subst st3 st2 st1. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
  - rewrite set_head_metas. auto.
  - match goal with |- context [s_metas (if ?c then _ else _)] => destruct c end; rewrite ?set_head_metas.
    all: destruct (m_next mr) as [q|]; destruct (m_prev mr) as [p'|]; rewrite ?lookup_metas_upd;
      repeat match goal with |- context [if aptr_eqb ?a ?y then _ else _] => destruct (aptr_eqb_spec a y) as [<-|?] end; auto.
Qed.

#[using="mr st1 st2 st3"] Lemma dequeue_keys_mono x : s_metas st !! x <> None -> s_metas st' !! x <> None.
Proof.
  rewrite dequeue_unfold. rewrite lookup_metas_upd.
  destruct (aptr_eqb_spec x m) as [->|NE]; [intros _; discriminate|].
  subst st3 st2 st1. destruct (optr_eqb (m_next mr) (Some m)); cbn [negb].
  - rewrite set_head_metas. auto.
  - match goal with |- context [s_metas (if ?c then _ else _)] => destruct c end; rewrite ?set_head_metas.
    all: destruct (m_next mr) as [q|]; destruct (m_prev mr) as [p'|]; rewrite ?lookup_metas_upd;
      repeat match goal with |- context [if aptr_eqb ?a ?y then _ else _] => destruct (aptr_eqb_spec a y) as [<-|?] end; auto; intros; discriminate.
Qed.

#[using="mr st1 st2 st3"] Lemma dequeue_key_m : s_metas st' !! m <> None.
Proof. rewrite dequeue_unfold, lookup_metas_upd, aptr_eqb_refl. discriminate. Qed.
End DEQUEUE.


(* [comment removed for export] *)
Section QUEUE.
Variables (h : lhead) (g : aptr) (st : mstate).
Let st' := queue_st h g st.

#[using="Type"] Lemma data_upd_links s m f x : (forall r, data_of (f r) = data_of r) -> data_of (MR (upd_meta m f s) x) = data_of (MR s x).
Proof. intros Hf. unfold MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m) as [->|NE]; [apply Hf| reflexivity]. Qed.

#[using="Type"] Lemma queue_data x : data_of (MR st' x) = data_of (MR st x).
Proof.
  subst st'. unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|].
  - rewrite data_upd_links by (intros; reflexivity).
    destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?data_upd_links by (intros; reflexivity); reflexivity.
  - unfold MR. rewrite get_meta_rec_set_head. fold (MR (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st) x). fold (MR st x).
    apply data_upd_links. intros; reflexivity.
Qed.

#[using="Type"] Lemma queue_next x : m_next (MR st' x) =
  match get_head st h with
  | Some a => if aptr_eqb x a then (if optr_eqb (m_prev (MR st a)) (Some a) then Some g else if aptr_eqb a g then Some a else m_next (MR st a))
              else if optr_eqb (m_prev (MR st a)) (Some x) then Some g
              else if aptr_eqb x g then Some a else m_next (MR st x)
  | None => if aptr_eqb x g then Some g else m_next (MR st x)
  end.
Proof.
  subst st'. unfold queue_st, q_link, q_single, MR.
  destruct (get_head st h) as [a|].
  - rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x a) as [->|NE].
    + cbn [m_next m_set_prev]. destruct (m_prev (get_meta_rec st a)) as [z|]; cbn [optr_eqb].
      * rewrite get_meta_rec_upd. destruct (aptr_eqb_spec a z) as [<-|NEz]; rewrite ?aptr_eqb_refl; [reflexivity|].
        rewrite (aptr_eqb_neq z a) by congruence. rewrite get_meta_rec_upd. destruct (aptr_eqb a g); reflexivity.
      * rewrite get_meta_rec_upd. destruct (aptr_eqb a g); reflexivity.
    + destruct (m_prev (get_meta_rec st a)) as [z|]; cbn [optr_eqb].
      * rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x z) as [<-|NEz].
        -- rewrite aptr_eqb_refl. reflexivity.
        -- rewrite (aptr_eqb_neq z x) by congruence. rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
      * rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
  - rewrite get_meta_rec_set_head, get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
Qed.

#[using="Type"] Lemma queue_prev x : m_prev (MR st' x) =
  match get_head st h with
  | Some a => if aptr_eqb x a then Some g
              else if aptr_eqb x g then m_prev (MR st a)
              else m_prev (MR st x)
  | None => if aptr_eqb x g then Some g else m_prev (MR st x)
  end.
Proof.
  subst st'. unfold queue_st, q_link, q_single, MR.
  destruct (get_head st h) as [a|].
  - rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x a) as [->|NE]; [reflexivity|].
    destruct (m_prev (get_meta_rec st a)) as [z|].
    + rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x z) as [<-|NEz].
      * cbn [m_prev m_set_next]. rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
      * rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
    + rewrite get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
  - rewrite get_meta_rec_set_head, get_meta_rec_upd. destruct (aptr_eqb x g); reflexivity.
Qed.

#[using="Type"] Lemma queue_head h' : get_head st' h' =
  if decide (h' = h) then match get_head st h with Some a => Some a | None => Some g end else get_head st h'.
Proof.
  subst st'. unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|] eqn:E.
  - destruct (m_prev (get_meta_rec st a)); rewrite ?get_head_upd_meta; destruct (decide (h' = h)) as [->|]; rewrite ?E; reflexivity.
  - destruct (decide (h' = h)) as [->|NE]; [apply get_head_set_head|]. rewrite get_head_set_head_other by exact NE. apply get_head_upd_meta.
Qed.

#[using="Type"] Lemma queue_keys x : s_metas st' !! x <> None ->
  s_metas st !! x <> None \/ x = g \/ get_head st h = Some x \/ (exists a, get_head st h = Some a /\ m_prev (MR st a) = Some x).
Proof.
  subst st'. unfold queue_st, q_link, q_single, MR.
  destruct (get_head st h) as [a|].
  - rewrite lookup_metas_upd. destruct (aptr_eqb_spec x a) as [->|NE]; [intros _; right; right; left; reflexivity|].
    destruct (m_prev (get_meta_rec st a)) as [z|] eqn:Ez; rewrite ?lookup_metas_upd.
    + destruct (aptr_eqb_spec x z) as [->|NEz]; [intros _; right; right; right; exists a; auto|].
      destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
    + destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
  - rewrite set_head_metas, lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NEg]; auto.
Qed.

#[using="Type"] Lemma queue_keys_mono x : s_metas st !! x <> None -> s_metas st' !! x <> None.
Proof.
  subst st'. unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|].
  - rewrite lookup_metas_upd. destruct (aptr_eqb x a); [intros; discriminate|].
    destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?lookup_metas_upd; [destruct (aptr_eqb x z); [intros; discriminate|]|];
      destruct (aptr_eqb x g); auto; intros; discriminate.
  - rewrite set_head_metas, lookup_metas_upd. destruct (aptr_eqb x g); auto; intros; discriminate.
Qed.

#[using="Type"] Lemma queue_key_g : s_metas st' !! g <> None.
Proof.
  subst st'. unfold queue_st, q_link, q_single.
  destruct (get_head st h) as [a|].
  - rewrite lookup_metas_upd. destruct (aptr_eqb g a); [discriminate|].
    destruct (m_prev (get_meta_rec st a)) as [z|]; rewrite ?lookup_metas_upd; [destruct (aptr_eqb g z); [discriminate|]|];
      rewrite aptr_eqb_refl; discriminate.
  - rewrite set_head_metas, lookup_metas_upd, aptr_eqb_refl. discriminate.
Qed.
End QUEUE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma In_removelast {A} (x : A) l : In x (removelast l) -> In x l.
Proof.
  induction l as [|a l IH]; cbn; [tauto|]. destruct l as [|b l']; [cbn; tauto|].
  intros [<-|H]; [left; reflexivity| right; apply IH; exact H].
Qed.
#[using="Type"] Lemma In_tl {A} (x : A) l : In x (tl l) -> In x l.
Proof. destruct l; cbn; tauto. Qed.

#[using="Type"] Lemma NoDup_app_In {A} (l1 l2 : list A) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros ND H1 H2. apply NoDup_app in ND as (_ & D & _). apply (D x); apply list_elem_of_In; assumption.
Qed.
#[using="Type"] Lemma NoDup_In_split {A} (l1 l2 : list A) x : NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros ND. apply NoDup_app in ND as (_ & D & ND2). apply NoDup_cons in ND2 as [N2 _]. split.
  - intros H. apply (D x); [apply list_elem_of_In; exact H| left].
  - intros H. apply N2. apply list_elem_of_In. exact H.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma linked_snoc st l x y : linked st (l ++ [x]) -> m_next (MR st x) = Some y -> m_prev (MR st y) = Some x -> linked st (l ++ [x; y]).
Proof. intros Hl Hn Hp. apply (linked_app st x l [y]). split; [exact Hl|]. cbn. auto. Qed.

#[using="Type"] Lemma linked_prefix st l x y t : linked st (l ++ x :: y :: t) -> linked st (l ++ [x]) /\ m_next (MR st x) = Some y /\ m_prev (MR st y) = Some x.
Proof. intros H. apply linked_app in H as [H1 H2]. cbn in H2. tauto. Qed.

#[using="Type"] Lemma last_In {A} (l : list A) d : In (List.last l d) (d :: l).
Proof.
  induction l as [|a l IH]; [left; reflexivity|].
  cbn [List.last]. destruct l as [|b l']; [right; left; reflexivity|].
  cbn in IH |- *. destruct IH as [IH|IH]; [left; exact IH| right; right; exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma dll_rot1 st a r : linked st (a :: r ++ [a]) -> dll st (r ++ [a]).
Proof.
  intros D. destruct r as [|b r']; cbn [dll app]; [exact D|].
  cbn [app] in D. destruct D as (D1 & D2 & D3). rewrite <- app_assoc. cbn [app].
  apply (linked_snoc st (b :: r') a b); assumption.
Qed.

#[using="Type"] Lemma dll_rot st l1 l2 : dll st (l1 ++ l2) -> dll st (l2 ++ l1).
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 D.
  - rewrite app_nil_r. exact D.
  - replace (l2 ++ a :: l1) with ((l2 ++ [a]) ++ l1) by (rewrite <- app_assoc; reflexivity).
    apply IH. rewrite app_assoc. apply dll_rot1. cbn [app dll] in D. exact D.
Qed.

#[using="Type"] Lemma dll_linked st a r : dll st (a :: r) -> linked st (a :: r).
Proof.
  intros D. cbn [dll app] in D. change (a :: r ++ [a]) with ((a :: r) ++ [a]) in D.
  destruct (@exists_last _ (a :: r) ltac:(discriminate)) as (l0 & z & Ez). rewrite Ez in D |- *.
  rewrite <- app_assoc in D. cbn [app] in D. apply linked_prefix in D. tauto.
Qed.

#[using="Type"] Lemma last_In' {A} (l : list A) d : l <> [] -> In (List.last l d) l.
Proof.
  induction l as [|a l IH]; intros H; [congruence|].
  destruct l as [|b l']; [left; reflexivity|]. right. apply IH. discriminate.
Qed.

#[using="Type"] Lemma last_cons_eq {A} (a : A) r d : r <> [] -> List.last (a :: r) d = List.last r d.
Proof. intros H. destruct r; [congruence| reflexivity]. Qed.

#[using="Type"] Lemma dll_ends st a r : dll st (a :: r) ->
  let q := match r with [] => a | b :: _ => b end in
  let p := List.last r a in
  m_next (MR st a) = Some q /\ m_prev (MR st q) = Some a /\ m_next (MR st p) = Some a /\ m_prev (MR st a) = Some p
  /\ linked st (a :: r).
Proof.
  intros D. cbn [dll app] in D. cbn zeta.
  assert (H1 : m_next (MR st a) = Some match r with [] => a | b :: _ => b end /\ m_prev (MR st match r with [] => a | b :: _ => b end) = Some a).
  { destruct r as [|b r']; cbn in D; tauto. }
  change (a :: r ++ [a]) with ((a :: r) ++ [a]) in D.
  pose proof (app_removelast_last a (l:=a :: r) ltac:(discriminate)) as Er.
  assert (El : List.last (a :: r) a = List.last r a) by (destruct r; reflexivity).
  rewrite El in Er. rewrite Er, <- app_assoc in D. cbn [app] in D. apply linked_prefix in D as (D & D2 & D3).
  rewrite <- Er in D. tauto.
Qed.

Section EVOL.
Variables (st : mstate) (LS : lhead -> list aptr).
Hypothesis LO : lists_ok st LS.
Local Notation R := (MR st).

(* [comment removed for export] *)
#[using="LO"] Lemma lists_rotate h a rest a' :
  LS h = a :: rest -> m_next (R a) = Some a' ->
  lists_ok (set_head h (Some a') st) (fupd LS h (rest ++ [a])).
Proof.
  intros E Hn. pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D.
  assert (Ha' : head_of (rest ++ [a]) = Some a').
  { destruct rest as [|b r]; cbn in D |- *; [destruct D as (D1 & _)| destruct D as (D1 & _)]; rewrite Hn in D1; congruence. }
  constructor.
  - intros h'. destruct (decide (h' = h)) as [->|NE].
    + rewrite get_head_set_head, fupd_eq. symmetry. exact Ha'.
    + rewrite get_head_set_head_other, fupd_ne by exact NE. apply (lo_head _ _ LO).
  - intros h'. assert (X : forall l, dll st l -> dll (set_head h (Some a') st) l).
    { intros [|b l] Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl]; intros; unfold MR; rewrite get_meta_rec_set_head; reflexivity. }
    destruct (decide (h' = h)) as [->|NE].
    + rewrite fupd_eq. apply X. destruct rest as [|b r].
      * cbn. exact D.
      * cbn [dll app]. cbn [app] in D. destruct D as (D1 & D2 & D3).
        rewrite <- app_assoc. cbn [app].
        apply (linked_snoc st (b :: r) a b); [exact D3| exact D1| exact D2].
    + rewrite fupd_ne by exact NE. apply X. apply (lo_dll _ _ LO).
  - intros h'. destruct (decide (h' = h)) as [->|NE].
    + rewrite fupd_eq. pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
      apply NoDup_cons in ND as [N1 N2]. apply NoDup_app. split; [exact N2|]. split.
      * intros x Hx Hx2. apply list_elem_of_singleton in Hx2. subst x. exact (N1 Hx).
      * apply NoDup_singleton.
    + rewrite fupd_ne by exact NE. apply (lo_nodup _ _ LO).
  - intros h1 h2 m H1 H2.
    assert (M : forall h', In m (fupd LS h (rest ++ [a]) h') -> In m (LS h')).
    { intros h' Hm. destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
      rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. cbn in Hm |- *. tauto. }
    apply (lo_disj _ _ LO _ _ m); apply M; assumption.
  - intros m. unfold MR. rewrite !get_meta_rec_set_head. fold (R m).
    destruct (lo_link _ _ LO m) as [L1 L2]. split; [|exact L2]. rewrite <- L1.
    split; intros [h' Hm]; exists h'.
    + destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
      rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. cbn in Hm |- *. tauto.
    + destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne by exact NE'; exact Hm].
      rewrite fupd_eq. rewrite E in Hm. apply in_app_iff. cbn in Hm |- *. tauto.
Qed.

(* [comment removed for export] *)
#[using="LO"] Lemma lists_queue h g :
  m_next (R g) = None ->
  lists_ok (queue_st h g st) (fupd LS h (LS h ++ [g])).
Proof.
  intros Hg. pose proof (lists_notin _ _ LO _ Hg) as Gn.
  set (st' := queue_st h g st).
  pose proof (queue_next h g st) as QN. pose proof (queue_prev h g st) as QP. pose proof (queue_head h g st) as QH.
  fold st' in QN, QP, QH.
  pose proof (lo_head _ _ LO h) as Hh.
  destruct (LS h) as [|a rest] eqn:E.
  - (* [comment removed for export] *)
    cbn [head_of] in Hh. rewrite Hh in QN, QP, QH.
    assert (EXT : forall l, ~ In g l -> dll st l -> dll st' l).
    { intros [|b l] Hgl Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl].
      + intros x Hx. rewrite QN. rewrite aptr_eqb_neq; [reflexivity|]. intros ->. apply Hgl. apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      + intros x Hx. rewrite QP. rewrite aptr_eqb_neq; [reflexivity|]. intros ->. apply Hgl. apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto. }
    constructor.
    + intros h'. rewrite QH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
    + intros h'. destruct (decide (h' = h)) as [->|NE].
      * rewrite fupd_eq. cbn. rewrite QN, QP, aptr_eqb_refl. auto.
      * rewrite fupd_ne by exact NE. apply EXT; [apply Gn| apply (lo_dll _ _ LO)].
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; apply NoDup_singleton| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
    + intros h1 h2 m H1 H2. destruct (decide (h1 = h)) as [->|N1], (decide (h2 = h)) as [->|N2]; try congruence.
      * rewrite fupd_eq in H1. rewrite fupd_ne in H2 by exact N2. cbn in H1. destruct H1 as [<-|[]]. exfalso. exact (Gn _ H2).
      * rewrite fupd_eq in H2. rewrite fupd_ne in H1 by exact N1. cbn in H2. destruct H2 as [<-|[]]. exfalso. exact (Gn _ H1).
      * rewrite fupd_ne in H1 by exact N1. rewrite fupd_ne in H2 by exact N2. exact (lo_disj _ _ LO _ _ _ H1 H2).
    + intros m. rewrite QN, QP. destruct (aptr_eqb_spec m g) as [->|NE].
      * split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. left. reflexivity.
      * destruct (lo_link _ _ LO m) as [L1 L2]. split; [|exact L2]. rewrite <- L1. split; intros [h' Hm]; exists h'.
        -- destruct (decide (h' = h)) as [->|NE']; [rewrite fupd_eq in Hm; cbn in Hm; destruct Hm as [->|[]]; congruence|].
           rewrite fupd_ne in Hm by exact NE'. exact Hm.
        -- destruct (decide (h' = h)) as [->|NE']; [rewrite E in Hm; destruct Hm|]. rewrite fupd_ne by exact NE'. exact Hm.
  - (* [comment removed for export] *)
    cbn [head_of] in Hh. rewrite Hh in QN, QP, QH.
    destruct (lists_head_prev _ _ LO h a rest E) as [Pa Nz]. remember (List.last rest a) as z eqn:Ez.
    rewrite Pa in QN. cbn [optr_eqb] in QN.
    assert (Zin : In z (a :: rest)).
    { rewrite Ez. apply last_In. }
    assert (Ga : a <> g) by (intros ->; apply (Gn h); rewrite E; left; reflexivity).
    assert (Gz : z <> g) by (intros X; apply (Gn h); rewrite E, <- X; exact Zin).
    rewrite (aptr_eqb_neq a g) in QN by exact Ga.
    (* [comment removed for export] *)
    assert (QN' : forall x, m_next (MR st' x) = if aptr_eqb x z then Some g else if aptr_eqb x g then Some a else m_next (R x)).
    { intros x. rewrite QN.
      repeat match goal with |- context [aptr_eqb ?u ?v] => destruct (aptr_eqb_spec u v) end; subst; try reflexivity; congruence. }
    clear QN.
    pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
    (* [comment removed for export] *)
    assert (Hl1 : exists l1, a :: rest = l1 ++ [z] /\ ~ In z l1).
    { assert (Elz : List.last (a :: rest) a = z) by (rewrite Ez; destruct rest; reflexivity).
      pose proof (app_removelast_last a (l:=a :: rest) ltac:(discriminate)) as Er. rewrite Elz in Er.
      exists (removelast (a :: rest)). split; [exact Er|].
      intros Hz. rewrite Er in ND. exact (proj1 (NoDup_In_split _ _ _ ND) Hz). }
    destruct Hl1 as (l1 & El1 & Zl1).
    assert (Al : ~ In a rest) by (apply NoDup_cons in ND as [N _]; intros X; apply N; apply list_elem_of_In; exact X).
    (* [comment removed for export] *)
    assert (EXT : forall l, (forall x, In x l -> x <> a /\ x <> z /\ x <> g) -> dll st l -> dll st' l).
    { intros [|b l] Hx Hl; [exact I|]. cbn [dll] in Hl |- *. eapply linked_ext; [| | exact Hl].
      + intros x Hin. apply In_removelast in Hin. assert (In x (b :: l)) by (apply in_app_iff in Hin; cbn in Hin; cbn; tauto).
        destruct (Hx x H) as (X1 & X2 & X3). rewrite QN'. rewrite !aptr_eqb_neq by assumption. reflexivity.
      + intros x Hin. apply In_tl in Hin. assert (In x (b :: l)) by (apply in_app_iff in Hin; cbn in Hin; cbn; tauto).
        destruct (Hx x H) as (X1 & X2 & X3). rewrite QP. rewrite !aptr_eqb_neq by assumption. reflexivity. }
    constructor.
    + intros h'. rewrite QH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
    + intros h'. destruct (decide (h' = h)) as [->|NE].
      * rewrite fupd_eq. cbn [dll app]. rewrite <- app_assoc. cbn [app].
        (* [comment removed for export] *)
        assert (L0 : linked st' (a :: rest)).
        { pose proof (lo_dll _ _ LO h) as D. rewrite E in D. cbn [dll] in D. rewrite El1, <- app_assoc in D. cbn [app] in D.
          apply linked_prefix in D as (D & _ & _). rewrite El1.
          eapply linked_ext; [| | exact D].
          - intros x Hx. rewrite removelast_app in Hx by discriminate. cbn in Hx. rewrite app_nil_r in Hx.
            rewrite QN'. rewrite (aptr_eqb_neq x z) by (intros ->; exact (Zl1 Hx)).
            rewrite (aptr_eqb_neq x g); [reflexivity|]. intros ->. apply (Gn h). rewrite E, El1. apply in_app_iff. left. exact Hx.
          - intros x Hx. rewrite QP.
            assert (Hx' : In x rest). { rewrite <- El1 in Hx. exact Hx. }
            rewrite (aptr_eqb_neq x a) by (intros ->; exact (Al Hx')).
            rewrite (aptr_eqb_neq x g); [reflexivity|]. intros ->. apply (Gn h). rewrite E. right. exact Hx'. }
        change (a :: rest ++ [g; a]) with ((a :: rest) ++ [g; a]).
        rewrite El1 in L0 |- *. rewrite <- app_assoc. cbn [app].
        apply (linked_app st' z l1 [g; a]). split; [exact L0|]. cbn.
        rewrite !QN', !QP, Pa.
        repeat match goal with |- context [aptr_eqb ?u ?v] => destruct (aptr_eqb_spec u v) end; subst; try congruence; repeat split; congruence.
      * rewrite fupd_ne by exact NE. apply EXT; [| apply (lo_dll _ _ LO)].
        intros x Hx. repeat split; intros ->.
        -- apply NE. eapply (lo_disj _ _ LO); [exact Hx| rewrite E; left; reflexivity].
        -- apply NE. eapply (lo_disj _ _ LO); [exact Hx| rewrite E; exact Zin].
        -- exact (Gn _ Hx).
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
      rewrite fupd_eq. apply NoDup_app. split; [exact ND|]. split; [| apply NoDup_singleton].
      intros x Hx Hx2. apply list_elem_of_singleton in Hx2. subst x. apply (Gn h). rewrite E. apply list_elem_of_In. exact Hx.
    + intros h1 h2 m H1 H2.
      assert (M : forall h', In m (fupd LS h ((a :: rest) ++ [g]) h') -> In m (LS h') \/ (m = g /\ h' = h)).
      { intros h' Hm. destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; auto].
        rewrite fupd_eq in Hm. apply in_app_iff in Hm. destruct Hm as [Hm|[<-|[]]]; [left; rewrite E; exact Hm| right; auto]. }
      destruct (M _ H1) as [M1|[Em1 Eh1]], (M _ H2) as [M2|[Em2 Eh2]]; subst; try reflexivity.
      * exact (lo_disj _ _ LO _ _ _ M1 M2).
      * exfalso. exact (Gn _ M1).
      * exfalso. exact (Gn _ M2).
    + intros m. rewrite QN', QP. destruct (aptr_eqb_spec m z) as [->|NEz].
      * split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. apply in_app_iff. left. exact Zin.
      * destruct (aptr_eqb_spec m g) as [->|NEg].
        -- split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. rewrite fupd_eq. apply in_app_iff. right. left. reflexivity.
        -- destruct (lo_link _ _ LO m) as [L1 L2]. split.
           ++ rewrite <- L1. split; intros [h' Hm]; exists h'.
              ** destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne in Hm by exact NE'; exact Hm].
                 rewrite fupd_eq in Hm. rewrite E. apply in_app_iff in Hm. destruct Hm as [Hm|[->|[]]]; [exact Hm| congruence].
              ** destruct (decide (h' = h)) as [->|NE']; [| rewrite fupd_ne by exact NE'; exact Hm].
                 rewrite fupd_eq. apply in_app_iff. left. rewrite E in Hm. exact Hm.
           ++ intros Hn. rewrite (aptr_eqb_neq m a); [exact (L2 Hn)|]. intros ->.
              apply (lists_in_next_some _ _ LO h a); [rewrite E; left; reflexivity| exact Hn].
Qed.


(* [comment removed for export] *)
#[using="LO"] Lemma lists_dequeue h m l1 l2 :
  LS h = l1 ++ m :: l2 ->
  lists_ok (dequeue h m st) (fupd LS h (l1 ++ l2)).
Proof.
  intros E. set (st' := dequeue h m st).
  pose proof (dequeue_next h m st) as DN. pose proof (dequeue_prev h m st) as DP. pose proof (dequeue_head h m st) as DH.
  fold st' in DN, DP, DH.
  pose proof (lo_nodup _ _ LO h) as ND. rewrite E in ND.
  destruct (NoDup_In_split _ _ _ ND) as [N1 N2].
  assert (Min : In m (LS h)) by (rewrite E; apply in_app_iff; right; left; reflexivity).
  pose proof (lo_head _ _ LO h) as Hh. rewrite E in Hh.
  pose proof (lo_dll _ _ LO h) as D. rewrite E in D.
  (* [comment removed for export] *)
  apply dll_rot in D. cbn [app] in D. remember (l2 ++ l1) as rest eqn:Erest.
  assert (NDr : NoDup (m :: rest)).
  { subst rest. apply NoDup_ListNoDup. apply (Permutation_NoDup (l:=l1 ++ m :: l2)).
    - apply Permutation_sym. etransitivity; [| apply Permutation_middle]. apply perm_skip. apply Permutation_app_comm.
    - apply NoDup_ListNoDup. exact ND. }
  apply NoDup_cons in NDr as [Nmr NDr]. assert (Nmr' : ~ In m rest) by (intros X; apply Nmr; apply list_elem_of_In; exact X).
  assert (Rin : forall x, In x rest <-> In x l1 \/ In x l2) by (intros x; subst rest; rewrite in_app_iff; tauto).
  destruct (dll_ends st m rest D) as (Nm & Pq & Np & Pm & LK).
  (* [comment removed for export] *)
  assert (MEM : forall h' x, In x (fupd LS h (l1 ++ l2) h') -> In x (LS h') /\ x <> m).
  { intros h' x Hx. destruct (decide (h' = h)) as [->|NE].
    - rewrite fupd_eq in Hx. apply in_app_iff in Hx. split.
      + rewrite E. apply in_app_iff. cbn. tauto.
      + intros ->. tauto.
    - rewrite fupd_ne in Hx by exact NE. split; [exact Hx|]. intros ->. apply NE. exact (lo_disj _ _ LO _ _ _ Hx Min). }
  assert (MEM' : forall h' x, In x (LS h') -> x <> m -> In x (fupd LS h (l1 ++ l2) h')).
  { intros h' x Hx NE. destruct (decide (h' = h)) as [->|NE'].
    - rewrite fupd_eq. rewrite E in Hx. apply in_app_iff in Hx. apply in_app_iff. cbn in Hx. destruct Hx as [?|[?|?]]; [tauto|congruence|tauto].
    - rewrite fupd_ne by exact NE'. exact Hx. }
  assert (ND12 : NoDup (l1 ++ l2)).
  { apply NoDup_app in ND as (A1 & A2 & A3). apply NoDup_cons in A3 as [_ A3].
    apply NoDup_app. split; [exact A1|]. split; [| exact A3]. intros x Hx Hx2. apply (A2 x Hx). right. exact Hx2. }
  destruct rest as [|q r].
  - (* [comment removed for export] *)
    cbn in Nm, Pm. rewrite Nm in DN, DP, DH. cbn [optr_eqb] in DN, DP, DH. rewrite aptr_eqb_refl in DN, DP, DH.
    assert (E12 : l1 = [] /\ l2 = []) by (destruct l2; [destruct l1; [auto|discriminate]| discriminate]).
    destruct E12 as [-> ->]. cbn [app] in *.
    constructor.
    + intros h'. rewrite DH. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; reflexivity|]. rewrite fupd_ne by exact NE. apply (lo_head _ _ LO).
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact I|]. rewrite fupd_ne by exact NE.
      pose proof (lo_dll _ _ LO h') as D'. destruct (LS h') as [|c l] eqn:E'; [exact I|]. cbn [dll] in D' |- *.
      eapply linked_ext; [| | exact D']; intros x Hx; [rewrite DN| rewrite DP]; rewrite aptr_eqb_neq; try reflexivity;
        intros ->; apply NE; [apply In_removelast in Hx| apply In_tl in Hx]; apply in_app_iff in Hx; cbn in Hx;
        (eapply (lo_disj _ _ LO); [| exact Min]); rewrite E'; cbn; tauto.
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; apply NoDup_nil_2| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
    + intros h1 h2 x H1 H2. apply MEM in H1 as [H1 _]. apply MEM in H2 as [H2 _]. exact (lo_disj _ _ LO _ _ _ H1 H2).
    + intros x. rewrite DN, DP. destruct (aptr_eqb_spec x m) as [->|NE].
      * split; [| reflexivity]. split; [| congruence]. intros [h' Hx]. apply MEM in Hx as [_ Hx]. congruence.
      * destruct (lo_link _ _ LO x) as [L1 L2]. split; [| exact L2]. rewrite <- L1. split; intros [h' Hx]; exists h'.
        -- apply MEM in Hx. tauto.
        -- apply MEM'; assumption.
  - (* [comment removed for export] *)
    cbn zeta in Nm, Pq. remember (List.last (q :: r) m) as p eqn:Ep.
    assert (Qin : In q (q :: r)) by (left; reflexivity).
    assert (Pin : In p (q :: r)) by (rewrite Ep; apply last_In'; discriminate).
    assert (NEq : q <> m) by (intros ->; exact (Nmr' Qin)).
    assert (NEp : p <> m) by (intros ->; exact (Nmr' Pin)).
    rewrite Nm, Pm in DN. rewrite Nm in DP. rewrite Nm in DH. cbn [optr_eqb] in DN, DP, DH.
    rewrite (aptr_eqb_neq q m) in DN, DP, DH by exact NEq.
    assert (DN' : forall x, m_next (MR st' x) = if aptr_eqb x m then None else if aptr_eqb x p then Some q else m_next (R x)).
    { intros x. rewrite DN. destruct (aptr_eqb x m); [reflexivity|]. destruct (aptr_eqb_spec p x), (aptr_eqb_spec x p); subst; try reflexivity; congruence. }
    assert (DP' : forall x, m_prev (MR st' x) = if aptr_eqb x m then None else if aptr_eqb x q then Some p else m_prev (R x)).
    { intros x. rewrite DP. destruct (aptr_eqb x m); [reflexivity|]. destruct (aptr_eqb_spec q x), (aptr_eqb_spec x q); subst; try reflexivity; congruence. }
    clear DN DP.
    assert (EXT : forall l, ~ In m l -> ~ In p (removelast l) -> ~ In q (tl l) -> linked st l -> linked st' l).
    { intros l Hm Hp Hq Hl. eapply linked_ext; [| | exact Hl].
      - intros x Hx. rewrite DN'. rewrite (aptr_eqb_neq x m) by (intros ->; exact (Hm (In_removelast _ _ Hx))).
        rewrite (aptr_eqb_neq x p) by (intros ->; exact (Hp Hx)). reflexivity.
      - intros x Hx. rewrite DP'. rewrite (aptr_eqb_neq x m) by (intros ->; exact (Hm (In_tl _ _ Hx))).
        rewrite (aptr_eqb_neq x q) by (intros ->; exact (Hq Hx)). reflexivity. }
    (* [comment removed for export] *)
    assert (CYC : dll st' (q :: r)).
    { cbn [dll app]. cbn [linked] in LK. destruct LK as (_ & _ & LK).
      pose proof (app_removelast_last m (l:=q :: r) ltac:(discriminate)) as Er.
      rewrite <- Ep in Er.
      change (q :: r ++ [q]) with ((q :: r) ++ [q]). rewrite Er, <- app_assoc. cbn [app].
      apply linked_snoc.
      - apply EXT.
        + intros Hm. rewrite <- Er in Hm. exact (Nmr' Hm).
        + rewrite removelast_app by discriminate. cbn. rewrite app_nil_r. intros Hp.
          pose proof NDr as X. rewrite Er in X. exact (proj1 (NoDup_In_split _ _ _ X) Hp).
        + intros Hq. rewrite <- Er in Hq. cbn in Hq. apply NoDup_cons in NDr as [X _]. apply X. apply list_elem_of_In. exact Hq.
        + rewrite <- Er. exact LK.
      - rewrite DN'. rewrite (aptr_eqb_neq p m) by exact NEp. rewrite aptr_eqb_refl. reflexivity.
      - rewrite DP'. rewrite (aptr_eqb_neq q m) by exact NEq. rewrite aptr_eqb_refl. reflexivity. }
    rewrite Erest in CYC. apply dll_rot in CYC.
    constructor.
    + intros h'. rewrite DH. destruct (decide (h' = h)) as [->|NE]; [| rewrite fupd_ne by exact NE; apply (lo_head _ _ LO)].
      rewrite fupd_eq, Hh. destruct l1 as [|c l1']; cbn [app head_of].
      * rewrite optr_eqb_refl. rewrite app_nil_r in Erest. rewrite <- Erest. reflexivity.
      * cbn [optr_eqb]. rewrite (aptr_eqb_neq c m) by (intros ->; apply N1; left; reflexivity). reflexivity.
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact CYC|]. rewrite fupd_ne by exact NE.
      pose proof (lo_dll _ _ LO h') as D'. destruct (LS h') as [|c l] eqn:E'; [exact I|]. cbn [dll] in D' |- *.
      apply EXT; [| | | exact D'].
      * intros Hm. apply NE. eapply (lo_disj _ _ LO); [| exact Min]. rewrite E'. apply in_app_iff in Hm. cbn in Hm |- *. tauto.
      * intros Hp. apply In_removelast in Hp. apply NE. eapply (lo_disj _ _ LO _ h p); [rewrite E'| rewrite E; apply in_app_iff; cbn; pose proof (proj1 (Rin p) Pin); tauto].
        apply in_app_iff in Hp. cbn in Hp |- *. tauto.
      * intros Hq. apply In_tl in Hq. apply NE. eapply (lo_disj _ _ LO _ h q); [rewrite E'| rewrite E; apply in_app_iff; cbn; pose proof (proj1 (Rin q) Qin); tauto].
        apply in_app_iff in Hq. cbn in Hq |- *. tauto.
    + intros h'. destruct (decide (h' = h)) as [->|NE]; [rewrite fupd_eq; exact ND12| rewrite fupd_ne by exact NE; apply (lo_nodup _ _ LO)].
    + intros h1 h2 x H1 H2. apply MEM in H1 as [H1 _]. apply MEM in H2 as [H2 _]. exact (lo_disj _ _ LO _ _ _ H1 H2).
    + intros x. rewrite DN', DP'. destruct (aptr_eqb_spec x m) as [->|NE].
      * split; [| reflexivity]. split; [| congruence]. intros [h' Hx]. apply MEM in Hx as [_ Hx]. congruence.
      * destruct (aptr_eqb_spec x p) as [->|NEp'].
        -- split; [| intros; discriminate]. split; [intros; discriminate|]. intros _. exists h. apply MEM'; [| exact NEp].
           rewrite E. apply in_app_iff. cbn. pose proof (proj1 (Rin p) Pin). tauto.
        -- destruct (lo_link _ _ LO x) as [L1 L2]. split.
           ++ rewrite <- L1. split; intros [h' Hx]; exists h'; [apply MEM in Hx; tauto| apply MEM'; assumption].
           ++ intros Hn. destruct (aptr_eqb_spec x q) as [->|NEq']; [| exact (L2 Hn)].
              exfalso. refine (lists_in_next_some _ _ LO h q _ Hn). rewrite E. apply in_app_iff. cbn. pose proof (proj1 (Rin q) Qin). tauto.
Qed.
End EVOL.

End WithCeil.
End MI_List.

(* [comment removed for export] *)
Module MI_Ext.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Record ctrl_eq (st st' : mstate) : Prop := mkCE {
  ce_ctx : s_ctx st' = s_ctx st;
  ce_regions : s_regions st' = s_regions st;
  ce_next_rid : s_next_rid st' = s_next_rid st;
  ce_metas : s_metas st' = s_metas st;
  ce_areas : s_areas st' = s_areas st;
  ce_groups : s_groups st' = s_groups st;
  ce_slots : s_slots st' = s_slots st;
  ce_secret : s_secret st' = s_secret st;
  ce_reserved : s_reserved st' = s_reserved st
}.

#[using="Type"] Lemma ctrl_eq_refl st : ctrl_eq st st.
Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_sym st st' : ctrl_eq st st' -> ctrl_eq st' st.
Proof. intros []; constructor; symmetry; assumption. Qed.
#[using="Type"] Lemma ctrl_eq_trans a b c : ctrl_eq a b -> ctrl_eq b c -> ctrl_eq a c.
Proof. intros [] []; constructor; congruence. Qed.

#[using="Type"] Lemma ctrl_eq_strip st st' : strip st' = strip st -> ctrl_eq st st'.
Proof. intros H. pose proof (strip_fields st) as A. pose proof (strip_fields st') as B. constructor; intuition congruence. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ctrl_eq_set_tick st t : ctrl_eq st (set_tick t st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_wr8 st p v : ctrl_eq st (wr8 p v st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_wr16 st p v : ctrl_eq st (wr16 p v st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_wr32 st p v : ctrl_eq st (wr32 p v st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_havoc st p n : ctrl_eq st (havoc p n st). Proof. apply ctrl_eq_strip. apply strip_havoc. Qed.
#[using="Type"] Lemma ctrl_eq_hdr_havoc st b : ctrl_eq st (hdr_havoc b st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_upd_shadow st rid f : ctrl_eq st (upd_shadow rid f st). Proof. constructor; reflexivity. Qed.
#[using="Type"] Lemma ctrl_eq_zero_hdrs st p size i cnt : ctrl_eq st (zero_hdrs p size i cnt st). Proof. apply ctrl_eq_strip. apply strip_zero_hdrs. Qed.
#[using="Type"] Lemma ctrl_eq_set_size st p e n b : ctrl_eq st (set_size p e n b st). Proof. apply ctrl_eq_strip. apply strip_set_size. Qed.
#[using="Type"] Lemma ctrl_eq_enframe_at st g idx n off : ctrl_eq st (fst (enframe_at st g idx n off)). Proof. apply ctrl_eq_strip. apply strip_enframe_at. Qed.
#[using="Type"] Lemma ctrl_eq_nest_layout st g idx j size cnt : ctrl_eq st (nest_layout st g idx j size cnt). Proof. apply ctrl_eq_strip. apply strip_nest_layout. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VIEWS.
Variables st st' : mstate.

#[using="Type"] Lemma MR_ext : s_metas st' = s_metas st -> forall x, MR st' x = MR st x.
Proof. intros H x. unfold MR. apply get_meta_rec_ext. exact H. Qed.
#[using="Type"] Lemma hosts_ext : s_groups st' = s_groups st -> forall b m, hosts st' b m <-> hosts st b m.
Proof. intros H b m. unfold hosts. rewrite H. tauto. Qed.
#[using="Type"] Lemma live_group_ext : s_groups st' = s_groups st -> forall m, live_group st' m <-> live_group st m.
Proof. intros H m. unfold live_group. split; intros [b Hb]; exists b; apply (hosts_ext H); exact Hb. Qed.
#[using="Type"] Lemma frontier_ext : c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st) -> forall rid r, frontier st' rid r = frontier st rid r.
Proof. intros H rid r. unfold frontier. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma gcnt_ext : s_groups st' = s_groups st -> s_metas st' = s_metas st -> forall sc, gcnt st' sc = gcnt st sc.
Proof. intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [|reflexivity]. rewrite !(MR_ext HM). reflexivity. Qed.
#[using="Type"] Lemma get_head_ext : s_ctx st' = s_ctx st -> forall h, get_head st' h = get_head st h.
Proof. intros H h. destruct h; cbn; unfold active, ctx; rewrite H; reflexivity. Qed.
#[using="Type"] Lemma active_ext : c_active (s_ctx st') = c_active (s_ctx st) -> forall sc, active st' sc = active st sc.
Proof. intros H sc. unfold active, ctx. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma usage_ext : c_usage (s_ctx st') = c_usage (s_ctx st) -> forall sc, usage st' sc = usage st sc.
Proof. intros H sc. unfold usage, ctx. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma get_shadow_ext' : s_shadow st' = s_shadow st -> forall rid, get_shadow st' rid = get_shadow st rid.
Proof. intros H rid. apply get_shadow_ext. exact H. Qed.
#[using="Type"] Lemma known_ext : s_shadow st' = s_shadow st -> forall p v, known st' p v <-> known st p v.
Proof. intros H p v. unfold known, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
#[using="Type"] Lemma unknown_ext : s_shadow st' = s_shadow st -> forall p, unknown st' p <-> unknown st p.
Proof. intros H p. unfold unknown, SHd. rewrite (get_shadow_ext _ _ _ H). tauto. Qed.
#[using="Type"] Lemma linked_ext_metas : s_metas st' = s_metas st -> forall l, linked st l -> linked st' l.
Proof. intros H l Hl. eapply linked_ext; [| | exact Hl]; intros; rewrite (MR_ext H); reflexivity. Qed.
#[using="Type"] Lemma dll_ext_metas : s_metas st' = s_metas st -> forall l, dll st l -> dll st' l.
Proof. intros H [|a l] Hl; [exact I|]. cbn [dll] in Hl |- *. apply linked_ext_metas; assumption. Qed.
End VIEWS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CTRL.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis CE : ctrl_eq st st'.

Let HC := ce_ctx _ _ CE. Let HR := ce_regions _ _ CE. Let HN := ce_next_rid _ _ CE. Let HM := ce_metas _ _ CE.
Let HA := ce_areas _ _ CE. Let HG := ce_groups _ _ CE. Let HS := ce_slots _ _ CE. Let HX := ce_secret _ _ CE. Let HV := ce_reserved _ _ CE.

#[using="CE HC HR HN HG HV"] Lemma inv_R_ctrl : inv_R X st L -> inv_R X st' L.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  destruct I; constructor; rewrite ?HR, ?HN, ?HV, ?HC, ?HG; try assumption.
  - (* [comment removed for export] *)
    eapply Permutation_trans; [exact ir_metas|].
    erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
  - intros rid r H1 H2. rewrite FR. eauto.
  - intros rid r H1 H2. rewrite FR. eauto.
Qed.

#[using="CE HC HR HM HA HG HX"] Lemma inv_A_ctrl : inv_A st -> inv_A st'.
Proof.
  intros I. pose proof (frontier_ext st st' ltac:(rewrite HC; reflexivity)) as FR.
  pose proof (gcnt_ext st st' HG HM) as GC. pose proof (usage_ext st st' ltac:(rewrite HC; reflexivity)) as US.
  destruct I; constructor; rewrite ?HR, ?HC, ?HA, ?HM, ?HX; try assumption.
  - intros a ar H. destruct (ia_areas a ar H) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
  - intros sc Hsc. rewrite US, GC. auto.
Qed.

#[using="CE HM HG"] Lemma inv_M_ctrl : inv_M X st LS -> inv_M X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

#[using="CE HC HM HG"] Lemma inv_L_ctrl : inv_L st LS -> inv_L st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (get_head_ext st st' HC) as HE.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

#[using="CE HR HM HS"] Lemma group_ok_ctrl m b ai : group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HR, ?HS; try assumption.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

#[using="CE HR HM HG HS"] Lemma inv_G_ctrl : inv_G X st LS -> inv_G X st' LS.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [G1 G2 G3 G4 G5]; constructor.
  - intros m b ai H. rewrite HG in H. apply group_ok_ctrl. eapply G1. exact H.
  - intros b ai H. rewrite HG in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite HG in H1, H2. rewrite !ME. eapply G3; eassumption.
  - intros rid r H1 H2 H3. rewrite HR in H1. destruct (G4 rid r H1 H2 H3) as (m & Hm & Hml). exists m. rewrite HE, ME. auto.
  - intros b h H. rewrite HG in H. rewrite HR. eapply G5. exact H.
Qed.

#[using="CE HM HG HS"] Lemma inv_S_ctrl : inv_S X st BL -> inv_S X st' BL.
Proof.
  intros I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End CTRL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma inv_SH_set_tick st BL t : (s_tick st <= t)%N -> inv_SH st BL -> inv_SH (set_tick t st) BL.
Proof.
  intros Ht I. destruct I; constructor; cbn -[cell_read get_shadow Z.add Z.sub Z.mul Z.div]; try assumption.
  intros rid sh H. destruct (ish_ticks rid sh H) as (T1 & T2 & T3). split; [|split].
  - intros o v t0 Ho. destruct (T1 o v t0 Ho) as [A B]. split; [exact A| lia].
  - intros u hl ch Hu Hin. pose proof (T2 u hl ch Hu Hin). lia.
  - intros pg t0 Hp. pose proof (T3 pg t0 Hp). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inv_SH_ctrl st st' BL : ctrl_eq st st' -> s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros CE SH TK I.
  pose proof (MR_ext st st' (ce_metas _ _ CE)) as ME. pose proof (ce_groups _ _ CE) as HG. pose proof (ce_slots _ _ CE) as HS. pose proof (ce_regions _ _ CE) as HR.
  pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
  destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
  - intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
  - intros b m i Hb Hi. rewrite ME in Hi |- *. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
  - intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
  - intros b m p i Hb Hml Hs. rewrite ME in Hml. rewrite HS in Hs. rewrite !ME.
    destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !ME.
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma inv_SH_view st st' BL :
  s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> s_regions st' = s_regions st ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  (forall x, gbase (MR st' x) = gbase (MR st x)) ->
  (forall x, get_stride (MR st' x) = get_stride (MR st x)) ->
  (forall x, m_last_idx (MR st' x) = m_last_idx (MR st x)) ->
  (forall x, m_maplen (MR st' x) = m_maplen (MR st x)) ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros SH TK HR HG HS VB VS VL VM I.
  assert (VSS : forall x i, sstart (MR st' x) i = sstart (MR st x) i) by (intros; unfold sstart; rewrite VB, VS; reflexivity).
  assert (VC : forall x, cnt_of (MR st' x) = cnt_of (MR st x)) by (intros; unfold cnt_of; rewrite VL; reflexivity).
  pose proof (hosts_ext st st' HG) as HE. pose proof (known_ext st st' SH) as KE. pose proof (unknown_ext st st' SH) as UE.
  destruct I as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros rid sh H. rewrite SH in H. rewrite HR. eapply D1. exact H.
  - intros rid sh H. rewrite SH in H. rewrite TK. eapply D2. exact H.
  - intros b m i Hb Hi. rewrite VC in Hi. rewrite VSS. apply KE. apply (D3 b m i); [apply HE; exact Hb| exact Hi].
  - intros b m o Hb Ho. apply UE. apply (D4 b m o); [apply HE; exact Hb| exact Ho].
  - intros b m p i Hb Hml Hs. rewrite VM in Hml. rewrite HS in Hs. rewrite !VB.
    destruct (D5 b m p i ltac:(apply HE; exact Hb) Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q).
    split; [exists v3; split; [apply KE; exact K3| auto]|]. split; [apply KE; exact K2|]. split; [apply KE; exact K1| exact Q].
  - intros k m i Hk Hs. rewrite HS in Hs. rewrite !VS, !VB.
    destruct (D6 k m i Hk Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
    split; [apply KE; exact A1|]. split; [apply KE; exact A2|]. split; [apply KE; exact A3|]. split; [apply KE; exact A4|].
    split; [exact A5|]. split.
    + intros Hr. destruct (A6 Hr) as (B1 & B2 & B3 & B4 & B5 & B6). repeat split; try apply KE; assumption.
    + split; [intros Hr; apply KE; apply A7; exact Hr|]. intros a Ha. apply UE. apply A8. exact Ha.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INVL_ctrl_same X st st' L BL LS :
  ctrl_eq st st' -> s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  INVL X st L BL LS -> INVL X st' L BL LS.
Proof.
  intros CE SH TK (IR & IA & IM & IL & IG & IS & ISH).
  split; [apply (inv_R_ctrl X st st'); assumption|].
  split; [apply (inv_A_ctrl st st'); assumption|].
  split; [apply (inv_M_ctrl X st st'); assumption|].
  split; [apply (inv_L_ctrl st st'); assumption|].
  split; [apply (inv_G_ctrl X st st'); assumption|].
  split; [apply (inv_S_ctrl X st st'); assumption|].
  apply (inv_SH_ctrl st st'); assumption.
Qed.

End WithCeil.
End MI_Ext.

(* [comment removed for export] *)
Module MI_Ext2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeil.
Context {CE : CEIL}.
Section EXT2.
Variables (X : extras) (st st' : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).

#[using="Type"] Lemma inv_M_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> inv_M X st LS -> inv_M X st' LS.
Proof.
  intros HM HG I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite !ME in *. apply M1. exact Hm.
  - intros m b Hm. rewrite ME in Hm. destruct (M2 m b Hm) as [H|H]; [left; apply HE; exact H| right; exact H].
  - intros b h Hb. rewrite HG in Hb. destruct (M3 b h Hb) as (m & H1 & H2 & H3). exists m. rewrite !ME. auto.
  - intros m Hm. rewrite HM. apply M4. exact Hm.
  - intros z Hz. destruct (M5 z Hz) as (H1 & H2 & H3 & b & H4 & H5). rewrite !ME, HG. repeat split; auto. exists b. auto.
Qed.

#[using="Type"] Lemma inv_L_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> (forall h, get_head st' h = get_head st h) ->
  inv_L st LS -> inv_L st' LS.
Proof.
  intros HM HG HE I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite HE. apply L1.
  - intros h. apply (dll_ext_metas st st' HM). apply L2.
  - exact L3.
  - exact L4.
  - intros m. rewrite !ME. apply L5.
  - intros m Hm. rewrite !ME. apply L6. exact Hm.
  - intros sc m Hm. destruct (L7 sc m Hm) as (H1 & H2 & H3). rewrite (live_group_ext st st' HG), ME. auto.
  - exact L9.
Qed.

#[using="Type"] Lemma group_ok_ext m b ai : s_metas st' = s_metas st -> s_slots st' = s_slots st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> fst b = rid -> s_regions st' !! rid = Some r) ->
  group_ok X st LS m b ai -> group_ok X st' LS m b ai.
Proof.
  intros HM HS HR I. pose proof (MR_ext st st' HM) as ME.
  destruct I as [G1 G2 G3 G4 G5 G6 G7 G8 G9 G9b G10 G11 G12 G13 G14]; constructor; rewrite ?ME, ?HM, ?HS; try assumption.
  - intros Hml. destruct (G13 Hml) as (H0 & r & Hr & Hk & E1 & E2). split; [exact H0|]. exists r. split; [| auto]. apply HR; auto.
  - intros H. destruct (G14 H) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !ME. auto 10.
Qed.

#[using="Type"] Lemma inv_S_ext : s_metas st' = s_metas st -> s_groups st' = s_groups st -> s_slots st' = s_slots st ->
  inv_S X st BL -> inv_S X st' BL.
Proof.
  intros HM HG HS I. pose proof (MR_ext st st' HM) as ME. pose proof (hosts_ext st st' HG) as HE.
  destruct I as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i H. rewrite HS in H. destruct (S1 s m i H) as (? & ? & ?). rewrite (live_group_ext st st' HG), !ME. auto.
  - intros b m i Hb Hi. rewrite HS, ME. apply (S2 b); [apply HE; exact Hb| rewrite <- ME; exact Hi].
  - intros b m ai i Hb Hi. rewrite HG in Hb. rewrite !ME, HG. apply (S3 b m ai i); [exact Hb| rewrite <- ME; exact Hi].
  - intros c Hc. rewrite HS. apply S4. exact Hc.
  - exact S5.
  - intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite HS, ME. auto.
Qed.
End EXT2.

End WithCeil.
End MI_Ext2.

(* [comment removed for export] *)
Module MI_Pres1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma slot_key_inj X st BL (IS : inv_S X st BL) b1 m1 b2 m2 i1 i2 :
  hosts st b1 m1 -> hosts st b2 m2 -> 0 <= i1 <= m_last_idx (MR st m1) -> 0 <= i2 <= m_last_idx (MR st m2) ->
  slot_start' (MR st m1) i1 = slot_start' (MR st m2) i2 -> m1 = m2 /\ i1 = i2.
Proof.
  intros H1 H2 R1 R2 E.
  pose proof (is_total _ _ _ IS _ _ _ H1 R1) as T1. pose proof (is_total _ _ _ IS _ _ _ H2 R2) as T2.
  rewrite E in T1. rewrite T1 in T2. inversion T2. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma one5_E_irrel (A B C D E E' : Prop) : one5 A B C D E -> ~ E -> ~ E' -> one5 A B C D E'.
Proof.
  unfold one5. intros (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) NE NE'.
  split; [destruct H0 as [a|[b|[c|[d|e]]]]; [left; exact a| right; left; exact b| right; right; left; exact c| right; right; right; left; exact d| exfalso; exact (NE e)]|].
  repeat split; try assumption; intros [? ?]; apply NE'; assumption.
Qed.

Section MASK.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g b : aptr) (ai : Z) (A' F' : Z) (pend' : option aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! b = Some (mkGhdr (Some g) ai).

Let X' := mkX (x_idle X) (x_zomb X) pend' (x_orph X) (x_fresh X).
Let f := fun r : meta => m_set_avail A' (m_set_freed F' r).
Let st' := upd_meta g f st.
Local Notation R := (MR st).
Local Notation R' := (MR st').

Hypothesis C_masks : 0 <= A' /\ 0 <= F'
  /\ (forall i, 0 <= i -> tbit A' i = true -> i <= ai)
  /\ (forall i, 0 <= i -> tbit F' i = true -> i <= m_last_idx (R g))
  /\ (forall i, 0 <= i -> tbit A' i = true -> tbit F' i = true -> False)
  /\ (forall i, ai < i <= m_last_idx (R g) -> tbit F' i = true).
Hypothesis C_part : forall i, 0 <= i <= m_last_idx (R g) ->
  let s := slot_start' (R g) i in
  one5 (tbit A' i = true) (tbit F' i = true) (In s (map bslot BL)) (s_groups st !! s <> None) (pend' = Some s).
(* [comment removed for export] *)
Hypothesis C_pend : pend' = x_pend X \/
  ((forall s, x_pend X = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)
   /\ (forall s, pend' = Some s -> exists i, 0 <= i <= m_last_idx (R g) /\ s = slot_start' (R g) i)).
Hypothesis C_rest : x_fresh X <> Some g -> forall sc, In g (LS (LActive sc)) -> Some g <> head_of (LS (LActive sc)) -> A' = 0 /\ F' <> 0.
Hypothesis C_unlisted : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> ~ in_list LS g -> A' = 0 /\ F' = 0.
Hypothesis C_under : x_fresh X <> Some g -> m_sizeclass (R g) < 48 -> get_stride (R g) < UNIT * size_class (m_sizeclass (R g)) -> A' = 0 /\ F' = 0.

#[using="Type"] Lemma R'_eq x : R' x = if aptr_eqb x g then f (R g) else R x.
Proof. unfold st', MR. apply get_meta_rec_upd. Qed.
#[using="Type"] Lemma R'_other x : x <> g -> R' x = R x.
Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_g : R' g = f (R g).
Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fR_mem : m_mem (f (R g)) = m_mem (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_prev : m_prev (f (R g)) = m_prev (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_next : m_next (f (R g)) = m_next (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_last : m_last_idx (f (R g)) = m_last_idx (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freeable : m_freeable (f (R g)) = m_freeable (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sc : m_sizeclass (f (R g)) = m_sizeclass (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_maplen : m_maplen (f (R g)) = m_maplen (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_avail : m_avail (f (R g)) = A'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_freed : m_freed (f (R g)) = F'. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_stride : get_stride (f (R g)) = get_stride (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gbase : gbase (f (R g)) = gbase (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_sstart i : sstart (f (R g)) i = sstart (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_slot_start' i : slot_start' (f (R g)) i = slot_start' (R g) i. Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_gend : gend (f (R g)) = gend (R g). Proof. reflexivity. Qed.
#[using="Type"] Lemma fR_cnt : cnt_of (f (R g)) = cnt_of (R g). Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_maplen x : m_maplen (R' x) = m_maplen (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_stride x : get_stride (R' x) = get_stride (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sstart x i : sstart (R' x) i = sstart (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_slot_start' x i : slot_start' (R' x) i = slot_start' (R x) i. Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_gend x : gend (R' x) = gend (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x g) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_avail_other x : x <> g -> m_avail (R' x) = m_avail (R x). Proof. intros; rewrite R'_other; auto. Qed.
#[using="Type"] Lemma R'_freed_other x : x <> g -> m_freed (R' x) = m_freed (R x). Proof. intros; rewrite R'_other; auto. Qed.

#[using="Type"] Lemma st'_groups : s_groups st' = s_groups st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_slots : s_slots st' = s_slots st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
#[using="Type"] Lemma st'_shadow : s_shadow st' = s_shadow st. Proof. reflexivity. Qed.
#[using="Type"] Lemma hosts' bb m : hosts st' bb m <-> hosts st bb m. Proof. apply hosts_ext. reflexivity. Qed.
#[using="Type"] Lemma live' m : live_group st' m <-> live_group st m. Proof. apply live_group_ext. reflexivity. Qed.
#[using="X ai pend' C_masks C_pend"] Lemma keys' x : s_metas st' !! x <> None <-> s_metas st !! x <> None \/ x = g.
Proof.
  unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [auto| intros _; discriminate].
Qed.

#[using="ai Hg"] Lemma g_hosts : hosts st b g. Proof. exists ai. exact Hg. Qed.

#[using="b ai INV Hg C_masks C_part C_pend C_rest C_unlisted C_under"] Theorem INVL_mask_change : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof IM as IM0. pose proof IG as IG0. pose proof IS as IS0.
  assert (Gpres : s_metas st !! g <> None).
  { exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)). }
  assert (HD : forall m, live_group st m -> m <> g -> True) by auto.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_groups; try assumption.
  - (* [comment removed for export] *) destruct IA; constructor; rewrite ?st'_regions, ?st'_ctx, ?st'_areas; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply keys' in K.
      destruct K as [K| ->].
      * destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
      * destruct (s_metas st !! g) as [mr0|] eqn:E; [| congruence]. exact (ia_metas g mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply keys' in K. destruct K as [K|K].
      * apply K. apply Hk. exact Hk2.
      * apply Gpres. rewrite <- K. apply Hk. exact Hk2.
    + intros sc Hsc. unfold usage, ctx. rewrite st'_ctx. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc).
      unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
      rewrite R'_sc, R'_cnt. reflexivity.
  - (* [comment removed for export] *) destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite R'_mem in Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts). congruence.
      * apply M1. exact Hm.
    + intros m bb Hm. rewrite R'_mem in Hm. setoid_rewrite hosts'. apply M2. exact Hm.
    + intros bb h Hb. rewrite st'_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite R'_mem, R'_last. auto.
    + intros m Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_upd. destruct (aptr_eqb_spec m g) as [->|NE]; [| exact E].
      exfalso. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
    + intros z Hz. destruct (M5 z Hz) as (? & ? & ? & bb & ? & ?). rewrite R'_next, R'_prev, R'_mem, st'_groups. repeat split; auto. exists bb. auto.
  - (* [comment removed for export] *) destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. unfold st'. rewrite get_head_upd_meta. apply L1.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros; rewrite ?R'_next, ?R'_prev; reflexivity.
    + exact L3.
    + exact L4.
    + intros m. rewrite R'_next, R'_prev. apply L5.
    + intros m Hm. rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
      exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM0 _ _ g_hosts) as Hmem. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
    + intros sc m Hm. rewrite live', R'_sc. apply L7. exact Hm.
    + exact L9.
  - (* [comment removed for export] *) destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros m bb aim Hm. rewrite st'_groups in Hm. pose proof (G1 m bb aim Hm) as GO.
      destruct (aptr_eqb_spec m g) as [->|NE].
      * (* [comment removed for export] *)
        pose proof (hosts_inj _ _ _ IM0 _ _ _ (ex_intro _ aim Hm) g_hosts) as Ebb. subst bb.
        rewrite Hg in Hm. assert (aim = ai) by congruence. subst aim.
        destruct GO; constructor; rewrite ?R'_g, ?fR_last, ?fR_sc, ?fR_maplen, ?fR_freeable, ?fR_avail, ?fR_freed, ?fR_stride, ?fR_gend, ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; exact g_present).
        all: try exact C_masks.
        all: try (intros NF Hp; apply g_partial; [exact NF| exact Hp]).
        all: try (intros NF Hsc NI; apply C_unlisted; assumption).
        all: try (intros NF sc Hm Hh; apply (C_rest NF sc Hm Hh)).
        all: try (intros NF Hsc Hs; apply C_under; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-G" g end.
      * destruct GO; constructor; rewrite ?(R'_other m NE), ?st'_regions, ?st'_slots; try assumption.
        all: try (apply keys'; left; assumption).
        all: try (intros Hml; destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?); exists p, i; rewrite R'_gbase, R'_sstart, R'_stride, R'_sc; auto 10; fail).
        all: match goal with |- ?g => idtac "REMAINS-O" g end.
    + intros bb aim H. rewrite st'_groups in H. eapply G2. exact H.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite st'_groups in H1, H2. rewrite !R'_last, !R'_sc. eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite hosts', R'_maplen. auto.
    + intros bb h H. rewrite st'_groups in H. rewrite st'_regions. eapply G5. exact H.
  - (* [comment removed for export] *) destruct IS as [S1 S2 S3 S4 S5 S6]; constructor.
    + intros s m i H. rewrite st'_slots in H. destruct (S1 s m i H) as (? & ? & ?). rewrite live', R'_last, R'_slot_start'. auto.
    + intros bb m i Hb Hi. rewrite st'_slots, R'_slot_start'. apply (S2 bb); [apply hosts'; exact Hb| rewrite <- R'_last; exact Hi].
    + intros bb m aim i Hb Hi. rewrite st'_groups in Hb. rewrite R'_last in Hi. rewrite R'_slot_start', st'_groups.
      rewrite R'_eq. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite fR_avail, fR_freed. apply C_part. exact Hi.
      * (* [comment removed for export] *)
        pose proof (S3 bb m aim i Hb Hi) as P. cbn zeta in P |- *.
        destruct C_pend as [EP|[C_pend_old C_pend_new]]; [unfold X'; cbn [x_pend]; rewrite EP; exact P|].
        assert (NP1 : forall s, x_pend X = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_old _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (NP2 : forall s, pend' = Some s -> s <> slot_start' (R m) i).
        { intros s Hs ->. destruct (C_pend_new _ Hs) as (j & Hj & E).
          destruct (slot_key_inj _ _ _ IS0 _ _ _ _ _ _ (ex_intro _ aim Hb) g_hosts Hi Hj E) as [Em _]. exact (NE Em). }
        assert (O1 : ~ (x_pend X = Some (slot_start' (R m) i))) by (intros E; exact (NP1 _ E eq_refl)).
        assert (O2 : ~ (pend' = Some (slot_start' (R m) i))) by (intros E; exact (NP2 _ E eq_refl)).
        exact (one5_E_irrel _ _ _ _ _ _ P O1 O2).
    + intros s Hs. rewrite st'_slots. destruct C_pend as [EP|[_ C_pend_new]].
      * apply S4. rewrite <- EP. unfold X' in Hs. exact Hs.
      * destruct (C_pend_new _ Hs) as (j & Hj & ->). rewrite (S2 b g j g_hosts Hj). discriminate.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (m & i & ? & ?). exists m, i. rewrite st'_slots, R'_stride. auto.
  - (* [comment removed for export] *) apply (inv_SH_view st st'); try reflexivity; try assumption.
    + apply R'_gbase. + apply R'_stride. + apply R'_last. + apply R'_maplen.
Qed.
End MASK.

End WithCeil.
End MI_Pres1.
