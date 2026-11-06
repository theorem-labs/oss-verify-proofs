(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv ABudget.

Module AQOps.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AInv ABudget.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qpush_last (qt : list batch) (e : qentry) : list batch :=
  match qt with
  | [] => []
  | _ => removelast qt ++ [BA (ba_idx (last qt (BA 0 []))) (ba_entries (last qt (BA 0 [])) ++ [e])]
  end.
(* [comment removed for export] *)
Definition qpush_new (qt : list batch) (k : Z) (e : qentry) : list batch := qt ++ [BA k [e]].
(* [comment removed for export] *)
Definition qtransfer (qt qg : list batch) : list batch := qg ++ qt.
(* [comment removed for export] *)
Fixpoint rsplit (qg : list batch) (min : Z) : list batch * list batch :=
  match qg with
  | [] => ([], [])
  | b :: r => if min <? q_bytes (b :: r) then let (R, rest) := rsplit r min in (b :: R, rest) else ([], b :: r)
  end.

Lemma q_bytes_cons : forall b bs, q_bytes (b :: bs) = batch_bytes b + q_bytes bs. Proof. reflexivity. Qed.
Lemma q_bytes_app : forall l1 l2, q_bytes (l1 ++ l2) = q_bytes l1 + q_bytes l2.
Proof.
  intros l1 l2. induction l1 as [|b l1 IH]; [reflexivity|].
  change ((b :: l1) ++ l2) with (b :: (l1 ++ l2)). rewrite !q_bytes_cons, IH. lia.
Qed.
Lemma q_bytes_nil : q_bytes [] = 0. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition ebytes (l : list qentry) : Z := fold_right (fun e acc => qe_bytes e + acc) 0 l.
Lemma ebytes_cons : forall e l, ebytes (e :: l) = qe_bytes e + ebytes l. Proof. reflexivity. Qed.
Lemma entries_bytes_app : forall l1 l2, ebytes (l1 ++ l2) = ebytes l1 + ebytes l2.
Proof.
  intros l1 l2. induction l1 as [|e l1 IH]; [reflexivity|].
  change ((e :: l1) ++ l2) with (e :: (l1 ++ l2)). rewrite !ebytes_cons, IH. lia.
Qed.
Lemma batch_bytes_ebytes : forall b, batch_bytes b = kQuarantineBatchBytes + ebytes (ba_entries b).
Proof. reflexivity. Qed.

Lemma q_entries_cons : forall b bs, q_entries (b :: bs) = ba_entries b ++ q_entries bs. Proof. reflexivity. Qed.
Lemma q_entries_nil : q_entries [] = []. Proof. reflexivity. Qed.
Lemma batch_indices_def : forall qt qg, batch_indices_ qt qg = map ba_idx (qt ++ qg). Proof. reflexivity. Qed.

Lemma removelast_last_app : forall {X} (l : list X) d, l <> [] -> removelast l ++ [last l d] = l.
Proof. intros X l d NE. symmetry. apply app_removelast_last. exact NE. Qed.

(* [comment removed for export] *)
Section PushLast.
  Variables (qt : list batch) (e : qentry).
  Hypothesis NE : qt <> [].
  #[local] Notation bl := (last qt (BA 0 [])).

  Lemma qpush_last_shape : qpush_last qt e = removelast qt ++ [BA (ba_idx bl) (ba_entries bl ++ [e])].
  Proof. unfold qpush_last. destruct qt; [congruence| reflexivity]. Qed.

  Lemma qt_split : qt = removelast qt ++ [bl].
  Proof. symmetry. apply removelast_last_app. exact NE. Qed.

  Lemma qpush_last_entries : q_entries (qpush_last qt e) = q_entries qt ++ [e].
  Proof.
    assert (EQ : q_entries qt = q_entries (removelast qt) ++ ba_entries bl).
    { rewrite qt_split at 1. rewrite q_entries_app. cbn [q_entries flat_map]. rewrite app_nil_r. reflexivity. }
    rewrite EQ, qpush_last_shape, q_entries_app. cbn [q_entries flat_map ba_entries]. rewrite app_nil_r, app_assoc. reflexivity.
  Qed.

  Lemma qpush_last_bytes : q_bytes (qpush_last qt e) = q_bytes qt + qe_bytes e.
  Proof.
    assert (EQ : q_bytes qt = q_bytes (removelast qt) + batch_bytes bl).
    { rewrite qt_split at 1. rewrite q_bytes_app, q_bytes_cons, q_bytes_nil. lia. }
    rewrite EQ, qpush_last_shape, q_bytes_app, q_bytes_cons, q_bytes_nil, !batch_bytes_ebytes. cbn [ba_entries].
    rewrite entries_bytes_app, ebytes_cons. cbn [ebytes fold_right]. lia.
  Qed.

  Lemma qpush_last_indices : map ba_idx (qpush_last qt e) = map ba_idx qt.
  Proof.
    assert (EQ : map ba_idx qt = map ba_idx (removelast qt) ++ [ba_idx bl]) by (rewrite qt_split at 1; rewrite map_app; reflexivity).
    rewrite EQ, qpush_last_shape, map_app. reflexivity.
  Qed.

  Lemma qpush_last_length : length (qpush_last qt e) = length qt.
  Proof.
    assert (EQ : length qt = (length (removelast qt) + 1)%nat) by (rewrite qt_split at 1; rewrite length_app; reflexivity).
    rewrite EQ, qpush_last_shape, length_app. reflexivity.
  Qed.

  Lemma qpush_last_nonnil : qpush_last qt e <> [].
  Proof. rewrite qpush_last_shape. intros H. apply app_eq_nil in H. destruct H as [_ H]. discriminate H. Qed.

  Lemma qpush_last_last : last (qpush_last qt e) (BA 0 []) = BA (ba_idx bl) (ba_entries bl ++ [e]).
  Proof. rewrite qpush_last_shape. rewrite last_last. reflexivity. Qed.

  Lemma qpush_last_head : forall b r, qt = b :: r -> exists r', qpush_last qt e = (match r with [] => BA (ba_idx b) (ba_entries b ++ [e]) | _ => b end) :: r'.
  Proof.
    intros b r E. rewrite qpush_last_shape. subst qt. destruct r as [|b2 r2].
    - cbn. exists []. reflexivity.
    - cbn [removelast]. eexists. reflexivity.
  Qed.
End PushLast.

(* [comment removed for export] *)
Lemma qpush_new_entries : forall qt k e, q_entries (qpush_new qt k e) = q_entries qt ++ [e].
Proof. intros. unfold qpush_new. rewrite q_entries_app. reflexivity. Qed.
Lemma qpush_new_bytes : forall qt k e, q_bytes (qpush_new qt k e) = q_bytes qt + kQuarantineBatchBytes + qe_bytes e.
Proof. intros. unfold qpush_new. rewrite q_bytes_app, q_bytes_cons, q_bytes_nil, batch_bytes_ebytes. cbn [ba_entries]. rewrite ebytes_cons. cbn [ebytes fold_right]. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma qtransfer_entries : forall qt qg, q_entries (qtransfer qt qg) = q_entries qg ++ q_entries qt.
Proof. intros. unfold qtransfer. apply q_entries_app. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rsplit_app : forall qg min, let (R, rest) := rsplit qg min in qg = R ++ rest.
Proof.
  intros qg min. induction qg as [|b r IH]; cbn -[q_bytes]; [reflexivity|].
  destruct (min <? q_bytes (b :: r)); [| reflexivity]. destruct (rsplit r min) as [R rest]. cbn. f_equal. exact IH.
Qed.
Lemma rsplit_rest_small : forall qg min, 0 <= min -> let (R, rest) := rsplit qg min in q_bytes rest <= min \/ rest = [].
Proof.
  intros qg min Hm. induction qg as [|b r IH]; cbn -[q_bytes]; [right; reflexivity|].
  destruct (Z.ltb_spec min (q_bytes (b :: r))) as [LT|GE].
  - destruct (rsplit r min) as [R rest]. exact IH.
  - left. exact GE.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cache_set (cache : Z -> pcache) (c : Z) (ks : list Z) : Z -> pcache :=
  fun c' => if Z.eqb c' c then PCc ks else cache c'.
Definition reg_set (reg : Z -> region) (c : Z) (R : region) : Z -> region :=
  fun c' => if Z.eqb c' c then R else reg c'.

(* [comment removed for export] *)
Definition drain_keep (ks : list Z) (h : nat) : list Z := firstn (length ks - h) ks.
Definition drain_out (ks : list Z) (h : nat) : list Z := skipn (length ks - h) ks.
Definition reg_return (R : region) (out : list Z) (fa' : Z) : region :=
  RG (rg_mapped_user R) (rg_allocated_user R) fa' (rg_free R ++ out).

Lemma drain_split : forall ks h, ks = drain_keep ks h ++ drain_out ks h.
Proof. intros. unfold drain_keep, drain_out. symmetry. apply firstn_skipn. Qed.
Lemma drain_keep_length : forall ks h, (h <= length ks)%nat -> length (drain_keep ks h) = (length ks - h)%nat.
Proof. intros. unfold drain_keep. rewrite firstn_length. lia. Qed.
Lemma drain_out_length : forall ks h, (h <= length ks)%nat -> length (drain_out ks h) = h.
Proof. intros. unfold drain_out. rewrite skipn_length. lia. Qed.
Lemma drain_in_iff : forall ks h k, In k ks <-> In k (drain_keep ks h) \/ In k (drain_out ks h).
Proof. intros. rewrite (drain_split ks h) at 1. apply in_app_iff. Qed.
Lemma drain_nodup : forall ks h, NoDup ks -> NoDup (drain_keep ks h) /\ NoDup (drain_out ks h) /\
  (forall k, In k (drain_keep ks h) -> ~ In k (drain_out ks h)).
Proof.
  intros ks h ND. rewrite (drain_split ks h) in ND. apply (proj1 (list.NoDup_app _ _)) in ND. destruct ND as (N1 & DJ & N2).
  split; [exact N1|]. split; [exact N2|]. intros k Hk Ho. apply (DJ k); apply list_elem_of_In; assumption.
Qed.

(* [comment removed for export] *)
Definition cache_push_list (ks : list Z) (maxc : Z) (k : Z) : list Z * list Z (* [comment removed for export] *) :=
  if Z.of_nat (length ks) =? maxc then let h := Z.to_nat (maxc / 2) in (drain_keep ks h ++ [k], drain_out ks h)
  else (ks ++ [k], []).

Lemma cache_push_list_in : forall ks maxc k x,
  In x (fst (cache_push_list ks maxc k)) \/ In x (snd (cache_push_list ks maxc k)) <-> In x ks \/ x = k.
Proof.
  intros ks maxc k x. unfold cache_push_list. destruct (Z.of_nat (length ks) =? maxc); cbn [fst snd].
  - rewrite in_app_iff. pose proof (drain_in_iff ks (Z.to_nat (maxc / 2)) x) as D. cbn [In].
    split.
    + intros [[H|[H|[]]]|H]; [left; tauto | right; congruence | left; tauto].
    + intros [H|H]; [| left; right; left; congruence]. apply D in H. tauto.
  - rewrite in_app_iff. cbn [In]. split.
    + intros [[H|[H|[]]]|[]]; [left; exact H | right; congruence].
    + intros [H|H]; [left; left; exact H | left; right; left; congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint list_set {X} (l : list X) (i : nat) (x : X) : list X :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set r i' x
  end.
Definition swap_remove {X} (l : list X) (i : nat) (d : X) : list X :=
  removelast (list_set l i (last l d)).

Lemma list_set_length : forall {X} (l : list X) i x, length (list_set l i x) = length l.
Proof. intros X l. induction l as [|y r IH]; intros [|i] x; cbn; try reflexivity; f_equal; apply IH. Qed.
(* [comment removed for export] *)
Lemma swap_remove_length : forall {X} (l : list X) i d, l <> [] -> length (swap_remove l i d) = (length l - 1)%nat.
Proof.
  intros X l i d NE. unfold swap_remove. rewrite removelast_firstn_len, firstn_length, list_set_length. lia.
Qed.

(* [comment removed for export] *)
Lemma In_list_set : forall {X} (l : list X) i x y, In y (list_set l i x) -> In y l \/ y = x.
Proof.
  intros X l. induction l as [|z r IH]; intros [|i] x y H; cbn in H; try tauto.
  - destruct H as [<-|H]; [right; reflexivity| left; right; exact H].
  - destruct H as [<-|H]; [left; left; reflexivity|]. destruct (IH i x y H); [left; right; assumption| right; assumption].
Qed.
Lemma removelast_incl' : forall {X} (l : list X) x, In x (removelast l) -> In x l.
Proof.
  intros X l. induction l as [|a l IH]; intros x H; [destruct H|]. cbn in H. destruct l as [|b l'].
  - destruct H.
  - destruct H as [<-|H]; [left; reflexivity| right; exact (IH x H)].
Qed.
Lemma swap_remove_incl : forall {X} (l : list X) i d y, l <> [] -> In y (swap_remove l i d) -> In y l.
Proof.
  intros X l i d y NE H. unfold swap_remove in H. apply removelast_incl' in H. apply In_list_set in H as [H| ->]; [exact H|].
  set (y0 := last l d). rewrite (app_removelast_last d NE). apply in_app_iff. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma as_nlive_delete : forall (lm : gmap Z liveinfo) u li, lm !! u = Some li -> as_nlive_ (delete u lm) = as_nlive_ lm - 1.
Proof.
  intros lm u li Hu. unfold as_nlive_.
  pose proof (map_size_delete_Some u lm ltac:(rewrite Hu; eexists; reflexivity)) as SZ.
  destruct (size lm) eqn:SZ0; [| lia]. exfalso. apply map_size_empty_inv in SZ0.
  apply (f_equal (fun m => m !! u)) in SZ0. rewrite lookup_empty in SZ0. rewrite Hu in SZ0. discriminate.
Qed.
Lemma tiny_live_delete : forall (lm : gmap Z liveinfo) u li, lm !! u = Some li -> tiny_live_ (delete u lm) = tiny_live_ lm - is_tiny (li_n li).
Proof.
  intros lm u li Hu. unfold tiny_live_. rewrite (map_fold_delete_L _ _ u li lm); [lia | | exact Hu].
  intros j1 j2 z1 z2 y _ _ _. lia.
Qed.
Lemma as_livebytes_delete' : forall (lm : gmap Z liveinfo) u li, lm !! u = Some li -> as_livebytes_ (delete u lm) = as_livebytes_ lm - li_n li.
Proof. intros lm u li Hu. pose proof (as_livebytes_delete lm u li Hu). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma list_set_nth_error : forall {X} (l : list X) i x j, (i < length l)%nat ->
  nth_error (list_set l i x) j = if Nat.eqb j i then Some x else nth_error l j.
Proof.
  intros X l. induction l as [|y r IH]; intros i x j Hi; cbn in Hi; [lia|].
  destruct i as [|i]; destruct j as [|j]; cbn; try reflexivity. rewrite IH by lia. reflexivity.
Qed.

Lemma nth_error_removelast : forall {X} (l : list X) j, (S j < length l)%nat -> nth_error (removelast l) j = nth_error l j.
Proof.
  intros X l j H. rewrite removelast_firstn_len. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec j (Init.Nat.pred (length l))); [reflexivity| lia].
Qed.

Lemma nth_error_Some_lt : forall {X} (l : list X) n x, nth_error l n = Some x -> (n < length l)%nat.
Proof. intros X l n x H. apply (proj1 (nth_error_Some l n)). rewrite H. discriminate. Qed.

(* [comment removed for export] *)
Lemma swap_remove_in_iff : forall {X} (l : list X) i d x0 y,
  NoDup l -> nth_error l i = Some x0 ->
  (In y (swap_remove l i d) <-> In y l /\ y <> x0).
Proof.
  intros X l i d x0 y ND Hi.
  assert (IL : (i < length l)%nat) by (apply nth_error_Some_lt in Hi; exact Hi).
  assert (NE : l <> []) by (intros ->; destruct i; discriminate Hi).
  set (n := length l).
  assert (LST : nth_error l (n - 1) = Some (last l d)).
  { subst n. rewrite (app_removelast_last d NE) at 1.
    assert (RL : length (removelast l) = (length l - 1)%nat) by (rewrite removelast_firstn_len, firstn_length; lia).
    rewrite nth_error_app2 by lia. rewrite RL. replace (length l - 1 - (length l - 1))%nat with 0%nat by lia. reflexivity. }
  (* [comment removed for export] *)
  assert (INJ : forall a b z, nth_error l a = Some z -> nth_error l b = Some z -> a = b).
  { intros a b z Ha Hb. apply NoDup_ListNoDup in ND. rewrite List.NoDup_nth_error in ND. apply ND; [apply nth_error_Some_lt in Ha; exact Ha|]. rewrite Ha, Hb. reflexivity. }
  unfold swap_remove. split.
  - intros H. apply In_nth_error in H as [j Hj].
    pose proof Hj as Hj'. apply nth_error_Some_lt in Hj'. rewrite removelast_firstn_len, firstn_length, list_set_length in Hj'.
    rewrite nth_error_removelast in Hj by (rewrite list_set_length; lia).
    rewrite list_set_nth_error in Hj by exact IL.
    destruct (Nat.eqb_spec j i) as [EJ|NJ].
    + injection Hj as EY. subst y. split; [eapply nth_error_In; exact LST|]. intros E. rewrite E in LST. pose proof (INJ _ _ _ LST Hi). lia.
    + split; [eapply nth_error_In; exact Hj|]. intros EY. subst y. pose proof (INJ _ _ _ Hj Hi). lia.
  - intros [H NEQ]. apply In_nth_error in H as [j Hj].
    assert (JL : (j < n)%nat) by (apply nth_error_Some_lt in Hj; exact Hj).
    assert (JI : j <> i) by (intros ->; rewrite Hi in Hj; injection Hj; intros ->; exact (NEQ eq_refl)).
    destruct (Nat.eq_dec j (n - 1)) as [EJ|JN].
    + (* [comment removed for export] *)
      rewrite EJ, LST in Hj. injection Hj as EY. subst y.
      apply (nth_error_In _ i). rewrite nth_error_removelast by (rewrite list_set_length; lia).
      rewrite list_set_nth_error by exact IL. rewrite Nat.eqb_refl. reflexivity.
    + apply (nth_error_In _ j). rewrite nth_error_removelast by (rewrite list_set_length; lia).
      rewrite list_set_nth_error by exact IL. destruct (Nat.eqb_spec j i); [lia|]. exact Hj.
Qed.

Lemma swap_remove_nth_error : forall {X} (l : list X) i d j, (i < length l)%nat -> (S j < length l)%nat ->
  nth_error (swap_remove l i d) j = if Nat.eqb j i then Some (last l d) else nth_error l j.
Proof.
  intros X l i d j Hi Hj. unfold swap_remove. rewrite nth_error_removelast by (rewrite list_set_length; lia).
  apply list_set_nth_error. exact Hi.
Qed.
End AQOps.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma quarantined_chunks_def : forall qt qg, quarantined_chunks_ qt qg = map qe_chunk (q_entries qt ++ q_entries qg).
Proof. intros. unfold quarantined_chunks_. rewrite q_entries_app. reflexivity. Qed.

Lemma tiny_quar_def : forall qt qg,
  tiny_quar_ qt qg = Z.of_nat (length (filter (fun e => Z.ltb (qe_n e) 16) (q_entries qt ++ q_entries qg))).
Proof. intros. unfold tiny_quar_. rewrite q_entries_app. reflexivity. Qed.

Lemma filter_app' : forall (l1 l2 : list qentry),
  filter (fun e : qentry => (qe_n e <? 16)%Z) (l1 ++ l2) = filter (fun e : qentry => (qe_n e <? 16)%Z) l1 ++ filter (fun e : qentry => (qe_n e <? 16)%Z) l2.
Proof. intros. apply list.filter_app. Qed.
Lemma filter_tiny_single : forall e, length (filter (fun e : qentry => (qe_n e <? 16)%Z) [e]) = (if (qe_n e <? 16)%Z then 1%nat else 0%nat).
Proof. intros e. cbn. unfold filter; cbn. unfold decide; cbn. destruct (qe_n e <? 16); reflexivity. Qed.

Section PushLast.
  Variables (qt qg : list batch) (e : qentry).
  Hypothesis NE : qt <> [].

  Lemma quarantined_chunks_push_last :
    forall ch, In ch (quarantined_chunks_ (qpush_last qt e) qg) <-> In ch (quarantined_chunks_ qt qg) \/ ch = qe_chunk e.
  Proof.
    intros ch. rewrite !quarantined_chunks_def, (qpush_last_entries qt e NE), !map_app. cbn [map].
    rewrite !in_app_iff. cbn [In]. split.
    - intros [[H|[H|[]]]|H]; [left; left; exact H | right; symmetry; exact H | left; right; exact H].
    - intros [[H|H]|H]; [left; left; exact H | right; exact H | left; right; left; symmetry; exact H].
  Qed.

  Lemma batch_indices_push_last : batch_indices_ (qpush_last qt e) qg = batch_indices_ qt qg.
  Proof. unfold batch_indices_. rewrite !map_app, (qpush_last_indices qt e NE). reflexivity. Qed.

  Lemma tiny_quar_push_last : tiny_quar_ (qpush_last qt e) qg = tiny_quar_ qt qg + is_tiny (qe_n e).
  Proof.
    rewrite !tiny_quar_def, (qpush_last_entries qt e NE), !filter_app', !length_app, filter_tiny_single.
    unfold is_tiny. destruct (qe_n e <? 16); lia.
  Qed.
End PushLast.

Section PushNew.
  Variables (qt qg : list batch) (k : Z) (e : qentry).

  Lemma quarantined_chunks_push_new :
    forall ch, In ch (quarantined_chunks_ (qpush_new qt k e) qg) <-> In ch (quarantined_chunks_ qt qg) \/ ch = qe_chunk e.
  Proof.
    intros ch. rewrite !quarantined_chunks_def, qpush_new_entries, !map_app. cbn [map].
    rewrite !in_app_iff. cbn [In]. split.
    - intros [[H|[H|[]]]|H]; [left; left; exact H | right; symmetry; exact H | left; right; exact H].
    - intros [[H|H]|H]; [left; left; exact H | right; exact H | left; right; left; symmetry; exact H].
  Qed.

  (* [comment removed for export] *)

  Lemma tiny_quar_push_new : tiny_quar_ (qpush_new qt k e) qg = tiny_quar_ qt qg + is_tiny (qe_n e).
  Proof.
    rewrite !tiny_quar_def, qpush_new_entries, !filter_app', !length_app, filter_tiny_single.
    unfold is_tiny. destruct (qe_n e <? 16); lia.
  Qed.
End PushNew.

Section Transfer.
  Variables (qt qg : list batch).
  Lemma quarantined_chunks_transfer :
    forall ch, In ch (quarantined_chunks_ [] (qtransfer qt qg)) <-> In ch (quarantined_chunks_ qt qg).
  Proof.
    intros ch. rewrite !quarantined_chunks_def, qtransfer_entries, !map_app. cbn [q_entries flat_map map app]. rewrite !in_app_iff. tauto.
  Qed.
  Lemma batch_indices_transfer : forall i, In i (batch_indices_ [] (qtransfer qt qg)) <-> In i (batch_indices_ qt qg).
  Proof. intros i. unfold batch_indices_, qtransfer. cbn [app]. rewrite !map_app, !in_app_iff. tauto. Qed.
  Lemma tiny_quar_transfer : tiny_quar_ [] (qtransfer qt qg) = tiny_quar_ qt qg.
  Proof. rewrite !tiny_quar_def, qtransfer_entries. cbn [q_entries flat_map app]. rewrite !filter_app', !length_app. lia. Qed.
  Lemma q_entries_transfer_perm : forall e, In e (q_entries [] ++ q_entries (qtransfer qt qg)) <-> In e (q_entries qt ++ q_entries qg).
  Proof. intros e. rewrite qtransfer_entries. cbn [q_entries flat_map app]. rewrite !in_app_iff. tauto. Qed.
End Transfer.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_app_comm : forall {X} (l1 l2 : list X), NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  intros X l1 l2 H. apply (proj1 (list.NoDup_app _ _)) in H. destruct H as (N1 & DJ & N2).
  apply (proj2 (list.NoDup_app _ _)). split; [exact N2|]. split; [| exact N1].
  intros x Hx2 Hx1. exact (DJ x Hx1 Hx2).
Qed.

Lemma NoDup_snoc : forall {X} (l : list X) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros X l x ND NI. apply (proj2 (list.NoDup_app _ _)). split; [exact ND|]. split.
  - intros y Hy Hyx. apply list_elem_of_In in Hy. apply list_elem_of_In in Hyx. destruct Hyx as [<-|[]]. exact (NI Hy).
  - constructor; [| constructor]. intros H. apply list_elem_of_In in H. destruct H.
Qed.

Lemma map_qe_chunk_snoc : forall l e, map qe_chunk (l ++ [e]) = map qe_chunk l ++ [qe_chunk e].
Proof. intros. rewrite map_app. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WfQuar.
  Variables (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg).
  Variables (u : Z) (li : liveinfo).
  Hypothesis WQ : wf_quarantine_ reg lm qt qg sec.
  Hypothesis LU : lm !! u = Some li.
  Hypothesis WE : wf_qentry_ reg sec (QE (li_chunk li) (li_n li)).
  (* [comment removed for export] *)
  Hypothesis UNIQ : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  Let e := QE (li_chunk li) (li_n li).
  Let lm' := delete u lm.

  (* [comment removed for export] *)

  Lemma live'_not_e : forall u' li', lm' !! u' = Some li' -> li_chunk li' <> li_chunk li.
  Proof.
    intros u' li' H. subst lm'. rewrite lookup_delete_Some in H. destruct H as [NEu H].
    intros E. apply (UNIQ u' li' H); [congruence | symmetry; exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma wf_quarantine_push_last :
    qt <> [] -> Z.of_nat (length (ba_entries (last qt (BA 0 [])))) < kQuarantineBatchCount ->
    q_bytes qt + qe_bytes e <= kQuarantineCacheSize ->
    wf_quarantine_ reg lm' (qpush_last qt e) qg sec.
  Proof.
    intros NE ROOM SZ. destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    pose proof (qt_split qt NE) as SPL.
    assert (Q1' : Forall (wf_batch_ reg sec) (removelast qt) /\ wf_batch_ reg sec (last qt (BA 0 []))).
    { rewrite SPL in Q1. apply Forall_app in Q1 as [A B]. split; [exact A|]. inversion B; assumption. }
    destruct Q1' as [Q1r Q1b].
    unfold wf_quarantine_.
    split; [| split; [exact Q2| split; [| split; [| split; [exact Q5| split; [| split]]]]]].
    - rewrite (qpush_last_shape qt e NE). apply Forall_app. split; [exact Q1r|]. constructor; [| constructor].
      destruct Q1b as (B1 & B2 & B3). split; [| split; [exact B2|]].
      + cbn [ba_entries]. rewrite length_app. cbn [length]. unfold kQuarantineBatchCount in *. lia.
      + cbn [ba_entries]. apply Forall_app. split; [exact B3|]. constructor; [exact WE| constructor].
    - (* [comment removed for export] *)
      intros b Hb. rewrite (qpush_last_shape qt e NE) in Hb. rewrite removelast_app in Hb by discriminate. cbn [removelast] in Hb. rewrite app_nil_r in Hb.
      apply Q3. rewrite SPL. rewrite removelast_app by discriminate. cbn [removelast]. rewrite app_nil_r. exact Hb.
    - rewrite (qpush_last_bytes qt e NE). exact SZ.
    - (* [comment removed for export] *) rewrite (batch_indices_push_last qt qg e NE). exact Q6.
    - (* [comment removed for export] *)
      rewrite quarantined_chunks_def, (qpush_last_entries qt e NE), map_app, map_qe_chunk_snoc. cbn [qe_chunk].
      rewrite quarantined_chunks_def, map_app in Q7. 
      assert (Q8' : ~ In (li_chunk li) (map qe_chunk (q_entries qt) ++ map qe_chunk (q_entries qg))).
      { intros Hin. apply (Q8 u li LU). rewrite quarantined_chunks_def, map_app. exact Hin. }
      apply (proj1 (list.NoDup_app _ _)) in Q7. destruct Q7 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [| split].
      + apply NoDup_snoc; [exact NA|]. intros Hin. apply Q8'. apply in_app_iff. left. exact Hin.
      + intros x Hx HB. apply list_elem_of_In in Hx. apply list_elem_of_In in HB. apply in_app_iff in Hx as [Hx|[<-|[]]].
        * apply (DJ x); apply list_elem_of_In; assumption.
        * apply Q8'. apply in_app_iff. right. exact HB.
      + exact NB.
    - (* [comment removed for export] *)
      intros u' li' H' Hin.
      apply (quarantined_chunks_push_last qt qg e NE) in Hin as [Hin|Eq].
      + subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [_ H']. exact (Q8 u' li' H' Hin).
      + cbn [qe_chunk] in Eq. exact (live'_not_e u' li' H' Eq).
  Qed.

  (* [comment removed for export] *)
  Lemma wf_quarantine_push_new : forall k,
    (qt = [] \/ Z.of_nat (length (ba_entries (last qt (BA 0 [])))) = kQuarantineBatchCount) ->
    0 <= k < carved_count_ reg kQuarantineBatchClass -> ~ In k (batch_indices_ qt qg) ->
    q_bytes qt + kQuarantineBatchBytes + qe_bytes e <= kQuarantineCacheSize ->
    wf_quarantine_ reg lm' (qpush_new qt k e) qg sec.
  Proof.
    intros k FULL KR KNB SZ. destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    unfold wf_quarantine_.
    split; [| split; [exact Q2| split; [| split; [| split; [exact Q5| split; [| split]]]]]].
    - unfold qpush_new. apply Forall_app. split; [exact Q1|]. constructor; [| constructor].
      split; [| split; [exact KR|]].
      + cbn [ba_entries length]. unfold kQuarantineBatchCount. lia.
      + cbn [ba_entries]. constructor; [exact WE| constructor].
    - intros b Hb. unfold qpush_new in Hb. rewrite removelast_app in Hb by discriminate. cbn [removelast] in Hb. rewrite app_nil_r in Hb.
      destruct FULL as [-> | FULL]; [destruct Hb|].
      assert (NE : qt <> []) by (intros ->; destruct Hb).
      rewrite (qt_split qt NE) in Hb. apply in_app_iff in Hb as [Hb|[<-|[]]]; [exact (Q3 b Hb) | exact FULL].
    - rewrite qpush_new_bytes. exact SZ.
    - (* [comment removed for export] *)
      unfold batch_indices_ in *. unfold qpush_new. rewrite <- app_assoc.
      rewrite map_app in Q6 |- *. rewrite map_app. cbn [map].
      apply (proj1 (list.NoDup_app _ _)) in Q6. destruct Q6 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [exact NA| split].
      + intros x Hx Hk. apply list_elem_of_In in Hx. apply list_elem_of_In in Hk. cbn [In] in Hk. destruct Hk as [<-|Hk].
        * apply KNB. rewrite map_app. apply in_app_iff. left. exact Hx.
        * apply (DJ x); apply list_elem_of_In; assumption.
      + constructor; [| exact NB]. intros Hk. apply list_elem_of_In in Hk. apply KNB. rewrite map_app. apply in_app_iff. right. exact Hk.
    - rewrite quarantined_chunks_def, qpush_new_entries, map_app, map_qe_chunk_snoc. cbn [qe_chunk].
      rewrite quarantined_chunks_def, map_app in Q7.
      assert (Q8' : ~ In (li_chunk li) (map qe_chunk (q_entries qt) ++ map qe_chunk (q_entries qg))).
      { intros Hin. apply (Q8 u li LU). rewrite quarantined_chunks_def, map_app. exact Hin. }
      apply (proj1 (list.NoDup_app _ _)) in Q7. destruct Q7 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [| split].
      + apply NoDup_snoc; [exact NA|]. intros Hin. apply Q8'. apply in_app_iff. left. exact Hin.
      + intros x Hx HB. apply list_elem_of_In in Hx. apply list_elem_of_In in HB. apply in_app_iff in Hx as [Hx|[<-|[]]].
        * apply (DJ x); apply list_elem_of_In; assumption.
        * apply Q8'. apply in_app_iff. right. exact HB.
      + exact NB.
    - intros u' li' H' Hin.
      apply (quarantined_chunks_push_new qt qg k e) in Hin as [Hin|Eq].
      + subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [_ H']. exact (Q8 u' li' H' Hin).
      + cbn [qe_chunk] in Eq. exact (live'_not_e u' li' H' Eq).
  Qed.
End WfQuar.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma NoDup_sublist_app_r : forall {X} (l1 l2 : list X), NoDup (l1 ++ l2) -> NoDup l2.
Proof. intros X l1 l2 H. apply (proj1 (list.NoDup_app _ _)) in H. tauto. Qed.

Section WfTransfer.
  Variables (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg).
  Hypothesis WQ : wf_quarantine_ reg lm qt qg sec.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End WfTransfer.

Section WfSplit.
  Variables (reg : Z -> region) (lm : gmap Z liveinfo) (qg : list batch) (sec : secreg) (min : Z).
  Hypothesis WQ1 : Forall (wf_batch_ reg sec) qg.
  Hypothesis WQ6 : NoDup (batch_indices_ [] qg).
  Hypothesis WQ7 : NoDup (quarantined_chunks_ [] qg).
  Hypothesis WQ8 : forall u li, lm !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ [] qg).
  Hypothesis MIN : 0 <= min <= kQuarantineMaxSize.

  Lemma wf_quarantine_rsplit : let (R, rest) := rsplit qg min in wf_quarantine_ reg lm [] rest sec.
  Proof.
    pose proof (rsplit_app qg min) as APP. pose proof (rsplit_rest_small qg min ltac:(lia)) as SM.
    destruct (rsplit qg min) as [R rest]. unfold wf_quarantine_.
    rewrite APP in WQ1, WQ6, WQ7, WQ8.
    split; [constructor|]. split; [apply Forall_app in WQ1; tauto|]. split; [intros b Hb; destruct Hb|].
    split; [rewrite q_bytes_nil; unfold kQuarantineCacheSize; lia|].
    split; [destruct SM as [SM| ->]; [lia| rewrite q_bytes_nil; unfold kQuarantineMaxSize; lia]|].
    split; [| split].
    - unfold batch_indices_ in *. cbn [app] in *. rewrite map_app in WQ6. exact (NoDup_sublist_app_r _ _ WQ6).
    - rewrite quarantined_chunks_def in *. cbn [q_entries flat_map app] in *. rewrite q_entries_app, map_app in WQ7.
      exact (NoDup_sublist_app_r _ _ WQ7).
    - intros u li Hu Hin. apply (WQ8 u li Hu). rewrite quarantined_chunks_def in *. cbn [q_entries flat_map app] in *.
      rewrite q_entries_app, map_app. apply in_app_iff. right. exact Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma rsplit_R_wf : let (R, rest) := rsplit qg min in
    Forall (wf_batch_ reg sec) R /\ NoDup (map ba_idx R ++ map ba_idx rest) /\
    NoDup (map qe_chunk (q_entries R) ++ map qe_chunk (q_entries rest)) /\
    (forall u li, lm !! u = Some li -> ~ In (li_chunk li) (map qe_chunk (q_entries R))).
  Proof.
    pose proof (rsplit_app qg min) as APP. destruct (rsplit qg min) as [R rest].
    rewrite APP in WQ1, WQ6, WQ7, WQ8. unfold batch_indices_ in WQ6. rewrite quarantined_chunks_def in WQ7, WQ8.
    cbn [q_entries flat_map app] in *. rewrite map_app in WQ6. rewrite q_entries_app, map_app in WQ7, WQ8.
    split; [apply Forall_app in WQ1; tauto|]. split; [exact WQ6|]. split; [exact WQ7|].
    intros u li Hu Hin. apply (WQ8 u li Hu). apply in_app_iff. left. exact Hin.
  Qed.
End WfSplit.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WfLiveFree.
  Variables (sb : Z) (reg : Z -> region) (lm : gmap Z liveinfo) (sec : secreg) (u : Z) (li : liveinfo).
  Hypothesis WV : wf_live_ sb reg lm sec.
  Hypothesis LU : lm !! u = Some li.

  Lemma wf_live_delete : wf_live_ sb reg (delete u lm) sec.
  Proof.
    destruct WV as (V1 & V2 & V3). split; [| split].
    - intros u' li' H. rewrite lookup_delete_Some in H. destruct H as [_ H]. exact (V1 u' li' H).
    - intros u1 u2 li1 li2 H1 H2 NE. rewrite lookup_delete_Some in H1, H2. destruct H1 as [_ H1], H2 as [_ H2]. exact (V2 _ _ _ _ H1 H2 NE).
    - rewrite (as_livebytes_delete' lm u li LU). pose proof (V1 u li LU) as (N & _). cbv zeta in N. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma live_chunk_unique : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  Proof. intros u' li' H NE. destruct WV as (_ & V2 & _). exact (V2 u u' li li' LU H NE). Qed.

  (* [comment removed for export] *)
  Lemma wf_qentry_of_live : wf_qentry_ reg sec (QE (li_chunk li) (li_n li)).
  Proof.
    destruct WV as (V1 & _ & _). pose proof (V1 u li LU) as (N & _ & M). cbv zeta in N, M. unfold wf_qentry_. cbn [qe_n qe_chunk].
    split; [lia|]. destruct (li_chunk li) as [[c k]|[mb n0]]; [exact M|]. destruct M as (M1 & M2 & M3). subst n0. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
End WfLiveFree.

Lemma is_tiny_range01 : forall n, 0 <= is_tiny n <= 1.
Proof. intros n. unfold is_tiny. destruct (Z.ltb n 16); lia. Qed.

Section WfBudgetFree.
  Variables (tiny : Z) (lm : gmap Z liveinfo) (qt qg : list batch) (u : Z) (li : liveinfo).
  Hypothesis WB : wf_budget_ tiny lm qt qg.
  Hypothesis LU : lm !! u = Some li.
  Hypothesis LBN : 0 <= li_n li.   (* [comment removed for export] *)
  Hypothesis LBNN : li_n li <= as_livebytes_ lm.  (* [comment removed for export] *)

  Lemma wf_budget_free_push_last : qt <> [] ->
    wf_budget_ tiny (delete u lm) (qpush_last qt (QE (li_chunk li) (li_n li))) qg.
  Proof.
    intros NE. destruct WB as (B1 & B2 & B3 & B4 & B5). unfold wf_budget_.
    rewrite (as_livebytes_delete' lm u li LU), (as_nlive_delete lm u li LU), (tiny_live_delete lm u li LU), (tiny_quar_push_last qt qg _ NE).
    cbn [qe_n]. pose proof (is_tiny_range01 (li_n li)) as IT.
    split; [exact B1|]. split; [lia|]. split; [lia|]. split; [| lia].
    (* [comment removed for export] *)
    pose proof (tiny_live_delete lm u li LU) as TD.
    assert (TLN : forall (l : gmap Z liveinfo), 0 <= tiny_live_ l).
    { intros l. unfold tiny_live_. apply (map_fold_weak_ind (fun r _ => 0 <= r)); [lia|]. intros i x mm r _ Hr. pose proof (is_tiny_range01 (li_n x)). lia. }
    pose proof (TLN (delete u lm)). lia.
  Qed.

  Lemma wf_budget_free_push_new : forall k,
    wf_budget_ tiny (delete u lm) (qpush_new qt k (QE (li_chunk li) (li_n li))) qg.
  Proof.
    intros k. destruct WB as (B1 & B2 & B3 & B4 & B5). unfold wf_budget_.
    rewrite (as_livebytes_delete' lm u li LU), (as_nlive_delete lm u li LU), (tiny_live_delete lm u li LU), (tiny_quar_push_new qt qg k _).
    cbn [qe_n]. pose proof (is_tiny_range01 (li_n li)) as IT.
    split; [exact B1|]. split; [lia|]. split; [lia|]. split; [| lia].
    assert (TLN : forall (l : gmap Z liveinfo), 0 <= tiny_live_ l).
    { intros l. unfold tiny_live_. apply (map_fold_weak_ind (fun r _ => 0 <= r)); [lia|]. intros i x mm r _ Hr. pose proof (is_tiny_range01 (li_n x)). lia. }
    pose proof (TLN (delete u lm)). pose proof (tiny_live_delete lm u li LU). lia.
  Qed.
End WfBudgetFree.

Section WfSecFree.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (L : alayout) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg) (u : Z) (li : liveinfo).   (* [comment removed for export] *)
  Hypothesis WS : wf_sec_ L lm qt qg sec.
  Hypothesis LU : lm !! u = Some li.
  Hypothesis UNIQ : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  (* [comment removed for export] *)
  Hypothesis LSHAPE : forall s, li_chunk li = ChS s -> li_n li = cs_n s.

  Lemma wf_sec_free_gen : forall qt',
    (forall ch, In ch (quarantined_chunks_ qt' qg) <-> In ch (quarantined_chunks_ qt qg) \/ ch = li_chunk li) ->
    wf_sec_ L (delete u lm) qt' qg sec.
  Proof.
    intros qt' QC. destruct WS as (S1 & S2 & S3 & S4 & S5). unfold wf_sec_.
    split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
    intros s Hs. destruct (S5 s Hs) as [(u0 & Hu0)|Hq].
    - destruct (decide (u0 = u)) as [->|NE].
      + right. apply QC. right. rewrite LU in Hu0. injection Hu0 as E. rewrite E. reflexivity.
      + left. exists u0. rewrite lookup_delete_Some. split; [congruence| exact Hu0].
    - right. apply QC. left. exact Hq.
  Qed.

  Lemma wf_sec_free_push_last : qt <> [] -> wf_sec_ L (delete u lm) (qpush_last qt (QE (li_chunk li) (li_n li))) qg sec.
  Proof. intros NE. apply wf_sec_free_gen. intros ch. rewrite (quarantined_chunks_push_last qt qg _ NE). cbn [qe_chunk]. tauto. Qed.
  Lemma wf_sec_free_push_new : forall k, wf_sec_ L (delete u lm) (qpush_new qt k (QE (li_chunk li) (li_n li))) qg sec.
  Proof. intros k. apply wf_sec_free_gen. intros ch. rewrite (quarantined_chunks_push_new qt qg k _). cbn [qe_chunk]. tauto. Qed.
End WfSecFree.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wf_quarantineB (B : Z) (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg) : Prop :=
    Forall (wf_batch_ reg sec) qt /\ Forall (wf_batch_ reg sec) qg /\
    (forall b, In b (removelast qt) -> Z.of_nat (length (ba_entries b)) = kQuarantineBatchCount) /\
    q_bytes qt <= B /\ q_bytes qg <= kQuarantineMaxSize /\
    NoDup (batch_indices_ qt qg) /\ NoDup (quarantined_chunks_ qt qg) /\
    (forall u li, lm !! u = Some li -> ~ In (li_chunk li) (quarantined_chunks_ qt qg)).

Section WfQuarB.
  Variables (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg).
  Variables (u : Z) (li : liveinfo).
  Hypothesis WQ : wf_quarantine_ reg lm qt qg sec.
  Hypothesis LU : lm !! u = Some li.
  Hypothesis WE : wf_qentry_ reg sec (QE (li_chunk li) (li_n li)).
  Hypothesis UNIQ : forall u' li', lm !! u' = Some li' -> u <> u' -> li_chunk li <> li_chunk li'.
  Let e := QE (li_chunk li) (li_n li).
  Let lm' := delete u lm.

  Lemma wf_quarantine_push_lastB :
    qt <> [] -> Z.of_nat (length (ba_entries (last qt (BA 0 [])))) < kQuarantineBatchCount ->
    wf_quarantineB (q_bytes qt + qe_bytes e) reg lm' (qpush_last qt e) qg sec.
  Proof.
    intros NE ROOM. destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    pose proof (qt_split qt NE) as SPL.
    assert (Q1' : Forall (wf_batch_ reg sec) (removelast qt) /\ wf_batch_ reg sec (last qt (BA 0 []))).
    { rewrite SPL in Q1. apply Forall_app in Q1 as [A B]. split; [exact A|]. inversion B; assumption. }
    destruct Q1' as [Q1r Q1b].
    unfold wf_quarantineB.
    split; [| split; [exact Q2| split; [| split; [| split; [exact Q5| split; [| split]]]]]].
    - rewrite (qpush_last_shape qt e NE). apply Forall_app. split; [exact Q1r|]. constructor; [| constructor].
      destruct Q1b as (B1 & B2 & B3). split; [| split; [exact B2|]].
      + cbn [ba_entries]. rewrite length_app. cbn [length]. unfold kQuarantineBatchCount in *. lia.
      + cbn [ba_entries]. apply Forall_app. split; [exact B3|]. constructor; [exact WE| constructor].
    - intros b Hb. rewrite (qpush_last_shape qt e NE) in Hb. rewrite removelast_app in Hb by discriminate. cbn [removelast] in Hb. rewrite app_nil_r in Hb.
      apply Q3. rewrite SPL. rewrite removelast_app by discriminate. cbn [removelast]. rewrite app_nil_r. exact Hb.
    - rewrite (qpush_last_bytes qt e NE). lia.
    - rewrite (batch_indices_push_last qt qg e NE). exact Q6.
    - rewrite quarantined_chunks_def, (qpush_last_entries qt e NE), map_app, map_qe_chunk_snoc. cbn [qe_chunk].
      rewrite quarantined_chunks_def, map_app in Q7.
      assert (Q8' : ~ In (li_chunk li) (map qe_chunk (q_entries qt) ++ map qe_chunk (q_entries qg))).
      { intros Hin. apply (Q8 u li LU). rewrite quarantined_chunks_def, map_app. exact Hin. }
      apply (proj1 (list.NoDup_app _ _)) in Q7. destruct Q7 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [| split].
      + apply NoDup_snoc; [exact NA|]. intros Hin. apply Q8'. apply in_app_iff. left. exact Hin.
      + intros x Hx HB. apply list_elem_of_In in Hx. apply list_elem_of_In in HB. apply in_app_iff in Hx as [Hx|[<-|[]]].
        * apply (DJ x); apply list_elem_of_In; assumption.
        * apply Q8'. apply in_app_iff. right. exact HB.
      + exact NB.
    - intros u' li' H' Hin.
      apply (quarantined_chunks_push_last qt qg e NE) in Hin as [Hin|Eq].
      + subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [_ H']. exact (Q8 u' li' H' Hin).
      + cbn [qe_chunk] in Eq. subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [NEu H']. exact (UNIQ u' li' H' ltac:(congruence) (eq_sym Eq)).
  Qed.

  Lemma wf_quarantine_push_newB : forall k,
    (qt = [] \/ Z.of_nat (length (ba_entries (last qt (BA 0 [])))) = kQuarantineBatchCount) ->
    0 <= k < carved_count_ reg kQuarantineBatchClass -> ~ In k (batch_indices_ qt qg) ->
    wf_quarantineB (q_bytes qt + kQuarantineBatchBytes + qe_bytes e) reg lm' (qpush_new qt k e) qg sec.
  Proof.
    intros k FULL KR KNB. destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    unfold wf_quarantineB.
    split; [| split; [exact Q2| split; [| split; [| split; [exact Q5| split; [| split]]]]]].
    - unfold qpush_new. apply Forall_app. split; [exact Q1|]. constructor; [| constructor].
      split; [| split; [exact KR|]].
      + cbn [ba_entries length]. unfold kQuarantineBatchCount. lia.
      + cbn [ba_entries]. constructor; [exact WE| constructor].
    - intros b Hb. unfold qpush_new in Hb. rewrite removelast_app in Hb by discriminate. cbn [removelast] in Hb. rewrite app_nil_r in Hb.
      destruct FULL as [-> | FULL]; [destruct Hb|].
      assert (NE : qt <> []) by (intros ->; destruct Hb).
      rewrite (qt_split qt NE) in Hb. apply in_app_iff in Hb as [Hb|[<-|[]]]; [exact (Q3 b Hb) | exact FULL].
    - rewrite qpush_new_bytes. lia.
    - unfold batch_indices_ in *. unfold qpush_new. rewrite <- app_assoc.
      rewrite map_app in Q6 |- *. rewrite map_app. cbn [map].
      apply (proj1 (list.NoDup_app _ _)) in Q6. destruct Q6 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [exact NA| split].
      + intros x Hx Hk. apply list_elem_of_In in Hx. apply list_elem_of_In in Hk. cbn [In] in Hk. destruct Hk as [<-|Hk].
        * apply KNB. rewrite map_app. apply in_app_iff. left. exact Hx.
        * apply (DJ x); apply list_elem_of_In; assumption.
      + constructor; [| exact NB]. intros Hk. apply list_elem_of_In in Hk. apply KNB. rewrite map_app. apply in_app_iff. right. exact Hk.
    - rewrite quarantined_chunks_def, qpush_new_entries, map_app, map_qe_chunk_snoc. cbn [qe_chunk].
      rewrite quarantined_chunks_def, map_app in Q7.
      assert (Q8' : ~ In (li_chunk li) (map qe_chunk (q_entries qt) ++ map qe_chunk (q_entries qg))).
      { intros Hin. apply (Q8 u li LU). rewrite quarantined_chunks_def, map_app. exact Hin. }
      apply (proj1 (list.NoDup_app _ _)) in Q7. destruct Q7 as (NA & DJ & NB).
      apply (proj2 (list.NoDup_app _ _)). split; [| split].
      + apply NoDup_snoc; [exact NA|]. intros Hin. apply Q8'. apply in_app_iff. left. exact Hin.
      + intros x Hx HB. apply list_elem_of_In in Hx. apply list_elem_of_In in HB. apply in_app_iff in Hx as [Hx|[<-|[]]].
        * apply (DJ x); apply list_elem_of_In; assumption.
        * apply Q8'. apply in_app_iff. right. exact HB.
      + exact NB.
    - intros u' li' H' Hin.
      apply (quarantined_chunks_push_new qt qg k e) in Hin as [Hin|Eq].
      + subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [_ H']. exact (Q8 u' li' H' Hin).
      + cbn [qe_chunk] in Eq. subst lm'. rewrite lookup_delete_Some in H'. destruct H' as [NEu H']. exact (UNIQ u' li' H' ltac:(congruence) (eq_sym Eq)).
  Qed.
End WfQuarB.

Section WfTransferB.
  Variables (B : Z) (reg : Z -> region) (lm : gmap Z liveinfo) (qt qg : list batch) (sec : secreg).
  Hypothesis WQ : wf_quarantineB B reg lm qt qg sec.
  Lemma wf_quarantine_transferB :
    q_bytes qg + q_bytes qt <= kQuarantineMaxSize ->
    wf_quarantine_ reg lm [] (qtransfer qt qg) sec.
  Proof.
    intros SZ. destruct WQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). unfold wf_quarantine_, qtransfer.
    split; [constructor|]. split; [apply Forall_app; split; assumption|]. split; [intros b Hb; destruct Hb|].
    split; [rewrite q_bytes_nil; unfold kQuarantineCacheSize; lia|]. split; [rewrite q_bytes_app; exact SZ|].
    split; [| split].
    - unfold batch_indices_ in *. cbn [app]. rewrite map_app. apply NoDup_app_comm. rewrite <- map_app. exact Q6.
    - rewrite quarantined_chunks_def in *. cbn [q_entries flat_map app]. rewrite q_entries_app, map_app. apply NoDup_app_comm.
      rewrite <- map_app. exact Q7.
    - intros u li Hu Hin. apply (Q8 u li Hu). apply (quarantined_chunks_transfer qt qg). exact Hin.
  Qed.
End WfTransferB.
