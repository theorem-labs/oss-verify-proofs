(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps Cost Tree PkOps PkLib.
Import ListNotations.
Import PK PKL.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkCost.

Lemma pk10_list_nil : pk10_list [] = 0. Proof. reflexivity. Qed.
Lemma pk10_list_cons : forall o l, pk10_list (o :: l) = pk10_tree o + pk10_list l.
Proof.
  intros o l. unfold pk10_list, pk10_tree.
  assert (E1 : objs_size (o :: l) = (obj_size o + objs_size l)%nat) by reflexivity.
  assert (E2 : Cost.objs_bodies (o :: l) = Cost.obj_bodies o + Cost.objs_bodies l) by reflexivity.
  rewrite E1, E2, Nat2Z.inj_add. lia.
Qed.

Lemma pk10_tree_split : forall o, pk10_tree o = own10 o + desc10 o.
Proof.
  intros o. unfold desc10, pk10_list, pk10_tree.
  destruct o as [| b| u| i| bits| bits| p n| p n| p n| p kids| p kids];
    try (cbn [okids own10 obj_size Cost.obj_bodies objs_size map list_sum Cost.objs_bodies fold_right]; lia).
  - rewrite Cost.obj_bodies_arr, obj_size_arr. cbn [okids own10]. rewrite Nat2Z.inj_succ. lia.
  - rewrite Cost.obj_bodies_map, obj_size_map. cbn [okids own10]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma pk10_tree_nonneg : forall bm z o, tree_wf bm z o -> 0 <= pk10_tree o.
Proof. intros bm z o H. unfold pk10_tree. pose proof (Cost.obj_bodies_wf_nonneg bm z o H). lia. Qed.
Lemma kids_wf : forall bm z o k, tree_wf bm z o -> In k (okids o) -> tree_wf bm z k.
Proof.
  intros bm z o k H Hk. destruct o; cbn [okids] in Hk; try contradiction; cbn [tree_wf] in H.
  - destruct H as (_ & _ & _ & W). revert W Hk. induction kids as [|x l IH]; intros W Hk; [destruct Hk|]. destruct W as [W1 W2]. destruct Hk as [<-|Hk]; [exact W1| exact (IH W2 Hk)].
  - destruct H as (_ & _ & _ & _ & W). revert W Hk. induction kids as [|x l IH]; intros W Hk; [destruct Hk|]. destruct W as [W1 W2]. destruct Hk as [<-|Hk]; [exact W1| exact (IH W2 Hk)].
Qed.
Lemma pk10_list_nonneg : forall bm z l, (forall k, In k l -> tree_wf bm z k) -> 0 <= pk10_list l.
Proof.
  intros bm z l. induction l as [|o l IH]; intros H; [rewrite pk10_list_nil; lia|]. rewrite pk10_list_cons.
  pose proof (pk10_tree_nonneg bm z o (H o (or_introl eq_refl))). specialize (IH (fun k Hk => H k (or_intror Hk))). lia.
Qed.
Lemma skipn_In' : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. induction n as [|n IH]; intros l x H; [exact H|]. destruct l as [|a l]; [exact H|]. right. exact (IH l x H). Qed.
Lemma ahead10_nonneg : forall bm z l, tree_wf bm z (fst l) -> 0 <= ahead10 l.
Proof. intros bm z l H. unfold ahead10. apply (pk10_list_nonneg bm z). intros k Hk. exact (kids_wf bm z _ k H (skipn_In' _ _ _ Hk)). Qed.
Lemma desc10_nonneg : forall bm z o, tree_wf bm z o -> 0 <= desc10 o.
Proof. intros bm z o H. unfold desc10. apply (pk10_list_nonneg bm z). intros k Hk. exact (kids_wf bm z o k H Hk). Qed.
Lemma focus_term_nonneg : forall bm z fo fr cz, (forall o, fo = Some o -> tree_wf bm z o) -> 0 <= focus_term fo fr cz.
Proof.
  intros bm z [o|] fr cz H; cbn [focus_term]; [| lia]. specialize (H o eq_refl).
  destruct fr; [exact (pk10_tree_nonneg bm z o H)|]. destruct cz; [lia| exact (desc10_nonneg bm z o H)].
Qed.

Lemma np_strict_app : forall l1 l2, np_strict (l1 ++ l2) = np_strict l1 + np_strict l2.
Proof. induction l1 as [|x l1 IH]; intros l2; [reflexivity|]. cbn [app np_strict fold_right]. fold (np_strict (l1 ++ l2)). fold (np_strict l1). rewrite IH. lia. Qed.
Lemma np_strict_one : forall l, np_strict [l] = ahead10 l. Proof. intros l. cbn. lia. Qed.
Lemma np_strict_nonneg : forall bm z ls, Forall (fun l => tree_wf bm z (fst l)) ls -> 0 <= np_strict ls.
Proof.
  intros bm z ls H. induction H as [|l ls Hl _ IH]; [cbn; lia|]. cbn [np_strict fold_right]. fold (np_strict ls).
  pose proof (ahead10_nonneg bm z l Hl). lia.
Qed.

Lemma focus_node_snoc : forall t ls l, focus_node t (ls ++ [l]) = lev_node l.
Proof. intros t ls l. unfold focus_node. rewrite Steps.last_opt_snoc. reflexivity. Qed.
Lemma np_snoc : forall t ls l fr cz, np t (ls ++ [l]) fr cz = np_strict ls + ahead10 l + focus_term (lev_node l) fr cz.
Proof.
  intros t ls l fr cz. unfold np. rewrite focus_node_snoc, np_strict_app, np_strict_one.
  destruct (ls ++ [l]) eqn:X; [destruct ls; discriminate| lia].
Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof. induction l as [|a l IH]; intros n x H; destruct n; try discriminate; cbn in *; [injection H as ->; reflexivity| exact (IH n x H)]. Qed.

Lemma enter_eq : forall k, ahead10 (k, 0) + focus_term (lev_node (k, 0)) true true = desc10 k.
Proof.
  intros k. unfold ahead10, desc10, lev_node. cbn [fst snd]. change (Z.to_nat 0) with 0%nat.
  destruct (okids k) as [|k0 ks] eqn:K.
  - change (skipn 1 (@nil obj)) with (@nil obj). cbn [nth_error focus_term]. rewrite pk10_list_nil. lia.
  - change (skipn 1 (k0 :: ks)) with ks. cbn [nth_error focus_term]. rewrite pk10_list_cons. lia.
Qed.

Lemma np_push0 : forall t fr cz, np t [(t, 0)] true true = np t [] fr cz.
Proof. intros t fr cz. rewrite (np_snoc t [] (t, 0)). cbn [np np_strict fold_right]. pose proof (enter_eq t). lia. Qed.

Lemma np_push : forall t ls l k, lev_node l = Some k -> np t ((ls ++ [l]) ++ [(k, 0)]) true true = np t (ls ++ [l]) false false.
Proof.
  intros t ls l k HN. rewrite (np_snoc t (ls ++ [l]) (k, 0)), (np_snoc t ls l), np_strict_app, np_strict_one, HN. cbn [focus_term].
  pose proof (enter_eq k). lia.
Qed.

Lemma np_next : forall bm z t ls c s k fr cz, 0 <= s -> nth_error (okids c) (Z.to_nat (s + 1)) = Some k ->
  (forall o, lev_node (c, s) = Some o -> tree_wf bm z o) ->
  np t (ls ++ [(c, s + 1)]) true true <= np t (ls ++ [(c, s)]) fr cz.
Proof.
  intros bm z t ls c s k fr cz Hs N W. rewrite !np_snoc. unfold lev_node at 1. cbn [fst snd]. rewrite N. cbn [focus_term].
  assert (A : ahead10 (c, s + 1) + pk10_tree k = ahead10 (c, s)).
  { unfold ahead10. cbn [fst snd]. replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) in * by lia. rewrite (skipn_nth_cons _ _ _ N), pk10_list_cons. lia. }
  pose proof (focus_term_nonneg bm z (lev_node (c, s)) fr cz W). lia.
Qed.

Lemma np_pop : forall bm z t ls lp l fr cz, tree_wf bm z (fst l) -> (forall o, lev_node l = Some o -> tree_wf bm z o) ->
  np t (ls ++ [lp]) false true <= np t ((ls ++ [lp]) ++ [l]) fr cz.
Proof.
  intros bm z t ls lp l fr cz WL WF. rewrite (np_snoc t (ls ++ [lp]) l), (np_snoc t ls lp), np_strict_app, np_strict_one.
  assert (F0 : focus_term (lev_node lp) false true = 0) by (destruct (lev_node lp); reflexivity). rewrite F0.
  pose proof (ahead10_nonneg bm z l WL). pose proof (focus_term_nonneg bm z (lev_node l) fr cz WF). lia.
Qed.

Lemma np_peek : forall t ls l fo, lev_node l = Some fo -> np t (ls ++ [l]) true true = own10 fo + np t (ls ++ [l]) false false.
Proof. intros t ls l fo HN. rewrite !np_snoc, HN. cbn [focus_term]. rewrite (pk10_tree_split fo). lia. Qed.

Lemma np_fresh_cz : forall t ls cz cz', np t ls true cz = np t ls true cz'.
Proof. intros t ls cz cz'. unfold np. destruct ls; [reflexivity|]. destruct (focus_node t (p :: ls)); reflexivity. Qed.

Lemma own10_nonneg : forall bm z o, tree_wf bm z o -> 0 <= own10 o.
Proof. intros bm z o H. destruct o; cbn [own10]; try lia; cbn [tree_wf] in H; lia. Qed.
Lemma np_peek_bound : forall bm z t ls l fo cz cz' v, lev_node l = Some fo -> tree_wf bm z fo -> Forall (fun l => tree_wf bm z (fst l)) (ls ++ [l]) ->
  np t (ls ++ [l]) true cz <= v -> 0 <= own10 fo <= v /\ 0 <= np t (ls ++ [l]) false cz' <= v - own10 fo.
Proof.
  intros bm z t ls l fo cz cz' v HN TW FA LE. rewrite (np_fresh_cz t (ls ++ [l]) cz true), (np_peek t ls l fo HN) in LE.
  apply Forall_app in FA as [FA1 FA2]. apply Forall_inv in FA2.
  pose proof (own10_nonneg bm z fo TW) as O. pose proof (np_strict_nonneg bm z ls FA1) as S. pose proof (ahead10_nonneg bm z l FA2) as A.
  pose proof (desc10_nonneg bm z fo TW) as D.
  rewrite !np_snoc, HN in *. cbn [focus_term] in *. destruct cz'; lia.
Qed.

End PkCost.
