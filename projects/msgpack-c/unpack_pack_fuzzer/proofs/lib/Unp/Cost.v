(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Fixpoint obj_bodies (o : obj) : Z :=
  match o with
  | OStr _ n | OBin _ n => n
  | OExt _ n => n + 1
  | OArr _ kids | OMap _ kids => (fix sum (l : list obj) : Z := match l with [] => 0 | o' :: l' => obj_bodies o' + sum l' end) kids
  | _ => 0
  end.
Definition objs_bodies (l : list obj) : Z := fold_right (fun o acc => obj_bodies o + acc) 0 l.
Lemma sumfix_objs_bodies : forall kids, (fix sum (l : list obj) : Z := match l with [] => 0 | o' :: l' => obj_bodies o' + sum l' end) kids = objs_bodies kids.
Proof. induction kids as [|o l IH]; [reflexivity|]. cbn [objs_bodies fold_right]. rewrite IH. reflexivity. Qed.
Lemma obj_bodies_arr : forall p kids, obj_bodies (OArr p kids) = objs_bodies kids.
Proof. intros p kids. cbn [obj_bodies]. apply sumfix_objs_bodies. Qed.
Lemma obj_bodies_map : forall p kids, obj_bodies (OMap p kids) = objs_bodies kids.
Proof. intros p kids. cbn [obj_bodies]. apply sumfix_objs_bodies. Qed.

Fixpoint obj_depth (o : obj) : nat :=
  match o with
  | OArr _ kids | OMap _ kids => S (fold_right (fun o' acc => Nat.max (obj_depth o') acc) 0%nat kids)
  | _ => 1%nat
  end.
Definition objs_depth (l : list obj) : nat := fold_right (fun o' acc => Nat.max (obj_depth o') acc) 0%nat l.
Lemma obj_depth_arr : forall p kids, obj_depth (OArr p kids) = S (objs_depth kids). Proof. reflexivity. Qed.
Lemma obj_depth_map : forall p kids, obj_depth (OMap p kids) = S (objs_depth kids). Proof. reflexivity. Qed.

Definition tree_cost (o : obj) : Z := Z.of_nat (obj_size o) + obj_bodies o.
Definition trees_cost (l : list obj) : Z := Z.of_nat (objs_size l) + objs_bodies l.

Lemma obj_bodies_wf_nonneg : forall m z o, tree_wf m z o -> 0 <= obj_bodies o.
Proof.
  intros m z. apply (obj_ind_size (fun o => tree_wf m z o -> 0 <= obj_bodies o)). intros o IH H.
  destruct o; try (cbn [obj_bodies]; lia).
  - cbn [tree_wf obj_bodies] in H |- *. lia. - cbn [tree_wf obj_bodies] in H |- *. lia. - cbn [tree_wf obj_bodies] in H |- *. lia.
  - change (0 <= obj_bodies (OArr p kids)). rewrite obj_bodies_arr. cbn [tree_wf] in H.
    assert (K : forall o', In o' kids -> tree_wf m z o').
    { destruct H as (_ & _ & _ & Hk). clear -Hk. induction kids as [|x l IHl]; [intros o' []|]. cbn in Hk. destruct Hk as [Hx Hl].
      intros o' [<-|Ho']; [exact Hx| apply IHl; assumption]. }
    assert (IH' : forall o', In o' kids -> 0 <= obj_bodies o').
    { intros o' Ho'. apply IH; [|apply K; exact Ho']. rewrite obj_size_arr. pose proof (in_kids_size o' kids Ho'). lia. }
    clear -IH'. induction kids as [|x l IHl]; cbn [objs_bodies fold_right]; [lia|].
    pose proof (IH' x ltac:(now left)). assert (0 <= objs_bodies l) by (apply IHl; intros o' Ho'; apply IH'; now right). unfold objs_bodies in *. lia.
  - change (0 <= obj_bodies (OMap p kids)). rewrite obj_bodies_map. cbn [tree_wf] in H.
    assert (K : forall o', In o' kids -> tree_wf m z o').
    { destruct H as (_ & _ & _ & _ & Hk). clear -Hk. induction kids as [|x l IHl]; [intros o' []|]. cbn in Hk. destruct Hk as [Hx Hl].
      intros o' [<-|Ho']; [exact Hx| apply IHl; assumption]. }
    assert (IH' : forall o', In o' kids -> 0 <= obj_bodies o').
    { intros o' Ho'. apply IH; [|apply K; exact Ho']. rewrite obj_size_map. pose proof (in_kids_size o' kids Ho'). lia. }
    clear -IH'. induction kids as [|x l IHl]; cbn [objs_bodies fold_right]; [lia|].
    pose proof (IH' x ltac:(now left)). assert (0 <= objs_bodies l) by (apply IHl; intros o' Ho'; apply IH'; now right). unfold objs_bodies in *. lia.
Qed.
Lemma tree_cost_arr : forall p kids, tree_cost (OArr p kids) = 1 + trees_cost kids.
Proof. intros. unfold tree_cost, trees_cost. rewrite obj_size_arr, obj_bodies_arr. lia. Qed.
Lemma tree_cost_map : forall p kids, tree_cost (OMap p kids) = 1 + trees_cost kids.
Proof. intros. unfold tree_cost, trees_cost. rewrite obj_size_map, obj_bodies_map. lia. Qed.
Lemma trees_cost_app : forall l1 l2, trees_cost (l1 ++ l2) = trees_cost l1 + trees_cost l2.
Proof.
  intros l1 l2. unfold trees_cost, objs_size, objs_bodies. rewrite map_app, list_sum_app, fold_right_app.
  assert (E : forall a, fold_right (fun o acc => obj_bodies o + acc) a l1 = fold_right (fun o acc => obj_bodies o + acc) 0 l1 + a).
  { induction l1 as [|x l IH]; intros a; cbn [fold_right]; [lia|]. rewrite IH. lia. }
  rewrite E. lia.
Qed.
Lemma objs_depth_app : forall l1 l2, objs_depth (l1 ++ l2) = Nat.max (objs_depth l1) (objs_depth l2).
Proof. intros l1 l2. unfold objs_depth. rewrite fold_right_app. induction l1 as [|x l IH]; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.
