(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition toff (t : tree_id) : Z := match t with TL => 212 | TD => 2504 | TB => 2748 end.
Definition tsize (t : tree_id) : Z := match t with TL => 573 | TD => 61 | TB => 39 end.

Lemma toff_tsize : forall t, 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573.
Proof. intros [| |]; cbn; lia. Qed.

Definition tree_lens (s : deflate_state) : Prop :=
  arr_len (ds_dyn_ltree_fc s) = 573 /\ arr_len (ds_dyn_ltree_dl s) = 573
  /\ arr_len (ds_dyn_dtree_fc s) = 61 /\ arr_len (ds_dyn_dtree_dl s) = 61
  /\ arr_len (ds_bl_tree_fc s) = 39 /\ arr_len (ds_bl_tree_dl s) = 39
  /\ arr_len (ds_bl_count s) = 16 /\ arr_len (ds_heap s) = 573 /\ arr_len (ds_depth s) = 573.

Lemma tree_lens_fc : forall s t, tree_lens s -> arr_len (tree_fc s t) = tsize t.
Proof. intros s [| |] H; unfold tree_lens in H; cbn; tauto. Qed.
Lemma tree_lens_dl : forall s t, tree_lens s -> arr_len (tree_dl s t) = tsize t.
Proof. intros s [| |] H; unfold tree_lens in H; cbn; tauto. Qed.

Lemma tree_lens_heap_set : forall s i v, tree_lens s -> tree_lens (heap_set s i v).
Proof. intros s i v H. unfold tree_lens, heap_set in *. dsred. rewrite arr_len_set. exact H. Qed.
Lemma tree_lens_depth_set : forall s i v, tree_lens s -> tree_lens (depth_set s i v).
Proof. intros s i v H. unfold tree_lens, depth_set in *. dsred. rewrite arr_len_set. exact H. Qed.
Lemma tree_lens_bl_count_set : forall s i v, tree_lens s -> tree_lens (bl_count_set s i v).
Proof. intros s i v H. unfold tree_lens, bl_count_set in *. dsred. rewrite arr_len_set. exact H. Qed.
Lemma tree_lens_set_fc : forall s t a, tree_lens s -> arr_len a = tsize t -> tree_lens (set_tree_fc s t a).
Proof. intros s [| |] a H Ha; unfold tree_lens in *; cbn [set_tree_fc tsize] in *; dsred; rewrite Ha; tauto. Qed.
Lemma tree_lens_set_dl : forall s t a, tree_lens s -> arr_len a = tsize t -> tree_lens (set_tree_dl s t a).
Proof. intros s [| |] a H Ha; unfold tree_lens in *; cbn [set_tree_dl tsize] in *; dsred; rewrite Ha; tauto. Qed.



Lemma set_heap_twice : forall s a b, set_heap (set_heap s a) b = set_heap s b.
Proof. intros. reflexivity. Qed.
Lemma set_heap_self : forall s, set_heap s (ds_heap s) = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma ds_heap_set_heap : forall s h, ds_heap (set_heap s h) = h.
Proof. intros. reflexivity. Qed.
Lemma heap_set_shape : forall s i v, heap_set s i v = set_heap s (arr_set (ds_heap s) i v).
Proof. intros. reflexivity. Qed.

Lemma sh_tree_fc : forall s h t, tree_fc (set_heap s h) t = tree_fc s t.
Proof. intros s h [| |]; reflexivity. Qed.
Lemma sh_tree_dl : forall s h t, tree_dl (set_heap s h) t = tree_dl s t.
Proof. intros s h [| |]; reflexivity. Qed.
Lemma sh_Freq : forall s h t n, Freq (set_heap s h) t n = Freq s t n.
Proof. intros. unfold Freq. rewrite sh_tree_fc. reflexivity. Qed.
Lemma sh_depth : forall s h, ds_depth (set_heap s h) = ds_depth s.
Proof. intros. reflexivity. Qed.
Lemma sh_depth_get : forall s h n, depth_get (set_heap s h) n = depth_get s n.
Proof. intros. reflexivity. Qed.
Lemma sh_heap_len : forall s h, ds_heap_len (set_heap s h) = ds_heap_len s.
Proof. intros. reflexivity. Qed.
Lemma sh_heap_max : forall s h, ds_heap_max (set_heap s h) = ds_heap_max s.
Proof. intros. reflexivity. Qed.
Lemma sh_smaller : forall s h t n m, smaller (set_heap s h) t n m = smaller s t n m.
Proof. intros. unfold smaller. rewrite !sh_Freq, !sh_depth_get. reflexivity. Qed.
Lemma sh_heap_get : forall s h i, heap_get (set_heap s h) i = arr_get h i.
Proof. intros. reflexivity. Qed.

Lemma heap_get_heap_set : forall s i v j,
  0 <= i < arr_len (ds_heap s) ->
  heap_get (heap_set s i v) j = if i =? j then v else heap_get s j.
Proof.
  intros s i v j Hi. unfold heap_get, heap_set. dsred. rewrite arr_get_set. unfold arr_inb.
  destruct (Z.eqb_spec i j), (Z.leb_spec 0 i), (Z.ltb_spec i (arr_len (ds_heap s))); cbn [andb]; try lia; reflexivity.
Qed.

Lemma arr_len_heap_set : forall s i v, arr_len (ds_heap (heap_set s i v)) = arr_len (ds_heap s).
Proof. intros. unfold heap_set. dsred. apply arr_len_set. Qed.


Lemma pqdownheap_loop_0 : forall s t v k j, pqdownheap_loop 0 s t v k j = (s, k).
Proof. reflexivity. Qed.

Lemma pqdownheap_loop_S : forall f s t v k j,
  pqdownheap_loop (S f) s t v k j =
    if j <=? ds_heap_len s then
      let j' := if (j <? ds_heap_len s) && smaller s t (heap_get s (j + 1)) (heap_get s j)
                then j + 1 else j in
      if smaller s t v (heap_get s j') then (s, k)
      else pqdownheap_loop f (heap_set s k (heap_get s j')) t v j' (Z.shiftl j' 1)
    else (s, k).
Proof. reflexivity. Qed.

Lemma pqdownheap_loop_out : forall f s t v k j,
  ds_heap_len s < j -> pqdownheap_loop f s t v k j = (s, k).
Proof.
  intros [|f] s t v k j H; [reflexivity|]. rewrite pqdownheap_loop_S.
  destruct (Z.leb_spec j (ds_heap_len s)); [lia | reflexivity].
Qed.

Lemma pqdownheap_loop_shape : forall f s t v k j s' k',
  pqdownheap_loop f s t v k j = (s', k') -> s' = set_heap s (ds_heap s').
Proof.
  induction f as [|f IH]; intros s t v k j s' k' H.
  - rewrite pqdownheap_loop_0 in H. injection H as <- <-. symmetry. apply set_heap_self.
  - rewrite pqdownheap_loop_S in H.
    destruct (j <=? ds_heap_len s); [| injection H as <- <-; symmetry; apply set_heap_self].
    cbv zeta in H.
    set (j' := if (j <? ds_heap_len s) && smaller s t (heap_get s (j + 1)) (heap_get s j) then j + 1 else j) in H.
    destruct (smaller s t v (heap_get s j')); [injection H as <- <-; symmetry; apply set_heap_self|].
    apply IH in H. rewrite H. rewrite heap_set_shape, set_heap_twice. reflexivity.
Qed.

Lemma pqdownheap_loop_len : forall f s t v k j s' k',
  pqdownheap_loop f s t v k j = (s', k') -> arr_len (ds_heap s') = arr_len (ds_heap s).
Proof.
  induction f as [|f IH]; intros s t v k j s' k' H.
  - rewrite pqdownheap_loop_0 in H. injection H as <- <-. reflexivity.
  - rewrite pqdownheap_loop_S in H.
    destruct (j <=? ds_heap_len s); [| injection H as <- <-; reflexivity].
    cbv zeta in H.
    set (j' := if (j <? ds_heap_len s) && smaller s t (heap_get s (j + 1)) (heap_get s j) then j + 1 else j) in H.
    destruct (smaller s t v (heap_get s j')); [injection H as <- <-; reflexivity|].
    apply IH in H. rewrite H. apply arr_len_heap_set.
Qed.

Lemma pqdownheap_shape : forall s t k, pqdownheap s t k = set_heap s (ds_heap (pqdownheap s t k)).
Proof.
  intros s t k. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:H.
  apply pqdownheap_loop_shape in H. rewrite H at 1.
  rewrite heap_set_shape, set_heap_twice. reflexivity.
Qed.

Lemma pqdownheap_len : forall s t k, arr_len (ds_heap (pqdownheap s t k)) = arr_len (ds_heap s).
Proof.
  intros s t k. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:H.
  rewrite arr_len_heap_set. exact (pqdownheap_loop_len _ _ _ _ _ _ _ _ H).
Qed.


Definition pq_ok (B : Z) (s : deflate_state) : Prop :=
  forall i, 1 <= i <= ds_heap_len s -> 0 <= heap_get s i < B.

Lemma pq_ok_heap_set : forall B s i v,
  pq_ok B s -> 0 <= i < arr_len (ds_heap s) -> 0 <= v < B -> pq_ok B (heap_set s i v).
Proof.
  intros B s i v H Hi Hv n Hn. change (ds_heap_len (heap_set s i v)) with (ds_heap_len s) in Hn.
  rewrite heap_get_heap_set by exact Hi. destruct (i =? n); [lia | exact (H n Hn)].
Qed.
