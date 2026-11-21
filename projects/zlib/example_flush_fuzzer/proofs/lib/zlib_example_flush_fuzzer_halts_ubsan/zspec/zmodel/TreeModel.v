(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import FillWinModel.
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

Lemma sh_heap_len : forall s h, ds_heap_len (set_heap s h) = ds_heap_len s.
Proof. intros. reflexivity. Qed.




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


Lemma pqdownheap_shape : forall s t k, pqdownheap s t k = set_heap s (ds_heap (pqdownheap s t k)).
Proof.
  intros s t k. unfold pqdownheap.
  destruct (pqdownheap_loop 32 s t (heap_get s k) k (Z.shiftl k 1)) as [s' k'] eqn:H.
  apply pqdownheap_loop_shape in H. rewrite H at 1.
  rewrite heap_set_shape, set_heap_twice. reflexivity.
Qed.



