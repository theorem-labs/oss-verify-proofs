(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma trip_unfold : forall s t BC OL SL MC FC DL HP HL HM DP node,
  RefBuildTree4.trip s t BC OL SL MC FC DL HP HL HM DP node
  = pqdownheap (bt_upd s t
      (arr_set FC node (wrap16 (arr_get FC (arr_get HP 1) + arr_get FC (arr_get (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) 1))))
      (arr_set (arr_set DL (arr_get (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) 1) (wrap16 node)) (arr_get HP 1) (wrap16 node))
      (arr_set (arr_set (arr_set (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) (HM - 1) (arr_get HP 1)) (HM - 2)
                        (arr_get (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) 1)) 1 node)
      (HL - 1) (HM - 2)
      (arr_set DP node (wrap8 (dmax DP (arr_get HP 1) (arr_get (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) 1) + 1)))
      BC OL SL MC) t 1.
Proof. intros. unfold RefBuildTree4.trip. match goal with |- ?a = ?b => constr_eq a b end. reflexivity. Qed.

Lemma l4_model : forall s t BC OL SL MC FC DL HP HL HM DP node f R HP2 m_ FC' DL' HP3 DP' HPf,
  R = build_tree_loop4 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  HP2 = ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1) ->
  m_ = arr_get HP2 1 ->
  FC' = arr_set FC node (wrap16 (arr_get FC (arr_get HP 1) + arr_get FC m_)) ->
  DL' = arr_set (arr_set DL m_ (wrap16 node)) (arr_get HP 1) (wrap16 node) ->
  HP3 = arr_set (arr_set (arr_set HP2 (HM - 1) (arr_get HP 1)) (HM - 2) m_) 1 node ->
  DP' = arr_set DP node (wrap8 (dmax DP (arr_get HP 1) m_ + 1)) ->
  HPf = ds_heap (pqdownheap (bt_upd s t FC' DL' HP3 (HL - 1) (HM - 2) DP' BC OL SL MC) t 1) ->
  R = (if 2 <=? HL - 1 then build_tree_loop4 f (bt_upd s t FC' DL' HPf (HL - 1) (HM - 2) DP' BC OL SL MC) t (node + 1)
       else bt_upd s t FC' DL' HPf (HL - 1) (HM - 2) DP' BC OL SL MC).
Proof.
  intros until HPf. intros ER E2 Em EF ED E3 EP Ef.
  rewrite RefBuildTree4.L4_step in ER. rewrite (RefBuildTree4.trip_flat s t BC OL SL MC FC DL HP HL HM DP node) in ER.
  rewrite trip_unfold in ER. rewrite <- E2 in ER. rewrite <- Em in ER. rewrite <- EF, <- ED, <- E3, <- EP in ER. rewrite <- Ef in ER. exact ER.
Qed.
