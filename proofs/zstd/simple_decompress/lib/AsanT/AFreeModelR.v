(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import ARefill_iface AFreeModel AFreeRead.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition afterK (s : astate) : AM astate :=
  if Q_CACHE <? a_qloc_bytes s then drain s (fun s3 => aret s3) else aret s.
(* [comment removed for export] *)
Definition KB (ch : achunk) (s : astate) (ok : bool) : AM astate :=
  if negb ok then aundef_ USpin (afterK s)
  else afterK (set_qloc (a_qloc s ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes s + chunk_size ch + Q_BATCH_BYTES) s).

Lemma afree_refill_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  afree st (Some p) = cache_refill_tree st1 K_BATCH_CLASS (KB ch).
Proof.
  intros st p ch LIVE SZ st1 EA CNT0.
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue.
  assert (NB : forall s, cache_alloc s K_BATCH_CLASS (fun (st0 : astate) (ok : bool) =>
      if negb ok then aundef_ USpin ((fun st2 : astate => if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 : astate => aret st3) else aret st2) st0)
      else (fun st2 : astate => if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 : astate => aret st3) else aret st2)
             (set_qloc (a_qloc st0 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st0 + chunk_size ch + Q_BATCH_BYTES) st0))
    = cache_alloc s K_BATCH_CLASS (KB ch)) by (intros s; reflexivity).
  pose proof EA as EA0. unfold enq_is_app in EA0. change (a_qloc st) with (a_qloc st1) in EA0.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - rewrite NB, cache_alloc_unfold. change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS). rewrite CNT0. reflexivity.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF]; [| cbn in EA0; discriminate].
    rewrite NB, cache_alloc_unfold. change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS). rewrite CNT0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma KB_apop_eq : forall s ch,
  enq_is_app s = false ->
  (Q_CACHE < a_qloc_bytes (st_enq s ch) -> a_qglob_bytes (st_enq s ch) + a_qloc_bytes (st_enq s ch) <= Q_MAX) ->
  KB ch (apop K_BATCH_CLASS s) true = aret (st_after (st_enq s ch)).
Proof.
  intros s ch EA NOREC.
  assert (EN : st_enq s ch = enq_new s ch).
  { unfold st_enq. destruct (enq_app s ch) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app s = true) by (apply (proj2 (enq_is_app_spec s ch)); eexists; exact E). congruence. }
  rewrite EN in *. unfold KB. cbn [negb].
  change (set_qloc (a_qloc (apop K_BATCH_CLASS s) ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]])
                   (a_qloc_bytes (apop K_BATCH_CLASS s) + chunk_size ch + Q_BATCH_BYTES) (apop K_BATCH_CLASS s)) with (enq_new s ch).
  unfold afterK, st_after, drain.
  destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes (enq_new s ch))) as [LT|GE]; [| reflexivity].
  cbn [a_qglob_bytes set_qglob].
  destruct (Z.ltb_spec Q_MAX (a_qglob_bytes (enq_new s ch) + a_qloc_bytes (enq_new s ch))) as [LT2|GE2]; [exfalso; specialize (NOREC LT); lia| reflexivity].
Qed.
End CANSEC1.
