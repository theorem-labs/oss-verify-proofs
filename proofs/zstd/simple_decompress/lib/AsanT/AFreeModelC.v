(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import ARefill_iface AFreeModel AFreeRead AFreeModelR.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma after_rec_eq : forall st2,
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)
  = recycle (st_after st2) Q_MIN (fun st3 => @aret astate st3)
  /\ a_qloc (st_after st2) = [] /\ a_qloc_bytes (st_after st2) = 0
  /\ a_qglob (st_after st2) = a_qglob st2 ++ a_qloc st2 /\ a_qglob_bytes (st_after st2) = a_qglob_bytes st2 + a_qloc_bytes st2.
Proof.
  intros st2 QC REC. unfold st_after, drain.
  replace (Q_CACHE <? a_qloc_bytes st2) with true by (symmetry; apply Z.ltb_lt; exact QC).
  cbn [a_qglob_bytes a_qloc a_qloc_bytes a_qglob set_qglob set_qloc].
  replace (Q_MAX <? a_qglob_bytes st2 + a_qloc_bytes st2) with true by (symmetry; apply Z.ltb_lt; exact REC).
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma afree_rec_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  (enq_app st1 ch = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  afree st (Some p) = recycle (st_after st2) Q_MIN (fun st3 => aret st3).
Proof.
  intros st p ch LIVE SZ st1 st2 CNT QC REC.
  pose proof (proj1 (after_rec_eq st2 QC REC)) as AFTER.
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue. subst st2. unfold st_enq in *. unfold enq_app in *.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - unfold cache_alloc. specialize (CNT eq_refl).
    replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
    cbn [negb]. unfold enq_new in *. exact AFTER.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF].
    + unfold cache_alloc. specialize (CNT eq_refl).
      replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
      cbn [negb]. unfold enq_new in *. exact AFTER.
    + exact AFTER.
Qed.

(* [comment removed for export] *)
Lemma KB_apop_rec_eq : forall s ch,
  enq_is_app s = false ->
  Q_CACHE < a_qloc_bytes (st_enq s ch) -> Q_MAX < a_qglob_bytes (st_enq s ch) + a_qloc_bytes (st_enq s ch) ->
  KB ch (apop K_BATCH_CLASS s) true = recycle (st_after (st_enq s ch)) Q_MIN (fun st3 => aret st3).
Proof.
  intros s ch EA QC REC.
  assert (EN : st_enq s ch = enq_new s ch).
  { unfold st_enq. destruct (enq_app s ch) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app s = true) by (apply (proj2 (enq_is_app_spec s ch)); eexists; exact E). congruence. }
  rewrite EN in *. unfold KB. cbn [negb].
  change (set_qloc (a_qloc (apop K_BATCH_CLASS s) ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]])
                   (a_qloc_bytes (apop K_BATCH_CLASS s) + chunk_size ch + Q_BATCH_BYTES) (apop K_BATCH_CLASS s)) with (enq_new s ch).
  unfold afterK. exact (proj1 (after_rec_eq _ QC REC)).
Qed.
End CANSEC1.
