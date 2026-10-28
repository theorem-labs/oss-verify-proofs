(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enq_app (st1 : astate) (ch : achunk) : option astate :=
  match rev (a_qloc st1) with
  | b :: rl => if b_count b =? Q_BATCH then None
               else Some (set_qloc (rev (mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b) :: rl))
                                   (a_qloc_bytes st1 + chunk_size ch) st1)
  | [] => None
  end.
(* [comment removed for export] *)
Definition enq_new (st1 : astate) (ch : achunk) : astate :=
  let r := get_cls st1 K_BATCH_CLASS in
  let st2 := put_cls K_BATCH_CLASS (cls_set_count (c_count r - 1) r) st1 in
  set_qloc (a_qloc st2 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st2 + chunk_size ch + Q_BATCH_BYTES) st2.
Definition st_enq (st1 : astate) (ch : achunk) : astate :=
  match enq_app st1 ch with Some s => s | None => enq_new st1 ch end.
(* [comment removed for export] *)
Definition st_after (st2 : astate) : astate :=
  if Q_CACHE <? a_qloc_bytes st2
  then set_qglob (a_qglob st2 ++ a_qloc st2) (a_qglob_bytes st2 + a_qloc_bytes st2) (set_qloc [] 0 st2)
  else st2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afree_fast_eq : forall st p ch,
  (a_live st) !! p = Some ch -> chunk_size ch <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  (enq_app st1 ch = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes (st_enq st1 ch) -> a_qglob_bytes (st_enq st1 ch) + a_qloc_bytes (st_enq st1 ch) <= Q_MAX) ->
  afree st (Some p) = aret (st_after (st_enq st1 ch)).
Proof.
  intros st p ch LIVE SZ st1 CNT NOREC.
  assert (AFTER : forall st2, (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
            (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2) = @aret astate (st_after st2)).
  { intros st2 NR. unfold st_after, drain.
    destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; [|reflexivity].
    cbn [a_qglob_bytes set_qglob].
    destruct (Z.ltb_spec Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [LT2|GE2]; [exfalso; specialize (NR LT); lia| reflexivity]. }
  unfold afree. rewrite LIVE. fold st1.
  replace (chunk_size ch <=? Q_MAX) with true by (symmetry; apply Z.leb_le; exact SZ).
  unfold enqueue. unfold st_enq in *. unfold enq_app in *.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - unfold cache_alloc. specialize (CNT eq_refl).
    replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
    cbn [negb]. unfold enq_new in *. apply AFTER. exact NOREC.
  - destruct (Z.eqb_spec (b_count b) Q_BATCH) as [FULL|NF].
    + unfold cache_alloc. specialize (CNT eq_refl).
      replace (0 <? c_count (get_cls st1 K_BATCH_CLASS)) with true by (symmetry; apply Z.ltb_lt; exact CNT).
      cbn [negb]. unfold enq_new in *. apply AFTER. exact NOREC.
    + apply AFTER. exact NOREC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enq_app_Some : forall st1 ch s, enq_app st1 ch = Some s ->
  exists l b, a_qloc st1 = l ++ [b] /\ b_count b <> Q_BATCH
    /\ s = set_qloc (l ++ [mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b)]) (a_qloc_bytes st1 + chunk_size ch) st1.
Proof.
  intros st1 ch s E. unfold enq_app in E.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (Z.eqb_spec (b_count b) Q_BATCH) as [F|NF]; [discriminate|].
  injection E as <-. exists (rev rl), b.
  assert (Q : a_qloc st1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc st1)), RV; reflexivity).
  split; [exact Q|]. split; [exact NF|]. cbn [rev]. reflexivity.
Qed.

Lemma enq_app_None : forall st1 ch, enq_app st1 ch = None ->
  a_qloc st1 = [] \/ exists l b, a_qloc st1 = l ++ [b] /\ b_count b = Q_BATCH.
Proof.
  intros st1 ch E. unfold enq_app in E.
  destruct (rev (a_qloc st1)) as [|b rl] eqn:RV.
  - left. rewrite <- (rev_involutive (a_qloc st1)), RV. reflexivity.
  - right. destruct (Z.eqb_spec (b_count b) Q_BATCH) as [F|NF]; [|discriminate].
    exists (rev rl), b. split; [| exact F]. rewrite <- (rev_involutive (a_qloc st1)), RV. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fields.
Variables (st : astate) (p : aptr) (ch : achunk).
Let st1 := set_live (delete p (a_live st)) st.

Lemma st1_fields :
  a_live st1 = delete p (a_live st) /\ a_cls st1 = a_cls st /\ a_next st1 = a_next st /\ a_cinit st1 = a_cinit st
  /\ a_qloc st1 = a_qloc st /\ a_qloc_bytes st1 = a_qloc_bytes st /\ a_qglob st1 = a_qglob st /\ a_qglob_bytes st1 = a_qglob_bytes st
  /\ a_space_beg st1 = a_space_beg st /\ a_ptr_array st1 = a_ptr_array st /\ a_nres st1 = a_nres st /\ a_nsec st1 = a_nsec st.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Definition same_core (s s' : astate) : Prop :=
  a_live s' = a_live s /\ a_next s' = a_next s /\ a_cinit s' = a_cinit s
  /\ a_space_beg s' = a_space_beg s /\ a_ptr_array s' = a_ptr_array s /\ a_nres s' = a_nres s /\ a_nsec s' = a_nsec s
  /\ (forall c, c <> K_BATCH_CLASS -> get_cls s' c = get_cls s c)
  /\ c_mapped_user (get_cls s' K_BATCH_CLASS) = c_mapped_user (get_cls s K_BATCH_CLASS)
  /\ c_allocated_user (get_cls s' K_BATCH_CLASS) = c_allocated_user (get_cls s K_BATCH_CLASS)
  /\ c_num_freed (get_cls s' K_BATCH_CLASS) = c_num_freed (get_cls s K_BATCH_CLASS)
  /\ c_mapped_free_array (get_cls s' K_BATCH_CLASS) = c_mapped_free_array (get_cls s K_BATCH_CLASS).

Lemma same_core_refl : forall s, same_core s s.
Proof. intros s. repeat split; intros; reflexivity. Qed.

Lemma get_cls_put_eq : forall c r s, get_cls (put_cls c r s) c = r.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma get_cls_put_ne : forall c c' r s, c' <> c -> get_cls (put_cls c r s) c' = get_cls s c'.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma enq_app_core : forall s1 s, enq_app s1 ch = Some s -> same_core s1 s /\ a_qglob s = a_qglob s1 /\ a_qglob_bytes s = a_qglob_bytes s1.
Proof.
  intros s1 s E. destruct (enq_app_Some s1 ch s E) as (l & b & Q & NF & ->).
  split; [| split; reflexivity]. repeat split; intros; reflexivity.
Qed.

Lemma get_cls_set_qloc : forall l b s c, get_cls (set_qloc l b s) c = get_cls s c. Proof. reflexivity. Qed.
Lemma get_cls_set_qglob : forall l b s c, get_cls (set_qglob l b s) c = get_cls s c. Proof. reflexivity. Qed.

Lemma enq_new_core : forall s1,
  same_core s1 (enq_new s1 ch) /\ a_qglob (enq_new s1 ch) = a_qglob s1 /\ a_qglob_bytes (enq_new s1 ch) = a_qglob_bytes s1
  /\ c_count (get_cls (enq_new s1 ch) K_BATCH_CLASS) = c_count (get_cls s1 K_BATCH_CLASS) - 1
  /\ a_qloc (enq_new s1 ch) = a_qloc s1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]
  /\ a_qloc_bytes (enq_new s1 ch) = a_qloc_bytes s1 + chunk_size ch + Q_BATCH_BYTES
  /\ a_cls (enq_new s1 ch) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls s1 K_BATCH_CLASS) - 1) (get_cls s1 K_BATCH_CLASS) ]> (a_cls s1).
Proof.
  intros s1. unfold enq_new. cbv zeta. rewrite !get_cls_set_qloc, !get_cls_put_eq.
  split.
  { unfold same_core. rewrite !get_cls_set_qloc, !get_cls_put_eq. repeat split; try reflexivity.
    intros c NE. rewrite get_cls_set_qloc, get_cls_put_ne by exact NE. reflexivity. }
  repeat split; reflexivity.
Qed.

Lemma same_core_trans : forall s1 s2 s3, same_core s1 s2 -> same_core s2 s3 -> same_core s1 s3.
Proof.
  intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  unfold same_core. rewrite B1, B2, B3, B4, B5, B6, B7, B9, B10, B11, B12.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
  split; [intros c NE; rewrite (B8 c NE); exact (A8 c NE)|].
  split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

Lemma st_after_q : forall s2,
  (Q_CACHE < a_qloc_bytes s2 -> a_qloc (st_after s2) = [] /\ a_qloc_bytes (st_after s2) = 0
      /\ a_qglob (st_after s2) = a_qglob s2 ++ a_qloc s2 /\ a_qglob_bytes (st_after s2) = a_qglob_bytes s2 + a_qloc_bytes s2)
  /\ (a_qloc_bytes s2 <= Q_CACHE -> st_after s2 = s2).
Proof.
  intros s2. unfold st_after. split; intros H.
  - replace (Q_CACHE <? a_qloc_bytes s2) with true by (symmetry; apply Z.ltb_lt; exact H). repeat split; reflexivity.
  - replace (Q_CACHE <? a_qloc_bytes s2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma st_after_core : forall s2, same_core s2 (st_after s2) /\ a_cls (st_after s2) = a_cls s2.
Proof.
  intros s2. unfold st_after. destruct (Q_CACHE <? a_qloc_bytes s2); [| split; [apply same_core_refl| reflexivity]].
  split; [| reflexivity]. repeat split; intros; reflexivity.
Qed.
End Fields.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qfilt (f : achunk -> bool) (s : astate) : list achunk :=
  List.filter f (flat_map b_chunks (a_qloc s ++ a_qglob s)).

Lemma flat_map_app_chunks : forall (l1 l2 : list abatch), flat_map b_chunks (l1 ++ l2) = flat_map b_chunks l1 ++ flat_map b_chunks l2.
Proof. intros. apply flat_map_app. Qed.

Lemma enq_app_qfilt : forall f s1 ch s, f ch = false -> enq_app s1 ch = Some s -> qfilt f s = qfilt f s1.
Proof.
  intros f s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. reflexivity.
Qed.

Lemma enq_new_qfilt : forall f s1 ch, f ch = false -> qfilt f (enq_new s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

Lemma st_enq_qfilt : forall f s1 ch, f ch = false -> qfilt f (st_enq s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt f s1 ch s Hf E)| exact (enq_new_qfilt f s1 ch Hf)].
Qed.

Lemma st_after_qfilt : forall f s2, Permutation (qfilt f (st_after s2)) (qfilt f s2).
Proof.
  intros f s2. unfold st_after, qfilt. destruct (Q_CACHE <? a_qloc_bytes s2); [| apply Permutation_refl].
  cbn [a_qloc a_qglob set_qglob set_qloc app]. rewrite !flat_map_app_chunks, !List.filter_app. apply Permutation_app_comm.
Qed.

Lemma st_after_enq_qfilt : forall f s1 ch, f ch = false -> Permutation (qfilt f (st_after (st_enq s1 ch))) (qfilt f s1).
Proof.
  intros f s1 ch Hf. rewrite <- (st_enq_qfilt f s1 ch Hf). apply st_after_qfilt.
Qed.
End CANSEC1.
