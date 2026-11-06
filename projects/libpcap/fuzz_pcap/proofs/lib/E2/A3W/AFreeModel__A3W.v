(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From stdpp Require bitvector.definitions.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ZBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AFreeModel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
#[using="Type"] Lemma afree_fast_eq : forall st p ch,
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
#[using="Type"] Lemma enq_app_Some : forall st1 ch s, enq_app st1 ch = Some s ->
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

#[using="Type"] Lemma enq_app_None : forall st1 ch, enq_app st1 ch = None ->
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

#[using="Type"] Lemma st1_fields :
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

#[using="Type"] Lemma same_core_refl : forall s, same_core s s.
Proof. intros s. repeat split; intros; reflexivity. Qed.

#[using="Type"] Lemma get_cls_put_eq : forall c r s, get_cls (put_cls c r s) c = r.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_cls_put_ne : forall c c' r s, c' <> c -> get_cls (put_cls c r s) c' = get_cls s c'.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma enq_app_core : forall s1 s, enq_app s1 ch = Some s -> same_core s1 s /\ a_qglob s = a_qglob s1 /\ a_qglob_bytes s = a_qglob_bytes s1.
Proof.
  intros s1 s E. (nd_pre (enq_app_Some s1 ch s E) 5%nat; intros l b Q NF ndR1__; nd_post; revert ndR1__; intros ->).
  split; [| split; reflexivity]. repeat split; intros; reflexivity.
Qed.

#[using="Type"] Lemma get_cls_set_qloc : forall l b s c, get_cls (set_qloc l b s) c = get_cls s c. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_qglob : forall l b s c, get_cls (set_qglob l b s) c = get_cls s c. Proof. reflexivity. Qed.

#[using="Type"] Lemma enq_new_core : forall s1,
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

#[using="Type"] Lemma same_core_trans : forall s1 s2 s3, same_core s1 s2 -> same_core s2 s3 -> same_core s1 s3.
Proof.
  intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  unfold same_core. rewrite B1, B2, B3, B4, B5, B6, B7, B9, B10, B11, B12.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
  split; [intros c NE; rewrite (B8 c NE); exact (A8 c NE)|].
  split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

#[using="Type"] Lemma st_after_q : forall s2,
  (Q_CACHE < a_qloc_bytes s2 -> a_qloc (st_after s2) = [] /\ a_qloc_bytes (st_after s2) = 0
      /\ a_qglob (st_after s2) = a_qglob s2 ++ a_qloc s2 /\ a_qglob_bytes (st_after s2) = a_qglob_bytes s2 + a_qloc_bytes s2)
  /\ (a_qloc_bytes s2 <= Q_CACHE -> st_after s2 = s2).
Proof.
  intros s2. unfold st_after. split; intros H.
  - replace (Q_CACHE <? a_qloc_bytes s2) with true by (symmetry; apply Z.ltb_lt; exact H). repeat split; reflexivity.
  - replace (Q_CACHE <? a_qloc_bytes s2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma st_after_core : forall s2, same_core s2 (st_after s2) /\ a_cls (st_after s2) = a_cls s2.
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

#[using="Type"] Lemma flat_map_app_chunks : forall (l1 l2 : list abatch), flat_map b_chunks (l1 ++ l2) = flat_map b_chunks l1 ++ flat_map b_chunks l2.
Proof. intros. apply flat_map_app. Qed.

#[using="Type"] Lemma enq_app_qfilt : forall f s1 ch s, f ch = false -> enq_app s1 ch = Some s -> qfilt f s = qfilt f s1.
Proof.
  intros f s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. reflexivity.
Qed.

#[using="Type"] Lemma enq_new_qfilt : forall f s1 ch, f ch = false -> qfilt f (enq_new s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma st_enq_qfilt : forall f s1 ch, f ch = false -> qfilt f (st_enq s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt f s1 ch s Hf E)| exact (enq_new_qfilt f s1 ch Hf)].
Qed.

#[using="Type"] Lemma st_after_qfilt : forall f s2, Permutation (qfilt f (st_after s2)) (qfilt f s2).
Proof.
  intros f s2. unfold st_after, qfilt. destruct (Q_CACHE <? a_qloc_bytes s2); [| apply Permutation_refl].
  cbn [a_qloc a_qglob set_qglob set_qloc app]. rewrite !flat_map_app_chunks, !List.filter_app. apply Permutation_app_comm.
Qed.

#[using="Type"] Lemma st_after_enq_qfilt : forall f s1 ch, f ch = false -> Permutation (qfilt f (st_after (st_enq s1 ch))) (qfilt f s1).
Proof.
  intros f s1 ch Hf. rewrite <- (st_enq_qfilt f s1 ch Hf). apply st_after_qfilt.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
#[using="Type"] Lemma afree_fast_eq : forall st p ch,
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
#[using="Type"] Lemma enq_app_Some : forall st1 ch s, enq_app st1 ch = Some s ->
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

#[using="Type"] Lemma enq_app_None : forall st1 ch, enq_app st1 ch = None ->
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

#[using="Type"] Lemma st1_fields :
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

#[using="Type"] Lemma same_core_refl : forall s, same_core s s.
Proof. intros s. repeat split; intros; reflexivity. Qed.

#[using="Type"] Lemma get_cls_put_eq : forall c r s, get_cls (put_cls c r s) c = r.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="Type"] Lemma get_cls_put_ne : forall c c' r s, c' <> c -> get_cls (put_cls c r s) c' = get_cls s c'.
Proof. intros. unfold get_cls, put_cls. cbn. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma enq_app_core : forall s1 s, enq_app s1 ch = Some s -> same_core s1 s /\ a_qglob s = a_qglob s1 /\ a_qglob_bytes s = a_qglob_bytes s1.
Proof.
  intros s1 s E. (nd_pre (enq_app_Some s1 ch s E) 5%nat; intros l b Q NF ndR1__; nd_post; revert ndR1__; intros ->).
  split; [| split; reflexivity]. repeat split; intros; reflexivity.
Qed.

#[using="Type"] Lemma get_cls_set_qloc : forall l b s c, get_cls (set_qloc l b s) c = get_cls s c. Proof. reflexivity. Qed.
#[using="Type"] Lemma get_cls_set_qglob : forall l b s c, get_cls (set_qglob l b s) c = get_cls s c. Proof. reflexivity. Qed.

#[using="Type"] Lemma enq_new_core : forall s1,
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

#[using="Type"] Lemma same_core_trans : forall s1 s2 s3, same_core s1 s2 -> same_core s2 s3 -> same_core s1 s3.
Proof.
  intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  unfold same_core. rewrite B1, B2, B3, B4, B5, B6, B7, B9, B10, B11, B12.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
  split; [intros c NE; rewrite (B8 c NE); exact (A8 c NE)|].
  split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

#[using="Type"] Lemma st_after_q : forall s2,
  (Q_CACHE < a_qloc_bytes s2 -> a_qloc (st_after s2) = [] /\ a_qloc_bytes (st_after s2) = 0
      /\ a_qglob (st_after s2) = a_qglob s2 ++ a_qloc s2 /\ a_qglob_bytes (st_after s2) = a_qglob_bytes s2 + a_qloc_bytes s2)
  /\ (a_qloc_bytes s2 <= Q_CACHE -> st_after s2 = s2).
Proof.
  intros s2. unfold st_after. split; intros H.
  - replace (Q_CACHE <? a_qloc_bytes s2) with true by (symmetry; apply Z.ltb_lt; exact H). repeat split; reflexivity.
  - replace (Q_CACHE <? a_qloc_bytes s2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Type"] Lemma st_after_core : forall s2, same_core s2 (st_after s2) /\ a_cls (st_after s2) = a_cls s2.
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

#[using="Type"] Lemma flat_map_app_chunks : forall (l1 l2 : list abatch), flat_map b_chunks (l1 ++ l2) = flat_map b_chunks l1 ++ flat_map b_chunks l2.
Proof. intros. apply flat_map_app. Qed.

#[using="Type"] Lemma enq_app_qfilt : forall f s1 ch s, f ch = false -> enq_app s1 ch = Some s -> qfilt f s = qfilt f s1.
Proof.
  intros f s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. reflexivity.
Qed.

#[using="Type"] Lemma enq_new_qfilt : forall f s1 ch, f ch = false -> qfilt f (enq_new s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf. cbn [app]. rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma st_enq_qfilt : forall f s1 ch, f ch = false -> qfilt f (st_enq s1 ch) = qfilt f s1.
Proof.
  intros f s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt f s1 ch s Hf E)| exact (enq_new_qfilt f s1 ch Hf)].
Qed.

#[using="Type"] Lemma st_after_qfilt : forall f s2, Permutation (qfilt f (st_after s2)) (qfilt f s2).
Proof.
  intros f s2. unfold st_after, qfilt. destruct (Q_CACHE <? a_qloc_bytes s2); [| apply Permutation_refl].
  cbn [a_qloc a_qglob set_qglob set_qloc app]. rewrite !flat_map_app_chunks, !List.filter_app. apply Permutation_app_comm.
Qed.

#[using="Type"] Lemma st_after_enq_qfilt : forall f s1 ch, f ch = false -> Permutation (qfilt f (st_after (st_enq s1 ch))) (qfilt f s1).
Proof.
  intros f s1 ch Hf. rewrite <- (st_enq_qfilt f s1 ch Hf). apply st_after_qfilt.
Qed.
End CANSEC1.
End TwB.
End AFreeModel.

(* [comment removed for export] *)
Module AModelFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rz_log_small : forall n, 1 <= n <= 448 -> rz_log n = (if n <=? 48 then 0 else if n <=? 96 then 1 else 2).
Proof. intros n H. unfold rz_log. destruct (n <=? 48); [reflexivity|]. destruct (n <=? 96); [reflexivity|].
  replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

#[using="Type"] Lemma rz_log_range_small : forall n, 1 <= n <= 448 -> 0 <= rz_log n <= 2.
Proof. intros n H. rewrite rz_log_small by lia. destruct (n <=? 48); [lia|]. destruct (n <=? 96); lia. Qed.

#[using="Type"] Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2. reflexivity. unfold rz_log.
  repeat (destruct (_ <=? _)); lia. Qed.

#[using="Type"] Lemma rounded_size_eq : forall n, rounded_size n = (Z.max n 8 + 7) / 8 * 8.
Proof. intros n. unfold rounded_size, rup. f_equal. f_equal. lia. Qed.

#[using="Type"] Lemma small_facts : forall n, 1 <= n <= 448 ->
  is_primary n = true /\ needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 64 /\ rz_size n = 16 * 2 ^ rz_log n
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 512.
Proof.
  intros n H.
  pose proof (rz_log_range_small n H) as R. pose proof (rz_size_eq n) as S.
  assert (S2 : 16 <= rz_size n <= 64).
  { rewrite S. assert (2 ^ rz_log n = 1 \/ 2 ^ rz_log n = 2 \/ 2 ^ rz_log n = 4).
    { destruct (Z.eq_dec (rz_log n) 0) as [->|]; [left; reflexivity|]. destruct (Z.eq_dec (rz_log n) 1) as [->|]; [right; left; reflexivity|].
      replace (rz_log n) with 2 by lia. right; right; reflexivity. } lia. }
  pose proof (rounded_size_eq n) as RS.
  assert (RR : Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0).
  { rewrite RS. Z.div_mod_to_equations. lia. }
  assert (P : is_primary n = true).
  { unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_le. lia. }
  assert (NS : needed_size n = rounded_size n + rz_size n).
  { unfold needed_size. rewrite P. reflexivity. }
  assert (UP : rounded_size n + rz_size n <= 512).
  { rewrite S, RS. rewrite rz_log_small by lia.
    destruct (Z.leb_spec n 48); [cbn; Z.div_mod_to_equations; lia|].
    destruct (Z.leb_spec n 96); cbn; Z.div_mod_to_equations; lia. }
  rewrite NS. split; [exact P|]. split; [reflexivity|]. split; [lia|]. split; [exact S|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma rounded_size_align : forall n, rounded_size n = Z.max n 8 + 7 - (Z.max n 8 + 7) mod 8.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sllw_rz : forall n, 1 <= n <= 448 ->
  bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n N. pose proof (rz_log_range_small n N) as RLR. pose proof (rz_size_eq n) as RZE.
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  assert (P4 : 2 ^ rz_log n <= 2 ^ 2) by (apply Z.pow_le_mono_r; lia).
  assert (P1 : 0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; lia).
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
  intros x Hx.
  replace 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 48) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 48; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma rz_size_small_cases : forall n, 1 <= n <= 448 -> rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64.
Proof.
  intros n N. rewrite rz_size_eq, (rz_log_small n N).
  destruct (n <=? 48); [left; reflexivity|]. destruct (n <=? 96); [right; left; reflexivity| right; right; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_fast_eq : forall RESV st n c,
  1 <= n <= 448 -> class_id (needed_size n) = c -> 0 < c_count (get_cls st c) ->
  amalloc ATOP RESV st n =
    SRet (set_next (N.succ (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
            (set_live (<[ a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) := CPrim c n ]>
                        (a_live (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)),
          Some (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st))).
Proof.
  intros RESV st n c N HC POS. (pose proof (small_facts n N) as ndP__; nd_pre ndP__ 7%nat; intros PRIM NS RZR RZE RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM. unfold cache_alloc. rewrite HC.
  replace (0 <? c_count (get_cls st c)) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

#[using="Type"] Lemma a_next_put_cls : forall c r st, a_next (put_cls c r st) = a_next st.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma a_live_put_cls : forall c r st, a_live (put_cls c r st) = a_live st.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma class_id_small : forall s, s <= 512 -> class_id s = Z.shiftr (s + 31) 5.
Proof. intros s Hs. unfold class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
#[using="Type"] Lemma size_of_class_small : forall c, c <= 16 -> size_of_class c = 32 * c.
Proof. intros c Hc. unfold size_of_class. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
#[using="Type"] Lemma class_small_facts : forall n c, 1 <= n <= 448 -> class_id (needed_size n) = c ->
  1 <= c <= 16 /\ Z.shiftr (needed_size n + 31) 5 = c /\ size_of_class c = 32 * c /\ needed_size n <= size_of_class c <= 512.
Proof.
  intros n c N HC. (pose proof (small_facts n N) as ndP__; nd_pre ndP__ 7%nat; intros PRIM NS RZR RZE RSR RSM NSR; nd_post).
  rewrite class_id_small in HC by lia.
  assert (C : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof (size_of_class_small c ltac:(lia)) as S.
  split; [exact C|]. split; [exact HC|]. split; [exact S|].
  rewrite S. rewrite <- HC. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma max_cached_le16 : forall c, 1 <= c -> max_cached c <= 16.
Proof. intros c Hc. unfold max_cached. lia. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.bitvector.definitions.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import stdpp.gmap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rz_log_small : forall n, 1 <= n <= 448 -> rz_log n = (if n <=? 48 then 0 else if n <=? 96 then 1 else 2).
Proof. intros n H. unfold rz_log. destruct (n <=? 48); [reflexivity|]. destruct (n <=? 96); [reflexivity|].
  replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

#[using="Type"] Lemma rz_log_range_small : forall n, 1 <= n <= 448 -> 0 <= rz_log n <= 2.
Proof. intros n H. rewrite rz_log_small by lia. destruct (n <=? 48); [lia|]. destruct (n <=? 96); lia. Qed.

#[using="Type"] Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2. reflexivity. unfold rz_log.
  repeat (destruct (_ <=? _)); lia. Qed.

#[using="Type"] Lemma rounded_size_eq : forall n, rounded_size n = (Z.max n 8 + 7) / 8 * 8.
Proof. intros n. unfold rounded_size, rup. f_equal. f_equal. lia. Qed.

#[using="Type"] Lemma small_facts : forall n, 1 <= n <= 448 ->
  is_primary n = true /\ needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 64 /\ rz_size n = 16 * 2 ^ rz_log n
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 512.
Proof.
  intros n H.
  pose proof (rz_log_range_small n H) as R. pose proof (rz_size_eq n) as S.
  assert (S2 : 16 <= rz_size n <= 64).
  { rewrite S. assert (2 ^ rz_log n = 1 \/ 2 ^ rz_log n = 2 \/ 2 ^ rz_log n = 4).
    { destruct (Z.eq_dec (rz_log n) 0) as [->|]; [left; reflexivity|]. destruct (Z.eq_dec (rz_log n) 1) as [->|]; [right; left; reflexivity|].
      replace (rz_log n) with 2 by lia. right; right; reflexivity. } lia. }
  pose proof (rounded_size_eq n) as RS.
  assert (RR : Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0).
  { rewrite RS. Z.div_mod_to_equations. lia. }
  assert (P : is_primary n = true).
  { unfold is_primary, needed0, K_MAX_SIZE. apply Z.leb_le. lia. }
  assert (NS : needed_size n = rounded_size n + rz_size n).
  { unfold needed_size. rewrite P. reflexivity. }
  assert (UP : rounded_size n + rz_size n <= 512).
  { rewrite S, RS. rewrite rz_log_small by lia.
    destruct (Z.leb_spec n 48); [cbn; Z.div_mod_to_equations; lia|].
    destruct (Z.leb_spec n 96); cbn; Z.div_mod_to_equations; lia. }
  rewrite NS. split; [exact P|]. split; [reflexivity|]. split; [lia|]. split; [exact S|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof.
  intros x Hx.
  replace 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 64) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma rounded_size_align : forall n, rounded_size n = Z.max n 8 + 7 - (Z.max n 8 + 7) mod 8.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sllw_rz : forall n, 1 <= n <= 448 ->
  bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n N. pose proof (rz_log_range_small n N) as RLR. pose proof (rz_size_eq n) as RZE.
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  assert (P4 : 2 ^ rz_log n <= 2 ^ 2) by (apply Z.pow_le_mono_r; lia).
  assert (P1 : 0 < 2 ^ rz_log n) by (apply Z.pow_pos_nonneg; lia).
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma land_align8_48 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof.
  intros x Hx.
  replace 281474976710648 with (Z.ldiff (Z.ones 48) (Z.ones 3)) by reflexivity.
  replace (x - x mod 8) with (Z.shiftl (Z.shiftr x 3) 3).
  2:{ rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite <- Z.ldiff_ones_r by lia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec i 48) as [L|L]; cbn.
  - reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.bits_0. reflexivity. }
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia |].
    apply Z.lt_le_trans with 48; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma rz_size_small_cases : forall n, 1 <= n <= 448 -> rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64.
Proof.
  intros n N. rewrite rz_size_eq, (rz_log_small n N).
  destruct (n <=? 48); [left; reflexivity|]. destruct (n <=? 96); [right; left; reflexivity| right; right; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_fast_eq : forall RESV st n c,
  1 <= n <= 448 -> class_id (needed_size n) = c -> 0 < c_count (get_cls st c) ->
  amalloc ATOP RESV st n =
    SRet (set_next (N.succ (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
            (set_live (<[ a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) := CPrim c n ]>
                        (a_live (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)),
          Some (a_next (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st))).
Proof.
  intros RESV st n c N HC POS. (pose proof (small_facts n N) as ndP__; nd_pre ndP__ 7%nat; intros PRIM NS RZR RZE RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM. unfold cache_alloc. rewrite HC.
  replace (0 <? c_count (get_cls st c)) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

#[using="Type"] Lemma a_next_put_cls : forall c r st, a_next (put_cls c r st) = a_next st.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma a_live_put_cls : forall c r st, a_live (put_cls c r st) = a_live st.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma class_id_small : forall s, s <= 512 -> class_id s = Z.shiftr (s + 31) 5.
Proof. intros s Hs. unfold class_id. replace (s <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
#[using="Type"] Lemma size_of_class_small : forall c, c <= 16 -> size_of_class c = 32 * c.
Proof. intros c Hc. unfold size_of_class. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
#[using="Type"] Lemma class_small_facts : forall n c, 1 <= n <= 448 -> class_id (needed_size n) = c ->
  1 <= c <= 16 /\ Z.shiftr (needed_size n + 31) 5 = c /\ size_of_class c = 32 * c /\ needed_size n <= size_of_class c <= 512.
Proof.
  intros n c N HC. (pose proof (small_facts n N) as ndP__; nd_pre ndP__ 7%nat; intros PRIM NS RZR RZE RSR RSM NSR; nd_post).
  rewrite class_id_small in HC by lia.
  assert (C : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof (size_of_class_small c ltac:(lia)) as S.
  split; [exact C|]. split; [exact HC|]. split; [exact S|].
  rewrite S. rewrite <- HC. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma max_cached_le16 : forall c, 1 <= c -> max_cached c <= 16.
Proof. intros c Hc. unfold max_cached. lia. Qed.
End CANSEC1.
End TwB.
End AModelFacts.

(* [comment removed for export] *)
Module APrimFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From stdpp Require Import bitvector.definitions.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Fixpoint forallb_range (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => if f lo then forallb_range f (lo + 1) k else false end.

#[using="Type"] Lemma forallb_range_spec : forall f n lo, forallb_range f lo n = true -> forall z, lo <= z < lo + Z.of_nat n -> f z = true.
Proof.
  intros f n. induction n as [|k IH]; intros lo H z Hz; [lia|].
  cbn [forallb_range] in H. destruct (f lo) eqn:E; [| discriminate].
  destruct (Z.eq_dec z lo) as [->|NE]; [exact E|]. apply (IH (lo + 1) H). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_by_compute : forall (P : Z -> Prop) (f : Z -> bool) lo hi,
  (forall z, f z = true -> P z) -> forallb_range f lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> P z.
Proof.
  intros P f lo hi Hf Hb z Hz. apply Hf. apply (forallb_range_spec f _ lo Hb). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_bv_eq : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_bv_eq8 : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => negb (z mod 8 =? 0) || Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> z mod 8 = 0 -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz M8. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  replace (z mod 8 =? 0) with true in E by (symmetry; apply Z.eqb_eq; exact M8). cbn in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

#[using="Type"] Lemma rz_size_cases : forall n,
  rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/ rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof.
  intros n. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6 \/ rz_log n = 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn; lia.
Qed.

#[using="Type"] Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; (split; [lia| reflexivity]). Qed.

#[using="Type"] Lemma rounded_facts : forall n, Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma prim_facts : forall n, 1 <= n -> is_primary n = true ->
  needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 2048 /\ rz_size n = 16 * 2 ^ rz_log n /\ rz_size n mod 16 = 0 /\ 0 <= rz_log n <= 7
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 65536.
Proof.
  intros n N PRIM. pose proof (rz_size_range n) as [R1 R2]. pose proof (rounded_facts n) as [Q1 Q2]. pose proof (rz_log_range n) as RL.
  unfold needed_size. rewrite PRIM. unfold is_primary, needed0, K_MAX_SIZE in PRIM. apply Z.leb_le in PRIM.
  unfold needed0. repeat split; try lia. apply rz_size_eq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sllw_rz_gen : forall n, bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. pose proof (rz_size_eq n) as RZE. pose proof (rz_size_range n) as [RR _].
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

#[using="Type"] Lemma sllw_rz_gen2 : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. rewrite <- (sllw_rz_gen n).
  rewrite !(Z.mod_small (rz_log n)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in let S := size_of_class c in
  (1 <=? c) && (c <=? 30) && (s <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (16 <=? S)
  && (implb (s <=? 512) (c =? Z.shiftr (s + 31) 5)) && (implb (512 <? s) (17 <=? c)).

#[using="Type"] Lemma class_ok_all : forallb_range class_ok 1 (Z.to_nat (65536 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma class_facts : forall s, 1 <= s <= 65536 ->
  let c := class_id s in let S := size_of_class c in
  1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S
  /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c).
Proof.
  intros s Hs. cbv zeta.
  pose proof (range_by_compute (fun s => let c := class_id s in let S := size_of_class c in
              1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c))
              class_ok 1 65536) as R.
  apply R; [| exact class_ok_all | exact Hs].
  intros z Hz. unfold class_ok in Hz. cbv zeta.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
Definition cls_ok (c : Z) : bool :=
  let S := size_of_class c in (16 <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (2 <=? max_cached c) && (max_cached c <=? 16)
  && (implb (17 <=? c) (S mod 256 =? 0)) && (implb (17 <=? c) (768 <=? S)).
#[using="Type"] Lemma cls_ok_all : forallb_range cls_ok 1 (Z.to_nat (30 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma cls_facts : forall c, 1 <= c <= 30 ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
  /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c).
Proof.
  intros c Hc.
  pose proof (range_by_compute (fun c => 16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
              /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c)) cls_ok 1 30) as R.
  apply R; [| exact cls_ok_all | exact Hc].
  intros z Hz. unfold cls_ok in Hz. cbv zeta in Hz.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma prim_class_facts : forall n c, 1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  1 <= c <= 30 /\ needed_size n <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0
  /\ (needed_size n <= 512 -> c = Z.shiftr (needed_size n + 31) 5 /\ size_of_class c = 32 * c)
  /\ 2 <= max_cached c <= 16.
Proof.
  intros n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR _ _ _ _ _ NR; nd_post).
  pose proof (class_facts (needed_size n) ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF.
  (nd_pre CF 6%nat; intros C1 C2 C3 C4 C5 C6; nd_post).
  (pose proof (cls_facts c C1) as ndP__; nd_pre ndP__ 4%nat; intros D1 D2 D3 D4; nd_post).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [| exact D3].
  intros L. split; [exact (C5 L)|]. apply size_of_class_small. specialize (C5 L). rewrite C5.
  rewrite Z.shiftr_div_pow2 by lia. clear -L NR. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Lists.List.
Import stdpp.bitvector.definitions.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB.
Import stdpp.gmap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Fixpoint forallb_range (f : Z -> bool) (lo : Z) (n : nat) : bool :=
  match n with O => true | S k => if f lo then forallb_range f (lo + 1) k else false end.

#[using="Type"] Lemma forallb_range_spec : forall f n lo, forallb_range f lo n = true -> forall z, lo <= z < lo + Z.of_nat n -> f z = true.
Proof.
  intros f n. induction n as [|k IH]; intros lo H z Hz; [lia|].
  cbn [forallb_range] in H. destruct (f lo) eqn:E; [| discriminate].
  destruct (Z.eq_dec z lo) as [->|NE]; [exact E|]. apply (IH (lo + 1) H). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_by_compute : forall (P : Z -> Prop) (f : Z -> bool) lo hi,
  (forall z, f z = true -> P z) -> forallb_range f lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> P z.
Proof.
  intros P f lo hi Hf Hb z Hz. apply Hf. apply (forallb_range_spec f _ lo Hb). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_bv_eq : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma range_bv_eq8 : forall (e c : Z -> Z) lo hi,
  forallb_range (fun z => negb (z mod 8 =? 0) || Z.eqb (e z mod 2^64) (c z mod 2^64)) lo (Z.to_nat (hi - lo + 1)) = true ->
  forall z, lo <= z <= hi -> z mod 8 = 0 -> Z_to_bv 64 (e z) = Z_to_bv 64 (c z).
Proof.
  intros e c lo hi Hb z Hz M8. pose proof (forallb_range_spec _ _ _ Hb z ltac:(lia)) as E. cbn beta in E.
  replace (z mod 8 =? 0) with true in E by (symmetry; apply Z.eqb_eq; exact M8). cbn in E.
  apply Z.eqb_eq in E. apply Z_to_bv_eqm. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

#[using="Type"] Lemma rz_size_cases : forall n,
  rz_size n = 16 \/ rz_size n = 32 \/ rz_size n = 64 \/ rz_size n = 128 \/ rz_size n = 256 \/ rz_size n = 512 \/ rz_size n = 1024 \/ rz_size n = 2048.
Proof.
  intros n. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  assert (E : rz_log n = 0 \/ rz_log n = 1 \/ rz_log n = 2 \/ rz_log n = 3 \/ rz_log n = 4 \/ rz_log n = 5 \/ rz_log n = 6 \/ rz_log n = 7) by lia.
  destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn; lia.
Qed.

#[using="Type"] Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; (split; [lia| reflexivity]). Qed.

#[using="Type"] Lemma rounded_facts : forall n, Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0.
Proof. intros n. rewrite rounded_size_eq. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma prim_facts : forall n, 1 <= n -> is_primary n = true ->
  needed_size n = rounded_size n + rz_size n
  /\ 16 <= rz_size n <= 2048 /\ rz_size n = 16 * 2 ^ rz_log n /\ rz_size n mod 16 = 0 /\ 0 <= rz_log n <= 7
  /\ Z.max n 8 <= rounded_size n <= Z.max n 8 + 7 /\ rounded_size n mod 8 = 0
  /\ 24 <= needed_size n <= 65536.
Proof.
  intros n N PRIM. pose proof (rz_size_range n) as [R1 R2]. pose proof (rounded_facts n) as [Q1 Q2]. pose proof (rz_log_range n) as RL.
  unfold needed_size. rewrite PRIM. unfold is_primary, needed0, K_MAX_SIZE in PRIM. apply Z.leb_le in PRIM.
  unfold needed0. repeat split; try lia. apply rz_size_eq.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sllw_rz_gen : forall n, bv_swrap 32 (Z.shiftl 16 ((rz_log n mod 18446744073709551616) mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. pose proof (rz_size_eq n) as RZE. pose proof (rz_size_range n) as [RR _].
  rewrite !(Z.mod_small (rz_log n)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite RZE.
  apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N (32 - 1)) with 2147483648 by reflexivity. lia.
Qed.

#[using="Type"] Lemma sllw_rz_gen2 : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n) as RLR. rewrite <- (sllw_rz_gen n).
  rewrite !(Z.mod_small (rz_log n)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition class_ok (s : Z) : bool :=
  let c := class_id s in let S := size_of_class c in
  (1 <=? c) && (c <=? 30) && (s <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (16 <=? S)
  && (implb (s <=? 512) (c =? Z.shiftr (s + 31) 5)) && (implb (512 <? s) (17 <=? c)).

#[using="Type"] Lemma class_ok_all : forallb_range class_ok 1 (Z.to_nat (65536 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma class_facts : forall s, 1 <= s <= 65536 ->
  let c := class_id s in let S := size_of_class c in
  1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S
  /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c).
Proof.
  intros s Hs. cbv zeta.
  pose proof (range_by_compute (fun s => let c := class_id s in let S := size_of_class c in
              1 <= c <= 30 /\ s <= S <= 65536 /\ S mod 16 = 0 /\ 16 <= S /\ (s <= 512 -> c = Z.shiftr (s + 31) 5) /\ (512 < s -> 17 <= c))
              class_ok 1 65536) as R.
  apply R; [| exact class_ok_all | exact Hs].
  intros z Hz. unfold class_ok in Hz. cbv zeta.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
Definition cls_ok (c : Z) : bool :=
  let S := size_of_class c in (16 <=? S) && (S <=? 65536) && (S mod 16 =? 0) && (2 <=? max_cached c) && (max_cached c <=? 16)
  && (implb (17 <=? c) (S mod 256 =? 0)) && (implb (17 <=? c) (768 <=? S)).
#[using="Type"] Lemma cls_ok_all : forallb_range cls_ok 1 (Z.to_nat (30 - 1 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma cls_facts : forall c, 1 <= c <= 30 ->
  16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
  /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c).
Proof.
  intros c Hc.
  pose proof (range_by_compute (fun c => 16 <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0 /\ 2 <= max_cached c <= 16
              /\ (17 <= c -> size_of_class c mod 256 = 0 /\ 768 <= size_of_class c)) cls_ok 1 30) as R.
  apply R; [| exact cls_ok_all | exact Hc].
  intros z Hz. unfold cls_ok in Hz. cbv zeta in Hz.
  repeat (apply andb_prop in Hz; destruct Hz as [Hz ?H]).
  repeat match goal with H : implb _ _ = true |- _ => rewrite implb_true_iff in H end.
  repeat split; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma prim_class_facts : forall n c, 1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  1 <= c <= 30 /\ needed_size n <= size_of_class c <= 65536 /\ size_of_class c mod 16 = 0
  /\ (needed_size n <= 512 -> c = Z.shiftr (needed_size n + 31) 5 /\ size_of_class c = 32 * c)
  /\ 2 <= max_cached c <= 16.
Proof.
  intros n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR _ _ _ _ _ NR; nd_post).
  pose proof (class_facts (needed_size n) ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF.
  (nd_pre CF 6%nat; intros C1 C2 C3 C4 C5 C6; nd_post).
  (pose proof (cls_facts c C1) as ndP__; nd_pre ndP__ 4%nat; intros D1 D2 D3 D4; nd_post).
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [| exact D3].
  intros L. split; [exact (C5 L)|]. apply size_of_class_small. specialize (C5 L). rewrite C5.
  rewrite Z.shiftr_div_pow2 by lia. clear -L NR. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.
End TwB.
End APrimFacts.
