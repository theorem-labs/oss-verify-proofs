(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngHeap MngSurgery MngCtx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma nth_zupd_same : forall (l : list Z) k v d, (k < length l)%nat -> nth k (zupd l k v) d = v.
Proof. intros l. induction l as [|x t IH]; intros [|k] v d H; cbn in *; try lia; try reflexivity; apply IH; lia. Qed.

Lemma nth_zupd_other : forall (l : list Z) k k' v d, k' <> k -> nth k' (zupd l k v) d = nth k' l d.
Proof. intros l. induction l as [|x t IH]; intros [|k] [|k'] v d H; cbn in *; try lia; try reflexivity; apply IH; lia. Qed.

Lemma length_zupd : forall (l : list Z) k v, length (zupd l k v) = length l.
Proof. intros l. induction l as [|x t IH]; intros [|k] v; cbn; [reflexivity | reflexivity | reflexivity | rewrite IH; reflexivity]. Qed.

Definition usg_cell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ v).
Definition unm_cell (k : nat) (v : Z) : mcell := MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ v).
Definition seq_cell (v : Z) : mcell := MCell (LCtx CTX_seq) 1 (VZ v).
Definition fmh_cell (v : option sptr) : mcell := MCell (LCtx CTX_free_meta_head) 8 (optr v).

(* [comment removed for export] *)
Lemma cov_ctx_only : forall s s' c, st_metas s' = st_metas s -> st_areas s' = st_areas s ->
  In c (image s') -> In c (image s) \/ In c (ctx_cells s').
Proof.
  intros s s' c Em Ea Hc. unfold image in *. apply in_app_iff in Hc as [Hc|Hc]; [right; exact Hc|].
  left. apply in_app_iff. right. rewrite Ea in Hc. rewrite (areas_cells_metas s s' _ Em), (used_metas_metas s s' Em) in Hc. exact Hc.
Qed.

Lemma ctx_in_image : forall s c, In c (ctx_cells s) -> In c (image s).
Proof. intros s c H. unfold image. apply in_app_iff. left. exact H. Qed.

Ltac ctx_unf H := unfold ctx_cells in H; cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_usage set_seq set_unmap_seq set_free_meta_head] in H.
Ltac ctx_unfg := unfold ctx_cells; cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_usage set_seq set_unmap_seq set_free_meta_head].

Lemma cov_usage : forall s k v c, (k < length (st_usage s))%nat ->
  In c (ctx_cells (set_usage (zupd (st_usage s) k v) s)) -> In c (ctx_cells s) \/ c = usg_cell k v.
Proof.
  intros s k v c Hk Hc. ctx_unf Hc. ctx_unfg.
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; left; exact Hc|].
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
  apply in_app_iff in Hc as [Hc|Hc].
  - apply in_map_iff in Hc as (k' & <- & Hk'). destruct (Nat.eq_dec k' k) as [->|Hne].
    + right. unfold usg_cell. rewrite nth_zupd_same by exact Hk. reflexivity.
    + left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. rewrite nth_zupd_other by exact Hne.
      apply (in_map (fun k0 => MCell (LCtx (CTX_usage + 8 * Z.of_nat k0)) 8 (VZ (nth k0 (st_usage s) 0)))). exact Hk'.
  - left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

Lemma cov_seq : forall s v c, In c (ctx_cells (set_seq v s)) -> In c (ctx_cells s) \/ c = seq_cell v.
Proof.
  intros s v c Hc. ctx_unf Hc. ctx_unfg.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (right; reflexivity) | (left; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
  destruct Hc.
Qed.

Lemma cov_fmh : forall s v c, In c (ctx_cells (set_free_meta_head v s)) -> In c (ctx_cells s) \/ c = fmh_cell v.
Proof.
  intros s v c Hc. ctx_unf Hc. ctx_unfg.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (right; reflexivity) | (left; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
  destruct Hc.
Qed.

Lemma cov_unmap : forall s l c, length l = 32%nat ->
  In c (ctx_cells (set_unmap_seq l s)) -> In c (ctx_cells s) \/ exists k, (k < 32)%nat /\ c = unm_cell k (nth k l 0).
Proof.
  intros s l c Hl Hc. ctx_unf Hc. ctx_unfg.
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; left; exact Hc|].
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
  apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
  apply in_app_iff in Hc as [Hc|Hc].
  - right. apply in_map_iff in Hc as (k' & <- & Hk'). apply in_seq in Hk'. exists k'. split; [lia | reflexivity].
  - left. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma usg_cell_in : forall s k, (k < 48)%nat -> In (usg_cell k (nth k (st_usage s) 0)) (image s).
Proof.
  intros s k Hk. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply (in_map (fun k0 => MCell (LCtx (CTX_usage + 8 * Z.of_nat k0)) 8 (VZ (nth k0 (st_usage s) 0)))). apply in_seq. lia.
Qed.

Lemma unm_cell_in : forall s k, (k < 32)%nat -> In (unm_cell k (nth k (st_unmap_seq s) 0)) (image s).
Proof.
  intros s k Hk. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
  apply (in_map (fun k0 => MCell (LCtx (CTX_unmap_seq + Z.of_nat k0)) 1 (VZ (nth k0 (st_unmap_seq s) 0)))). apply in_seq. lia.
Qed.

Lemma seq_cell_in : forall s, In (seq_cell (st_seq s)) (image s).
Proof. intros s. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. repeat first [ (left; reflexivity) | right ]. Qed.

Lemma fmh_cell_in : forall s, In (fmh_cell (st_free_meta_head s)) (image s).
Proof. intros s. apply ctx_in_image. unfold ctx_cells. apply in_app_iff. left. cbn [In]. repeat first [ (left; reflexivity) | right ]. Qed.
