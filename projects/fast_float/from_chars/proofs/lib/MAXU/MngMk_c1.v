(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGroup.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngRepr MngImage MngHeap MngSurgery AXG_ntfm AXG_ntfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngPost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition MKS (s' s : astate) : Prop := forall c, In c (markers s') -> In c (markers s).

Lemma MKS_refl : forall s, MKS s s.
Proof. intros s c H. exact H. Qed.

Lemma MKS_trans : forall s3 s2 s1, MKS s3 s2 -> MKS s2 s1 -> MKS s3 s1.
Proof. intros s3 s2 s1 A B c H. exact (B c (A c H)). Qed.

Lemma MKS_metas : forall s' s, st_metas s' = st_metas s -> MKS s' s.
Proof. intros s' s E c H. unfold markers, used_metas in *. rewrite E in H. exact H. Qed.

Lemma MKS_setm_same : forall s q am am', MT s q = Some (MUsed am) -> meta_markers am' = meta_markers am -> MKS (set_meta s q (MUsed am')) s.
Proof. intros s q am am' Hq Hm c H. rewrite (markers_set_meta s q am am' Hq Hm) in H. exact H. Qed.

Lemma MKS_setm_free : forall s q p n, MKS (set_meta s q (MFree p n)) s.
Proof.
  intros s q p n c H. rewrite !markers_eq in *. unfold used_metas, set_meta in *. cbn [st_metas set_metas] in H.
  induction (st_metas s) as [|[k y] t IH]; [exact H|].
  cbn [mupdate] in H. destruct (sptr_eqb q k) eqn:E.
  - cbn [flat_map app] in H |- *. destruct y; cbn [app] in *; try exact H. apply in_app_iff. right. exact H.
  - cbn [flat_map] in H |- *. rewrite !flat_map_app' in *. apply in_app_iff in H as [H|H]; apply in_app_iff; [left; exact H | right; exact (IH H)].
Qed.

(* [comment removed for export] *)
Lemma mm_links : forall am p n, meta_markers (am_set_links p n am) = meta_markers am.
Proof. intros am p n. reflexivity. Qed.
Lemma mm_freed : forall am f, meta_markers (am_set_freed f am) = meta_markers am.
Proof. intros am f. reflexivity. Qed.
Lemma mm_avail : forall am v, meta_markers (am_set_avail v am) = meta_markers am.
Proof. intros am v. reflexivity. Qed.

Lemma mm_forget : forall am i fr h, 0 <= i -> ss_fr (nth_slot am i) = Some fr -> fr_kind fr = FGroup ->
  meta_markers (upd_slot am i (mkSlot h None)) = meta_markers am.
Proof.
  intros am i fr h Hi Hfr Kfr.
  assert (Hlen : (Z.to_nat i < length (am_slots am))%nat).
  { destruct (Nat.lt_ge_cases (Z.to_nat i) (length (am_slots am))) as [A|A]; [exact A|].
    exfalso. unfold nth_slot in Hfr. rewrite nth_overflow in Hfr by exact A. discriminate. }
  pose proof (upd_slot_fields am i (mkSlot h None)) as (Fm & Fl & Fsc & Fml & Fst & Fex & Fss).
  unfold meta_markers. rewrite Fl. f_equal.
  apply flat_map_ext_In. intros j Hj. unfold zseq in Hj. apply in_map_iff in Hj as (k & <- & _).
  rewrite nth_slot_upd_slot by (first [exact Hi | lia | exact Hlen]).
  destruct (0 + Z.of_nat k =? i) eqn:E.
  + apply Z.eqb_eq in E. rewrite E. rewrite Hfr, Kfr. reflexivity.
  + unfold marker_cells, slot_end, frame_rsv. rewrite Fss, Fst. reflexivity.
Qed.
