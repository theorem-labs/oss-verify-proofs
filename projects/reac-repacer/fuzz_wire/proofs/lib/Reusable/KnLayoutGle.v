(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/KnLayoutGle.v at 88154566652a (donor image sha256 61768cf4739b), with its module paths changed. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, for a Theorem Labs lane's driver adaptation): on the empty-depot kernel (DepotCfg.v:16,
   DepotCfg.depot_has_trace = false) the layout clause of acall_post is `exists l, layout_grow ly l /\ layout_le n l ly'`.
   layout_grow changes only ly_NB and ly_SB (YG0f.layout_grow), so the composite is a plain layout_le from ly with those two
   fields set to ly''s (gle_le). The driver files read only fields that layout_le keeps (top, stack bounds, extra, image),
   so with gle_le every positional read of the old layout_le works unchanged, at the first StackDepot Put and at every
   later call. A step that needs the whole layout_le from ly itself (AR_laws' al_layout) is a later call: the depot is not
   empty there, so both blocks are mapped (YG0n.depot_ok_mapped) and the composite is plain layout_le (YG0f.gle_mapped),
   as the kernel's own call-step lemmas do (YCbq.v, option (B)). gle_le_live takes st_depot S <> [] directly; gle_le_chunk,
   gle_le_blk and gle_le_ablocks take a live chunk / block / allocated block, which makes the depot non-empty
   (YG0n.am_alloc_depot).
   Image-free: it names no address of either image.
   rule 24: proves no function (kind: layout lemma). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YG00 YG01 YG04 YG0f YG0n YG0d YM05.
Import ListNotations.
Open Scope Z_scope.
Lemma gle_le : forall n ly ly', (exists l, layout_grow ly l /\ layout_le n l ly') ->
layout_le n (set_ly_SB (set_ly_NB ly (ly_NB ly')) (ly_SB ly')) ly'.
Proof.
intros n ly ly' (l & (nb & sb & _ & _ & ->) & L). pose proof L as L'.
destruct L' as (_ & _ & _ & _ & _ & _ & E7 & E8 & _). cbn in E7, E8. rewrite E7, E8. exact L.
Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma gle_le_live : forall segs B ly S W mem md n ly', AR segs B ly S W mem md -> st_depot S <> [] ->
(exists l, layout_grow ly l /\ layout_le n l ly') -> layout_le n ly ly'.
Proof.
intros segs B ly S W mem md n ly' HAR KDM Hg.
pose proof (depot_ok_mapped B ly _ S (am_depot B ly S _ (proj1 HAR)) KDM) as [KNB KSB].
exact (gle_mapped _ _ _ KNB KSB Hg).
Qed.
Lemma gle_le_chunk : forall segs B ly S W mem md n ly', AR segs B ly S W mem md -> (exists k, In k (st_chunks S)) ->
(exists l, layout_grow ly l /\ layout_le n l ly') -> layout_le n ly ly'.
Proof.
intros segs B ly S W mem md n ly' HAR Hk Hg.
exact (gle_le_live segs B ly S W mem md n ly' HAR (am_alloc_depot B ly S _ (proj1 HAR) Hk) Hg).
Qed.
Lemma gle_le_blk : forall segs B ly S W mem md n ly' x, AR segs B ly S W mem md -> In x (blocks S) ->
(exists l, layout_grow ly l /\ layout_le n l ly') -> layout_le n ly ly'.
Proof.
intros segs B ly S W mem md n ly' [p m] HAR Hb Hg. apply In_blocks in Hb as (k & Hk & _).
exact (gle_le_chunk segs B ly S W mem md n ly' HAR (ex_intro _ k Hk) Hg).
Qed.
Lemma gle_le_ablocks : forall segs B ly S W mem md n ly' x, AR segs B ly S W mem md -> In x (ablocks B ly S) ->
(exists l, layout_grow ly l /\ layout_le n l ly') -> layout_le n ly ly'.
Proof.
intros segs B ly S W mem md n ly' x HAR Hx Hg. unfold ablocks in Hx. apply in_map_iff in Hx as (b & _ & Hb).
exact (gle_le_blk segs B ly S W mem md n ly' b HAR Hb Hg).
Qed.
End k.
