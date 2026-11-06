(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition readable_mono_in (z : zoneg) (m m' : bmem) : Prop := forall p n, in_zone z p n -> readable m p (Z.to_nat n) -> readable m' p (Z.to_nat n).

Lemma tree_wf_mono_in : forall m m' z z' o, readable_mono_in z m m' -> zone_grows z z' -> tree_wf m z o -> tree_wf m' z' o.
Proof.
  intros m m' z z' o R [G _]. revert o. apply (obj_ind_size (fun o => tree_wf m z o -> tree_wf m' z' o)).
  intros o IH H. destruct o; try exact H.
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|]. intros Hp. destruct (C Hp) as [C1 C2]. split; [now apply G|exact (R _ _ C1 C2)].
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C). split; [exact A|]. split; [exact B|]. intros Hp. destruct (C Hp) as [C1 C2]. split; [now apply G|exact (R _ _ C1 C2)].
  - cbn [tree_wf] in H |- *. destruct H as (A & B & C & D & E). repeat split; auto.
  - apply tree_wf_arr in H. apply tree_wf_arr. destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
    + intros Hk. destruct (H3 Hk) as [A B]. split; [exact A| now apply G].
    + apply trees_wf_forall. intros o' Ho'. apply IH; [|revert o' Ho'; now apply trees_wf_forall].
      rewrite obj_size_arr. pose proof (in_kids_size o' kids Ho'). lia.
  - apply tree_wf_map in H. apply tree_wf_map. destruct H as (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
    + intros Hk. destruct (H3 Hk) as [A B]. split; [exact A| now apply G].
    + apply trees_wf_forall. intros o' Ho'. apply IH; [|revert o' Ho'; now apply trees_wf_forall].
      rewrite obj_size_map. pose proof (in_kids_size o' kids Ho'). lia.
Qed.
Lemma tree_at_frame_in : forall m m' z z' a o,
  readable_mono_in z m m' -> zone_grows z z' -> (forall c, In c (obj_cells a o) -> agree_on m m' c OBJ_SIZE) ->
  tree_at m z a o -> tree_at m' z' a o.
Proof.
  intros m m' z z' a o R G Hc [H1 H2]. split; [eapply obj_at_frame; eauto| eapply tree_wf_mono_in; eauto].
Qed.

Definition in_chunks (z : zoneg) (x : Z) : Prop := exists c, In c (z_chunks z) /\ fst c <= x < fst c + CHUNK_HDR + snd c.
Definition zkept (z : zoneg) (hs : list (Z * Z)) (m m' : bmem) : Prop :=
  forall x, in_chunks z x -> Forall (outside x) hs -> m' x = m x.

Lemma in_alloc_in_chunks : forall z a n x, zone_valid z -> in_alloc z a n -> a <= x < a + n -> in_chunks z x.
Proof.
  intros z a n x V A Hx. destruct (in_alloc_chunk z a n V A) as (c & Hc & Hin). exists c. split; [exact Hc|].
  unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *. lia.
Qed.

Lemma zkept_agree_cell : forall z ls hs m m' c, zone_valid z -> Forall (fun h => store_ok z ls (fst h) (snd h)) hs -> zkept z hs m m' ->
  cell_ok z ls c -> agree_on m m' c OBJ_SIZE.
Proof.
  intros z ls hs m m' c V Hs K Hc x Hx. apply K.
  - destruct Hc as [A _]. eapply in_alloc_in_chunks; eauto.
  - apply Forall_forall. intros h Hh. pose proof (proj1 (Forall_forall _ _) Hs h Hh) as Sh.
    pose proof (store_ok_disj_cell z ls (fst h) (snd h) c V Hc Sh). unfold outside, rdisj in *. lia.
Qed.

Lemma completed_wf_frame_in : forall m m' z z' ls hs,
  zone_valid z -> readable_mono_in z m m' -> zone_grows z z' -> Forall (fun h => store_ok z ls (fst h) (snd h)) hs -> zkept z hs m m' ->
  completed_wf m z ls -> completed_wf m' z' ls.
Proof.
  intros m m' z z' ls hs V R G S K H l Hl i Hi. destruct (H l Hl i Hi) as (o & Ht & Hc). exists o. split.
  - eapply tree_at_frame_in; eauto. intros c Hcc. eapply zkept_agree_cell; eauto.
  - intros c Hcc. eapply cell_ok_mono_zone; eauto.
Qed.

Lemma readable_mono_in_of_zkept : forall z ls hs m m',
  zone_valid z -> Forall (fun h => store_ok z ls (fst h) (snd h)) hs -> zkept z hs m m' ->
  (forall x, in_chunks z x -> m x <> None -> m' x <> None) ->
  readable_mono_in z m m'.
Proof.
  intros z ls hs m m' V S K W p n Hz Hr. apply rdZ_some_iff. intros i Hi. apply W.
  - destruct Hz as (c & Hc & Hin). exists c. split; [exact Hc|]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in *.
    destruct (Z.le_gt_cases 0 n) as [Hn|Hn]; [rewrite Z2Nat.id in Hi by lia| replace (Z.of_nat (Z.to_nat n)) with 0 in Hi by lia]; lia.
  - revert i Hi. apply rdZ_some_iff. exact Hr.
Qed.
