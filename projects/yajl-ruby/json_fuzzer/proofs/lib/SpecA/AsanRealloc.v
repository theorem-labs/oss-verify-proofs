(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanRep AsanKern AsanClient AsanWf1 AsanWf4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma arun_mono : forall {R} f d (t : stree aev aans (astate * aout R)) orc res,
  arun f t orc = Some res -> arun (f + d)%nat t orc = Some res.
Proof.
  intros R f. induction f as [|f IH]; intros d t orc res H; destruct t as [[s o]|e k]; cbn in H |- *.
  - destruct d; cbn; exact H.
  - destruct orc; discriminate.
  - exact H.
  - destruct orc as [|a rest]; [discriminate|].
    destruct (arun f (k a) rest) as [[[[s o] evs] orc']|] eqn:HR; [| discriminate].
    rewrite (IH d (k a) rest _ HR). exact H.
Qed.

Lemma arun_sbind : forall {R S} (t : stree aev aans (astate * aout R)) (k : astate * aout R -> stree aev aans (astate * aout S))
    f1 f2 orc s1 o1 evs1 orc1 s2 o2 evs2 orc2,
  arun f1 t orc = Some (s1, o1, evs1, orc1) ->
  arun f2 (k (s1, o1)) orc1 = Some (s2, o2, evs2, orc2) ->
  arun (f1 + f2)%nat (sbind t k) orc = Some (s2, o2, evs1 ++ evs2, orc2).
Proof.
  intros R S t. induction t as [[s o]|e kk IH]; intros k f1 f2 orc s1 o1 evs1 orc1 s2 o2 evs2 orc2 H1 H2.
  - destruct f1; cbn in H1; injection H1 as <- <- <- <-; cbn [sbind app].
    + exact H2.
    + rewrite Nat.add_comm. apply arun_mono. exact H2.
  - destruct f1 as [|f1]; cbn in H1; [destruct orc; discriminate|].
    destruct orc as [|a rest]; [discriminate|].
    destruct (arun f1 (kk a) rest) as [[[[s' o'] evs'] orc']|] eqn:HR; [| discriminate].
    injection H1 as E1 E2 E3 E4. subst s' o' evs1 orc'. cbn [sbind Nat.add arun].
    rewrite (IH a k f1 f2 rest s1 o1 evs' orc1 s2 o2 evs2 orc2 HR H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arun_abind : forall {R S} (m : AM R) (k : R -> AM S) s0 f1 f2 orc s1 r evs1 orc1 s2 o2 evs2 orc2,
  arun f1 (m s0) orc = Some (s1, ONorm r, evs1, orc1) ->
  arun f2 (k r s1) orc1 = Some (s2, o2, evs2, orc2) ->
  arun (f1 + f2)%nat (abind m k s0) orc = Some (s2, o2, evs1 ++ evs2, orc2).
Proof.
  intros R S m k s0 f1 f2 orc s1 r evs1 orc1 s2 o2 evs2 orc2 H1 H2. unfold abind.
  eapply arun_sbind; [exact H1|]. cbn [fst snd]. exact H2.
Qed.

Lemma arun_aupd : forall (g : astate -> astate) s orc, arun 0%nat (aupd g s) orc = Some (g s, ONorm tt, [], orc).
Proof. reflexivity. Qed.
Lemma arun_aret : forall {R} (r : R) s orc, arun 0%nat (aret r s) orc = Some (s, ONorm r, [], orc).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section REA.
Variable E : aenv.
(* [comment removed for export] *)
Definition ia0 (a : astate) : astate := upd_ia_inited true a.
Definition ts0 (n : Z) (a : astate) : astate := upd_ts (ts_on_realloc n) a.

(* [comment removed for export] *)
Lemma arealloc_run_null : forall key n a f orc a' r evs orc',
  arun f (amalloc_core E key n (ia0 a)) orc = Some (a', ONorm r, evs, orc') ->
  exists f', arun f' (arealloc E key 0 n a) orc = Some (a', ONorm r, evs, orc').
Proof.
  intros key n a f orc a' r evs orc' H. exists (0 + f)%nat. unfold arealloc, ia_init. rewrite Z.eqb_refl.
  replace evs with ([] ++ evs) by reflexivity.
  eapply arun_abind; [apply arun_aupd| exact H].
Qed.

(* [comment removed for export] *)
Lemma arealloc_run_none : forall key p n a f orc a1 evs orc',
  p <> 0 -> n <> 0 ->
  arun f (amalloc_core E key n (ts0 n (ia0 a))) orc = Some (a1, ONorm None, evs, orc') ->
  exists f', arun f' (arealloc E key p n a) orc = Some (a1, ONorm (@None Z), evs, orc').
Proof.
  intros key p n a f orc a1 evs orc' Hp Hn H. unfold arealloc, ia_init.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn).
  exists (0 + (0 + (f + 0)))%nat.
  replace evs with ([] ++ ([] ++ (evs ++ []))) by (rewrite app_nil_r; reflexivity).
  eapply arun_abind; [apply arun_aupd|].
  eapply arun_abind; [apply arun_aupd|].
  eapply arun_abind; [exact H|]. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arealloc_run_some : forall key p n a f1 f2 orc a1 q evs1 orc1 meta aid a2 evs2 orc2,
  p <> 0 -> n <> 0 ->
  arun f1 (amalloc_core E key n (ts0 n (ia0 a))) orc = Some (a1, ONorm (Some q), evs1, orc1) ->
  as_chunks a1 !! (p - kChunkHeaderSize) = Some meta -> cm_state meta = CAllocated aid -> cm_user_beg meta = p ->
  arun f2 (afree_core E key p a1) orc1 = Some (a2, ONorm tt, evs2, orc2) ->
  exists f, arun f (arealloc E key p n a) orc = Some (a2, ONorm (Some q), evs1 ++ evs2, orc2).
Proof.
  intros key p n a f1 f2 orc a1 q evs1 orc1 meta aid a2 evs2 orc2 Hp Hn H1 CM ST UB H2. unfold arealloc, ia_init.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp). replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hn).
  exists (0 + (0 + (f1 + (0 + (f2 + 0)))))%nat.
  replace (evs1 ++ evs2) with ([] ++ ([] ++ (evs1 ++ ([] ++ (evs2 ++ []))))) by (rewrite app_nil_r; reflexivity).
  eapply arun_abind; [apply arun_aupd|].
  eapply arun_abind; [apply arun_aupd|].
  eapply arun_abind; [exact H1|]. cbn beta iota.
  eapply (arun_abind aget); [reflexivity|]. rewrite CM, ST, UB, Z.eqb_refl.
  eapply arun_abind; [exact H2|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_block_meta : forall P D a p m, AWf E P D a -> In (p, m) (live_blocks a) ->
  exists meta aid, as_chunks a !! (p - kChunkHeaderSize) = Some meta /\ cm_state meta = CAllocated aid /\ cm_user_beg meta = p /\ cm_n meta = m.
Proof.
  intros P D a p m WF Hin. unfold live_blocks, chunk_list in Hin.
  apply in_map_iff in Hin. destruct Hin as ([k cm] & E1 & Hin). cbn in E1. injection E1 as E2 E3.
  apply filter_In in Hin. destruct Hin as [Hin AL]. cbn in AL.
  apply (proj2 (list_elem_of_In _ _)) in Hin. apply elem_of_map_to_list in Hin.
  pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 k cm Hin) as (KB & _).
  destruct (cm_state cm) as [aid|] eqn:STc; [| discriminate].
  exists cm, aid. rewrite <- E2. change (cm_user_beg cm - kChunkHeaderSize) with (cm_chunk_beg cm). rewrite <- KB.
  split; [exact Hin|]. split; [exact STc|]. split; [reflexivity| exact E3].
Qed.

(* [comment removed for export] *)
Lemma ia0_ts0_fields : forall n a,
  as_chunks (ts0 n (ia0 a)) = as_chunks a /\ as_regions (ts0 n (ia0 a)) = as_regions a /\ as_cache (ts0 n (ia0 a)) = as_cache a
  /\ as_sec (ts0 n (ia0 a)) = as_sec a /\ as_tq (ts0 n (ia0 a)) = as_tq a /\ as_gq (ts0 n (ia0 a)) = as_gq a
  /\ as_keys (ts0 n (ia0 a)) = as_keys a /\ as_frames (ts0 n (ia0 a)) = as_frames a
  /\ as_node_blocks (ts0 n (ia0 a)) = as_node_blocks a /\ as_store_blocks (ts0 n (ia0 a)) = as_store_blocks a
  /\ as_nprim_ever (ts0 n (ia0 a)) = as_nprim_ever a /\ as_ndepot_ins (ts0 n (ia0 a)) = as_ndepot_ins a /\ as_residue (ts0 n (ia0 a)) = as_residue a
  /\ as_ia_inited (ts0 n (ia0 a)) = true /\ as_ts (ts0 n (ia0 a)) = ts_on_realloc n (as_ts a).
Proof. intros n a. destruct a; repeat split; reflexivity. Qed.
End REA.
End RC__1.
