(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition same_but_shadow (a b : astate) : Prop :=
  as_space_beg a = as_space_beg b /\ as_ptr_array a = as_ptr_array b /\ as_regions a = as_regions b /\ as_cache_inited a = as_cache_inited b
  /\ as_cache a = as_cache b /\ as_n_reserved a = as_n_reserved b /\ as_sec a = as_sec b /\ as_chunks a = as_chunks b /\ as_tq a = as_tq b
  /\ as_gq a = as_gq b /\ as_internal_init a = as_internal_init b /\ as_maps a = as_maps b /\ as_env a = as_env b
  /\ as_qmax a = as_qmax b /\ as_qmin a = as_qmin b /\ as_qcache a = as_qcache b.

Lemma sbs_refl : forall a, same_but_shadow a a. Proof. intros; repeat split; reflexivity. Qed.
Lemma sbs_trans : forall a b c, same_but_shadow a b -> same_but_shadow b c -> same_but_shadow a c.
Proof. intros a b c H1 H2. unfold same_but_shadow in *. intuition congruence. Qed.
Lemma sbs_paint : forall st lo hi v, same_but_shadow (paint st lo hi v) st.
Proof. intros. destruct st; repeat split; reflexivity. Qed.

Lemma poison_shadow_some : forall st a sz v,
  Z.land a 7 = 0 -> addr_is_in_mem a = true -> Z.land sz 7 = 0 -> addr_is_in_mem (a + sz - 8) = true ->
  exists st' ev, poison_shadow st a sz v = Some (st', ev) /\ same_but_shadow st' st.
Proof.
  intros st a sz v H1 H2 H3 H4. unfold poison_shadow. rewrite H1, H2, H3, H4. cbn [negb Z.eqb].
  set (st' := if 0 <? sz then paint st a (a + sz) v else st).
  assert (S : same_but_shadow st' st) by (subst st'; destruct (0 <? sz); [apply sbs_paint| apply sbs_refl]).
  repeat match goal with |- context [if ?b then _ else _] => destruct b; try (do 2 eexists; split; [reflexivity| exact S]) end.
  all: do 2 eexists; split; [reflexivity| exact S].
Qed.

(* [comment removed for export] *)
Definition hit_state (st : astate) (c cnt : Z) (rest : list Z) (ch : chunk) : astate :=
  upd_chunk (set_pc st c (mkPC (cnt - 1) rest)) ch.

(* [comment removed for export] *)
Lemma am_malloc_hit : forall st n kaddr c cp rest,
  0 <= n ->
  let r := compute_req n in
  let needed := rq_needed r in
  let U := compact_to_addr st c cp + rq_rz r in
  size_too_big r = false -> needed <= kMaxSize ->
  c = class_id needed -> 0 < c < kNumClasses ->
  pc_chunks (get_pc st c) = cp :: rest -> pc_count (get_pc st c) <> 0 ->
  (* [comment removed for export] *)
  Z.land U 7 = 0 -> addr_is_in_mem U = true -> addr_is_in_mem (U + Z.land (rq_size r) (Z.lnot 7) - 8) = true ->
  addr_is_in_mem (U + Z.land (rq_size r) (Z.lnot 7)) = true ->
  (rq_rz r = 16 \/ 32 <= rq_rz r) -> rq_primary r = true -> rq_rz r + rq_size r <= needed ->
  exists st' ev, am_malloc_k st n kaddr = Some (U, st', ev)
    /\ same_but_shadow st' (hit_state st c (pc_count (get_pc st c)) rest (mkChunk (compact_to_addr st c cp) U (rq_size r) (rq_rz r) c CAllocated)).
Proof.
  intros st n kaddr c cp rest Hn r needed U TB NK Hc HC PCS CNT AL8 IM1 IM2 IM3 RZ16 PRIM FIT.
  unfold am_malloc_k. replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold r. rewrite TB.
  fold needed. replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite <- Hc. unfold cache_alloc.
  replace ((c =? 0) || (kNumClasses <=? c)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply Z.leb_gt; lia]).
  replace (pc_count (get_pc st c) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNT).
  rewrite PCS.
  assert (CA : forall st1, as_space_beg st1 = as_space_beg st -> compact_to_addr st1 c cp = compact_to_addr st c cp)
    by (intros st1 E; unfold compact_to_addr, region_beg; rewrite E; reflexivity).
  rewrite (CA (set_pc _ _ _)) by (destruct st; reflexivity). fold U.
  replace (compact_to_addr st c cp + needed <? U + rq_size r) with false by (symmetry; apply Z.ltb_ge; subst U; lia).
  rewrite PRIM. cbn [negb].
  set (st2 := upd_chunk _ _).
  set (rd := Z.land (rq_size r) (Z.lnot 7)).
  assert (RD8 : Z.land rd 7 = 0) by (subst rd; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 7) 7), Z.land_lnot_diag, Z.land_0_r; reflexivity).
  assert (S14 : exists st4 ev4, (if 0 <? rd then poison_shadow st2 U rd 0 else Some (st2, [])) = Some (st4, ev4) /\ same_but_shadow st4 st2).
  { destruct (0 <? rd). 2:{ do 2 eexists. split; [reflexivity| apply sbs_refl]. }
    destruct (poison_shadow_some st2 U rd 0 AL8 IM1 RD8 IM2) as (st4 & ev4 & E & S). exists st4, ev4. split; [exact E| exact S]. }
  destruct S14 as (st4 & ev4 & E14 & S4). rewrite E14.
  fold rd in IM3. rewrite IM3. cbn [negb].
  assert (S15 : exists st5 ev5, (if negb (rq_size r =? rd) then Some (paint st4 (U + rd) (U + rd + 8) (Z.land (rq_size r) 7), [EShadow1 (U + rd) (Z.land (rq_size r) 7)]) else Some (st4, []))
                               = Some (st5, ev5) /\ same_but_shadow st5 st4).
  { destruct (negb (rq_size r =? rd)); do 2 eexists; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]. }
  destruct S15 as (st5 & ev5 & E15 & S5). rewrite E15.
  replace (negb (U - kChunkHeaderSize =? compact_to_addr st c cp) && (U - kChunkHeaderSize <? compact_to_addr st c cp + 16)) with false.
  2:{ symmetry. unfold kChunkHeaderSize. subst U. destruct RZ16 as [E|GE].
      - rewrite E. replace (compact_to_addr st c cp + 16 - 16 =? compact_to_addr st c cp) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      - rewrite andb_false_iff. right. apply Z.ltb_ge. lia. }
  do 2 eexists. split; [reflexivity|].
  eapply sbs_trans; [exact S5|]. eapply sbs_trans; [exact S4|]. subst st2. unfold hit_state. apply sbs_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import FMapPositive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Lemma gadd_find : forall (mp : PositiveMap.t chunk) k k' v,
  PositiveMap.find k' (PositiveMap.add k v mp) = if PositiveMap.E.eq_dec k k' then Some v else PositiveMap.find k' mp.
Proof.
  intros mp k k' v. destruct (PositiveMap.E.eq_dec k k') as [E|NE].
  - apply PositiveMap.find_1. apply PositiveMap.add_1. exact E.
  - destruct (PositiveMap.find k' mp) as [w|] eqn:F.
    + apply PositiveMap.find_1. apply PositiveMap.add_2; [exact NE|]. apply PositiveMap.find_2. exact F.
    + destruct (PositiveMap.find k' (PositiveMap.add k v mp)) as [w|] eqn:G; [|reflexivity].
      exfalso. apply PositiveMap.find_2 in G. apply PositiveMap.add_3 in G; [|exact NE]. apply PositiveMap.find_1 in G. congruence.
Qed.

Lemma chunk_list_in_iff : forall st x, In x (chunk_list st) <-> exists k, PositiveMap.find k (as_chunks st) = Some x.
Proof.
  intros st x. unfold chunk_list. rewrite in_map_iff. split.
  - intros [[k v] [E Hin]]. cbn in E. subst v. exists k. apply PositiveMap.elements_complete. exact Hin.
  - intros [k F]. exists (k, x). split; [reflexivity|]. apply PositiveMap.elements_correct. exact F.
Qed.

Lemma chunk_list_upd_iff : forall st ch x,
  In x (chunk_list (upd_chunk st ch)) <-> x = ch \/ exists k, PositiveMap.find k (as_chunks st) = Some x /\ k <> ckey (ch_user_beg ch).
Proof.
  intros st ch x. rewrite chunk_list_in_iff. unfold upd_chunk, set_chunks. cbn [as_chunks]. split.
  - intros [k F]. rewrite gadd_find in F. destruct (PositiveMap.E.eq_dec (ckey (ch_user_beg ch)) k) as [E|NE].
    + left. congruence.
    + right. exists k. split; [exact F| congruence].
  - intros [->|[k [F NE]]].
    + exists (ckey (ch_user_beg ch)). rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [reflexivity| congruence].
    + exists k. rewrite gadd_find. destruct (PositiveMap.E.eq_dec _ _); [congruence| exact F].
Qed.
