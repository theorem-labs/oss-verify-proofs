(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocWf BllocKit BG_MallocModel BG_WFHit BS_Refill1 BG_RefillModel BG_ColdModel.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition qch (ch : chunk) : chunk := mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine.

Definition tq_app (t : qcache) (m size : Z) : qcache :=
  let l := qc_list t in let lb := last l (mkQB 0 0 0 []) in
  mkQC (firstn (length l - 1)%nat l ++ [mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [m])]) (qc_bytes t + size).
Definition tq_new (t : qcache) (B m size : Z) : qcache :=
  mkQC (qc_list t ++ [mkQB B (size + kBatchSize) 1 [m]]) (qc_bytes t + size + kBatchSize).

Definition need_new (t : qcache) : bool :=
  match qc_list t with [] => true | _ => kBatchCount <=? qb_count (last (qc_list t) (mkQB 0 0 0 [])) end.

Definition free_app_state (st : astate) (ch : chunk) : astate :=
  set_tq (upd_chunk st (qch ch)) (tq_app (as_tq st) (ch_chunk_beg ch) (ch_used ch)).

Definition free_new_state (st : astate) (ch : chunk) (cp : Z) (rest : list Z) : astate :=
  set_tq (set_pc (upd_chunk st (qch ch)) kBatchClass (mkPC (pc_count (get_pc st kBatchClass) - 1) rest))
         (tq_new (as_tq st) (compact_to_addr st kBatchClass cp) (ch_chunk_beg ch) (ch_used ch)).

Definition gset (b a : astate) : astate :=
  mkState (as_space_beg b) (as_ptr_array b) (as_regions a) (as_cache_inited b) (as_cache b) (as_n_reserved b) (as_sec b) (as_chunks b)
          (as_tq b) (as_gq b) (as_internal_init b) (as_maps a) (as_shadow b) (as_env b) (as_track_shadow b) (as_qmax b) (as_qmin b) (as_qcache b).
Definition agree3 (a b : astate) : Prop := as_space_beg a = as_space_beg b /\ as_regions a = as_regions b /\ as_maps a = as_maps b.

Lemma poison_shadow_transfer : forall a b addr sz v,
  match poison_shadow a addr sz v with
  | None => poison_shadow b addr sz v = None
  | Some (a', ev) => exists b', poison_shadow b addr sz v = Some (b', ev) /\ same_but_shadow b' b /\ same_but_shadow a' a
  end.
Proof.
  intros a b addr sz v. unfold poison_shadow.
  repeat match goal with |- context [if ?x then _ else _] =>
    lazymatch x with context [poison_shadow] => fail | _ => destruct x end end;
    try reflexivity; eexists; (split; [reflexivity|]); split; first [apply sbs_paint | apply sbs_refl].
Qed.

Ltac sbs_solve :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat match goal with H : @eq _ ?x _ |- _ => is_var x; subst x | H : @eq _ _ ?x |- _ => is_var x; subst x end;
  repeat split; reflexivity.
Ltac dest_if := match goal with |- context [if ?x then _ else _] => lazymatch x with context [match _ with _ => _ end] => fail | _ => destruct x end end.

Lemma sbs_gset_same : forall a b, agree3 a b -> same_but_shadow b (gset b a).
Proof. intros a b AG. unfold same_but_shadow, agree3, gset in *; destruct a, b; cbn in *; sbs_solve. Qed.

Lemma efs_transfer : forall a b c nf, agree3 a b ->
  match ensure_free_array_space a c nf with
  | None => True
  | Some (a', ev) => exists b', ensure_free_array_space b c nf = Some (b', ev) /\ same_but_shadow b' (gset b a') /\ agree3 a' b'
  end.
Proof.
  intros a b c nf AG. pose proof AG as (E1 & E2 & E3). unfold ensure_free_array_space, get_region, free_array_base, region_beg. rewrite <- E1, <- E2.
  dest_if. { eexists. split; [reflexivity|]. split; [apply sbs_gset_same; exact AG| exact AG]. }
  dest_if; [exact I|].
  unfold map_fixed.
  match goal with |- context [poison_shadow (add_map a ?mp) ?x ?y ?v] =>
    pose proof (poison_shadow_transfer (add_map a mp) (add_map b mp) x y v) as PT; destruct (poison_shadow (add_map a mp) x y v) as [[a2 ev2]|]; [| exact I] end.
  destruct PT as (b2 & EB & SB & SA). rewrite EB.
  eexists. split; [reflexivity|].
  unfold same_but_shadow, agree3, gset in *; destruct a, b, a2, b2; cbn in *; sbs_solve.
Qed.

Lemma pfa_transfer : forall a b c rq, agree3 a b ->
  match populate_free_array a c rq with
  | None => True
  | Some (a', ev) => exists b', populate_free_array b c rq = Some (b', ev) /\ same_but_shadow b' (gset b a') /\ agree3 a' b'
  end.
Proof.
  intros a b c rq AG. pose proof AG as (E1 & E2 & E3).
  assert (GR : get_region b c = get_region a c) by (unfold get_region; rewrite E2; reflexivity).
  assert (RBq : region_beg b c = region_beg a c) by (unfold region_beg; rewrite E1; reflexivity).
  unfold populate_free_array. rewrite GR, RBq.
  set (r := get_region a c).
  dest_if.
  -
    pose proof (efs_transfer a b c (rg_num_freed r + (rg_mapped_user r - rg_allocated_user r) / class_size c) AG) as ET.
    destruct (ensure_free_array_space a c _) as [[a2 ev2]|]; [| exact I].
    destruct ET as (b2 & EB & SB & AG2). rewrite EB.
    assert (GR2 : get_region b2 c = get_region a2 c) by (unfold get_region; rewrite (proj1 (proj2 AG2)); reflexivity). rewrite GR2.
    dest_if; [exact I|].
    eexists. split; [reflexivity|].
    unfold same_but_shadow, agree3, gset, set_region in *; destruct a, b, a2, b2; cbn in *; sbs_solve.
  - dest_if; [exact I|]. unfold map_fixed.
    match goal with |- context [poison_shadow (add_map a ?mp) ?x ?y ?v] =>
      pose proof (poison_shadow_transfer (add_map a mp) (add_map b mp) x y v) as PT; destruct (poison_shadow (add_map a mp) x y v) as [[a2 ev2]|]; [| exact I] end.
    destruct PT as (b2 & EB & SB & SA). rewrite EB.
    match goal with |- context [ensure_free_array_space (set_region a2 c ?r2) c ?k] =>
      assert (AG2 : agree3 (set_region a2 c r2) (set_region b2 c r2))
        by (unfold same_but_shadow, agree3, set_region, add_map in *; destruct a, b, a2, b2; cbn in *; sbs_solve);
      pose proof (efs_transfer (set_region a2 c r2) (set_region b2 c r2) c k AG2) as ET;
      destruct (ensure_free_array_space (set_region a2 c r2) c k) as [[a3 ev3]|]; [| exact I] end.
    destruct ET as (b3 & EB3 & SB3 & AG3). rewrite EB3.
    assert (GR3 : get_region b3 c = get_region a3 c) by (unfold get_region; rewrite (proj1 (proj2 AG3)); reflexivity). rewrite GR3.
    dest_if; [exact I|].
    eexists. split; [reflexivity|].
    unfold same_but_shadow, agree3, gset, set_region, add_map in *; destruct a, b, a2, b2, a3, b3; cbn in *; sbs_solve.
Qed.

Lemma gfa_transfer : forall a b c n, agree3 a b ->
  match get_from_allocator a c n with
  | None => True
  | Some (a', l, ev) => exists b', get_from_allocator b c n = Some (b', l, ev) /\ same_but_shadow b' (gset b a')
  end.
Proof.
  intros a b c n AG. pose proof AG as (E1 & E2 & E3).
  assert (GR : get_region b c = get_region a c) by (unfold get_region; rewrite E2; reflexivity).
  unfold get_from_allocator. rewrite GR.
  dest_if.
  - pose proof (pfa_transfer a b c (n - rg_num_freed (get_region a c)) AG) as PT.
    destruct (populate_free_array a c _) as [[a1 ev1]|]; [| exact I].
    destruct PT as (b1 & EB & SB & AG1). rewrite EB.
    assert (GR1 : get_region b1 c = get_region a1 c) by (unfold get_region; rewrite (proj1 (proj2 AG1)); reflexivity). rewrite !GR1.
    dest_if; [exact I|]. cbv beta iota. rewrite !GR1.
    eexists. split; [reflexivity|].
    unfold same_but_shadow, agree3, gset, set_region in *; destruct a, b, a1, b1; cbn in *; sbs_solve.
  - cbv beta iota. rewrite !GR. eexists. split; [reflexivity|].
    unfold same_but_shadow, agree3, gset, set_region in *; destruct a, b; cbn in *; sbs_solve.
Qed.

Lemma set_internal_init_id : forall st, as_internal_init st = true -> set_internal_init st = st.
Proof. intros st H. destruct st; cbn in *. subst. reflexivity. Qed.

Lemma sbs_set_tq : forall a b q, same_but_shadow a b -> same_but_shadow (set_tq a q) (set_tq b q).
  Proof. intros a b q S. unfold same_but_shadow in *. destruct a, b; cbn in *; sbs_solve. Qed.
Lemma sbs_fields : forall a b, same_but_shadow a b ->
  as_tq a = as_tq b /\ as_qcache a = as_qcache b /\ as_qmax a = as_qmax b /\ as_cache a = as_cache b /\ as_space_beg a = as_space_beg b
  /\ as_regions a = as_regions b /\ as_cache_inited a = as_cache_inited b /\ as_chunks a = as_chunks b.
Proof. intros a b S. unfold same_but_shadow in S. repeat match goal with H : _ /\ _ |- _ => destruct H end. repeat split; assumption. Qed.

Section FreeModel.
  Variables (st : astate) (ch : chunk).
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let st0 := set_internal_init st.

  Hypothesis FIND : find_chunk (as_chunks st) U = Some ch.
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis SZ : 1 <= size.
  Hypothesis QMAX : size <= as_qmax st /\ as_qcache st <> 0.

  Hypothesis AL8 : Z.land U 7 = 0.
  Hypothesis IM1 : addr_is_in_mem U = true.
  Hypothesis IM2 : addr_is_in_mem (U + round_up size 8 - 8) = true.

  Let UPOS : 0 < U.
  Proof. unfold find_chunk in FIND. subst U. destruct (ch_user_beg ch <=? 0) eqn:E; [discriminate| apply Z.leb_gt in E; exact E]. Qed.

  Lemma poison_free_some : forall stx, exists st' , poison_shadow stx U (round_up size 8) kAsanHeapFreeMagic = Some (st', [EPoison U (round_up size 8) kAsanHeapFreeMagic])
                                               /\ same_but_shadow st' stx.
  Proof.
    intros stx. unfold poison_shadow. rewrite AL8, IM1, IM2.
    replace (Z.land (round_up size 8) 7 =? 0) with true by (symmetry; apply Z.eqb_eq; rewrite land7_mod8; unfold round_up; Z.div_mod_to_equations; lia).
    cbn [negb Z.eqb kAsanHeapFreeMagic].
    eexists. split; [reflexivity|]. destruct (0 <? round_up size 8); [apply sbs_paint| apply sbs_refl].
  Qed.

  Lemma am_free_unfold : exists ev0 stp,
       (forall K : astate -> list effect -> option (astate * list effect), True) /\
       same_but_shadow stp (upd_chunk st0 (qch ch)) /\ syscalls_of ev0 = [] /\
       am_free_full st U
       = match quarantine_enqueue stp (ch_chunk_beg (qch ch)) size with
         | None => None
         | Some (st2, ev2) =>
             match (if as_qcache st2 <? qc_bytes (as_tq st2)
                    then match quarantine_drain st2 with None => None | Some (st3, ev3) => Some (st3, [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2 ++ ev3) end
                    else Some (st2, [EPoison U (round_up size 8) kAsanHeapFreeMagic] ++ ev2)) with
             | None => None
             | Some (st4, ev4) => Some (st4, ev0 ++ [EStore64 U 0xFFFFFFFF00000000; EStore64 U 0] ++ ev4)
             end
         end.
  Proof.
    assert (E0 : exists ev0, (if as_internal_init st then (st, []) else (set_internal_init st, [EInternalAllocInit])) = (st0, ev0) /\ syscalls_of ev0 = []).
    { subst st0. destruct (as_internal_init st) eqn:II.
      - exists []. rewrite (set_internal_init_id st II). split; reflexivity.
      - exists [EInternalAllocInit]. split; reflexivity. }
    destruct E0 as (ev0 & E0 & SC0).
    destruct (poison_free_some (upd_chunk st0 (qch ch))) as (stp & EP & SP).
    exists ev0, stp. split; [intros; exact I|]. split; [exact SP|]. split; [exact SC0|].
    unfold am_free_full. rewrite E0.
    replace (U =? 0) with false by (symmetry; apply Z.eqb_neq; clear - UPOS; lia).
    assert (F0 : find_chunk (as_chunks st0) U = Some ch) by (subst st0; exact FIND). rewrite F0, ALLOC.
    change (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine) with (qch ch).
    unfold quarantine_put. change (ch_used (qch ch)) with size. change (ch_user_beg (qch ch)) with U.
    replace ((as_qcache (upd_chunk st0 (qch ch)) =? 0) || (as_qmax (upd_chunk st0 (qch ch)) <? size)) with false.
    2:{ symmetry. apply orb_false_intro; [apply Z.eqb_neq| apply Z.ltb_ge]; subst st0; cbn; clear - QMAX; lia. }
    rewrite EP.
    destruct (quarantine_enqueue stp (ch_chunk_beg (qch ch)) size) as [[st2 ev2]|]; [| reflexivity].
    destruct (as_qcache st2 <? qc_bytes (as_tq st2)).
    - destruct (quarantine_drain st2) as [[st3 ev3]|]; reflexivity.
    - reflexivity.
  Qed.

  Lemma ensure_cache_inited_eq : forall x,
    ensure_cache_inited x = mkState (as_space_beg x) (as_ptr_array x) (as_regions x) true (as_cache x) (as_n_reserved x) (as_sec x) (as_chunks x) (as_tq x) (as_gq x)
                              (as_internal_init x) (as_maps x) (as_shadow x) (as_env x) (as_track_shadow x) (as_qmax x) (as_qmin x) (as_qcache x).
  Proof. intros x. unfold ensure_cache_inited. destruct x; cbn. destruct as_cache_inited; reflexivity. Qed.

End FreeModel.
