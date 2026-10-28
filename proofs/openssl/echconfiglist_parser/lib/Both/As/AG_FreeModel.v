(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit AS_Refill1 AG_RefillModel AG_ColdModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition qch (ch : chunk) : chunk := mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine.

(* [comment removed for export] *)
Definition tq_app (t : qcache) (m size : Z) : qcache :=
  let l := qc_list t in let lb := last l (mkQB 0 0 0 []) in
  mkQC (firstn (length l - 1)%nat l ++ [mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [m])]) (qc_bytes t + size).
Definition tq_new (t : qcache) (B m size : Z) : qcache :=
  mkQC (qc_list t ++ [mkQB B (size + kBatchSize) 1 [m]]) (qc_bytes t + size + kBatchSize).

(* [comment removed for export] *)
Definition need_new (t : qcache) : bool :=
  match qc_list t with [] => true | _ => kBatchCount <=? qb_count (last (qc_list t) (mkQB 0 0 0 [])) end.

Definition free_app_state (st : astate) (ch : chunk) : astate :=
  set_tq (upd_chunk st (qch ch)) (tq_app (as_tq st) (ch_chunk_beg ch) (ch_used ch)).
(* [comment removed for export] *)
Definition free_new_state (st : astate) (ch : chunk) (cp : Z) (rest : list Z) : astate :=
  set_tq (set_pc (upd_chunk st (qch ch)) kBatchClass (mkPC (pc_count (get_pc st kBatchClass) - 1) rest))
         (tq_new (as_tq st) (compact_to_addr st kBatchClass cp) (ch_chunk_beg ch) (ch_used ch)).

Lemma syscalls_of_app : forall a b, syscalls_of (a ++ b) = syscalls_of a ++ syscalls_of b.
Proof. induction a as [|e a IH]; intros b; [reflexivity|]. cbn. destruct e; cbn; rewrite IH; reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
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

Lemma gset_self : forall a, gset a a = a. Proof. intros a; destruct a; reflexivity. Qed.
Lemma sbs_gset : forall b b1 a a1, same_but_shadow b1 b -> same_but_shadow a1 a -> same_but_shadow (gset b1 a1) (gset b a).
Proof. intros b b1 a a1 S1 S2. unfold same_but_shadow in *; destruct a, a1, b, b1; cbn in *; sbs_solve. Qed.
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
  - (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Lemma am_free_app : need_new (as_tq st) = false -> qc_bytes (as_tq st) + size <= as_qcache st ->
    exists st' ev, am_free_full st U = Some (st', ev) /\ same_but_shadow st' (free_app_state st0 ch) /\ syscalls_of ev = [].
  Proof.
    intros NN NOD. destruct am_free_unfold as (ev0 & stp & _ & SP & SC0 & E). rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    destruct (qc_list (as_tq st)) as [|b0 l0] eqn:EL; [discriminate|]. rewrite NN.
    cbn [as_tq set_tq qc_bytes as_qcache].
    rewrite QC0. replace (as_qcache st <? qc_bytes (as_tq st) + size) with false by (symmetry; apply Z.ltb_ge; clear - NOD; lia).
    do 2 eexists. split; [reflexivity|]. split.
    - unfold free_app_state, tq_app. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
      replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity). rewrite EL. apply sbs_set_tq. exact SP.
    - rewrite !syscalls_of_app, SC0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma am_free_newhit : forall cp rest,
    need_new (as_tq st) = true -> pc_chunks (get_pc st kBatchClass) = cp :: rest -> pc_count (get_pc st kBatchClass) <> 0 ->
    0 < compact_to_addr st kBatchClass cp ->
    qc_bytes (as_tq st) + size + kBatchSize <= as_qcache st ->
    exists st' ev, am_free_full st U = Some (st', ev) /\ same_but_shadow st' (free_new_state st0 ch cp rest) /\ syscalls_of ev = [].
  Proof.
    intros cp rest NN PCS CNT BPOS NOD. destruct am_free_unfold as (ev0 & stp & _ & SP & SC0 & E). rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _ & Fca & Fsb & _).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    assert (PC0 : get_pc stp kBatchClass = get_pc st kBatchClass) by (unfold get_pc; rewrite Fca; subst st0; reflexivity).
    assert (CA0 : forall stx p, as_space_beg stx = as_space_beg st -> compact_to_addr stx kBatchClass p = compact_to_addr st kBatchClass p)
      by (intros stx p Hs; unfold compact_to_addr, region_beg; rewrite Hs; reflexivity).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite PC0.
    replace (pc_count (get_pc st kBatchClass) =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNT).
    rewrite PCS. rewrite (CA0 (set_pc stp kBatchClass _)) by (cbn; rewrite Fsb; subst st0; reflexivity).
    replace (compact_to_addr st kBatchClass cp =? 0) with false by (symmetry; apply Z.eqb_neq; clear - BPOS; lia).
    assert (NB : forall X : option (astate * list effect),
              (let need_new := match qc_list (as_tq st) with [] => true | _ :: _ => kBatchCount <=? qb_count (last (qc_list (as_tq st)) (mkQB 0 0 0 [])) end in
               if need_new then X
               else let l := qc_list (as_tq st) in let k := length l in let lb := last l (mkQB 0 0 0 []) in
                    let lb' := mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [ch_chunk_beg (qch ch)]) in
                    let t1 := mkQC (firstn (k - 1) l ++ [lb']) (qc_bytes (as_tq st) + size) in Some (set_tq stp t1, [])) = X).
    { intros X. destruct (qc_list (as_tq st)); [reflexivity|]. rewrite NN. reflexivity. }
    rewrite NB. clear NB.
    cbn [as_tq set_tq set_pc qc_bytes as_qcache qc_list]. rewrite TQ0, QC0.
    replace (as_qcache st <? qc_bytes (as_tq st) + size + kBatchSize) with false by (symmetry; apply Z.ltb_ge; clear - NOD; lia).
    do 2 eexists. split; [reflexivity|]. split.
    - unfold free_new_state, tq_new. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
      replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity).
      replace (get_pc st0 kBatchClass) with (get_pc st kBatchClass) by (subst st0; reflexivity).
      rewrite (CA0 st0) by (subst st0; reflexivity).
      apply sbs_set_tq. apply sbs_set_pc. exact SP.
    - rewrite !syscalls_of_app, SC0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ensure_cache_inited_eq : forall x,
    ensure_cache_inited x = mkState (as_space_beg x) (as_ptr_array x) (as_regions x) true (as_cache x) (as_n_reserved x) (as_sec x) (as_chunks x) (as_tq x) (as_gq x)
                              (as_internal_init x) (as_maps x) (as_shadow x) (as_env x) (as_track_shadow x) (as_qmax x) (as_qmin x) (as_qcache x).
  Proof. intros x. unfold ensure_cache_inited. destruct x; cbn. destruct as_cache_inited; reflexivity. Qed.

  Lemma am_free_refill : forall cp rest,
    WF st -> need_new (as_tq st) = true -> pc_count (get_pc st kBatchClass) = 0 ->
    rg_mapped_user (get_region st kBatchClass) + 2 * kUserMapSize <= kFreeArrayOffset ->
    kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0 ->
    let r := get_region st kBatchClass in
    firstn (Z.to_nat (rf_n kBatchClass)) (rf_fl1 kBatchClass (rg_num_freed r) (rg_allocated_user r) (rg_mapped_user r) (rg_free_array r)) = cp :: rest ->
    0 < compact_to_addr st kBatchClass cp ->
    qc_bytes (as_tq st) + size + kBatchSize <= as_qcache st ->
    exists st' ev, am_free_full st U = Some (st', ev) /\ same_but_shadow st' (free_new_state (refilled st0 kBatchClass) ch cp rest).
  Proof.
    intros cp rest W NN EMPTY ROOM HM r TAKEN BPOS NOD. destruct am_free_unfold as (ev0 & stp & _ & SP & SC0 & E). rewrite E.
    pose proof (sbs_fields _ _ SP) as (Ftq & Fqc & _ & Fca & Fsb & Frg & Fci & Fch).
    assert (TQ0 : as_tq stp = as_tq st) by (rewrite Ftq; subst st0; reflexivity).
    assert (QC0 : as_qcache stp = as_qcache st) by (rewrite Fqc; subst st0; reflexivity).
    assert (PC0 : get_pc stp kBatchClass = get_pc st kBatchClass) by (unfold get_pc; rewrite Fca; subst st0; reflexivity).
    assert (CA0 : forall stx p, as_space_beg stx = as_space_beg st -> compact_to_addr stx kBatchClass p = compact_to_addr st kBatchClass p)
      by (intros stx p Hs; unfold compact_to_addr, region_beg; rewrite Hs; reflexivity).
    assert (W0 : WF st0) by (subst st0; eapply WF_ext; [ .. | exact W]; reflexivity).
    assert (HC : 1 <= kBatchClass <= 30) by (unfold kBatchClass; lia).
    destruct (gfa_cold st0 kBatchClass W0 HC EMPTY ROOM HM) as (stg & evg & EG & SG).
    unfold quarantine_enqueue. rewrite TQ0. unfold need_new in NN.
    unfold cache_alloc. replace ((kBatchClass =? 0) || (kNumClasses <=? kBatchClass)) with false by reflexivity. rewrite PC0, EMPTY. cbn [Z.eqb].
    assert (AG3 : agree3 (ensure_cache_inited st0) (ensure_cache_inited stp)).
    { rewrite !ensure_cache_inited_eq. unfold agree3. cbn. rewrite Fsb, Frg. unfold same_but_shadow in SP. subst st0; cbn in SP |- *.
      repeat split; try reflexivity. symmetry. tauto. }
    pose proof (gfa_transfer (ensure_cache_inited st0) (ensure_cache_inited stp) kBatchClass (max_count kBatchClass / 2) AG3) as GT.
    change (rf_n kBatchClass) with (max_count kBatchClass / 2) in EG, TAKEN. rewrite EG in GT. destruct GT as (b' & EB & SB'). rewrite EB.
    cbn [pc_chunks pc_count]. change (get_region st0 kBatchClass) with r. rewrite TAKEN.
    assert (NB : forall X Y : option (astate * list effect),
              (if match qc_list (as_tq st) with [] => true | _ :: _ => kBatchCount <=? qb_count (last (qc_list (as_tq st)) (mkQB 0 0 0 [])) end then X else Y) = X).
    { intros X Y. destruct (qc_list (as_tq st)); [reflexivity|]. rewrite NN. reflexivity. }
    rewrite NB. clear NB.
    pose proof (sbs_fields _ _ SB') as (Gtq & Gqc & _ & Gca & Gsb & _).
    assert (SB0 : as_space_beg b' = as_space_beg st).
    { rewrite Gsb. cbn. rewrite ensure_cache_inited_eq. cbn. rewrite Fsb. subst st0; reflexivity. }
    rewrite (CA0 (set_pc b' kBatchClass _)) by (cbn; exact SB0).
    replace (compact_to_addr st kBatchClass cp =? 0) with false by (symmetry; apply Z.eqb_neq; clear - BPOS; lia).
    cbn [as_tq set_tq set_pc qc_bytes as_qcache qc_list].
    assert (TQb : as_tq b' = as_tq st) by (rewrite Gtq; cbn; rewrite ensure_cache_inited_eq; cbn; exact TQ0).
    assert (QCb : as_qcache b' = as_qcache st) by (rewrite Gqc; cbn; rewrite ensure_cache_inited_eq; cbn; exact QC0).
    rewrite TQb, QCb.
    replace (as_qcache st <? qc_bytes (as_tq st) + size + kBatchSize) with false by (symmetry; apply Z.ltb_ge; clear - NOD; lia).
    do 2 eexists. split; [reflexivity|].
    (* [comment removed for export] *)
    unfold free_new_state, tq_new. change (ch_chunk_beg (qch ch)) with (ch_chunk_beg ch). fold size.
    rewrite (rfd_pc_c st0 kBatchClass W0 HC ROOM). cbn [pc_count refill_pc].
    pose proof (rfd_same st0 kBatchClass) as (Rsb & _ & _ & _ & _ & Rtq & _ & _ & _ & _ & _ & _ & _ & _ & Rca & _).
    rewrite Rtq, Rca. replace (as_tq st0) with (as_tq st) by (subst st0; reflexivity). rewrite (CA0 st0) by (subst st0; reflexivity).
    change (rf_n kBatchClass) with (max_count kBatchClass / 2).
    apply sbs_set_tq.
    (* [comment removed for export] *)
    clear - SP SB' SG W0 HC.
    unfold same_but_shadow, gset in SB', SG |- *. rewrite ensure_cache_inited_eq in SB'. unfold gfa_state in SG.
    unfold set_pc, upd_chunk, set_chunks, refilled. cbn -[refill_region refill_pc refill_newmaps rf_n rf_fl1 get_region compact_to_addr max_count].
    unfold same_but_shadow in SP. subst st0. unfold set_internal_init, upd_chunk, set_chunks in SP, SB', SG |- *.
    cbn -[refill_region refill_pc refill_newmaps rf_n rf_fl1 get_region compact_to_addr max_count] in SP, SB', SG |- *.
    rewrite upd_nth_upd_nth.
    destruct SP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16).
    destruct SB' as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16).
    destruct SG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    repeat split; congruence.
  Qed.
End FreeModel.
