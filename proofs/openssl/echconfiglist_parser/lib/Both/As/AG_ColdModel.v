(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AllocRep AllocRepFacts AW_Efs AW_Populate AG_WFHit AG_MallocModel AS_Refill1 AG_RefillModel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma upd_nth_upd_nth {A} : forall (l : list A) i x y, upd_nth (upd_nth l i x) i y = upd_nth l i y.
Proof. induction l as [|a l IH]; intros [|i] x y; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma firstn_length_ge {A} : forall k (l : list A), (k <= length l)%nat -> length (firstn k l) = k.
Proof. intros k l H. rewrite length_firstn. lia. Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma in_mem_high : forall a, kHighMemBeg <= a <= kHighMemEnd -> addr_is_in_mem a = true.
Proof. intros a H. unfold addr_is_in_mem. apply Bool.orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia. Qed.

Lemma upd_nth_znth {A} : forall (l : list A) i d, (i < length l)%nat -> upd_nth l i (znth l i d) = l.
Proof. induction l as [|a l IH]; intros [|i] d H; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sbs_set_pc : forall a b c p, same_but_shadow a b -> same_but_shadow (set_pc a c p) (set_pc b c p).
Proof. intros a b c p S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_upd_chunk : forall a b ch, same_but_shadow a b -> same_but_shadow (upd_chunk a ch) (upd_chunk b ch).
Proof. intros a b ch S. unfold same_but_shadow, upd_chunk in *. cbn. intuition congruence. Qed.
Lemma sbs_set_region : forall a b c r, same_but_shadow a b -> same_but_shadow (set_region a c r) (set_region b c r).
Proof. intros a b c r S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_add_map : forall a b mp, same_but_shadow a b -> same_but_shadow (add_map a mp) (add_map b mp).
Proof. intros a b mp S. unfold same_but_shadow in *. cbn. intuition congruence. Qed.
Lemma sbs_get_region : forall a b c, same_but_shadow a b -> get_region a c = get_region b c.
Proof. intros a b c S. unfold get_region. destruct S as (_ & _ & E & _). rewrite E. reflexivity. Qed.
Lemma sbs_region_beg : forall a b c, same_but_shadow a b -> region_beg a c = region_beg b c.
Proof. intros a b c S. unfold region_beg. destruct S as (E & _). rewrite E. reflexivity. Qed.
Lemma sbs_free_array_base : forall a b c, same_but_shadow a b -> free_array_base a c = free_array_base b c.
Proof. intros a b c S. unfold free_array_base. rewrite (sbs_region_beg a b c S). reflexivity. Qed.
Lemma sbs_compact_to_addr : forall a b c cp, same_but_shadow a b -> compact_to_addr a c cp = compact_to_addr b c cp.
Proof. intros a b c cp S. unfold compact_to_addr. rewrite (sbs_region_beg a b c S). reflexivity. Qed.
Lemma sbs_sym : forall a b, same_but_shadow a b -> same_but_shadow b a.
Proof. intros a b S. unfold same_but_shadow in *. intuition congruence. Qed.

Section ColdModel.
  Variables (st : astate) (c : Z).
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.

  Hypothesis W : WF st.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  (* [comment removed for export] *)
  Hypothesis HM : kHighMemBeg <= as_space_beg st /\ as_space_beg st + kSpaceSize <= kHighMemEnd + 1 /\ as_space_beg st mod 4096 = 0.

  (* [comment removed for export] *)
  Definition gfa_state : astate :=
    mkState (as_space_beg st) (as_ptr_array st) (upd_nth (as_regions st) (zidx c) (refill_region st c)) true
            (as_cache st) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
            (as_internal_init st) (refill_newmaps st c ++ as_maps st) (as_shadow st) (as_env st) (as_track_shadow st)
            (as_qmax st) (as_qmin st) (as_qcache st).

  Let RO : region_ok st c. Proof. apply WF_region; [exact W| unfold kNumClasses; lia]. Qed.
  Let T : 32 <= csz <= 65536 /\ csz mod 32 = 0 /\ 2 <= max_count c <= 16 /\ max_count c mod 2 = 0.
  Proof. pose proof (class_size_table_facts c ltac:(lia)) as (T1 & T2 & T3 & T4 & T5 & T6). subst csz. repeat split; try lia. Qed.
  Let NR : 1 <= n <= 8 /\ n + n = max_count c.
  Proof. subst n. unfold rf_n. lia. Qed.
  Let LENR : length (as_regions st) = 32%nat.
  Proof. destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L & _). exact L. Qed.
  Let FLL : zlen fl = nf. Proof. symmetry. exact (ro_numfreed _ _ RO). Qed.
  Let AUR : 0 <= au <= mu /\ mu mod kUserMapSize = 0 /\ au mod csz = 0 /\ mu - au < csz + (if au =? 0 then kUserMapSize else 0).
  Proof.
    pose proof (ro_alloc_nonneg _ _ RO). pose proof (ro_alloc_le _ _ RO). pose proof (ro_mapped_mod _ _ RO). pose proof (ro_alloc_mod _ _ RO ltac:(destruct T; lia)).
    pose proof (ro_tail_small _ _ RO ltac:(destruct T; lia)) as TS. fold r au mu csz in TS |- *.
    repeat split; try assumption; try lia.
  Qed.
  Let NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize /\ mfa mod kFreeArrayMapSize = 0.
  Proof.
    pose proof (ro_fa_le _ _ RO). pose proof (ro_fa_mod _ _ RO). pose proof (ro_fa_bound _ _ RO). fold r nf mfa in H, H0, H1 |- *.
    assert (0 <= nf) by (rewrite <- FLL; unfold zlen; lia). lia.
  Qed.

  Lemma get_region_set_region : forall x rg, length (as_regions x) = 32%nat -> get_region (set_region x c rg) c = rg.
  Proof. intros x rg L. unfold get_region, set_region. cbn [as_regions]. apply znth_upd_nth_eq. rewrite L. unfold zidx. lia. Qed.

  (* [comment removed for export] *)
  Lemma gfa_cold : exists stg ev,
    get_from_allocator (ensure_cache_inited st) c n = Some (stg, firstn (Z.to_nat n) fl1, ev) /\ same_but_shadow stg gfa_state.
  Proof.
    pose proof (rf_facts st c W HC ROOM) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold r in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    fold nf mfa au mu fl n csz in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    fold mu' nnew nf1 mfa' au' fl1 in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15.
    (* [comment removed for export] *)
    set (st0 := ensure_cache_inited st).
    assert (S0 : st0 = mkState (as_space_beg st) (as_ptr_array st) (as_regions st) true (as_cache st) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
                              (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st)).
    { subst st0. unfold ensure_cache_inited. destruct st; cbn. destruct as_cache_inited; reflexivity. }
    assert (GR0 : get_region st0 c = r) by (rewrite S0; reflexivity).
    assert (RB0 : region_beg st0 c = region_beg st c) by (rewrite S0; reflexivity).
    assert (FB0 : free_array_base st0 c = free_array_base st c) by (rewrite S0; reflexivity).
    assert (L0 : length (as_regions st0) = 32%nat) by (rewrite S0; exact LENR).
    unfold get_from_allocator. rewrite GR0. fold nf.
    destruct (Z.lt_ge_cases nf n) as [NF|NF].
    2:{ (* [comment removed for export] *)
        rewrite (proj2 (Z.ltb_ge nf n) NF). destruct (Q15 NF) as (E1 & E2 & E3).
        assert (EFL : fl1 = fl) by (subst fl1; unfold rf_fl1; fold n; fold nnew; rewrite E2; reflexivity).
        rewrite !GR0. fold nf mfa au mu fl. rewrite <- EFL.
        do 2 eexists. split; [reflexivity|].
        unfold gfa_state, refill_region, refill_newmaps. fold r. fold nf mfa au mu fl. fold n mu' nnew nf1 mfa' au' fl1.
        rewrite E1, E3, Q5, Q4, E2, EFL, !Z.ltb_irrefl. cbn [app]. rewrite Z.mul_0_l, !Z.add_0_r. rewrite S0. apply sbs_refl. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_lt nf n) NF). destruct (Q14 NF) as [TOTLE ENN].
    pose proof (rf_batch_small c HC) as [BSM _]. fold n csz in BSM.
    pose proof AUR as (A1 & A2 & A3 & A4). pose proof NFR as (F1 & F2 & F3 & F4). pose proof T as (T1 & _). pose proof HM as (M1 & M2 & M3).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kHighMemBeg, kHighMemEnd, kSpaceSize in *.
    assert (ERB : region_beg st c = as_space_beg st + c * 4294967296) by (rewrite region_beg_eq; reflexivity).
    assert (EFA : free_array_base st c = region_beg st c + 3758096384) by (rewrite free_array_base_eq; reflexivity).
    assert (TOTB : au + csz <= rf_total c nf au <= au + 65536) by (unfold rf_total, rf_k; fold n csz; clear - BSM NF NR T1 F1; nia).
    assert (ETOT : au + (n - nf) * csz = rf_total c nf au) by (unfold rf_total, rf_k; fold n csz; clear; lia).
    unfold populate_free_array. rewrite GR0. fold au mu nf fl mfa csz. rewrite ETOT.
    (* [comment removed for export] *)
    assert (PSu : forall stA, exists stB evB, poison_shadow stA (region_beg st c + mu) 262144 kAsanHeapLeftRedzoneMagic = Some (stB, evB) /\ same_but_shadow stB stA).
    { intros stA. apply poison_shadow_some.
      - rewrite land7_mod8, ERB. clear - M3 A2. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite ERB. clear - M1 M2 A1 ROOM HC; lia.
      - reflexivity.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite ERB. clear - M1 M2 A1 ROOM HC; lia. }
    assert (PSf : forall stA, mfa < mfa' -> exists stB evB, poison_shadow stA (free_array_base st c + mfa) (mfa' - mfa) kAsanHeapLeftRedzoneMagic = Some (stB, evB) /\ same_but_shadow stB stA).
    { intros stA LT. apply poison_shadow_some.
      - rewrite land7_mod8, EFA, ERB. clear - M3 F4. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite EFA, ERB. clear - M1 M2 F1 F2 F3 HC; lia.
      - rewrite land7_mod8. clear - F4 Q13. Z.div_mod_to_equations. lia.
      - apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. rewrite EFA, ERB. clear - M1 M2 F1 F2 F3 HC LT Q12 F4 Q13; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    set (R1 := mkRegion mu' au nf fl mfa).
    set (stU := if mu <? mu' then add_map st0 (mkMap (region_beg st c + mu) (mu' - mu) (MkUserMap c) PROT_RW false) else st0).
    assert (LU : length (as_regions stU) = 32%nat) by (subst stU; destruct (mu <? mu'); [cbn [as_regions add_map]; exact L0| exact L0]).
    assert (STEP1 : exists st1 ev1,
      (if rf_total c nf au <=? mu then Some (st0, r, [])
       else if kFreeArrayOffset <? mu + 0 + round_up (rf_total c nf au - mu) kUserMapSize then None
       else let (st1, ev1) := map_fixed st0 (region_beg st0 c + mu) (round_up (rf_total c nf au - mu) kUserMapSize) (MkUserMap c) in
            match poison_shadow st1 (region_beg st0 c + mu) (round_up (rf_total c nf au - mu) kUserMapSize) kAsanHeapLeftRedzoneMagic with
            | Some (st2, ev2) => Some (set_region st2 c (mkRegion (mu + round_up (rf_total c nf au - mu) kUserMapSize) au nf fl mfa),
                                       mkRegion (mu + round_up (rf_total c nf au - mu) kUserMapSize) au nf fl mfa, ev1 ++ ev2)
            | None => None end)
      = Some (st1, R1, ev1) /\ same_but_shadow st1 (set_region stU c R1)).
    { destruct (Z.leb_spec (rf_total c nf au) mu) as [TOT|TOT].
      - assert (E1 : mu' = mu) by (subst mu'; unfold rf_mu'; fold n; rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_ge _ _) TOT); reflexivity).
        assert (RREC : r = R1) by (subst R1; rewrite E1; subst mu au nf fl mfa; destruct r; reflexivity).
        do 2 eexists. split; [rewrite <- RREC; reflexivity|].
        subst stU. rewrite E1, Z.ltb_irrefl. rewrite <- RREC. rewrite S0. unfold same_but_shadow, set_region. cbn.
        repeat split; try reflexivity. unfold r, get_region. symmetry. apply upd_nth_znth. rewrite LENR. unfold zidx. clear - HC. lia.
      - assert (MS : round_up (rf_total c nf au - mu) kUserMapSize = 262144) by (unfold round_up, kUserMapSize; clear - TOT TOTB A1; Z.div_mod_to_equations; lia).
        assert (E1 : mu' = mu + 262144).
        { subst mu'. unfold rf_mu'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF), (proj2 (Z.ltb_lt _ _) TOT). unfold pop_ms. fold csz. rewrite MS. reflexivity. }
        rewrite MS. unfold kFreeArrayOffset. replace (3758096384 <? mu + 0 + 262144) with false by (symmetry; apply Z.ltb_ge; clear - ROOM; lia).
        unfold map_fixed. cbv iota beta. rewrite RB0.
        destruct (PSu (add_map st0 (mkMap (region_beg st c + mu) 262144 (MkUserMap c) PROT_RW false))) as (stB & evB & EP & SB). rewrite EP.
        replace (mu + 262144) with mu' by exact E1. do 2 eexists. split; [reflexivity|].
        apply sbs_set_region. subst stU. rewrite (proj2 (Z.ltb_lt mu mu')) by (clear - E1; lia). replace (mu' - mu) with 262144 by (clear - E1; lia). exact SB. }
    destruct STEP1 as (st1 & ev1 & ES1 & S1). rewrite ES1. clear ES1.
    assert (L1 : length (as_regions st1) = 32%nat) by (destruct S1 as (_ & _ & E & _); rewrite E; cbn [as_regions set_region]; rewrite length_upd_nth; exact LU).
    assert (GR1 : get_region st1 c = R1) by (rewrite (sbs_get_region _ _ c S1); apply get_region_set_region; exact LU).
    assert (FB1 : free_array_base st1 c = free_array_base st c).
    { rewrite (sbs_free_array_base _ _ c S1). subst stU. rewrite <- FB0. destruct (mu <? mu'); reflexivity. }
    subst R1. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    rewrite <- ENN, <- Q4.
    (* [comment removed for export] *)
    set (R2 := mkRegion mu' au nf fl mfa').
    set (mpF := mkMap (free_array_base st c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false).
    set (stF := if mfa <? mfa' then add_map stU mpF else stU).
    assert (LF : length (as_regions stF) = 32%nat) by (subst stF; destruct (mfa <? mfa'); [cbn [as_regions add_map]; exact LU| exact LU]).
    assert (SRSR : forall x A B, set_region (set_region x c A) c B = set_region x c B) by (intros x A B; unfold set_region; cbn; rewrite upd_nth_upd_nth; reflexivity).
    assert (EMFA : mfa' = (if 4 * nf1 <=? mfa then mfa else round_up (4 * nf1) 262144)).
    { subst mfa'. unfold rf_mfa'. fold n. rewrite (proj2 (Z.ltb_lt nf n) NF). fold nf1. unfold efs_new, kFreeArrayMapSize. reflexivity. }
    assert (STEP2 : exists st2 ev2, ensure_free_array_space st1 c nf1 = Some (st2, ev2) /\ same_but_shadow st2 (set_region stF c R2)).
    { unfold ensure_free_array_space. rewrite GR1. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
      rewrite (Z.mul_comm nf1 4).
      destruct (Z.leb_spec (4 * nf1) mfa) as [FAST|SLOW].
      - do 2 eexists. split; [reflexivity|]. subst stF R2. rewrite EMFA, Z.ltb_irrefl. exact S1.
      - assert (LT : mfa < mfa') by (rewrite EMFA; unfold round_up; clear - SLOW; Z.div_mod_to_equations; lia).
        unfold kFreeArrayMapSize, kFreeArraySize in *. rewrite <- EMFA. replace (_ <? mfa') with false by (symmetry; apply Z.ltb_ge; clear - Q12; lia).
        unfold map_fixed. cbv iota beta. rewrite FB1. fold mpF.
        destruct (PSf (add_map st1 mpF) LT) as (stB & evB & EP & SB). rewrite EP.
        do 2 eexists. split; [reflexivity|]. subst R2.
        assert (SB' : same_but_shadow stB (set_region stF c (mkRegion mu' au nf fl mfa))).
        { eapply sbs_trans; [exact SB|]. subst stF. rewrite (proj2 (Z.ltb_lt _ _) LT).
          change (set_region (add_map stU mpF) c (mkRegion mu' au nf fl mfa)) with (add_map (set_region stU c (mkRegion mu' au nf fl mfa)) mpF). apply sbs_add_map. exact S1. }
        rewrite <- (SRSR stF (mkRegion mu' au nf fl mfa)). apply sbs_set_region. exact SB'. }
    destruct STEP2 as (st2 & ev2 & ES2 & S2). rewrite ES2. clear ES2.
    assert (L2 : length (as_regions st2) = 32%nat) by (destruct S2 as (_ & _ & E & _); rewrite E; cbn [as_regions set_region]; rewrite length_upd_nth; exact LF).
    assert (GR2 : get_region st2 c = R2) by (rewrite (sbs_get_region _ _ c S2); apply get_region_set_region; exact LF).
    rewrite GR2. subst R2. cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    replace (mu' <? au + nnew * csz) with false by (symmetry; apply Z.ltb_ge; clear - Q5 Q6; lia).
    rewrite (get_region_set_region st2 _ L2). cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    replace (nf1 <? n) with false by (symmetry; apply Z.ltb_ge; clear - Q1; lia). cbn iota.
    rewrite (get_region_set_region st2 _ L2). cbn [rg_num_freed rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array].
    assert (EFL1 : carve_asc au csz 0 (Z.to_nat nnew) ++ fl = fl1) by (subst fl1; unfold rf_fl1; fold n csz; fold nnew; reflexivity).
    rewrite EFL1, <- Q5, SRSR.
    do 2 eexists. split; [reflexivity|].
    (* [comment removed for export] *)
    eapply sbs_trans; [apply sbs_set_region; exact S2|]. rewrite SRSR.
    unfold gfa_state, refill_region, refill_newmaps. fold r. fold nf mfa au mu fl. fold n csz. fold mu' nnew nf1 mfa' au' fl1. fold mpF.
    subst stF stU. rewrite S0. destruct (mfa <? mfa'); destruct (mu <? mu'); apply sbs_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma am_malloc_cold : forall sz kaddr cp rest,
    0 <= sz ->
    let rq := compute_req sz in
    let needed := rq_needed rq in
    let U := compact_to_addr st c cp + rq_rz rq in
    size_too_big rq = false -> needed <= kMaxSize ->
    c = class_id needed ->
    firstn (Z.to_nat n) fl1 = cp :: rest ->
    Z.land U 7 = 0 -> addr_is_in_mem U = true -> addr_is_in_mem (U + Z.land (rq_size rq) (Z.lnot 7) - 8) = true ->
    addr_is_in_mem (U + Z.land (rq_size rq) (Z.lnot 7)) = true ->
    (rq_rz rq = 16 \/ 32 <= rq_rz rq) -> rq_primary rq = true -> rq_rz rq + rq_size rq <= needed ->
    exists st' ev, am_malloc_k st sz kaddr = Some (U, st', ev)
      /\ same_but_shadow st' (hit_state (refilled st c) c n rest (mkChunk (compact_to_addr st c cp) U (rq_size rq) (rq_rz rq) c CAllocated)).
  Proof.
    intros sz kaddr cp rest Hn rq needed U TB NK Hc TAKEN AL8 IM1 IM2 IM3 RZ16 PRIM FIT.
    destruct gfa_cold as (stg & evg & EG & SG).
    unfold am_malloc_k. replace (sz <? 0) with false by (symmetry; apply Z.ltb_ge; lia). fold rq. rewrite TB.
    fold needed. replace (kMaxSize <? needed) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite <- Hc. unfold cache_alloc.
    replace ((c =? 0) || (kNumClasses <=? c)) with false by (symmetry; apply orb_false_intro; [apply Z.eqb_neq; lia| apply Z.leb_gt; unfold kNumClasses; lia]).
    rewrite EMPTY. cbn [Z.eqb]. change (max_count c / 2) with n. rewrite EG. cbn [pc_chunks pc_count]. rewrite TAKEN.
    assert (CA : compact_to_addr (set_pc stg c (mkPC (n - 1) rest)) c cp = compact_to_addr st c cp).
    { etransitivity; [| exact (sbs_compact_to_addr _ _ c cp SG)]. reflexivity. }
    rewrite CA. fold U.
    replace (compact_to_addr st c cp + needed <? U + rq_size rq) with false by (symmetry; apply Z.ltb_ge; subst U; lia).
    rewrite PRIM. cbn [negb].
    set (st2 := upd_chunk _ _).
    set (rd := Z.land (rq_size rq) (Z.lnot 7)).
    assert (RD8 : Z.land rd 7 = 0) by (subst rd; rewrite <- Z.land_assoc, (Z.land_comm (Z.lnot 7) 7), Z.land_lnot_diag, Z.land_0_r; reflexivity).
    assert (S14 : exists st4 ev4, (if 0 <? rd then poison_shadow st2 U rd 0 else Some (st2, [])) = Some (st4, ev4) /\ same_but_shadow st4 st2).
    { destruct (0 <? rd). 2:{ do 2 eexists. split; [reflexivity| apply sbs_refl]. }
      destruct (poison_shadow_some st2 U rd 0 AL8 IM1 RD8 IM2) as (st4 & ev4 & E & S). exists st4, ev4. split; [exact E| exact S]. }
    destruct S14 as (st4 & ev4 & E14 & S4). rewrite E14.
    fold rd in IM3. rewrite IM3. cbn [negb].
    assert (S15 : exists st5 ev5, (if negb (rq_size rq =? rd) then Some (paint st4 (U + rd) (U + rd + 8) (Z.land (rq_size rq) 7), [EShadow1 (U + rd) (Z.land (rq_size rq) 7)]) else Some (st4, []))
                                 = Some (st5, ev5) /\ same_but_shadow st5 st4).
    { destruct (negb (rq_size rq =? rd)); do 2 eexists; (split; [reflexivity|]); [apply sbs_paint| apply sbs_refl]. }
    destruct S15 as (st5 & ev5 & E15 & S5). rewrite E15.
    replace (negb (U - kChunkHeaderSize =? compact_to_addr st c cp) && (U - kChunkHeaderSize <? compact_to_addr st c cp + 16)) with false.
    2:{ symmetry. unfold kChunkHeaderSize. subst U. destruct RZ16 as [E|GE].
        - rewrite E. replace (compact_to_addr st c cp + 16 - 16 =? compact_to_addr st c cp) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
        - rewrite andb_false_iff. right. apply Z.ltb_ge. lia. }
    do 2 eexists. split; [reflexivity|].
    eapply sbs_trans; [exact S5|]. eapply sbs_trans; [exact S4|]. subst st2. unfold hit_state. apply sbs_upd_chunk.
    eapply sbs_trans; [apply sbs_set_pc; exact SG|].
    unfold gfa_state, refilled, set_pc. cbn. rewrite upd_nth_upd_nth. apply sbs_refl.
  Qed.
End ColdModel.

End HCW.

