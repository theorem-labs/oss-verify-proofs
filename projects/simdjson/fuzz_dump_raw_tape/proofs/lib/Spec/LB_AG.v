(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import STree Malloc KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4 MI_WFree2 MI_Cnt MI_WCreate2 MI_WSlot
  LB_Tables LB_Inv LB_Sum LB_Bound LB_WNtf LB_XferF LB_QM LB_Cnt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition cnt_tab_f (sc : Z) : bool :=
  (if sc <? 9 then (small_cnt sc 0 <=? 32) && (1 <=? small_cnt sc 0) else true) && (med_cnt (Z.land sc 3) <=? 32) && (1 <=? med_cnt (Z.land sc 3)).
Lemma cnt_tab_ok sc : 0 <= sc < 48 -> (sc < 9 -> 1 <= small_cnt sc 0 <= 32) /\ 1 <= med_cnt (Z.land sc 3) <= 32.
Proof.
  intros Hsc. assert (H : forallb cnt_tab_f classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H sc Hsc) as T. unfold cnt_tab_f in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2]. apply Z.leb_le in T2. apply Z.leb_le in T3.
  split; [| lia]. intros H9. replace (sc <? 9) with true in T1 by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in T1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Lemma cnt0_of_ge128 sc u : 0 <= sc < 48 -> 128 <= u -> cnt0_of sc u = cmax sc.
Proof.
  intros Hsc Hu. destruct (cnt_tab_ok sc Hsc) as [S0 M0]. unfold cnt0_of, cmax, S_.
  destruct (Z.ltb_spec sc 9) as [L9|G9].
  - unfold small_cnt_pick. replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; specialize (S0 L9); lia). reflexivity.
  - f_equal. cbn [halve_even]. replace (u <? 4 * med_cnt (Z.land sc 3)) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

Lemma bump_big size c : 8 <= c -> bump size c = c.
Proof. intros H. unfold bump. replace (c =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma adj_small sc size c : adj sc size c = c \/ adj sc size c <= 5.
Proof. unfold adj. repeat (destruct (_ && _); [right; lia|]). left. reflexivity. Qed.

Definition nest_host_f (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun cnt0 => let cnt1 := bump size cnt0 in
     (PGSZ / 2 <? size * cnt1 + UNIT)
     || (let j := size_to_class (UNIT + cnt1 * size - IB) in (j =? 15) || (j =? 19) || (j =? 23))) (cnt0_list sc).
Lemma nest_host_all : forallb nest_host_f classes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nest_host sc u : 0 <= sc < 48 ->
  let size := UNIT * size_class sc in let cnt1 := bump size (cnt0_of sc u) in
  size * cnt1 + UNIT <= PGSZ / 2 ->
  let j := size_to_class (UNIT + cnt1 * size - IB) in j = 15 \/ j = 19 \/ j = 23.
Proof.
  intros Hsc. cbn zeta. intros HB. pose proof (forallb_classes _ nest_host_all sc Hsc) as T. unfold nest_host_f in T.
  rewrite forallb_forall in T. specialize (T _ (cnt0_in sc u)). cbn zeta in T.
  apply orb_prop in T as [T|T]; [apply Z.ltb_lt in T; lia|].
  apply orb_prop in T as [T|T]; [apply orb_prop in T as [T|T]|]; apply Z.eqb_eq in T; auto.
Qed.

Definition rank (c : Z) : Z := if c <? 15 then 0 else if c <? 19 then 1 else if c <? 23 then 2 else 3.
Lemma rank_host c j : 0 <= c < j -> (j = 15 \/ j = 19 \/ j = 23) -> rank c + 1 <= rank j <= 3.
Proof. intros Hc Hj. unfold rank. destruct Hj as [->|[->| ->]]; destruct (Z.ltb_spec c 15); destruct (Z.ltb_spec c 19); destruct (Z.ltb_spec c 23); cbn; lia. Qed.
Lemma rank_range c : 0 <= rank c <= 3.
Proof. unfold rank. destruct (c <? 15); [lia|]. destruct (c <? 19); [lia|]. destruct (c <? 23); lia. Qed.

Section AGTQ.
Variables (X X' : extras) (stI st : mstate) (L L' : mled) (BL : list blk) (LS LS' : lhead -> list aptr) (P : Z -> Z).
Variables (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.

Hypothesis INV : INVL X stI L BL LS.
Hypothesis INV' : INVL X' st' L' BL LS'.
Hypothesis LKg : s_groups st = s_groups stI.
Hypothesis LKs : s_slots st = s_slots stI.
Hypothesis LKr : s_regions st = s_regions stI.
Hypothesis LKm : forall x, x <> m -> s_metas st !! x = s_metas stI !! x.
Hypothesis LKc : c_avail_meta_count (s_ctx st) = c_avail_meta_count (s_ctx stI) /\ c_avail_meta_areas (s_ctx st) = c_avail_meta_areas (s_ctx stI)
  /\ c_meta_alloc_shift (s_ctx st) = c_meta_alloc_shift (s_ctx stI).
Hypothesis Hm : s_metas st !! m <> None.
Hypothesis HmI : s_metas stI !! m = Some meta0.
Hypothesis Hp : s_groups stI !! p = None.
Hypothesis SGst : SG stI BL.
Hypothesis Q : QM X stI 0.
Hypothesis XI : forall x, In x (x_idle X) -> x = m \/ In x (x_idle X').
Hypothesis HAQ : AQ stI BL P.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis ROOM : gcnt stI sc <= CAP P sc.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis NEWG : m_sizeclass (MR st' m) = sc /\ m_last_idx (MR st' m) = cnt - 1.
Hypothesis QG_map : m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots stI !! p = None.
Hypothesis QG_nest : m_maplen (MR st' m) = 0 -> exists g i, s_slots stI !! p = Some (g, i) /\ m_sizeclass (MR stI g) <= 23
   /\ (stdg st' m = true -> m_sizeclass (MR stI g) = bighost sc).
Hypothesis QG_std : stdg st' m = true -> (m_maplen (MR st' m) = 0 <-> std_nested sc = true) /\ (m_maplen (MR st' m) <> 0 -> m_maplen (MR st' m) * 4096 = std_len sc).
Hypothesis QG_small : stdg st' m = false -> gcnt stI sc < 128.

Lemma MR_st x : x <> m -> MR st x = MR stI x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite (LKm x NE). reflexivity. Qed.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IM' := proj1 (proj2 (proj2 INV')).
Let IG' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let IS' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

Lemma aq_old x : (exists b, hosts stI b x) -> x <> m /\ MR st' x = MR stI x.
Proof.
  intros [b [aix Hb]]. assert (NE : x <> m).
  { intros ->. pose proof (hosts_mem _ _ _ IM _ _ (ex_intro _ aix Hb)) as MM. rewrite (MR_of_lookup stI m meta0 HmI) in MM. cbn in MM. discriminate. }
  split; [exact NE|]. unfold st'. rewrite agt_MR_other by exact NE. apply MR_st. exact NE.
Qed.

Lemma aq_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups stI).
Proof. unfold st'. rewrite agt_groups, LKg. reflexivity. Qed.

Lemma aq_hosts_old b x : hosts stI b x -> hosts st' b x.
Proof.
  intros [aix Hb]. exists aix. rewrite aq_groups. rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite Hp in Hb. discriminate.
Qed.

Lemma aq_slots_old s v : s_slots stI !! s = Some v -> s_slots st' !! s = Some v.
Proof.
  intros Hs. destruct v as [x i]. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  destruct (aq_old x (ex_intro _ b Hb)) as [NE MRx].
  pose proof (is_total _ _ _ IS' b x i (aq_hosts_old b x Hb) ltac:(rewrite MRx; exact Hi)) as T. rewrite MRx, <- Es in T. exact T.
Qed.

Lemma aq_gmetas : Permutation (gmetas st') ((m, p) :: gmetas stI).
Proof.
  unfold gmetas, groups_l. rewrite aq_groups.
  etransitivity; [apply Permutation_flat_map; apply mtl_insert; exact Hp|]. cbn. apply Permutation_refl.
Qed.

Lemma aq_stdg_old x : (exists b, hosts stI b x) -> stdg st' x = stdg stI x.
Proof. intros Hx. destruct (aq_old x Hx) as [_ E]. unfold stdg, cls. rewrite E. reflexivity. Qed.

Lemma aq_slotcls_old s : s_slots stI !! s <> None -> slotcls st' s = slotcls stI s.
Proof.
  intros Hs. destruct (s_slots stI !! s) as [[x i]|] eqn:E; [| congruence]. unfold slotcls. rewrite (aq_slots_old _ _ E), E.
  destruct (is_valid _ _ _ IS _ _ _ E) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. unfold cls. rewrite MRx. reflexivity.
Qed.

Lemma gmetas_hosts x b : In (x, b) (gmetas stI) -> exists b', hosts stI b' x.
Proof. intros H. apply gmetas_in in H as [aix Hb]. exists b, aix. exact Hb. Qed.

Lemma aq_sum (F F' : aptr * aptr -> Z) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zsum (map F' (gmetas st')) = F' (m, p) + zsum (map F (gmetas stI)).
Proof.
  intros HF. rewrite (zsum_map_perm _ _ _ aq_gmetas). cbn [map]. rewrite zsum_cons. f_equal. apply zsum_map_ext. intros [x b] Hin. apply HF. exact Hin.
Qed.
Lemma aq_count (F F' : aptr * aptr -> bool) :
  (forall x b, In (x, b) (gmetas stI) -> F' (x, b) = F (x, b)) ->
  zcount F' (gmetas st') = (if F' (m, p) then 1 else 0) + zcount F (gmetas stI).
Proof. intros HF. rewrite !zcount_eq_zsum. apply (aq_sum (fun x => if F x then 1 else 0)). intros x b Hin. rewrite (HF x b Hin). reflexivity. Qed.

Lemma aq_gcnt c : gcnt st' c = (if sc =? c then cnt else 0) + gcnt stI c.
Proof.
  rewrite !gcnt_gmetas. rewrite (aq_sum (fun mb => if m_sizeclass (MR stI (fst mb)) =? c then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cnt_of. rewrite E1, E2. destruct (sc =? c); lia.
  - intros x b Hin. cbn [fst]. destruct (aq_old x (gmetas_hosts x b Hin)) as [_ E]. rewrite E. reflexivity.
Qed.

Lemma aq_nsc c : nsc st' c = (if (sc =? c) && negb (stdg st' m) then cnt else 0) + nsc stI c.
Proof.
  unfold nsc. rewrite (aq_sum (fun mb => if (cls stI (fst mb) =? c) && negb (stdg stI (fst mb)) then cnt_of (MR stI (fst mb)) else 0)).
  - cbn [fst]. destruct NEWG as [E1 E2]. unfold cls, cnt_of. rewrite E1, E2. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
  - intros x b Hin. cbn [fst]. pose proof (gmetas_hosts x b Hin) as Hx. rewrite (aq_stdg_old x Hx). destruct (aq_old x Hx) as [_ E]. unfold cls. rewrite E. reflexivity.
Qed.

Lemma aq_ncarved : ncarved st' = ncarved stI.
Proof.
  transitivity (ncarved st).
  - destruct (s_metas st !! m) as [r|] eqn:E; [| congruence]. unfold ncarved, st'. rewrite agt_metas. unfold zlen.
    rewrite (Permutation_length (mtl_insert_old (s_metas st) m _ r E)), (Permutation_length (mtl_delete (s_metas st) m r E)). reflexivity.
  - apply ncarved_dom. intros x. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite HmI; split; [congruence| intros _; exact Hm]|]. rewrite (LKm x NE). tauto.
Qed.

Lemma aq_LS c : LB_Inv.LS st' BL c = LB_Inv.LS stI BL c.
Proof.
  unfold LB_Inv.LS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.
Lemma aq_MIS c : MIS st' BL c = MIS stI BL c.
Proof.
  unfold MIS. apply zcount_ext. intros k Hk. destruct (is_blocks _ _ _ IS k Hk) as (x & i & Hs & _). rewrite (aq_slotcls_old (bslot k)); [reflexivity| rewrite Hs; discriminate].
Qed.

Theorem agt_quant : SG st' BL /\ QM X' st' 0 /\ AQ st' BL P.
Proof.
  destruct NEWG as [E1 E2].
  assert (GRP' : forall b x aix, s_groups st' !! b = Some (mkGhdr (Some x) aix) -> (x = m /\ b = p) \/ (x <> m /\ s_groups stI !! b = Some (mkGhdr (Some x) aix) /\ MR st' x = MR stI x)).
  { intros b x aix Hb. rewrite aq_groups in Hb. destruct (aptr_eq_dec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. inversion Hb. left. auto.
    - rewrite lookup_insert_ne in Hb by congruence. right. destruct (aq_old x (ex_intro _ b (ex_intro _ aix Hb))) as [NEx MRx]. auto. }
  split; [| split].
  -   destruct SGst as [S1 S2 S3 S4 S5 S6 S7]. constructor.
    + intros k Hk. destruct (S1 k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact (aq_slots_old _ _ Hs)|].
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _). destruct (aq_old x (ex_intro _ b Hb)) as [_ MRx]. rewrite MRx. auto.
    + intros c. rewrite aq_MIS. apply S2.
    + intros b x aix Hb Hc Hml. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1, E2 in *. unfold cnt_of. rewrite E2. replace (cnt - 1 + 1) with cnt by lia. exact (proj1 (QG_map Hml)).
      * rewrite MRx in *. exact (S3 _ _ _ Hb0 Hc Hml).
    + intros b x aix Hb SD. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * rewrite E1. destruct (QG_std SD) as [Q1 Q3]. split; [exact Q1|]. split; [| exact Q3].
        intros Z0. destruct (QG_nest Z0) as (g & i & Hs & _ & BH). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (BH SD).
      * rewrite (aq_stdg_old x (ex_intro _ b (ex_intro _ aix Hb0))) in SD. rewrite MRx. destruct (S4 _ _ _ Hb0 SD) as (Q1 & Q2 & Q3).
        split; [exact Q1|]. split; [| exact Q3]. intros Z0. destruct (Q2 Z0) as (g & i & Hs & Eg). exists g, i. split; [exact (aq_slots_old _ _ Hs)|].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact Eg.
    + intros c Hc. rewrite aq_nsc. specialize (S5 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; cbn [andb]; [| lia].
      destruct (stdg st' m) eqn:SD; cbn [negb]; [lia|]. pose proof (QG_small eq_refl). pose proof (nsc_le_gcnt X stI L BL LS INV sc). lia.
    + intros b x aix Hb H63. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)]; [rewrite E1 in H63; lia|]. rewrite MRx in *. exact (S6 _ _ _ Hb0 H63).
    + intros b x aix g i Hb Z0 Hs'. destruct (GRP' _ _ _ Hb) as [[-> ->]|(NE & Hb0 & MRx)].
      * destruct (QG_nest Z0) as (g0 & i0 & Hs & C23 & _). rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g) by congruence. subst g0.
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact C23.
      * rewrite MRx in Z0. destruct (g_nest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb0) Z0) as (g0 & i0 & Hs & _).
        rewrite (aq_slots_old _ _ Hs) in Hs'. assert (g0 = g /\ i0 = i) as [-> ->] by (split; congruence).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bg Hbg] & _). destruct (aq_old g (ex_intro _ bg Hbg)) as [_ MRg]. rewrite MRg. exact (S7 _ _ _ _ _ Hb0 Z0 Hs).
  -   destruct LKc as (C1 & C2 & C3).
    assert (RG' : s_regions st' = s_regions stI) by (unfold st'; rewrite agt_regions; exact LKr).
    assert (AP' : apages st' = apages stI) by (apply apages_ext; [exact RG'| unfold st'; rewrite agt_ctx; cbn; exact C2]).
    assert (CK' : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C1).
    assert (SH' : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx stI)) by (unfold st'; rewrite agt_ctx; cbn; exact C3).
    destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?RG', ?aq_ncarved, ?AP', ?CK', ?SH'; auto.
    intros x mr Hx Z0. unfold st' in Hx. rewrite agt_metas in Hx. destruct (aptr_eq_dec x m) as [->|NE].
    + rewrite lookup_insert_eq in Hx. inversion Hx. subst mr. exfalso. revert Z0.
      unfold agG, m_set_sizeclass, m_set_freeable, m_set_last_idx, m_set_mem, m_set_freed, m_set_avail. cbn. discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. rewrite (LKm x NE) in Hx.
      destruct (Q1 x mr Hx Z0) as [N0|I0]; [left; exact N0|]. destruct (XI x I0) as [->|I1]; [congruence| right; exact I1].
  -   destruct HAQ as [A1 A2 A3 A4 A5]. constructor; auto.
    + intros c Hc. rewrite aq_gcnt. specialize (A2 c Hc). destruct (Z.eqb_spec sc c) as [<-|NE]; lia.
    + rewrite aq_ncarved. exact A4.
Qed.
End AGTQ.
