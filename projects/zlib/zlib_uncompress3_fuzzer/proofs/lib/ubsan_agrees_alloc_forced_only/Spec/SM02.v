(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require Lia.
From Stdlib Require Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require KInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Inv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_List.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Ext.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Pres3.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_Pres4.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_WFree2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MI_Bits.
From Stdlib Require Import ZArith. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM01. Import SM01.MI_Arith.
Unset Lia Cache.
Local Open Scope Z_scope.

Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma lowbit_testbit : forall v k, 0 <= k -> lowbit v = 2 ^ k -> Z.testbit v k = true.
Proof.
  intros v k Hk E. unfold lowbit in E.
  assert (T : Z.testbit (Z.land v (- v)) k = true) by (rewrite E; apply Z.pow2_bits_true; lia).
  rewrite Z.land_spec in T. apply andb_prop in T. tauto.
Qed.

Lemma sub_bit_ldiff f i : 0 <= f -> 0 <= i -> Z.testbit f i = true -> f - 2 ^ i = Z.ldiff f (2 ^ i).
Proof.
  intros Hf Hi Hb.
  assert (E : f = Z.lor (Z.ldiff f (2 ^ i)) (2 ^ i)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec i n) as [<-|NE]; [rewrite Hb; reflexivity|]. cbn. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. }
  assert (D : Z.land (Z.ldiff f (2 ^ i)) (2 ^ i) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.pow2_bits_eqb, Z.bits_0 by lia.
    destruct (Z.eqb_spec i n); cbn; [rewrite Bool.andb_false_r| rewrite Bool.andb_false_r]; reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as A. rewrite (Z.lxor_lor _ _ D) in A. rewrite <- E in A. lia.
Qed.

Lemma testbit_sub_bit f i j : 0 <= f -> 0 <= i -> 0 <= j -> Z.testbit f i = true ->
  Z.testbit (f - 2 ^ i) j = Z.testbit f j && negb (i =? j).
Proof.
  intros Hf Hi Hj Hb. rewrite (sub_bit_ldiff f i Hf Hi Hb), Z.ldiff_spec, Z.pow2_bits_eqb by lia. reflexivity.
Qed.

Lemma lowbit_idiom m : 0 < m ->
  exists k, 0 <= k /\ lowbit m = 2 ^ k /\ ctz32 (lowbit m) = k /\ Z.testbit m k = true
    /\ 0 <= m - lowbit m /\ (forall j, 0 <= j -> Z.testbit (m - lowbit m) j = Z.testbit m j && negb (k =? j)).
Proof.
  intros Hm. destruct (lowbit_nonzero m Hm) as (k & Hk & E & L). exists k.
  pose proof (lowbit_testbit m k Hk E) as Tb.
  split; [exact Hk|]. split; [exact E|]. split; [rewrite E; apply ctz32_pow2; exact Hk|]. split; [exact Tb|].
  rewrite E. split; [lia|]. intros j Hj. apply testbit_sub_bit; auto; lia.
Qed.

Lemma mask_below m n : 0 <= m -> 0 <= n -> (forall i, 0 <= i -> Z.testbit m i = true -> i <= n) -> m < 2 ^ (n + 1).
Proof. intros Hm Hn H. apply bits_below_bound; [lia| lia|]. intros i Hi Hb. pose proof (H i Hi Hb). lia. Qed.
End MI_Bits.

Module MI_Ledger.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_List. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Ext. Import SM01.MI_Ext2. Import SM01.MI_Shadow. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Pres4. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_WFree2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma In_map_to_list_regions st rid r : In (rid, r) (map_to_list (s_regions st)) <-> s_regions st !! rid = Some r.
Proof.
  split.
  - intros H. apply elem_of_map_to_list. apply list_elem_of_In. exact H.
  - intros H. apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact H.
Qed.

Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.

Lemma lranges_iff x : In x (lranges L) <-> In x (live_ranges st).
Proof.
  unfold lranges, live_ranges. rewrite (proj1 (ir_resv _ _ _ IR)). rewrite !in_app_iff. split.
  - intros [H|[H|[H|H]]]; [left; exact H| right| right| right].
    + apply in_map_iff in H as ([b l] & <- & Hg). cbn.
      pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hg) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
      cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
    + apply in_map_iff in H as ([[b l] kk] & <- & Hm). cbn.
      pose proof (Permutation_in _ (ir_metas _ _ _ IR) Hm) as Hin. apply in_map_iff in Hin as ([rid r] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk]. cbn in Hk. apply in_map_iff. exists (rid, r). split; [| exact Hf].
      cbn. unfold region_live_range. destruct (r_kind r); try discriminate; reflexivity.
    + destruct (ld_brkreg L) as [[b l]|] eqn:EB; [| destruct H]. destruct H as [<-|[]].
      destruct (proj1 (ir_brkreg _ _ _ IR b l) EB) as (rid & r & Hr & Hk & <- & <-).
      apply in_map_iff. exists (rid, r). split; [| apply In_map_to_list_regions; exact Hr].
      cbn. unfold region_live_range. rewrite Hk. reflexivity.
  - intros [H|H]; [left; exact H| right].
    apply in_map_iff in H as ([rid r] & <- & Hin). cbn. apply In_map_to_list_regions in Hin.
    unfold region_live_range. destruct (r_kind r) eqn:Hk.
    + right. right. rewrite (proj2 (ir_brkreg _ _ _ IR (r_base r) (r_len r))); [left; reflexivity| exists rid, r; auto].
    + right. left.
      assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1)) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_metas _ _ _ IR)) Hm) as Hm'.
      apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
    + left.
      assert (Hf : In (rid, r) (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR)) Hm) as Hm'.
      apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
Qed.

Lemma forallb_ext {A} (f : A -> bool) l1 l2 : (forall x, In x l1 <-> In x l2) -> forallb f l1 = forallb f l2.
Proof.
  intros H. destruct (forallb f l1) eqn:E1; destruct (forallb f l2) eqn:E2; try reflexivity.
  - rewrite forallb_forall in E1. assert (E2' : forallb f l2 = true) by (apply forallb_forall; intros x Hx; apply E1; apply H; exact Hx). congruence.
  - rewrite forallb_forall in E2. assert (E1' : forallb f l1 = true) by (apply forallb_forall; intros x Hx; apply E2; apply H; exact Hx). congruence.
Qed.

Lemma ranges_free_eq a n : ranges_free (lranges L) a n = ranges_free (live_ranges st) a n.
Proof. unfold ranges_free. apply forallb_ext. apply lranges_iff. Qed.

Lemma mmap_answer_ok_eq len r : mmap_answer_ok (ld_atop L) (lranges L) len r = mmap_answer_ok (s_atop st) (live_ranges st) len r.
Proof. unfold mmap_answer_ok. rewrite ranges_free_eq, (proj1 (proj2 (ir_resv _ _ _ IR))). reflexivity. Qed.

Lemma brk_pages_ok_eq lo len : lbrk_pages_ok L lo len = brk_pages_ok st lo len.
Proof. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq, (proj1 (proj2 (ir_resv _ _ _ IR))). reflexivity. Qed.

Lemma ranges_free_regions a n rid r : ranges_free (live_ranges st) a n = true -> s_regions st !! rid = Some r ->
  let '(b, l) := region_live_range r in a + n <= b \/ b + l <= a.
Proof.
  intros H Hr. unfold ranges_free in H. rewrite forallb_forall in H.
  specialize (H (region_live_range r)). destruct (region_live_range r) as [b l] eqn:E.
  assert (Hin : In (b, l) (live_ranges st)).
  { unfold live_ranges. apply in_app_iff. right. apply in_map_iff. exists (rid, r). rewrite <- E. split; [reflexivity| apply In_map_to_list_regions; exact Hr]. }
  specialize (H Hin). cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; [apply Z.leb_le in H| apply Z.leb_le in H]; lia.
Qed.
End RANGES.


Lemma mmap_ok_facts atop live len r :
  mmap_answer_ok atop live len r = true -> is_err r = false ->
  0 < r /\ r mod PGSZ = 0 /\ r + round_up_pg len <= atop /\ ranges_free live r (round_up_pg len) = true.
Proof.
  unfold mmap_answer_ok, is_errno_form, is_err. intros H E.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_ge in E. unfold TWO64 in *. lia.
  - apply Bool.andb_true_iff in H as [H H4]. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma regions_insert_perm (st : mstate) rid r (F : N * region -> bool) :
  s_regions st !! rid = None ->
  Permutation (List.filter F (map_to_list (<[rid := r]> (s_regions st)))) (List.filter F ((rid, r) :: map_to_list (s_regions st))).
Proof. intros H. apply perm_filter. apply map_to_list_insert. exact H. Qed.

Section NEW_GROUP_REGION.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r len : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HO : x_orph X = None.
Hypothesis HOK : mmap_answer_ok (s_atop st) (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Hypothesis HLEN : 0 < len < LEN_MAX.
Let rid := s_next_rid st.
Let st' := fst (new_region RKGroup r len st).
Let L' := KInv.set_groups ((r, len) :: ld_groups L) L.
Let X' := xorph X (Some rid).

Lemma ng_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma ng_lookup q : s_regions st' !! q = if (q =? rid)%N then Some (mkRegion RKGroup r len) else s_regions st !! q.
Proof. unfold st'. apply lookup_new_region. Qed.
Lemma ng_keep q rq : s_regions st !! q = Some rq -> s_regions st' !! q = Some rq.
Proof. intros H. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite ng_fresh in H; discriminate| exact H]. Qed.
Lemma ng_some q rq : s_regions st' !! q = Some rq -> (q = rid /\ rq = mkRegion RKGroup r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite ng_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma ng_frontier q rq : frontier st' q rq = frontier st q rq. Proof. reflexivity. Qed.

Theorem INVL_new_group_region : INVL X' st' L' BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (mmap_ok_facts _ _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
  pose proof (round_up_ge len) as RU.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[new_region st' frontier region_live_range round_up_pg Z.mul Z.pow Z.add filter].
    + intros q rq Hq. unfold st'. rewrite s_next_rid_new_region. apply ng_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
      split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros [K|K]; discriminate.
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply ng_some in H1 as [[-> ->]|[N1 H1]]; apply ng_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D.
        destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D.
        destruct (region_live_range r1) as [b1 l1]. cbn. lia.
    + exact ir_resv.
    + unfold L'. cbn. eapply Permutation_trans; [apply perm_skip; exact ir_groups|].
      fold rid.
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
      cbn. apply Permutation_refl.
    + unfold L'. cbn. eapply Permutation_trans; [exact ir_metas|].
      fold rid.
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ ng_fresh)].
      cbn. erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn. rewrite ng_frontier. reflexivity.
    + intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_metalen q rq Hq K).
    + intros q rq Hq K. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite ng_frontier. exact (ir_brkfront q rq Hq K).
    + destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
      right. exists q, rq. split; [apply ng_keep; exact Hq| auto].
    + intros b l. unfold L'. cbn. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
      * split; [apply ng_keep; exact Hq| auto].
      * apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
    + intros q1 q2 r1 r2 H1 H2 K1 K2. apply ng_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply ng_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
      exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + unfold L'. cbn. revert ir_brk. change (c_brk (s_ctx st')) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply ng_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply ng_keep; exact Hq| auto].
    + destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
      intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply ng_keep; exact Hq| auto].
    + intros q Hq. unfold X' in Hq. cbn in Hq. inversion Hq. subst q. exists (mkRegion RKGroup r len).
      split; [rewrite ng_lookup, N.eqb_refl; reflexivity|]. split; [reflexivity|].
      intros b Hb. change (s_groups st') with (s_groups st). destruct (s_groups st !! b) as [h|] eqn:E; [| reflexivity]. exfalso.
      destruct (ig_region _ _ _ IG _ _ E) as (rq & Hrq & _). rewrite Hb in Hrq. fold rid in Hrq. rewrite ng_fresh in Hrq. discriminate.
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite ng_frontier. split; [apply ng_keep; exact Hq| auto].
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
  - apply (inv_M_ext X' st st'); [reflexivity| reflexivity|]. apply (inv_M_X X); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X' st st'); [reflexivity| reflexivity| |].
      * intros q rq Hq K E. apply ng_keep. exact Hq.
      * apply (group_ok_X X); [reflexivity|]. exact (G1 m b ai Hb).
    + exact G2.
    + exact G3.
    + intros q rq Hq K Ho. apply ng_some in Hq as [[-> ->]|[NE Hq]].
      * exfalso. apply Ho. reflexivity.
      * apply (G4 q rq Hq K). rewrite HO. discriminate.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply ng_keep; exact Hq| exact K].
  - apply (inv_S_ext X' st st' BL); [reflexivity| reflexivity| reflexivity|]. apply (inv_S_X X); [reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply ng_keep; exact Hrq| exact K].
Qed.
End NEW_GROUP_REGION.
End MI_Ledger.

Module MI_WGroup.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Bool. From Stdlib Require Import Lia. From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. Import SM01. Import SM01.MI_Tree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Inv. Import SM08.MI_Kit. Import SM01.MI_Arith. Import MI_Bits. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_List. Import SM01.MI_Geom. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Ext. Import SM01.MI_Ext2. Import SM01.MI_Shadow. Import SM01.MI_Read. Import SM01.MI_Pres1. Import SM01.MI_Pres2. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Pres3. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_Pres4. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_WFree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import MI_WFree2.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition TF (st : mstate) : Prop :=
  forall rid sh o v t, s_shadow st !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> t = s_tick st -> 12 <= o mod 16.

Definition TKS (st : mstate) (T : N) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh ->
      (forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= T)%N)
      /\ (forall u hl ch, r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= T)%N)
      /\ (forall pg t, r_havp sh !! pg = Some t -> (t <= T)%N).
Definition DOMS (st0 st : mstate) : Prop :=
  forall rid sh, s_shadow st !! rid = Some sh -> exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup.

Lemma TKS_of X st L BL LS : INVL X st L BL LS -> TKS st (s_tick st).
Proof. intros INV. exact (ish_ticks _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.
Lemma DOMS_of X st L BL LS : INVL X st L BL LS -> DOMS st st.
Proof. intros INV. exact (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))). Qed.

Lemma TF_tick_new st t : TKS st (s_tick st) -> (s_tick st < t)%N -> TF (set_tick t st).
Proof.
  intros TK LT rid sh o v t' Hsh Ho E. cbn in E, Hsh. subst t'. destruct (TK rid sh Hsh) as (C & _ & _). destruct (C o v t Ho) as [_ LE]. exfalso. lia.
Qed.

Lemma get_shadow_cells_some st rid o c : r_cells (get_shadow st rid) !! o = Some c -> exists sh, s_shadow st !! rid = Some sh /\ r_cells sh !! o = Some c.
Proof.
  unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn; [intros H; exists sh; auto|]. rewrite lookup_empty. discriminate.
Qed.

Lemma TF_wr8 st q v : TF st -> 12 <= snd q mod 16 -> TF (wr8 q v st).
Proof.
  intros H Hq rid sh o w t. rewrite (wr8_shadow_lookup st q v rid). destruct (N.eqb_spec rid (fst q)) as [->|NE]; [| apply H].
  intros E. inversion E. subst sh. cbn. destruct (Z.eq_dec o (snd q)) as [->|NEo].
  - rewrite lookup_insert_eq. intros _ _. exact Hq.
  - rewrite lookup_insert_ne by congruence. intros Ho Et. destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
Qed.

Lemma TF_hdr_havoc st b : TF st -> TF (hdr_havoc b st).
Proof.
  intros H rid sh o w t. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE].
  - rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn. intros Ho Et.
    destruct (get_shadow_cells_some _ _ _ _ Ho) as (sh0 & Hs0 & Ho0). exact (H _ _ _ _ _ Hs0 Ho0 Et).
  - rewrite lookup_insert_ne by congruence. apply H.
Qed.

Lemma TF_ctrl st st' : s_shadow st' = s_shadow st -> s_tick st' = s_tick st -> TF st -> TF st'.
Proof. intros E1 E2 H rid sh o v t. rewrite E1, E2. apply H. Qed.

Lemma TKS_hdr_havoc st b : TKS st (s_tick st) -> TKS (hdr_havoc b st) (s_tick st).
Proof.
  intros TK rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [| rewrite lookup_insert_ne by congruence; apply TK].
  rewrite lookup_insert_eq. intros E. inversion E. subst sh. cbn.
  assert (G : forall P : shadow -> Prop, (forall sh, s_shadow st !! fst b = Some sh -> P sh) -> P shadow0 -> P (get_shadow st (fst b))).
  { intros P H1 H0. unfold get_shadow. destruct (s_shadow st !! fst b) eqn:Es; [apply H1; reflexivity| exact H0]. }
  split; [| split].
  - apply (G (fun sh => forall o w t, r_cells sh !! o = Some (w, t) -> 0 <= w < 256 /\ (t <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (TK _ _ Hsh))| intros o w t Ho; cbn in Ho; rewrite lookup_empty in Ho; discriminate].
  - intros u hl ch. destruct (Z.eq_dec u (snd b / 16)) as [->|NEu].
    + rewrite lookup_insert_eq. intros E2. inversion E2. subst hl. unfold hav_add. cbn. intros [<-|Hin]; [cbn; lia|].
      apply (proj2 (list_elem_of_In _ _)) in Hin. apply list_elem_of_filter in Hin as [_ Hin]. apply (proj1 (list_elem_of_In _ _)) in Hin.
      revert Hin. apply (G (fun sh => In ch (default [] (r_hav sh !! (snd b / 16))) -> (snd ch <= s_tick st)%N)).
      * intros sh Hsh Hin. destruct (r_hav sh !! (snd b / 16)) as [hl0|] eqn:Eh; cbn in Hin; [| destruct Hin]. exact (proj1 (proj2 (TK _ _ Hsh)) _ hl0 ch Eh Hin).
      * cbn. rewrite lookup_empty. cbn. tauto.
    + rewrite lookup_insert_ne by congruence.
      apply (G (fun sh => r_hav sh !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)); [intros sh Hsh; exact (proj1 (proj2 (TK _ _ Hsh)) u hl ch)|].
      cbn. rewrite lookup_empty. discriminate.
  - apply (G (fun sh => forall pg t, r_havp sh !! pg = Some t -> (t <= s_tick st)%N)); [intros sh Hsh; exact (proj2 (proj2 (TK _ _ Hsh)))|].
    intros pg t Hp. cbn in Hp. rewrite lookup_empty in Hp. discriminate.
Qed.

Lemma DOMS_wr8 st0 st q v : DOMS st0 st -> (exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wr8 q v st).
Proof. intros D Hq. unfold DOMS. apply (wr8_dom st q v (fun rid => exists r, s_regions st0 !! rid = Some r /\ r_kind r = RKGroup) D Hq). Qed.
Lemma DOMS_hdr_havoc st0 st b : DOMS st0 st -> (exists r, s_regions st0 !! fst b = Some r /\ r_kind r = RKGroup) -> DOMS st0 (hdr_havoc b st).
Proof.
  intros D Hb rid sh. unfold hdr_havoc, upd_shadow. cbn. destruct (N.eqb_spec rid (fst b)) as [->|NE]; [intros _; exact Hb|].
  rewrite lookup_insert_ne by congruence. apply D.
Qed.
Lemma TKS_wr8 st q v T : (s_tick st <= T)%N -> TKS st T -> TKS (wr8 q v st) T.
Proof. intros LE TK. exact (wr8_tks st q v T LE TK). Qed.

Lemma sh_ticks_of st rid : TKS st (s_tick st) -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros TK. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - destruct (TK _ _ E) as (_ & A & B). split; [exact A| exact B].
  - split; [intros u hl ch H; rewrite lookup_empty in H; discriminate| intros pg t H; rewrite lookup_empty in H; discriminate].
Qed.


Fixpoint wrs (l : list (aptr * Z)) (st : mstate) : mstate :=
  match l with [] => st | (q, v) :: l' => wrs l' (wr8 q v st) end.

Lemma wrs_app l1 l2 st : wrs (l1 ++ l2) st = wrs l2 (wrs l1 st).
Proof. revert st. induction l1 as [|[q v] l1 IH]; intros st; cbn; [reflexivity| apply IH]. Qed.

Section WRS.

Lemma wrs_ctrl l st : ctrl_eq st (wrs l st) /\ s_tick (wrs l st) = s_tick st.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st; cbn; [split; [apply ctrl_eq_refl| reflexivity]|].
  destruct (IH (wr8 q v st)) as [C T]. split; [eapply ctrl_eq_trans; [apply ctrl_eq_wr8| exact C]| rewrite T; reflexivity].
Qed.

Lemma wrs_read_other l st q : ~ In q (map fst l) ->
  cell_read (get_shadow (wrs l st) (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  revert st. induction l as [|[q' v] l IH]; intros st Hn; cbn; [reflexivity|].
  rewrite IH by (cbn in Hn; tauto). apply cell_read_wr8_other. cbn in Hn. intros ->. apply Hn. left. reflexivity.
Qed.

Lemma wrs_TKS l st T : (s_tick st <= T)%N -> TKS st T -> TKS (wrs l st) T.
Proof.
  revert st. induction l as [|[q v] l IH]; intros st LE TK; cbn; [exact TK|].
  apply IH; [cbn; exact LE|]. apply TKS_wr8; assumption.
Qed.

Lemma wrs_DOMS l st0 st : DOMS st0 st -> (forall q, In q (map fst l) -> exists r, s_regions st0 !! fst q = Some r /\ r_kind r = RKGroup) -> DOMS st0 (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st D H; cbn; [exact D|].
  apply IH; [apply DOMS_wr8; [exact D| apply H; left; reflexivity]| intros q' Hq'; apply H; right; exact Hq'].
Qed.

Lemma wrs_TF l st : TF st -> (forall q, In q (map fst l) -> 12 <= snd q mod 16) -> TF (wrs l st).
Proof.
  revert st. induction l as [|[q v] l IH]; intros st H Hl; cbn; [exact H|].
  apply IH; [apply TF_wr8; [exact H| apply Hl; left; reflexivity]| intros q' Hq'; apply Hl; right; exact Hq'].
Qed.

Lemma wrs_read_last l1 q v l2 st :
  ~ In q (map fst l2) -> TKS st (s_tick st) ->
  cell_read (get_shadow (wrs (l1 ++ (q, v) :: l2) st) (fst q)) (snd q) = Known (Z.land v 255).
Proof.
  intros Hn TK. rewrite wrs_app. cbn. rewrite wrs_read_other by exact Hn.
  destruct (wrs_ctrl l1 st) as [C T].
  apply cell_read_wr8_same. apply sh_ticks_of. rewrite T. apply wrs_TKS; [lia| exact TK].
Qed.
End WRS.


Fixpoint zlist (p : aptr) (size : Z) (i : Z) (n : nat) : list (aptr * Z) :=
  match n with O => [] | S n' => (aadd p (UNIT + i * size - 4), 0) :: zlist p size (i + 1) n' end.

Lemma zero_hdrs_wrs p size i n st : zero_hdrs p size i n st = wrs (zlist p size i n) st.
Proof. revert i st. induction n as [|n IH]; intros; cbn; [reflexivity| apply IH]. Qed.

Lemma in_zlist p size q : forall n i, In q (map fst (zlist p size i n)) <-> exists k, i <= k < i + Z.of_nat n /\ q = aadd p (UNIT + k * size - 4).
Proof.
  induction n as [|n IH]; intros i; cbn.
  - split; [tauto| intros (k & Hk & _); lia].
  - rewrite IH. split.
    + intros [<-|(k & Hk & ->)]; [exists i; split; [lia| reflexivity]| exists k; split; [lia| reflexivity]].
    + intros (k & Hk & ->). destruct (Z.eq_dec k i) as [->|NE]; [left; reflexivity| right; exists k; split; [lia| reflexivity]].
Qed.

Lemma zlist_split p size i n k : i <= k < i + Z.of_nat n ->
  exists l1 l2, zlist p size i n = l1 ++ (aadd p (UNIT + k * size - 4), 0) :: l2
    /\ (forall q, In q (map fst l2) -> exists k', k < k' < i + Z.of_nat n /\ q = aadd p (UNIT + k' * size - 4)).
Proof.
  revert i. induction n as [|n IH]; intros i Hk; [cbn in Hk; lia|].
  cbn. destruct (Z.eq_dec k i) as [->|NE].
  - exists [], (zlist p size (i + 1) n). split; [reflexivity|]. intros q Hq. apply in_zlist in Hq as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
  - destruct (IH (i + 1) ltac:(lia)) as (l1 & l2 & E & H). exists ((aadd p (UNIT + i * size - 4), 0) :: l1), l2.
    rewrite E. split; [reflexivity|]. intros q Hq. destruct (H q Hq) as (k' & Hk' & ->). exists k'. split; [lia| reflexivity].
Qed.


Section NL.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g bg : aptr) (aig idx j size cnt : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st g).
Let p : aptr := (fst bg, sstart (MR st g) idx).
Hypothesis HP : x_pend X = Some p.
Hypothesis STR : get_stride (MR st g) = UNIT * size_class j.
Hypothesis SZ16 : size mod 16 = 0.
Hypothesis SZ0 : 16 <= size.
Hypothesis CNT : 1 <= cnt.
Hypothesis FIT : UNIT + cnt * size <= get_stride (MR st g).
Hypothesis HTF : TF st.
Let q : Z := (snd p - (snd bg + UNIT)) / UNIT.
Let st' := nest_layout st g idx j size cnt.

Definition nl_list : list (aptr * Z) :=
  [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5);
   (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ zlist p size 0 (Z.to_nat (cnt + 1)).

Lemma g_hosts : hosts st bg g. Proof. exists aig. exact Hg. Qed.
Lemma p_eq : slot_start' (MR st g) idx = p. Proof. unfold p. apply (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ g_hosts). Qed.
Lemma bg_gbase : gbase (MR st g) = bg. Proof. apply (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV))) _ _ g_hosts). Qed.

Lemma nl_eq : st' = wrs nl_list st.
Proof.
  unfold st', nest_layout, enframe_at. fold (MR st g). cbn [negb Z.eqb].
  change (aadd (default (0%N, 0) (m_mem (MR st g))) (UNIT + get_stride (MR st g) * idx)) with (slot_start' (MR st g) idx).
  rewrite p_eq. unfold set_size.
  replace (snd (aadd p (get_stride (MR st g) - IB)) - snd p - (UNIT * size_class j - IB)) with 0
    by (unfold aadd; cbn [fst snd]; rewrite STR; unfold UNIT, IB; lia).
  change (5 <=? 0) with false. change (0 =? 0) with true. cbn [negb].
  unfold nl_list. rewrite wrs_app. cbn [wrs app]. rewrite zero_hdrs_wrs. unfold wr16.
  unfold q. fold (gbase (MR st g)). rewrite bg_gbase. reflexivity.
Qed.

Lemma p_mod16 : snd p mod 16 = 0.
Proof.
  unfold p. cbn. unfold sstart. rewrite bg_gbase.
  pose proof (g_align _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hg)) as [_ A].
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [_ SM].
  pose proof (Z.div_mod (snd bg) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (get_stride (MR st g)) 16 ltac:(lia)) as D2.
  unfold UNIT in *. rewrite A in D1. rewrite SM in D2.
  replace (snd bg + 16 + get_stride (MR st g) * idx) with ((snd bg / 16 + 1 + get_stride (MR st g) / 16 * idx) * 16) by nia.
  apply Z_mod_mult.
Qed.

Lemma res16 a d : a mod 16 = 0 -> (a + d) mod 16 = d mod 16.
Proof. intros H. rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

Lemma nl_residues r : In r (map fst nl_list) -> 12 <= snd r mod 16.
Proof.
  pose proof p_mod16 as PM. clearbody p. unfold nl_list. rewrite map_app, in_app_iff. unfold aadd. cbn [map fst snd In]. intros [H|H].
  - destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [snd]; rewrite <- ?Z.add_assoc, (res16 _ _ PM); cbn; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [snd]. rewrite (res16 _ _ PM). unfold UNIT.
    replace (16 + k * size - 4) with (k * size + 12) by lia. rewrite res16; [cbn; lia|].
    rewrite Z.mul_mod, SZ16, Z.mul_0_r by lia. reflexivity.
Qed.

Lemma nl_in_T r : In r (map fst nl_list) ->
  inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r \/ r = (fst bg, sstart (MR st g) (idx + 1) - 4).
Proof.
  unfold nl_list. rewrite map_app, in_app_iff. rewrite sstart_succ. unfold inT, p, aadd. cbn [map fst snd In]. intros [H|H].
  - left. pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ g_hosts) as [SG _].
    destruct H as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold UNIT in *; lia.
  - apply in_zlist in H as (k & Hk & ->). cbn [fst snd]. unfold UNIT in *. rewrite Z2Nat.id in Hk by lia.
    destruct (Z.eq_dec (16 + k * size) (get_stride (MR st g))) as [E|NE].
    + right. unfold aadd. cbn [fst snd]. f_equal. lia.
    + left. unfold aadd. cbn [fst snd]. split; [reflexivity|]. assert (k * size <= cnt * size) by nia. lia.
Qed.
Lemma nl_regions r : In r (map fst nl_list) -> fst r = fst bg.
Proof. intros H. destruct (nl_in_T r H) as [[E _]| ->]; [exact E| reflexivity]. Qed.

Theorem nest_layout_ok :
  INVL X st' L BL LS /\ TF st' /\ ctrl_eq st st' /\ s_tick st' = s_tick st
  /\ known st' (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st' (aadd p (-2)) (Z.land q 255) /\ known st' (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr q 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st' (aadd p (UNIT + k * size - 4)) 0)
  /\ (forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow st' (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
Proof.
  rewrite nl_eq. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (wrs_ctrl nl_list st) as [CE TK].
  pose proof (TKS_of _ _ _ _ _ INV) as TK0. pose proof (DOMS_of _ _ _ _ _ INV) as DM0.
  assert (RD : forall r, ~ inT (fst bg) (sstart (MR st g) idx - 3) (sstart (MR st g) (idx + 1) - 4) r ->
        cell_read (get_shadow (wrs nl_list st) (fst r)) (snd r) = cell_read (get_shadow st (fst r)) (snd r)).
  { intros r Hr. destruct (in_dec aptr_eq_dec r (map fst nl_list)) as [Hin|Hn]; [| apply wrs_read_other; exact Hn].
    destruct (nl_in_T r Hin) as [HT| ->]; [exfalso; exact (Hr HT)|].
    pose proof (ish_hdr0 _ _ ISH bg g (idx + 1) g_hosts ltac:(unfold cnt_of; lia)) as K0. unfold known, SHd, IB in K0. cbn [fst snd] in K0 |- *. rewrite K0.
    assert (E : (fst bg, sstart (MR st g) (idx + 1) - 4) = aadd p (UNIT + cnt * size - 4) /\ UNIT + cnt * size = get_stride (MR st g)).
    { unfold nl_list in Hin. rewrite map_app in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - exfalso. cbn [map fst In] in Hin. pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
        destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold p, aadd in E; cbn [fst snd] in E; rewrite sstart_succ in E; unfold UNIT in *; lia.
      - apply in_zlist in Hin as (k & Hk & Ek). rewrite Z2Nat.id in Hk by lia. apply (f_equal snd) in Ek. unfold p, aadd in Ek. cbn [fst snd] in Ek.
        rewrite sstart_succ in Ek. destruct (Z.eq_dec k cnt) as [->|NEk].
        + split; [unfold p, aadd; cbn [fst snd]; rewrite sstart_succ; f_equal; unfold UNIT in *; lia| unfold UNIT in *; lia].
        + exfalso. assert (k * size <= (cnt - 1) * size) by nia. unfold UNIT in *. lia. }
    destruct E as [E1 E2]. apply (f_equal snd) in E1. cbn [snd] in E1. rewrite E1.
    destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) cnt ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & EZ & Hl2).
    change (cell_read (get_shadow (wrs nl_list st) (fst (aadd p (UNIT + cnt * size - 4)))) (snd (aadd p (UNIT + cnt * size - 4))) = Known (Z.land 0 255)).
    unfold nl_list. rewrite EZ.
    rewrite (app_assoc _ l1) || rewrite app_assoc.
    apply wrs_read_last; [| exact TK0].
    intros Hin2. destruct (Hl2 _ Hin2) as (k' & Hk' & _). rewrite Z2Nat.id in Hk' by lia. lia. }
  pose proof (is_part _ _ _ IS _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite p_eq, HP in P5. unfold one5 in P5.
  assert (NH : s_groups st !! p = None).
  { destruct (s_groups st !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (NB : forall k, In k BL -> bslot k <> p).
  { intros k Hk E. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & nCE & _). apply nCE. split; [| reflexivity]. rewrite <- E. apply in_map. exact Hk. }
  assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hg).
  split; [| split; [| split; [exact CE| split; [exact TK|]]]].
  - split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
    split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
    split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
    apply (inv_SH_write_T X st (wrs nl_list st) BL LS IM IG IS ISH g bg idx g_hosts Hidx NH NB CE TK RD).
    + apply wrs_DOMS; [exact DM0|]. intros r Hr. rewrite (nl_regions r Hr). exact REG.
    + apply wrs_TKS; [lia| exact TK0].
  - apply wrs_TF; [exact HTF| apply nl_residues].
  -
    assert (KN : forall l1 r v l2, nl_list = l1 ++ (r, v) :: l2 -> ~ In r (map fst l2) -> known (wrs nl_list st) r (Z.land v 255)).
    { intros l1 r v l2 E Hn. unfold known, SHd. rewrite E. apply wrs_read_last; [exact Hn| exact TK0]. }
    pose proof (stride_ge _ _ _ IG _ _ g_hosts) as [SG _].
    assert (ZL : forall r, In r (map fst (zlist p size 0 (Z.to_nat (cnt + 1)))) -> snd p + 12 <= snd r).
    { intros r Hr. apply in_zlist in Hr as (k & Hk & ->). cbn. unfold UNIT. nia. }
    split; [| split; [| split; [| split; [| exact RD]]]].
    + apply (KN [(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5)] (aadd p (-3)) _ (zlist p size 0 (Z.to_nat (cnt + 1))) eq_refl).
      intros Hin. pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + rewrite <- (Z.land_assoc q 255 255 : Z.land (Z.land q 255) 255 = Z.land q (Z.land 255 255)) || idtac.
      replace (Z.land q 255) with (Z.land (Z.land q 255) 255) by (rewrite <- Z.land_assoc; reflexivity).
      replace (Z.land (Z.land q 255) 255) with (Z.land q 255) by (rewrite <- Z.land_assoc; reflexivity).
      apply (KN [] (aadd p (-2)) q _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|[E|Hin]]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + apply (KN [(aadd p (-2), q)] (aadd (aadd p (-2)) 1) (Z.shiftr q 8) _ eq_refl).
      cbn [map fst app]. intros [E|[E|[E|Hin]]]; try (unfold aadd in E; cbn in E; apply (f_equal snd) in E; cbn in E; lia). pose proof (ZL _ Hin) as Z1. cbn in Z1. lia.
    + intros k Hk. destruct (zlist_split p size 0 (Z.to_nat (cnt + 1)) k ltac:(rewrite Z2Nat.id by lia; lia)) as (l1 & l2 & E & Hl2).
      change (known (wrs nl_list st) (aadd p (UNIT + k * size - 4)) (Z.land 0 255)).
      apply (KN ([(aadd p (-2), q); (aadd (aadd p (-2)) 1, Z.shiftr q 8); (aadd p (-3), idx); (aadd p (-3), Z.land idx 31 + Z.shiftl 0 5); (aadd p (-3), Z.lor (Z.land idx 31) 192)] ++ l1) _ 0 l2).
      * unfold nl_list. rewrite E. rewrite <- app_assoc. reflexivity.
      * intros Hin. destruct (Hl2 _ Hin) as (k' & Hk' & E'). unfold aadd in E'. apply (f_equal snd) in E'. cbn in E'. unfold UNIT in E'. nia.
Qed.
End NL.
End MI_WGroup.
