(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From Stdlib Require Permutation.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Inv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree2.
Module MI_Ledger.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
  unfold lranges, live_ranges. rewrite (ir_resv _ _ _ IR). rewrite !in_app_iff. split.
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

Lemma mmap_answer_ok_eq len r : mmap_answer_ok (lranges L) len r = mmap_answer_ok (live_ranges st) len r.
Proof. unfold mmap_answer_ok. rewrite ranges_free_eq. reflexivity. Qed.

Lemma brk_pages_ok_eq lo len : lbrk_pages_ok L lo len = brk_pages_ok st lo len.
Proof. unfold lbrk_pages_ok, brk_pages_ok. rewrite ranges_free_eq. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_ok_facts live len r :
  mmap_answer_ok live len r = true -> is_err r = false ->
  0 < r /\ r mod PGSZ = 0 /\ r + round_up_pg len <= alloc_ceiling /\ ranges_free live r (round_up_pg len) = true.
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
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
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
  destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
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


End CeilWrap.
End MI_Ledger.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
Module MI_WAMeta.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_Ledger.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record AM_frame (st st1 : mstate) : Prop := mkAMF {
  amf_groups : s_groups st1 = s_groups st;
  amf_slots : s_slots st1 = s_slots st;
  amf_shadow : s_shadow st1 = s_shadow st;
  amf_tick : s_tick st1 = s_tick st;
  amf_active : forall sc, active st1 sc = active st sc;
  amf_usage : forall sc, usage st1 sc = usage st sc;
  amf_bounces : c_bounces (s_ctx st1) = c_bounces (s_ctx st);
  amf_seq : c_seq (s_ctx st1) = c_seq (s_ctx st);
  amf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  amf_regions : forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st1 !! rid = Some r;
  amf_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amf_ssec : s_secret st1 = s_secret st
}.
Lemma amf_refl st : AM_frame st st.
Proof. constructor; auto; first [reflexivity| lia]. Qed.
Lemma amf_trans a b c : AM_frame a b -> AM_frame b c -> AM_frame a c.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11]; constructor; try congruence.
  - intros rid r H K. apply B10; [| exact K]. apply A10; assumption.
  - clear -A11 B11. eapply N.le_trans; eassumption.
Qed.

Record L_frame (L L1 : mled) : Prop := mkLF {
  lf_groups : ld_groups L1 = ld_groups L;
  lf_live : ld_live L1 = ld_live L;
  lf_resv : ld_resv L1 = ld_resv L
}.
Lemma lf_refl L : L_frame L L. Proof. constructor; reflexivity. Qed.
Lemma lf_trans a b c : L_frame a b -> L_frame b c -> L_frame a c.
Proof. intros [] []; constructor; congruence. Qed.

(* [comment removed for export] *)
Lemma inv_SH_view' st st' BL :
  s_shadow st' = s_shadow st -> s_tick st' = s_tick st ->
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r) ->
  s_groups st' = s_groups st -> s_slots st' = s_slots st -> s_metas st' = s_metas st ->
  inv_SH st BL -> inv_SH st' BL.
Proof.
  intros SH TK HR HG HS HM I.
  pose proof (inv_SH_view st (set_regions (s_regions st) st') BL SH TK eq_refl HG HS) as V.
  assert (ME : forall x, MR (set_regions (s_regions st) st') x = MR st x) by (intros; apply MR_ext; exact HM).
  specialize (V ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) ltac:(intros; rewrite ME; reflexivity) I).
  destruct V as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
  intros rid sh H. destruct (D1 rid sh H) as (r & Hr & K). exists r. split; [apply HR; assumption| exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mslot_succ a k : aadd (mslot a k) META_SIZE = mslot a (k + 1).
Proof. unfold mslot, aadd, META_SIZE. cbn. f_equal. lia. Qed.

Section TAKE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HC : 0 < c_avail_meta_count (s_ctx st).

Lemma am_take_ok {T} (k : mstate -> optr -> M T) bail :
  exists m st2, am_take st k bail = k st2 (Some m) /\ INVL (xidle X (m :: x_idle X)) st2 L BL LS /\ AM_frame st st2 /\ ~ In m (x_idle X).
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (ia_avail _ IA) as [A1 A2]. destruct (A2 HC) as (a & Ht & Eam & FREE).
  set (k0 := NSLOTS - c_avail_meta_count (s_ctx st)) in *.
  exists (mslot a k0).
  unfold am_take, ctx. rewrite Eam.
  set (st1 := upd_ctx _ st). set (st2 := upd_meta (mslot a k0) _ st1).
  exists st2. split; [reflexivity|].
  assert (ABS : s_metas st !! mslot a k0 = None) by (apply FREE; lia).
  assert (MRm : MR st (mslot a k0) = meta0) by (unfold MR, get_meta_rec; rewrite ABS; reflexivity).
  assert (M2 : s_metas st2 = <[mslot a k0 := meta0]> (s_metas st)).
  { unfold st2, st1. rewrite s_metas_upd_meta. cbn. f_equal. rewrite get_meta_rec_upd_ctx. fold (MR st (mslot a k0)). rewrite MRm. reflexivity. }
  assert (MR2 : forall x, MR st2 x = MR st x).
  { intros x. unfold MR, get_meta_rec. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
    - rewrite lookup_insert_eq, ABS. reflexivity.
    - rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (DE : forall x, data_of (MR st2 x) = data_of (MR st x)) by (intros x; rewrite MR2; reflexivity).
  assert (KEYS : forall x, s_metas st2 !! x <> None <-> s_metas st !! x <> None \/ x = mslot a k0).
  { intros x. rewrite M2. destruct (aptr_eq_dec x (mslot a k0)) as [->|NE].
    - rewrite lookup_insert_eq. split; [auto| discriminate].
    - rewrite lookup_insert_ne by congruence. tauto. }
  assert (Ha : s_areas st !! a <> None) by (apply (ia_tail _ IA); exact Ht).
  assert (NLm : forall h, ~ In (mslot a k0) (LS h)).
  { intros h Hin. apply (listed_present _ _ _ _ _ (conj IR (conj IA (conj IM (conj IL (conj IG (conj IS ISH)))))) _ _ Hin). exact ABS. }
  split.
  - (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
      assert (CT2 : c_meta_area_tail (s_ctx st2) = c_meta_area_tail (ctx st)) by reflexivity.
      assert (CC2 : c_avail_meta_count (s_ctx st2) = c_avail_meta_count (s_ctx st) - 1) by reflexivity.
      assert (CA2 : c_avail_meta (s_ctx st2) = Some (mslot a (k0 + 1))) by (rewrite <- mslot_succ; reflexivity).
      destruct IA; constructor.
      * exact ia_ctx.
      * exact ia_secret.
      * exact ia_areas.
      * exact ia_head.
      * exact ia_tail.
      * cbn. intros Hn. exfalso. unfold ctx in Ht. rewrite Ht in Hn. discriminate.
      * intros m mr Hm. rewrite M2 in Hm. destruct (aptr_eq_dec m (mslot a k0)) as [->|NE].
        -- exists a, ar, k0. split; [exact Ea|]. split; [unfold k0; lia| reflexivity].
        -- rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas m mr Hm).
      * rewrite CT2, CA2, CC2. split; [lia|]. intros Hc. exists a. split; [exact Ht|]. split; [unfold k0; f_equal; f_equal; lia|].
        intros k1 Hk1. rewrite M2, lookup_insert_ne; [apply FREE; lia|]. unfold mslot, aadd. intros E. inversion E. unfold META_SIZE in *. lia.
      * rewrite CA2. intros q Hq. inversion Hq. subst q. unfold mslot, aadd. cbn [fst].
        destruct (ia_areas _ _ Ea) as ((r & Hr & K & _) & _). exists r. auto.
      * intros sc Hsc. unfold usage, ctx. cbn. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry.
        apply (gcnt_ext_groups st st2 eq_refl). intros b h m _ _. rewrite MR2. auto.
      * exact ia_usage_keys.
      * exact ia_active_keys.
    + destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn [x_idle x_zomb x_pend x_orph x_fresh xidle].
      * intros m Hm. rewrite !MR2 in *. exact (Q1 m Hm).
      * intros m b Hm. rewrite MR2 in Hm. exact (Q2 m b Hm).
      * intros b h Hb. destruct (Q3 b h Hb) as (m & ? & ? & ?). exists m. rewrite !MR2. auto.
      * intros m [<-|Hm].
        -- split; [rewrite M2, lookup_insert_eq; reflexivity|]. intros [h Hin]. exact (NLm h Hin).
        -- destruct (Q4 m Hm) as [E NI]. split; [| exact NI]. rewrite M2, lookup_insert_ne; [exact E|]. intros Emm. congruence.
      * intros z Hz. rewrite !MR2. exact (Q5 z Hz).
    + destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
      all: try (intros h; destruct h; cbn; apply L1).
      * intros h. pose proof (L2 h) as D. destruct (LS h) as [|x l]; [exact I|]. cbn [dll] in D |- *. eapply linked_ext; [| | exact D]; intros; rewrite MR2; reflexivity.
      * intros m. rewrite !MR2. apply L5.
      * intros m Hm. rewrite !MR2. apply L6. exact Hm.
      * intros sc m Hm. rewrite MR2. exact (L7 sc m Hm).
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      * intros m b ai Hb. pose proof (G1 m b ai Hb) as GO. destruct GO; constructor; rewrite ?MR2; try assumption.
        -- apply KEYS. left. exact g_present.
        -- intros Hml. destruct (g_nest Hml) as (p & i & ? & ? & ? & ? & ?). exists p, i. rewrite !MR2. auto 10.
      * intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MR2. eapply G3; eassumption.
      * intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite MR2. auto.
    + destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
      * intros s m i Hs. rewrite !MR2. exact (S1 s m i Hs).
      * intros b m i Hb Hi. rewrite MR2 in Hi |- *. exact (S2 b m i Hb Hi).
      * intros b m ai i Hb Hi. rewrite MR2 in Hi. rewrite !MR2. exact (S3 b m ai i Hb Hi).
      * intros kk Hk. destruct (S6 kk Hk) as (m & i & ? & ?). exists m, i. rewrite MR2. auto.
    + apply (inv_SH_view st st2); try reflexivity; try (intros; rewrite MR2; reflexivity). exact ISH.
  - split; [constructor; cbn; auto; first [reflexivity| lia]|].
    intros Hin. pose proof (proj1 (im_idle _ _ _ IM _ Hin)) as E. rewrite ABS in E. discriminate.
Qed.
End TAKE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition adv (st : mstate) (p : aptr) : mstate :=
  upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st.

Definition carve_rest (s : mstate) (p : aptr) : mstate :=
  let st2 := match c_meta_area_tail (ctx s) with
             | Some tl => set_areas (<[tl := match (s_areas s) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas s)) s
             | None => upd_ctx (set_meta_area_head (Some p)) s
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
  upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4.

Lemma am_carve_eq {T} st p (k : mstate -> optr -> M T) bail : am_carve st p k bail = am_take (carve_rest (adv st p) p) k bail.
Proof. reflexivity. Qed.

Section CARVE.
Variables (X : extras) (s : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (p : aptr).
Hypothesis INV : INVL X s L BL LS.
Hypothesis HP : c_avail_meta_areas (s_ctx s) = Some (aadd p 4096).
Hypothesis NA : s_areas s !! p = None.
Hypothesis NM : forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None.
Hypothesis PG : PGSZ <= snd p.
Hypothesis PM : snd p mod PGSZ = 0.
Hypothesis INIT : c_init_done (s_ctx s) = 1.
Let s' := carve_rest s p.

(* [comment removed for export] *)
Definition cr_areas : gmap aptr area :=
  match c_meta_area_tail (ctx s) with
  | Some tl => <[p := mkArea (c_secret (ctx s)) None NSLOTS]>
                 (<[tl := match (s_areas s) !! tl with Some a => mkArea (a_check a) (Some p) (a_nslots a) | None => mkArea 0 (Some p) 0 end]> (s_areas s))
  | None => <[p := mkArea (c_secret (ctx s)) None NSLOTS]> (s_areas s)
  end.
Definition cr_head : optr := match c_meta_area_tail (ctx s) with Some _ => c_meta_area_head (ctx s) | None => Some p end.

Lemma tail_not_p tl : c_meta_area_tail (ctx s) = Some tl -> tl <> p.
Proof. intros Ht ->. apply (ia_tail _ (proj1 (proj2 INV)) p Ht). exact NA. Qed.

Lemma cr_shape :
  s_areas s' = cr_areas /\ c_meta_area_head (s_ctx s') = cr_head /\ c_meta_area_tail (s_ctx s') = Some p
  /\ c_avail_meta (s_ctx s') = Some (aadd p AREA_HDR) /\ c_avail_meta_count (s_ctx s') = NSLOTS
  /\ s_regions s' = s_regions s /\ s_metas s' = s_metas s /\ s_groups s' = s_groups s /\ s_slots s' = s_slots s
  /\ s_shadow s' = s_shadow s /\ s_tick s' = s_tick s /\ s_next_rid s' = s_next_rid s /\ s_secret s' = s_secret s /\ s_reserved s' = s_reserved s
  /\ c_avail_meta_areas (s_ctx s') = c_avail_meta_areas (s_ctx s) /\ c_avail_meta_area_count (s_ctx s') = c_avail_meta_area_count (s_ctx s)
  /\ c_secret (s_ctx s') = c_secret (s_ctx s) /\ c_init_done (s_ctx s') = c_init_done (s_ctx s)
  /\ c_active (s_ctx s') = c_active (s_ctx s) /\ c_usage (s_ctx s') = c_usage (s_ctx s) /\ c_free_meta_head (s_ctx s') = c_free_meta_head (s_ctx s)
  /\ c_meta_alloc_shift (s_ctx s') = c_meta_alloc_shift (s_ctx s) /\ c_brk (s_ctx s') = c_brk (s_ctx s)
  /\ c_mmap_counter (s_ctx s') = c_mmap_counter (s_ctx s) /\ c_seq (s_ctx s') = c_seq (s_ctx s)
  /\ c_bounces (s_ctx s') = c_bounces (s_ctx s) /\ c_unmap_seq (s_ctx s') = c_unmap_seq (s_ctx s).
Proof.
  unfold s', carve_rest, cr_areas, cr_head, ctx. destruct (c_meta_area_tail (s_ctx s)) as [tl|] eqn:ET; cbn -[lookup insert NSLOTS AREA_HDR].
  - rewrite lookup_insert_ne by (intros E; exact (tail_not_p tl ET (eq_sym E)) || exact (tail_not_p tl ET E)). rewrite NA. cbn. repeat split; reflexivity.
  - rewrite NA. cbn. repeat split; reflexivity.
Qed.

Lemma cr_areas_lookup a : cr_areas !! a =
  if aptr_eqb a p then Some (mkArea (c_secret (ctx s)) None NSLOTS)
  else match c_meta_area_tail (ctx s) with
       | Some tl => if aptr_eqb a tl then Some (match (s_areas s) !! tl with Some ar => mkArea (a_check ar) (Some p) (a_nslots ar) | None => mkArea 0 (Some p) 0 end)
                    else s_areas s !! a
       | None => s_areas s !! a
       end.
Proof.
  unfold cr_areas. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ET.
  - destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence.
    destruct (aptr_eqb_spec a tl) as [->|NE2]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
  - destruct (aptr_eqb_spec a p) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma mslot0 : aadd p AREA_HDR = mslot p (NSLOTS - NSLOTS).
Proof. unfold mslot, aadd. f_equal. Qed.

Theorem INVL_carve : INVL X s' L BL LS /\ AM_frame s s' /\ 0 < c_avail_meta_count (s_ctx s').
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct cr_shape as (EA & EH & ET & EAM & EAC & ER & EM & EG & ESL & ESH & ETK & EN & ESE & ERS & ECA & ECC & EC1 & EC2 & EC3 & EC4 & EC5 & EC6 & EC7 & EC8 & EC9 & EC10 & EC11).
  assert (FR : forall rid r, frontier s' rid r = frontier s rid r) by (intros; unfold frontier; rewrite ECA; reflexivity).
  assert (MRE : forall x, MR s' x = MR s x) by (intros; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  destruct (ir_cursor _ _ _ IR) as (CU1 & CU2 & CU3). destruct (CU3 _ _ HP) as (rp & Hrp & Kp & _ & _ & Ep & _). cbn in Hrp, Ep.
  assert (HE : forall h, get_head s' h = get_head s h) by (intros [sc|]; cbn [get_head]; unfold active, ctx; rewrite ?EC3, ?EC5; reflexivity).
  split; [| split].
  - split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; rewrite ?ER, ?EN, ?ERS, ?EG, ?ECA, ?ECC, ?EC6, ?EC7; try assumption.
      * eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
      * intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
      * intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
    + destruct IA; constructor; rewrite ?ER, ?EA, ?EH, ?ET, ?EAM, ?EAC, ?EM, ?ESE, ?EC1, ?EC2, ?EC3, ?EC4, ?EC8, ?EC9, ?EC10, ?EC11; try assumption.
      * destruct ia_secret as [S0 [[I0 _]|S1]]; [exfalso; rewrite INIT in I0; discriminate|]. split; [exact S0| right; exact S1].
      * intros a ar. rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp].
        -- intros E. inversion E. subst ar. cbn. split; [| split; [reflexivity| split; [reflexivity| intros a' H; discriminate]]].
           exists rp. rewrite FR. unfold frontier. rewrite HP. cbn. rewrite N.eqb_refl. split; [exact Hrp|]. split; [exact Kp|]. split; [exact PM|]. split; [exact PG|]. unfold PGSZ. lia.
        -- assert (OLD : forall ar0, s_areas s !! a = Some ar0 -> (exists r, s_regions s !! fst a = Some r /\ is_metakind r /\ snd a mod PGSZ = 0 /\ PGSZ <= snd a /\ snd a + PGSZ <= frontier s' (fst a) r)
                          /\ a_check ar0 = c_secret (s_ctx s) /\ a_nslots ar0 = NSLOTS /\ (forall a', a_next ar0 = Some a' -> cr_areas !! a' <> None)).
           { intros ar0 H0. destruct (ia_areas a ar0 H0) as ((r & Hr & K & M & P & F) & C & NS & NX). split; [exists r; rewrite FR; auto 10|]. split; [exact C|]. split; [exact NS|].
             intros a' Ha'. rewrite cr_areas_lookup. destruct (aptr_eqb a' p); [discriminate|].
             destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a' tl); [discriminate|]|]; exact (NX a' Ha'). }
           destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
           ++ destruct (aptr_eqb_spec a tl) as [->|NEt].
              ** destruct (s_areas s !! tl) as [ar0|] eqn:E0; [| exfalso; exact (ia_tail tl ETL E0)].
                 intros E. inversion E. subst ar. cbn. destruct (OLD ar0 E0) as (R1 & C & NS & _). split; [exact R1|]. split; [exact C|]. split; [exact NS|].
                 intros a' Ha'. inversion Ha'. subst a'. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
              ** intros H0. exact (OLD ar H0).
           ++ intros H0. exact (OLD ar H0).
      * intros h Hh. rewrite cr_areas_lookup. destruct (aptr_eqb_spec h p) as [->|NEhp]; [discriminate|].
        unfold cr_head in Hh. destruct (c_meta_area_tail (ctx s)) as [tl|] eqn:ETL.
        -- destruct (aptr_eqb h tl); [discriminate|]. exact (ia_head h Hh).
        -- inversion Hh. congruence.
      * intros t Ht. inversion Ht. subst t. rewrite cr_areas_lookup, aptr_eqb_refl. discriminate.
      * intros H. discriminate.
      * intros m mr Hm. destruct (ia_metas m mr Hm) as (a & ar & k & Ha & Hk & Em). exists a.
        rewrite cr_areas_lookup. destruct (aptr_eqb_spec a p) as [->|NEp]; [rewrite NA in Ha; discriminate|].
        destruct (c_meta_area_tail (ctx s)) as [tl|]; [destruct (aptr_eqb a tl); [eexists _, k; eauto| exists ar, k; auto]| exists ar, k; auto].
      * split; [unfold NSLOTS; lia|]. intros _. exists p. split; [reflexivity|]. split; [rewrite mslot0; reflexivity|].
        intros k Hk. apply NM. unfold NSLOTS in *. lia.
      * intros q Hq. inversion Hq. subst q. cbn. exists rp. auto.
      * intros sc Hsc. unfold usage, ctx. rewrite EC4. fold (ctx s). fold (usage s sc). rewrite (ia_usage sc Hsc). symmetry.
        apply (gcnt_ext s s'); [exact EG| exact EM].
    + apply (inv_M_ext X s s'); [exact EM| exact EG| exact IM].
    + apply (inv_L_ext s s'); [exact EM| exact EG| exact HE| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; rewrite ?EG, ?ER.
      * intros m b ai Hb. apply (group_ok_ext X s s'); [exact EM| exact ESL| intros; rewrite ER; assumption| exact (G1 m b ai Hb)].
      * exact G2.
      * intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !MRE. eapply G3; eassumption.
      * intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (hosts_ext s s' EG), MRE. auto.
      * exact G5.
    + apply (inv_S_ext X s s' BL); [exact EM| exact EG| exact ESL| exact IS].
    + apply (inv_SH_view s s'); auto; intros; rewrite MRE; reflexivity.
  - constructor; rewrite ?EG, ?ESL, ?ESH, ?ETK, ?EC8, ?EC9, ?EC10, ?EN; auto; try reflexivity.
    + intros sc. unfold active, ctx. rewrite EC3. reflexivity.
    + intros sc. unfold usage, ctx. rewrite EC4. reflexivity.
    + intros rid r H _. rewrite ER. exact H.
  - rewrite EAC. unfold NSLOTS. lia.
Qed.
End CARVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma above_frontier X st L BL LS rid r (p : aptr) :
  INVL X st L BL LS -> s_regions st !! rid = Some r -> fst p = rid -> frontier st rid r <= snd p ->
  s_areas st !! p = None /\ forall k, 0 <= k < NSLOTS -> s_metas st !! mslot p k = None.
Proof.
  intros INV Hr Hf Hfr. pose proof (proj1 (proj2 INV)) as IA. split.
  - destruct (s_areas st !! p) as [ar|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _ & _ & _ & F) & _). rewrite Hf, Hr in Hr'. inversion Hr'. subst r'. rewrite Hf in F. unfold PGSZ in F. lia.
  - intros k Hk. destruct (s_metas st !! mslot p k) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em).
    destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _).
    unfold mslot, aadd in Em. inversion Em. rewrite Hf in H0. rewrite <- H0, Hr in Hr'. inversion Hr'. subst r'. rewrite <- H0 in F.
    unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section META_ADV.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcur : c_avail_meta_areas (s_ctx st) = Some (rid, off).
Hypothesis Hcnt : 0 < c_avail_meta_area_count (s_ctx st).
Let p : aptr := (rid, off).
Let a : Z := conc st p.
Let st' := adv st p.
Let L' := KInv.set_metas (map (bump_meta a) (ld_metas L)) L.

Lemma ma_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKMeta /\ PGSZ <= off /\ off mod PGSZ = 0
  /\ off + c_avail_meta_area_count (s_ctx st) * PGSZ = r_len r /\ r_len r mod PGSZ = 0 /\ 0 < r_base r
  /\ r_base r + r_len r <= alloc_ceiling.
Proof.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3). destruct (C3 _ _ Hcur) as (r & Hr & K & P1 & P2 & P3 & P4).
  pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 K) as [S7 S8].
  exists r. repeat split; auto.
  pose proof (round_up_ge (r_len r)). lia.
Qed.

Lemma ma_frontier q rq : frontier st q rq = if (rid =? q)%N then off else r_len rq.
Proof. unfold frontier. rewrite Hcur. reflexivity. Qed.
Lemma ma_frontier' q rq : frontier st' q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st', adv. cbn. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ma_event_pre : event_pre L (EMprotect a PGSZ PROT_RW).
Proof.
  destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|].
  exists (r_base r), (r_len r), (frontier st rid r / PGSZ - 1).
  split.
  - pose proof (ir_metas _ _ _ (proj1 INV)) as P. eapply Permutation_in; [apply Permutation_sym; exact P|].
    apply in_map_iff. exists (rid, r). split; [reflexivity|]. apply filter_In. split; [apply In_map_to_list_regions; exact Hr| cbn; rewrite K; reflexivity].
  - rewrite ma_frontier, N.eqb_refl. unfold a, conc, get_region, p. cbn [fst snd]. rewrite Hr.
    unfold PGSZ in *. pose proof (round_up_ge (r_len r)).
    pose proof (Z.div_mod off 4096 ltac:(lia)) as DM. rewrite P2 in DM. set (q := off / 4096) in *. clearbody q. nia.
Qed.

Theorem INVL_meta_adv : INVL X st' L' BL LS
  /\ c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)
  /\ s_areas st' !! p = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st' !! mslot p k = None)
  /\ PGSZ <= snd p /\ snd p mod PGSZ = 0 /\ c_init_done (s_ctx st') = c_init_done (s_ctx st)
  /\ AM_frame st st'.
Proof.
  destruct ma_region as (r & Hr & K & P1 & P2 & P3 & P4 & P5 & P6).
  destruct (above_frontier X st L BL LS rid r p INV Hr eq_refl ltac:(rewrite ma_frontier, N.eqb_refl; cbn; lia)) as [NA NM].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [cbn; lia| split; [exact P2| split; [reflexivity|]]]]]]].
  2:{ constructor; cbn; auto; first [reflexivity| lia]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - assert (Rg : s_regions st' = s_regions st) by reflexivity. assert (Rn : s_next_rid st' = s_next_rid st) by reflexivity.
    assert (Rv : s_reserved st' = s_reserved st) by reflexivity. assert (Rgr : s_groups st' = s_groups st) by reflexivity.
    assert (Csh : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st)) by reflexivity.
    assert (Cbrk : c_brk (s_ctx st') = c_brk (s_ctx st)) by reflexivity.
    assert (Cam : c_avail_meta_areas (s_ctx st') = Some (aadd p 4096)) by reflexivity.
    assert (Cac : c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st) - 1) by reflexivity.
    unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_metas];
      rewrite ?Rg, ?Rn, ?Rv, ?Rgr, ?Csh, ?Cbrk, ?Cam, ?Cac; try assumption.
    + (* [comment removed for export] *)
      eapply Permutation_trans; [apply Permutation_map; exact ir_metas|]. rewrite map_map.
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. cbn in Hk |- *.
      apply In_map_to_list_regions in Hin. destruct (r_kind rq) eqn:Ekq; try discriminate.
      rewrite ma_frontier.
      pose proof (ir_shape q rq Hin) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(right; exact Ekq)) as [S7 S8].
      destruct (N.eqb_spec rid q) as [<-|NE].
      * rewrite Hr in Hin. inversion Hin. subst rq.
        replace (r_base r + (1 + (off / PGSZ - 1)) * PGSZ) with a.
        2:{ unfold a, conc, get_region, p. cbn. rewrite Hr. unfold PGSZ in *. pose proof (Z.div_mod off 4096 ltac:(lia)). lia. }
        rewrite Z.eqb_refl. f_equal. unfold PGSZ in *.
        pose proof (Z.div_mod off 4096 ltac:(lia)). rewrite P2 in H.
        replace (off + 4096) with ((off / 4096 + 1) * 4096) by lia. rewrite Z.div_mul by lia. lia.
      * destruct (Z.eqb_spec (r_base rq + (1 + (r_len rq / PGSZ - 1)) * PGSZ) a) as [E|NE2]; [| reflexivity]. exfalso.
        unfold a, conc, get_region, p in E. cbn in E. rewrite Hr in E.
        pose proof (Z.div_mod (r_len rq) PGSZ ltac:(unfold PGSZ; lia)) as DM. rewrite S7 in DM.
        pose proof (ir_disj q rid rq r Hin Hr ltac:(congruence)) as D. unfold region_live_range in D. rewrite Ekq, K in D.
        pose proof (round_up_ge (r_len rq)). pose proof (round_up_ge (r_len r)). unfold PGSZ in *. nia.
    + intros q rq Hq Kq. rewrite ma_frontier'. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite ma_frontier in F1, F2.
      split; [exact J|]. destruct (N.eqb_spec rid q) as [<-|NE]; [| auto].
      rewrite Hr in Hq. inversion Hq. subst rq. unfold PGSZ in *. split; [lia|].
      rewrite <- Zplus_mod_idemp_l, P2. reflexivity.
    + intros q rq Hq Kq. rewrite ma_frontier'. destruct (N.eqb_spec rid q) as [<-|NE]; [rewrite Hr in Hq; inversion Hq; subst rq; rewrite Kq in K; discriminate|].
      pose proof (ir_brkfront q rq Hq Kq) as F. rewrite ma_frontier in F. destruct (N.eqb_spec rid q); [congruence| exact F].
    + split; [lia|]. split; [intros _; discriminate|]. intros q o E. inversion E. subst q o. exists r.
      split; [exact Hr|]. split; [right; exact K|]. split; [lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, P2; reflexivity|].
      split; [unfold PGSZ in *; lia| intros _; exact K].
  - destruct IA; constructor; cbn -[frontier PGSZ]; try assumption.
    intros a0 ar Ha. destruct (ia_areas a0 ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
    exists rq. split; [exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
    rewrite ma_frontier'. rewrite ma_frontier in F. destruct (N.eqb_spec rid (fst a0)); lia.
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End META_ADV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma frontier_full X st L rid r :
  inv_R X st L -> c_avail_meta_area_count (s_ctx st) = 0 -> s_regions st !! rid = Some r -> frontier st rid r = r_len r.
Proof.
  intros IR Hc Hr. unfold frontier. destruct (c_avail_meta_areas (s_ctx st)) as [[q off]|] eqn:E; [| reflexivity].
  destruct (N.eqb_spec q rid) as [->|NE]; [| reflexivity].
  destruct (ir_cursor _ _ _ IR) as (_ & _ & C3). destruct (C3 _ _ E) as (r' & Hr' & _ & _ & _ & Eq & _).
  rewrite Hr in Hr'. inversion Hr'. subst r'. rewrite Hc in Eq. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEW_META.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (r : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let n : Z := Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)).
Let len : Z := n * PGSZ.
Hypothesis HOK : mmap_answer_ok (live_ranges st) len r = true.
Hypothesis NERR : is_err r = false.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKMeta r len st).
Let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                              (set_avail_meta_area_count (n - 1) (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1.
Let L' := KInv.set_metas ((r, len, 0) :: ld_metas L) L.

Lemma nm_n : n = 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) /\ 2 <= n.
Proof.
  pose proof (proj1 (ir_shift _ _ _ (proj1 INV))) as S0. unfold n. rewrite Z.shiftl_mul_pow2 by exact S0.
  rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. split; [lia|].
  pose proof (Z.pow_pos_nonneg 2 (c_meta_alloc_shift (s_ctx st))). lia.
Qed.

Lemma nm_len : 0 < len < LEN_MAX.
Proof.
  destruct nm_n as [En N2]. unfold len. split; [unfold PGSZ; lia|].
  destruct (ir_shift _ _ _ (proj1 INV)) as [S0 [S1|(q & rq & Hq & K & E)]].
  - unfold n. rewrite S1. change (Z.shiftl 2 0 * PGSZ) with 8192. unfold LEN_MAX. lia.
  - pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hq) as (A1 & _ & _ & _ & A5 & _). pose proof (round_up_ge (r_len rq)).
    rewrite En. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. rewrite E in *. unfold alloc_ceiling, LEN_MAX, PGSZ in *. nia.
Qed.

Lemma nm_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma nm_lookup q : s_regions st2 !! q = if (q =? rid)%N then Some (mkRegion RKMeta r len) else s_regions st !! q.
Proof. unfold st2, st1. cbn -[new_region]. apply lookup_new_region. Qed.
Lemma nm_keep q rq : s_regions st !! q = Some rq -> s_regions st2 !! q = Some rq.
Proof. intros H. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite nm_fresh in H; discriminate| exact H]. Qed.
Lemma nm_some q rq : s_regions st2 !! q = Some rq -> (q = rid /\ rq = mkRegion RKMeta r len) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite nm_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma nm_frontier q rq : frontier st2 q rq = if (rid =? q)%N then PGSZ else r_len rq.
Proof. reflexivity. Qed.
Lemma nm_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

Lemma nm_event_pre : event_pre L (EMmap 0 len PROT_NONE MAPF).
Proof. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV))|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity| exact nm_len]. Qed.

Theorem INVL_new_meta : INVL X st2 L' BL LS /\ 0 < c_avail_meta_area_count (s_ctx st2)
  /\ c_init_done (s_ctx st2) = c_init_done (s_ctx st) /\ AM_frame st st2.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (mmap_ok_facts _ _ _ HOK NERR) as (R0 & RPG & RCEIL & RFREE).
  destruct nm_n as [En N2]. pose proof nm_len as [L0 L1].
  assert (LPG : len mod PGSZ = 0) by (unfold len; apply Z_mod_mult).
  assert (RU : round_up_pg len = len).
  { unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
    rewrite Z.mod_opp_l_z; [lia| lia| ]. change (2 ^ 12) with 4096. exact LPG. }
  split; [| split; [cbn; lia| split; [reflexivity| constructor; cbn; auto; try reflexivity; [intros q rq H _; apply nm_keep; exact H| unfold rid; lia]]]].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_metas].
    + intros q rq Hq. unfold st2, st1. cbn -[new_region]. rewrite s_next_rid_new_region. apply nm_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn.
      rewrite RU. rewrite RU in RCEIL. split; [lia|]. split; [exact RPG|]. split; [lia|]. split; [lia|]. split; [exact RCEIL|]. intros _. split; [exact LPG|]. unfold len, PGSZ in *. nia.
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply nm_some in H1 as [[-> ->]|[N1 H1]]; apply nm_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. rewrite RU in RFREE |- *. pose proof (ranges_free_regions st _ _ q2 r2 RFREE H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 RFREE H1) as D. rewrite RU in D. destruct (region_live_range r1) as [b1 l1]. cbn. rewrite RU. lia.
    + exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|].
      change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
      cbn. apply Permutation_refl.
    + eapply Permutation_trans; [apply perm_skip; exact ir_metas|].
      change (s_regions st2) with (<[rid := mkRegion RKMeta r len]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ nm_fresh)].
      cbn -[frontier PGSZ Z.div Z.sub]. rewrite nm_frontier, N.eqb_refl. replace (PGSZ / PGSZ - 1) with 0 by reflexivity. apply perm_skip.
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn.
      rewrite (nm_frontier_old q rq Hin). destruct (N.eqb_spec rid q) as [<-|]; [rewrite nm_fresh in Hin; discriminate| reflexivity].
    + intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]].
      * rewrite N.eqb_refl. cbn. split; [exists (c_meta_alloc_shift (s_ctx st) + 1); split; [pose proof (proj1 ir_shift); lia| unfold len; rewrite En; reflexivity]|].
        unfold len, PGSZ in *. split; [nia| reflexivity].
      * destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (nm_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq K. rewrite nm_frontier. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence| reflexivity].
    + cbn. split; [pose proof (proj1 ir_shift); lia|]. right. exists rid, (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|].
      split; [reflexivity|]. cbn. unfold len. rewrite En. reflexivity.
    + intros b l. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1 & E2); exists q, rq.
      * split; [apply nm_keep; exact Hq| auto].
      * apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
    + intros q1 q2 r1 r2 H1 H2 K1 K2. apply nm_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply nm_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
      exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + revert ir_brk. change (c_brk (s_ctx st2)) with (c_brk (s_ctx st)). destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply nm_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NB q rq Hq)].
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply nm_keep; exact Hq| auto].
    + cbn. split; [lia|]. split; [intros _; discriminate|]. intros q off E. inversion E. subst q off.
      exists (mkRegion RKMeta r len). split; [rewrite nm_lookup, N.eqb_refl; reflexivity|]. cbn. split; [right; reflexivity|].
      split; [lia|]. split; [reflexivity|]. split; [unfold len; lia| reflexivity].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & K & NG). exists rq. split; [apply nm_keep; exact Hrq| auto].
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite nm_frontier. split; [apply nm_keep; exact Hq|]. split; [exact K|]. split; [exact M|]. split; [exact P|].
      rewrite (nm_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E|]; [| exact F]. exfalso. rewrite <- E, nm_fresh in Hq. discriminate.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
  - apply (inv_M_ext X st st2); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st2); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X st st2); [reflexivity| reflexivity| intros q rq Hq K E; apply nm_keep; exact Hq| exact (G1 m b ai Hb)].
    + exact G2.
    + exact G3.
    + intros q rq Hq K Ho. apply nm_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq K Ho).
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & K). exists rq. split; [apply nm_keep; exact Hq| exact K].
  - apply (inv_S_ext X st st2 BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & K). exists rq. split; [apply nm_keep; exact Hrq| exact K].
Qed.
End NEW_META.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_brk_dead X st L L' BL LS :
  INVL X st L BL LS ->
  ld_resv L' = ld_resv L -> ld_groups L' = ld_groups L -> ld_metas L' = ld_metas L -> ld_brkreg L' = ld_brkreg L ->
  ld_brk L' = BPDead ->
  INVL X (upd_ctx (set_brk BrkDead) st) L' BL LS /\ AM_frame st (upd_ctx (set_brk BrkDead) st).
Proof.
  intros INV E1 E2 E3 E4 E5. destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  set (st' := upd_ctx (set_brk BrkDead) st).
  assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by reflexivity.
  split; [| constructor; cbn; auto; first [reflexivity| lia]].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; cbn -[frontier]; rewrite ?E1, ?E2, ?E3, ?E4, ?E5; try assumption.
    all: try reflexivity.
    all: try (intros q rq H1 H2; rewrite FR; first [exact (ir_metalen q rq H1 H2)| exact (ir_brkfront q rq H1 H2)]).
    all: try (eapply Permutation_trans; [exact ir_metas|]; erewrite map_ext; [apply Permutation_refl|]; intros [q rq]; cbn -[frontier]; rewrite FR; reflexivity).
  - destruct IA; constructor; cbn -[frontier]; try assumption.
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.

(* [comment removed for export] *)
Lemma round_up_pg_mod x : round_up_pg x mod PGSZ = 0.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  pose proof (Z.div_mod (-x) 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as B.
  replace (x + (- x) mod 4096) with ((- ((- x) / 4096)) * 4096) by lia. apply Z_mod_mult.
Qed.
Lemma round_up_pg_id x : x mod PGSZ = 0 -> round_up_pg x = x.
Proof.
  intros H. unfold round_up_pg. unfold PGSZ in *. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H in D.
  replace (- x) with ((- (x / 4096)) * 4096) by lia. rewrite Z_mod_mult. lia.
Qed.

Lemma brk_pages_ok_facts st lo len :
  brk_pages_ok st lo len = true -> 0 < lo /\ lo + len <= alloc_ceiling /\ ranges_free (live_ranges st) lo len = true.
Proof.
  unfold brk_pages_ok. intros H. apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. auto.
Qed.

Lemma regions_update_perm (st : mstate) rid r r' (F : N * region -> bool) :
  s_regions st !! rid = Some r -> F (rid, r) = false -> F (rid, r') = false ->
  Permutation (List.filter F (map_to_list (s_regions st))) (List.filter F (map_to_list (<[rid := r']> (s_regions st)))).
Proof.
  intros H F1 F2.
  eapply Permutation_trans; [apply perm_filter; apply Permutation_sym; apply (map_to_list_delete _ _ _ H)|].
  eapply Permutation_trans; [| apply perm_filter; apply (map_to_list_delete _ rid r'); rewrite lookup_insert_eq; reflexivity].
  cbn. rewrite F1, F2. rewrite delete_insert_eq. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BRK_GROW.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (rid : N) (off : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkLive rid off.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Let old : Z := conc st (rid, off).
Hypothesis HOK : brk_pages_ok st old PGSZ = true.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st.
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, off)) (set_brk (BrkLive rid (off + PGSZ)) c))) st1.
Let st3 := adv st2 (rid, off).

Lemma bg_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKBrk /\ r_len r = off /\ ld_brk L = BPLive
  /\ ld_brkreg L = Some (r_base r, off) /\ 0 < r_base r /\ r_base r mod PGSZ = 0 /\ off mod PGSZ = 0 /\ 2 * PGSZ <= off
  /\ old = r_base r + off.
Proof.
  pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [BP (r & Hr & K & E)].
  pose proof (ir_shape _ _ _ (proj1 INV) _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6). destruct (S6 ltac:(left; exact K)) as [S7 S8].
  exists r. split; [exact Hr|]. split; [exact K|]. split; [exact E|]. split; [exact BP|].
  split; [rewrite <- E; apply (proj2 (ir_brkreg _ _ _ (proj1 INV) (r_base r) (r_len r))); exists rid, r; auto|].
  split; [exact S1|]. split; [exact S2|]. split; [rewrite <- E; exact S7|]. split; [rewrite <- E; exact S8|].
  unfold old, conc, get_region. rewrite Hr. reflexivity.
Qed.

Let L' := KInv.set_brkreg (Some (old - off, off + PGSZ)) L.

Lemma bg_lookup q : s_regions st3 !! q = if (q =? rid)%N then option_map (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) (s_regions st !! rid) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[upd_region]. apply lookup_upd_region. Qed.
Lemma bg_frontier q rq : frontier st3 q rq = if (rid =? q)%N then off + 4096 else r_len rq.
Proof. unfold frontier, st3, adv. cbn. reflexivity. Qed.
Lemma bg_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

Lemma bg_event_pre : event_pre L (EBrk (old + PGSZ)).
Proof.
  destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
  right. right. exists (r_base r), off. split; [exact BP|]. split; [exact BR|]. lia.
Qed.

Theorem INVL_brk_grow : INVL X st3 L' BL LS
  /\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, off) 4096)
  /\ s_areas st3 !! (rid, off) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, off) k = None)
  /\ PGSZ <= off /\ off mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
  destruct bg_region as (r & Hr & K & E & BP & BR & B0 & BM & OM & O2 & Eold).
  destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF).
  destruct (above_frontier X st L BL LS rid r (rid, off) INV Hr eq_refl ltac:(rewrite (bg_frontier_old _ _ Hr); cbn; lia)) as [NA NM].
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  set (r' := mkRegion RKBrk (r_base r) (off + PGSZ)).
  assert (LK : forall q, s_regions st3 !! q = if (q =? rid)%N then Some r' else s_regions st !! q).
  { intros q. rewrite bg_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite Hr; cbn; rewrite K; reflexivity| reflexivity]. }
  assert (KEEP : forall q rq, s_regions st !! q = Some rq -> q <> rid -> s_regions st3 !! q = Some rq).
  { intros q rq Hq NE. rewrite LK. destruct (N.eqb_spec q rid); [congruence| exact Hq]. }
  assert (SOME : forall q rq, s_regions st3 !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq)).
  { intros q rq. rewrite LK. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. }
  assert (KEEPG : forall q rq, s_regions st !! q = Some rq -> r_kind rq = RKGroup -> s_regions st3 !! q = Some rq).
  { intros q rq Hq Kq. apply KEEP; [exact Hq|]. intros ->. rewrite Hr in Hq. inversion Hq. subst. congruence. }
  assert (KEEPM : forall q rq, s_regions st !! q = Some rq -> is_metakind rq -> exists rq', s_regions st3 !! q = Some rq' /\ is_metakind rq').
  { intros q rq Hq Kq. destruct (N.eq_dec q rid) as [->|NE]; [exists r'; rewrite LK, N.eqb_refl; split; [reflexivity| left; reflexivity]|].
    exists rq. split; [apply KEEP; assumption| exact Kq]. }
  assert (RU : round_up_pg (off + PGSZ) = off + PGSZ) by (apply round_up_pg_id; unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity).
  assert (RUo : round_up_pg off = off) by (apply round_up_pg_id; exact OM).
  assert (F3 : s_metas st3 = s_metas st /\ s_areas st3 = s_areas st /\ s_groups st3 = s_groups st /\ s_slots st3 = s_slots st
               /\ s_shadow st3 = s_shadow st /\ s_tick st3 = s_tick st /\ s_next_rid st3 = s_next_rid st /\ s_secret st3 = s_secret st
               /\ s_reserved st3 = s_reserved st /\ (forall h, get_head st3 h = get_head st h)
               /\ c_usage (s_ctx st3) = c_usage (s_ctx st) /\ c_bounces (s_ctx st3) = c_bounces (s_ctx st) /\ c_seq (s_ctx st3) = c_seq (s_ctx st)
               /\ c_mmap_counter (s_ctx st3) = c_mmap_counter (s_ctx st) /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st)
               /\ c_meta_alloc_shift (s_ctx st3) = c_meta_alloc_shift (s_ctx st) /\ c_secret (s_ctx st3) = c_secret (s_ctx st)
               /\ c_avail_meta (s_ctx st3) = c_avail_meta (s_ctx st) /\ c_avail_meta_count (s_ctx st3) = c_avail_meta_count (s_ctx st)
               /\ c_meta_area_head (s_ctx st3) = c_meta_area_head (s_ctx st) /\ c_meta_area_tail (s_ctx st3) = c_meta_area_tail (s_ctx st)
               /\ c_free_meta_head (s_ctx st3) = c_free_meta_head (s_ctx st) /\ c_unmap_seq (s_ctx st3) = c_unmap_seq (s_ctx st)).
  { unfold st3, adv, st2, st1, upd_region, get_region. rewrite Hr. repeat split; try reflexivity. all: intros h; destruct h; reflexivity. }
  destruct F3 as (FM & FA & FG & FS & FSH & FT & FN & FSE & FRS & FH & FU & FB & FQ & FMC & FI & FSF & FSC & FAM & FAC & FMH & FMT & FFH & FUS).
  split; [| split; [reflexivity| split; [rewrite FA; exact NA| split; [rewrite FM; exact NM| split; [clear -O2; unfold PGSZ in *; lia| split; [exact OM| split; [exact FI|]]]]]]].
  2:{ constructor; rewrite ?FG, ?FS, ?FSH, ?FT, ?FB, ?FQ, ?FMC, ?FN; auto; try reflexivity; try lia.
      - intros sc. exact (FH (LActive sc)).
      - intros sc. unfold usage, ctx. rewrite FU. reflexivity. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_brkreg].
    + intros q rq Hq. rewrite FN.
      apply SOME in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids _ _ Hq)].
    + intros q rq Hq. apply SOME in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RU.
      pose proof (ir_shape _ _ Hr) as (S1 & S2 & S3 & S4 & S5 & S6).
      split; [lia|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold alloc_ceiling, LEN_MAX, PGSZ in *; lia|]. split; [unfold PGSZ in *; lia|].
      intros _. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity| lia].
    + intros q1 q2 r1 r2 H1 H2 NE.
      assert (GROW : forall q rq, s_regions st !! q = Some rq -> q <> rid ->
                let '(b2, l2) := region_live_range rq in r_base r + PGSZ + (round_up_pg (off + PGSZ) - PGSZ) <= b2 \/ b2 + l2 <= r_base r + PGSZ).
      { intros q rq Hq NEq. pose proof (ir_disj rid q r rq Hr Hq ltac:(congruence)) as D. unfold region_live_range in D at 1. rewrite K, E, RUo in D.
        pose proof (ranges_free_regions st _ _ q rq PF Hq) as D2. rewrite Eold in D2.
        pose proof (ir_shape q rq Hq) as (T1 & _ & T3 & _). pose proof (round_up_ge (r_len rq)) as T4.
        assert (NB : r_kind rq <> RKBrk) by (intros Kq; apply NEq; exact (ir_brk1 q rid rq r Hq Hr Kq K)).
        unfold region_live_range in *. destruct (r_kind rq); [congruence| |]; rewrite RU; unfold PGSZ in *; lia. }
      apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn. pose proof (GROW q2 r2 H2 N2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (GROW q1 r1 H1 N1) as D. destruct (region_live_range r1) as [b1 l1]. cbn. lia.
    + rewrite FRS. exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|]. apply Permutation_map.
      change (s_regions st3) with (s_regions st1). unfold st1, upd_region, get_region. rewrite Hr. cbn -[map_to_list].
      apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity.
    + eapply Permutation_trans; [exact ir_metas|].
      eapply Permutation_trans; [| apply Permutation_map; change (s_regions st3) with (s_regions st1); unfold st1, upd_region, get_region; rewrite Hr; cbn -[map_to_list];
                                   apply (regions_update_perm st rid r _ _ Hr); cbn; rewrite ?K; reflexivity].
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin Hk]. apply In_map_to_list_regions in Hin. cbn in Hk. cbn [fst snd].
      rewrite (bg_frontier_old q rq Hin), bg_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite Hr in Hin; inversion Hin; subst rq; rewrite K in Hk; discriminate| reflexivity].
    + intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq Kq) as (J & F1 & F2). rewrite (bg_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq Kq. rewrite bg_frontier. apply SOME in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|].
      exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
    + rewrite FSF. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
      exists q, rq. split; [apply KEEP; [exact Hq| intros ->; rewrite Hr in Hq; inversion Hq; subst; congruence]| auto].
    + intros b l. split.
      * intros Eb. inversion Eb. subst b l. exists rid, r'. split; [rewrite LK, N.eqb_refl; reflexivity|]. cbn. repeat split; auto. lia.
      * intros (q & rq & Hq & Kq & Eb & El). apply SOME in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; f_equal; f_equal; lia|].
        exfalso. apply NE. exact (ir_brk1 q rid rq r Hq Hr Kq K).
    + intros q1 q2 r1 r2 H1 H2 K1 K2.
      apply SOME in H1 as [[-> ->]|[N1 H1]]; apply SOME in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
      * exfalso. apply N2. exact (ir_brk1 q2 rid r2 r H2 Hr K2 K).
      * exfalso. apply N1. exact (ir_brk1 q1 rid r1 r H1 Hr K1 K).
      * exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + change (c_brk (s_ctx st3)) with (BrkLive rid (off + PGSZ)). split; [exact BP|]. exists r'. rewrite LK, N.eqb_refl. cbn. auto.
    + change (c_avail_meta_area_count (s_ctx st3)) with (1 - 1). change (c_avail_meta_areas (s_ctx st3)) with (Some (aadd (rid, off) 4096)).
      split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists r'. rewrite LK, N.eqb_refl.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [unfold PGSZ in *; lia|]. split; [unfold PGSZ in *; rewrite <- Zplus_mod_idemp_l, OM; reflexivity|].
      cbn. split; [unfold PGSZ; lia| intros; lia].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply KEEPG; assumption|]. split; [exact Kq|]. rewrite FG. exact NG.
  - destruct IA; constructor; rewrite ?FA, ?FM, ?FSE, ?FU, ?FB, ?FQ, ?FMC, ?FI, ?FSC, ?FAM, ?FAC, ?FMH, ?FMT, ?FUS; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
      destruct (KEEPM _ _ Hq Kq) as (rq' & Hq' & Kq'). exists rq'. rewrite bg_frontier. split; [exact Hq'|]. split; [exact Kq'|]. split; [exact M|]. split; [exact P|].
      rewrite (bg_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|NE1].
      * rewrite <- E1, Hr in Hq. inversion Hq. subst rq. lia.
      * rewrite LK in Hq'. destruct (N.eqb_spec (fst a) rid); [congruence|]. rewrite Hq in Hq'. inversion Hq'. subst. lia.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). destruct (KEEPM _ _ Hrq Kq) as (rq' & Hq' & Kq'). exists rq'. auto.
    + intros sc Hsc. unfold usage, ctx. rewrite FU. fold (ctx st). fold (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply (gcnt_ext st st3 FG FM).
    + intros sc g. unfold active, ctx in FH. rewrite <- !get_head_active, (FH (LActive sc)). apply ia_active_keys.
  - apply (inv_M_ext X st st3); [exact FM| exact FG| exact IM].
  - apply (inv_L_ext st st3); [exact FM| exact FG| exact FH| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor; rewrite ?FG.
    + intros m b ai Hb. apply (group_ok_ext X st st3); [exact FM| exact FS| intros q rq Hq Kq _; apply KEEPG; assumption| exact (G1 m b ai Hb)].
    + exact G2.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite !(MR_ext st st3 FM). eapply G3; eassumption.
    + intros q rq Hq Kq Ho. apply SOME in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml). exists m.
      rewrite (hosts_ext st st3 FG), (MR_ext st st3 FM). auto.
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply KEEPG; assumption| exact Kq].
  - apply (inv_S_ext X st st3 BL); [exact FM| exact FG| exact FS| exact IS].
  - apply (inv_SH_view' st st3 BL FSH FT KEEPG FG FS FM ISH).
Qed.
End BRK_GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BRK_FIRST.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (cur : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hbrk : c_brk (s_ctx st) = BrkUntried.
Hypothesis Hcnt : c_avail_meta_area_count (s_ctx st) = 0.
Hypothesis Hcur : brk0_answer_ok cur = true.
Let base : Z := round_up_pg cur.
Hypothesis HOK : brk_pages_ok st base (2 * PGSZ) = true.
Let rid := s_next_rid st.
Let st1 := fst (new_region RKBrk base (2 * PGSZ) st).
Let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (rid, PGSZ)) (set_brk (BrkLive rid (2 * PGSZ)) c))) st1.
Let st3 := adv st2 (rid, PGSZ).
Variable L0 : mled.
Hypothesis HL0 : ld_resv L0 = ld_resv L /\ ld_groups L0 = ld_groups L /\ ld_metas L0 = ld_metas L.
Let L' := KInv.set_brkph BPLive (KInv.set_brkreg (Some (base, 2 * PGSZ)) L0).

Lemma bf_base : 0 < base /\ base mod PGSZ = 0 /\ base + 2 * PGSZ <= alloc_ceiling /\ ranges_free (live_ranges st) base (2 * PGSZ) = true.
Proof.
  destruct (brk_pages_ok_facts _ _ _ HOK) as (P0 & PC & PF). split; [exact P0|]. split; [apply round_up_pg_mod|]. auto.
Qed.

Lemma bf_fresh : s_regions st !! rid = None.
Proof.
  destruct (s_regions st !! rid) as [r0|] eqn:E; [| reflexivity]. exfalso.
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ E) as H. unfold rid in H. lia.
Qed.
Lemma bf_nobrk q rq : s_regions st !! q = Some rq -> r_kind rq <> RKBrk.
Proof. pose proof (ir_brk _ _ _ (proj1 INV)) as B. rewrite Hbrk in B. destruct B as [_ NB]. apply NB. Qed.
Lemma bf_lookup q : s_regions st3 !! q = if (q =? rid)%N then Some (mkRegion RKBrk base (2 * PGSZ)) else s_regions st !! q.
Proof. unfold st3, adv, st2, st1. cbn -[new_region Z.mul]. apply lookup_new_region. Qed.
Lemma bf_keep q rq : s_regions st !! q = Some rq -> s_regions st3 !! q = Some rq.
Proof. intros H. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|]; [rewrite bf_fresh in H; discriminate| exact H]. Qed.
Lemma bf_some q rq : s_regions st3 !! q = Some rq -> (q = rid /\ rq = mkRegion RKBrk base (2 * PGSZ)) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite bf_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma bf_frontier q rq : frontier st3 q rq = if (rid =? q)%N then PGSZ + 4096 else r_len rq.
Proof. reflexivity. Qed.
Lemma bf_frontier_old q rq : s_regions st !! q = Some rq -> frontier st q rq = r_len rq.
Proof. intros Hq. exact (frontier_full X st L q rq (proj1 INV) Hcnt Hq). Qed.

Theorem INVL_brk_first : INVL X st3 L' BL LS
  /\ c_avail_meta_areas (s_ctx st3) = Some (aadd (rid, PGSZ) 4096)
  /\ s_areas st3 !! (rid, PGSZ) = None /\ (forall k, 0 <= k < NSLOTS -> s_metas st3 !! mslot (rid, PGSZ) k = None)
  /\ PGSZ <= PGSZ /\ PGSZ mod PGSZ = 0 /\ c_init_done (s_ctx st3) = c_init_done (s_ctx st) /\ AM_frame st st3.
Proof.
  destruct bf_base as (B0 & BM & BC & BF). destruct HL0 as (HL1 & HL2 & HL3).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (NA : s_areas st !! (rid, PGSZ) = None).
  { destruct (s_areas st !! (rid, PGSZ)) as [ar|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_areas _ IA _ _ E) as ((r' & Hr' & _) & _). cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
  assert (NM : forall k, 0 <= k < NSLOTS -> s_metas st !! mslot (rid, PGSZ) k = None).
  { intros k Hk. destruct (s_metas st !! mslot (rid, PGSZ) k) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k' & Ha & Hk' & Em). destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _) & _).
    unfold mslot, aadd in Em. inversion Em. rewrite <- H0 in Hr'. cbn in Hr'. fold rid in Hr'. rewrite bf_fresh in Hr'. discriminate. }
  assert (RU : round_up_pg (2 * PGSZ) = 2 * PGSZ) by reflexivity.
  split; [| split; [reflexivity| split; [exact NA| split; [exact NM| split; [lia| split; [reflexivity| split; [reflexivity|]]]]]]].
  2:{ constructor; cbn -[Z.mul]; auto; try reflexivity; [intros q rq H _; apply bf_keep; exact H| unfold rid; lia]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - unfold L'. destruct IR; constructor; cbn [KInv.ld_metas KInv.ld_groups KInv.ld_resv KInv.ld_brkreg KInv.ld_brk KInv.ld_live KInv.set_brkreg KInv.set_brkph]; rewrite ?HL1, ?HL2, ?HL3.
    + intros q rq Hq. change (s_next_rid st3) with (N.succ (s_next_rid st)). apply bf_some in Hq as [[-> _]|[_ Hq]]; [unfold rid; lia|]. pose proof (ir_ids q rq Hq). lia.
    + intros q rq Hq. apply bf_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn -[Z.mul]. rewrite RU.
      split; [exact B0|]. split; [exact BM|]. split; [unfold PGSZ; lia|]. split; [unfold PGSZ, LEN_MAX; lia|]. split; [exact BC|]. intros _. split; [apply Z_mod_mult| lia].
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * cbn -[Z.mul]. rewrite RU. pose proof (ranges_free_regions st _ _ q2 r2 BF H2) as D. destruct (region_live_range r2) as [b2 l2]. unfold PGSZ in *. lia.
      * pose proof (ranges_free_regions st _ _ q1 r1 BF H1) as D. destruct (region_live_range r1) as [b1 l1]. cbn -[Z.mul]. rewrite RU. unfold PGSZ in *. lia.
    + exact ir_resv.
    + eapply Permutation_trans; [exact ir_groups|].
      change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
      cbn -[Z.mul map_to_list]. apply Permutation_refl.
    + eapply Permutation_trans; [exact ir_metas|].
      change (s_regions st3) with (<[rid := mkRegion RKBrk base (2 * PGSZ)]> (s_regions st)).
      eapply Permutation_trans; [| apply Permutation_map; apply Permutation_sym; apply (regions_insert_perm st rid _ _ bf_fresh)].
      cbn -[frontier PGSZ Z.div Z.sub Z.mul map_to_list].
      erewrite map_ext_in; [apply Permutation_refl|]. intros [q rq] Hin. apply filter_In in Hin as [Hin _]. apply In_map_to_list_regions in Hin. cbn [fst snd].
      rewrite (bf_frontier_old q rq Hin), bf_frontier. destruct (N.eqb_spec rid q) as [<-|]; [rewrite bf_fresh in Hin; discriminate| reflexivity].
    + intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|].
      destruct (N.eqb_spec rid q) as [<-|]; [congruence|]. pose proof (ir_metalen q rq Hq K) as (J & F1 & F2). rewrite (bf_frontier_old q rq Hq) in F1, F2. auto.
    + intros q rq Hq K. rewrite bf_frontier. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [rewrite N.eqb_refl; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq K).
    + cbn. split; [exact (proj1 ir_shift)|]. destruct ir_shift as [_ [S|(q & rq & Hq & Kq & Eq)]]; [left; exact S| right].
      exists q, rq. split; [apply bf_keep; exact Hq| auto].
    + intros b l. split.
      * intros Eb. inversion Eb. subst b l. exists rid, (mkRegion RKBrk base (2 * PGSZ)). split; [rewrite bf_lookup, N.eqb_refl; reflexivity|]. cbn. auto.
      * intros (q & rq & Hq & Kq & Eb & El). apply bf_some in Hq as [[-> ->]|[NE Hq]]; [cbn in Eb, El; subst; reflexivity|]. exfalso. exact (bf_nobrk q rq Hq Kq).
    + intros q1 q2 r1 r2 H1 H2 K1 K2.
      apply bf_some in H1 as [[-> ->]|[N1 H1]]; apply bf_some in H2 as [[-> ->]|[N2 H2]]; [reflexivity| | |].
      * exfalso. exact (bf_nobrk q2 r2 H2 K2).
      * exfalso. exact (bf_nobrk q1 r1 H1 K1).
      * exfalso. exact (bf_nobrk q1 r1 H1 K1).
    + cbn -[Z.mul]. split; [reflexivity|]. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl. cbn. auto.
    + cbn -[Z.mul]. split; [lia|]. split; [intros; lia|]. intros q o Eq. inversion Eq. subst q o. exists (mkRegion RKBrk base (2 * PGSZ)). rewrite bf_lookup, N.eqb_refl.
      split; [reflexivity|]. split; [left; reflexivity|]. cbn -[Z.mul]. unfold PGSZ. split; [lia|]. split; [reflexivity|]. split; [lia| intros; lia].
    + intros q Hq. destruct (ir_orph q Hq) as (rq & Hrq & Kq & NG). exists rq. split; [apply bf_keep; exact Hrq| auto].
  - destruct IA; constructor; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & Kq & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite bf_frontier. split; [apply bf_keep; exact Hq|]. split; [exact Kq|]. split; [exact M|]. split; [exact P|].
      rewrite (bf_frontier_old _ _ Hq) in F. destruct (N.eqb_spec rid (fst a)) as [E1|]; [| exact F]. exfalso. rewrite <- E1, bf_fresh in Hq. discriminate.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
  - apply (inv_M_ext X st st3); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st3); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]. constructor.
    + intros m b ai Hb. apply (group_ok_ext X st st3); [reflexivity| reflexivity| intros q rq Hq Kq E; apply bf_keep; exact Hq| exact (G1 m b ai Hb)].
    + exact G2.
    + exact G3.
    + intros q rq Hq Kq Ho. apply bf_some in Hq as [[-> ->]|[NE Hq]]; [discriminate|]. exact (G4 q rq Hq Kq Ho).
    + intros b h Hb. destruct (G5 b h Hb) as (rq & Hq & Kq). exists rq. split; [apply bf_keep; exact Hq| exact Kq].
  - apply (inv_S_ext X st st3 BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    intros q sh Hq. destruct (D1 q sh Hq) as (rq & Hrq & Kq). exists rq. split; [apply bf_keep; exact Hrq| exact Kq].
Qed.
End BRK_FIRST.


End CeilWrap.
End MI_WAMeta.

(* [comment removed for export] *)
Module MI_WAMeta2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_Ledger MI_WAMeta.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

Lemma INVL_am_init X st L BL LS : INVL X st L BL LS ->
  INVL X (am_init st) L BL LS /\ c_init_done (s_ctx (am_init st)) = 1 /\ AM_frame st (am_init st).
Proof.
  intros INV. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). unfold am_init, ctx.
  destruct (ia_secret _ IA) as [S0 [(I0 & C0 & A0)|(I1 & C1)]].
  - rewrite I0. cbn. set (st' := upd_ctx _ st).
    split; [| split; [reflexivity| constructor; cbn; auto; first [reflexivity| lia]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + destruct IR; constructor; try assumption.
    + destruct IA; constructor; try assumption.
      * cbn. split; [exact S0|]. right. auto.
      * intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. rewrite A0 in Ha. rewrite lookup_empty in Ha. discriminate.
    + apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
    + apply (inv_L_ext st st'); [reflexivity| reflexivity| intros h; destruct h; reflexivity| exact IL].
    + destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
      intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 m b ai Hb)].
    + apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
    + apply (inv_SH_view st st'); try reflexivity. exact ISH.
  - rewrite I1. cbn. split; [exact INV|]. split; [exact I1| apply amf_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 (Some m)) Post.

Lemma am_take_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
  intros INV AF LF HC. destruct (am_take_ok X st L BL LS INV HC k bail) as (m & st2 & -> & INV2 & AF2 & NI).
  eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| exact LF].
Qed.

Lemma am_carve_ft s p L LS : INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC].
Qed.

Lemma am_finish_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
  ftree L (am_finish st true k bail) Post.
Proof.
  intros INV AF LF HC HI.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ft; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')|].
      destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
  intros INV AF LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact LF].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

Lemma lbrk_pages_ok_ext L1 L2 lo len :
  ld_resv L1 = ld_resv L2 -> ld_groups L1 = ld_groups L2 -> ld_metas L1 = ld_metas L2 -> ld_brkreg L1 = ld_brkreg L2 ->
  lbrk_pages_ok L1 lo len = lbrk_pages_ok L2 lo len.
Proof. intros E1 E2 E3 E4. unfold lbrk_pages_ok, lranges. rewrite E1, E2, E3, E4. reflexivity. Qed.

Theorem alloc_meta_ft st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 LF.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. clear AF0 AFi INV0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    eapply KS; [exact INV1| | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ft; [exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  (* [comment removed for export] *)
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  - (* [comment removed for export] *)
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
           destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - (* [comment removed for export] *) eapply am_after_brk_ft; [exact INV| exact AF| exact LF| exact HI].
  - (* [comment removed for export] *)
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ft; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')|].
        destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ft; [exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.


End CeilWrap.
End MI_WAMeta2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Module MI_WCreate2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WCreate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land31_id x : 0 <= x <= 31 -> Z.land x 31 = x.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land63_id x : 0 <= x <= 63 -> Z.land x 63 = x.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma land52_id x : 0 <= x < 2 ^ 52 -> Z.land x (2 ^ 52 - 1) = x.
Proof. intros. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma one5_A (A B E : Prop) : A -> ~ B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_B (A B E : Prop) : ~ A -> B -> ~ E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.
Lemma one5_E (A B E : Prop) : ~ A -> ~ B -> E -> one5 A B False False E.
Proof. intros. unfold one5. tauto. Qed.

Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read. cbn. rewrite !lookup_empty. reflexivity. Qed.

Lemma known_noshadow st rid o : s_shadow st !! rid = None -> known st (rid, o) 0.
Proof. intros H. unfold known, SHd, get_shadow. cbn. rewrite H. cbn. apply cell_read_shadow0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agG (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agt (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st0 := hdr_havoc p st in
  let st1 := set_usage sc (usage st0 sc + cnt) st0 in
  let st2 := upd_meta m (agG sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail full_lay st sc m p cnt ai k = k (agt st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Section AGT.
Variables (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z).
Let st' := agt st sc m p cnt ai.
Let mr' := agG sc p cnt ai (MR st m).

Lemma agt_metas : s_metas st' = <[m := mr']> (s_metas st).
Proof. reflexivity. Qed.
Lemma agt_MR_m : MR st' m = mr'.
Proof. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_eq. reflexivity. Qed.
Lemma agt_MR_other x : x <> m -> MR st' x = MR st x.
Proof. intros NE. unfold MR, get_meta_rec. rewrite agt_metas, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma agt_groups : s_groups st' = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.
Lemma agt_rec3 :
  get_meta_rec (put_group p (Some m) ai (upd_meta m (agG sc p cnt ai) (set_usage sc (usage (hdr_havoc p st) sc + cnt) (hdr_havoc p st)))) m = mr'.
Proof. unfold get_meta_rec. cbn -[agG get_meta_rec]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma agt_slots s : 0 <= cnt -> 0 < get_stride mr' ->
  s_slots st' !! s =
  if (fst s =? fst p)%N && (0 <=? snd s - snd p - UNIT) && ((snd s - snd p - UNIT) mod get_stride mr' =? 0) && ((snd s - snd p - UNIT) / get_stride mr' <? cnt)
  then Some (m, (snd s - snd p - UNIT) / get_stride mr') else s_slots st !! s.
Proof. intros Hc Hs. unfold st', agt. cbn zeta. rewrite agt_rec3. rewrite lookup_add_slots by assumption. reflexivity. Qed.
Lemma agt_shadow : s_shadow st' = s_shadow (hdr_havoc p st). Proof. reflexivity. Qed.
Lemma agt_regions : s_regions st' = s_regions st. Proof. reflexivity. Qed.
Lemma agt_areas : s_areas st' = s_areas st. Proof. reflexivity. Qed.
Lemma agt_next_rid : s_next_rid st' = s_next_rid st. Proof. reflexivity. Qed.
Lemma agt_tick : s_tick st' = s_tick st. Proof. reflexivity. Qed.
Lemma agt_secret : s_secret st' = s_secret st. Proof. reflexivity. Qed.
Lemma agt_reserved : s_reserved st' = s_reserved st. Proof. reflexivity. Qed.
Lemma agt_ctx : s_ctx st' = set_usage_map (<[sc := usage st sc + cnt]> (c_usage (s_ctx st))) (s_ctx st). Proof. reflexivity. Qed.
Lemma agt_usage sc0 : usage st' sc0 = usage st sc0 + (if sc0 =? sc then cnt else 0).
Proof.
  unfold usage at 1. unfold ctx. rewrite agt_ctx. cbn -[usage]. destruct (Z.eqb_spec sc0 sc) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. unfold usage, ctx. lia.
Qed.
Lemma agt_active sc0 : active st' sc0 = active st sc0. Proof. reflexivity. Qed.
Lemma agt_get_head h : get_head st' h = get_head st h. Proof. destruct h; reflexivity. Qed.

Lemma agt_TF0 : TF0 st -> TF0 st'.
Proof. intros H. apply (TF0_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. exact H. Qed.
Lemma agt_TW P : TW st P -> TW st' P.
Proof. intros H. apply (TW_ctrl (hdr_havoc p st)); [reflexivity| reflexivity|]. apply TW_hdr_havoc. exact H. Qed.
End AGT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG_TOP.
Variables (idle0 : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (r : region) (sc cnt needed ai : Z).
Let X := mkX (m :: idle0) [] None (Some rid) None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st2 L BL LS.
Hypothesis Hr : s_regions st2 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st2 !! rid = None.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hai : 0 <= ai <= cnt - 1.
Hypothesis Hai0 : sc = 0 -> ai = cnt - 1.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF0 st2.
Hypothesis NIm : ~ In m idle0.
Let p : aptr := (rid, 0).
Let ml := Z.shiftr needed 12.
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let st3 := upd_ctx MC st2.
Let st4 := upd_meta m (m_set_maplen ml) st3.
Let st' := agt st4 sc m p cnt ai.
Let mr' := agG sc p cnt ai (m_set_maplen ml meta0).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma top_MRm : MR st2 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.

Lemma top_INV3 : INVL X st3 L BL LS.
Proof. exact (INVL_mmap_counter X st2 L BL LS INV). Qed.

Lemma top_MR4 : MR st4 m = m_set_maplen ml meta0.
Proof. unfold st4, MR. rewrite get_meta_rec_upd_same. f_equal. exact top_MRm. Qed.

Lemma top_facts :
  let size := UNIT * size_class sc in
  let stride := get_stride mr' in
  1 <= cnt <= 32 /\ ml = needed / 4096 /\ 1 <= ml <= 256 /\ UNIT + stride * cnt <= ml * 4096
  /\ (stride <= size \/ 28 <= sc) /\ (cnt - 1 = 0 -> 27 <= sc) /\ stride * cnt < 2 ^ 20 /\ 16 <= stride /\ stride mod 16 = 0
  /\ ml * 4096 = round_up_pg needed /\ 0 < needed
  /\ mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.
Proof.
  unfold ml in *. pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto ai) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml).
  { (* [comment removed for export] *)
    unfold mr', agG. cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite land52_id by lia. reflexivity. }
  assert (Es : get_stride mr' = (if (cnt - 1 =? 0) && negb (ml =? 0) then ml * 4096 - UNIT else UNIT * size_class sc)).
  { rewrite Emr. unfold get_stride. cbn. reflexivity. }
  cbn zeta. unfold ml in *.
  assert (RU : needed / 4096 * 4096 = round_up_pg needed).
  { destruct (round_up_pg_spec needed) as [A B]. pose proof (Z.div_mod needed 4096 ltac:(lia)). rewrite G2 in H.
    pose proof (Z.div_mod (round_up_pg needed) 4096 ltac:(lia)). rewrite B in H0. nia. }
  rewrite Es. repeat split; try assumption; try lia.
Qed.

Theorem ag_top_ok :
  INVL X' st' L BL LS /\ TF0 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) ai)
  /\ (forall sc0, active st' sc0 = active st2 sc0) /\ (forall h, get_head st' h = get_head st2 h)
  /\ s_tick st' = s_tick st2.
Proof.
  pose proof top_facts as TFX. cbn zeta in TFX. destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  pose proof top_INV3 as INV3. pose proof INV3 as (IR & IA & IM3 & IL & IG & IS & ISH).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite top_MR4; reflexivity).
  pose proof (created_masks ai (cnt - 1) Hai ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  assert (Sp : get_stride mr' > 0) by lia.
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st3 st' L BL LS m p ai mr' INV3 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - exact Hai0.
    - left. lia.
    - unfold tbit. repeat split; try lia; assumption.
    - intros _. rewrite <- Emr. repeat split; lia.
    - rewrite <- Emr. lia.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X'].
      destruct (Z.le_gt_cases i ai).
      + apply one5_A; [apply M7; lia| intros Hf; exact (M5 i ltac:(lia) (M7 i ltac:(lia)) Hf)| discriminate].
      + apply one5_B; [intros Ha; pose proof (M3 i ltac:(lia) Ha); lia| apply M6; lia| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - left. rewrite <- Emr. cbn [snd fst x_orph x_pend X X' p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. replace (m_maplen mr') with ml by (rewrite Emr; reflexivity).
      split; [exact F10|]. unfold cnt_of. replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity). lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - unfold st'. rewrite agt_metas. unfold st4. rewrite s_metas_upd_meta. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. fold st4. first [rewrite top_MR4; exact Emr| unfold mr'; f_equal; exact top_MR4].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st4 sc m p cnt ai s); [| lia| rewrite top_MR4; fold mr'; lia].
      rewrite top_MR4. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - cbn. repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx in Hv. cbn in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { unfold st'. apply agt_TF0. apply (TF0_ctrl st2); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'm|]. split; [unfold st'; rewrite agt_groups, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros; reflexivity|]. split; [intros h; destruct h; reflexivity| reflexivity].
Qed.
End AG_TOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_metas_id st v : v = s_metas st -> Malloc.set_metas v st = st.
Proof. destruct st; cbn; intros ->; reflexivity. Qed.

Definition hdr3_f (i : Z) : bool := (Z.land (Z.lor (Z.land i 31) 192) 255 =? i + 192) && (Z.land (i + 192) 31 =? i).
Lemma hdr3_all : forallb hdr3_f (zrange 0 32) = true. Proof. vm_compute. reflexivity. Qed.
Lemma hdr3_facts i : 0 <= i <= 31 -> Z.land (Z.lor (Z.land i 31) 192) 255 = i + 192 /\ Z.land (i + 192) 31 = i.
Proof.
  intros Hi. pose proof (forallb_zrange hdr3_f 0 32 i hdr3_all ltac:(lia) ltac:(lia)) as H. unfold hdr3_f in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Section AG_NESTED.
Variables (idle0 : list aptr) (st1 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m g bg : aptr) (aig idx sc cnt : Z).
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).
Let p : aptr := (fst bg, sstart (MR st1 g) idx).
Let X := mkX (m :: idle0) [] (Some p) None None.
Let X' := mkX idle0 [] None None (Some m).
Hypothesis INV : INVL X st1 L BL LS.
Hypothesis Hg : s_groups st1 !! bg = Some (mkGhdr (Some g) aig).
Hypothesis Hidx : 0 <= idx <= m_last_idx (MR st1 g).
Hypothesis SCg : m_sizeclass (MR st1 g) = j.
Hypothesis STR : get_stride (MR st1 g) = UNIT * size_class j.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis EMP : LS (LActive sc) = [].
Hypothesis TF : TF2 st1.
Hypothesis NIm : ~ In m idle0.
Let st2 := nest_layout st1 g idx j size cnt.
Let st3 := upd_meta m (m_set_maplen 0) st2.
Let st' := agt st3 sc m p cnt (cnt - 1).
Let mr' := agG sc p cnt (cnt - 1) meta0.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma nst_MRm : MR st1 m = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). reflexivity. Qed.
Lemma nst_hosts : hosts st1 bg g. Proof. exists aig. exact Hg. Qed.

Lemma nst_facts :
  2 <= cnt <= 32 /\ sc < j <= 23 /\ UNIT + cnt * size <= UNIT * size_class j /\ size * cnt < 2 ^ 20
  /\ 16 <= size /\ size mod 16 = 0 /\ size_class j <= 127
  /\ mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0
  /\ get_stride mr' = size.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0.
  destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  pose proof (size_class_bound sc Hsc) as SB.
  assert (Emr : mr' = mkMeta None None (Some p) (mask_upto (cnt - 1)) 0 (cnt - 1) 1 sc 0).
  { unfold mr', agG. cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
    rewrite land31_id by lia. rewrite land63_id by lia. rewrite Z.sub_diag. reflexivity. }
  assert (SJ : size_class j <= 127) by (change 127 with (size_class 23); apply size_class_le; lia).
  repeat split; try lia.
  - unfold size, UNIT. lia.
  - unfold size, UNIT. rewrite Z.mul_comm. apply Z_mod_mult.
  - exact Emr.
  - rewrite Emr. unfold get_stride. cbn -[Z.eqb size_class Z.mul]. replace (cnt - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nst_layout :
  INVL X st2 L BL LS /\ ctrl_eq st1 st2 /\ s_tick st2 = s_tick st1
  /\ known st2 (aadd p (-3)) (Z.land (Z.lor (Z.land idx 31) 192) 255)
  /\ known st2 (aadd p (-2)) (Z.land ((snd p - (snd bg + UNIT)) / UNIT) 255)
  /\ known st2 (aadd (aadd p (-2)) 1) (Z.land (Z.shiftr ((snd p - (snd bg + UNIT)) / UNIT) 8) 255)
  /\ (forall k, 0 <= k <= cnt -> known st2 (aadd p (UNIT + k * size - 4)) 0)
  /\ st2 = wrs (nl_list st1 g bg idx size cnt) st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & _ & _).
  pose proof (nest_layout_ok X st1 L BL LS g bg aig idx j size cnt INV Hg Hidx eq_refl STR N6 N5 ltac:(lia) ltac:(rewrite STR; exact N3)
                (TF2_TF X st1 L BL LS INV TF)) as (A & _ & C & D & E & F & G & H & _).
  refine (conj A (conj C (conj D (conj E (conj F (conj G (conj H _))))))). apply (nl_eq X st1 L BL LS g bg aig idx j size cnt INV Hg STR).
Qed.

Lemma nst_st3 : st3 = st2.
Proof.
  pose proof nst_layout as (INV2 & CE & _).
  unfold st3, upd_meta, put_meta. apply set_metas_id.
  assert (E : get_meta_rec st2 m = meta0) by (rewrite (get_meta_rec_ext st1 st2 m (ce_metas _ _ CE)); exact nst_MRm).
  rewrite E. change (m_set_maplen 0 meta0) with meta0. apply insert_id. rewrite (ce_metas _ _ CE). exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))).
Qed.

Theorem ag_nested_ok :
  INVL X' st' L BL LS /\ TF2 st' /\ MR st' m = mr'
  /\ s_groups st' !! p = Some (mkGhdr (Some m) (cnt - 1))
  /\ (forall sc0, active st' sc0 = active st1 sc0) /\ (forall h, get_head st' h = get_head st1 h)
  /\ s_tick st' = s_tick st1.
Proof.
  pose proof nst_facts as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & Emr & Es).
  pose proof nst_layout as (INV2 & CE & TK2 & K3 & K2 & K1 & KZ & Ewrs).
  pose proof INV as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  pose proof INV2 as (IR & IA & IM2 & IL & IG2 & IS2 & ISH).
  pose proof nst_st3 as E3.
  assert (MR2 : forall x, MR st2 x = MR st1 x) by (intros x; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (MR'm : MR st' m = mr') by (unfold st'; rewrite agt_MR_m; unfold mr'; rewrite E3, MR2, nst_MRm; reflexivity).
  pose proof (created_masks (cnt - 1) (cnt - 1) ltac:(lia) ltac:(lia)) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  rewrite Z.sub_diag in *.
  pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg)) as LI31.
  pose proof (hdr3_facts idx ltac:(lia)) as [H3a H3b].
  pose proof (sstart_res X st1 L BL LS INV bg g idx nst_hosts) as PR. fold p in PR.
  assert (P16 : snd p mod 16 = 0).
  { unfold p. cbn [snd]. unfold IB in PR. pose proof (Z.div_mod (sstart (MR st1 g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st1 g) idx) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (sstart (MR st1 g) idx) 16 ltac:(lia)). lia. }
  pose proof (hosts_gbase _ _ _ IM1 _ _ nst_hosts) as GB.
  assert (S0 : sstart (MR st1 g) idx = snd bg + UNIT + get_stride (MR st1 g) * idx) by (unfold sstart; rewrite GB; reflexivity).
  assert (Q : (snd p - snd bg - UNIT) / UNIT = size_class j * idx).
  { unfold p. cbn [snd]. rewrite S0, STR. unfold UNIT. replace (snd bg + 16 + 16 * size_class j * idx - snd bg - 16) with ((size_class j * idx) * 16) by lia. apply Z.div_mul. lia. }
  assert (Qr : 0 <= size_class j * idx < 2 ^ 16).
  { pose proof (size_class_bound j ltac:(clear - N2 Hsc; lia)) as SB.
    destruct (g_stride _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hg) ltac:(rewrite SCg; clear - N2; lia)) as (_ & _ & LT).
    rewrite STR in LT. unfold cnt_of in LT. clear - SB LT Hidx. unfold UNIT in LT. nia. }
  assert (NH : s_groups st1 !! p = None).
  { pose proof (is_part _ _ _ IS1 _ _ _ idx Hg Hidx) as P5. cbn zeta in P5. rewrite (slot_start'_eq _ _ _ IM1 _ _ _ nst_hosts) in P5. fold p in P5.
    destruct (s_groups st1 !! p) eqn:E; [| reflexivity]. exfalso. destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [congruence| reflexivity]. }
  assert (INV' : INVL X' st' L BL LS).
  { apply (INVL_create X X' st2 st' L BL LS m p (cnt - 1) mr' INV2 ltac:(left; reflexivity)).
    all: try (rewrite Emr; cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed]).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - left. lia.
    - unfold tbit. repeat split; try lia; try assumption; try (intros i Hi Hb; rewrite Z.bits_0 in Hb; discriminate).
    - intros _. rewrite <- Emr, Es. unfold size. clear - N1 N4. repeat split; lia.
    - rewrite <- Emr, Es. lia.
    - unfold UNIT. split; [| exact P16]. unfold p. cbn [snd]. pose proof (sstart0 _ _ _ IM1 _ _ nst_hosts). pose proof (sstart_mono _ _ _ IG1 _ _ 0 idx nst_hosts ltac:(lia)).
      destruct (hosts_ok _ _ _ IG1 _ _ nst_hosts) as (a0 & _ & GO). pose proof (g_align _ _ _ _ _ _ GO). unfold UNIT in *. lia.
    - left. reflexivity.
    - reflexivity.
    - intros x Hx. cbn [x_idle X X'] in Hx |- *. split; [right; exact Hx|]. intros ->. exact (NIm Hx).
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X']. apply one5_A; [apply M7; lia| rewrite Z.bits_0; discriminate| discriminate].
    - intros s Hs. discriminate.
    - intros _. exact EMP.
    - right. rewrite <- Emr. cbn [x_pend x_orph X X']. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists g, idx, bg. rewrite !MR2.
      split; [rewrite (ce_slots _ _ CE); unfold p; rewrite <- (slot_start'_eq _ _ _ IM1 _ _ idx nst_hosts); exact (is_total _ _ _ IS1 _ _ _ nst_hosts Hidx)|].
      split; [apply (proj2 (hosts_ext st1 st2 (ce_groups _ _ CE) bg g)); exact nst_hosts|].
      split; [reflexivity|]. split; [exact Hidx|]. split; [reflexivity|].
      split; [rewrite Es; unfold p; cbn [snd]; rewrite STR; unfold cnt_of; replace (m_last_idx mr') with (cnt - 1) by (rewrite Emr; reflexivity); unfold size in N3 |- *; lia|].
      split; [rewrite SCg; replace (m_sizeclass mr') with sc by (rewrite Emr; reflexivity); lia|].
      split; [rewrite STR, SCg; reflexivity|].
      split; [exists (idx + 192); split; [| split; [exact H3b| clear - Hidx LI31; lia]]; rewrite <- H3a; exact K3|].
      rewrite Q. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r. rewrite <- Q.
      replace (snd p - snd bg - UNIT) with (snd p - (snd bg + UNIT)) by lia.
      split; [exact K2|]. split; [replace (fst p, snd p - 1) with (aadd (aadd p (-2)) 1) by (unfold aadd; cbn [fst snd]; f_equal; lia); exact K1|].
      replace ((snd p - (snd bg + UNIT)) / UNIT) with (size_class j * idx) by (rewrite <- Q; f_equal; lia). exact Qr.
    - rewrite <- Emr. intros i Hi. rewrite Es. replace (fst p, snd p + UNIT + size * i - IB) with (aadd p (UNIT + i * size - 4)) by (unfold aadd, IB; f_equal; lia).
      apply KZ. unfold cnt_of in Hi. rewrite ?Emr in Hi. cbn [m_last_idx] in Hi. lia.
    - intros o v tk Ho Hc. rewrite Ewrs in Hc. rewrite wrs_cells_other in Hc.
      + rewrite TK2. exact (TF2_ghdr_old X st1 L BL LS INV p TF P16 o v tk Ho Hc).
      + unfold nl_list. rewrite map_app. intros Hin. apply in_app_iff in Hin. unfold p in Ho. cbn [snd] in Ho. destruct Hin as [Hin|Hin].
        * cbn [map fst In] in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; apply (f_equal snd) in E; unfold aadd in E; cbn [fst snd] in E; clear - E Ho N1 N5; lia.
        * apply in_zlist in Hin as (k & Hk & E). apply (f_equal snd) in E. unfold aadd in E. cbn [fst snd] in E. unfold UNIT in E.
          assert (0 <= k * size) by (apply Z.mul_nonneg_nonneg; clear - Hk N5; lia). clear - E Ho H Hk N5. lia.
    - unfold st'. rewrite agt_metas. rewrite E3. apply map_eq. intros kk. destruct (decide (kk = m)) as [->|NE].
      + rewrite !lookup_insert_eq. f_equal. rewrite MR2, nst_MRm. first [exact Emr| reflexivity].
      + rewrite !lookup_insert_ne by congruence. reflexivity.
    - unfold st'. rewrite agt_groups, E3. rewrite land31_id by lia. reflexivity.
    - intros s. unfold st'. rewrite (agt_slots st3 sc m p cnt (cnt - 1) s); [| lia| rewrite E3, MR2, nst_MRm; fold mr'; rewrite Es; lia].
      rewrite E3, MR2, nst_MRm. fold mr'. rewrite Emr. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - unfold st'. rewrite agt_shadow, E3. reflexivity.
    - unfold st'. rewrite agt_regions, E3. reflexivity.
    - unfold st'. rewrite agt_areas, E3. reflexivity.
    - unfold st'. rewrite agt_next_rid, E3. reflexivity.
    - unfold st'. rewrite agt_tick, E3. reflexivity.
    - unfold st'. rewrite agt_secret, E3. reflexivity.
    - unfold st'. rewrite agt_reserved, E3. reflexivity.
    - unfold st'. rewrite agt_ctx, E3. repeat split; reflexivity.
    - unfold st'. rewrite agt_ctx, E3. cbn [c_mmap_counter set_usage_map]. rewrite (ce_ctx _ _ CE). pose proof (ia_ctx _ IA1) as (C & _). exact C.
    - intros sc0 Hsc0. unfold st'. rewrite agt_usage, E3. replace (cnt - 1 + 1) with cnt by lia. reflexivity.
    - intros sc0 v Hv. unfold st' in Hv. rewrite agt_ctx, E3 in Hv. cbn [c_usage set_usage_map] in Hv.
      destruct (Z.eq_dec sc0 sc) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hv by congruence. rewrite (ce_ctx _ _ CE) in Hv. exact (ia_usage_keys _ IA1 sc0 v Hv). }
  split; [exact INV'|]. split.
  { (* [comment removed for export] *)
    unfold TF2. unfold st'. rewrite E3.
    apply (TW_mono _ (fun q => PS st1 q \/ In q (map fst (nl_list st1 g bg idx size cnt)))).
    2:{ apply agt_TW. rewrite Ewrs. apply TW_wrs; [| intros q Hq; right; exact Hq]. apply (TW_mono _ (PS st1)); [intros q Hq; left; exact Hq| exact TF]. }
    intros q [Hq|Hq].
    - apply (PS_mono st1); [| exact Hq]. apply geom_kept_of.
      + intros b h Hb. rewrite <- E3. fold st'. unfold st'. rewrite agt_groups, E3, (ce_groups _ _ CE).
        rewrite lookup_insert_ne; [exact Hb|]. intros ->. rewrite NH in Hb. discriminate.
      + intros b x Hx. rewrite <- E3. fold st'. rewrite (agt_MR_other st3 sc m p cnt (cnt - 1) x), E3, MR2; [reflexivity|].
        intros ->. exact (idle_not_live _ _ _ _ _ INV m ltac:(left; reflexivity) (ex_intro _ b Hx)).
    - assert (Hm' : hosts (agt st2 sc m p cnt (cnt - 1)) p m) by (exists (Z.land (cnt - 1) 31); rewrite agt_groups, lookup_insert_eq; reflexivity).
      assert (R' : MR (agt st2 sc m p cnt (cnt - 1)) m = mr') by (rewrite <- E3; exact MR'm).
      exists p, m. split; [exact Hm'|]. rewrite R'.
      unfold nl_list in Hq. rewrite map_app in Hq. apply in_app_iff in Hq. destruct Hq as [Hq|Hq].
      + cbn [map fst In app] in Hq. assert (E : fst q = fst p /\ snd p - 3 <= snd q <= snd p - 1).
        { destruct Hq as [E|[E|[E|[E|[E|[]]]]]]; subst q; unfold aadd, p; cbn [fst snd]; split; first [reflexivity| lia]. }
        destruct E as [E1 E2]. split; [symmetry; exact E1|]. right. split; [rewrite Emr; reflexivity| exact E2].
      + apply in_zlist in Hq as (k & Hk & ->). unfold aadd. cbn [fst snd]. split; [reflexivity|]. left. exists k.
        split; [unfold cnt_of; rewrite Emr; cbn [m_last_idx]; clear - Hk; lia|].
        unfold sstart. replace (gbase mr') with p by (rewrite Emr; reflexivity). rewrite Es. unfold p. cbn [snd]. unfold sstart, UNIT, IB. lia. }
  split; [exact MR'm|].
  split; [unfold st'; rewrite agt_groups, E3, lookup_insert_eq, land31_id by lia; reflexivity|].
  split; [intros sc0; unfold st'; rewrite agt_active, E3; unfold active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  split; [intros h; unfold st'; rewrite agt_get_head, E3; unfold get_head, active, ctx; rewrite (ce_ctx _ _ CE); reflexivity|].
  unfold st'. rewrite agt_tick, E3. exact TK2.
Qed.
End AG_NESTED.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_div x : 0 < x -> (x + 4095) / 4096 * 4096 = round_up_pg x.
Proof.
  intros Hx. destruct (round_up_pg_spec x) as [A B].
  pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as M1.
  pose proof (Z.div_mod (round_up_pg x) 4096 ltac:(lia)) as D2. rewrite B in D2. nia.
Qed.

Definition F63 (rid : N) (ml : Z) (mr : meta) : meta :=
  m_set_freed 0 (m_set_avail 0 (m_set_maplen ml (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))).

Section CREATE63.
Variables (st3 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (g : aptr) (rid : N) (r : region) (needed : Z).
Let X := mkX [g] [] None (Some rid) None.
Let p : aptr := (rid, 0).
Let X' := mkX [] [] (Some (rid, 16)) None None.
Hypothesis INV : INVL X st3 L BL LS.
Hypothesis Hr : s_regions st3 !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Lr : r_len r = needed.
Hypothesis NS : s_shadow st3 !! rid = None.
Hypothesis Hn : 0 < needed < 2 ^ 63.
Hypothesis TF : TF0 st3.
Let ml := (needed + 4095) / 4096.
Let st4 := upd_meta g (F63 rid ml) st3.
Let st5 := put_group p (Some g) (group_active_idx st4 p) (hdr_havoc p st4).
Let st6 := add_slots g p (get_stride (get_meta_rec st5 g)) 1 st5.
Let mr' := mkMeta None None (Some p) 0 0 0 1 63 ml.

Let IR := proj1 INV.
Let IM := proj1 (proj2 (proj2 INV)).

Lemma c63_MRg : MR st3 g = meta0.
Proof. unfold MR, get_meta_rec. rewrite (proj1 (im_idle _ _ _ IM g ltac:(left; reflexivity))). reflexivity. Qed.

Lemma c63_ml : 1 <= ml < 2 ^ 52 /\ ml * 4096 = round_up_pg needed.
Proof.
  unfold ml. split; [| apply round_up_pg_div; lia].
  split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia].
Qed.

Lemma c63_F : F63 rid ml meta0 = mr'.
Proof.
  pose proof c63_ml as [M _]. unfold F63, mr'. cbv beta iota delta [m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail m_set_maplen m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen]. cbn.
  rewrite land52_id by lia. reflexivity.
Qed.

Lemma c63_stride : get_stride mr' = ml * 4096 - UNIT.
Proof. pose proof c63_ml as [M _]. unfold get_stride, mr'. cbn -[Z.mul Z.sub Z.eqb]. replace (ml =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.

Lemma c63_nogroup : s_groups st3 !! p = None.
Proof. destruct (ir_orph _ _ _ IR rid eq_refl) as (r0 & _ & _ & NG). apply NG. reflexivity. Qed.

Lemma c63_rec5 : get_meta_rec st5 g = mr'.
Proof. unfold get_meta_rec. cbn -[F63 get_meta_rec]. rewrite lookup_insert_eq. fold (MR st3 g). rewrite c63_MRg. exact c63_F. Qed.

Theorem create63_ok :
  INVL X' st6 L BL LS /\ TF0 st6 /\ MR st6 g = mr' /\ s_groups st6 !! p = Some (mkGhdr (Some g) 0)
  /\ s_ctx st6 = s_ctx st3 /\ s_tick st6 = s_tick st3 /\ s_regions st6 = s_regions st3
  /\ get_stride mr' = ml * 4096 - UNIT /\ ml * 4096 = round_up_pg needed.
Proof.
  pose proof c63_ml as [M RU]. pose proof c63_stride as Es.
  pose proof INV as (IR0 & IA & IM0 & IL & IG & IS & ISH).
  assert (Emetas : s_metas st6 = <[g := mr']> (s_metas st3)).
  { change (s_metas st6) with (s_metas st4). unfold st4. rewrite s_metas_upd_meta. fold (MR st3 g). rewrite c63_MRg, c63_F. reflexivity. }
  assert (MR'g : MR st6 g = mr') by (unfold MR, get_meta_rec; rewrite Emetas, lookup_insert_eq; reflexivity).
  assert (GAI : group_active_idx st4 p = 0).
  { unfold group_active_idx, get_group. change (s_groups st4) with (s_groups st3). rewrite c63_nogroup. reflexivity. }
  assert (Egroups : s_groups st6 = <[p := mkGhdr (Some g) 0]> (s_groups st3)).
  { change (s_groups st6) with (s_groups st5). unfold st5. rewrite GAI. reflexivity. }
  assert (INV' : INVL X' st6 L BL LS).
  { apply (INVL_create X X' st3 st6 L BL LS g p 0 mr' INV ltac:(left; reflexivity)).
    all: cbn [m_prev m_next m_mem m_freeable m_maplen m_last_idx m_sizeclass m_avail m_freed mr'].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - lia.
    - lia.
    - lia.
    - intros _. reflexivity.
    - right. lia.
    - unfold tbit. repeat split; try lia; intros i Hi Hb; rewrite Z.testbit_0_l in Hb; discriminate.
    - lia.
    - fold mr'. rewrite Es. unfold UNIT. split; [lia|]. replace (ml * 4096 - 16) with ((ml * 256 - 1) * 16) by lia. apply Z_mod_mult.
    - cbn. unfold UNIT. split; [lia| reflexivity].
    - right. split; reflexivity.
    - reflexivity.
    - intros x Hx. destruct Hx.
    - reflexivity.
    - reflexivity.
    - intros i Hi. unfold tbit. cbn [x_pend X' fst snd p]. apply one5_E; [rewrite Z.testbit_0_l; discriminate| rewrite Z.testbit_0_l; discriminate|].
      assert (i = 0) by lia. subst i. rewrite Z.mul_0_r. reflexivity.
    - intros s Hs. cbn [x_pend X'] in Hs. inversion Hs. subst s. exists 0. split; [lia|]. cbn [fst snd p]. rewrite Z.mul_0_r. reflexivity.
    - intros H. lia.
    - left. cbn [x_orph x_pend X X' fst snd p]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists r. split; [exact Hr|]. split; [exact Kr|]. rewrite Lr. split; [exact RU|]. fold mr'. rewrite Es. unfold UNIT. lia.
    - intros i Hi. apply known_noshadow. exact NS.
    - intros o v tk Ho Hc. exfalso. unfold get_shadow in Hc. cbn [fst p] in Hc. rewrite NS in Hc. cbn in Hc. rewrite lookup_empty in Hc. discriminate.
    - exact Emetas.
    - exact Egroups.
    - intros s. unfold st6. rewrite c63_rec5. rewrite lookup_add_slots; [| lia| rewrite Es; unfold UNIT; lia]. fold mr'. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - repeat split; reflexivity.
    - pose proof (ia_ctx _ IA) as (C & _). exact C.
    - intros sc0 Hsc0. replace (sc0 =? 63) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r. reflexivity.
    - intros sc0 v Hv. exact (ia_usage_keys _ IA sc0 v Hv). }
  split; [exact INV'|]. split.
  { apply (TF0_ctrl (hdr_havoc p st4)); [reflexivity| reflexivity|]. apply TF0_hdr_havoc. apply (TF0_ctrl st3); [reflexivity| reflexivity| exact TF]. }
  split; [exact MR'g|]. split; [rewrite Egroups, lookup_insert_eq; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Es| exact RU].
Qed.
End CREATE63.


End CeilWrap.
End MI_WCreate2.

(* [comment removed for export] *)
Module MI_WNtf2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WKill OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition decodes (T : Type) (st : mstate) (p pm : aptr) (ip : Z) : Prop :=
  s_slots st !! p = Some (pm, ip) /\ forall (k : aptr -> Z -> M T) (bail : M T), dec_hdr st p k bail = k pm ip.
Definition DEC_OK (T : Type) (dec : decoder T) : Prop :=
  forall st p pm ip (k : aptr -> Z -> M T) (bail : M T), decodes T st p pm ip -> dec st p k bail = k pm ip.
Lemma dec_hdr_ok T : DEC_OK T dec_hdr.
Proof. intros st p pm ip k bail [_ H]. apply H. Qed.
Lemma dec_slots_ok T : DEC_OK T dec_slots.
Proof. intros st p pm ip k bail [H _]. unfold dec_slots. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Definition NTF_AT (T : Type) (f : nat) : Prop :=
  forall (dec1 dec2 : decoder T), DEC_OK T dec1 -> DEC_OK T dec2 ->
  forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec1 f st g i k bail = k st' mi /\ nontrivial_free dec2 f st g i k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

Lemma rem_notin g l : ~ In g l -> rem g l = l.
Proof.
  induction l as [|x l IH]; cbn; [reflexivity|]. intros H.
  unfold rem. cbn. destruct (aptr_eq_dec g x) as [->|NE]; [exfalso; apply H; left; reflexivity|].
  cbn. f_equal. apply IH. tauto.
Qed.

Lemma regions_fm_st st g : s_regions (fm_st st g) = s_regions st.
Proof. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 st)) as (E & _). rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma INVL_free_zombie idle zomb pend orph st L BL LS g :
  INVL (mkX idle (g :: zomb) pend orph None) st L BL LS ->
  ~ In g zomb -> ~ In g idle ->
  exists LS', INVL (mkX idle zomb pend orph None) (fm_st st g) L BL LS'.
Proof.
  intros INV NZ NI.
  pose proof (INVL_unzombie _ st L BL LS g INV ltac:(left; reflexivity)) as INV1. cbn in INV1.
  unfold xzomb in INV1. cbn in INV1.
  unfold rem in INV1. cbn in INV1. destruct (aptr_eq_dec g g) as [_|NE]; [| congruence]. cbn in INV1.
  fold (rem g zomb) in INV1. rewrite (rem_notin g zomb NZ) in INV1.
  eexists. unfold fm_st.
  apply (INVL_queue _ (put_meta g meta0 st) L BL LS g LFree INV1).
  - unfold MR. rewrite get_meta_rec_put_same. reflexivity.
  - rewrite lookup_metas_put, aptr_eqb_refl. discriminate.
  - cbn. split; [unfold MR; rewrite get_meta_rec_put_same; reflexivity|]. split; [exact NI| exact NZ].
Qed.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_AT T f.
Variables (dec1 dec2 : decoder T).
Hypothesis D1 : DEC_OK T dec1.
Hypothesis D2 : DEC_OK T dec2.
Variables (idle zomb : list aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Variables (k : mstate -> mapinfo -> M T) (bail : M T).
Let X := mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis NL : m_next (MR st g) = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Hypothesis FUEL : 49 - m_sizeclass (MR st g) <= Z.of_nat (S f).

Theorem free_group_ok :
  exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st g k bail = k st' mi /\
    free_group T dec2 (nontrivial_free dec2 f) st g k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (mkX idle zomb None None None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
    end.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
            (del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
  assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
  { intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
  unfold free_group. fold (MR st g).
  set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
  rewrite (hosts_mem _ _ _ IM _ _ Hgh).
  set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
  pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
  cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
  pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
  - (* [comment removed for export] *)
    destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
                (fun m idx => nontrivial_free dec1 f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
      as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
    fold stk in EQ, Hs', Hpm'.
    assert (DQ : decodes T stk bg pm ip).
    { split; [exact Hs'|]. intros k' bail'.
      destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
      fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
    rewrite (D1 stk bg pm ip _ bail DQ), (D2 stk bg pm ip _ bail DQ).
    destruct (IHf dec1 dec2 D1 D2 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
                  (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
      as (st3 & mi & LS3 & EQ3 & EQ3b & REG3 & POST3).
    + rewrite KMR. exact Hip.
    + cbn. rewrite KMR, Ep. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + rewrite KMR. lia.
    + rewrite EQ3, EQ3b. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
      destruct mi as [[base len]|].
      * destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
        destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. exists r.
        split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
      * cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]| exact INV4].
  - (* [comment removed for export] *)
    rewrite !free_meta_eq.
    destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
    fold stk in Hr.
    assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
    { apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
    destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
    assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    eexists _, _, LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, RS, FMSEC, RSS.
    split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. cbn. exists r. cbn.
    split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ntf_unfold {T} dec f st g i (k : mstate -> mapinfo -> M T) bail :
  nontrivial_free dec (S f) st g i k bail =
    (if (Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g then
      match m_next (MR st g) with
      | Some _ =>
        guard 50 (m_sizeclass (MR st g) <? 48) (
          match optr_eqb (active st (m_sizeclass (MR st g))) (Some g), active (dequeue (LActive (m_sizeclass (MR st g))) g st) (m_sizeclass (MR st g)) with
          | true, Some a => activate_group a (dequeue (LActive (m_sizeclass (MR st g))) g st)
                              (fun st2 _ => free_group T dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group T dec (nontrivial_free dec f) (dequeue (LActive (m_sizeclass (MR st g))) g st) g k bail
          end) bail
      | None => free_group T dec (nontrivial_free dec f) st g k bail
      end
    else if Z.lor (m_freed (MR st g)) (m_avail (MR st g)) =? 0 then
      guard 51 (m_sizeclass (MR st g) <? 48) (
        if negb (optr_eqb (active st (m_sizeclass (MR st g))) (Some g))
        then queue (LActive (m_sizeclass (MR st g))) g st (fun st' => k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st') None) bail
        else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None) bail
    else
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma data_same r r' i : data_of r' = data_of r ->
  sstart r' i = sstart r i /\ m_last_idx r' = m_last_idx r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r /\ m_mem r' = m_mem r.
Proof.
  intros D. pose proof (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold sstart, gbase. rewrite (get_stride_data _ _ D), E1. repeat split; auto.
Qed.

Lemma head_of_eq_app (l1 l2 : list aptr) g : NoDup (l1 ++ g :: l2) -> head_of (l1 ++ g :: l2) = Some g -> l1 = [].
Proof.
  intros ND H. destruct l1 as [|a l1']; [reflexivity|]. cbn in H. inversion H. subst a. exfalso.
  cbn in ND. apply NoDup_cons in ND as [N _]. apply N. apply elem_of_list_In || apply list_elem_of_In. apply in_app_iff. right. left. reflexivity.
Qed.

Theorem ntf_all T : forall f, NTF_AT T f.
Proof.
  induction f as [|f IH]; intros dec1 dec2 D1 D2 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
  destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof Hgh as [ai Hg].
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi. cbn [x_pend] in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false) by (destruct (tbit (m_avail (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  assert (NB : tbit (m_freed (MR st g)) i = false) by (destruct (tbit (m_freed (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  clear Pi.
  rewrite !ntf_unfold.
  set (mask := Z.lor (m_freed (MR st g)) (m_avail (MR st g))).
  assert (MN : 0 <= mask) by (apply Z.lor_nonneg; auto).
  assert (MI : Z.testbit mask i = false) by (unfold mask; rewrite Z.lor_spec; unfold tbit in NA, NB; rewrite NA, NB; reflexivity).
  assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; auto; lia).
  (* [comment removed for export] *)
  assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
  { intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
    destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
    rewrite Bool.orb_true_r in OK. discriminate. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
  - (* [comment removed for export] *)
    apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
    assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
    { intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
      rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
      unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
    pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
    (* [comment removed for export] *)
    assert (FGT : forall st2 LS2,
      INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
      s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
      exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st2 g k bail = k st' mi /\
        free_group T dec2 (nontrivial_free dec2 f) st2 g k bail = k st' mi /\
        (s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2) /\
        match mi with
        | None => INVL (mkX idle zomb None None None) st' L BL LS'
        | Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
            /\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
        end).
    { intros st2 LS2 INV2 HG2 DD2 NL2. destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
      rewrite <- Es in INV2.
      apply (free_group_ok T f IH dec1 dec2 D1 D2 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
      - rewrite HG2. exact Hg.
      - exact NL2.
      - rewrite El. exact Hi.
      - rewrite El, Ea, Ef. exact ALL.
      - rewrite Esc. exact F2. }
    destruct (m_next (MR st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
      destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
      destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
      rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
      destruct (in_split _ _ Hin) as (l1 & l2 & HL).
      pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
      assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
      { apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
      set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
      destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _). fold st1 in G1, RG1, SE1.
      pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
      assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
      assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
      { pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
      destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
      * (* [comment removed for export] *)
        destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
        assert (El1 : l1 = []).
        { apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
        subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
        assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
        assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
        destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
        pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
        pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
        destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
        assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
        assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
        assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
        { rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
        rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
        pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
        set (st2 := upd_meta a _ st1) in INV2 |- *.
        destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & EQb & REG & POST).
        -- unfold st2. cbn. exact G1.
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
        -- exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|].
           split; [destruct REG as [RA RB]; rewrite RA, RB; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| etransitivity; [| exact SE1]; reflexivity]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
      * destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
    + (* [comment removed for export] *)
      destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & POST). exists st', mi, LS'. split; [exact EQ| exact POST].
  - (* [comment removed for export] *)
    assert (OKF : m_last_idx (MR st g) = 0 -> okay_to_free st g = false).
    { intros L0. rewrite L0 in C1. assert (i = 0) by lia. subst i.
      assert (mask = 0).
      { apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0. unfold mask. rewrite Z.lor_spec.
        destruct (Z.eq_dec j 0) as [->|NE]; [unfold tbit in NA, NB; rewrite NA, NB; reflexivity|].
        destruct (Z.testbit (m_freed (MR st g)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|].
        destruct (Z.testbit (m_avail (MR st g)) j) eqn:EA; [pose proof (M3 j Hj EA); lia|]. reflexivity. }
      rewrite H in C1. cbn in C1. exact C1. }
    assert (C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
    { intros Hsc. destruct (Z.eq_dec (m_last_idx (MR st g)) 0) as [L0|L0]; [exact (NU (OKF L0) Hsc)|].
      unfold get_stride. destruct (Z.eqb_spec (m_last_idx (MR st g)) 0); [lia|]. cbn. lia. }
    destruct (Z.eqb_spec mask 0) as [MZ|MNZ].
    + (* [comment removed for export] *)
      assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
      { destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
        rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
        cbn in OKF. discriminate (OKF L0). }
      rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
      destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
      * (* [comment removed for export] *)
        eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
        apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
        -- intros _ sc _ _. exact AZ.
        -- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
        -- exact C3.
      * (* [comment removed for export] *)
        assert (NL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
          assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
          destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
          destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
          apply NHD. rewrite <- Esc at 1 || idtac.
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
          rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
        assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
        rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
        pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
        pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
        cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(repeat split; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
        set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
        set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
        destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _). fold stq in Gq, RGq, SEq.
        pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
        destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
        assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
        { apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
          - rewrite Gq. exact Hg.
          - rewrite El. exact Hi.
          - cbn. rewrite Es. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
        eexists _, None, LSq. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; rewrite RGq, SEq; split; reflexivity|]. cbn.
        apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
        intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
        assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
        split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
        split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
        intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
        replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
        rewrite (get_stride_data _ _ Dq) in LT. lia.
    + (* [comment removed for export] *)
      eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|]. cbn.
      apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
      * intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
      * intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
        -- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
        -- exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc (fun H => lists_notin st LS (old_lists _ _ _ _ _ INV) g NX _ (proj2 (In_nth _ _ g H) ))) || idtac.
           assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
           destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
      * exact C3.
Qed.

Theorem ntf_spec : NTF_SPEC.
Proof.
  intros T f X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_hdr (dec_hdr_ok T) (dec_hdr_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ & _ & _ & POST).
  exists st', mi, LS'. split; [exact EQ| exact POST].
Qed.

(* [comment removed for export] *)
Theorem ntf_slots_agree T f X st L BL LS g bg i (k : mstate -> mapinfo -> M T) bail :
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  nontrivial_free dec_slots f st g i k bail = nontrivial_free dec_hdr f st g i k bail.
Proof.
  intros INV Hg Hi HP HF HO F1 F2.
  destruct (ntf_all T f dec_hdr dec_slots (dec_hdr_ok T) (dec_slots_ok T) X st L BL LS g bg i k bail INV Hg Hi HP HF HO F1 F2) as (st' & mi & LS' & EQ1 & EQ2 & _).
  rewrite EQ1, EQ2. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem ntf_spec2 T f : NTF_AT T f.
Proof. apply ntf_all. Qed.

(* [comment removed for export] *)
Theorem free_INVL_closed st L BL LS c off n :
  INVL x0 st L BL LS -> In ((c, off), n) BL ->
  ftree L (free st (Some (aadd c (UNIT * off))))
        (fun L' st' => exists LS', INVL x0 st' L' (bl_remove c BL) LS').
Proof. exact (free_INVL ntf_spec st L BL LS c off n). Qed.


End CeilWrap.
End MI_WNtf2.

(* [comment removed for export] *)
Module MI_WTry.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_Bits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WKill OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WNtf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma one5_A_to_E (A B C D E A' E' : Prop) : A -> ~ A' -> E' -> one5 A B C D E -> one5 A' B C D E'.
Proof. unfold one5. tauto. Qed.

Section TAFIN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m bm : aptr) (ai : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hm : s_groups st !! bm = Some (mkGhdr (Some m) ai).
Hypothesis HEAD : head_of (LS (LActive (m_sizeclass (MR st m)))) = Some m.
Let mask := m_avail (MR st m).
Hypothesis MNZ : mask <> 0.
Let first := lowbit mask.
Let idx := ctz32 first.
Let st' := upd_meta m (m_set_avail (mask - first)) st.

Lemma tafin_listed : In m (LS (LActive (m_sizeclass (MR st m)))).
Proof. destruct (LS (LActive (m_sizeclass (MR st m)))); cbn in HEAD; [discriminate|]. inversion HEAD. left. reflexivity. Qed.

Theorem ta_fin_ok :
  INVL (xpend X (Some (fst bm, sstart (MR st m) idx))) st' L BL LS
  /\ 0 <= idx <= m_last_idx (MR st m) /\ first <> 0 /\ 0 <= first
  /\ UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m).
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (Hmh : hosts st bm m) by (exists ai; exact Hm).
  assert (MPOS : 0 < mask) by (unfold mask in *; lia).
  destruct (lowbit_idiom mask MPOS) as (k0 & K0 & EL & EC & TB & A0 & TA).
  assert (Eidx : idx = k0) by (unfold idx, first; exact EC).
  assert (Hk0 : k0 <= ai) by (apply M3; [exact K0| exact TB]).
  assert (NU : UNIT * size_class (m_sizeclass (MR st m)) <= get_stride (MR st m)).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hsc _]|(E63 & _)].
    - destruct (Z.lt_ge_cases (get_stride (MR st m)) (UNIT * size_class (m_sizeclass (MR st m)))) as [LT|GE]; [| exact GE].
      exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite HF; discriminate) ltac:(lia) LT) as [A _]. unfold mask in MNZ. exact (MNZ A).
    - rewrite E63. change (size_class 63) with 0. pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _]. unfold UNIT in *. lia. }
  assert (Ef : st' = upd_meta m (fun r => m_set_avail (mask - first) (m_set_freed (m_freed (MR st m)) r)) st).
  { unfold st', upd_meta, MR. destruct (get_meta_rec st m); reflexivity. }
  rewrite Ef.
  assert (FNZ : first <> 0 /\ 0 <= first) by (unfold first; rewrite EL; clear -K0; pose proof (Z.pow_pos_nonneg 2 k0); split; [lia| apply Z.pow_nonneg; lia]).
  rewrite Eidx.
  pose proof (stride_ge _ _ _ IG _ _ Hmh) as [SG _].
  split; [| split; [clear -K0 Hk0 AI; lia| split; [exact (proj1 FNZ)| split; [exact (proj2 FNZ)| exact NU]]]]. replace X with (mkX (x_idle X) (x_zomb X) (x_pend X) (x_orph X) (x_fresh X)) at 1 by (destruct X; reflexivity).
  apply (INVL_mask_change X st L BL LS m bm ai (mask - first) (m_freed (MR st m)) (Some (fst bm, sstart (MR st m) k0)) INV Hm).
  - unfold first. split; [exact A0|]. split; [exact M2|]. split; [| split; [exact M4| split; [| exact M6]]].
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M3 i Hi H).
    + intros i Hi. unfold tbit. rewrite TA by exact Hi. rewrite Bool.andb_true_iff. intros [H _]. exact (M5 i Hi H).
  - intros j Hj. cbn zeta. unfold first, tbit. rewrite TA by (clear -Hj; lia).
    pose proof (is_part _ _ _ IS _ _ _ j Hm Hj) as P. cbn zeta in P. rewrite HP in P. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh) in P |- *.
    unfold tbit in P. destruct (Z.eqb_spec k0 j) as [<-|NE].
    + eapply one5_A_to_E; [exact TB| rewrite TB; cbn; discriminate| reflexivity| exact P].
    + rewrite Bool.andb_true_r. eapply one5_iff; [reflexivity| reflexivity| reflexivity| reflexivity| | exact P].
      split; [discriminate|]. intros E. exfalso. inversion E.
      destruct (Z.lt_total k0 j) as [LT|[EQ|LT]]; [| lia|].
      * pose proof (sstart_lt _ _ _ IG _ _ k0 j Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
      * pose proof (sstart_lt _ _ _ IG _ _ j k0 Hmh LT) as SL. clear -SL SG H0. unfold UNIT in *. lia.
  - right. split; [rewrite HP; discriminate|]. intros s Hs. inversion Hs. subst s. exists k0. split; [clear -K0 Hk0 AI; lia|]. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hmh). reflexivity.
  - intros _ sc Hin Hnh. exfalso. destruct (il_active _ _ IL sc m Hin) as (_ & _ & Esc). subst sc. exact (Hnh (eq_sym HEAD)).
  - intros _ _ NI. exfalso. apply NI. eexists. exact tafin_listed.
  - intros _ Hsc LT. exfalso. clear -LT NU. lia.
Qed.
End TAFIN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SETAI.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (m b : aptr) (ai ai' : Z).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hm : s_groups st !! b = Some (mkGhdr (Some m) ai).
Hypothesis Hai' : ai <= ai' <= m_last_idx (MR st m).
Hypothesis AV : forall i, 0 <= i -> tbit (m_avail (MR st m)) i = true -> i <= ai'.
Hypothesis LISTED : ai' < m_last_idx (MR st m) -> In m (LS (LActive (m_sizeclass (MR st m)))).
Let st' := Malloc.set_groups (<[b := mkGhdr (Some m) ai']> (s_groups st)) st.

Lemma sa_lookup bb : s_groups st' !! bb = if aptr_eqb bb b then Some (mkGhdr (Some m) ai') else s_groups st !! bb.
Proof.
  unfold st'. cbn. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity.
Qed.
Lemma sa_hosts bb x : hosts st' bb x <-> hosts st bb x.
Proof.
  unfold hosts. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| tauto].
  split; intros [a H]; [rewrite Hm; inversion H; subst; eexists; reflexivity| rewrite Hm in H; inversion H; subst; eexists; reflexivity].
Qed.
Lemma sa_live x : live_group st' x <-> live_group st x.
Proof. unfold live_group. split; intros [bb H]; exists bb; apply sa_hosts; exact H. Qed.

Theorem INVL_set_ai : INVL X st' L BL LS.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  assert (GNE : forall bb h, s_groups st' !! bb = Some h -> (bb = b /\ h = mkGhdr (Some m) ai') \/ (bb <> b /\ s_groups st !! bb = Some h)).
  { intros bb h. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [intros H; inversion H; auto| auto]. }
  assert (GN : forall bb, s_groups st' !! bb <> None <-> s_groups st !! bb <> None).
  { intros bb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [rewrite Hm; split; discriminate| tauto]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; try assumption.
    intros rid Ho. destruct (ir_orph rid Ho) as (r & Hr & K & NG). exists r. split; [exact Hr|]. split; [exact K|].
    intros bb Hbb. rewrite sa_lookup. destruct (aptr_eqb_spec bb b) as [->|NE]; [| exact (NG bb Hbb)]. specialize (NG b Hbb). rewrite Hm in NG. discriminate.
  - destruct IA; constructor; try assumption.
    intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). unfold gcnt.
    change (s_groups st') with (<[b:=mkGhdr (Some m) ai']> (s_groups st)).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (s_groups st) b _ Hm))).
    rewrite <- (zsum_perm _ _ (Permutation_map _ (map_to_list_delete (<[b:=mkGhdr (Some m) ai']> (s_groups st)) b (mkGhdr (Some m) ai') ltac:(apply lookup_insert_eq)))).
    cbn [map zsum fold_right snd g_meta]. rewrite delete_insert_eq. reflexivity.
  - destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; try assumption.
    + intros x bb Hx. destruct (Q2 x bb Hx) as [H|H]; [left; apply sa_hosts; exact H| right; exact H].
    + intros bb h Hbb. apply GNE in Hbb as [[-> ->]|[NE Hbb]]; [| exact (Q3 bb h Hbb)].
      exists m. cbn [g_meta g_active_idx]. split; [reflexivity|]. split; [exact (hosts_mem _ _ _ (mkIM _ _ _ Q1 Q2 Q3 Q4 Q5) _ _ (ex_intro _ ai Hm))| change (MR st' m) with (MR st m); lia].
    + intros z Hz. destruct (Q5 z Hz) as (A1 & A2 & A3 & bz & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      exists bz. split; [exact A4|]. rewrite sa_lookup. destruct (aptr_eqb_spec bz b) as [->|NE]; [rewrite Hm in A5; discriminate| exact A5].
  - destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. apply (dll_ext_metas st st' eq_refl). apply L2.
    + intros sc x Hx. destruct (L7 sc x Hx) as (B1 & B2 & B3). split; [exact B1|]. split; [apply sa_live; exact B2| exact B3].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor.
    + intros x bb aix Hbb. apply GNE in Hbb as [[-> E]|[NE Hbb]].
      * inversion E. subst x aix. destruct GO; constructor; change (MR st') with (MR st); try assumption.
        -- lia.
        -- destruct g_masks as (W1 & W2 & W3 & W4 & W5 & W6). split; [exact W1|]. split; [exact W2|]. split; [exact AV|]. split; [exact W4|]. split; [exact W5|].
           intros i Hi. apply W6. lia.
        -- intros NF Hlt. apply LISTED. exact Hlt.
        -- intros Hsc0. pose proof (g_full0 Hsc0). lia.
      * apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto| exact (G1 x bb aix Hbb)].
    + intros bb aix Hbb. apply GNE in Hbb as [[_ E]|[NE Hbb]]; [discriminate| exact (G2 bb aix Hbb)].
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2 P1 P2 Esc. change (MR st') with (MR st) in P1, P2, Esc.
      apply GNE in H1 as [[-> E1]|[N1 H1]]; apply GNE in H2 as [[-> E2]|[N2 H2]].
      * inversion E1. inversion E2. subst. reflexivity.
      * inversion E1. subst m1 ai1. eapply G3; [exact Hm| exact H2| lia| exact P2| exact Esc].
      * inversion E2. subst m2 ai2. eapply G3; [exact H1| exact Hm| exact P1| lia| exact Esc].
      * eapply G3; eassumption.
    + intros rid r Hr K Ho. destruct (G4 rid r Hr K Ho) as (x & Hx & Hml). exists x. split; [apply sa_hosts; exact Hx| exact Hml].
    + intros bb h Hbb. apply GNE in Hbb as [[-> _]|[NE Hbb]]; [exact (G5 _ _ Hm)| exact (G5 bb h Hbb)].
  - destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s x i Hs. destruct (S1 s x i Hs) as (B1 & B2 & B3). split; [apply sa_live; exact B1| auto].
    + intros bb x i Hbb Hi. apply (S2 bb); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x aix i Hbb Hi. cbn zeta. change (MR st') with (MR st) in Hi |- *.
      eapply one5_iff; [reflexivity| reflexivity| reflexivity| apply iff_sym; apply GN| reflexivity|].
      apply GNE in Hbb as [[-> E]|[NE Hbb]]; [inversion E; subst x aix; exact (S3 b m ai i Hm Hi)| exact (S3 bb x aix i Hbb Hi)].
  - destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros bb x i Hbb Hi. apply (D3 bb x i); [apply sa_hosts; exact Hbb| exact Hi].
    + intros bb x o Hbb Ho. apply (D4 bb x o); [apply sa_hosts; exact Hbb| exact Ho].
    + intros bb x p i Hbb Hml Hs. apply (D5 bb x p i); [apply sa_hosts; exact Hbb| exact Hml| exact Hs].
Qed.
End SETAI.

(* [comment removed for export] *)
Lemma span_loop_ge f : forall cnt span size, cnt <= span_loop f cnt span size.
Proof. induction f as [|f IH]; intros; cbn; [lia|]. destruct (_ <? _); [| lia]. pose proof (IH (cnt + 1) (span + size) size). lia. Qed.


End CeilWrap.
End MI_WTry.

(* [comment removed for export] *)
Module MI_WTry2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_Bits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Ext2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WKill OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WNtf MI_WNtf2 MI_WTry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Record TA_frame (st st1 : mstate) (sc : Z) : Prop := mkTAF {
  taf_regions : s_regions st1 = s_regions st;
  taf_shadow : s_shadow st1 = s_shadow st;
  taf_tick : s_tick st1 = s_tick st;
  taf_slots : s_slots st1 = s_slots st;
  taf_areas : s_areas st1 = s_areas st;
  taf_next_rid : s_next_rid st1 = s_next_rid st;
  taf_heads : forall h, h <> LActive sc -> get_head st1 h = get_head st h;
  taf_usage : forall sc', usage st1 sc' = usage st sc';
  taf_mc : c_mmap_counter (s_ctx st1) = c_mmap_counter (s_ctx st);
  taf_ssec : s_secret st1 = s_secret st;
  taf_secret : c_secret (s_ctx st1) = c_secret (s_ctx st) /\ c_init_done (s_ctx st1) = c_init_done (s_ctx st)
}.
Lemma taf_refl st sc : TA_frame st st sc. Proof. constructor; auto. Qed.
Lemma taf_trans a b c sc : TA_frame a b sc -> TA_frame b c sc -> TA_frame a c sc.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A12 [A10 A11]] [B1 B2 B3 B4 B5 B6 B7 B8 B9 B12 [B10 B11]]; constructor; try congruence.
  all: try (intros h Hh; rewrite (B7 h Hh); apply A7; exact Hh).
  all: try (intros sc'; rewrite (B8 sc'); apply A8).
  all: split; congruence.
Qed.
Lemma taf_upd_meta st m f sc : TA_frame st (upd_meta m f st) sc.
Proof. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_set_active st sc v : TA_frame st (set_active sc v st) sc.
Proof.
  constructor; auto; try (intros h Hh; change (set_active sc v st) with (set_head (LActive sc) v st); apply get_head_set_head_other; exact Hh).
Qed.
Lemma taf_decay st sc sc0 : TA_frame st (decay_bounces sc0 st) sc.
Proof. unfold decay_bounces. destruct (sc_in_seq_range _ && _); [| apply taf_refl]. constructor; auto; try (intros h _; destruct h; reflexivity). Qed.
Lemma taf_dequeue st sc m : TA_frame st (dequeue (LActive sc) m st) sc.
Proof.
  destruct (dequeue_frame (LActive sc) m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). destruct FC.
  constructor; auto.
  all: try (intros h Hh; rewrite dequeue_head; destruct (decide (h = LActive sc)); [congruence| reflexivity]).
  all: try (intros sc'; unfold usage, ctx; rewrite cb_usage; reflexivity).
  all: try (split; assumption).
Qed.

(* [comment removed for export] *)
Section HEADFACTS.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis HA : active st sc = Some m.
Lemma hd_list : exists rest, LS (LActive sc) = m :: rest.
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as H. change (get_head st (LActive sc)) with (active st sc) in H. rewrite HA in H.
  destruct (LS (LActive sc)) as [|a rest]; cbn in H; [discriminate|]. inversion H. exists rest. reflexivity.
Qed.
Lemma hd_in : In m (LS (LActive sc)).
Proof. destruct hd_list as [rest ->]. left. reflexivity. Qed.
Lemma hd_facts : 0 <= sc < 48 /\ m_sizeclass (MR st m) = sc /\ exists b ai, s_groups st !! b = Some (mkGhdr (Some m) ai).
Proof.
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m hd_in) as (A & [b [ai Hb]] & C). split; [exact A|]. split; [exact C|]. exists b, ai. exact Hb.
Qed.
Lemma hd_head : head_of (LS (LActive sc)) = Some m.
Proof. destruct hd_list as [rest ->]. reflexivity. Qed.
Lemma hd_next : exists mn, m_next (MR st m) = Some mn /\ In mn (LS (LActive sc)).
Proof.
  destruct (lists_next_in st LS (old_lists _ _ _ _ _ INV) (LActive sc) m hd_in) as (y & Hy & E & _). exists y. auto.
Qed.
End HEADFACTS.

(* [comment removed for export] *)
Definition GOODH (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (sc : Z) (m : aptr) : Prop :=
  INVL X st L BL LS /\ active st sc = Some m /\ m_avail (MR st m) = 0 /\ m_freed (MR st m) <> 0.

Section STEPS.
Variables (X : extras) (L : mled) (BL : list blk) (sc : Z).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

(* [comment removed for export] *)
Lemma rotate_ok st LS m mn :
  GOODH X st L BL LS sc m -> m_next (MR st m) = Some mn ->
  exists LS', GOODH X (set_active sc (Some mn) st) L BL LS' sc mn.
Proof.
  intros (INV & HA & AV & FR) Hn.
  destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  assert (INV' : INVL X (set_head (LActive sc) (Some mn) st) L BL (fupd LS (LActive sc) (rest ++ [m]))).
  { apply (INVL_rotate X st L BL LS sc m mn rest INV HL Hn). intros _ _. auto. }
  exists (fupd LS (LActive sc) (rest ++ [m])). split; [exact INV'|].
  split; [unfold active, set_active, ctx; cbn; rewrite lookup_insert_eq; reflexivity|].
  change (MR (set_active sc (Some mn) st) mn) with (MR st mn).
  pose proof (next_listed X st L BL LS INV (LActive sc) m mn (hd_in X st L BL LS sc m INV HA) Hn) as Hin.
  destruct (aptr_eq_dec mn m) as [->|NE]; [auto|].
  destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc mn Hin) as (_ & [bb [aa Hbb]] & _).
  apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
  rewrite (hd_head X st L BL LS sc m INV HA). congruence.
Qed.

(* [comment removed for export] *)
Lemma dequeue_exhausted_ok st LS m :
  INVL X st L BL LS -> active st sc = Some m -> m_avail (MR st m) = 0 -> m_freed (MR st m) = 0 ->
  exists LS' rest, INVL X (dequeue (LActive sc) m st) L BL LS' /\ LS (LActive sc) = m :: rest
    /\ active (dequeue (LActive sc) m st) sc = head_of rest
    /\ (forall m1, head_of rest = Some m1 -> m_avail (MR st m1) = 0 /\ m_freed (MR st m1) <> 0).
Proof.
  intros INV HA AV FR. destruct (hd_list X st L BL LS sc m INV HA) as [rest HL].
  destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & b & ai & Hb).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  pose proof (INVL_dequeue X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)) as INV1.
  assert (INV2 : INVL (xfresh (xfresh X (Some m)) None) (dequeue (LActive sc) m st) L BL (fupd LS (LActive sc) ([] ++ rest))).
  { apply (INVL_clear_fresh _ _ L BL _ m INV1 eq_refl). intros bb aix Hbb.
    destruct (dequeue_frame (LActive sc) m st) as (_ & _ & _ & _ & G5 & _). rewrite G5 in Hbb.
    pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ (ex_intro _ aix Hbb) (ex_intro _ ai Hb)) as ->. rewrite Hb in Hbb. inversion Hbb. subst aix.
    pose proof (dequeue_data (LActive sc) m st m) as D. destruct (data_same _ _ 0 D) as (_ & El & Ea & Ef & Es & _).
    rewrite El, Ea, Ef, Es. split; [| split; [intros; auto| split; [| intros; auto]]].
    - intros Hlt. exfalso. pose proof (g_masks _ _ _ _ _ _ GO) as (_ & _ & _ & _ & _ & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
      specialize (M6 (m_last_idx (MR st m)) ltac:(lia)). unfold tbit in M6. rewrite FR, Z.bits_0 in M6. discriminate.
    - intros sc0 Hin. exfalso. cbn in Hin.
      apply (m_out X (xfresh X (Some m)) st L BL LS m (LActive sc) [] rest INV ltac:(rewrite HL; reflexivity) ltac:(left; exists sc; auto)). exists (LActive sc0). exact Hin. }
  replace (xfresh (xfresh X (Some m)) None) with X in INV2 by (destruct X; cbn in HF |- *; subst; reflexivity).
  exists (fupd LS (LActive sc) ([] ++ rest)), rest. split; [exact INV2|]. split; [exact HL|]. split.
  - change (active (dequeue (LActive sc) m st) sc) with (get_head (dequeue (LActive sc) m st) (LActive sc)). rewrite dequeue_head.
    rewrite decide_True by reflexivity. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. rewrite HL in HH. cbn in HH.
    destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
    destruct (optr_eqb_spec (Some mn) (Some m)) as [E|NE].
    + inversion E. subst mn. pose proof (proj1 (lists_singleton st LS (old_lists _ _ _ _ _ INV) (LActive sc) m rest HL) Hn) as ER. rewrite ER. reflexivity.
    + change (get_head st (LActive sc)) with (active st sc). rewrite HA, optr_eqb_refl. rewrite HL in Hin. destruct Hin as [->|Hin]; [congruence|].
      destruct rest as [|a rest']; [destruct Hin|]. cbn.
      pose proof (il_dll _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as D. rewrite HL in D. cbn [dll app] in D. destruct D as (D1 & _). rewrite Hn in D1. exact D1.
  - intros m1 Hm1. destruct rest as [|a rest']; cbn in Hm1; [discriminate|]. inversion Hm1. subst a.
    assert (Hin : In m1 (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
    destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV)))) sc m1 Hin) as (_ & [bb [aa Hbb]] & _).
    apply (g_rest _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbb) ltac:(rewrite HF; discriminate) sc Hin).
    rewrite HL. cbn. intros E. inversion E. subst m1.
    pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left.
Qed.
End STEPS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_mask_upto_all f n : 0 <= f -> 0 <= n -> (forall i, 0 <= i -> Z.testbit f i = true -> i <= n) -> Z.land f (mask_upto n) = f.
Proof.
  intros Hf Hn H. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_mask_upto by lia.
  destruct (Z.testbit f i) eqn:E; [| reflexivity]. cbn. apply Z.leb_le. exact (H i Hi E).
Qed.

Lemma land_mask_upto_zero_above f n : 0 <= f -> 0 <= n -> Z.land f (mask_upto n) = 0 ->
  forall i, 0 <= i -> Z.testbit f i = true -> n < i.
Proof.
  intros Hf Hn H i Hi Hb. destruct (Z.lt_ge_cases n i) as [|LE]; [assumption|]. exfalso.
  assert (T : Z.testbit (Z.land f (mask_upto n)) i = true) by (rewrite Z.land_spec, testbit_mask_upto, Hb by lia; cbn; apply Z.leb_le; lia).
  rewrite H, Z.bits_0 in T. discriminate.
Qed.

Section TRY.
Variables (T : Type) (X : extras) (L : mled) (BL : list blk) (sc : Z) (k : mstate -> Z -> M T) (bail : M T).
Hypothesis HP : x_pend X = None.
Hypothesis HF : x_fresh X = None.
Hypothesis Hsc : 0 <= sc < 48.

Definition TA_POST (st st1 : mstate) (first : Z) (LS1 : lhead -> list aptr) : Prop :=
  TA_frame st st1 sc /\
  ((first = 0 /\ active st1 sc = None /\ INVL X st1 L BL LS1)
   \/ (exists g bg ai idx, first <> 0 /\ 0 <= first /\ ctz32 first = idx /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ 0 <= idx <= m_last_idx (MR st1 g)
         /\ m_sizeclass (MR st1 g) = sc /\ UNIT * size_class sc <= get_stride (MR st1 g)
         /\ INVL (xpend X (Some (fst bg, sstart (MR st1 g) idx))) st1 L BL LS1)).

Lemma set_avail_views v r : m_last_idx (m_set_avail v r) = m_last_idx r /\ m_sizeclass (m_set_avail v r) = m_sizeclass r
  /\ get_stride (m_set_avail v r) = get_stride r /\ (forall i, sstart (m_set_avail v r) i = sstart r i).
Proof. destruct r; repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma fin_ok st0 st LS m (mask : Z) :
  INVL X st L BL LS -> TA_frame st0 st sc -> active st sc = Some m -> m_avail (MR st m) = mask -> mask <> 0 ->
  exists st1 first LS1, ta_fin st m mask k = k st1 first /\ TA_POST st0 st1 first LS1.
Proof.
  intros INV TF HA AM MNZ. destruct (hd_facts X st L BL LS sc m INV HA) as (_ & Esc & bm & ai & Hbm).
  pose proof (ta_fin_ok X st L BL LS m bm ai INV HP HF Hbm ltac:(rewrite Esc; exact (hd_head X st L BL LS sc m INV HA)) ltac:(rewrite AM; exact MNZ)) as (INV1 & R1 & R2 & R3 & R4).
  rewrite AM in *. unfold ta_fin. eexists _, _, LS. split; [reflexivity|]. split; [eapply taf_trans; [exact TF| apply taf_upd_meta]|].
  right. exists m, bm, ai, (ctz32 (lowbit mask)).
  assert (MRE : forall x, x <> m -> MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) x = MR st x) by (intros; unfold MR; apply get_meta_rec_upd_other; assumption).
  assert (MRm : MR (upd_meta m (m_set_avail (mask - lowbit mask)) st) m = m_set_avail (mask - lowbit mask) (MR st m)) by (unfold MR; apply get_meta_rec_upd_same).
  rewrite MRm. destruct (set_avail_views (mask - lowbit mask) (MR st m)) as (V1 & V2 & V3 & V4). rewrite V1, V2, V3, V4. rewrite Esc in R4 |- *.
  split; [exact R2|]. split; [exact R3|]. split; [reflexivity|]. split; [exact HA|]. split; [exact Hbm|]. split; [exact R1|]. split; [reflexivity|]. split; [exact R4| exact INV1].
Qed.

Theorem try_avail_ok st LS :
  INVL X st L BL LS ->
  exists st1 first LS1, try_avail sc st k bail = k st1 first /\ TA_POST st st1 first LS1.
Proof.
  intros INV. unfold try_avail.
  destruct (active st sc) as [m|] eqn:HA.
  2:{ eexists _, _, LS. split; [reflexivity|]. split; [apply taf_refl| left; auto]. }
  fold (MR st m). destruct (Z.eqb_spec (m_avail (MR st m)) 0) as [AZ|ANZ]; cbn [negb].
  2:{ exact (fin_ok st st LS m _ INV (taf_refl st sc) HA eq_refl ANZ). }
  (* [comment removed for export] *)
  assert (STEP1 : exists st1 m1 LS1,
    (if m_freed (MR st m) =? 0
     then match active (dequeue (LActive sc) m st) sc with Some m1 => Some (dequeue (LActive sc) m st, m1) | None => None end
     else match m_next (MR st m) with Some m1 => Some (set_active sc (Some m1) st, m1) | None => None end) = Some (st1, m1)
    /\ GOODH X st1 L BL LS1 sc m1 /\ TA_frame st st1 sc
    \/ (m_freed (MR st m) = 0 /\ active (dequeue (LActive sc) m st) sc = None /\ exists LS1, INVL X (dequeue (LActive sc) m st) L BL LS1)).
  { destruct (Z.eqb_spec (m_freed (MR st m)) 0) as [FZ|FNZ].
    - destruct (dequeue_exhausted_ok X L BL sc HP HF Hsc st LS m INV HA AZ FZ) as (LS1 & rest & INV1 & HL & HA1 & NXT).
      rewrite HA1. destruct rest as [|m1 rest']; cbn.
      + exists st, m, LS. right. split; [exact FZ|]. split; [first [reflexivity| rewrite HA1; reflexivity]| exists LS1; exact INV1].
      + exists (dequeue (LActive sc) m st), m1, LS1. left. split; [reflexivity|]. split; [| apply taf_dequeue].
        destruct (NXT m1 eq_refl) as [A1 F1].
        assert (NE : m1 <> m).
        { intros ->. pose proof (il_nodup _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as ND. rewrite HL in ND. apply NoDup_cons in ND as [N _]. apply N. left. }
        pose proof (dequeue_data (LActive sc) m st m1) as D. destruct (data_same _ _ 0 D) as (_ & _ & Ea & Ef & _).
        split; [exact INV1|]. split; [first [reflexivity| rewrite HA1; reflexivity]|]. rewrite Ea, Ef. auto.
    - destruct (hd_next X st L BL LS sc m INV HA) as (mn & Hn & Hin). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st LS m mn (conj INV (conj HA (conj AZ FNZ))) Hn) as [LS1 G1].
      exists (set_active sc (Some mn) st), mn, LS1. left. split; [reflexivity|]. split; [exact G1| apply taf_set_active]. }
  destruct STEP1 as (st1 & m1 & LS1 & [(E1 & G1 & TF1)|(FZ & HA1 & LS1' & INV1)]).
  2:{ rewrite (proj2 (Z.eqb_eq _ _) FZ), HA1. eexists _, 0, LS1'. split; [reflexivity|]. split; [apply taf_dequeue| left; auto]. }
  rewrite E1. clear E1.
  (* [comment removed for export] *)
  assert (STEP2 : exists st2 m2 LS2,
    (let mr := get_meta_rec st1 m1 in
     if (m_freed (MR st1 m1) =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0)
     then match m_next mr with Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn)) | None => (st1, m1, m_freed (MR st1 m1)) end
     else (st1, m1, m_freed (MR st1 m1))) = (st2, m2, m_freed (MR st2 m2))
    /\ GOODH X st2 L BL LS2 sc m2 /\ TA_frame st st2 sc).
  { cbn zeta. fold (MR st1 m1). destruct (_ && _).
    - pose proof G1 as (INV1 & HA1 & _). destruct (hd_next X st1 L BL LS1 sc m1 INV1 HA1) as (mn & Hn & _). rewrite Hn.
      destruct (rotate_ok X L BL sc HF st1 LS1 m1 mn G1 Hn) as [LS2 G2].
      exists (set_active sc (Some mn) st1), mn, LS2. split; [reflexivity|]. split; [exact G2| eapply taf_trans; [exact TF1| apply taf_set_active]].
    - exists st1, m1, LS1. auto. }
  destruct STEP2 as (st2 & m2 & LS2 & E2 & G2 & TF2). cbn zeta in E2. fold (MR st1 m1) in E2 |- *.
  match goal with |- context [let '(p, mask) := ?t in _] => change t with (st2, m2, m_freed (MR st2 m2)) end || rewrite E2.
  cbn iota. fold (MR st2 m2).
  destruct G2 as (INV2 & HA2 & AZ2 & FNZ2).
  destruct (hd_facts X st2 L BL LS2 sc m2 INV2 HA2) as (_ & Esc2 & b2 & ai2 & Hb2).
  pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb2) as GO2.
  pose proof (g_masks _ _ _ _ _ _ GO2) as (W1 & W2 & W3 & W4 & W5 & W6). pose proof (g_ai _ _ _ _ _ _ GO2) as AI2. pose proof (g_li _ _ _ _ _ _ GO2) as LI2.
  rewrite (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ (ex_intro _ ai2 Hb2)). cbn [default].
  assert (GAI : group_active_idx st2 b2 = ai2).
  { unfold group_active_idx, get_group. rewrite Hb2. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  rewrite GAI.
  (* [comment removed for export] *)
  assert (STEP3 : exists st3 m3 LS3 b3 ai3,
    (if Z.land (m_freed (MR st2 m2)) (mask_upto ai2) =? 0
     then if negb (optr_eqb (m_next (MR st2 m2)) (Some m2))
          then match m_next (MR st2 m2) with Some mn => (set_active sc (Some mn) st2, mn) | None => (st2, m2) end
          else (let cnt := ai2 + 2 in
                let size := size_class (m_sizeclass (MR st2 m2)) * UNIT in
                let span := UNIT + size * cnt in
                let cnt := span_loop 300 cnt span size in
                let cnt := if m_last_idx (MR st2 m2) + 1 <? cnt then m_last_idx (MR st2 m2) + 1 else cnt in
                (set_group_active_idx b2 (cnt - 1) st2, m2))
     else (st2, m2)) = (st3, m3)
    /\ GOODH X st3 L BL LS3 sc m3 /\ TA_frame st st3 sc
    /\ s_groups st3 !! b3 = Some (mkGhdr (Some m3) ai3) /\ Z.land (m_freed (MR st3 m3)) (mask_upto ai3) <> 0).
  { destruct (Z.eqb_spec (Z.land (m_freed (MR st2 m2)) (mask_upto ai2)) 0) as [LZ|LNZ].
    - (* [comment removed for export] *)
      pose proof (land_mask_upto_zero_above _ _ W2 (proj1 AI2) LZ) as ABOVE.
      assert (PART : ai2 < m_last_idx (MR st2 m2)).
      { destruct (Z.eq_dec (m_freed (MR st2 m2)) 0) as [|NZ]; [contradiction|].
        destruct (Z.lt_ge_cases ai2 (m_last_idx (MR st2 m2))) as [|GE]; [assumption|]. exfalso. apply NZ.
        apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. destruct (Z.testbit (m_freed (MR st2 m2)) i) eqn:E; [| reflexivity].
        pose proof (ABOVE i Hi E). pose proof (W4 i Hi E). lia. }
      destruct (hd_next X st2 L BL LS2 sc m2 INV2 HA2) as (mn & Hn & Hin). rewrite Hn.
      destruct (optr_eqb_spec (Some mn) (Some m2)) as [E|NE]; cbn [negb].
      + (* [comment removed for export] *)
        set (cnt0 := span_loop 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)).
        set (cnt := if m_last_idx (MR st2 m2) + 1 <? cnt0 then m_last_idx (MR st2 m2) + 1 else cnt0).
        pose proof (span_loop_ge 300 (ai2 + 2) (UNIT + size_class (m_sizeclass (MR st2 m2)) * UNIT * (ai2 + 2)) (size_class (m_sizeclass (MR st2 m2)) * UNIT)) as SL. fold cnt0 in SL.
        assert (CR : ai2 + 1 <= cnt - 1 <= m_last_idx (MR st2 m2)) by (unfold cnt; destruct (Z.ltb_spec (m_last_idx (MR st2 m2) + 1) cnt0); lia).
        unfold set_group_active_idx, get_group. rewrite Hb2. cbn [g_meta].
        replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia).
        set (st3 := Malloc.set_groups _ st2).
        assert (INV3 : INVL X st3 L BL LS2).
        { apply (INVL_set_ai X st2 L BL LS2 m2 b2 ai2 (cnt - 1) INV2 Hb2); [lia| | intros _; rewrite Esc2; exact (hd_in X st2 L BL LS2 sc m2 INV2 HA2)].
          intros i Hi Hb. unfold tbit in Hb. rewrite AZ2, Z.bits_0 in Hb. discriminate. }
        exists st3, m2, LS2, b2, (cnt - 1). split; [reflexivity|].
        split; [split; [exact INV3| split; [exact HA2| auto]]|].
        split; [eapply taf_trans; [exact TF2| constructor; auto; try (intros h _; destruct h; reflexivity)]|].
        split; [unfold st3; cbn; rewrite lookup_insert_eq; reflexivity|].
        change (MR st3 m2) with (MR st2 m2). intros E0.
        assert (Tb : Z.testbit (Z.land (m_freed (MR st2 m2)) (mask_upto (cnt - 1))) (ai2 + 1) = true).
        { rewrite Z.land_spec, testbit_mask_upto by lia. unfold tbit in W6. rewrite (W6 (ai2 + 1)) by lia. cbn. apply Z.leb_le. lia. }
        rewrite E0, Z.bits_0 in Tb. discriminate.
      + (* [comment removed for export] *)
        destruct (rotate_ok X L BL sc HF st2 LS2 m2 mn (conj INV2 (conj HA2 (conj AZ2 FNZ2))) Hn) as [LS3 G3].
        assert (NEm : mn <> m2) by congruence.
        destruct (il_active _ _ (proj1 (proj2 (proj2 (proj2 INV2)))) sc mn Hin) as (_ & [b3 [ai3 Hb3]] & Esc3).
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb3) as GO3.
        assert (FULL : ai3 = m_last_idx (MR st2 mn)).
        { pose proof (g_ai _ _ _ _ _ _ GO3) as AI3. destruct (Z.lt_ge_cases ai3 (m_last_idx (MR st2 mn))) as [LT|]; [| lia]. exfalso.
          apply NEm. eapply (ig_onepartial _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2)))))); [exact Hb3| exact Hb2| exact LT| exact PART| congruence]. }
        exists (set_active sc (Some mn) st2), mn, LS3, b3, ai3. split; [reflexivity|]. split; [exact G3|].
        split; [eapply taf_trans; [exact TF2| apply taf_set_active]|]. split; [exact Hb3|].
        change (MR (set_active sc (Some mn) st2) mn) with (MR st2 mn).
        pose proof (g_masks _ _ _ _ _ _ GO3) as (V1 & V2 & V3 & V4 & V5 & V6).
        pose proof (g_ai _ _ _ _ _ _ GO3) as AI3.
        rewrite (land_mask_upto_all (m_freed (MR st2 mn)) ai3 V2 ltac:(clear -AI3; lia) ltac:(rewrite FULL; exact V4)).
        destruct G3 as (_ & _ & _ & F3). exact F3.
    - exists st2, m2, LS2, b2, ai2. split; [reflexivity|]. split; [split; [exact INV2| auto]|]. auto. }
  destruct STEP3 as (st3 & m3 & LS3 & b3 & ai3 & E3 & G3 & TF3 & Hb3 & ACT).
  match goal with |- context [let '(st4, m4) := ?t in _] => change t with (st3, m3) end || rewrite E3.
  cbn iota. clear E3.
  (* [comment removed for export] *)
  destruct G3 as (INV3 & HA3 & AZ3 & FNZ3).
  destruct (hd_facts X st3 L BL LS3 sc m3 INV3 HA3) as (_ & Esc3 & _).
  rewrite (activate_group_eq X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3).
  pose proof (INVL_activate X st3 L BL LS3 m3 b3 ai3 INV3 Hb3 AZ3 ltac:(rewrite Esc3; exact (hd_head X st3 L BL LS3 sc m3 INV3 HA3))) as INV4.
  set (st4 := upd_meta m3 _ st3) in INV4 |- *.
  rewrite (guard_true 40) by (apply Bool.negb_true_iff; apply Z.eqb_neq; exact ACT).
  pose proof (INVL_decay_bounces X st4 L BL LS3 (m_sizeclass (get_meta_rec st4 m3)) INV4) as INV5.
  set (st5 := decay_bounces _ st4) in INV5 |- *.
  assert (MR5 : MR st5 m3 = m_set_avail (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) (m_set_freed (Z.ldiff (m_freed (MR st3 m3)) (mask_upto ai3)) (MR st3 m3))).
  { transitivity (MR st4 m3); [unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); reflexivity|]. unfold st4, MR. apply get_meta_rec_upd_same. }
  assert (HA5 : active st5 sc = Some m3) by (unfold st5, decay_bounces; destruct (sc_in_seq_range _ && _); exact HA3).
  destruct (fin_ok st st5 LS3 m3 (Z.land (m_freed (MR st3 m3)) (mask_upto ai3)) INV5) as (st6 & first & LS6 & E6 & POST).
  - eapply taf_trans; [exact TF3|]. eapply taf_trans; [apply taf_upd_meta| apply taf_decay].
  - exact HA5.
  - rewrite MR5. reflexivity.
  - exact ACT.
  - exists st6, first, LS6. split; [exact E6| exact POST].
Qed.
End TRY.


End CeilWrap.
End MI_WTry2.

(* [comment removed for export] *)
Module MI_WSlot.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Inv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WCreate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2 MI_WCreate2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition X_as (idle : list aptr) : extras := mkX idle [] None None None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GP (st st' : mstate) : Prop :=
  (forall rid r, s_regions st !! rid = Some r -> r_kind r = RKGroup -> s_regions st' !! rid = Some r)
  /\ s_secret st' = s_secret st.
Lemma GP_refl st : GP st st. Proof. split; [intros rid r H _; exact H| reflexivity]. Qed.
Lemma GP_trans a b c : GP a b -> GP b c -> GP a c.
Proof. intros [H1 S1] [H2 S2]. split; [intros rid r H K; exact (H2 rid r (H1 rid r H K) K)| congruence]. Qed.
Lemma GP_eq st st' : s_regions st' = s_regions st -> s_secret st' = s_secret st -> GP st st'.
Proof. intros E S. split; [intros rid r H _; rewrite E; exact H| exact S]. Qed.
Lemma GP_amf st st' : AM_frame st st' -> GP st st'.
Proof. intros AF. split; [exact (amf_regions _ _ AF)| exact (amf_ssec _ _ AF)]. Qed.
Lemma GP_taf st st' sc : TA_frame st st' sc -> GP st st'.
Proof. intros TF. apply GP_eq; [exact (taf_regions _ _ _ TF)| exact (taf_ssec _ _ _ TF)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geo_of (r : meta) : (optr * Z * Z * Z)%type := (m_mem r, m_last_idx r, m_maplen r, m_sizeclass r).

Lemma geo_facts r r' : geo_of r' = geo_of r ->
  (forall i, sstart r' i = sstart r i) /\ cnt_of r' = cnt_of r /\ m_maplen r' = m_maplen r /\ get_stride r' = get_stride r.
Proof.
  unfold geo_of. intros H. injection H. intros E1 E2 E3 E4.
  assert (ES : get_stride r' = get_stride r) by (unfold get_stride; rewrite E2, E3, E1; reflexivity).
  unfold sstart, cnt_of, gbase. rewrite ES, E4, E3, E2. auto.
Qed.

Lemma geom_kept_geo st st' :
  (forall b h, s_groups st !! b = Some h -> s_groups st' !! b = Some h) ->
  (forall x, geo_of (MR st' x) = geo_of (MR st x)) ->
  geom_kept st st'.
Proof.
  intros HG HM b m Hm. pose proof Hm as [ai Hb]. split; [exists ai; apply HG; exact Hb|].
  destruct (geo_facts _ _ (HM m)) as (A & B & C & _). auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_idle_sub X idle' st L BL LS :
  (forall x, In x idle' -> In x (x_idle X)) -> INVL X st L BL LS -> INVL (xidle X idle') st L BL LS.
Proof.
  intros SUB (IR & IA & IM & IL & IG & IS & ISH).
  split; [exact (inv_R_X X (xidle X idle') st L eq_refl IR)|]. split; [exact IA|].
  split.
  { destruct IM as [Q1 Q2 Q3 Q4 Q5]; constructor; cbn; auto. }
  split; [exact IL|]. split; [exact (inv_G_X X (xidle X idle') st LS eq_refl eq_refl IG)|]. split; [exact (inv_S_X X (xidle X idle') st BL eq_refl IS)| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREE_IDLE.
Variables (idle : list aptr) (m : aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL (X_as (m :: idle)) st L BL LS.
Hypothesis NIm : ~ In m idle.
Let st' := fm_st st m.
Let LS' := fupd LS LFree (LS LFree ++ [m]).

Let IM := proj1 (proj2 (proj2 INV)).
Lemma fi_metas : s_metas st !! m = Some meta0.
Proof. exact (proj1 (im_idle _ _ _ IM m ltac:(left; reflexivity))). Qed.
Lemma fi_put : put_meta m meta0 st = st.
Proof. unfold put_meta. apply set_metas_id. apply insert_id. exact fi_metas. Qed.

Lemma free_idle_ok :
  INVL (X_as idle) st' L BL LS'
  /\ s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ s_groups st' = s_groups st /\ s_slots st' = s_slots st
  /\ s_regions st' = s_regions st /\ s_next_rid st' = s_next_rid st
  /\ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
  /\ c_mmap_counter (s_ctx st') = c_mmap_counter (s_ctx st)
  /\ c_bounces (s_ctx st') = c_bounces (s_ctx st) /\ c_seq (s_ctx st') = c_seq (s_ctx st).
Proof.
  pose proof (INVL_idle_sub (X_as (m :: idle)) idle st L BL LS ltac:(intros x Hx; right; exact Hx) INV) as INV1.
  assert (MRm : MR st m = meta0) by (unfold MR, get_meta_rec; rewrite fi_metas; reflexivity).
  unfold st', fm_st. rewrite fi_put.
  pose proof (INVL_queue (xidle (X_as (m :: idle)) idle) st L BL LS m LFree INV1 ltac:(rewrite MRm; reflexivity)
                ltac:(rewrite fi_metas; discriminate) ltac:(cbn; rewrite MRm; split; [reflexivity| tauto])) as INV2.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  split; [exact INV2|]. split; [exact F2|]. split; [exact F7|]. split; [exact F5|]. split; [exact F6|]. split; [exact F1|]. split; [exact F3|].
  split; [intros sc; change (active ?s sc) with (get_head s (LActive sc)); rewrite queue_head; destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]|].
  split; [intros sc; unfold usage, ctx; rewrite (cb_usage _ _ FC); reflexivity|].
  split; [exact (cb_mc _ _ FC)|]. split; [exact (cb_bounces _ _ FC)| exact (cb_seq _ _ FC)].
Qed.
End FREE_IDLE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FINISH.
Variables (T : Type) (idle : list aptr) (st2 : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (m b : aptr) (ai last sc ml : Z) (k : mstate -> M T) (bail : M T).
Let X2 := mkX idle [] None None (Some m).
Hypothesis INV : INVL X2 st2 L BL LS.
Hypothesis Hb : s_groups st2 !! b = Some (mkGhdr (Some m) ai).
Hypothesis Em : MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml.
Hypothesis Hai : 0 <= ai <= last.
Hypothesis Hl : last <= 31.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis HA : active st2 sc = None.
Hypothesis UND : get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0.
Hypothesis TF : TF2 st2.

Let st3 := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2.
Let st4 := queue_st (LActive sc) m st3.
Let LS4 := fupd LS (LActive sc) (LS (LActive sc) ++ [m]).
Let s0 : aptr := (fst b, sstart (MR st2 m) 0).

Lemma fin_hosts : hosts st2 b m. Proof. exists ai. exact Hb. Qed.
Lemma fin_empty : LS (LActive sc) = [].
Proof.
  pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma mask_upto_pred a : 0 <= a -> mask_upto a - 1 = Z.ldiff (mask_upto a) 1.
Proof.
  intros Ha. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
  destruct (Z.eq_dec i 0) as [->|NZ].
  - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (Z.testbit 1 i) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma testbit_avail' i : 0 <= i -> Z.testbit (mask_upto ai - 1) i = ((1 <=? i) && (i <=? ai)).
Proof.
  intros Hi. rewrite mask_upto_pred by lia. rewrite Z.ldiff_spec, testbit_mask_upto by lia.
  change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i ai); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma st3_eq : st3 = upd_meta m (fun r => m_set_avail (mask_upto ai - 1) (m_set_freed (mask_upto last - mask_upto ai) r)) st2.
Proof.
  unfold st3, upd_meta. f_equal. fold (MR st2 m). rewrite Em. reflexivity.
Qed.

Lemma fin_INV3 : INVL (mkX idle [] (Some s0) None (Some m)) st3 L BL LS.
Proof.
  rewrite st3_eq.
  pose proof (created_masks ai last Hai Hl) as CM. cbn zeta in CM. destruct CM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (Elast : m_last_idx (MR st2 m) = last) by (rewrite Em; reflexivity).
  apply (INVL_mask_change X2 st2 L BL LS m b ai (mask_upto ai - 1) (mask_upto last - mask_upto ai) (Some s0) INV Hb).
  - rewrite Elast. unfold tbit. split; [unfold mask_upto; assert (P2 : 2 ^ 1 <= 2 ^ (ai + 1)) by (apply Z.pow_le_mono_r; lia); change (2 ^ 1) with 2 in P2; lia|].
    split; [exact M2|]. split; [intros i Hi Hb'; rewrite testbit_avail' in Hb' by lia; apply andb_true_iff in Hb' as [_ Hb']; apply Z.leb_le in Hb'; exact Hb'|].
    split; [exact M4|]. split; [| exact M6].
    intros i Hi Ha Hf. rewrite testbit_avail' in Ha by lia. apply andb_true_iff in Ha as [_ Ha]. apply Z.leb_le in Ha. exact (M5 i Hi (M7 i ltac:(lia)) Hf).
  - rewrite Elast. intros i Hi. cbn zeta. unfold tbit.
    pose proof (is_part _ _ _ IS _ _ _ i Hb ltac:(rewrite Elast; exact Hi)) as P5. cbn zeta in P5. rewrite Em in P5. cbn [m_avail m_freed x_pend X2] in P5.
    rewrite <- Em in P5.
    destruct P5 as (_ & _ & nAC & nAD & _ & nBC & nBD & _ & _ & _ & _).
    rewrite testbit_avail' by lia.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + assert (A0 : Z.testbit (mask_upto ai) 0 = true) by (apply M7; lia).
      apply one5_iff_create; [apply one5_E| intros C; exact (nAC (conj A0 C))| intros D; exact (nAD (conj A0 D))].
      * cbn. discriminate.
      * intros F. exact (M5 0 ltac:(lia) A0 F).
      * unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
    + destruct (Z.le_gt_cases i ai) as [Hle|Hgt].
      * assert (A : Z.testbit (mask_upto ai) i = true) by (apply M7; lia).
        apply one5_iff_create; [apply one5_A| intros C; exact (nAC (conj A C))| intros D; exact (nAD (conj A D))].
        -- replace (1 <=? i) with true by (symmetry; apply Z.leb_le; lia). replace (i <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- intros F. exact (M5 i ltac:(lia) A F).
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
      * assert (F : Z.testbit (mask_upto last - mask_upto ai) i = true) by (apply M6; lia).
        apply one5_iff_create; [apply one5_B| intros C; exact (nBC (conj F C))| intros D; exact (nBD (conj F D))].
        -- replace (i <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite andb_false_r. discriminate.
        -- exact F.
        -- unfold s0. rewrite (slot_start'_eq _ _ _ IM _ _ i fin_hosts). intros E. injection E. intros E2.
           pose proof (sstart_lt _ _ _ IG _ _ 0 i fin_hosts ltac:(lia)). pose proof (stride_ge _ _ _ IG _ _ fin_hosts). unfold UNIT in *. lia.
  - right. split; [intros s Hs; discriminate|]. intros s Hs. inversion Hs. exists 0. rewrite Elast. split; [lia|].
    rewrite (slot_start'_eq _ _ _ IM _ _ 0 fin_hosts). reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
  - intros NF. exfalso. apply NF. reflexivity.
Qed.

Lemma fin_MR3 : MR st3 m = mkMeta None None (Some b) (mask_upto ai - 1) (mask_upto last - mask_upto ai) last 1 sc ml.
Proof. unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 m). rewrite Em. reflexivity. Qed.
Lemma fin_MR3_other x : x <> m -> MR st3 x = MR st2 x.
Proof. intros NE. unfold st3, MR. apply get_meta_rec_upd_other. exact NE. Qed.

Lemma fin_queue_eq : queue (LActive sc) m st3 k bail = k st4.
Proof. apply queue_eq; fold (MR st3 m); rewrite fin_MR3; reflexivity. Qed.

Lemma fin_head3 : get_head st3 (LActive sc) = None.
Proof. unfold st3. rewrite get_head_upd_meta. cbn. exact HA. Qed.

Lemma fin_INV4 : INVL (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4.
Proof.
  apply (INVL_queue (mkX idle [] (Some s0) None (Some m)) st3 L BL LS m (LActive sc) fin_INV3).
  - rewrite fin_MR3. reflexivity.
  - unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
  - cbn. split; [exact Hsc|]. split; [exists b; exists ai; exact Hb|]. split; [rewrite fin_MR3; reflexivity| reflexivity].
Qed.

Lemma fin_LS4 : LS4 (LActive sc) = [m].
Proof. unfold LS4. rewrite fupd_eq, fin_empty. reflexivity. Qed.

Lemma fin_MR4 : geo_of (MR st4 m) = geo_of (MR st3 m) /\ m_avail (MR st4 m) = m_avail (MR st3 m) /\ m_freed (MR st4 m) = m_freed (MR st3 m).
Proof.
  pose proof (queue_data (LActive sc) m st3 m) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  unfold geo_of. fold st4 in D1, D2, D3, D4, D5, D6, D7. rewrite D1, D4, D7, D6, D2, D3. auto.
Qed.

Lemma fin_geo x : geo_of (MR st4 x) = geo_of (MR st2 x).
Proof.
  pose proof (queue_data (LActive sc) m st3 x) as D. apply data_of_eq in D. destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  fold st4 in D1, D2, D3, D4, D5, D6, D7. unfold geo_of. rewrite D1, D4, D6, D7.
  destruct (aptr_eq_dec x m) as [->|NE].
  - rewrite fin_MR3, Em. reflexivity.
  - rewrite (fin_MR3_other x NE). reflexivity.
Qed.

Theorem slot_finish_ok :
  exists LS',
    queue (LActive sc) m st3 k bail = k st4
    /\ INVL (xpend (X_as idle) (Some s0)) st4 L BL LS'
    /\ TF2 st4
    /\ active st4 sc = Some m /\ (forall sc', sc' <> sc -> active st4 sc' = active st2 sc')
    /\ s_groups st4 = s_groups st2 /\ s_tick st4 = s_tick st2 /\ s_shadow st4 = s_shadow st2
    /\ m_last_idx (MR st4 m) = last /\ m_sizeclass (MR st4 m) = sc /\ get_stride (MR st4 m) = get_stride (MR st2 m)
    /\ (forall i, sstart (MR st4 m) i = sstart (MR st2 m) i) /\ s_regions st4 = s_regions st2 /\ s_secret st4 = s_secret st2.
Proof.
  exists LS4. destruct (queue_frame (LActive sc) m st3) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC). fold st4 in F1, F2, F3, F4, F5, F6, F7, F8, F9, FC.
  pose proof fin_INV4 as INV4.
  assert (G4 : s_groups st4 = s_groups st2) by (rewrite F5; reflexivity).
  destruct (geo_facts _ _ (fin_geo m)) as (S1 & S2 & S3 & S4).
  split; [exact fin_queue_eq|].
  split.
  { (* [comment removed for export] *)
    apply (INVL_clear_fresh (mkX idle [] (Some s0) None (Some m)) st4 L BL LS4 m INV4 eq_refl).
    intros b' ai' Hb'. rewrite G4 in Hb'.
    assert (Eb : b' = b /\ ai' = ai).
    { pose proof (hosts_inj _ _ _ (proj1 (proj2 (proj2 INV))) _ _ _ fin_hosts (ex_intro _ ai' Hb')) as <-. rewrite Hb in Hb'. inversion Hb'. auto. }
    destruct Eb as [-> ->].
    assert (Esc : m_sizeclass (MR st4 m) = sc) by (pose proof (fin_geo m) as G; unfold geo_of in G; rewrite Em in G; injection G; intros; congruence).
    rewrite Esc. split; [| split; [| split]].
    - intros _. rewrite fin_LS4. left. reflexivity.
    - intros _ NI. exfalso. apply NI. exists (LActive sc). rewrite fin_LS4. left. reflexivity.
    - intros sc0 Hin Hh. exfalso.
      pose proof (il_disj _ _ (proj1 (proj2 (proj2 (proj2 INV4)))) (LActive sc0) (LActive sc) m Hin ltac:(rewrite fin_LS4; left; reflexivity)) as E.
      inversion E. subst sc0. rewrite fin_LS4 in Hh. apply Hh. reflexivity.
    - intros _ HU. destruct fin_MR4 as (_ & EA & EF). rewrite EA, EF, fin_MR3. cbn. rewrite S4 in HU.
      destruct (UND HU) as [-> ->]. cbn. split; reflexivity. }
  split.
  { apply (TF2_kept st2 st4); [rewrite F2; reflexivity| rewrite F7; reflexivity| | exact TF].
    apply geom_kept_geo; [intros bb h Hh; rewrite G4; exact Hh| apply fin_geo]. }
  split; [change (active st4 sc) with (get_head st4 (LActive sc)); unfold st4; rewrite queue_head; destruct (decide (LActive sc = LActive sc)); [rewrite fin_head3; reflexivity| congruence]|].
  split; [intros sc' NE; change (active st4 sc') with (get_head st4 (LActive sc')); change (active st2 sc') with (get_head st2 (LActive sc')); unfold st4; rewrite queue_head; destruct (decide (LActive sc' = LActive sc)); [congruence|]; unfold st3; rewrite get_head_upd_meta; reflexivity|].
  split; [exact G4|]. split; [rewrite F7; reflexivity|]. split; [rewrite F2; reflexivity|].
  pose proof (fin_geo m) as G. unfold geo_of in G. rewrite Em in G. injection G. intros E4 E3 E2 E1.
  split; [exact E2|]. split; [exact E4|]. split; [exact S4|]. split; [exact S1|]. split; [rewrite F1; reflexivity| rewrite F8; reflexivity].
Qed.
End FINISH.


End CeilWrap.
End MI_WSlot.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MEX_defs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MEX_defs.MI_Tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Inv MI_Kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Cnt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Cnt.MI_Arith.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres1.MI_Geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Ext.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Ext.MI_List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Ext.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Pres1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Pres4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Pres4.MI_Pres3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Pres4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WFree.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WFree.MI_Read.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_WFree2.
Import MI_Ledger.
Import MI_WAMeta.
Import MI_WAMeta2.
Import MI_WTry.
Import MI_WTry2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WGroup.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_WCreate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import MI_Cnt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_WEnframe2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_WEnframe2.MI_TF2.
Import MI_WCreate2.
Import MI_WSlot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SLOT_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st1 : mstate) (idx : Z) (L1 : mled) (LS1 : lhead -> list aptr) : Prop :=
  (forall sc', sc' < sc -> active st1 sc' = active st sc') /\ ld_live L1 = ld_live L /\ GP st st1 /\
  ((idx = -1 /\ INVL (X_as idle) st1 L1 BL LS1 /\ TF0 st1)
   \/ (exists g bg ai, 0 <= idx <= m_last_idx (MR st1 g) /\ active st1 sc = Some g
         /\ s_groups st1 !! bg = Some (mkGhdr (Some g) ai) /\ m_sizeclass (MR st1 g) = sc
         /\ req + IB <= get_stride (MR st1 g)
         /\ (sc < 28 -> get_stride (MR st1 g) = UNIT * size_class sc)
         /\ INVL (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
         /\ TF2 st1)).

(* [comment removed for export] *)
Definition AG_POST (idle : list aptr) (sc req : Z) (st : mstate) (L : mled) (BL : list blk)
   (st2 : mstate) (go : optr) (L2 : mled) (LS2 : lhead -> list aptr) : Prop :=
  (forall sc', sc' <= sc -> active st2 sc' = active st sc') /\ ld_live L2 = ld_live L /\ GP st st2 /\
  match go with
  | None => INVL (X_as idle) st2 L2 BL LS2 /\ TF0 st2
  | Some m => exists b ai last ml,
      s_groups st2 !! b = Some (mkGhdr (Some m) ai)
      /\ MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml
      /\ 0 <= ai <= last /\ last <= 31
      /\ req + IB <= get_stride (MR st2 m)
      /\ (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc)
      /\ (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0)
      /\ INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 /\ TF2 st2
  end.

(* [comment removed for export] *)
Definition REC_OK (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> ftree L1 (k st1 idx) Post) ->
  ftree L (rec st j req k bail) Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ag_cnt1 (sc u0 : Z) : Z :=
  let size := UNIT * size_class sc in
  let cnt := cnt0_of sc u0 in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_cnt2 (sc cnt1 u1 : Z) (nosmall : bool) : Z :=
  if (u1 <? 4 * cnt1) && negb nosmall then adj sc (UNIT * size_class sc) cnt1 else cnt1.

Definition ag_cn3 (sc req cnt2 u1 : Z) (nosmall : bool) : Z * Z :=
  let size := UNIT * size_class sc in
  let needed := round_up_pg (size * cnt2 + UNIT) in
  if negb nosmall && (cnt2 <=? 7) then
    let req' := round_up_pg (req + IB + UNIT) in
    if (req' <? size + UNIT) || ((4 * PGSZ <=? req') && (u1 <? 2 * cnt2)) then (1, req') else (cnt2, needed)
  else (cnt2, needed).

Lemma ag_arith sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  let size := UNIT * size_class sc in
  (PGSZ / 2 < size * ag_cnt1 sc u0 + UNIT ->
   ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
   grp_ok sc c3 n3 = true /\ ((c3 = 1 /\ n3 = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (size * c3 + UNIT <= n3)))
  /\ (size * ag_cnt1 sc u0 + UNIT <= PGSZ / 2 -> nest_ok sc (ag_cnt1 sc u0) = true).
Proof.
  intros Hsc Hreq Hfit. pose proof (alloc_group_arith sc req u0 u1 ns Hsc Hreq Hfit) as AR. cbn zeta in AR.
  change (if (cnt0_of sc u0 =? 1) && (UNIT * size_class sc * cnt0_of sc u0 + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc u0) with (ag_cnt1 sc u0) in AR.
  destruct AR as [AR1 AR2]. cbn zeta. split; [| exact AR2].
  intros HB E. specialize (AR1 HB).
  change (if (u1 <? 4 * ag_cnt1 sc u0) && negb ns
          then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 2
               else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 3
               else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * ag_cnt1 sc u0) then 5
               else ag_cnt1 sc u0
          else ag_cnt1 sc u0) with (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in AR1.
  set (c2 := ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) in *. clearbody c2.
  unfold ag_cn3 in E. cbn zeta in E.
  destruct (negb ns && (c2 <=? 7)).
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [R|(R1 & R2 & R3)]; [left; exact R| right; rewrite R2 at 1; lia].
    + inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
      right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
  - inversion E; subst. destruct AR1 as [G R]. split; [exact G|]. destruct R as [(R1 & R2 & R3)|(R1 & R2 & R3)]; [| right; exact R3].
    right. rewrite R1. pose proof (proj1 (round_up_pg_spec (UNIT * size_class sc * 1 + UNIT))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma shadow_next_rid_none X st L BL LS : INVL X st L BL LS -> s_shadow st !! s_next_rid st = None.
Proof.
  intros INV. destruct (s_shadow st !! s_next_rid st) as [sh|] eqn:E; [| reflexivity]. exfalso.
  destruct (ish_dom _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ E) as (r & Hr & _).
  pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hr). lia.
Qed.

Lemma LS_empty_of X st L BL LS sc : INVL X st L BL LS -> active st sc = None -> LS (LActive sc) = [].
Proof.
  intros INV HA. pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV)))) (LActive sc)) as HH. cbn in HH. rewrite HA in HH.
  destruct (LS (LActive sc)); [reflexivity| discriminate].
Qed.

Lemma step_seq_fields st : let st' := step_seq st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); cbn; repeat split; reflexivity. Qed.

Lemma account_bounce_fields sc0 st : let st' := account_bounce sc0 st in
  s_shadow st' = s_shadow st /\ s_tick st' = s_tick st /\ (forall sc, active st' sc = active st sc) /\ s_regions st' = s_regions st
  /\ s_next_rid st' = s_next_rid st /\ s_metas st' = s_metas st /\ s_groups st' = s_groups st /\ (forall sc, usage st' sc = usage st sc).
Proof.
  unfold account_bounce. destruct (sc_in_seq_range sc0); [| cbn; repeat split; reflexivity].
  destruct (negb (unmap_seq st (sc0 - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc0 - 7) <? 10)); [| cbn; repeat split; reflexivity].
  destruct (bounces st (sc0 - 7) + 1 <? 100); cbn; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section MMAP_BRANCH.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma st1'_facts :
  INVL (X_as (m :: idle)) st1' L1 BL LS1 /\ s_shadow st1' = s_shadow st1 /\ s_tick st1' = s_tick st1
  /\ (forall sc', active st1' sc' = active st1 sc') /\ TF0 st1' /\ s_regions st1' = s_regions st1 /\ s_secret st1' = s_secret st1.
Proof.
  destruct (account_bounce_fields sc st1) as (A1 & A2 & A3 & A4 & _). destruct (step_seq_fields (account_bounce sc st1)) as (B1 & B2 & B3 & B4 & _).
  assert (SH : s_shadow st1' = s_shadow st1) by (unfold st1'; rewrite B1, A1; reflexivity).
  assert (TK : s_tick st1' = s_tick st1) by (unfold st1'; rewrite B2, A2; reflexivity).
  split; [apply INVL_step_seq; apply INVL_account_bounce; exact INV1|].
  split; [exact SH|]. split; [exact TK|]. split; [intros sc'; unfold st1'; rewrite B3, A3; reflexivity|].
  split; [exact (TF0_ctrl st1 st1' SH TK TF1)|]. split; [unfold st1'; rewrite B4, A4; reflexivity|].
  unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
Qed.

Theorem ag_mmap_ft :
  ftree L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct st1'_facts as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1').
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - (* [comment removed for export] *) cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + (* [comment removed for export] *)
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
      split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
    + (* [comment removed for export] *)
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
      rewrite <- Est2, <- Erid in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
      assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)).
      { rewrite Est2, ng_lookup, Erid, N.eqb_refl. reflexivity. }
      assert (NS : s_shadow st2 !! rid = None).
      { rewrite Est2, Erid. change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'). exact (shadow_next_rid_none _ _ _ _ _ INV1'). }
      assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; rewrite Est2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
      assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
      assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [rewrite Est2; reflexivity| rewrite Est2; reflexivity| exact TF1']).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      assert (HAI0 : sc = 0 -> AI = cnt - 1).
      { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
        pose proof (grp_ok_sound sc cnt needed GRP) as (Gc & _).
        replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
                  INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK. split; [intros sc' _; rewrite ACT'; apply ACT2|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite agt_regions. cbn. rewrite Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - rewrite agt_secret. cbn. rewrite Est2. cbn. exact SS1'. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F2; pose proof (Z.div_mod needed 4096 ltac:(lia)); lia).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NEST_BRANCH.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis HK : forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_ft :
  ftree L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons. split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND].
  - exact N5.
  - lia.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES). destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    + (* [comment removed for export] *)
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK. split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
        unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
      split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      eapply HK. split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
        - rewrite agt_regions. change (s_regions (nest_layout st2 g idx j size cnt) = s_regions st2).
          rewrite <- (s_regions_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity.
        - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
          rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), strip_nest_layout. reflexivity. }
      exists (fst bg, sstart (MR st2 g) idx), (cnt - 1), (cnt - 1), 0.
      rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
      rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
      split; [exact INV'| exact TF'].
Qed.
End NEST_BRANCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AG.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OK T rec sc Post.

Theorem alloc_group_ft idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None ->
  (forall st2 go L2 LS2, AG_POST idle sc req st L BL st2 go L2 LS2 -> ftree L2 (k st2 go) Post) ->
  ftree L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA HK. unfold alloc_group.
  eapply (alloc_meta_ft T BL Post _ bail (X_as idle) st L); [ | | exact INV| apply amf_refl| apply lf_refl].
  - (* [comment removed for export] *)
    intros st1 L1 LS1 INV1 AF LF. cbn beta iota. eapply HK.
    split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
    exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
  - (* [comment removed for export] *)
    intros st1 L1 LS1 m INV1 NIm AF LF. cbn beta iota zeta.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    + (* [comment removed for export] *)
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns). 
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        ftree L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        exact (ag_mmap_ft T idle st st1 L L1 BL LS1 m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED HK). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + (* [comment removed for export] *)
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      exact (ag_nest_ft T rec idle st st1 L L1 BL LS1 m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST HK).
Qed.
End AG.


End CeilWrap.
