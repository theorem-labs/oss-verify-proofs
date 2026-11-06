(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2 MI_WSlot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require MState ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MI_Realloc2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma nodup_map_on {A B} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup l -> List.NoDup (map f l).
Proof.
  induction l as [|a l IH]; intros INJ ND; cbn; [constructor|].
  inversion ND as [|? ? NI ND']; subst. constructor.
  - intros Hin. apply in_map_iff in Hin as (y & E & Hy). apply NI. rewrite (INJ a y (or_introl eq_refl) (or_intror Hy) (eq_sym E)). exact Hy.
  - apply IH; [| exact ND']. intros x y Hx Hy. apply INJ; right; assumption.
Qed.

Section RANGES.
Variables (X : extras) (st : mstate) (L : mled).
Hypothesis IR : inv_R X st L.

(* [comment removed for export] *)
#[using="CE X L IR"] Lemma region_base_inj rid1 rid2 r1 r2 :
  s_regions st !! rid1 = Some r1 -> s_regions st !! rid2 = Some r2 -> r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
  r_base r1 = r_base r2 -> rid1 = rid2.
Proof.
  intros H1 H2 K1 K2 E. destruct (N.eq_dec rid1 rid2) as [->|NE]; [reflexivity|]. exfalso.
  pose proof (ir_disj _ _ _ IR _ _ _ _ H1 H2 NE) as D. unfold region_live_range in D.
  pose proof (ir_shape _ _ _ IR _ _ H1) as (_ & _ & L1 & _). pose proof (ir_shape _ _ _ IR _ _ H2) as (_ & _ & L2 & _).
  pose proof (round_up_ge (r_len r1)). pose proof (round_up_ge (r_len r2)).
  destruct (r_kind r1); try (exfalso; exact (K1 eq_refl)); destruct (r_kind r2); try (exfalso; exact (K2 eq_refl)); lia.
Qed.

Let GF := fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end.

#[using="CE X st IR"] Lemma group_bases_nodup : List.NoDup (map fst (ld_groups L)).
Proof.
  eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact (ir_groups _ _ _ IR)|].
  rewrite map_map. cbn. apply nodup_map_on.
  - intros [q1 rq1] [q2 rq2] H1 H2 E. apply filter_In in H1 as [H1 K1]. apply filter_In in H2 as [H2 K2]. apply mtl_in in H1. apply mtl_in in H2. cbn in *.
    assert (Eq : q1 = q2).
    { apply (region_base_inj q1 q2 rq1 rq2 H1 H2); [destruct (r_kind rq1); try discriminate| destruct (r_kind rq2); try discriminate| exact E]. }
    subst q2. rewrite H1 in H2. inversion H2. reflexivity.
  - apply List.NoDup_filter. apply NoDup_ListNoDup. apply NoDup_map_to_list.
Qed.

Variables (rid : N) (r : region).
Hypothesis Hr : s_regions st !! rid = Some r.
Hypothesis Hk : r_kind r = RKGroup.

#[using="CE X st IR GF rid Hr Hk"] Lemma g_remove_in b' l' : In (b', l') (g_remove (r_base r) (ld_groups L)) <-> In (b', l') (ld_groups L) /\ b' <> r_base r.
Proof.
  assert (Hin : In (r_base r, r_len r) (ld_groups L)).
  { apply (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR))). apply in_map_iff. exists (rid, r). split; [reflexivity|].
    apply filter_In. split; [apply mtl_in; exact Hr| cbn; rewrite Hk; reflexivity]. }
  pose proof group_bases_nodup as ND.
  destruct (g_remove_split (r_base r) (r_len r) (ld_groups L) [] Hin ltac:(rewrite app_nil_r; exact ND)) as (l1 & l2 & E & Eg).
  rewrite Eg. rewrite E in ND |- *. rewrite map_app in ND. cbn [map fst] in ND. apply List.NoDup_remove in ND as [ND NI].
  rewrite !in_app_iff. cbn. split.
  - intros H. split; [tauto|]. intros Eb. subst b'. apply NI. rewrite <- map_app. apply in_map_iff. exists (r_base r, l'). split; [reflexivity|]. apply in_app_iff. exact H.
  - intros [[H|[H|H]] NE]; [tauto| exfalso; apply NE; congruence| tauto].
Qed.

#[using="Type"] Lemma in_filter_ne (kr : N * region) (l : list (N * region)) :
  In kr (filter (fun kr : N * region => Is_true (negb (N.eqb (fst kr) rid))) l) <-> In kr l /\ fst kr <> rid.
Proof.
  rewrite <- !list_elem_of_In. rewrite list_elem_of_filter. rewrite negb_True. 
  split; [intros [H1 H2]| intros [H2 H1]]; (split; [| ]); try assumption.
  - intros E. apply H1. apply Is_true_eq_left. apply N.eqb_eq. exact E.
  - intros T. apply H1. apply N.eqb_eq. apply Is_true_eq_true. exact T.
Qed.

#[using="CE X IR GF Hr Hk"] Lemma lranges_wo_iff x : In x (lranges_wo L (r_base r)) <-> In x (live_ranges_wo st rid).
Proof.
  unfold lranges_wo, live_ranges_wo. unfold lranges. cbn [ld_resv ld_groups ld_metas ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups].
  rewrite (ir_resv _ _ _ IR). rewrite !in_app_iff. split.
  - intros [H|[H|[H|H]]]; [left; exact H| right| right| right].
    + apply in_map_iff in H as ([b l] & <- & Hg). cbn. apply g_remove_in in Hg as [Hg NE].
      pose proof (Permutation_in _ (ir_groups _ _ _ IR) Hg) as Hin. apply in_map_iff in Hin as ([rid' r'] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk']. cbn in Hk'. apply in_map_iff. exists (rid', r'). split.
      * cbn. unfold region_live_range. destruct (r_kind r'); try discriminate; reflexivity.
      * apply in_filter_ne. split; [exact Hf|]. cbn. intros ->. apply mtl_in in Hf. rewrite Hr in Hf. inversion Hf. subst. apply NE. reflexivity.
    + apply in_map_iff in H as ([[b l] kk] & <- & Hm). cbn.
      pose proof (Permutation_in _ (ir_metas _ _ _ IR) Hm) as Hin. apply in_map_iff in Hin as ([rid' r'] & E & Hf). cbn in E. inversion E. subst.
      apply filter_In in Hf as [Hf Hk']. cbn in Hk'. apply in_map_iff. exists (rid', r'). split.
      * cbn. unfold region_live_range. destruct (r_kind r'); try discriminate; reflexivity.
      * apply in_filter_ne. split; [exact Hf|]. cbn. intros ->. apply mtl_in in Hf. rewrite Hr in Hf. inversion Hf. subst. rewrite Hk in Hk'. discriminate.
    + destruct (ld_brkreg L) as [[b l]|] eqn:EB; [| destruct H]. destruct H as [<-|[]].
      destruct (proj1 (ir_brkreg _ _ _ IR b l) EB) as (rid' & r' & Hr' & Hk' & <- & <-).
      apply in_map_iff. exists (rid', r'). split; [cbn; unfold region_live_range; rewrite Hk'; reflexivity|].
      apply in_filter_ne. split; [apply In_map_to_list_regions; exact Hr'|]. cbn. intros ->. rewrite Hr in Hr'. inversion Hr'. subst. rewrite Hk in Hk'. discriminate.
  - intros [H|H]; [left; exact H| right].
    apply in_map_iff in H as ([rid' r'] & <- & Hin). apply in_filter_ne in Hin as [Hin NE']. cbn in NE'.
    cbn. apply In_map_to_list_regions in Hin.
    unfold region_live_range. destruct (r_kind r') eqn:Hk'.
    + right. right. rewrite (proj2 (ir_brkreg _ _ _ IR (r_base r') (r_len r'))); [left; reflexivity| exists rid', r'; auto].
    + right. left.
      assert (Hf : In (rid', r') (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| cbn; rewrite Hk'; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1)) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_metas _ _ _ IR)) Hm) as Hm'.
      apply in_map_iff. eexists. split; [| exact Hm']. reflexivity.
    + left.
      assert (Hf : In (rid', r') (List.filter GF (map_to_list (s_regions st)))).
      { apply filter_In. split; [apply In_map_to_list_regions; exact Hin| unfold GF; cbn; rewrite Hk'; reflexivity]. }
      pose proof (in_map (fun kr : N * region => (r_base (snd kr), r_len (snd kr))) _ _ Hf) as Hm.
      pose proof (Permutation_in _ (Permutation_sym (ir_groups _ _ _ IR)) Hm) as Hm'. cbn in Hm'.
      apply in_map_iff. exists (r_base r', r_len r'). split; [reflexivity|]. apply g_remove_in. split; [exact Hm'|].
      intros E. apply NE'. apply (region_base_inj rid' rid r' r Hin Hr); [rewrite Hk'; discriminate| rewrite Hk; discriminate| exact E].
Qed.

#[using="CE X IR GF Hr Hk"] Lemma ranges_free_wo_eq a n : ranges_free (lranges_wo L (r_base r)) a n = ranges_free (live_ranges_wo st rid) a n.
Proof. unfold ranges_free. apply forallb_ext. apply lranges_wo_iff. Qed.

#[using="X IR GF Hr Hk"] Theorem mremap_answer_ok_eq oldlen newlen z :
  mremap_answer_okL L (r_base r) oldlen newlen z = mremap_answer_ok st rid (r_base r) oldlen newlen z.
Proof.
  unfold mremap_answer_okL, mremap_answer_ok. rewrite ranges_free_wo_eq, (ranges_free_eq X st L IR). reflexivity.
Qed.
End RANGES.

End WithCeil.
End MI_Realloc2.

(* [comment removed for export] *)
Module MI_Realloc3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WEnframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.MI_Realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
#[using="Type"] Lemma filter_cons_true {A} (F : A -> bool) x l : F x = true -> List.filter F (x :: l) = x :: List.filter F l.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.
#[using="Type"] Lemma filter_cons_false {A} (F : A -> bool) x l : F x = false -> List.filter F (x :: l) = List.filter F l.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

Section REGROUP63.
Variables (st : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (ai : Z) (r : region) (nb needed : Z).
Let c : cptr := (rid, UNIT).
Let X1 : extras := mkX [] [] (Some c) None None.
Hypothesis INV1 : INVL X1 st L BL1 LS.
Hypothesis Hg : s_groups st !! (rid, 0) = Some (mkGhdr (Some m) ai).
Local Notation R := (MR st).
Hypothesis H63 : m_sizeclass (R m) = 63.
Hypothesis Hr : s_regions st !! rid = Some r.
Hypothesis Hnb : 0 < nb /\ nb mod PGSZ = 0.
Hypothesis Hnd : PGSZ <= needed /\ needed mod PGSZ = 0 /\ needed < LEN_MAX /\ nb + needed <= alloc_ceiling.
Hypothesis DISJ : forall rid' r', s_regions st !! rid' = Some r' -> rid' <> rid ->
  let '(b', l') := region_live_range r' in nb + needed <= b' \/ b' + l' <= nb.

Let f := fun rg : meta => m_set_maplen (needed / 4096) rg.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st.
Let st2 := upd_meta m f st1.
Let e : aptr := (rid, needed - IB).
Let st' := wr8 e 0 st2.
Let L' := set_groups ((nb, needed) :: g_remove (r_base r) (ld_groups L)) L.
Local Notation R' := (MR st').

Let IR := proj1 INV1. Let IA := proj1 (proj2 INV1). Let IM := proj1 (proj2 (proj2 INV1)). Let IL := proj1 (proj2 (proj2 (proj2 INV1))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

(* [comment removed for export] *)
#[using="ai Hg"] Lemma g_hosts : hosts st (rid, 0) m. Proof. exists ai. exact Hg. Qed.
#[using="CEc L BL1 INV1 Hg IG"] Lemma GO : group_ok X1 st LS m (rid, 0) ai. Proof. exact (ig_ok _ _ _ IG _ _ _ Hg). Qed.
#[using="CEc L BL1 rid ai nb needed c X1 INV1 Hg H63 IG"] Lemma g_facts : m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0 /\ ~ in_list LS m.
Proof. destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(_ & A & B & C)]; [rewrite H63 in H; lia| auto]. Qed.
#[using="CEc L BL1 LS rid ai nb needed c X1 INV1 Hg H63 Hr IG"] Lemma r_group : r_kind r = RKGroup /\ m_maplen (R m) * 4096 = round_up_pg (r_len r).
Proof.
  destruct g_facts as (_ & ML & _). destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr0 & K & E & _). cbn [fst] in Hr0.
  rewrite Hr in Hr0. injection Hr0 as <-. auto.
Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg IM"] Lemma gbase_m : gbase (R m) = (rid, 0). Proof. exact (hosts_gbase _ _ _ IM _ _ g_hosts). Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg IM"] Lemma mem_m : m_mem (R m) = Some (rid, 0). Proof. exact (hosts_mem _ _ _ IM _ _ g_hosts). Qed.
#[using="CEc nb Hnb Hnd"] Lemma needed_div : needed / 4096 * 4096 = needed /\ 1 <= needed / 4096.
Proof. destruct Hnd as (N1 & N2 & _). unfold PGSZ in *. split; [| apply Z.div_le_lower_bound; lia]. pose proof (Z_div_mod_eq_full needed 4096). lia. Qed.

(* [comment removed for export] *)
#[using="CEc L BL1 LS ai nb needed c X1 INV1 Hg H63 IM IG IS"] Lemma region_only b m' : hosts st b m' -> fst b = rid -> m' = m /\ b = (rid, 0).
Proof.
  intros Hm' Hf. destruct g_facts as (L0 & ML & NL).
  destruct (Z.eq_dec (m_maplen (R m')) 0) as [Z0|NZ].
  - exfalso. destruct (top_chain X1 st BL1 LS IM IG IS m' b Hm' Z0) as (t & j & ch & bt & Ha & Ht & Htop & Hft).
    assert (t = m) by (apply (top_unique X1 st LS IG t m bt (rid, 0) Ht g_hosts Htop ML); cbn; congruence). subst t.
    destruct (anc_facts X1 st BL1 LS IM IG IS _ _ _ _ Ha) as (bm' & bp & _ & _ & _ & _ & _ & _ & _ & _ & Hsc). rewrite H63 in Hsc. lia.
  - pose proof (top_unique X1 st LS IG m' m b (rid, 0) Hm' g_hosts NZ ML Hf) as ->. split; [reflexivity|].
    exact (hosts_inj _ _ _ IM _ _ _ Hm' g_hosts).
Qed.

(* [comment removed for export] *)
#[using="Hr"] Lemma st1_regions : s_regions st1 = <[rid := mkRegion (r_kind r) nb needed]> (s_regions st).
Proof. unfold st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="Hr"] Lemma st'_regions : s_regions st' = <[rid := mkRegion (r_kind r) nb needed]> (s_regions st).
Proof. unfold st'. rewrite s_regions_wr8. unfold st2. rewrite s_regions_upd_meta. exact st1_regions. Qed.
#[using="r Hr"] Lemma st'_region_other rid' : rid' <> rid -> s_regions st' !! rid' = s_regions st !! rid'.
Proof. intros NE. rewrite st'_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Hr"] Lemma st'_region_rid : s_regions st' !! rid = Some (mkRegion (r_kind r) nb needed).
Proof. rewrite st'_regions. apply lookup_insert_eq. Qed.
#[using="Type"] Lemma st'_ctx : s_ctx st' = s_ctx st. Proof. unfold st', st2, st1. rewrite s_ctx_wr8, s_ctx_upd_meta, s_ctx_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_groups : s_groups st' = s_groups st. Proof. unfold st', st2, st1. rewrite s_groups_wr8, s_groups_upd_meta, s_groups_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_slots : s_slots st' = s_slots st. Proof. unfold st', st2, st1. rewrite s_slots_wr8, s_slots_upd_meta, s_slots_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_areas : s_areas st' = s_areas st. Proof. unfold st', st2, st1. rewrite s_areas_wr8, s_areas_upd_meta, s_areas_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_next_rid : s_next_rid st' = s_next_rid st. Proof. unfold st', st2, st1. rewrite s_next_rid_wr8, s_next_rid_upd_meta, s_next_rid_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_secret : s_secret st' = s_secret st. Proof. unfold st', st2, st1. rewrite s_secret_wr8, s_secret_upd_meta, s_secret_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_reserved : s_reserved st' = s_reserved st. Proof. unfold st', st2, st1. rewrite s_reserved_wr8, s_reserved_upd_meta, s_reserved_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_tick : s_tick st' = s_tick st. Proof. unfold st', st2, st1. rewrite s_tick_wr8, s_tick_upd_meta, s_tick_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st2_metas : s_metas st2 = <[m := f (R m)]> (s_metas st).
Proof. unfold st2. rewrite s_metas_upd_meta. unfold st1. unfold MR, get_meta_rec. rewrite s_metas_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st'_metas : s_metas st' = <[m := f (R m)]> (s_metas st). Proof. unfold st'. rewrite s_metas_wr8. exact st2_metas. Qed.
#[using="Type"] Lemma R'_eq x : R' x = if aptr_eqb x m then f (R m) else R x.
Proof.
  unfold MR at 1, get_meta_rec. rewrite st'_metas. destruct (aptr_eqb_spec x m) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="Type"] Lemma R'_other x : x <> m -> R' x = R x. Proof. intros NE. rewrite R'_eq, aptr_eqb_neq by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_m : R' m = f (R m). Proof. rewrite R'_eq, aptr_eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma f_mem x : m_mem (f x) = m_mem x. Proof. reflexivity. Qed.
#[using="Type"] Lemma R'_mem x : m_mem (R' x) = m_mem (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_prev x : m_prev (R' x) = m_prev (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_next x : m_next (R' x) = m_next (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_last x : m_last_idx (R' x) = m_last_idx (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freeable x : m_freeable (R' x) = m_freeable (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_sc x : m_sizeclass (R' x) = m_sizeclass (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_avail x : m_avail (R' x) = m_avail (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_freed x : m_freed (R' x) = m_freed (R x). Proof. rewrite R'_eq. destruct (aptr_eqb_spec x m) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma R'_cnt x : cnt_of (R' x) = cnt_of (R x). Proof. unfold cnt_of. rewrite R'_last. reflexivity. Qed.
#[using="Type"] Lemma R'_gbase x : gbase (R' x) = gbase (R x). Proof. unfold gbase. rewrite R'_mem. reflexivity. Qed.
#[using="CEc Hnd"] Lemma R'_maplen_m : m_maplen (R' m) = needed / 4096.
Proof.
  rewrite R'_m. unfold f, m_set_maplen. cbn [m_maplen]. destruct Hnd as (N1 & _ & N3 & _).
  change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small.
  split; [apply Z.div_pos; unfold PGSZ in *; lia|]. apply Z.div_lt_upper_bound; [lia|]. unfold LEN_MAX, PGSZ in *. lia.
Qed.
#[using="Type"] Lemma R'_maplen_other x : x <> m -> m_maplen (R' x) = m_maplen (R x). Proof. intros NE. rewrite R'_other by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_stride_other x : x <> m -> get_stride (R' x) = get_stride (R x). Proof. intros NE. rewrite R'_other by exact NE. reflexivity. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg H63 Hnb Hnd IG"] Lemma R'_stride_m : get_stride (R' m) = needed - UNIT.
Proof.
  destruct g_facts as (L0 & _ & _). pose proof needed_div as [D1 D2].
  unfold get_stride. rewrite R'_last, R'_maplen_m, L0. cbn [Z.eqb andb].
  replace (needed / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. lia.
Qed.
#[using="CEc L BL1 LS rid ai nb needed c X1 INV1 Hg H63 IG"] Lemma R_stride_m : get_stride (R m) = m_maplen (R m) * 4096 - UNIT.
Proof.
  destruct g_facts as (L0 & ML & _). unfold get_stride. rewrite L0. cbn [Z.eqb andb].
  replace (m_maplen (R m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). reflexivity.
Qed.
#[using="Type"] Lemma R'_sstart_other x i : x <> m -> sstart (R' x) i = sstart (R x) i. Proof. intros NE. rewrite R'_other by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_slot_start'_other x i : x <> m -> slot_start' (R' x) i = slot_start' (R x) i. Proof. intros NE. rewrite R'_other by exact NE. reflexivity. Qed.
#[using="Type"] Lemma R'_gend_other x : x <> m -> gend (R' x) = gend (R x). Proof. intros NE. rewrite R'_other by exact NE. reflexivity. Qed.
#[using="CEc L BL1 LS rid ai nb needed c X1 INV1 Hg IM"] Lemma sstart_m0 : sstart (R m) 0 = UNIT. Proof. unfold sstart. rewrite gbase_m. cbn. lia. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg IM"] Lemma R'_sstart_m0 : sstart (R' m) 0 = UNIT. Proof. unfold sstart. rewrite R'_gbase, gbase_m. cbn. lia. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg H63 Hnb Hnd IM IG"] Lemma R'_sstart_m1 : sstart (R' m) 1 = needed. Proof. unfold sstart. rewrite R'_gbase, gbase_m, R'_stride_m. cbn. unfold UNIT. lia. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg H63 Hnb Hnd IM IG"] Lemma R'_gend_m : gend (R' m) = needed. Proof. unfold gend. rewrite R'_cnt. unfold cnt_of. rewrite (proj1 g_facts). exact R'_sstart_m1. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg IM"] Lemma R'_slot_start'_m0 : slot_start' (R' m) 0 = slot_start' (R m) 0.
Proof. rewrite !slot_start'_sstart, R'_gbase, R'_sstart_m0, sstart_m0. reflexivity. Qed.

#[using="Type"] Lemma hosts' b x : hosts st' b x <-> hosts st b x. Proof. apply hosts_ext. exact st'_groups. Qed.
#[using="Type"] Lemma live' x : live_group st' x <-> live_group st x. Proof. apply live_group_ext. exact st'_groups. Qed.
#[using="Type"] Lemma get_head' h : get_head st' h = get_head st h. Proof. apply get_head_ext. exact st'_ctx. Qed.
#[using="Type"] Lemma frontier' rid0 r0 : frontier st' rid0 r0 = frontier st rid0 r0. Proof. apply frontier_ext. rewrite st'_ctx. reflexivity. Qed.
#[using="Type"] Lemma gcnt' sc : gcnt st' sc = gcnt st sc.
Proof.
  unfold gcnt. rewrite st'_groups. f_equal. apply map_ext. intros [b h]. cbn. destruct (g_meta h); [| reflexivity].
  rewrite R'_sc, R'_cnt. reflexivity.
Qed.
#[using="Type"] Lemma usage' sc : usage st' sc = usage st sc. Proof. apply usage_ext. rewrite st'_ctx. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma st2_shadow : s_shadow st2 = s_shadow st. Proof. unfold st2, st1. rewrite s_shadow_upd_meta, s_shadow_upd_region. reflexivity. Qed.
#[using="Type"] Lemma st2_tick : s_tick st2 = s_tick st. Proof. unfold st2, st1. rewrite s_tick_upd_meta, s_tick_upd_region. reflexivity. Qed.
#[using="CEc L BL1 LS c X1 INV1"] Lemma read' q : cell_read (get_shadow st' (fst q)) (snd q) =
  if aptr_eqb q e then Known 0 else cell_read (get_shadow st (fst q)) (snd q).
Proof.
  unfold st'. destruct (aptr_eqb_spec q e) as [->|NE].
  - rewrite cell_read_wr8_same; [reflexivity|]. rewrite (get_shadow_ext' st st2 st2_shadow), st2_tick. apply sh_ticks_of. exact (TKS_of _ _ _ _ _ INV1).
  - rewrite (cell_read_wr8_other e 0 st2 q NE). rewrite (get_shadow_ext' st st2 st2_shadow). reflexivity.
Qed.
#[using="CEc L BL1 LS c X1 INV1 Hnb Hnd"] Lemma known' q v : q <> e -> (known st' q v <-> known st q v).
Proof. intros NE. unfold known, SHd. rewrite read', aptr_eqb_neq by exact NE. tauto. Qed.
#[using="CEc L BL1 LS c X1 INV1"] Lemma known'_e : known st' e 0. Proof. unfold known, SHd. rewrite read', aptr_eqb_refl. reflexivity. Qed.
#[using="CEc L BL1 LS c X1 INV1 Hnb Hnd"] Lemma unknown' q : q <> e -> (unknown st' q <-> unknown st q).
Proof. intros NE. unfold unknown, SHd. rewrite read', aptr_eqb_neq by exact NE. tauto. Qed.

(* [comment removed for export] *)
#[using="CEc nb Hnd"] Lemma e_snd : snd e = needed - 4 /\ 4092 <= snd e. Proof. destruct Hnd as (N1 & _). unfold e, IB, PGSZ in *. cbn. lia. Qed.

(* [comment removed for export] *)
#[using="Hr"] Lemma st'_region_some q rq : s_regions st' !! q = Some rq ->
  (q = rid /\ rq = mkRegion (r_kind r) nb needed) \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite st'_region_rid in H. injection H as <-. auto.
  - right. rewrite st'_region_other in H by exact NE. auto.
Qed.
#[using="r Hr"] Lemma st'_region_keep q rq : s_regions st !! q = Some rq -> q <> rid -> s_regions st' !! q = Some rq.
Proof. intros H NE. rewrite st'_region_other by exact NE. exact H. Qed.
#[using="CEc L BL1 LS m ai r nb needed c X1 INV1 Hg H63 Hr IG"] Lemma rid_group q rq : s_regions st !! q = Some rq -> r_kind rq <> RKGroup -> q <> rid.
Proof. intros H K ->. rewrite Hr in H. injection H as <-. apply K. exact (proj1 r_group). Qed.
#[using="CEc L BL1 LS m ai r nb needed c X1 INV1 Hg H63 Hr IG"] Lemma rid_metakind q rq : s_regions st !! q = Some rq -> is_metakind rq -> q <> rid.
Proof. intros H [K|K]; apply (rid_group q rq H); rewrite K; discriminate. Qed.

(* [comment removed for export] *)
#[using="CEc L LS ai nb needed c X1 INV1 Hg H63 Hnb IM IG IS"] Lemma blocks_other k x i : In k BL1 -> s_slots st !! (bslot k) = Some (x, i) -> x <> m /\ fst (bslot k) <> rid.
Proof.
  intros Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  assert (NE : x <> m).
  { intros ->. destruct g_facts as (L0 & _ & _). assert (i = 0) by lia. subst i.
    pose proof (is_part _ _ _ IS _ _ _ 0 Hg ltac:(lia)) as P. cbn zeta in P.
    rewrite <- Es in P. unfold one5 in P. destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CE & _).
    apply CE. split; [apply in_map; exact Hk|]. unfold X1. cbn. rewrite Es, slot_start'_sstart, gbase_m, sstart_m0. reflexivity. }
  split; [exact NE|]. intros Ef. apply NE. rewrite Es, (slot_start'_eq _ _ _ IM _ _ _ Hb) in Ef. cbn in Ef.
  exact (proj1 (region_only b x Hb Ef)).
Qed.

(* [comment removed for export] *)
#[using="CEc BL1 LS ai c X1 INV1 Hg H63 Hr IR IG"] Lemma groups_perm :
  Permutation (ld_groups L')
    (map (fun kr : N * region => (r_base (snd kr), r_len (snd kr)))
       (List.filter (fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) (map_to_list (s_regions st')))).
Proof.
  pose proof (ir_groups _ _ _ IR) as PG. pose proof (proj1 r_group) as KG.
  set (F := fun kr : N * region => match r_kind (snd kr) with RKGroup => true | _ => false end) in *.
  set (g := fun kr : N * region => (r_base (snd kr), r_len (snd kr))) in *.
  (* [comment removed for export] *)
  pose proof (map_to_list_delete (s_regions st) rid r Hr) as PD.
  assert (PG' : Permutation (ld_groups L) ((r_base r, r_len r) :: map g (List.filter F (map_to_list (delete rid (s_regions st)))))).
  { eapply Permutation_trans; [exact PG|]. change ((r_base r, r_len r) :: map g (List.filter F (map_to_list (delete rid (s_regions st)))))
      with (map g ((rid, r) :: List.filter F (map_to_list (delete rid (s_regions st))))).
    apply Permutation_map. rewrite <- (filter_cons_true F (rid, r)) by (unfold F; cbn; rewrite KG; reflexivity).
    apply perm_filter. apply Permutation_sym. exact PD. }
  (* [comment removed for export] *)
  pose proof (group_bases_nodup X1 st L IR) as ND.
  destruct (g_remove_split (r_base r) (r_len r) (ld_groups L) [] ltac:(eapply Permutation_in; [apply Permutation_sym; exact PG'| left; reflexivity]) ltac:(rewrite app_nil_r; exact ND)) as (l1 & l2 & E & Eg).
  assert (PR : Permutation (g_remove (r_base r) (ld_groups L)) (map g (List.filter F (map_to_list (delete rid (s_regions st)))))).
  { rewrite Eg. apply Permutation_cons_inv with (a := (r_base r, r_len r)). eapply Permutation_trans; [| exact PG']. rewrite E. apply Permutation_middle. }
  (* [comment removed for export] *)
  unfold L'. cbn [ld_groups OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups].
  assert (PN : Permutation (map_to_list (s_regions st')) ((rid, mkRegion (r_kind r) nb needed) :: map_to_list (delete rid (s_regions st)))).
  { rewrite st'_regions. rewrite <- insert_delete_eq. apply map_to_list_insert. apply lookup_delete_eq. }
  eapply Permutation_trans; [| apply Permutation_map; apply perm_filter; apply Permutation_sym; exact PN].
  rewrite (filter_cons_true F) by (unfold F; cbn; rewrite KG; reflexivity). cbn [map]. unfold g at 1. cbn [snd r_base r_len].
  apply perm_skip. exact PR.
Qed.

#[using="CEc BL1 LS ai c X1 INV1 Hg H63 Hr IR IG"] Lemma metas_perm :
  Permutation (ld_metas L')
    (map (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st' (fst kr) (snd kr) / PGSZ - 1))
       (List.filter (fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) (map_to_list (s_regions st')))).
Proof.
  pose proof (ir_metas _ _ _ IR) as PM. pose proof (proj1 r_group) as KG.
  set (F := fun kr : N * region => match r_kind (snd kr) with RKMeta => true | _ => false end) in *.
  unfold L'. cbn [ld_metas OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups].
  erewrite (map_ext _ (fun kr : N * region => (r_base (snd kr), r_len (snd kr), frontier st (fst kr) (snd kr) / PGSZ - 1))) by (intros [q rq]; cbn; rewrite frontier'; reflexivity).
  eapply Permutation_trans; [exact PM|]. apply Permutation_map.
  pose proof (map_to_list_delete (s_regions st) rid r Hr) as PD.
  assert (PN : Permutation (map_to_list (s_regions st')) ((rid, mkRegion (r_kind r) nb needed) :: map_to_list (delete rid (s_regions st)))).
  { rewrite st'_regions. rewrite <- insert_delete_eq. apply map_to_list_insert. apply lookup_delete_eq. }
  eapply Permutation_trans; [apply perm_filter; apply Permutation_sym; exact PD|]. eapply Permutation_trans; [| apply perm_filter; apply Permutation_sym; exact PN].
  rewrite !(filter_cons_false F) by (unfold F; cbn; rewrite KG; reflexivity). apply Permutation_refl.
Qed.

#[using="ai INV1 Hg H63 Hr Hnb Hnd DISJ IR IA IM IL IG IS ISH"] Theorem INVL_regroup63 : INVL X1 st' L' BL1 LS.
Proof.
  pose proof IR as IR0. pose proof IA as IA0. pose proof IM as IM0. pose proof IL as IL0. pose proof IG as IG0. pose proof IS as IS0. pose proof ISH as ISH0.
  destruct Hnb as [B0 BA]. destruct Hnd as (N1 & N2 & N3 & N4). destruct g_facts as (L0 & ML & NL). pose proof (proj1 r_group) as KG.
  pose proof needed_div as [D1 D2]. pose proof e_snd as [E1 E2].
  assert (RUP : round_up_pg needed = needed) by (apply round_up_pg_aligned; unfold PGSZ in N2; exact N2).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* [comment removed for export] *) destruct IR0; constructor; rewrite ?st'_next_rid, ?st'_ctx, ?st'_reserved, ?st'_groups.
    + intros q rq Hq. apply st'_region_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids rid r Hr)| exact (ir_ids q rq Hq)].
    + intros q rq Hq. apply st'_region_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn. rewrite RUP.
      split; [lia|]. split; [exact BA|]. split; [unfold PGSZ in N1; lia|]. split; [exact N3|]. split; [lia|]. rewrite KG. intros [K|K]; discriminate.
    + intros q1 q2 r1 r2 H1 H2 NE.
      apply st'_region_some in H1 as [[-> ->]|[N1' H1]]; apply st'_region_some in H2 as [[-> ->]|[N2' H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
      * unfold region_live_range at 1. cbn [r_kind r_base r_len]. rewrite KG, RUP. pose proof (DISJ q2 r2 H2 N2') as D. destruct (region_live_range r2) as [b2 l2]. lia.
      * pose proof (DISJ q1 r1 H1 N1') as D. destruct (region_live_range r1) as [b1 l1].
        unfold region_live_range. cbn [r_kind r_base r_len]. rewrite KG, RUP. lia.
    + exact ir_resv.
    + exact groups_perm.
    + exact metas_perm.
    + intros q rq Hq K. rewrite frontier'. apply st'_region_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite KG in K; discriminate| exact (ir_metalen q rq Hq K)].
    + intros q rq Hq K. rewrite frontier'. apply st'_region_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite KG in K; discriminate| exact (ir_brkfront q rq Hq K)].
    + destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
      right. exists q, rq. split; [apply st'_region_keep; [exact Hq| apply (rid_group q rq Hq); rewrite K; discriminate]| auto].
    + intros b l. unfold L'. cbn [ld_brkreg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups]. rewrite ir_brkreg. split; intros (q & rq & Hq & K & E1' & E2'); exists q, rq.
      * split; [apply st'_region_keep; [exact Hq| apply (rid_group q rq Hq); rewrite K; discriminate]| auto].
      * apply st'_region_some in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite KG in K; discriminate| auto].
    + intros q1 q2 r1 r2 H1 H2 K1 K2. apply st'_region_some in H1 as [[-> ->]|[_ H1]]; [cbn in K1; rewrite KG in K1; discriminate|].
      apply st'_region_some in H2 as [[-> ->]|[_ H2]]; [cbn in K2; rewrite KG in K2; discriminate|]. exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
    + unfold L'. cbn [ld_brk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.set_groups]. revert ir_brk. destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
      * destruct IBK as [B NB]. split; [exact B|]. intros q rq Hq. apply st'_region_some in Hq as [[-> ->]|[_ Hq]]; [cbn; rewrite KG; discriminate| exact (NB q rq Hq)].
      * exact IBK.
      * destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq. split; [apply st'_region_keep; [exact Hq| apply (rid_group _ rq Hq); rewrite K; discriminate]| auto].
    + destruct ir_cursor as (C1 & C2 & C3). split; [exact C1|]. split; [exact C2|].
      intros q off E. destruct (C3 q off E) as (rq & Hq & K & B). exists rq. split; [apply st'_region_keep; [exact Hq| exact (rid_metakind q rq Hq K)]| auto].
    + intros q Hq. cbn in Hq. discriminate.
  - (* [comment removed for export] *) destruct IA0; constructor; rewrite ?st'_ctx, ?st'_areas, ?st'_secret; try assumption.
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
      exists rq. rewrite frontier'. split; [apply st'_region_keep; [exact Hq| exact (rid_metakind _ rq Hq K)]| auto].
    + intros x mr Hm. rewrite st'_metas in Hm. destruct (aptr_eqb_spec x m) as [->|NE].
      * destruct (s_metas st !! m) as [mr0|] eqn:E0; [exact (ia_metas m mr0 E0)| exfalso; exact (g_present _ _ _ _ _ _ GO E0)].
      * rewrite lookup_insert_ne in Hm by congruence. exact (ia_metas x mr Hm).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk). exists a. split; [assumption|]. split; [assumption|].
      intros k Hk2. rewrite st'_metas. destruct (aptr_eqb_spec (mslot a k) m) as [E|NE].
      * exfalso. apply (g_present _ _ _ _ _ _ GO). rewrite <- E. apply Hk. exact Hk2.
      * rewrite lookup_insert_ne by congruence. apply Hk. exact Hk2.
    + intros q Hq. destruct (ia_availptr q Hq) as (rq & Hrq & K). exists rq. split; [apply st'_region_keep; [exact Hrq| exact (rid_metakind _ rq Hrq K)]| exact K].
    + intros sc Hsc. rewrite usage', gcnt'. exact (ia_usage sc Hsc).
  - (* [comment removed for export] *) destruct IM0 as [M1 M2 M3 M4 M5]; constructor.
    + intros x Hm. rewrite R'_mem in Hm. destruct (aptr_eqb_spec x m) as [->|NE]; [rewrite mem_m in Hm; discriminate|]. rewrite R'_other by exact NE. exact (M1 x Hm).
    + intros x b Hm. rewrite R'_mem in Hm. destruct (M2 x b Hm) as [H|H]; [left; apply hosts'; exact H| right; exact H].
    + intros b h Hb. rewrite st'_groups in Hb. destruct (M3 b h Hb) as (x & ? & ? & ?). exists x. rewrite R'_mem, R'_last. auto.
    + intros x Hx. destruct Hx.
    + intros z Hz. destruct Hz.
  - (* [comment removed for export] *) destruct IL0 as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
    + intros h. rewrite get_head'. apply L1.
    + intros h. specialize (L2 h). unfold dll in *. destruct (LS h) as [|a l] eqn:EL; [exact I|].
      eapply linked_ext; [| | exact L2]; intros; [apply R'_next| apply R'_prev].
    + exact L3.
    + exact L4.
    + intros x. rewrite R'_next, R'_prev. exact (L5 x).
    + intros x Hx. assert (NE : x <> m) by (intros ->; apply NL; exists LFree; exact Hx). rewrite R'_other by exact NE. exact (L6 x Hx).
    + intros sc x Hx. rewrite live', R'_sc. exact (L7 sc x Hx).
    + exact L9.
  - (* [comment removed for export] *) destruct IG0 as [G1 G2 G3 G4 G5]. constructor.
    + intros x b ai' Hb. rewrite st'_groups in Hb. pose proof (G1 x b ai' Hb) as GOx.
      destruct (aptr_eqb_spec x m) as [->|NE].
      * (* [comment removed for export] *)
        assert (Eb : b = (rid, 0)) by (exact (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai' Hb) g_hosts)). subst b.
        rewrite Hg in Hb. injection Hb as <-.
        destruct GOx as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16]. constructor; rewrite ?R'_last, ?R'_sc, ?R'_freeable, ?R'_avail, ?R'_freed, ?R'_maplen_m, ?R'_gend_m.
        -- rewrite st'_metas, lookup_insert_eq. discriminate.
        -- exact P2.
        -- exact P3.
        -- right. rewrite H63. repeat split; try reflexivity; try lia. exact NL.
        -- exact P5.
        -- lia.
        -- exact P7.
        -- intros HF Hai. exfalso. lia.
        -- intros HF Hsc. rewrite H63 in Hsc. lia.
        -- intros HF sc Hin. exfalso. apply NL. exists (LActive sc). exact Hin.
        -- intros Hsc. rewrite H63 in Hsc. lia.
        -- intros HF Hsc. rewrite H63 in Hsc. lia.
        -- exact P13.
        -- intros _. split; [reflexivity|]. exists (mkRegion (r_kind r) nb needed). split; [exact st'_region_rid|]. cbn. split; [exact KG|]. rewrite RUP. split; [lia| lia].
        -- intros Z0. exfalso. lia.
        -- intros Hsc. rewrite H63 in Hsc. lia.
      * (* [comment removed for export] *)
        assert (NR : fst b <> rid) by (intros Ef; apply NE; exact (proj1 (region_only b x (ex_intro _ ai' Hb) Ef))).
        destruct GOx as [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16]. constructor; rewrite ?(R'_other x NE); try assumption.
        -- rewrite st'_metas, lookup_insert_ne by congruence. exact P1.
        -- intros HM. destruct (P14 HM) as (S0 & rq & Hq & K & E & GE). split; [exact S0|]. exists rq. split; [apply st'_region_keep; [exact Hq| exact NR]| auto].
        -- intros HM. destruct (P15 HM) as (p & i & Hsl & Hf & GE & SC & STR). exists p, i. rewrite st'_slots.
           assert (NP : p <> m) by (intros ->; rewrite H63 in SC; lia). rewrite !(R'_other p NP). auto 10.
    + intros b ai' Hb. rewrite st'_groups in Hb. exact (G2 b ai' Hb).
    + intros m1 m2 b1 b2 a1 a2 H1 H2 Hl1 Hl2 Hsc. rewrite st'_groups in H1, H2. rewrite !R'_last in *. rewrite !R'_sc in Hsc. exact (G3 m1 m2 b1 b2 a1 a2 H1 H2 Hl1 Hl2 Hsc).
    + intros q rq Hq K _. apply st'_region_some in Hq as [[-> ->]|[NE Hq]].
      * exists m. split; [apply hosts'; exact g_hosts|]. rewrite R'_maplen_m. lia.
      * destruct (G4 q rq Hq K ltac:(cbn; discriminate)) as (x & Hx & HM). exists x. split; [apply hosts'; exact Hx|].
        assert (NX : x <> m) by (intros ->; apply NE; pose proof (hosts_inj _ _ _ IM _ _ _ Hx g_hosts) as EE; injection EE as EE'; exact EE').
        rewrite R'_maplen_other by exact NX. exact HM.
    + intros b h Hb. rewrite st'_groups in Hb. destruct (G5 b h Hb) as (rq & Hq & K). destruct (N.eq_dec (fst b) rid) as [E|NE].
      * exists (mkRegion (r_kind r) nb needed). rewrite E, st'_region_rid. split; [reflexivity| cbn; exact KG].
      * exists rq. split; [apply st'_region_keep; [exact Hq| exact NE]| exact K].
  - (* [comment removed for export] *) destruct IS0 as [S1 S2 S3 S4 S5 S6]; constructor; rewrite ?st'_slots.
    + intros sl x i H. destruct (S1 sl x i H) as (LV & Hi & Es). split; [apply live'; exact LV|]. rewrite R'_last. split; [exact Hi|].
      destruct (aptr_eqb_spec x m) as [->|NE]; [| rewrite R'_slot_start'_other by exact NE; exact Es].
      assert (i = 0) by lia. subst i. rewrite R'_slot_start'_m0. exact Es.
    + intros b x i Hb Hi. apply hosts' in Hb. rewrite R'_last in Hi.
      destruct (aptr_eqb_spec x m) as [->|NE]; [| rewrite R'_slot_start'_other by exact NE; exact (S2 b x i Hb Hi)].
      assert (i = 0) by lia. subst i. rewrite R'_slot_start'_m0. exact (S2 b m 0 Hb Hi).
    + intros b x ai' i Hb Hi. rewrite st'_groups in Hb |- *. rewrite R'_last in Hi. rewrite R'_avail, R'_freed.
      destruct (aptr_eqb_spec x m) as [->|NE]; [| rewrite R'_slot_start'_other by exact NE; exact (S3 b x ai' i Hb Hi)].
      assert (i = 0) by lia. subst i. rewrite R'_slot_start'_m0. exact (S3 b m ai' 0 Hb Hi).
    + exact S4.
    + exact S5.
    + intros k Hk. destruct (S6 k Hk) as (x & i & Hs & Ho & Hz & Hfit). exists x, i. destruct (blocks_other k x i Hk Hs) as [NE _].
      rewrite R'_stride_other by exact NE. auto.
  - (* [comment removed for export] *) destruct ISH0 as [SH1 SH2 SH3 SH4 SH5 SH6]. constructor.
    + intros q sh Hq. unfold st' in Hq. unfold wr8 in Hq. cbn [s_shadow upd_shadow set_shadow] in Hq.
      assert (Hq' : q = rid \/ s_shadow st2 !! q = Some sh).
      { unfold upd_shadow, set_shadow in Hq. cbn in Hq. destruct (N.eq_dec q rid) as [->|NE]; [left; reflexivity| right].
        rewrite lookup_insert_ne in Hq by congruence. exact Hq. }
      destruct Hq' as [->|Hq'].
      * exists (mkRegion (r_kind r) nb needed). split; [exact st'_region_rid| cbn; exact KG].
      * rewrite st2_shadow in Hq'. destruct (SH1 q sh Hq') as (rq & Hrq & K). destruct (N.eq_dec q rid) as [->|NE].
        -- exists (mkRegion (r_kind r) nb needed). split; [exact st'_region_rid| cbn; exact KG].
        -- exists rq. split; [apply st'_region_keep; [exact Hrq| exact NE]| exact K].
    + rewrite st'_tick. unfold st'. rewrite <- st2_tick. apply TKS_wr8; [lia|]. rewrite st2_tick.
      intros q sh Hq. rewrite st2_shadow in Hq. exact (SH2 q sh Hq).
    + intros b x i Hb Hi. apply hosts' in Hb. rewrite R'_cnt in Hi.
      destruct (aptr_eqb_spec x m) as [->|NE].
      * pose proof (hosts_inj _ _ _ IM _ _ _ Hb g_hosts) as ->. cbn [fst]. unfold cnt_of in Hi. rewrite L0 in Hi.
        assert (i = 0 \/ i = 1) as [->| ->] by lia.
        -- rewrite R'_sstart_m0. apply known'; [unfold e; intros E; injection E; unfold UNIT, IB in *; lia|].
           rewrite <- sstart_m0. apply (SH3 (rid, 0) m 0 Hb). unfold cnt_of. lia.
        -- rewrite R'_sstart_m1. replace (rid, needed - IB) with e by reflexivity. exact known'_e.
      * destruct (N.eq_dec (fst b) rid) as [Ef|NR]; [exfalso; apply NE; exact (proj1 (region_only b x Hb Ef))|].
        rewrite R'_sstart_other by exact NE. apply known'; [intros E; apply NR; exact (f_equal fst E)|]. exact (SH3 b x i Hb Hi).
    + intros b x o Hb Ho. apply hosts' in Hb. apply unknown'; [| exact (SH4 b x o Hb Ho)].
      intros E. destruct (N.eq_dec (fst b) rid) as [Ef|NR]; [| apply NR; exact (f_equal fst E)].
      destruct (region_only b x Hb Ef) as [_ Eb]. rewrite Eb in E. apply (f_equal snd) in E. cbn -[Z.add Z.sub] in E. unfold IB, PGSZ in *. lia.
    + intros b x p i Hb HM Hsl. apply hosts' in Hb. rewrite st'_slots in Hsl.
      assert (NE : x <> m) by (intros ->; rewrite R'_maplen_m in HM; lia). rewrite R'_maplen_other in HM by exact NE.
      destruct (N.eq_dec (fst b) rid) as [Ef|NR]; [exfalso; apply NE; exact (proj1 (region_only b x Hb Ef))|].
      rewrite R'_gbase. cbn zeta. pose proof (SH5 b x p i Hb HM Hsl) as ((v3 & K3 & L3 & B3) & K2 & K1 & Q). cbn zeta in K2, K1, Q.
      assert (NRE : forall y, (fst b, y) <> e) by (intros y E; apply NR; exact (f_equal fst E)).
      split; [exists v3; split; [apply known'; [apply NRE| exact K3]| auto]|].
      split; [apply known'; [apply NRE| exact K2]|]. split; [apply known'; [apply NRE| exact K1]| exact Q].
    + intros k x i Hk Hs. rewrite st'_slots in Hs. destruct (blocks_other k x i Hk Hs) as [NE NR].
      rewrite (R'_other x NE). cbn zeta.
      pose proof (SH6 k x i Hk Hs) as B. cbn zeta in B.
      assert (NRE : forall y, (fst (bslot k), y) <> e) by (intros y E; apply NR; exact (f_equal fst E)).
      destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
      split; [apply known'; [apply NRE| exact B1]|]. split; [apply known'; [apply NRE| exact B2]|].
      split; [apply known'; [apply NRE| exact B3]|]. split; [apply known'; [apply NRE| exact B4]|]. split; [exact B5|].
      split; [intros H5; destruct (B6 H5) as (C1 & C2 & C3 & C4 & C5 & C6); repeat (split; [apply known'; [apply NRE| assumption]|]); exact C6|].
      split; [intros H0'; apply known'; [apply NRE| exact (B7 H0')]|].
      intros a Ha. apply unknown'; [apply NRE| exact (B8 a Ha)].
Qed.
End REGROUP63.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BIG63.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off n : Z) (m bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis BF : blk_facts st c off n m bm i ai a ar ka.
Hypothesis H63 : m_sizeclass (MR st m) = 63.
Hypothesis TF : TF0 st.
Variable n' : Z.
Hypothesis Hn' : MMAP_THRESHOLD <= n'.
Hypothesis Hov : size_overflows n' = false.
Hypothesis Hnx : n' + 3 * PGSZ < LEN_MAX.
Local Notation R := (MR st).
Let rid : N := fst c.
Let p : aptr := aadd c (UNIT * off).
Let needed : Z := round_up_pg (n' + UNIT * off + UNIT + IB).
Let oldlen : Z := m_maplen (R m) * 4096.
Let X1 : extras := mkX [] [] (Some c) None None.
Let BL1 := bl_remove c BL.

Let IR := proj1 INV. Let IM := proj1 (proj2 (proj2 INV)). Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))). Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

#[using="CEc L BL c off n i a ar ka INV BF IG"] Lemma b_GO : group_ok x0 st LS m bm ai. Proof. exact (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)). Qed.
#[using="CEc L BL c off n bm ai a ar ka INV BF H63 n' rid needed oldlen IG"] Lemma b_facts : m_last_idx (R m) = 0 /\ m_maplen (R m) <> 0 /\ ~ in_list LS m /\ i = 0.
Proof.
  destruct (g_sc _ _ _ _ _ _ b_GO) as [[H _]|(_ & A & B & C)]; [rewrite H63 in H; lia|]. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF). repeat split; auto. lia.
Qed.
#[using="CEc st L BL LS off n m i ai a ar ka INV BF H63 n' needed oldlen IG"] Lemma b_bm : bm = (rid, 0).
Proof.
  destruct b_facts as (_ & ML & _ & _). destruct (bf_top _ _ _ _ _ _ _ _ _ _ _ BF ML) as [S0 _].
  unfold rid. rewrite (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). cbn [fst]. destruct bm as [b1 b2]. cbn in S0 |- *. subst b2. reflexivity.
Qed.
#[using="CEc L BL LS c off n bm i ai a ar ka INV BF H63 n' rid needed IG"] Lemma b_stride : get_stride (R m) = oldlen - UNIT.
Proof.
  destruct b_facts as (L0 & ML & _ & _). unfold get_stride, oldlen. rewrite L0. cbn [Z.eqb andb].
  replace (m_maplen (R m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). reflexivity.
Qed.
#[using="CEc st L BL LS off n m bm i ai a ar ka INV BF H63 n' needed oldlen IG"] Lemma b_c : c = (rid, UNIT).
Proof.
  destruct b_facts as (_ & _ & _ & I0). pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as E. rewrite b_bm, I0 in E.
  unfold sstart in E. rewrite (gbase_bm st c off n m bm i ai a ar ka BF), b_bm in E. cbn in E. rewrite Z.mul_0_r, Z.add_0_r in E. exact E.
Qed.
#[using="CEc L BL LS off n bm i ai a ar ka INV BF H63 n' needed IG"] Lemma b_region : exists r, s_regions st !! rid = Some r /\ r_kind r = RKGroup /\ oldlen = round_up_pg (r_len r).
Proof.
  destruct b_facts as (_ & ML & _ & _). destruct (g_top _ _ _ _ _ _ b_GO ML) as (_ & r & Hr & K & E & _).
  rewrite b_bm in Hr. cbn [fst] in Hr. exists r. auto.
Qed.
#[using="st c n m bm i ai a ar ka BF Hn' Hov Hnx rid oldlen"] Lemma needed_facts : n' + UNIT * off + UNIT + IB <= needed < n' + UNIT * off + UNIT + IB + PGSZ /\ needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed < LEN_MAX.
Proof.
  pose proof (round_up_pg_spec (n' + UNIT * off + UNIT + IB)) as [[A B] C].
  pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  fold needed in A, B, C. unfold MMAP_THRESHOLD, UNIT, IB, PGSZ, LEN_MAX in *. lia.
Qed.

(* [comment removed for export] *)
#[using="CEc L BL LS n m bm i ai a ar ka INV BF H63 TF Hn' Hov Hnx oldlen IG"] Lemma TFp_of sx : s_tick sx = s_tick st ->
  (forall o v t sh, s_shadow sx !! rid = Some sh -> r_cells sh !! o = Some (v, t) -> o < needed - IB ->
     exists sh0, s_shadow st !! rid = Some sh0 /\ r_cells sh0 !! o = Some (v, t)) ->
  forall sh o v t, s_shadow sx !! (fst c) = Some sh -> r_cells sh !! o = Some (v, t) ->
    snd c + UNIT * off <= o < snd c + UNIT * off + n' -> (t < s_tick sx)%N.
Proof.
  intros TK CELLS sh o v t Hs Hc Ho. pose proof needed_facts as (NF & _). rewrite b_c in Ho. cbn [snd] in Ho.
  destruct (CELLS o v t sh Hs Hc ltac:(unfold UNIT, IB in *; lia)) as (sh0 & Hs0 & Hc0). rewrite TK. exact (TF _ _ _ _ _ Hs0 Hc0).
Qed.

(* [comment removed for export] *)
#[using="n bm ai a ar ka INV Hk BF H63 TF Hn' Hov Hnx X1 IG ISH"] Theorem resize63_INVL : oldlen = needed -> INVL x0 (resize63 st rid needed p n' i) L (((c, off), n') :: BL1) LS.
Proof.
  intros EQ. destruct b_facts as (L0 & ML & NL & I0). pose proof needed_facts as (NF & NM & NP & NX). pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof b_stride as STR. pose proof b_c as Ec. pose proof b_bm as Ebm.
  set (e := (rid, needed - IB)). set (stw := wr8 e 0 st).
  (* [comment removed for export] *)
  assert (K0 : known st e 0).
  { unfold e. replace (needed - IB) with (sstart (R m) 1 - IB).
    2:{ unfold sstart. rewrite (gbase_bm st c off n m bm i ai a ar ka BF), Ebm, STR, <- EQ. cbn [snd]. lia. }
    replace rid with (fst bm) by (rewrite Ebm; reflexivity).
    apply (ish_hdr0 _ _ ISH bm m 1 (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))). unfold cnt_of. lia. }
  assert (RD : forall q, cell_read (get_shadow stw (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q)).
  { intros q. unfold stw. destruct (aptr_eq_dec q e) as [->|NE].
    - rewrite cell_read_wr8_same by (apply sh_ticks_of; exact (TKS_of _ _ _ _ _ INV)). symmetry. exact K0.
    - apply cell_read_wr8_other. exact NE. }
  assert (DOMw : DOMS st stw).
  { unfold stw. apply DOMS_wr8; [exact (DOMS_of _ _ _ _ _ INV)|]. unfold e. cbn [fst]. destruct b_region as (r & Hr & K & _). exists r. auto. }
  assert (TKw : TKS stw (s_tick st)) by (unfold stw; apply TKS_wr8; [lia| exact (TKS_of _ _ _ _ _ INV)]).
  assert (INV1 : INVL X1 stw L BL1 LS).
  { unfold X1, BL1. change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st stw L BL LS ((c, off), n) INV Hk eq_refl (ctrl_eq_wr8 st e 0) eq_refl).
    - intros; apply RD.
    - exact DOMw.
    - exact TKw. }
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (gbase_bm st c off n m bm i ai a ar ka BF) in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _).
  assert (KT : forall q v, known st q v -> known stw q v) by (intros q v Kq; unfold known, SHd in *; rewrite RD; exact Kq).
  rewrite resize63_havoc_last. fold rid. fold e. fold stw.
  assert (EA : e = aadd (aadd bm (UNIT + get_stride (MR stw m) * i)) (get_stride (MR stw m) - IB)).
  { unfold stw. change (MR (wr8 e 0 st) m) with (R m). rewrite STR, Ebm, I0, EQ. unfold e, aadd. cbn. f_equal. lia. }
  rewrite EA.
  assert (Hgb : gbase (MR stw m) = bm) by (change (MR stw m) with (R m); exact (gbase_bm st c off n m bm i ai a ar ka BF)).
  assert (Hcc : c = (fst bm, sstart (MR stw m) i)) by (change (MR stw m) with (R m); exact (bf_c _ _ _ _ _ _ _ _ _ _ _ BF)).
  rewrite (set_size_eq stw c off m bm i Hgb Hcc n').
  change x0 with (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)).
  apply (resize_INVL_tail X1 stw L BL1 LS c off m bm i ai INV1 eq_refl).
  - exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact Hgb.
  - exact Hcc.
  - exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact (bf_li _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact Ho.
  - change (MR stw m) with (R m). exact (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF).
  - unfold MMAP_THRESHOLD in Hn'. lia.
  - unfold p. rewrite Ec. cbn [aadd snd]. unfold UNIT, IB in *. lia.
  - change (MR stw m) with (R m). rewrite STR, EQ. unfold UNIT, IB in *. lia.
  - change (MR stw m) with (R m). rewrite STR, EQ. unfold UNIT, IB, PGSZ in *. lia.
  - apply KT. exact K4.
  - apply KT. exact K2.
  - apply KT. exact K1.
  - exact Q.
  - apply TFp_of; [reflexivity|]. intros o v t sh Hs Hcl Ho'. unfold stw, wr8 in Hs. cbn [s_shadow upd_shadow set_shadow] in Hs.
    unfold upd_shadow, set_shadow in Hs. cbn in Hs. unfold e in Hs. cbn [fst snd] in Hs. rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hcl.
    rewrite lookup_insert_ne in Hcl by lia.
    unfold get_shadow in Hcl. destruct (s_shadow st !! rid) as [sh0|] eqn:E0; [exists sh0; auto|]. cbn in Hcl. rewrite lookup_empty in Hcl. discriminate.
  - (* [comment removed for export] *) unfold p. rewrite Ec. cbn [aadd snd]. change (MR stw m) with (R m). rewrite STR, EQ. lia.
  - change (MR stw m) with (R m). exact ML.
  - change (MR stw m) with (R m). rewrite L0. exact I0.
  - (* [comment removed for export] *) unfold stw. rewrite wr8_cells_at. change (MR (wr8 e 0 st) m) with (R m). rewrite STR, EQ. rewrite Ec. cbn [fst snd]. unfold e.
    replace (UNIT + (needed - UNIT) - IB) with (needed - IB) by lia. rewrite aptr_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Variable r : region.
Hypothesis Hr : s_regions st !! rid = Some r.
Variable nb : Z.
Hypothesis Hnb : 0 < nb /\ nb mod PGSZ = 0 /\ nb + needed <= alloc_ceiling.
Hypothesis DISJ : forall rid' r', s_regions st !! rid' = Some r' -> rid' <> rid ->
  let '(b', l') := region_live_range r' in nb + needed <= b' \/ b' + l' <= nb.
Let L' := set_groups ((nb, needed) :: g_remove (r_base r) (ld_groups L)) L.

#[using="n bm ai a ar ka INV Hk BF H63 TF Hn' Hov Hnx oldlen X1 IG Hr Hnb DISJ"] Theorem big_resize_INVL : INVL x0 (big_resize st m rid nb needed p n' i) L' (((c, off), n') :: BL1) LS.
Proof.
  destruct b_facts as (L0 & ML & NL & I0). pose proof needed_facts as (NF & NM & NP & NX). pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof b_stride as STR. pose proof b_c as Ec. pose proof b_bm as Ebm. destruct Hnb as (B0 & BA & BC).
  assert (HNB : 0 < nb /\ nb mod PGSZ = 0) by (split; assumption).
  assert (HND : PGSZ <= needed /\ needed mod PGSZ = 0 /\ needed < LEN_MAX /\ nb + needed <= alloc_ceiling) by (repeat split; assumption).
  assert (INV1 : INVL X1 st L BL1 LS).
  { unfold X1, BL1. change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st L BL LS ((c, off), n) INV Hk eq_refl (ctrl_eq_refl st) eq_refl).
    - intros; reflexivity.
    - exact (DOMS_of _ _ _ _ _ INV).
    - exact (TKS_of _ _ _ _ _ INV). }
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hg. rewrite Ebm in Hg.
  assert (INV1c : INVL (mkX [] [] (Some (rid, UNIT)) None None) st L BL1 LS) by (rewrite <- Ec; exact INV1).
  pose proof (INVL_regroup63 st L BL1 LS m rid ai r nb needed INV1c Hg H63 Hr HNB HND DISJ) as INV2.
  rewrite <- Ec in INV2. fold X1 in INV2.
  set (st2 := upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st)) in *.
  set (e := (rid, needed - IB)) in *. set (st' := wr8 e 0 st2) in *.
  unfold big_resize. cbv zeta. rewrite resize63_havoc_last.
  change (upd_meta m (m_set_maplen (needed / 4096)) (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st)) with st2. fold rid. fold e. fold st'.
  pose proof (R'_stride_m st L BL1 LS m rid ai nb needed INV1c Hg H63 HNB HND) as STR'. cbv zeta in STR'.
  change (wr8 (rid, needed - IB) 0 (upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st))) with st' in STR'.
  assert (EA : e = aadd (aadd bm (UNIT + get_stride (MR st' m) * i)) (get_stride (MR st' m) - IB)).
  { rewrite STR', Ebm, I0. unfold e, aadd. cbn. f_equal. lia. }
  rewrite EA.
  pose proof (bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF) as SH. unfold blk_shadow_ok in SH. cbn [bslot boff bsize fst snd] in SH.
  rewrite (gbase_bm st c off n m bm i ai a ar ka BF) in SH. destruct SH as (K4 & K3 & K2 & K1 & Q & _).
  assert (KT : forall y v, y < needed - IB -> known st (rid, y) v -> known st' (rid, y) v).
  { intros y v Hy Ky. apply (known' st L BL1 LS m rid nb needed INV1c HNB HND); [| exact Ky]. intros E. injection E. lia. }
  rewrite Ec in K4, K2, K1. cbn [fst snd] in K4, K2, K1.
  assert (Hgb : gbase (MR st' m) = bm) by (rewrite (R'_gbase st m rid nb needed); exact (gbase_bm st c off n m bm i ai a ar ka BF)).
  assert (Hcc : c = (fst bm, sstart (MR st' m) i)) by (rewrite Ebm, I0, Ec; cbn [fst]; rewrite (R'_sstart_m0 st L BL1 LS m rid ai nb needed INV1c Hg); reflexivity).
  rewrite (set_size_eq st' c off m bm i Hgb Hcc n').
  change x0 with (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)).
  apply (resize_INVL_tail X1 st' L' BL1 LS c off m bm i ai INV2 eq_refl).
  - rewrite (st'_groups st m rid nb needed). exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
  - rewrite (st'_slots st m rid nb needed). exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact Hgb.
  - exact Hcc.
  - rewrite (R'_last st m rid nb needed). exact (bf_i _ _ _ _ _ _ _ _ _ _ _ BF).
  - rewrite (R'_last st m rid nb needed). exact (bf_li _ _ _ _ _ _ _ _ _ _ _ BF).
  - exact Ho.
  - rewrite STR'. unfold UNIT, PGSZ in *. split; [lia|].
    replace (needed - 16) with ((needed / 4096 * 256 - 1) * 16) by (pose proof (Z_div_mod_eq_full needed 4096); lia). apply Z_mod_mult.
  - exact (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF).
  - unfold MMAP_THRESHOLD in Hn'. lia.
  - unfold p. rewrite Ec. cbn [aadd snd]. unfold UNIT, IB in *. lia.
  - rewrite STR'. unfold UNIT, IB in *. lia.
  - rewrite STR'. unfold UNIT, IB, PGSZ in *. lia.
  - rewrite Ec. cbn [fst snd]. apply KT; [unfold MMAP_THRESHOLD, UNIT, IB in *; lia| exact K4].
  - rewrite Ec. cbn [fst snd]. apply KT; [unfold MMAP_THRESHOLD, UNIT, IB in *; lia| exact K2].
  - rewrite Ec. cbn [fst snd]. apply KT; [unfold MMAP_THRESHOLD, UNIT, IB in *; lia| exact K1].
  - rewrite Ec in Q |- *. cbn [fst snd] in Q |- *. exact Q.
  - apply TFp_of; [apply (st'_tick st m rid nb needed)|].
    intros o v t sh Hs Hcl Ho'. unfold st', wr8 in Hs. cbn [s_shadow upd_shadow set_shadow] in Hs.
    unfold upd_shadow, set_shadow in Hs. cbn in Hs. unfold e in Hs. cbn [fst snd] in Hs. rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hcl.
    rewrite lookup_insert_ne in Hcl by lia.
    match type of Hcl with context [get_shadow ?sx rid] => replace (get_shadow sx rid) with (get_shadow st rid) in Hcl by (apply get_shadow_ext; symmetry; apply (st2_shadow st m rid nb needed)) end.
    unfold get_shadow in Hcl. destruct (s_shadow st !! rid) as [sh0|] eqn:E0; [exists sh0; auto|]. cbn in Hcl. rewrite lookup_empty in Hcl. discriminate.
  - (* [comment removed for export] *) unfold p. rewrite STR'. rewrite Ec. cbn [aadd fst snd]. lia.
  - pose proof (R'_maplen_m st m rid nb needed HND) as MLN. cbv zeta in MLN.
    change (wr8 (rid, needed - IB) 0 (upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st))) with st' in MLN.
    rewrite MLN. pose proof (Z.div_le_lower_bound needed 4096 1). unfold PGSZ in *. lia.
  - rewrite (R'_last st m rid nb needed). rewrite L0. exact I0.
  - (* [comment removed for export] *) rewrite STR'. rewrite Ec. cbn [fst snd]. unfold st'. rewrite wr8_cells_at. unfold e.
    replace (UNIT + (needed - UNIT) - IB) with (needed - IB) by lia. rewrite aptr_eqb_refl. reflexivity.
Qed.
End BIG63.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ranges_free_regions_wo st rid x n rid' r' :
  ranges_free (live_ranges_wo st rid) x n = true -> s_regions st !! rid' = Some r' -> rid' <> rid ->
  let '(b, l) := region_live_range r' in x + n <= b \/ b + l <= x.
Proof.
  intros H Hr NE. unfold ranges_free in H. rewrite forallb_forall in H.
  specialize (H (region_live_range r')). destruct (region_live_range r') as [b l] eqn:E.
  assert (Hin : In (b, l) (live_ranges_wo st rid)).
  { unfold live_ranges_wo. apply in_app_iff. right. apply in_map_iff. exists (rid', r'). rewrite <- E. split; [reflexivity|].
    apply (proj2 (in_filter_ne rid (rid', r') _)). split; [apply In_map_to_list_regions; exact Hr| exact NE]. }
  specialize (H Hin). cbn in H. unfold iv_disjoint in H. apply Bool.orb_true_iff in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

#[using="Type"] Lemma region_live_range_pos X st L q rq : inv_R X st L -> s_regions st !! q = Some rq ->
  let '(b, l) := region_live_range rq in 0 < l.
Proof.
  intros IR Hq. pose proof (ir_shape _ _ _ IR _ _ Hq) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (round_up_ge (r_len rq)).
  unfold region_live_range. destruct (r_kind rq) eqn:K; try lia.
  destruct (S6 ltac:(left; exact K)) as [M1 M2]. rewrite round_up_pg_aligned by (unfold PGSZ in M1; exact M1). unfold PGSZ in *. lia.
Qed.

#[using="Type"] Lemma is_err_false_not_errno z : is_err z = false -> is_errno_form z = false.
Proof. unfold is_err, is_errno_form. intros H. apply Z.ltb_ge in H. apply andb_false_iff. left. apply Z.leb_gt. lia. Qed.

#[using="Type"] Theorem realloc_ft st0 L BL LS c off n n' :
  INVL x0 st0 L BL LS -> In ((c, off), n) BL -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX ->
  ftree L (realloc st0 (Some (aadd c (UNIT * off))) n') (realloc_post st0 BL c n').
Proof.
  intros INV0 Hk Hn' Hov Hnx.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  rewrite (realloc_eq st0 c off n m bm i ai a ar ka n' BF Hov). fold st.
  assert (MRE : MR st m = MR st0 m) by reflexivity.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (ip_ea_snd st c off m bm i (gbase_bm st c off n m bm i ai a ar ka BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) n') as EAS. cbn zeta in EAS.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold realloc_body.
  match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EC end.
  - (* [comment removed for export] *)
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
    rewrite EAS in E1. cbn [aadd snd] in E1.
    assert (Hsc : m_sizeclass (MR st m) < 48).
    { pose proof (size_to_class_ok n' ltac:(lia)) as [ST _]. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H63]; lia. }
    pose proof (stride_small x0 st L BL LS c off n m bm i ai a ar ka INV BF Hsc) as SS.
    apply ftree_ret. unfold realloc_post. cbn [fst snd]. exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
    apply (inplace_INVL x0 st L BL LS c off n m bm i ai a ar ka INV eq_refl Hk BF TF n' Hn'); unfold IB, UNIT in *; lia.
  - match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EB end.
    + (* [comment removed for export] *)
      apply andb_prop in EB as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
      assert (H63 : m_sizeclass (MR st m) = 63) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H]; [lia| exact H]).
      apply ftree_guard; [apply Z.eqb_eq; exact H63|].
      rewrite (start_eq st c off n m bm i ai a ar ka BF). cbn [aadd fst snd].
      replace (snd c + UNIT * off - snd c) with (UNIT * off) by lia.
      destruct (b_facts st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (L0 & ML & NL & I0).
      destruct (b_region st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (r & Hr & KG & OL).
      pose proof (needed_facts st c off n m bm i ai a ar ka BF n' B2 Hov Hnx) as (NF & NM & NP & NX). cbv zeta in NF, NM, NP, NX.
      set (needed := round_up_pg (n' + UNIT * off + UNIT + IB)) in *.
      set (oldlen := m_maplen (MR st m) * 4096) in *.
      assert (Ebase : conc st (fst c, 0) = r_base r) by (rewrite (conc_eq st (fst c, 0) r Hr); cbn; lia).
      rewrite Ebase.
      pose proof (ir_shape _ _ _ IR _ _ Hr) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
      destruct (Z.eqb_spec oldlen needed) as [EQ|NEQ].
      * apply ftree_ret. unfold realloc_post. cbn [fst snd]. exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
        exact (resize63_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx EQ).
      * cbn [ftree is_peek is_undef]. split.
        -- (* [comment removed for export] *)
           split; [exact (brk_quiet_of _ _ _ IR)|]. split; [exists (r_len r); split; [exact (group_region_in_ledger _ _ _ _ _ IR Hr KG)| symmetry; exact OL]|].
           split; [split; [unfold PGSZ in NP; lia| exact NX]|]. split; [exact NM| exact NEQ].
        -- intros z. cbn [answer_ok]. rewrite (mremap_answer_ok_eq x0 st L IR (fst c) r Hr KG oldlen needed z).
           destruct (mremap_answer_ok st (fst c) (r_base r) oldlen needed z) eqn:OK; cbn [negb]; [| exact I].
           cbn [event_post]. destruct (is_err z) eqn:ERR.
           ++ apply (fallback_ft st L BL LS c off n n' INV Hk Hn').
           ++ apply ftree_ret. unfold realloc_post. cbn [fst snd]. exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
              (* [comment removed for export] *)
              unfold mremap_answer_ok in OK. rewrite (is_err_false_not_errno z ERR) in OK. cbn [orb] in OK.
              apply (big_resize_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx r Hr z).
              ** apply Bool.orb_true_iff in OK. destruct OK as [OK|OK].
                 +++ apply andb_prop in OK as [Ez OK]. apply Z.eqb_eq in Ez. subst z. split; [lia|]. split; [exact RS2|].
                     apply Bool.orb_true_iff in OK. destruct OK as [LE|OK]; [apply Z.leb_le in LE; rewrite OL in *; fold needed in LE |- *; lia|].
                     apply andb_prop in OK as [CE _]. apply Z.leb_le in CE. exact CE.
                 +++ apply andb_prop in OK as [OK RFz]. apply andb_prop in OK as [OK CE]. apply andb_prop in OK as [OK AL]. apply andb_prop in OK as [NEz POS].
                     apply Z.ltb_lt in POS. apply Z.eqb_eq in AL. apply Z.leb_le in CE. repeat split; assumption.
              ** intros rid' r' Hr' NE'. apply Bool.orb_true_iff in OK. destruct OK as [OK|OK].
                 +++ apply andb_prop in OK as [Ez OK]. apply Z.eqb_eq in Ez. subst z.
                     pose proof (ir_disj _ _ _ IR (fst c) rid' r r' Hr Hr' ltac:(congruence)) as D. unfold region_live_range at 1 in D. rewrite KG in D. rewrite <- OL in D.
                     destruct (region_live_range r') as [b' l'] eqn:ER.
                     apply Bool.orb_true_iff in OK. destruct OK as [LE|OK]; [apply Z.leb_le in LE; lia|].
                     apply andb_prop in OK as [_ RF]. pose proof (ranges_free_regions_wo st (fst c) _ _ rid' r' RF Hr' NE') as D2. rewrite ER in D2.
                     pose proof (region_live_range_pos x0 st L rid' r' IR Hr') as P2. rewrite ER in P2. first [ solve [ clear - D D2 P2; lia ] | lia ].   (* [comment removed for export] *)
                 +++ apply andb_prop in OK as [OK RFz]. pose proof (ranges_free_regions st _ _ rid' r' RFz Hr') as D2. destruct (region_live_range r') as [b' l']. exact D2.
    + apply (fallback_ft st L BL LS c off n n' INV Hk Hn').
Qed.

End WithCeil.
End MI_Realloc3.

(* [comment removed for export] *)
Module ProgFull.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section WithCeil.
Context {CE : CEIL}.
Section Full.
Context {St : Type} {AS : AllocSt St}.
Local Notation MP := (Monad.M St).

(* [comment removed for export] *)
Variable peek : Z -> MP Z.
Hypothesis peek_spec : forall caddr (P : assn St),
  mspec P (peek caddr) (fun v s mo => 0 <= v < 256 /\ P s mo).

(* [comment removed for export] *)
Definition ev_stepF (e : ev) : MP Z :=
  match e with
  | EPeek _ caddr _ => peek caddr
  | _ => ev_step e
  end.

Fixpoint membedF {R} (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_stepF e ;; membedF (k z)
  end.

(* [comment removed for export] *)
Inductive fpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| fpath_ret L r : fpath L (SRet r) L r
| fpath_vis L e k z L' r :
    is_peek e = false -> answer_ok L e z = true -> fpath (event_post L e z) (k z) L' r -> fpath L (SVis e k) L' r
| fpath_peek L p c h k v L' r :
    0 <= v < 256 -> fpath L (k v) L' r -> fpath L (SVis (EPeek p c h) k) L' r.

#[using="Type"] Lemma fpath_live {R} : forall L (t : stree ev Z R) L' r, fpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity| rewrite IHfpath; apply event_post_live| exact IHfpath]. Qed.

#[using="Type"] Lemma fpath_post {R} : forall L (t : stree ev Z R) Post L' r, ftree L t Post -> fpath L t L' r -> Post L' r.
Proof.
  intros L t Post L' r Hf Hp. induction Hp as [L r|L e k z L' r Hpk Hans Hp IH|L p c h k v L' r Hv Hp IH].
  - exact Hf.
  - cbn [ftree] in Hf. destruct e; cbn in Hpk; try discriminate; try (destruct Hf; fail);
      destruct Hf as [_ Hk]; specialize (Hk z); rewrite Hans in Hk; exact (IH Hk).
  - cbn [ftree] in Hf. exact (IH (Hf v Hv)).
Qed.

(* [comment removed for export] *)
#[using="peek_spec"] Lemma membedF_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : St -> Model -> Prop) L s0,
  frame_ok G -> ftree L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membedF t)
        (fun r s mo => exists L', fpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_rest s = ps_rest s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membedF]. apply mspec_ret. intros s mo (-> & HK & HGs). exists L.
    split; [constructor|]. cbn in Hok. split; [exact Hok|]. split; [exact HK|]. split; [exact HGs|]. split; reflexivity.
  - cbn [membedF]. cbn [ftree] in Hok.
    destruct (is_peek e) eqn:Ep.
    + (* [comment removed for export] *)
      destruct e as [| | | |p c h| |]; cbn in Ep; try discriminate. cbn [ev_stepF].
      eapply mspec_bind; [apply peek_spec|].
      intros v. cbn beta. apply mspec_pointwise. intros s1 mo1 (Hv & -> & HK1 & HG1).
      eapply mspec_conseq; [apply (IH v Post G L s0 HG (Hok v Hv))| |].
      * intros s mo [-> ->]. auto.
      * intros r s mo (L' & Hp & HP & HK & HG' & Hm & Hx). exists L'. split; [eapply fpath_peek; eauto|].
        split; [exact HP|]. split; [exact HK|]. split; [exact HG'|]. split; assumption.
    + (* [comment removed for export] *)
      assert (Hev : event_pre L e /\ (forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a))
                    /\ ev_stepF e = ev_step e).
      { destruct e; cbn in Ep; try discriminate; cbn [ftree] in Hok; try (destruct Hok; fail); destruct Hok as [H1 H2]; auto. }
      destruct Hev as (Hpre & Hk & ->).
      eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
      intros z. unfold ev_step_post. apply mspec_pointwise. intros s1 mo1 (Hans & HK1 & HG1 & Hm & Hx1).
      specialize (Hk z). rewrite Hans in Hk.
      eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG Hk)| |].
      * intros s mo [-> ->]. auto.
      * intros r s mo (L' & Hp & HP & HK & HG' & Hm' & Hx'). exists L'. split; [eapply fpath_vis; eauto|].
        split; [exact HP|]. split; [exact HK|]. split; [exact HG'|]. split; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bptrF (k : blk) : aptr := aadd (bslot k) (UNIT * boff k).

(* [comment removed for export] *)
Definition FOWN (BL : list blk) (G : St -> Model -> Prop) : assn St := fun s mo =>
  (exists L LS, INVL x0 (ps_m s) L BL LS /\ KL L (ps_brk s) mo) /\ G s mo.

Definition raw_mallocF (n : Z) : MP (option aptr) :=
  s <- mget ;;
  '(st', p) <- membedF (malloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret p.

Definition raw_freeF (p : aptr) : MP unit :=
  s <- mget ;;
  st' <- membedF (free (ps_m s) (Some p)) ;;
  mupd (set_m st').

Definition raw_reallocF (p : optr) (n : Z) : MP (option aptr) :=
  s <- mget ;;
  '(st', q) <- membedF (realloc (ps_m s) p n) ;;
  mupd (set_m st') ;;;
  mret q.

Definition raw_callocF (m n : Z) : MP (option aptr) :=
  s <- mget ;;
  '(st', q) <- membedF (calloc (ps_m s) m n) ;;
  mupd (set_m st') ;;;
  mret q.

(* [comment removed for export] *)
Definition ptr_addrF (s : St) (p : aptr) : Z := conc (ps_m s) p.

#[using="peek_spec"] Lemma raw_mallocF_spec : forall BL G n, frame_ok G -> 0 <= n ->
  mspec (FOWN BL G) (raw_mallocF n)
        (fun r s mo => match r with
                       | Some p => exists c off, p = aadd c (UNIT * off) /\ 0 <= off <= 255
                                   /\ ~ In c (map bslot BL) /\ FOWN (((c, off), n) :: BL) G s mo
                       | None => FOWN BL G s mo
                       end).
Proof.
  intros BL G n HG Hn. unfold raw_mallocF.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & LS & INV & HK) HGs]].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_spec (malloc (ps_m s1) n) _ G L s1 HG (malloc_INVL (ps_m s1) L BL LS n INV Hn))|].
    intros s mo [-> ->]. auto. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hx).
  cbn [fst snd] in HPost. destruct HPost as (LIVE & _ & RES).
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->]. unfold FOWN. autorewrite with alloc_lens.
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']. }
  destruct p as [p|].
  - destruct RES as (c & off & LS' & Hp' & Hoff & INV' & Hni). exists c, off. split; [exact Hp'|]. split; [exact Hoff|]. split; [exact Hni|].
    split; [| exact HG2]. exists L', LS'. split; [exact INV'| exact HK'].
  - destruct RES as (LS' & INV'). split; [| exact HG2]. exists L', LS'. split; [exact INV'| exact HK'].
Qed.

#[using="peek_spec"] Lemma raw_freeF_spec : forall BL G c off n, frame_ok G -> In ((c, off), n) BL ->
  mspec (FOWN BL G) (raw_freeF (aadd c (UNIT * off))) (fun _ => FOWN (bl_remove c BL) G).
Proof.
  intros BL G c off n HG Hin. unfold raw_freeF.
  eapply mspec_bind; [apply mspec_get|]. intros s0.
  apply mspec_pointwise. intros s1 mo1 [-> [(L & LS & INV & HK) HGs]].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_spec (free (ps_m s1) (Some (aadd c (UNIT * off)))) _ G L s1 HG (free_INVL_closed (ps_m s1) L BL LS c off n INV Hin))|].
    intros s mo [-> ->]. auto. }
  intros st'. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HG' & Hm & Hx).
  apply mspec_upd'. intros s mo [-> ->]. unfold FOWN. autorewrite with alloc_lens.
  destruct HPost as (LS' & INV').
  split; [| apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']].
  exists L', LS'. split; [exact INV'| exact HK'].
Qed.

End Full.

(* [comment removed for export] *)
Definition peekG {St : Type} (caddr : Z) : Monad.M St Z :=
  msys (NPeek caddr) (fun rsp => Some (dec_peek rsp)).

#[using="Type"] Lemma peekG_spec {St : Type} : forall caddr (P : assn St),
  mspec P (peekG caddr) (fun v s mo => 0 <= v < 256 /\ P s mo).
Proof.
  intros caddr P. unfold peekG. apply mspec_sys. intros s mo HP. split; [exact I|].
  intros rsp mo' evs Hst. destruct (nstep_dec_peek _ _ _ _ _ Hst) as (-> & -> & Hv & _).
  exists (dec_peek rsp). split; [reflexivity|]. split; [exact Hv| exact HP].
Qed.

End WithCeil.
End ProgFull.

(* [comment removed for export] *)
Module MI_Stable.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.
Set Implicit Arguments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Fixpoint aleaf {R} (P : R -> Prop) (t : M R) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis (EUndef _) _ => True
  | SVis _ k => forall z, aleaf P (k z)
  end.

#[using="Type"] Lemma aleaf_ret {R} (P : R -> Prop) r : P r -> aleaf P (SRet r).
Proof. exact (fun H => H). Qed.

#[using="Type"] Lemma aleaf_vis {R} (P : R -> Prop) e k : (forall z, aleaf P (k z)) -> aleaf P (SVis e k).
Proof. intros H. destruct e; cbn; auto. Qed.

#[using="Type"] Lemma aleaf_mono {R} (P Q : R -> Prop) : (forall r, P r -> Q r) -> forall t, aleaf P t -> aleaf Q t.
Proof.
  intros HPQ. induction t as [r|e k IH]; cbn; [auto|].
  destruct e; intros H; try (intros z; apply IH; apply H). exact I.
Qed.

#[using="Type"] Lemma aleaf_bind {R S} (P : R -> Prop) (Q : S -> Prop) (t : M R) (f : R -> M S) :
  aleaf P t -> (forall r, P r -> aleaf Q (f r)) -> aleaf Q (sbind t f).
Proof.
  revert t. induction t as [r|e k IH]; intros Ht Hf; cbn [sbind]; [apply Hf; exact Ht|].
  destruct e; cbn in Ht |- *; auto.
Qed.

#[using="Type"] Lemma aleaf_guard {R} (P : R -> Prop) tag c (k bail : M R) : aleaf P k -> aleaf P (guard tag c k bail).
Proof. intros H. unfold guard. destruct c; [exact H| exact I]. Qed.

#[using="Type"] Lemma aleaf_bad {R} (P : R -> Prop) (bail : M R) : aleaf P (bad_answer bail).
Proof. exact I. Qed.

#[using="Type"] Lemma aleaf_rd8 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, aleaf P (k v)) -> aleaf P (rd8 st p k).
Proof. intros H. unfold rd8. destruct (cell_read _ _); [apply H|]. cbn. intros v. destruct (peek_answer_ok v); [apply H| exact I]. Qed.

#[using="Type"] Lemma aleaf_rd16 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, aleaf P (k v)) -> aleaf P (rd16 st p k).
Proof. intros H. unfold rd16. apply aleaf_rd8. intros; apply aleaf_rd8. intros; apply H. Qed.

#[using="Type"] Lemma aleaf_rd32 {R} (P : R -> Prop) st p (k : Z -> M R) : (forall v, aleaf P (k v)) -> aleaf P (rd32 st p k).
Proof. intros H. unfold rd32. repeat (apply aleaf_rd8; intros). apply H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fpath_aleaf {R} (P : R -> Prop) (t : M R) L L' r :
  aleaf P t -> fpath L t L' r -> P r.
Proof.
  intros Ha Hp. induction Hp as [L0 r0|L0 e k z L1 r0 He Hz Hp IH|L0 p c h k v L1 r0 Hv Hp IH].
  - exact Ha.
  - apply IH. destruct e; cbn in He, Hz, Ha; try discriminate; auto.
  - apply IH. exact (Ha v).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rsub (st0 st : mstate) : Prop :=
  forall rid r, s_regions st !! rid = Some r -> s_regions st0 !! rid = Some r.

#[using="Type"] Lemma rsub_refl st : rsub st st. Proof. intros rid r H; exact H. Qed.
#[using="Type"] Lemma rsub_eq st0 st st' : s_regions st' = s_regions st -> rsub st0 st -> rsub st0 st'.
Proof. intros E H rid r. rewrite E. apply H. Qed.
#[using="Type"] Lemma rsub_drop st0 st rid : rsub st0 st -> rsub st0 (drop_region rid st).
Proof.
  intros H rid' r. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions.
  destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite lookup_delete_eq; discriminate|]. rewrite lookup_delete_ne by congruence. apply H.
Qed.

#[using="Type"] Lemma queue_aleaf {R} (P : R -> Prop) h m st (k : mstate -> M R) bail :
  (forall st', s_regions st' = s_regions st -> aleaf P (k st')) -> aleaf P (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply aleaf_guard, aleaf_guard.
  destruct (get_head st h) as [hd|]; [destruct (m_prev (get_meta_rec st hd))|]; apply Hk; (destruct h; reflexivity).
Qed.

#[using="Type"] Lemma free_meta_aleaf {R} (P : R -> Prop) m st (k : mstate -> M R) bail :
  (forall st', s_regions st' = s_regions st -> aleaf P (k st')) -> aleaf P (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply queue_aleaf. intros st' E. apply Hk. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma activate_group_aleaf {R} (P : R -> Prop) m st (k : mstate -> Z -> M R) bail :
  (forall st' z, s_regions st' = s_regions st -> aleaf P (k st' z)) -> aleaf P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply aleaf_guard. apply Hk. reflexivity. Qed.

#[using="Type"] Lemma get_meta_aleaf {R} (P : R -> Prop) st p (k : aptr -> Z -> Z -> M R) bail :
  (forall m off idx, aleaf P (k m off idx)) -> aleaf P (get_meta st p k bail).
Proof.
  intros Hk. unfold get_meta. apply aleaf_guard. apply aleaf_rd16. intros o16. cbv beta. apply aleaf_rd8. intros b3. cbv beta. apply aleaf_rd8. intros b4. cbv beta.
  destruct (negb (b4 =? 0)).
  - apply aleaf_guard. apply aleaf_rd32. intros o32. cbv beta. apply aleaf_guard.
    destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply aleaf_guard. apply Hk.
  - destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply aleaf_guard. apply Hk.
Qed.

#[using="Type"] Lemma get_nominal_size_aleaf {R} (P : R -> Prop) st p e (k : Z -> M R) bail :
  (forall v, aleaf P (k v)) -> aleaf P (get_nominal_size st p e k bail).
Proof.
  intros Hk. unfold get_nominal_size. apply aleaf_rd8. intros b3.
  assert (C : forall reserved, aleaf P (guard 22 (reserved <=? snd e - snd p)
     (rd8 st (aadd e (- reserved)) (fun cb => guard 23 (cb =? 0) (rd8 st e (fun eb => guard 24 (eb =? 0) (k (snd e - reserved - snd p)) bail)) bail)) bail)).
  { intros reserved. apply aleaf_guard. apply aleaf_rd8. intros. apply aleaf_guard. apply aleaf_rd8. intros. apply aleaf_guard. apply Hk. }
  destruct (5 <=? Z.shiftr b3 5); [| apply C].
  apply aleaf_guard. apply aleaf_rd32. intros. apply aleaf_guard. apply aleaf_rd8. intros. apply aleaf_guard. apply C.
Qed.

#[using="Type"] Lemma dec_hdr_aleaf R' (P' : R' -> Prop) st p (k' : aptr -> Z -> M R') bail' :
  (forall m idx, aleaf P' (k' m idx)) -> aleaf P' (@dec_hdr R' st p k' bail').
Proof. intros Hk. unfold dec_hdr. apply get_meta_aleaf. intros; apply Hk. Qed.

#[using="Type"] Lemma free_group_aleaf {R} (P : R -> Prop) (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R) st g (k : mstate -> mapinfo -> M R) bail :
  (forall st1 m i k1 bail1, (forall st' mi, s_regions st' = s_regions st1 -> aleaf P (k1 st' mi)) -> aleaf P (rec st1 m i k1 bail1)) ->
  (forall st' mi, s_regions st' = s_regions st -> aleaf P (k st' mi)) ->
  aleaf P (free_group R (@dec_hdr R) rec st g k bail).
Proof.
  intros Hrec Hk. unfold free_group.
  set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else _).
  assert (E1 : s_regions st1 = s_regions st) by (subst st1; destruct (_ <? 48); reflexivity).
  destruct (m_mem _) as [p|]; [| exact I].
  destruct (negb (m_maplen _ =? 0)).
  - apply free_meta_aleaf. intros st' E'. apply Hk. rewrite E', s_regions_record_seq, s_regions_step_seq, s_regions_del_slots. unfold del_group. rewrite s_regions_set_groups. exact E1.
  - apply dec_hdr_aleaf. intros m idx. apply Hrec. intros st3 mi E3. apply free_meta_aleaf. intros st4 E4. apply Hk.
    rewrite E4, E3, s_regions_del_slots. unfold del_group. rewrite s_regions_set_groups. exact E1.
Qed.

#[using="Type"] Lemma nontrivial_free_aleaf {R} (P : R -> Prop) : forall fuel st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st' mi, s_regions st' = s_regions st -> aleaf P (k st' mi)) -> aleaf P (nontrivial_free (@dec_hdr R) fuel st g i k bail).
Proof.
  induction fuel as [|f IH]; intros st g i k bail Hk; cbn [nontrivial_free]; [exact I|].
  match goal with |- aleaf P (if ?c then _ else _) => destruct c end.
  - assert (FG : forall st', s_regions st' = s_regions st -> aleaf P (free_group R (@dec_hdr R) (nontrivial_free (@dec_hdr R) f) st' g k bail)).
    { intros st' E'. apply free_group_aleaf; [intros; apply IH; assumption|]. intros st'' mi E''. apply Hk. congruence. }
    destruct (m_next _); [| apply FG; reflexivity]. apply aleaf_guard.
    destruct (optr_eqb _ _); [| apply FG; apply s_regions_dequeue]. destruct (active _ _); [| apply FG; apply s_regions_dequeue].
    apply activate_group_aleaf. intros st' z E'. apply FG. rewrite E'. apply s_regions_dequeue.
  - destruct (_ =? 0); [| apply Hk; apply s_regions_upd_meta]. apply aleaf_guard.
    destruct (negb _); [| apply Hk; apply s_regions_upd_meta].
    apply queue_aleaf. intros st' E'. apply Hk. rewrite s_regions_upd_meta. exact E'.
Qed.

#[using="Type"] Theorem free_regions st p : aleaf (rsub st) (free st (Some p)).
Proof.
  unfold free. eapply aleaf_bind with (P := fun r => match r with Some (st1, _, _) => s_regions st1 = s_regions st | None => True end).
  { unfold free_hdr. apply get_meta_aleaf. intros m off idx. destruct (slot_start _ _); [| exact I].
    apply get_nominal_size_aleaf. intros v. cbn. reflexivity. }
  intros [[[st1 g] idx]|] E1; [| apply rsub_refl].
  unfold free_tail. apply aleaf_guard. destruct (negb _).
  { cbn. apply (rsub_eq (st:=st)); [rewrite s_regions_upd_meta; exact E1| apply rsub_refl]. }
  apply nontrivial_free_aleaf. intros st2 [[base len]|] E2.
  - destruct (negb (len =? 0)).
    + cbn. intros z. destruct (munmap_answer_ok z); [| exact I]. cbn. apply rsub_drop. apply (rsub_eq (st:=st)); [congruence| apply rsub_refl].
    + cbn. apply (rsub_eq (st:=st)); [congruence| apply rsub_refl].
  - cbn. apply (rsub_eq (st:=st)); [congruence| apply rsub_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma blk_region X st L BL LS k : INVL X st L BL LS -> In k BL ->
  exists r, s_regions st !! (fst (bslot k)) = Some r /\ r_kind r = RKGroup.
Proof.
  intros INV Hk. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_blocks _ _ _ IS k Hk) as (m & i & Hs & _).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es).
  rewrite (slot_start'_eq _ _ _ IM _ _ _ Hb) in Es. rewrite Es. cbn [fst].
  destruct Hb as [ai Hb']. exact (ig_region _ _ _ IG _ _ Hb').
Qed.

#[using="Type"] Lemma conc_aadd st p d : conc st (aadd p d) = match get_region st (fst p) with Some r => r_base r + (snd p + d) | None => 0 end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem free_conc_stable X st L BL LS c off n st' (Lp L' : mled) :
  INVL X st L BL LS -> In ((c, off), n) BL ->
  fpath Lp (free st (Some (aadd c (UNIT * off)))) L' st' ->
  (exists LS', INVL X st' L' (bl_remove c BL) LS') ->
  forall k d, In k (bl_remove c BL) -> conc st' (aadd (bslot k) d) = conc st (aadd (bslot k) d).
Proof.
  intros INV Hin FP [LS' INV'] k d Hk.
  pose proof (fpath_aleaf _ (free_regions st (aadd c (UNIT * off))) FP) as RS. cbn beta in RS.
  destruct (blk_region _ INV' Hk) as (r' & Hr' & _).
  rewrite !conc_aadd. unfold get_region. rewrite Hr', (RS _ _ Hr'). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem malloc_conc_stable X st L BL LS n st' (res : optr) (L' : mled) Post :
  INVL X st L BL LS ->
  fpath L (malloc st n) L' (st', res) ->
  ftree L (malloc st n) Post -> (forall L1 r, Post L1 r -> GP st (fst r)) ->
  forall k d, In k BL -> conc st' (aadd (bslot k) d) = conc st (aadd (bslot k) d).
Proof.
  intros INV FP FT HGP k d Hk.
  pose proof (HGP _ _ (fpath_post _ _ _ _ _ FT FP)) as [G _]. cbn [fst] in G.
  destruct (blk_region _ INV Hk) as (r & Hr & K).
  rewrite !conc_aadd. unfold get_region. rewrite Hr, (G _ _ Hr K). reflexivity.
Qed.

(* [comment removed for export] *)

End WithCeil.
End MI_Stable.
