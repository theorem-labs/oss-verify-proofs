(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_AM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_alloc_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From Stdlib Require Zify.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Module RF_am_P.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocRep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocTree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_AM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_A OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_K OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_C OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_D OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_G.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_alloc_meta.F_am_P.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.


Notation RAMpre := (@AMpre_g ref_reserved).
Notation ram_pre := (am_pre_g ref_reserved).


Section PURE.
Variable st : mstate.
Hypothesis AMP : RAMpre st.

Lemma rAMpre_init : RAMpre (am_init_st st).
Proof using AMP.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0); [| exact AMP].
  destruct AMP as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17]. split; cbn; try assumption.
  - rewrite A3. lia.
  - right; reflexivity.
  - destruct A8 as [L1 L2 L3 L4]. split; cbn; assumption.
Qed.

Lemma ram_init_regions : s_regions (am_init_st st) = s_regions st.
Proof. unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_brk : c_brk (ctx (am_init_st st)) = c_brk (ctx st).
Proof using . unfold am_init_st. destruct (c_init_done (ctx st) =? 0); reflexivity. Qed.
Lemma ram_init_conc q : conc (am_init_st st) q = conc st q.
Proof using . unfold conc, get_region. rewrite ram_init_regions. reflexivity. Qed.

Lemma rAMI_init : AMI st (am_init_st st).
Proof using AMP.
  unfold am_init_st. destruct (c_init_done (ctx st) =? 0);
  (split; [ repeat split; reflexivity | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | intros rid r Hr; exists r; repeat split; auto; lia
          | intros rid r' H1 H2; cbn in H1; congruence
          | cbn; lia
          | intros P _ HP; exact HP || (destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10); repeat split; assumption)
          | intros rid Hrid; apply (proj2 (amp_ptrs st AMP)); exact Hrid
          | exact (amp_rpos st AMP) ]).
  - cbn. rewrite (amp_s_secret st AMP). lia.
  - exact (amp_secret st AMP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rptrs_in_upd_ctx (P : N -> Prop) st0 f :
  optr_in P (c_free_meta_head (f (ctx st0))) -> optr_in P (c_avail_meta (f (ctx st0))) ->
  optr_in P (c_meta_area_head (f (ctx st0))) -> optr_in P (c_meta_area_tail (f (ctx st0))) ->
  optr_in P (c_avail_meta_areas (f (ctx st0))) -> c_active (f (ctx st0)) = c_active (ctx st0) ->
  match c_brk (f (ctx st0)) with BrkLive rid _ => P rid | _ => True end ->
  ptrs_in P st0 -> ptrs_in P (upd_ctx f st0).
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
  rewrite E6.
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  split; [exact H6|]. split; [exact E7|]. split; [|split; [exact H9| exact H10]].
  intros g. exact (H8 g).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_final stX st1 mo :
  AMI st stX ->
  c_active (ctx st1) = c_active (ctx stX) -> c_usage (ctx st1) = c_usage (ctx stX) -> c_unmap_seq (ctx st1) = c_unmap_seq (ctx stX) ->
  c_bounces (ctx st1) = c_bounces (ctx stX) -> c_seq (ctx st1) = c_seq (ctx stX) -> c_mmap_counter (ctx st1) = c_mmap_counter (ctx stX) ->
  s_groups st1 = s_groups stX -> s_slots st1 = s_slots stX -> s_shadow st1 = s_shadow stX -> s_tick st1 = s_tick stX ->
  s_reserved st1 = s_reserved stX -> s_regions st1 = s_regions stX -> s_next_rid st1 = s_next_rid stX ->
  (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas st1) !! a)) ->
  (forall g, Some g <> mo -> (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) -> get_meta_rec st1 g = get_meta_rec stX g) ->
  (forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m) ->
  (forall P : N -> Prop, (forall rid r, (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> P rid) -> ptrs_in P stX -> ptrs_in P st1) ->
  am_rel st st1 mo.
Proof using .
  intros AI E1 E2 E3 E4 E5 E6 EG ESl ESh ET ERs ER EN HA HM HR HP.
  destruct AI as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split.
  - intros sc. unfold active. rewrite E1, C7. reflexivity.
  - intros sc. unfold usage. rewrite E2, C8. reflexivity.
  - intros i. unfold bounces. rewrite E4, C10. reflexivity.
  - intros i. unfold unmap_seq. rewrite E3, C9. reflexivity.
  - rewrite E5, C11. reflexivity.
  - rewrite E6, C1. reflexivity.
  - rewrite EG, XG. reflexivity.
  - rewrite ESl, XS. reflexivity.
  - rewrite ESh, XSH. reflexivity.
  - rewrite ET, XT. reflexivity.
  - rewrite ERs, XR. reflexivity.
  - intros g Hg Hm. rewrite (HM g Hg Hm). unfold get_meta_rec. rewrite XM. reflexivity.
  - exact HR.
  - intros rid r Hr. rewrite ER. exact (XREG rid r Hr).
  - intros rid r' H1 H2. rewrite ER in H1. exact (XNEW rid r' H1 H2).
  - rewrite EN. exact XNX.
  - intros a Ha. apply HA. rewrite XA. exact Ha.
  - intros P HPn HP0. apply HP; [intros rid r Hr Hk; apply (HPn rid r); [rewrite ER|]; assumption|].
    apply XP; [| exact HP0]. intros rid r Hr Hk. apply (HPn rid r); [rewrite ER|]; assumption.
  - intros rid Hrid. rewrite ER, ESh, XSH. rewrite EN in Hrid. destruct (XF rid Hrid) as [A B]. split; [exact A| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ram_rel_none stX : AMI st stX -> am_rel st stX None.
Proof using .
  intros AI. eapply (ram_rel_final stX stX None AI); try reflexivity; auto.
  - intros m Hm. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_take stX q :
  AMI st stX -> c_avail_meta (ctx st) = Some q -> (s_metas st) !! q = None -> meta_slot st q ->
  am_rel st (am_took stX q (c_avail_meta_count (ctx stX) - 1)) (Some q).
Proof using .
  intros AI AVM MQ MSq. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  unfold am_took. rewrite upd_meta_put.
  eapply (ram_rel_final stX _ (Some q) AI); try reflexivity.
  - intros a Ha. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. reflexivity.
    + apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSq]. cbn. rewrite XA. reflexivity.
  - intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta.
    + cbn. exact I.
    + cbn. exact I.
    + unfold get_meta_rec. cbn [s_metas upd_ctx]. rewrite XM, MQ. cbn. exact I.
    + pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      apply rptrs_in_upd_ctx; cbn [c_free_meta_head c_avail_meta c_meta_area_head c_meta_area_tail c_avail_meta_areas c_active c_brk set_avail_meta set_avail_meta_count];
        try assumption; try reflexivity.
      cbn. rewrite C3, AVM in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma ram_rel_carve stX p r :
  AMI st stX -> (s_regions stX) !! (fst p) = Some r -> r_kind r <> RKGroup ->
  (s_areas stX) !! p = None -> (forall k, 0 <= k < NSLOTS -> (s_metas stX) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
  (forall tl, c_meta_area_tail (ctx stX) = Some tl -> is_Some ((s_areas stX) !! tl)) ->
  am_rel st (am_took (carve_st stX p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR)).
Proof using .
  intros AI Hr NK ANone FRESH TL. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (M0 : (s_metas stX) !! (aadd p AREA_HDR) = None).
  { replace (aadd p AREA_HDR) with (aadd p (AREA_HDR + META_SIZE * 0)) by (unfold aadd, AREA_HDR, META_SIZE; f_equal; lia). apply FRESH. unfold NSLOTS; lia. }
  (* [comment removed for export] *)
  assert (EX : exists stC, carve_st stX p = set_areas (<[p := mkArea (c_secret (ctx stX)) None NSLOTS]> (s_areas stC)) stC
            /\ s_regions stC = s_regions stX /\ s_metas stC = s_metas stX /\ s_groups stC = s_groups stX /\ s_slots stC = s_slots stX
            /\ s_shadow stC = s_shadow stX /\ s_tick stC = s_tick stX /\ s_reserved stC = s_reserved stX /\ s_next_rid stC = s_next_rid stX
            /\ c_active (ctx stC) = c_active (ctx stX) /\ c_usage (ctx stC) = c_usage (ctx stX) /\ c_unmap_seq (ctx stC) = c_unmap_seq (ctx stX)
            /\ c_bounces (ctx stC) = c_bounces (ctx stX) /\ c_seq (ctx stC) = c_seq (ctx stX) /\ c_mmap_counter (ctx stC) = c_mmap_counter (ctx stX)
            /\ (forall a, is_Some ((s_areas stX) !! a) -> is_Some ((s_areas stC) !! a))
            /\ (forall P : N -> Prop, P (fst p) -> ptrs_in P stX -> ptrs_in P stC)).
  { destruct (c_meta_area_tail (ctx stX)) as [tl|] eqn:HT.
    - destruct (TL tl eq_refl) as [ar Har]. rewrite (carve_st_some stX p tl ar HT Har ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. cbn. destruct (decide (a = tl)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence; exact Ha].
      + intros P HP H0. apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
        * destruct H0 as (H1 & _). exact H1.
        * destruct H0 as (_ & H2 & _). exact H2.
        * destruct H0 as (_ & _ & H3 & _). exact H3.
        * exact HP.
        * exact HP.
        * destruct H0 as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
        * pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
          assert (PI : ptrs_in P (upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) stX)).
          { apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity. }
          destruct PI as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
          unfold ptrs_in. cbn [ctx s_ctx set_areas upd_ctx s_areas s_groups s_metas].
          split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|].
          split; [exact Q8|]. split; [| exact Q10].
          intros a ar' Ha. destruct (decide (a = tl)) as [->|NE].
          -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [| exact HP]. exact (proj1 (H9 tl ar Har)).
          -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
    - rewrite (carve_st_none stX p HT ANone). cbv zeta.
      eexists. split; [reflexivity|]. repeat (split; [reflexivity|]). split.
      + intros a Ha. exact Ha.
      + intros P HP H0. pose proof H0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption. }
  destruct EX as (stC & EC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & RA & RP).
  rewrite EC. unfold am_took. rewrite upd_meta_put.
  set (stD := set_areas _ stC).
  eapply (ram_rel_final stX _ (Some (aadd p AREA_HDR)) AI); cbn [ctx s_ctx upd_ctx put_meta set_metas set_areas s_groups s_slots s_shadow s_tick s_reserved s_regions s_next_rid s_areas stD
     c_active c_usage c_unmap_seq c_bounces c_seq c_mmap_counter set_avail_meta set_avail_meta_count]; try assumption.
  - intros a Ha. destruct (decide (a = p)) as [->|NE]; [rewrite lookup_insert_eq; eauto| rewrite lookup_insert_ne by congruence]. apply RA. exact Ha.
  - intros g Hg _. rewrite get_meta_rec_put_other by congruence. unfold get_meta_rec. cbn. rewrite R2. reflexivity.
  - intros m Hm. inversion Hm; subst m. split.
    + rewrite get_meta_rec_put_same. unfold get_meta_rec. cbn. rewrite R2, M0. reflexivity.
    + apply meta_slot_put_meta. exists p, (mkArea (c_secret (ctx stX)) None NSLOTS), 0. cbn. rewrite lookup_insert_eq.
      split; [reflexivity|]. split; [unfold NSLOTS; lia|]. unfold aadd, AREA_HDR, META_SIZE. f_equal; lia.
  - intros P HPn HP0. assert (HPp : P (fst p)) by (apply (HPn (fst p) r Hr NK)).
    apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
    + unfold get_meta_rec. cbn. rewrite R2, M0. cbn. exact I.
    + apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity.
      * destruct (RP P HPp HP0) as (H1 & _). exact H1.
      * exact HPp.
      * destruct (RP P HPp HP0) as (_ & _ & H3 & _). exact H3.
      * destruct (RP P HPp HP0) as (_ & _ & _ & H4 & _). exact H4.
      * destruct (RP P HPp HP0) as (_ & _ & _ & _ & H5 & _). exact H5.
      * destruct (RP P HPp HP0) as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7.
      * pose proof (RP P HPp HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        unfold ptrs_in. cbn [ctx s_ctx set_areas s_areas s_groups s_metas].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
        split; [exact H8|]. split; [| exact H10].
        intros a ar' Ha. destruct (decide (a = p)) as [->|NE].
        -- rewrite lookup_insert_eq in Ha. inversion Ha; subst. cbn. split; [exact HPp| exact I].
        -- rewrite lookup_insert_ne in Ha by congruence. exact (H9 a ar' Ha).
Qed.

(* [comment removed for export] *)
Lemma ram_rel_deq stI h nx pv :
  AMI st stI ->
  c_free_meta_head (ctx st) = Some h -> c_free_meta_head (ctx stI) = Some h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv -> (nx = h <-> pv = h) ->
  meta_slot st h -> clr_links (get_meta_rec st h) = meta0 ->
  m_mem (get_meta_rec st nx) = None -> m_next (get_meta_rec st nx) <> None ->
  m_mem (get_meta_rec st pv) = None -> m_next (get_meta_rec st pv) <> None ->
  am_rel st (dequeue LFree h stI) (Some h).
Proof using .
  intros AI FMH FMHI HN HP SELF MSh CL MN NN MP NP. pose proof AI as AI'.
  destruct AI' as [(C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) SR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (GM : forall g, get_meta_rec stI g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite XM; reflexivity).
  rewrite dequeue_mid. unfold deq_mid. rewrite !GM, HN, HP. cbn [optr_eqb negb get_head]. rewrite FMHI.
  destruct (aptr_eqb nx h) eqn:E.
  - (* [comment removed for export] *)
    apply aptr_eqb_eq in E. subst nx. cbn [negb]. rewrite upd_meta_put. unfold set_head.
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg _. rewrite get_meta_rec_put_other by congruence. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same. change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| |].
      * change (get_meta_rec (upd_ctx (set_free_meta_head None) stI) h) with (get_meta_rec stI h). rewrite GM, CL0 || (rewrite GM; destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & H8 & _);
          destruct (H8 h) as (_ & _ & Q); rewrite GM in Q; cbn; exact Q).
      * pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
        apply rptrs_in_upd_ctx; cbn; try exact I; try reflexivity; try assumption.
  - (* [comment removed for export] *)
    assert (NEn : nx <> h) by (intros ->; rewrite aptr_eqb_refl in E; discriminate).
    assert (NEp : pv <> h) by (intros Ep; apply NEn; apply (proj2 SELF); exact Ep).
    cbn [negb]. rewrite optr_eqb_refl. rewrite !upd_meta_put. unfold set_head.
    set (st1 := put_meta pv _ stI). set (st2 := put_meta nx _ st1). set (st3 := upd_ctx _ st2).
    assert (R3 : get_meta_rec st3 h = get_meta_rec st h).
    { change (get_meta_rec st3 h) with (get_meta_rec st2 h). unfold st2, st1.
      rewrite !get_meta_rec_put_other by congruence. apply GM. }
    eapply (ram_rel_final stI _ (Some h) AI); cbn; try reflexivity; try assumption.
    + intros a Ha; exact Ha.
    + intros g Hg Hm. rewrite get_meta_rec_put_other by congruence.
      change (get_meta_rec st3 g) with (get_meta_rec st2 g). unfold st2, st1.
      assert (g <> nx) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MN| apply NN; exact Hm]).
      assert (g <> pv) by (intros ->; destruct Hm as [Hm|Hm]; [apply Hm; exact MP| apply NP; exact Hm]).
      rewrite !get_meta_rec_put_other by assumption. reflexivity.
    + intros m Hm. inversion Hm; subst m. split.
      * rewrite get_meta_rec_put_same, R3. exact CL.
      * apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSh]. cbn. rewrite XA. reflexivity.
    + intros P HPn HP0. pose proof HP0 as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
      destruct (H8 h) as (Q1 & Q2 & Q3). rewrite GM, HP in Q1. rewrite GM, HN in Q2. cbn in Q1, Q2.
      assert (P1 : ptrs_in P st1).
      { unfold st1. apply MallocKit_A2.ptrs_in_put_meta; [| cbn; exact Q2 | | exact HP0].
        - destruct (H8 pv) as (X & _ & _). exact X.
        - destruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P2 : ptrs_in P st2).
      { unfold st2. apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact Q1 | | | exact P1].
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [exact Q2|]. destruct (H8 nx) as (_ & X & _). exact X.
        - unfold st1. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv); cbn; [| destruct (H8 nx) as (_ & _ & X); exact X].
          destruct (H8 pv) as (_ & _ & X). exact X. }
      assert (P3 : ptrs_in P st3).
      { unfold st3. pose proof P2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
        apply rptrs_in_upd_ctx; cbn; try reflexivity.
        - exact Q2.
        - change (ctx st2) with (ctx stI). exact H2.
        - change (ctx st2) with (ctx stI). exact H3.
        - change (ctx st2) with (ctx stI). exact H4.
        - change (ctx st2) with (ctx stI). exact H5.
        - change (ctx st2) with (ctx stI). exact H7.
        - exact P2. }
      apply MallocKit_A2.ptrs_in_put_meta; [cbn; exact I| cbn; exact I| | exact P3].
      rewrite R3. rewrite <- GM. exact Q3.
Qed.

(* [comment removed for export] *)
Lemma rAMI_ctx stX f :
  AMI st stX ->
  ctx_core_eq (ctx stX) (f (ctx stX)) -> 0 <= c_secret (f (ctx stX)) < 2^64 ->
  (c_avail_meta_areas (f (ctx stX)) = c_avail_meta_areas (ctx stX)
   \/ exists q r, c_avail_meta_areas (f (ctx stX)) = Some q /\ (s_regions stX) !! (fst q) = Some r /\ r_kind r <> RKGroup) ->
  (c_brk (f (ctx stX)) = c_brk (ctx stX)
   \/ c_brk (f (ctx stX)) = BrkDead
   \/ exists rid off r, c_brk (f (ctx stX)) = BrkLive rid off /\ (s_regions stX) !! rid = Some r /\ r_kind r <> RKGroup) ->
  AMI st (upd_ctx f stX).
Proof using .
  intros AI CE SR HA HB. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  split; cbn; try assumption.
  - destruct CC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
    destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    unfold ctx_core_eq. change (ctx (upd_ctx f stX)) with (f (ctx stX)).
    rewrite D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11. repeat split; assumption.
  - intros P HPn HP0. pose proof (XP P HPn HP0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    destruct CE as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    apply rptrs_in_upd_ctx; rewrite ?D2, ?D3, ?D5, ?D6, ?D7; try assumption; try reflexivity.
    + destruct HA as [-> | (q & r & -> & Hq & Kq)]; [exact H5|]. cbn. exact (HPn _ _ Hq Kq).
    + destruct HB as [-> | [-> | (rid & off & r & -> & Hq & Kq)]]; [exact H7| exact I|]. exact (HPn _ _ Hq Kq).
    + exact (XP P HPn HP0).
Qed.

Lemma rAMI_new_region stX k base len :
  AMI st stX -> k <> RKGroup -> 0 < len ->
  AMI st (fst (new_region k base len stX))
  /\ (s_regions (fst (new_region k base len stX))) !! (s_next_rid stX) = Some (mkRegion k base len)
  /\ (forall q, fst q <> s_next_rid stX -> conc (fst (new_region k base len stX)) q = conc stX q)
  /\ (forall off, conc (fst (new_region k base len stX)) (s_next_rid stX, off) = base + off).
Proof using .
  intros AI NK LEN. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  destruct (XF (s_next_rid stX) ltac:(lia)) as [FRr FRs].
  unfold new_region. cbn [fst].
  set (rid := s_next_rid stX). set (st' := set_next_rid _ _).
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion k base len) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  split; [| split; [| split]].
  - split; cbn -[insert]; try assumption.
    + intros q r Hq. destruct (XREG q r Hq) as (r' & Hr' & REST). exists r'. rewrite LK.
      destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hr'; discriminate|]. auto.
    + intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
    + unfold rid. lia.
    + intros P HPn HP0. apply (MallocKit_A2.ptrs_in_new_region stX base len k). apply XP; [| exact HP0].
      intros q r Hq Hk. apply (HPn q r); [| exact Hk]. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate| exact Hq].
    + intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE]; [unfold rid in Hq; lia|]. apply XF. unfold rid in Hq. lia.
    + intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; lia|]. exact (XRP q rq Hq).
  - rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
  - intros q Hq. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [exfalso; apply Hq; exact E| reflexivity].
  - intros off. unfold conc, get_region. cbn [fst snd]. rewrite LK. destruct (decide (rid = rid)); [reflexivity| congruence].
Qed.

Lemma rAMI_grow stX rid r off :
  AMI st stX -> (s_regions stX) !! rid = Some r -> r_kind r <> RKGroup -> r_len r = off ->
  let st' := set_regions (<[rid := mkRegion (r_kind r) (r_base r) (off + 4096)]> (s_regions stX)) stX in
  AMI st st' /\ (forall q, conc st' q = conc stX q) /\ (s_regions st') !! rid = Some (mkRegion (r_kind r) (r_base r) (off + 4096)).
Proof using .
  intros AI Hr NK LEN st'. pose proof AI as AI'.
  destruct AI' as [CC XSR XM XA XG XS XSH XT XR XREG XNEW XNX XP XF XRP].
  assert (LK : forall q, (s_regions st') !! q = if decide (q = rid) then Some (mkRegion (r_kind r) (r_base r) (off + 4096)) else (s_regions stX) !! q).
  { intros q. cbn. destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
  assert (CQ : forall q, conc st' q = conc stX q).
  { intros q. unfold conc, get_region. rewrite LK. destruct (decide (fst q = rid)) as [E|NE]; [rewrite E, Hr|]; reflexivity. }
  split; [| split; [exact CQ| rewrite LK; destruct (decide (rid = rid)); [reflexivity| congruence]]].
  split; cbn -[insert]; try assumption.
  - intros q rq Hq. destruct (XREG q rq Hq) as (r' & Hr' & K' & B' & L' & G'). rewrite LK.
    destruct (decide (q = rid)) as [->|NE].
    + rewrite Hr in Hr'. inversion Hr'; subst r'. eexists. split; [reflexivity|]. cbn. split; [exact K'|]. split; [exact B'|]. split; [lia|].
      intros HG. exfalso. apply NK. rewrite K'. exact HG.
    + exists r'. auto.
  - intros q r' Hq Hn. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; exact NK|]. exact (XNEW q r' Hq Hn).
  - intros P HPn HP0. apply XP; [| exact HP0]. intros q rq Hq Hk.
    destruct (decide (q = rid)) as [->|NE].
    + apply (HPn rid (mkRegion (r_kind r) (r_base r) (off + 4096))); [rewrite LK; destruct (decide (rid = rid)); [reflexivity|congruence]|]. cbn. rewrite Hr in Hq. inversion Hq; subst. exact Hk.
    + apply (HPn q rq); [rewrite LK; destruct (decide (q = rid)); [congruence| exact Hq]| exact Hk].
  - intros q Hq. rewrite LK. destruct (decide (q = rid)) as [->|NE].
    + destruct (XF rid Hq) as [A _]. rewrite Hr in A. discriminate.
    + apply XF. exact Hq.
  - intros q rq Hq. rewrite LK in Hq. destruct (decide (q = rid)) as [->|NE]; [inversion Hq; subst; cbn; pose proof (XRP rid r Hr); lia|]. exact (XRP q rq Hq).
Qed.
End PURE.


End CeilWrap.
(* [comment removed for export] *)
Notation RAMpre := (@AMpre_g ref_reserved).
Notation ram_pre := (am_pre_g ref_reserved).
End RF_am_P.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Export UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_malloc_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocModel_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.F_ntf_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require MallocFacts_Bpres.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.MallocFacts_Bpres.MallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.MallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.MallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_ntf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_ntf.F_am_K2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_E.F_am_D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_am_H.F_am_G.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_am_H.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require F_alloc_meta.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.F_alloc_meta.F_am_P.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import F_alloc_meta.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocRep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RRealloc_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RRealloc_iface.RMallocTree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RMallocKit_B.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RMallocKit_A2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RMallocKit_A2.RMallocKit_B2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RMallocKit_B3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RF_mm_syscalls RMallocKit_A2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_ntf_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_am_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_am_K.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RF_am_K2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_am_C.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_E.RF_am_D.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RF_am_E.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_H.RF_am_F.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require RF_am_H.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.RF_am_H.RF_am_G.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import RF_am_H.
Import RF_am_P.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.
(* [comment removed for export] *)
From Stdlib Require Import Zify Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require HeapLiaImp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.HeapLiaImp.HeapLia.
Local Ltac Lia.lia ::= heap_lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof using . intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof using . intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

(* [comment removed for export] *)
Lemma rrw_cells_magree C m m' A cs :
  rw_cells usegs m A cs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ C a) -> rw_cells usegs m' A cs.
Proof.
  intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RA2.rrw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma rbytes_at_magree C m m' A bs :
  bytes_at usegs m A bs -> magree C m m' -> (forall a, A <= a < A + Z.of_nat (length bs) -> ~ C a) -> bytes_at usegs m' A bs.
Proof.
  intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RA2.rbytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Lemma rwr_at_magree C m m' A n :
  wr_at usegs m A n -> magree C m m' -> (forall a, A <= a < A + n -> ~ C a) -> 0 <= A -> A + n <= 2^64 -> wr_at usegs m' A n.
Proof using . intros H AG HC H0 H1. eapply RA2.rwr_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha]. Qed.

Lemma rauxv_ok_magree C m m' B :
  rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof using .
  intros (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H) AG HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rrw_cells_magree; [exact AC| exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. exact Ha.
  - eapply rbytes_at_magree; [exact AL| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
    unfold auxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. lia.
  - eapply rbytes_at_magree; [exact RN| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite length_le8 in Ha. lia.
Qed.

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 0x349d0.
Hypothesis KH : forall st1 mo s' ms',
     ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof using . intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

Lemma rETP : errno_addr tp = 0x349d0 - 164.
Proof using ACEIL TP. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rfinish_K : forall (st1 : mstate) (mo : optr) (sX : PState) (m' : mem) (e : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv : word),
  am_rel st st1 mo -> rmrep st1 m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp) ->
  rw_cells usegs m' (errno_addr tp) [C4 e] -> rauxv_ok m' (bv_unsigned sp) -> magree (rFP st1) m m' ->
  brk_link_ps st1 sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rv = pw st1 mo ->
  rimplT o (k st1 mo) sX Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)).
Proof using KH TK.
  intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 ->.
  apply KH; [| exact BL1]. unfold ram_post. nexists 16%nat. split; [reflexivity|].
  split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
  { apply rpres_of_magree. exact AG. }
  split; [exact MR1|]. split.
  { destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
  auto.
Qed.

(* [comment removed for export] *)
Lemma rFP_mono stX stY a :
  (forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  rFP stX a -> rFP stY a.
Proof using .
  intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
  (nelim (HR rid r Hr) 5%nat; intros r' Hr' K' B' L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
  assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
  { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
  unfold lr_lo in *. rewrite K', B'. lia.
Qed.

Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof using . intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof using AMP LO LOLE.
  intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK, alloc_ceiling in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - (nelim (WR _ _ Hr) 5%nat; intros _ _ _ RBC RF). (nelim (rreserved_disjoint _ _ RF) 4%nat; intros D1 _ D23 D2). pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
  - pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. unfold alloc_ceiling in C. lia.
Qed.

Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof using LO TP. intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

(* [comment removed for export] *)
Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof using . reflexivity. Qed.
(* [comment removed for export] *)
Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof using . reflexivity. Qed.
Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof using . reflexivity. Qed.
Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof using .
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof using . unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rcarve_K : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  c_init_done (ctx stY) <> 0 ->   (* [comment removed for export] *)
  rmrep stY mX -> mem_inv usegs mX -> bytes_at usegs mX (conc stY p) (zeros 4096) -> wr_at usegs mX (conc stY p) 4096 ->
  rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
  rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (k (am_took (carve_st stY p) (aadd p AREA_HDR) 100) (Some (aadd p AREA_HDR))) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16d34) fc None mX (seg_rom usegs)).
Proof using AMP KH LO LOLE TK TP.
  intros until t6. intros AI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT INIY MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof MRX as (WFX & _).
  eapply rimplT_evt.
  { eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
      first [exact MRX | exact MIX | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
            | exact (ami_secretr _ _ AI) | exact INIY | exact ZB | exact ZW | exact FRX | exact STX | exact LO | lia]. }
  intros ms2 RP. unfold ram_ret_post in RP.
  (nelim RP 21%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m2 -> PE2 WM2 MI2 ST2 MR2).
  pose proof (carve_st_regions stY p) as RC.
  eapply rfinish_K.
  - eapply (ram_rel_carve st stY p r AI); assumption.
  - exact MR2.
  - exact MI2.
  - exact ST2.
  - eapply rrw_cells_magree; [exact ERRX| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X.
    apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
  - eapply rauxv_ok_magree; [exact AUXX| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
  - assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; exact RC).
    eapply magree_trans; [exact AGX| apply rmagree_of_pres; exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
  - unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
    rewrite rconc_am_took, rconc_carve. exact BLX.
  - exact P1.
  - exact P2.
  - exact P3.
  - unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof using TP.
  intros WF H. rewrite rETP. (nelimp WF 5%nat; intros _ WR _ WA WG). unfold alloc_ceiling.
  destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try heap_lia_pruned.
  - (nelim C 4%nat; intros ak ar Hak Hin). (nelim (rarea_conc stY ak ar WF Hak) 10%nat; intros rra Hra Ca Sa0 Sa1 SaL NKa RB0 RBAL RBC).
    (nelim (WR _ _ Hra) 5%nat; intros _ _ _ _ RF). (nelim (rreserved_disjoint _ _ RF) 4%nat; intros D1 _ D23 D2). unfold alloc_ceiling in RBC. lia.
  - (nelim C 4%nat; intros b gh Hb Hin). (nelim (rgroup_conc stY b gh WF Hb) 9%nat; intros rb Hrb Cb Krb Sb0 Sb1 Al RB0 RBC).
    (nelim (WR _ _ Hrb) 5%nat; intros _ _ _ _ RF). (nelim (rreserved_disjoint _ _ RF) 4%nat; intros D1 _ D23 D2). unfold alloc_ceiling in RBC. lia.
  - (nelim C 7%nat; intros rid rg v Hrg Krg Hin _). (nelim (WR _ _ Hrg) 5%nat; intros _ _ _ RBC RF). (nelim (rreserved_disjoint _ _ RF) 4%nat; intros D1 _ D23 D2). unfold alloc_ceiling in RBC. lia.
Qed.

Lemma rfinish_path : forall (stY : mstate) (p : aptr) (r : region) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> c_avail_meta_areas (ctx stY) = Some p ->
  (s_regions stY) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  pgal (snd p) -> lr_lo r <= r_base r + snd p ->
  (s_areas stY) !! p = None -> (forall j, 0 <= j < NSLOTS -> (s_metas stY) !! (aadd p (AREA_HDR + META_SIZE * j)) = None) ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  1 <= c_avail_meta_area_count (ctx stY) < 2^64 ->
  c_init_done (ctx stY) <> 0 ->   (* [comment removed for export] *)
  rmrep stY mX -> mem_inv usegs mX ->
  rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
  rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_finish stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16dc4) fc None mX (seg_rom usegs)).
Proof using AMP KH LO LOLE TK TP.
  intros until t6. intros AI AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT INIY MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. unfold alloc_ceiling in LO'.
  pose proof MRX as (WFX & _ & (_ & _ & PGX & _) & _). (nelimp WFX 5%nat; intros RS WR DJ WA WG).
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RF). (nelim (rreserved_disjoint _ _ RF) 4%nat; intros DR1 _ DR23 DR2). unfold alloc_ceiling in RBC.
  pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
  assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL; Z.div_mod_to_equations; lia).
  assert (IMG : conc stY p + 4096 <= 0x10000 \/ 0x56000 <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
  pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.
  (* [comment removed for export] *)
  unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
  intros ms2 ->.
  eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
  { eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
    unfold PGSZ, PROT_RW.
    eapply rmprotect_spec with (lo := lo) (errv := e);
      [ rewrite unsigned_lit by heap_lia_pruned; exact STX | exact ERRX | exact PGX | exact MIX | reflexivity | reflexivity | reflexivity
      | exact PAL | reflexivity | heap_lia_pruned | heap_lia_pruned | heap_lia_pruned | heap_lia_pruned | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by heap_lia_pruned; unfold RPAGE_SIZE; try heap_lia_pruned.
    (* [comment removed for export] *)
    all: unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); rewrite ?Cp; lia. }
  intros ans ms3 [MP G]. unfold rmprotect_post in MP.
  (nelim MP 23%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m3 -> MU3 WM3 MI3 ST3 ERR3 PG3 CASE).
  rewrite unsigned_lit in MU3, ST3 by lia.
  replace (ret_pc (Z_to_bv 64 0x16dd4)) with (Z_to_bv 64 0x16dd4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
  { eapply rw_cells_transport; [exact FRX| exact MU3| exact WM3|]. rewrite rETP'. cbn. unfold alloc_ceiling in LO. lia. }
  assert (MR3 : rmrep stY m3).
  { eapply rmrep_transport_unowned; [exact MRX| exact MU3| exact WM3|].
    intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
    - intros RFt. destruct (rrepfoot_low stY y WFX RFt). unfold alloc_ceiling in *. lia.
    - intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
    - eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
  assert (M23 : magree (rFP stY) mX m3).
  { eapply magree_of_munch; [exact MU3|].
    cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
    - left. left. lia.
    - left. right. left. rewrite TPv in Hx. exact Hx.
    - left. right. right. right. exists (fst p), r. split; [exact Hr|]. split; [exact NK|]. lia. }
  assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AGX| exact M23| intros a X; exact X| intros a X; exact X]).
  assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUXX| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
  clear MU3 WM3.
  destruct ans as [e'|b]; cbn in G.
  - (* [comment removed for export] *)
    cbn [range_val F_mm_syscalls.munmap_ret F_mm_syscalls.rg_errno] in *.
    unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
    replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    cbn [negb].
    eapply rimplT_evt.
    { eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
        first [exact MR3 | exact MI3 | exact TPv | exact ERR3 | exact G | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
    intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
    (nelim RP 21%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m4 EQ PE4 WM4 MI4 ST4 MR4).
    rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
    eapply rfinish_K.
    + apply (ram_rel_none st stY AI).
    + exact MR4.
    + exact MI4.
    + exact ST4.
    + exact ERR4.
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
    + exact BLX.
    + exact P1.
    + exact P2.
    + exact P3.
    + reflexivity.
  - (* [comment removed for export] *)
    subst b. cbn [range_val] in *.
    unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
    rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
    destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
    eapply rimplT_evt.
    { apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0x16dd4) F fc m3). }
    intros ms4 ->.
    eapply (rcarve_K stY p r m3 sX junk); first [exact AI | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT | exact INIY
      | exact MR3 | exact MI3 | exact ZB | exact ZW | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | exact BLX | exact P1 | exact P2 | exact P3 | idtac].
    unfold pgal. exact SAL.
Qed.

Lemma rlive_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma rfresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= alloc_ceiling -> x <= a < x + L -> fresh_addr st a.
Proof.
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

Lemma rrepfoot_clear stY mY x L a :
  rmrep stY mY -> ranges_free (live_ranges stY) x L = true -> rrepfoot stY a \/ rgrp_region_addr stY a -> ~ (x <= a < x + L).
Proof using .
  intros MRY RF H. pose proof MRY as (WF & _). (nelimp WF 5%nat; intros RS WR DJ WA WG).
  pose proof (clear_range_of_ranges_free stY x L RF) as CR.
  assert (IMG : forall y, 0x10000 <= y < 0x56000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
  destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - (nelim C 4%nat; intros ak ar Hak Hin). (nelim (WA ak ar Hak) 3%nat; intros rra Hra _).
    eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
  - (nelim C 4%nat; intros b gh Hb Hin). (nelim (WG b gh Hb) 3%nat; intros rb Hrb _).
    eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
  - (nelim C 7%nat; intros rid rg v Hrg Krg Hin _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - (nelim C 5%nat; intros rid rg Hrg Krg Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.

Lemma rmmap_path : forall (stY : mstate) (mX : mem) (sX : PState) (junk : list byte) (e : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  AMI st stY -> s_regions stY = s_regions st -> c_avail_meta_area_count (ctx stY) = 0 ->
  c_init_done (ctx stY) <> 0 ->   (* [comment removed for export] *)
  0 <= c_meta_alloc_shift (ctx stY) <= 38 ->
  (forall tl, c_meta_area_tail (ctx stY) = Some tl -> is_Some ((s_areas stY) !! tl)) ->
  (forall q mr, (s_metas stY) !! q = Some mr -> meta_slot stY q) ->
  ptrs_in (fun rid => (rid < s_next_rid stY)%N) stY ->
  rmrep stY mX -> mem_inv usegs mX ->
  rw_cells usegs mX (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs mX lo (bv_unsigned sp + -64) ->
  rw_cells usegs mX (errno_addr tp) [C4 e] -> rauxv_ok mX (bv_unsigned sp) -> magree (rFP stY) m mX ->
  brk_link_ps stY sX -> ps_m sX = ps_m s -> ps_fa sX = ps_fa s -> ps_so sX = ps_so s ->
  rimplT o (am_after_brk stY true k bail) sX Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16cd4) fc None mX (seg_rom usegs)).
Proof using AMP KH LO LOLE TK TP.
  intros until t6. intros AI RGY ACNT INIY SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MRX as (WFX & _). (nelimp WFX 5%nat; intros RS WR DJ WA WG).
  set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
  assert (NR : 2 <= n <= 2^39).
  { unfold n. rewrite Z.shiftl_mul_pow2 by lia. split.
    - rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
    - change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
  intros ms2 ->. fold n.
  pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
  set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
  clear MRX MIX FRX STX ERRX AUXX AGX.
  eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
  { unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by reflexivity.
    eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
      [ rewrite unsigned_lit by lia; exact ST2 | exact ERR2 | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
      rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. all: first [rewrite F_mm_syscalls.alloc_ceiling_val; lia | unfold alloc_ceiling in *; lia]. }
  intros ans ms3 MP. unfold rmmap_anon_post in MP.
  destruct ans as [e'|x].
  - (* [comment removed for export] *)
    (nelim MP 22%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m3 -> MU3 WM3 MI3 ST3 ERR3 ER).
    rewrite unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x16d00)) with (Z_to_bv 64 0x16d00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
    replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. rewrite rETP'. cbn. lia. }
    assert (MR3 : rmrep stY m3).
    { eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
      intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
    assert (M23 : magree (rFP stY) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. exact Hy. }
    assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
    eapply rimplT_evt.
    { eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
        first [exact MR3 | exact MI3 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
    intros ms4 RP. unfold ram_ret_post in RP.
    (nelim RP 21%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m4 -> PE4 WM4 MI4 ST4 MR4).
    eapply rfinish_K.
    + apply (ram_rel_none st stY AI).
    + exact MR4.
    + exact MI4.
    + exact ST4.
    + eapply rrw_cells_magree; [exact ERR3| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
    + exact BLX.
    + exact P1.
    + exact P2.
    + exact P3.
    + reflexivity.
  - (* [comment removed for export] *)
    (nelim MP 22%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m2' -> MU3 WM3 MI3 ST3 ERR3 AOK).
    rewrite unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x16d00)) with (Z_to_bv 64 0x16d00 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].
    (* [comment removed for export] *)
    unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
    apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
    rewrite A2.mmap_len_round_up in XC. first [rewrite F_mm_syscalls.alloc_ceiling_val in XC | unfold alloc_ceiling in XC]. change page_size with 4096 in XA.
    assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
    rewrite LAL in XC.
    unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
    assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
    { destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; exact V].
      unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
    unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
    unfold new_region. cbv beta iota zeta delta [fst snd].
    set (rid := s_next_rid stY).
    (nelimp (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) 4%nat; intros AI1 RG1 CQ1 CN1).
    unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
    set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
    set (st2 := upd_ctx _ st1).
    assert (E2 : st2 = mm_ok_st st1 rid n) by reflexivity.
    (* [comment removed for export] *)
    unfold F_mm_syscalls.mmap_raw in ST3 |- *. rewrite A2.mmap_len_round_up, LAL in ST3 |- *.
    set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
    assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      - eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. lia.
      - cbn. unfold PGSZ in *. lia. }
    assert (ERR4 : rw_cells usegs m3 (errno_addr tp) [C4 e]).
    { apply (rw_cells_unmaps_other usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [exact ERR3|]. cbn. rewrite rETP'.
      pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x349d0 - 164) RS RF ltac:(lia)).
      pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x349d0 - 161) RS RF ltac:(lia)). unfold PGSZ in *. lia. }
    assert (MI4 : mem_inv usegs m3) by (apply (mem_inv_unmaps usegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); exact MI3).
    assert (MR2' : rmrep stY m2').
    { eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
      intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); unfold alloc_ceiling in *; lia. }
    assert (MR3 : rmrep stY m3).
    { eapply rmrep_transport_agree'; [exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
    assert (MRn : rmrep st1 m3).
    { unfold st1. apply (RA2.rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
        first [ exact MR3
              | eapply ptrs_in_mono; [| exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
              | apply (ami_fresh _ _ AI); unfold rid; lia
              | unfold alloc_ceiling; rewrite LAL; exact XC
              | rewrite LAL; exact RF
              | intros; reflexivity
              | intros; discriminate
              | unfold PGSZ in *; lia ]. }
    assert (M23 : magree (rFP stY) m2 m3).
    { intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      - apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
      - rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
        exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [exact RGY| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; exact XC| lia]. }
    assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
    clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
        first [exact MRn | exact MI4 | intros a X; exact X | exact RG1 | reflexivity | exact XA | exact X0 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | idtac];
        try (unfold alloc_ceiling, PGSZ in *; heap_lia_pruned).
      change (ctx st1) with (ctx stY). lia. }
    intros ms4 nelH_; (nelim nelH_ 8%nat; intros m4 -> PE4 WM4 MI5 FR4 ST4 MR4).
    pose proof MRn as (WFn & _).
    assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
    { intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
      destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
    destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
    replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
    eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
    + unfold st2. apply (rAMI_ctx st st1 _ AI1).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AI1).
      * right. exists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [exact RG1| cbn; discriminate].
      * left. reflexivity.
    + reflexivity.
    + cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
    + cbn. discriminate.
    + cbn. lia.
    + cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
    + unfold pgal. reflexivity.
    + cbn. lia.
    + change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
      exfalso. (nelim (WA _ _ EA) 3%nat; intros rr Hrr _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
    + intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
      exfalso. (nelim (MK _ _ EM) 6%nat; intros a ar kk Ha Hk Eq). (nelim (WA _ _ Ha) 3%nat; intros rr Hrr _).
      assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
    + intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. exact Htl.
    + cbn. lia.
    + cbn. exact INIY.
    + exact MR4.
    + exact MI5.
    + exact FR4.
    + exact ST4.
    + eapply rrw_cells_magree; [exact ERR4| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| |].
      * intros a X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq. rewrite RG2.
        destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
      * intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
    + unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
      (nelim PTR 8%nat; intros _ _ _ _ _ _ PB _).
      destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [exact BLX|]. cbn [fst]. unfold rid. lia.
    + exact P1.
    + exact P2.
    + exact P3.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimage_range_clear stY x L : s_reserved stY = ref_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
  x + L <= 0x10000 \/ 0x56000 <= x.
Proof.
  intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
  c_init_done (ctx stI) <> 0 ->   (* [comment removed for export] *)
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv usegs m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (let old := conc stI (brid, boff) in
           let new := old + PGSZ in
           SVis (EBrk new) (fun r =>
             if negb (brk_answer_ok old new r) then bad_answer bail else
             if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
             else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
             else
               let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
               let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
               am_after_brk st2 false k bail)) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16c24) fc None m1 (seg_rom usegs)).
Proof using AMP ERR KH LO LOLE TK TP.
  intros until t6. intros AMPI AI RGI BLI ACNT BRK INII PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). (nelimp WF1 5%nat; intros RS WR DJ WA WG).
  pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. (nelim HB 8%nat; intros r Hr Kr Lr OAL O4 FRA UNQ).
  pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
  (nelim (WR _ _ Hr) 5%nat; intros RB0 RBAL RL0 RBC RFr). unfold alloc_ceiling in RBC. rewrite Lr in RBC.
  assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; exact OAL). rewrite RUB in RBC.
  set (old := conc stI (brid, boff)) in *.
  assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
  assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
  unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
  cbv zeta.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [exact MR1| exact ACNT| exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
  intros ms2 ->. fold old.
  eapply (rimplT_brk o (old + PGSZ) _ s).
  { unfold PGSZ; lia. }
  { rewrite BLI. unfold PGSZ.
    exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 0x16c48 (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
  intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs.
  destruct a.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
    destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
    unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
    unfold alloc_ceiling, PGSZ in OC. unfold PGSZ in RF.
    assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
    rewrite (brk_new_pages_aligned old 4096) by (first [lia | exact OALD | reflexivity]).
    rewrite (rgr_eq stI brid r boff Hr).
    set (stG := set_regions _ stI).
    unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [heap_lia_pruned | reflexivity | unfold PGSZ in OAL; exact OAL]).
    rewrite am_carve_took, carve_st_brk_irrel.
    set (stX := upd_ctx _ stG).
    (* [comment removed for export] *)
    assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
    pose proof (rimage_range_clear stI old 4096 RS RF ltac:(lia)) as IMG.
    set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
    unfold rctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
    assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
      by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX1| cbn; unfold RCTX; lia]).
    assert (TC2 : rw_cells usegs m2 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
      by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact HX6| cbn; unfold RCTX; lia]).
    assert (MI2 : mem_inv usegs m2).
    { apply (mem_inv_zeros usegs m1 old 4096 Ho1 Hn1 Hon MI1); [intros y Hy; apply ref_ro_addr_false; lia | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; lia]. }
    assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
      by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact FR1| cbn; lia]).
    assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m1 old 4096 Ho1 Hn1 Hon); exact ST1).
    assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1])
      by (apply (rw_cells_zeros_other usegs m1 old 4096 Ho1 Hn1 Hon); [exact ERR1| cbn; rewrite rETP'; lia]).
    pose proof (rw_cells_zeros_new usegs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
    assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
    assert (WM12 : wmono usegs m1 m2) by (apply (wmono_zeros usegs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
    assert (MR2 : rmrep stI m2).
    { eapply rmrep_transport_unowned; [exact MR1| exact MU12| exact WM12|].
      intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
    assert (M12 : magree (rFP stI) m1 m2).
    { intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
      destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
      exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }
    clearbody m2.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | exact MI2].
      - unfold pw in HC2. cbn [oconc] in HC2. exact HC2.
      - unfold wz in TC2. exact TC2. }
    intros ms4 nelH_; (nelim nelH_ 7%nat; intros m3 -> MU3 WM3 MI3 HC3 TC3). replace (old + 4096 - 4096) with old by lia.
    (* [comment removed for export] *)
    (nelimp (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) 3%nat; intros AIG CQG RG'). fold stG in AIG, CQG, RG'.
    assert (MRG : rmrep stG m2).
    { unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
        first [ rewrite Kr; discriminate
              | exact Lr
              | unfold PGSZ in OAL; exact OAL
              | rewrite <- OLD; exact RF
              | exact (amp_rpos stI AMPI)
              | intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
              | unfold alloc_ceiling, PGSZ in *; lia ]. }
    assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
    assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
    assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
    assert (MRX : rmrep stX m3).
    { eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
      - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold rctx_head_cells. rewrite !PWX.
        cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (s_ctx stI) with (ctx stI). unfold wz at 4. exact HC3.
      - right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
        unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
        change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
        rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
        replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). exact TC3. }
    (* [comment removed for export] *)
    assert (M23 : magree (rFP stX) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. unfold RCTX. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; unfold RCTX; lia. }
    assert (ZN3 : rw_cells usegs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
    { eapply rw_cells_transport; [exact ZN| exact MU3| exact WM3|]. cbn. unfold RCTX. lia. }
    destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
    assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
    assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; rewrite rETP'; unfold RCTX; lia).
    assert (AGX1 : forall y, rFP stI y -> rFP stX y).
    { intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; exact Hq|]. (* [comment removed for export] *)
      destruct (decide (q = brid)) as [->|NE].
      - eexists. split; [exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
      - exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
    assert (AG3 : magree (rFP stX) m m3).
    { eapply magree_trans; [| exact M23| exact AGX1| intros y X; exact X]. eapply magree_trans; [exact AG1| exact M12| intros y X; exact X| intros y X; exact X]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_magree; [exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
      eapply magree_trans; [exact M12| exact M23| exact AGX1| intros y X; exact X]. }
    replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
    eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
      first [exact RG' | exact MRX | exact MI3 | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | reflexivity | idtac].
    + unfold stX. apply (rAMI_ctx st stG _ AIG).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AIG).
      * left. reflexivity.
      * right. right. exists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [exact RG'|]. cbn. rewrite Kr. discriminate.
    + cbn. rewrite Kr. discriminate.
    + cbn. lia.
    + cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
    + unfold pgal. unfold PGSZ in OAL. exact OAL.
    + cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
    + change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
    + intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
    + intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
    + cbn. lia.
    + cbn. exact INII.
    + change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZB.
    + change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZW.
    + unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
      rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl.
    replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
    eapply rimplT_evt.
    { unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [exact MR1| exact ACNT| lia| lia| exact MI1]. }
    intros ms4 nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 MRD).
    assert (M13 : magree (rFP stI) m1 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
    eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
    + apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
    + exact RGI.
    + exact ACNT.
    + cbn. exact INII.
    + change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
    + exact TLI.
    + exact MKI.
    + (nelimp PTRI 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
    + eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply rw_cells_transport; [exact ERR1| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
    + eapply rauxv_ok_magree; [exact AUX1| exact M13| intros y X; exact (rFP_below stI y WF1 X)].
    + eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.


Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
  c_init_done (ctx stI) <> 0 ->   (* [comment removed for export] *)
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv usegs m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  ps_m s = ps_m s ->
  rimplT o (SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
            else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16c24) fc None m1 (seg_rom usegs)).
Proof using AMP ERR KH LO LOLE TK TP.
  intros until t6. intros AMPI AI RGI ACNT BRK INII PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). (nelimp WF1 5%nat; intros RS WR DJ WA WG).
  assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
  assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
  unfold rctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
  intros ms2 ->.
  eapply (rimplT_brk0 o _ s).
  { exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
  intros cur ms3 [-> CR]. unfold rbrk_regs.
  destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
  unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
  apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
  rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
  replace (2 * 4096) with 8192 by reflexivity.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| exact CAL| unfold wz in HX6; exact HX6| exact MI1]. }
  intros ms4 nelH_; (nelim nelH_ 7%nat; intros a2' m2 -> MU2 WM2 MI2 TC2).
  eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
  { lia. }
  { exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 0x16c84 (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
  intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (ERR2 : rw_cells usegs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; cbn; rewrite rETP'; unfold RCTX; lia).
  assert (HC2 : rw_cells usegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
    by (eapply rw_cells_transport; [exact HX1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (M12 : magree (rFP stI) m1 m2).
  { eapply magree_of_munch; [exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
  destruct a.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
    destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
    unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
    unfold alloc_ceiling in OC.
    rewrite (brk_new_pages_aligned cur 8192) by (first [lia | exact CAL | reflexivity]).
    pose proof (rimage_range_clear stI cur 8192 RS RF ltac:(lia)) as IMG.
    assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
    set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
    assert (HC3 : rw_cells usegs m3 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
      by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact HC2| cbn; unfold RCTX; lia]).
    assert (TC3 : rw_cells usegs m3 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
      by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [unfold RCTX in TC2 |- *; exact TC2| cbn; unfold RCTX; lia]).
    assert (MI3 : mem_inv usegs m3) by (apply (mem_inv_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn MI2); [intros y Hy; apply ref_ro_addr_false; lia | unfold TASK_SIZE; pose proof (@ceil_hi ACEIL); unfold alloc_ceiling in *; lia]).
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact FR2| cbn; lia]).
    assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros usegs m2 cur 8192 Hc1 Hn1 Hcn); exact ST2).
    assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other usegs m2 cur 8192 Hc1 Hn1 Hcn); [exact ERR2| cbn; rewrite rETP'; lia]).
    pose proof (rw_cells_zeros_new usegs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
    assert (M23 : magree (rFP stI) m2 m3).
    { intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
      destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
      exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| lia]. }
    (* [comment removed for export] *)
    assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
    { intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
    clearbody m3.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
        first [exact TC3 | lia]. }
    intros ms6 ->.
    pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
    eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
    { unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
        [ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
        | rewrite unsigned_lit by lia; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
        rewrite ?A2.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
    intros fa ms7 MP. unfold rmmap_fixed_post in MP.
    (nelim MP 24%nat; intros rr u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m5 REL -> MU5 WM5 MI5 ST5 ERR5).
    rewrite A2.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
    replace (ret_pc (Z_to_bv 64 0x16ca8)) with (Z_to_bv 64 0x16ca8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
    2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
        destruct fa as [e|  |e]; cbn in REL.
        - destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
        - apply orb_true_iff. right. apply Z.eqb_refl.
        - destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    cbn [negb].
    unfold new_region. cbv beta iota zeta delta [fst snd].
    set (rid := s_next_rid stI).
    (nelimp (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) 4%nat; intros AI1 RG1 CQ1 CN1).
    unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
    set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
    rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [heap_lia_pruned | reflexivity]).
    rewrite am_carve_took, carve_st_brk_irrel.
    set (stX := upd_ctx _ st1).
    (* [comment removed for export] *)
    assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 80 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
    { intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
    assert (HC5 : rw_cells usegs m5 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
    { eapply RA2.rrw_cells_agree; [exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
    assert (TC5 : rw_cells usegs m5 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
    { eapply RA2.rrw_cells_agree; [exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
    assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply RA2.rrw_cells_agree; [exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
    eapply rimplT_evt.
    { eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
        first [exact HC5 | exact TC5 | exact MI5 | lia]. }
    intros ms8 nelH_; (nelim nelH_ 7%nat; intros m6 -> MU6 WM6 MI6 HC6 TC6). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
    assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
    destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
    (* [comment removed for export] *)
    assert (E16 : forall y, 0 <= y < 2^64 ->
              ~ (RCTX + 40 <= y < RCTX + 48) -> ~ (RCTX + 920 <= y < RCTX + 928) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
              m6 (wa y) = m1 (wa y)).
    { intros y Hy N0 N1 N2 N3 N4.
      rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; unfold RCTX in *; lia).
      rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
      rewrite (E23 y Hy) by lia.
      apply MU2. rewrite wa_unsigned by lia. cbn. unfold RCTX in *. lia. }
    assert (MRn1 : rmrep st1 m1).
    { unfold st1. apply (RA2.rmrep_new_region stI m1 m1 cur 8192 RKBrk);
        first [ exact MR1
              | eapply ptrs_in_mono; [| exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; heap_lia_pruned
              | exact FRr | exact FRs
              | unfold alloc_ceiling; change (round_up_pg 8192) with 8192; heap_lia_pruned
              | change (round_up_pg 8192) with 8192; exact RF
              | intros; reflexivity
              | intros; discriminate
              | heap_lia_pruned ]. }
    assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; exact Hq).
    (nelimp PTRI 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
    assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
    { intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
    assert (MRX : rmrep stX m6).
    { apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RMLOCK, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RLIBC, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RGOT_SSP, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RSSP_GUARD, RCTX in *; lia.
      - intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
        (nelim (rarea_conc stI a ar WF1 Ha) 10%nat; intros rra Hra Ca Sa0 Sa1 SaL NKa RBa RBAa RBCa).
        (nelim (WR _ _ Hra) 5%nat; intros _ _ _ _ RFa). (nelim (rreserved_disjoint _ _ RFa) 4%nat; intros Da1 _ Da23 Da2). unfold alloc_ceiling in RBCa.
        rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
        apply E16; rewrite ?rETP'; unfold RCTX; try heap_lia_pruned. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [exact Ha| heap_lia_pruned].
      - intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
        (nelim (rgroup_conc stI b gh WF1 Hb) 9%nat; intros rb Hrb Cb Krb Sb0 Sb1 Alb RBb RBCb).
        (nelim (WR _ _ Hrb) 5%nat; intros _ _ _ _ RFb). (nelim (rreserved_disjoint _ _ RFb) 4%nat; intros Db1 _ Db23 Db2). unfold alloc_ceiling in RBCb.
        pose proof (round_up_pg_ge (r_len rb)).
        rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
        apply E16; rewrite ?rETP'; unfold RCTX; try heap_lia_pruned. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. exists b, gh. split; [exact Hb| heap_lia_pruned].
      - intros q rq Hq Kq y Hy.
        assert (Hq' : (s_regions stI) !! q = Some rq).
        { change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
          destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; exact Hq]. }
        (nelim (WR _ _ Hq') 5%nat; intros RB0 _ _ RBC RFq). (nelim (rreserved_disjoint _ _ RFq) 4%nat; intros Dq1 _ Dq23 Dq2). unfold alloc_ceiling in RBC.
        apply E16; rewrite ?rETP'; unfold RCTX; try heap_lia_pruned. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. exists q, rq. auto.
      - (* [comment removed for export] *)
        destruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5). (* [comment removed for export] *)
        { intros y Hy. apply E16; rewrite ?rETP'; unfold RCTX in *; lia. }
        split; [| split; [exact X2| split; [exact X3| split; [exact X4| split; [exact X5|]]]]].
        + unfold rctx_head_cells. rewrite !PWX by assumption.
          cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
               c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
          change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. exact HC6.
        + unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
          change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. exact TC6. }
    (* [comment removed for export] *)
    assert (ZP3 : rw_cells usegs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
    { destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
      eapply (rrw_cells_of_zeros m3 cur 8192 4096); [exact ZB0| exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
    assert (ZP6 : rw_cells usegs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
    { eapply rw_cells_transport; [| exact MU6| exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; unfold RCTX; lia].
      eapply RA2.rrw_cells_agree; [exact ZP3|].
      cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
    destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
    assert (ST6 : stk usegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
    assert (ERR6 : rw_cells usegs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]; cbn; rewrite rETP'; unfold RCTX; lia).
    assert (FPX : forall y, rFP stI y -> rFP stX y).
    { intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq.
      change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
      rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
    assert (M16 : magree (rFP stX) m1 m6).
    { intros y Hy Hc.
      assert (~ (RCTX + 40 <= y < RCTX + 48)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
      assert (~ (RCTX + 920 <= y < RCTX + 928)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
      assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; exact X).
      assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; exact X).
      assert (~ (cur <= y < cur + 8192)).
      { intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| unfold alloc_ceiling; lia| exact X]. }
      apply E16; assumption. }
    replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
    eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
      first [exact RG1 | exact MRX | exact MI6 | exact FR6 | exact ST6 | exact ERR6 | reflexivity | idtac].
    all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | heap_lia_pruned]).
    + unfold stX. apply (rAMI_ctx st st1 _ AI1).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AI1).
      * left. reflexivity.
      * right. right. exists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [exact RG1|]. cbn. discriminate.
    + change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
      exfalso. (nelim (WA _ _ EA) 3%nat; intros rr0 Hrr _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
    + intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
      exfalso. (nelim (MKI _ _ EM) 6%nat; intros a ar kk Ha Hk Eq). (nelim (WA _ _ Ha) 3%nat; intros rr0 Hrr _).
      assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
    + intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
    + cbn. lia.
    + cbn. exact INII.
    + change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZB.
    + change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZW.
    + eapply rauxv_ok_magree; [exact AUX1| exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
    + eapply magree_trans; [exact AG1| exact M16| exact FPX| intros y X; exact X].
    + unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
      change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl.
    replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
    eapply rimplT_evt.
    { eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
        first [exact MR1 | exact MU2 | exact WM2 | exact ACNT | exact MI2 | reflexivity | exact TC2 | lia]. }
    intros ms6 nelH_; (nelim nelH_ 6%nat; intros m3 -> MU3 WM3 MI3 MRD).
    assert (M23 : magree (rFP stI) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
    eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
    + apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
    + exact RGI.
    + exact ACNT.
    + cbn. exact INII.
    + change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
    + exact TLI.
    + exact MKI.
    + (nelimp PTRI 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
    + eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
    + eapply rauxv_ok_magree; [exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
      eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X].
    + eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X] | |];
        intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rbody_spec : forall (stI : mstate) (x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (junk : list byte) (e1 : word),
  RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  c_init_done (ctx stI) <> 0 ->   (* [comment removed for export] *)
  rmrep stI m1 -> mem_inv usegs m1 ->
  rw_cells usegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk usegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells usegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (am_body stI k bail) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x16bd0) fc None m1 (seg_rom usegs)).
Proof using AMP ERR KH LO LOLE TK TP.
  intros until e1. intros AMPI AI RGI BLI INII MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof MR1 as (WF1 & _).
  unfold am_body.
  destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
  - (* [comment removed for export] *)
    pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
    pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
    pose proof (CLs h HN0) as MSh.
    (nelimp (amp_fml stI AMPI h HM0 HN0) 3%nat; intros CL0 FMn FMp).
    destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
    destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
    2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
    destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
    assert (SELF : nx = h <-> pv = h).
    { split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
    eapply rimplT_evt.
    { eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
        first [exact MR1 | exact MI1 | exact FMH | exact MSh | exact HN | exact HP | exact MSn | exact MSp | exact SELF | exact FR1 | exact ST1 | exact LO | lia]. }
    intros ms2 RP. unfold ram_ret_post in RP.
    (nelim RP 21%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m2 -> PE2 WM2 MI2 ST2 MR2).
    eapply rfinish_K.
    + eapply (ram_rel_deq st stI h nx pv AI); try assumption.
      * rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HN.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HP.
      * eapply meta_slot_same_areas; [| exact MSh]. symmetry. exact (ami_areas _ _ AI).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact CL0.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
    + exact MR2.
    + exact MI2.
    + exact ST2.
    + eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
    + pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
      eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [exact RD| exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); exact X].
    + unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
      unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). exact BLI.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
    + (* [comment removed for export] *)
      eapply rimplT_evt.
      { eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact FMH| exact CNT]. }
      intros ms2 ->.
      assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
      assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
      assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
      { apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
        destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
      destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
      * (* [comment removed for export] *)
        destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
        -- (* [comment removed for export] *)
           eapply (rbrk_untried_path stI m1 junk e1); first [exact INII | exact AMPI | exact AI | exact RGI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | reflexivity].
        -- (* [comment removed for export] *)
           eapply rimplT_evt.
           { eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
           intros ms3 ->.
           eapply (rmmap_path stI m1 s junk e1); first [exact INII | exact AI | exact RGI | exact ACNT | exact TLI | exact MKI | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
           pose proof (amp_shift stI AMPI). lia.
        -- (* [comment removed for export] *)
           eapply (rbrk_live_path stI brid boff m1 junk e1); first [exact INII | exact AMPI | exact AI | exact RGI | exact BLI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1].
      * (* [comment removed for export] *)
        (nelim (amp_avail_areas stI AMPI ACNT) 10%nat; intros p r AMA Hr NK PAL P0 PLR PHI FRA).
        pose proof (amp_acount stI AMPI) as ACR.
        unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
        eapply rimplT_evt.
        { eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
            first [exact MR1 | exact ACNT | exact AMA | exact Hr | unfold pgal, PGSZ in *; exact PAL | heap_lia_pruned | idtac]. unfold PGSZ in *. lia. }
        intros ms3 ->.
        eapply (rfinish_path stI p r m1 s junk e1); first [exact INII | exact AI | exact AMA | exact Hr | exact NK | exact P0 | exact PLR | exact TLI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
        -- unfold PGSZ in PHI. lia.
        -- unfold pgal. unfold PGSZ in PAL. exact PAL.
        -- apply (proj1 (FRA p eq_refl ltac:(lia))).
        -- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
        -- lia.
    + (* [comment removed for export] *)
      (nelim (amp_avail stI AMPI CNT) 8%nat; intros aa ar kk Haa AVM K0 K1 MQ).
      pose proof (amp_count stI AMPI) as CR.
      assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
      rewrite (am_take_eq stI k bail _ AVM).
      eapply rimplT_evt.
      { eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
          first [exact MR1 | exact MI1 | exact FMH | exact CNT | exact AVM | exact MSq | exact FR1 | exact ST1 | exact LO | unfold NSLOTS in CR; lia | lia]. }
      intros ms2 RP. unfold ram_ret_post in RP.
      (nelim RP 21%nat; intros v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m2 -> PE2 WM2 MI2 ST2 MR2).
      eapply rfinish_K.
      * eapply (ram_rel_take st stI _ AI).
        -- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
        -- rewrite <- (ami_metas _ _ AI). exact MQ.
        -- eapply meta_slot_same_areas; [| exact MSq]. symmetry. exact (ami_areas _ _ AI).
      * exact MR2.
      * exact MI2.
      * exact ST2.
      * eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
      * eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
      * eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [| exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); exact X].
      * unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold pw, oconc, wz. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ralloc_meta_main : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rimplT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom usegs)).
Proof.
  intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. unfold alloc_ceiling in LO'. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MR as (WF0 & _).
  rewrite alloc_meta_eq. unfold ralloc_meta_entry.
  eapply rimplT_evt.
  { eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
      first [exact MR | exact MI | exact AUX | exact ST | exact LO | exact (amp_init st AMP) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
  intros ms1 nelH_; (nelim nelH_ 27%nat; intros x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk -> MU1 WM1 MI1 FR1 ST1 MR1).
  assert (M01 : magree (rFP (am_init_st st)) m m1).
  { eapply magree_of_munch; [exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
    - left. left. lia.
    - left. right. right. left. unfold RCTX in *. lia. }
  eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
  - exact (rAMpre_init st AMP).
  - exact (rAMI_init st AMP).
  - exact (ram_init_regions st).
  - unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. exact BL.
  - (* [comment removed for export] *)
    unfold am_init_st. destruct (c_init_done (ctx st) =? 0) eqn:EI; cbn; [discriminate | apply Z.eqb_neq; exact EI].
  - exact MR1.
  - exact MI1.
  - exact FR1.
  - exact ST1.
  - eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite rETP'. cbn. unfold RCTX. lia.
  - eapply rauxv_ok_magree; [exact AUX| exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
  - exact M01.
Qed.
End ASM.

Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof.
  unfold ralloc_meta_stmt. intros.
  eapply ralloc_meta_main; eassumption.
Qed.




End CeilWrap.
