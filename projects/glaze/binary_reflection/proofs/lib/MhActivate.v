(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.MhBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition is_freedb (s : slot_st) : bool := match s with SFreed => true | _ => false end.
Lemma is_freedb_true : forall s, is_freedb s = true <-> s = SFreed.
Proof. intros s; destruct s; cbn; split; intros H; try reflexivity; try discriminate H. Qed.

Section Activate.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (h : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st h.
  Hypothesis Hhead : h = head_of (s_alist st (g_sc st h)).
  Hypothesis Hav0 : mr_avail (s_meta st h) = 0.
  #[local] Notation fr := (mr_freed (s_meta st h)).
  #[local] Notation ai := (s_ai st h).
  Definition av' : Z := lo_bits fr (ai + 1).
  Definition fr' : Z := hi_bits fr (ai + 1).

  Definition a_slot (x k : Z) : slot_st :=
    if ((x =? h) && (k <=? ai) && is_freedb (s_slot st x k))%bool then SAvail else s_slot st x k.
  Definition a_meta (x : Z) : meta_rec :=
    if x =? h then MR (mr_prev (s_meta st h)) (mr_next (s_meta st h)) (mr_mem (s_meta st h)) av' fr' (mr_W (s_meta st h))
    else s_meta st x.
  Definition st' : mst :=
    MST (s_ctx st) (s_areas st) a_meta (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        a_slot (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).


  (* [comment removed for export] *)
  Lemma h_wfg : wf_group st L h. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) h Hgrp). Qed.
  Lemma h_U : metaU st h. Proof using Hgrp HWF L RN. exact (wg_U st L h h_wfg). Qed.
  Lemma h_rng : HEAPLO + 24 <= h /\ h + 40 <= CEIL.
  Proof using Hgrp HWF L st. destruct (metaU_rng st L HWF h h_U) as (A & B & _). lia. Qed.
  Lemma ai_rng : 0 <= ai <= g_lastidx st h. Proof using Hgrp HWF L RN. exact (wg_ai st L h h_wfg). Qed.
  Lemma fr_rng : 0 <= fr < 2 ^ 32. Proof using Hgrp HWF L RN. exact (wg_frr st L h h_wfg). Qed.
  Lemma av'_rng : 0 <= av' < 2 ^ 32.
  Proof using Hgrp HWF L RN. unfold av'. pose proof fr_rng. pose proof ai_rng. destruct (lo_bits_range fr (ai + 1) ltac:(lia) ltac:(lia)). lia. Qed.
  Lemma fr'_rng : 0 <= fr' < 2 ^ 32.
  Proof using Hgrp HWF L RN. unfold fr'. pose proof fr_rng. pose proof ai_rng. destruct (hi_bits_range fr (ai + 1) ltac:(lia) ltac:(lia)). lia. Qed.
  Lemma no_avail : forall k, 0 <= k <= g_lastidx st h -> s_slot st h k <> SAvail.
  Proof using Hav0 Hgrp HWF L RN.
    intros k Hk E. pose proof (proj2 (wg_av st L h h_wfg k ltac:(lia)) (conj (proj2 Hk) E)) as T.
    rewrite Hav0, Z.bits_0 in T. discriminate T.
  Qed.

  (* [comment removed for export] *)
  Lemma e_meta_h : s_meta st' h = MR (mr_prev (s_meta st h)) (mr_next (s_meta st h)) (mr_mem (s_meta st h)) av' fr' (mr_W (s_meta st h)).
  Proof using. cbn. unfold a_meta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_meta_other : forall x, x <> h -> s_meta st' x = s_meta st x.
  Proof using. intros x Hx. cbn. unfold a_meta. destruct (Z.eqb_spec x h); [contradiction | reflexivity]. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = mr_next (s_meta st x).
  Proof using. intros x. cbn. unfold a_meta. destruct (Z.eqb_spec x h); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = mr_prev (s_meta st x).
  Proof using. intros x. cbn. unfold a_meta. destruct (Z.eqb_spec x h); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_mem : forall x, mr_mem (s_meta st' x) = mr_mem (s_meta st x).
  Proof using. intros x. cbn. unfold a_meta. destruct (Z.eqb_spec x h); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_Wr : forall x, mr_W (s_meta st' x) = mr_W (s_meta st x).
  Proof using. intros x. cbn. unfold a_meta. destruct (Z.eqb_spec x h); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_avail_other : forall x, x <> h -> mr_avail (s_meta st' x) = mr_avail (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_freed_other : forall x, x <> h -> mr_freed (s_meta st' x) = mr_freed (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_avail_h : mr_avail (s_meta st' h) = av'. Proof using. rewrite e_meta_h. reflexivity. Qed.
  Lemma e_freed_h : mr_freed (s_meta st' h) = fr'. Proof using. rewrite e_meta_h. reflexivity. Qed.
  Lemma e_gW : forall x, g_W st' x = g_W st x. Proof using. intros; unfold g_W; apply e_Wr. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof using. intros; unfold g_mem; apply e_mem. Qed.
  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof using. intros; unfold g_lastidx; rewrite e_gW; reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using. intros; unfold g_sc; rewrite e_gW; reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof using. intros; unfold g_maplen; rewrite e_gW; reflexivity. Qed.
  Lemma e_gcnt : forall x, g_cnt st' x = g_cnt st x. Proof using. intros; unfold g_cnt; rewrite e_glast; reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x.
  Proof using. intros; unfold g_stride; rewrite e_gml, e_glast, e_gsc; reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k.
  Proof using. intros; unfold g_slot_start; rewrite e_gmem, e_gstride; reflexivity. Qed.
  Lemma e_slot : forall x k, s_slot st' x k = a_slot x k. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = s_regions st. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_ctx : s_ctx st' = s_ctx st. Proof using. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = s_limbo st. Proof using. reflexivity. Qed.
  Lemma e_gse : forall x k, g_slot_end st' x k = g_slot_end st x k.
  Proof using. intros; unfold g_slot_end; rewrite e_gss, e_gstride; reflexivity. Qed.
  Lemma a_slot_cases : forall x k,
    (a_slot x k = s_slot st x k /\ (x = h -> k <= ai -> s_slot st x k <> SFreed)) \/
    (x = h /\ k <= ai /\ s_slot st x k = SFreed /\ a_slot x k = SAvail).
  Proof using.
    intros x k. unfold a_slot. destruct (Z.eqb_spec x h) as [->|Hx]; cbn [andb].
    - destruct (Z.leb_spec k ai) as [Hk|Hk]; cbn [andb].
      + destruct (is_freedb (s_slot st h k)) eqn:F.
        * right. apply is_freedb_true in F. repeat split; try assumption. 
        * left. split; [reflexivity|]. intros _ _ E. rewrite E in F. discriminate F.
      + left. split; [reflexivity|]. intros _ Hk'. lia.
    - left. split; [reflexivity|]. intros E. contradiction.
  Qed.
  Lemma a_slot_other : forall x k, x <> h -> a_slot x k = s_slot st x k.
  Proof using. intros x k Hx. unfold a_slot. destruct (Z.eqb_spec x h); [contradiction|]. reflexivity. Qed.

  Lemma SLa : same_layout st st'.
  Proof using.
    constructor; try reflexivity.
    - intros x k. rewrite e_slot. destruct (a_slot_cases x k) as [[E _]|(_ & _ & S & E)]; rewrite E; [apply slot_sim_refl|].
      right. rewrite S. tauto.
    - intros; apply e_mem.
    - intros; apply e_Wr.
  Qed.

  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x. Proof using. intros; unfold listed; rewrite e_in_flist, e_in_alist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using. intros; unfold fresh; rewrite e_areas, e_ctx; tauto. Qed.

  (* [comment removed for export] *)
  Lemma av'_bit : forall j, 0 <= j -> Z.testbit av' j = (Z.testbit fr j && (j <=? ai))%bool.
  Proof using Hgrp HWF L RN.
    intros j Hj. unfold av', lo_bits. pose proof ai_rng.
    destruct (Z.le_gt_cases j ai) as [A|A].
    - rewrite Z.mod_pow2_bits_low by lia. replace (j <=? ai) with true by (symmetry; apply Z.leb_le; lia). rewrite Bool.andb_true_r. reflexivity.
    - rewrite Z.mod_pow2_bits_high by lia. replace (j <=? ai) with false by (symmetry; apply Z.leb_gt; lia). rewrite Bool.andb_false_r. reflexivity.
  Qed.
  Lemma fr'_bit : forall j, 0 <= j -> Z.testbit fr' j = (Z.testbit fr j && negb (j <=? ai))%bool.
  Proof using Hgrp HWF L RN.
    intros j Hj. unfold fr'. pose proof ai_rng. rewrite testbit_hi_bits by lia.
    destruct (Z.le_gt_cases j ai) as [A|A].
    - replace (ai + 1 <=? j) with false by (symmetry; apply Z.leb_gt; lia). replace (j <=? ai) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - replace (ai + 1 <=? j) with true by (symmetry; apply Z.leb_le; lia). replace (j <=? ai) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L. destruct (WF_ctx st L HWF); constructor; rewrite ?e_ctx, ?e_flist, ?e_alist, ?e_areas, ?e_regions, ?e_brk; assumption. Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hhead Hgrp HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist; try assumption.
    - apply (dll_ext st st'); [intros; rewrite e_next, e_prev; split; reflexivity | exact D1].
    - intros x Hx. destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
      assert (x <> h) by (intros ->; exact (NG Hgrp)).
      rewrite e_metaU, e_is_group, e_fresh. rewrite e_meta_other by assumption. repeat split; assumption.
    - intros sc Hsc. apply (dll_ext st st'); [intros; rewrite e_next, e_prev; split; reflexivity | exact (D2 sc Hsc)].
    - intros sc x Hx. rewrite e_is_group, e_gsc. exact (AU sc x Hx).
    - intros x U NL. rewrite e_next, e_prev. apply LK; [apply e_metaU; exact U | intros Hl; apply NL; apply e_listed; exact Hl].
    - intros x Hl. rewrite e_next, e_prev. apply LKD. apply e_listed. exact Hl.
    - intros sc x Hx Hne.
      assert (Hxh : x <> h).
      { intros ->. apply Hne. destruct (AU sc h Hx) as (_ & _ & E). rewrite <- E. exact Hhead. }
      rewrite e_avail_other, e_freed_other by exact Hxh. exact (RS sc x Hx Hne).
  Qed.

  Lemma t_wf_group_other : forall x, is_group st x -> x <> h -> wf_group st' L x.
  Proof using HWF RN.
    intros x Hx Hxh. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_flist, ?e_kind, ?e_regions, ?e_slot;
      rewrite ?(e_meta_other x Hxh); try assumption.
    - intros k Hk. rewrite e_slot, a_slot_other by exact Hxh. exact (Av k Hk).
    - intros k Hk. rewrite e_slot, a_slot_other by exact Hxh. exact (Fr k Hk).
    - intros k Hk. rewrite e_slot, a_slot_other by exact Hxh. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot, a_slot_other by exact Hxh. exact (High k Hk).
    - intros Hall Hne Hl. apply (Full ltac:(intros k Hk; rewrite <- (a_slot_other x k Hxh), <- e_slot; exact (Hall k Hk)) Hne). apply e_listed. exact Hl.
    - destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride, ?e_slot.
      assert (HG : is_group st' hm) by (apply e_is_group; exact K2).
      assert (HS : a_slot hm j = SHost x hoff).
      { destruct (a_slot_cases hm j) as [[E _]|(_ & _ & S & E)]; rewrite E; [exact K6|]. rewrite K6 in S. discriminate S. }
      repeat (split; [assumption|]). assumption.
    - intros Hall. apply FF. intros k Hk. rewrite <- (a_slot_other x k Hxh), <- e_slot. exact (Hall k Hk).
    - intros k Hk. rewrite e_slot, a_slot_other by exact Hxh. apply (x_slot_wf_same st st' L SLa); [exact Hx|]. exact (Slots k Hk).
    - intros Hsc Hst k Hk. rewrite e_slot, a_slot_other by exact Hxh. exact (Fit Hsc Hst k Hk).
  Qed.

  Lemma t_wf_group_h : wf_group st' L h.
  Proof using Hav0 Hgrp HWF RN.
    pose proof h_wfg as WG. pose proof ai_rng as AI. pose proof fr_rng as FR. pose proof av'_rng as AV. pose proof fr'_rng as FR'.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_flist, ?e_kind, ?e_regions, ?e_slot,
      ?e_avail_h, ?e_freed_h; try assumption.
    - (* [comment removed for export] *) intros k Hk. rewrite av'_bit by exact Hk. rewrite e_slot.
      destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E.
      + split.
        * intros T. apply Bool.andb_true_iff in T. destruct T as [T1 T2]. apply Z.leb_le in T2.
          apply (proj1 (Fr k Hk)) in T1. destruct T1 as [T1 T3]. exfalso. exact (NFk eq_refl T2 T3).
        * intros [Hk1 SA]. exfalso. exact (no_avail k (conj Hk Hk1) SA).
      + split; [intros _; split; [lia | reflexivity]|]. intros _.
        assert (Hkl : k <= g_lastidx st h) by lia.
        rewrite (proj2 (Fr k Hk) (conj Hkl S)). rewrite (proj2 (Z.leb_le k ai) Hk2). reflexivity.
    - (* [comment removed for export] *) intros k Hk. rewrite fr'_bit by exact Hk. rewrite e_slot.
      destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E.
      + destruct (Z.leb_spec k ai) as [B|B]; cbn [negb].
        * rewrite Bool.andb_false_r. split; [intros H; discriminate H | intros [_ SF]; exfalso; exact (NFk eq_refl B SF)].
        * rewrite Bool.andb_true_r. exact (Fr k Hk).
      + rewrite (proj2 (Z.leb_le k ai) Hk2). cbn. rewrite Bool.andb_false_r. split; [intros H; discriminate H | intros [_ H]; discriminate H].
    - (* [comment removed for export] *) intros k Hk SA. rewrite e_slot in SA. destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E in SA; [|exact Hk2].
      exfalso. exact (no_avail k Hk SA).
    - (* [comment removed for export] *) intros k Hk. rewrite e_slot. destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E; [exact (High k Hk) | lia].
    - (* [comment removed for export] *) intros Hall Hne Hl. apply e_listed in Hl. refine (Full _ Hne Hl). intros k Hk.
      destruct (Hall k Hk) as [A B]. rewrite e_slot in A, B.
      destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E in A, B; [split; assumption|]. exfalso. apply A. reflexivity.
    - (* [comment removed for export] *) destruct (s_kind st h) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride, ?e_slot.
      assert (HG : is_group st' hm) by (apply e_is_group; exact K2).
      assert (HS : a_slot hm j = SHost h hoff).
      { destruct (a_slot_cases hm j) as [[E _]|(_ & _ & S & E)]; rewrite E; [exact K6|]. rewrite K6 in S. discriminate S. }
      repeat (split; [assumption|]). assumption.
    - (* [comment removed for export] *) intros Hall. apply FF. intros k Hk. destruct (Hall k Hk) as [A|A]; rewrite e_slot in A.
      + destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E in A; [left; exact A | right; exact S].
      + destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E in A; [right; exact A | discriminate A].
    - (* [comment removed for export] *) intros k Hk. rewrite e_slot. apply (x_slot_wf st st' L SLa); [exact Hgrp|]. exact (Slots k Hk).
    - (* [comment removed for export] *) intros Hsc Hst k Hk. rewrite e_slot.
      destruct (a_slot_cases h k) as [[E NFk]|(_ & Hk2 & S & E)]; rewrite E; [exact (Fit Hsc Hst k Hk)|].
      exfalso. exact (proj2 (Fit Hsc Hst k Hk) S).
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hav0 Hgrp HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - exact ND.
    - intros x Hx. destruct (Z.eq_dec x h) as [->|Hxh]; [apply t_wf_group_h | apply t_wf_group_other; [exact Hx | exact Hxh]].
    - intros m1 m2 H1 H2. rewrite !e_ai, !e_glast, !e_gsc. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. rewrite e_is_group, e_kind, e_gmem, e_gml. exact (REG b len x Hin).
    - intros x F. apply e_fresh in F. rewrite e_meta_other; [exact (FR0 x F)|]. intros ->. exact (wg_notfresh st L h h_wfg F).
    - intros x U NG NFL NFR. apply (OTH x); [apply e_metaU; exact U | rewrite <- e_is_group; exact NG
        | rewrite <- e_in_flist; exact NFL | rewrite <- e_fresh; exact NFR].
    - intros x Hl. destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_listed, e_fresh. repeat split; assumption.
    - intros m1 m2 H1 H2 G1 G2 E. rewrite !e_gsc in E. rewrite !e_glast in G1, G2.
      assert (BK : forall x, (forall k, 0 <= k <= g_lastidx st x -> s_slot st' x k = SAvail \/ s_slot st' x k = SFreed) ->
                   forall k, 0 <= k <= g_lastidx st x -> s_slot st x k = SAvail \/ s_slot st x k = SFreed).
      { intros x G k Hk. specialize (G k Hk). rewrite e_slot in G.
        destruct (a_slot_cases x k) as [[Ea _]|(_ & _ & S & _)]; [rewrite Ea in G; exact G | right; exact S]. }
      exact (ONEFF m1 m2 H1 H2 (BK m1 G1) (BK m2 G2) E).
  Qed.

  Lemma t_WF : WF st' L.
  Proof using Hav0 Hhead Hgrp HWF.
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SLa (WF_areas st L HWF))|]. split; [exact t_wf_lists|].
    split; [exact t_wf_groups|]. split; [exact (wf_geom_ext st st' L SLa HWF (WF_geom st L HWF))|].
    split; [exact (wf_live_ext st st' L SLa (WF_live st L HWF)) |]. split; [exact (wf_regions_ext st st' L SLa HWF eq_refl (WF_regions st L HWF)) | exact (wf_img_ext st st' SLa (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition a_wr (a : Z) : Prop := (sp - MSTK <= a < sp) \/ (h + 24 <= a < h + 32).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> a_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMav : cell M' (h + 24) 4 av'.
  Hypothesis HMfr : cell M' (h + 28) 4 fr'.

  (* [comment removed for export] *)
  Lemma t_REP : REP st' M'.
  Proof using HMfr HMav HMgrow HMwr Hsp Hgrp HREP HWF sp M L RN.
    pose proof h_rng as [MR1 MR2].
    assert (WR : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> CEIL <= a \/ (h + 24 <= a < h + 32)).
    { intros a Hr NE. destruct (HMwr a Hr NE) as [W|W]; [left; ceil; unfold MSTK in *; lia | right; exact W]. }
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (WR a Hr NE); hsep; ceil; unfold HEAPLO, CTX in *; lia.
    - apply (rep_ctx_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow) (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (WR a Hr NE); hsep; ceil; unfold HEAPLO, CTX_END, CTX in *; lia.
      + intros s Hs. right. split; reflexivity.
      + right. split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) (fun x => x =? h)); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (WR a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [ceil; lia|].
        exists h. split; [exact h_U|]. split; [apply Z.eqb_refl | lia].
      + intros x Ux X. apply Z.eqb_eq in X. subst x. rewrite e_meta_h.
        pose proof (metaU_area st L HWF h h_U) as (ar & k & Har & Hk & Hm & _).
        pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hm in RM.
        destruct RM as [P N Me Av Fr Wc].
        assert (AG : agree_on (fun a => h <= a < h + 40 /\ ~ (h + 24 <= a < h + 32)) M M').
        { intros a Hr [Ha Hn]. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (WR a Hr NE); [ceil; lia | exact (Hn ltac:(assumption))]. }
        constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
        * eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact P]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact N]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
        * exact HMav.
        * exact HMfr.
        * eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
      + intros x Ux X. apply Z.eqb_neq in X. exact (e_meta_other x X).
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. apply e_is_group. exact Hx.
      + intros x Hx. rewrite e_mem, e_Wr. repeat split; reflexivity.
      + intros x Hx E. apply (x_endb st st' L SLa HWF); [exact Hx|]. exact E.
      + intros x k Hx Hk. rewrite e_slot. destruct (a_slot_cases x k) as [[E _]|(_ & _ & S & E)]; rewrite E; [left; reflexivity | right; left; reflexivity].
      + intros x a Hx G. apply e_is_group in Hx. apply (x_gcell st st' L SLa HWF) in G; [|exact Hx].
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (WR a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [ceil; lia|].
        exact (gcell_not_meta st L HWF x h a Hx G h_U ltac:(lia)).
      + intros x a Hx G. left. apply (x_gcell st st' L SLa HWF); [apply e_is_group; exact Hx|]. exact G.
  Qed.

  Theorem activate_close : WF st' L /\ REP st' M'.
  Proof using HMfr HMav HMgrow HMwr Hsp Hav0 Hhead Hgrp HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.
End Activate.

