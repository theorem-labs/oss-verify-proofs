(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_wf.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
Definition plain3 (st : slot_st) : Prop :=
  st = SIdle \/ st = STaken \/ exists off n, st = SLive off n.

Section GrpUpd.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  (* [comment removed for export] *)
  Variables (av' fr' aib' : Z) (slots' : list slot_st) (L : Z -> option Z).

  Definition gu_f (fl : mfield) : Z :=
    match fl with FAvail => av' | FFreed => fr' | _ => mt_f mt fl end.
  Let mt' := MT gu_f (RGroup aib' slots').
  Let A' := set_live (ameta_upd A ma mt') L.
  Let scm := mt_sc mt.

  Hypothesis G_len : length slots' = length slots.
  Hypothesis G_kind : forall j st st', nth_error slots j = Some st -> nth_error slots' j = Some st' ->
    st = st' \/ (plain3 st /\ plain3 st').
  Hypothesis G_av : 0 <= av' < 2 ^ (mt_cnt mt).
  Hypothesis G_fr : 0 <= fr' < 2 ^ (mt_cnt mt).
  Hypothesis G_disj : Z.land av' fr' = 0.
  Hypothesis G_aib : 0 <= aib' < 256.
  Hypothesis G_avact : av' < 2 ^ (aib' mod 32 + 1).
  Hypothesis G_aibl : aib' mod 32 <= mt_last mt.
  Hypothesis G_idle : forall j st, nth_error slots' (Z.to_nat j) = Some st -> 0 <= j ->
    (Z.testbit (Z.lor av' fr') j = true <-> st = SIdle).
  Hypothesis G_live : forall j off n, nth_error slots' (Z.to_nat j) = Some (SLive off n) -> 0 <= j ->
    0 <= off /\ 0 <= n /\ 16 * off + n <= mt_stride mt - 4 /\ off < 2^16 /\ off <= 255 /\ mt_stride mt - n < 2^20.
  Hypothesis G_inact : forall j, aib' mod 32 < j <= mt_last mt -> Z.testbit fr' j = true.
  Hypothesis G_nonhead : In ma (a_active A scm) -> ma <> hd 0 (a_active A scm) -> av' = 0 /\ fr' <> 0.
  Hypothesis G_partial : aib' mod 32 < mt_last mt -> aib mod 32 < mt_last mt.
  Hypothesis G_reuse : mt_sc mt < 48 -> Z.lor av' fr' <> 0 -> Z.lor (mt_avail mt) (mt_freed mt) <> 0 \/ 16 * size_class (mt_sc mt) <= mt_stride mt.
  (* [comment removed for export] *)
  Hypothesis HL : forall q k, L q = Some k <->
    (exists j off, 0 <= j /\ nth_error slots' (Z.to_nat j) = Some (SLive off k) /\ q = slot_start mt j + 16 * off) \/
    (exists x mtx aibx slx j off, x <> ma /\ a_meta A x = Some mtx /\ mt_role mtx = RGroup aibx slx /\ 0 <= j /\
       nth_error slx (Z.to_nat j) = Some (SLive off k) /\ q = slot_start mtx j + 16 * off).

  Lemma A'_meta : forall x, a_meta A' x = if Z.eq_dec x ma then Some mt' else a_meta A x.
  Proof using L aib' av' fr' mt slots'. pu_keep (L, aib', av', fr', mt, slots'). intros x. reflexivity. Qed.

  Lemma A'_live : a_live A' = L. Proof using A ma mt'. pu_keep (A, ma, mt'). reflexivity. Qed.

  Lemma A'_meta_other : forall x, x <> ma -> a_meta A' x = a_meta A x.
  Proof using L mt'. pu_keep (L, mt'). intros x Hx. rewrite A'_meta. destruct (Z.eq_dec x ma); [contradiction | reflexivity]. Qed.

  Lemma A'_meta_same : a_meta A' ma = Some mt'.
  Proof using A L aib' av' fr' mt slots'. pu_keep (A, L, aib', av', fr', mt, slots'). rewrite A'_meta. destruct (Z.eq_dec ma ma); [reflexivity | contradiction]. Qed.

  Lemma A'_ctx : a_ctx A' = a_ctx A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_areas : a_areas A' = a_areas A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_freelist : a_freelist A' = a_freelist A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_active : a_active A' = a_active A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_blocks : a_pages A' = a_pages A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_mblocks : a_mblocks A' = a_mblocks A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_xmaps : a_xmaps A' = a_xmaps A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.
  Lemma A'_brk : a_brk_lo A' = a_brk_lo A. Proof using L ma mt'. pu_keep (L, ma, mt'). reflexivity. Qed.

  Lemma mt'_mem : mt_mem mt' = mt_mem mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_w32 : mt_w32 mt' = mt_w32 mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_prev : mt_prev mt' = mt_prev mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_next : mt_next mt' = mt_next mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_avail : mt_avail mt' = av'. Proof using aib' fr' mt slots'. pu_keep (aib', fr', mt, slots'). reflexivity. Qed.
  Lemma mt'_freed : mt_freed mt' = fr'. Proof using aib' av' mt slots'. pu_keep (aib', av', mt, slots'). reflexivity. Qed.
  Lemma mt'_stride : mt_stride mt' = mt_stride mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_cnt : mt_cnt mt' = mt_cnt mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_last : mt_last mt' = mt_last mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_maplen : mt_maplen mt' = mt_maplen mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.
  Lemma mt'_sc : mt_sc mt' = mt_sc mt. Proof using aib' av' fr' slots'. pu_keep (aib', av', fr', slots'). reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma A'_group_inv : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    (x = ma /\ mtx = mt' /\ aibx = aib' /\ slx = slots') \/
    (x <> ma /\ a_meta A x = Some mtx).
  Proof using L av' fr' mt. pu_keep (L, av', fr', mt).
    intros x mtx aibx slx Hx Hrx. rewrite A'_meta in Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
    - left. injection Hx as <-. cbn in Hrx. injection Hrx as <- <-. auto.
    - right. auto.
  Qed.

  Lemma A'_meta_inv : forall x mtx, a_meta A' x = Some mtx ->
    (x = ma /\ mtx = mt') \/ (x <> ma /\ a_meta A x = Some mtx).
  Proof using L aib' av' fr' mt slots'. pu_keep (L, aib', av', fr', mt, slots').
    intros x mtx Hx. rewrite A'_meta in Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
    - left. injection Hx as <-. auto.
    - right. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma slots'_inv : forall j stj, nth_error slots' j = Some stj ->
    nth_error slots j = Some stj \/ (exists st0, nth_error slots j = Some st0 /\ plain3 st0 /\ plain3 stj).
  Proof using G_aib G_av G_fr G_kind G_len aib scm. pu_keep (G_aib, G_av, G_fr, G_kind, G_len, aib, scm).
    intros j stj H.
    assert (Hj : (j < length slots)%nat) by (rewrite <- G_len; apply (proj1 (nth_error_Some slots' j)); rewrite H; discriminate).
    destruct (nth_error slots j) as [st0|] eqn:E; [| apply nth_error_None in E; llia].
    destruct (G_kind j st0 stj E H) as [-> | [P0 P1]]; [left; reflexivity | right; exists st0; auto].
  Qed.

  Lemma slots'_nested : forall j ch, nth_error slots' j = Some (SNested ch) -> nth_error slots j = Some (SNested ch).
  Proof using G_aib G_av G_fr G_kind G_len aib scm. pu_keep (G_aib, G_av, G_fr, G_kind, G_len, aib, scm).
    intros j ch H. destruct (slots'_inv j _ H) as [E | (st0 & E & P0 & P1)]; [exact E|].
    exfalso. destruct P1 as [E1 | [E1 | (off & n & E1)]]; discriminate.
  Qed.

  Lemma slots_nested_kept : forall j ch, nth_error slots j = Some (SNested ch) -> nth_error slots' j = Some (SNested ch).
  Proof using G_aib G_av G_fr G_kind G_len aib scm. pu_keep (G_aib, G_av, G_fr, G_kind, G_len, aib, scm).
    intros j ch H.
    assert (Hj : (j < length slots')%nat) by (rewrite G_len; apply (proj1 (nth_error_Some slots j)); rewrite H; discriminate).
    destruct (nth_error slots' j) as [st1|] eqn:E; [| apply nth_error_None in E; llia].
    destruct (G_kind j _ st1 H E) as [<- | [P0 P1]]; [reflexivity|].
    exfalso. destruct P0 as [E1 | [E1 | (off & n & E1)]]; discriminate.
  Qed.

  Lemma dll_kept : forall l, dll A l -> dll A' l.
  Proof using Hma L mt'. pu_keep (Hma, L, mt').
    intros l Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & Hn & Hp).
    rewrite A'_meta. destruct (Z.eq_dec x ma) as [-> | Hne].
    - exists mt'. rewrite Hma in Hx. injection Hx as E. subst mtx. split; [reflexivity|]. split; [exact Hn | exact Hp].
    - exists mtx. auto.
  Qed.
  Theorem WF_grp_upd : WF A'.
  Proof using G_aib G_aibl G_av G_avact G_disj G_fr G_idle G_inact G_kind G_len G_live G_nonhead G_partial G_reuse HL HW Hma Hr mt'. pu_keep (G_aib, G_aibl, G_av, G_avact, G_disj, G_fr, G_idle, G_inact, G_kind, G_len, G_live, G_nonhead, G_partial, G_reuse, HL, HW, Hma, Hr, mt').
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0]. 
    assert (Hgrp0 := wf_grp0 ma mt aib slots Hma Hr).
    constructor; rewrite ?A'_ctx, ?A'_areas, ?A'_freelist, ?A'_active, ?A'_blocks, ?A'_live, ?A'_mblocks, ?A'_xmaps; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. rewrite A'_meta.
      destruct (Z.eq_dec x ma) as [-> | Hne]; [rewrite Hma; split; discriminate | tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). rewrite A'_meta.
      destruct (Z.eq_dec (meta_addr pg k) ma) as [E | Hne].
      + exfalso. rewrite E, Hma in Hmk. injection Hmk as ->. rewrite Hr in Hrk. discriminate.
      + exists mtk. auto.
    - (* [comment removed for export] *) intros x mtx Hx Hrx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrx; discriminate | eauto].
    - (* [comment removed for export] *) intros x mtx Hx Hrx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrx; discriminate | eauto].
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). rewrite A'_meta.
      destruct (Z.eq_dec x ma) as [-> | Hne]; [|tauto].
      rewrite Hma. split; intros (mtx & E & Hrx); injection E as <-; [rewrite Hr in Hrx | cbn in Hrx]; discriminate.
    - (* [comment removed for export] *) apply dll_kept. exact wf_fl_dll0.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_grp0; eauto].
      destruct Hgrp0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
      rewrite mt'_w32, mt'_cnt, mt'_sc, mt'_maplen, mt'_stride, mt'_mem, mt'_avail, mt'_freed. change (mt_last mt') with (mt_last mt).
      rewrite G_len.
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
      split; [exact G_av|]. split; [exact G_fr|]. split; [exact G_disj|]. split; [exact G_aib|].
      split; [exact G_avact|]. split; [exact G_aibl|]. split; [exact G_idle|]. exact G12.
    - (* [comment removed for export] *) intros x mtx aibx slx j off n Hx Hrx Hj Hj0.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_live0; eauto].
      rewrite mt'_stride. apply (G_live j off n Hj Hj0).
    - (* [comment removed for export] *) intros x mtx aibx slx j ch Hx Hrx Hj Hj0.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + pose proof (slots'_nested _ _ Hj) as Hj'.
        destruct (wf_nested0 ma mt aib slots j ch Hma Hr Hj' Hj0) as (mc & aibc & slc & Hmc & Hrc & H1 & H2 & H3).
        assert (Hcne : ch <> ma).
        { intros ->. rewrite Hma in Hmc. injection Hmc as <-.
          (* [comment removed for export] *)
          destruct Hgrp0 as (G1 & G2 & G3 & G4 & _). pose proof (stride_ge16 mt ltac:(llia) G3).
          unfold slot_start, slot_start_g in H2. lnia. }
        exists mc, aibc, slc. rewrite A'_meta_other by exact Hcne. unfold slot_start in *. rewrite mt'_mem, mt'_stride. auto 10.
      + destruct (wf_nested0 x mtx aibx slx j ch Hx' Hrx Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & H1 & H2 & H3).
        destruct (Z.eq_dec ch ma) as [-> | Hcne].
        * rewrite Hma in Hmc. injection Hmc as <-. rewrite Hr in Hrc. injection Hrc as <- <-.
          exists mt', aib', slots'. rewrite A'_meta_same. rewrite mt'_maplen, mt'_mem, mt'_cnt, mt'_stride. auto 10.
        * exists mc, aibc, slc. rewrite A'_meta_other by exact Hcne. auto 10.
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hml.
      destruct (A'_group_inv ch mc aibc slc Hch Hrc) as [(-> & -> & -> & ->) | (Hne & Hch')].
      + rewrite mt'_maplen in Hml.
        destruct (wf_nested_parent0 ma mt aib slots Hma Hr Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (Z.eq_dec x ma) as [-> | Hxne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists ma, mt', aib', slots', j. rewrite A'_meta_same.
          repeat split; auto. apply slots_nested_kept. exact Hj.
        * exists x, mtx, aibx, slx, j. rewrite A'_meta_other by exact Hxne. auto 10.
      + destruct (wf_nested_parent0 ch mc aibc slc Hch' Hrc Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
        destruct (Z.eq_dec x ma) as [-> | Hxne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists ma, mt', aib', slots', j. rewrite A'_meta_same.
          repeat split; auto. apply slots_nested_kept. exact Hj.
        * exists x, mtx, aibx, slx, j. rewrite A'_meta_other by exact Hxne. auto 10.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      assert (Hx0 : exists mt0 aib0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\
                      mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, aib, slots. auto.
        - exists mtx, aibx, slx. auto. }
      destruct Hx0 as (mt0 & aib0 & sl0 & Hx0 & Hr0 & Hm0 & Hw0).
      destruct (wf_grp_root0 x mt0 aib0 sl0 Hx0 Hr0) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & Hself).
      destruct (gext_ext mt0 mtx ltac:(symmetry; exact Hm0) ltac:(symmetry; exact Hw0)) as [Elo Ehi].
      destruct (Z.eq_dec mr ma) as [-> | Hrne].
      + rewrite Hma in Hmr. injection Hmr as <-. rewrite Hr in Hrr. injection Hrr as <- <-.
        exists ma, mt', aib', slots'. rewrite A'_meta_same.
        rewrite mt'_maplen, mt'_mem. unfold grp_map_len in *. rewrite mt'_maplen. rewrite Elo, Ehi.
        repeat split; auto. intros Hmx. apply Hself. unfold mt_maplen in *. rewrite Hw0. exact Hmx.
      + exists mr, mtr, aibr, slr. rewrite A'_meta_other by exact Hrne. rewrite Elo, Ehi.
        repeat split; auto. intros Hmx. apply Hself. unfold mt_maplen in *. rewrite Hw0. exact Hmx.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hxy.
      (* [comment removed for export] *)
      assert (KX : exists mt0 aib0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\
               mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx /\
               (forall j ch, nth_error sl0 j = Some (SNested ch) -> nth_error slx j = Some (SNested ch))).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, aib, slots. repeat split; auto. apply slots_nested_kept.
        - exists mtx, aibx, slx. repeat split; auto. }
      assert (KY : exists mt0 aib0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\
               mt_mem mt0 = mt_mem mty /\ mt_w32 mt0 = mt_w32 mty /\
               (forall j ch, nth_error sl0 j = Some (SNested ch) -> nth_error sly j = Some (SNested ch))).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')].
        - exists mt, aib, slots. repeat split; auto. apply slots_nested_kept.
        - exists mty, aiby, sly. repeat split; auto. }
      destruct KX as (mx0 & aibx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx & Nx).
      destruct KY as (my0 & aiby0 & sly0 & Hy0 & Hry0 & Emy & Ewy & Ny).
      destruct (gext_ext mx0 mtx ltac:(symmetry; exact Emx) ltac:(symmetry; exact Ewx)) as [Exlo Exhi].
      destruct (gext_ext my0 mty ltac:(symmetry; exact Emy) ltac:(symmetry; exact Ewy)) as [Eylo Eyhi].
      assert (Esx : forall j, slot_start mtx j = slot_start mx0 j /\ slot_end mtx j = slot_end mx0 j).
      { intros j. unfold slot_start, slot_end. rewrite (stride_ext mx0 mtx) by (symmetry; assumption). rewrite Emx. auto. }
      assert (Esy : forall j, slot_start mty j = slot_start my0 j /\ slot_end mty j = slot_end my0 j).
      { intros j. unfold slot_start, slot_end. rewrite (stride_ext my0 mty) by (symmetry; assumption). rewrite Emy. auto. }
      rewrite Exlo, Exhi, Eylo, Eyhi.
      destruct (wf_laminar0 x mx0 aibx0 slx0 y my0 aiby0 sly0 Hx0 Hrx0 Hy0 Hry0 Hxy)
        as [Hd | [Hd | [(j & ch & Hj0 & Hj & H1 & H2) | (j & ch & Hj0 & Hj & H1 & H2)]]].
      + left. exact Hd.
      + right; left. exact Hd.
      + right; right; left. exists j, ch. destruct (Esx j) as [-> ->]. auto.
      + right; right; right. exists j, ch. destruct (Esy j) as [-> ->]. auto.
    - (* [comment removed for export] *) intros sc Hsc. apply dll_kept. apply wf_act_dll0. exact Hsc.
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aibx & slx & Hx & Hrx & Hscx).
      rewrite A'_meta. destruct (Z.eq_dec x ma) as [-> | Hne].
      + rewrite Hma in Hx. injection Hx as E. subst mtx. rewrite Hr in Hrx. injection Hrx as <- <-.
        exists mt', aib', slots'. split; [reflexivity|]. split; [reflexivity|]. exact Hscx.
      + exists mtx, aibx, slx. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hnin.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + rewrite mt'_prev, mt'_next. eapply (wf_unlinked0 ma mt aib slots); eauto.
      + eapply wf_unlinked0; eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hnh Hx.
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
      + rewrite mt'_avail, mt'_freed.
        destruct (wf_act_mem0 sc ma Hin) as (mt1 & aib1 & sl1 & Hm1 & Hr1 & Hsc1).
        rewrite Hma in Hm1. injection Hm1 as E. subst mt1.
        apply G_nonhead; unfold scm; rewrite Hsc1; assumption.
      + eapply wf_act_nonhead0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + rewrite mt'_prev, mt'_next. eapply (wf_act630 ma mt aib slots); eauto.
      + eapply wf_act630; eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + rewrite mt'_mem. unfold grp_map_len. rewrite mt'_maplen. eapply (wf_disj_area_grp0 pg ma mt aib slots); eauto.
      + eapply wf_disj_area_grp0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hmlx Hy Hry Hmly Hxy.
      assert (KX : exists mt0 aib0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_mem mt0 = mt_mem mtx /\ mt_w32 mt0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [exists mt, aib, slots | exists mtx, aibx, slx]; auto. }
      assert (KY : exists mt0 aib0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_mem mt0 = mt_mem mty /\ mt_w32 mt0 = mt_w32 mty).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')]; [exists mt, aib, slots | exists mty, aiby, sly]; auto. }
      destruct KX as (mx0 & aibx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx). destruct KY as (my0 & aiby0 & sly0 & Hy0 & Hry0 & Emy & Ewy).
      unfold grp_map_len, mt_maplen in *. rewrite <- Emx, <- Ewx, <- Emy, <- Ewy in *.
      eapply (wf_disj_grp_grp0 x mx0 aibx0 slx0 y my0 aiby0 sly0); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hmm.
      assert (KX : exists mt0 aib0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_mem mt0 = mt_mem mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [exists mt, aib, slots | exists mtx, aibx, slx]; auto. }
      assert (KY : exists mt0 aib0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_mem mt0 = mt_mem mty).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')]; [exists mt, aib, slots | exists mty, aiby, sly]; auto. }
      destruct KX as (mx0 & aibx0 & slx0 & Hx0 & Hrx0 & Emx). destruct KY as (my0 & aiby0 & sly0 & Hy0 & Hry0 & Emy).
      eapply (wf_grp_mem_inj0 x mx0 aibx0 slx0 y my0 aiby0 sly0); eauto. congruence.
    - (* [comment removed for export] *) intros q k. rewrite HL. unfold is_live. split.
      + intros [(j & off & Hj0 & Hj & Eq) | (x & mtx & aibx & slx & j & off & Hne & Hx & Hrx & Hj0 & Hj & Eq)].
        * exists ma, mt', aib', slots', j, off. rewrite A'_meta_same. repeat split; auto.
        * exists x, mtx, aibx, slx, j, off. rewrite A'_meta_other by exact Hne. repeat split; auto.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Eq).
        destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        * left. exists j, off. auto.
        * right. exists x, mtx, aibx, slx, j, off. auto 10.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_span0; eauto].
      rewrite mt'_last, mt'_cnt, mt'_stride. eapply wf_span0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_single0; eauto].
      rewrite mt'_last, mt'_maplen, mt'_sc, mt'_stride. eapply wf_single0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_inactive0; eauto].
      rewrite mt'_last, mt'_freed. apply G_inact.
    - (* [comment removed for export] *) intros sc x mtx aibx slx y mty aiby sly Hinx Hiny Hx Hrx Hy Hry Hpx Hpy.
      assert (KX : exists mt0 aib0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_last mt0 = mt_last mtx /\ aib0 mod 32 < mt_last mt0).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, aib, slots. rewrite mt'_last in Hpx. repeat split; auto.
        - exists mtx, aibx, slx. repeat split; auto. }
      assert (KY : exists mt0 aib0 sl0, a_meta A y = Some mt0 /\ mt_role mt0 = RGroup aib0 sl0 /\ mt_last mt0 = mt_last mty /\ aib0 mod 32 < mt_last mt0).
      { destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')].
        - exists mt, aib, slots. rewrite mt'_last in Hpy. repeat split; auto.
        - exists mty, aiby, sly. repeat split; auto. }
      destruct KX as (mx0 & ax0 & slx0 & Hx0 & Hrx0 & Elx & Hpx0). destruct KY as (my0 & ay0 & sly0 & Hy0 & Hry0 & Ely & Hpy0).
      eapply (wf_partial0 sc x mx0 ax0 slx0 y my0 ay0 sly0); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_nested_small0; eauto].
      rewrite mt'_last, mt'_maplen, mt'_cnt, mt'_stride. eapply wf_nested_small0; eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_reusable0; eauto].
      rewrite mt'_sc, mt'_stride, mt'_avail, mt'_freed. intros Hsc Hnz.
      destruct (G_reuse Hsc Hnz) as [H | H]; [eapply wf_reusable0; eauto | exact H].
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      assert (KP : exists pm0 aib0 psl0, a_meta A pa = Some pm0 /\ mt_role pm0 = RGroup aib0 psl0 /\
                 mt_mem pm0 = mt_mem pm /\ mt_w32 pm0 = mt_w32 pm /\ nth_error psl0 (Z.to_nat j) = Some (SNested ch)).
      { destruct (A'_group_inv pa pm paib psl Hpa Hpr) as [(-> & -> & -> & ->) | (Hne & Hpa')].
        - exists mt, aib, slots. repeat split; auto. apply slots'_nested. exact Hj.
        - exists pm, paib, psl. repeat split; auto. }
      assert (KX : exists mx0 aib0 slx0, a_meta A x = Some mx0 /\ mt_role mx0 = RGroup aib0 slx0 /\ mt_mem mx0 = mt_mem mtx /\ mt_w32 mx0 = mt_w32 mtx).
      { destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
        - exists mt, aib, slots. repeat split; auto.
        - exists mtx, aibx, slx. repeat split; auto. }
      destruct KP as (pm0 & aibp0 & psl0 & Hpa0 & Hpr0 & Epm & Epw & Hjj).
      destruct KX as (mx0 & aibx0 & slx0 & Hx0 & Hrx0 & Emx & Ewx).
      assert (Esp : slot_start pm j = slot_start pm0 j /\ slot_end pm j = slot_end pm0 j).
      { unfold slot_start, slot_end. rewrite (stride_ext pm0 pm) by (symmetry; assumption). rewrite Epm. auto. }
      destruct (gext_ext mx0 mtx ltac:(symmetry; exact Emx) ltac:(symmetry; exact Ewx)) as [Exlo Exhi].
      destruct Esp as [Es1 Es2]. rewrite Exlo, Exhi. rewrite Exlo, Es1 in Hlo. rewrite Exhi, Es2 in Hhi.
      destruct (wf_cover0 pa pm0 aibp0 psl0 j ch x mx0 aibx0 slx0 Hpa0 Hpr0 Hj0 Hjj Hx0 Hrx0 Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & H1 & H2).
      rewrite A'_meta. destruct (Z.eq_dec ch ma) as [-> | Hnc].
      + rewrite Hma in Hch. injection Hch as E. subst mtc. rewrite Hr in Hrc. injection Hrc as <- <-.
        exists mt', aib', slots'. destruct (gext_ext mt mt' mt'_mem mt'_w32) as [-> ->]. repeat split; auto.
      + exists mtc, aibc, slc. rewrite Hch. repeat split; auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hsc.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_stride200; eauto].
      rewrite mt'_stride. rewrite mt'_sc in Hsc. eapply wf_stride200; eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_disj_page_grp0; eauto].
      rewrite mt'_mem. unfold grp_map_len. rewrite mt'_maplen. rewrite mt'_maplen in Hml.
      eapply (wf_disj_page_grp0 pg ma mt aib slots); eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx Hp.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')]; [| eapply wf_partial_sc0; eauto].
      rewrite mt'_sc. rewrite mt'_last in Hp. eapply (wf_partial_sc0 ma mt aib slots Hma Hr). apply G_partial. exact Hp.
  Qed.



  (* [comment removed for export] *)
  Lemma has_grp_upd : forall f, has A' f ->
    (has A f /\ (has_ctx A f \/ has_area A f \/
                  (exists x mtx fl, x <> ma /\ a_meta A x = Some mtx /\ f = FCT (x + moff fl) (mlen fl) (mt_f mtx fl)) \/
                  (exists x mtx aibx slx, x <> ma /\ a_meta A x = Some mtx /\ mt_role mtx = RGroup aibx slx /\
                     (In f (grp_hdr_fields x mtx aibx) \/ exists j st, nth_error slx j = Some st /\ In f (slot_fields mtx (Z.of_nat j) st)))))
    \/ (exists fl, f = FCT (ma + moff fl) (mlen fl) (gu_f fl))
    \/ In f (grp_hdr_fields ma mt aib')
    \/ (exists j st, nth_error slots' j = Some st /\ In f (slot_fields mt (Z.of_nat j) st)).
  Proof using L. pu_keep (L).
    intros f Hf. destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - left. split; [left; exact Hc | left; exact Hc].
    - left. split; [right; left; exact Har | right; left; exact Har].
    - destruct Hm as (x & mtx & fl & Hx & ->).
      destruct (A'_meta_inv x mtx Hx) as [(-> & ->) | (Hne & Hx')].
      + right; left. exists fl. unfold mt'. rewrite mt_f_MT. reflexivity.
      + left. split; [right; right; left; exists x, mtx, fl; auto |]. right; right; left. exists x, mtx, fl. auto.
    - destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & Hin).
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + destruct Hin as [Hin | (j & stj & Hj & Hin)].
        * right; right; left. unfold grp_hdr_fields in *. rewrite mt'_mem in Hin. exact Hin.
        * right; right; right. exists j, stj. rewrite (slot_fields_ext mt mt' (Z.of_nat j) stj mt'_mem mt'_w32) in Hin. auto.
      + left. split.
        * right; right; right. exists x, mtx, aibx, slx. auto.
        * right; right; right. exists x, mtx, aibx, slx. auto 10.
  Qed.

  (* [comment removed for export] *)
  Lemma has_grp_upd_intro_field : forall fl, has A' (FCT (ma + moff fl) (mlen fl) (gu_f fl)).
  Proof. intros fl. right; right; left. exists ma, mt', fl. rewrite A'_meta_same. unfold mt'. rewrite mt_f_MT. auto. Qed.

  Lemma has_grp_upd_intro_slot : forall j st f, nth_error slots' j = Some st -> In f (slot_fields mt (Z.of_nat j) st) -> has A' f.
  Proof.
    intros j st f Hj Hin. right; right; right. exists ma, mt', aib', slots'. rewrite A'_meta_same.
    split; [reflexivity|]. split; [reflexivity|]. right. exists j, st.
    rewrite (slot_fields_ext mt mt' (Z.of_nat j) st mt'_mem mt'_w32). auto.
  Qed.


  Lemma VMok_grp_upd : forall h, VMok A h -> VMok A' h.
  Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt').
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vlim]. constructor.
    - intros x mtx aibx slx Hx Hrx Hml.
      destruct (A'_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (Hne & Hx')].
      + rewrite mt'_mem. unfold grp_map_len. rewrite mt'_maplen. rewrite mt'_maplen in Hml. eapply (Vg ma mt aib slots); eauto.
      + eapply Vg; eauto.
    - rewrite A'_ctx. exact Vb.
    - rewrite A'_ctx. exact Va.
    - exact Vres.
    - exact Vbv.
    - exact Vpw.
    - exact Vmw.
    - exact Vna.
    - rewrite A'_areas. exact Vac.
    - exact Vpc.
    - (* [comment removed for export] *) intros b sz Hin. rewrite A'_mblocks, A'_xmaps.
      destruct (Vall b sz Hin) as [(x & mtx & aibx & slx & Hx & Hrx & Hml & Eb & Esz) | [Hbr | Hbl]]; [left | right; left; exact Hbr | right; right; exact Hbl].
      destruct (Z.eq_dec x ma) as [-> | Hne].
      + rewrite Hma in Hx. injection Hx as <-. exists ma, mt', aib', slots'. rewrite A'_meta.
        rewrite mt'_mem. unfold grp_map_len in *. rewrite mt'_maplen. destruct (Z.eq_dec ma ma); [| contradiction]. repeat split; auto.
      + exists x, mtx, aibx, slx. rewrite A'_meta. destruct (Z.eq_dec x ma); [contradiction|]. repeat split; auto.
    - rewrite A'_ctx, A'_areas. exact Vspan.
    - exact Vlim.
  Qed.

  Lemma dom_grp_upd : forall x, dom A' x <-> dom A x.
  Proof using Hma Hr L mt'. pu_keep (Hma, Hr, L, mt').
    intros x. unfold dom. rewrite A'_areas. split.
    - intros [H | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | H]]; [left; exact H | right; left | right; right; exact H].
      destruct (A'_group_inv y mty aiby sly Hy Hry) as [(-> & -> & -> & ->) | (Hne & Hy')].
      + exists ma, mt, aib, slots. rewrite mt'_maplen, mt'_mem in *. unfold grp_map_len in *. rewrite mt'_maplen in Hx. auto.
      + exists y, mty, aiby, sly. auto.
    - intros [H | [(y & mty & aiby & sly & Hy & Hry & Hml & Hx) | H]]; [left; exact H | right; left | right; right; exact H].
      destruct (Z.eq_dec y ma) as [-> | Hne].
      + rewrite Hma in Hy. injection Hy as E. subst mty. rewrite Hr in Hry. injection Hry as <- <-.
        exists ma, mt', aib', slots'. rewrite A'_meta_same. rewrite mt'_maplen, mt'_mem. unfold grp_map_len in *. rewrite mt'_maplen. auto.
      + exists y, mty, aiby, sly. rewrite A'_meta_other by exact Hne. auto.
  Qed.
End GrpUpd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma slot_fact_cases : forall A, WF A -> forall ma mt aib slots i st f,
  a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
  nth_error slots i = Some st -> In f (slot_fields mt (Z.of_nat i) st) ->
  f = FCT (slot_start mt (Z.of_nat i) - 4) 1 0 \/
  (slot_start mt (Z.of_nat i) - 3 <= f_a f /\ f_a f + f_n f <= slot_end mt (Z.of_nat i) + 1).
Proof using Type. pu_keep tt.
  intros A HW ma mt aib slots i st f Hma Hr Hi Hf.
  destruct (wf_grp A HW ma mt aib slots Hma Hr) as
    (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
  pose proof (stride_ge16 mt ltac:(llia) Hsc) as Hstride.
  unfold slot_fields, slot_fields_g in Hf. unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
  set (S := mt_stride mt) in *. set (M := mt_mem mt) in *.
  apply in_app_iff in Hf. destruct Hf as [Hf | Hf].
  { destruct Hf as [<- | [<- | []]]; [left; reflexivity | right; cbn [f_a f_n]; llia]. }
  right.
  destruct st as [ | | off n | ch].
  - destruct Hf.
  - destruct Hf.
  - pose proof (wf_live A HW ma mt aib slots (Z.of_nat i) off n Hma Hr ltac:(rewrite Nat2Z.id; exact Hi) ltac:(llia))
      as (Hoff & Hn & Hfit2 & Hoff16 & _). fold S in Hfit2.
    repeat (apply in_app_iff in Hf; destruct Hf as [Hf | Hf]).
    + destruct (off =? 0) eqn:E; [destruct Hf|]. apply Z.eqb_neq in E.
      destruct Hf as [<- | [<- | [<- | []]]]; cbn [f_a f_n]; llia.
    + destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
    + destruct (M + 16 + Z.of_nat i * S + S - 4 - (M + 16 + Z.of_nat i * S + 16 * off) - n <? 5) eqn:E; [destruct Hf|].
      apply Z.ltb_ge in E.
      destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
    + destruct (M + 16 + Z.of_nat i * S + S - 4 - (M + 16 + Z.of_nat i * S + 16 * off) - n =? 0) eqn:E; [destruct Hf|].
      apply Z.eqb_neq in E.
      destruct Hf as [<- | []]; cbn [f_a f_n]; llia.
  - destruct Hf as [<- | [<- | []]]; cbn [f_a f_n]; llia.
Qed.

Section Locate.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.

  (* [comment removed for export] *)
  Lemma fact_locate : forall f, has A f ->
    (exists fl, f = FCT (ma + moff fl) (mlen fl) (mt_f mt fl)) \/
    In f (grp_hdr_fields ma mt aib) \/
    (exists j st, nth_error slots j = Some st /\ In f (slot_fields mt (Z.of_nat j) st)) \/
    (exists j ch, nth_error slots j = Some (SNested ch) /\
       slot_start mt (Z.of_nat j) <= f_a f /\ f_a f + f_n f <= slot_end mt (Z.of_nat j) + 1) \/
    ((f_a f + f_n f <= ma \/ ma + 40 <= f_a f) /\ (f_a f + f_n f <= gext_lo mt \/ gext_hi mt <= f_a f)).
  Proof using HW Hma Hr MLok. pu_keep (HW, Hma, Hr, MLok).
    intros f Hf.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16.
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & Hself).
    destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpgr).
    destruct (Hpgr Hml) as [_ Hheap].
    pose proof (has_addr A HW f Hf) as (Hfn & Hf1 & Hf2 & _).
    destruct Hf as [Hc | [Har | [Hm | Hg]]].
    - right; right; right; right. split.
      + destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_introl Hc)); llia.
      + pose proof (has_ctx_where A f Hc) as (C1 & C2 & C3). destruct Hc as (k & Hk & ->). cbn in *.
        destruct (heap_avoids_ctx _ _ Hheap k Hk); unfold gext_lo, gext_hi in *; llia.
    - right; right; right; right. split.
      + destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_introl Har))); llia.
      + destruct Har as (pg & Hpga & ->). cbn in *.
        destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - destruct Hm as (x & mtx & fl & Hx & ->).
      destruct (Z.eq_dec x ma) as [-> | Hne].
      + left. rewrite Hma in Hx. injection Hx as ->. exists fl. reflexivity.
      + right; right; right; right. cbn. pose proof (mfield_range fl). split.
        * destruct (other_meta_avoid_meta A HW ma mt Hma x mtx fl Hx Hne); llia.
        * destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpga & Hk & ->).
          pose proof (meta_addr_range pg k Hk).
          destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & Hin).
      destruct (Z.eq_dec x ma) as [-> | Hne].
      + rewrite Hma in Hx. injection Hx as ->. rewrite Hr in Hrx. injection Hrx as <- <-.
        destruct Hin as [Hin | (j & st & Hj & Hin)]; [right; left; exact Hin | right; right; left; exists j, st; auto].
      + (* [comment removed for export] *)
        assert (Hgf : has_grp A f) by (exists x, mtx, aibx, slx; auto).
        assert (Hmeta : f_a f + f_n f <= ma \/ ma + 40 <= f_a f).
        { destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_intror Hgf))); llia. }
        assert (Hfin : gext_lo mtx <= f_a f /\ f_a f + f_n f <= gext_hi mtx + 1).
        { destruct (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw32' & _ & Hsc' & Hlen' & _).
          pose proof (stride_ge16 mtx ltac:(llia) Hsc') as HS'.
          destruct Hin as [Hin | (j & st & Hj & Hin)].
          - unfold gext_lo, gext_hi. assert (0 <= mt_cnt mtx * mt_stride mtx) by lnia.
            destruct Hin as [<- | [<- | []]]; cbn; llia.
          - pose proof (slot_fields_where A HW x mtx aibx slx j st f Hx Hrx Hj Hin). llia. }
        destruct (wf_laminar A HW ma mt aib slots x mtx aibx slx Hma Hr Hx Hrx ltac:(congruence))
          as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
        * right; right; right; right. split; [exact Hmeta | llia].
        * right; right; right; right. split; [exact Hmeta | llia].
        * (* [comment removed for export] *)
          right; right; right; left. exists (Z.to_nat j), ch. rewrite Z2Nat.id by llia. split; [exact Hj | llia].
        * (* [comment removed for export] *)
          destruct (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw32' & _ & Hsc' & Hlen' & _ & _ & _ & _ & _ & _ & _ & Hal16' & _).
          pose proof (stride_ge16 mtx ltac:(llia) Hsc') as HS'.
          destruct Hin as [Hin | (j' & st' & Hj' & Hin)].
          -- right; right; right; right. split; [exact Hmeta|].
             left. unfold slot_start, slot_start_g in Hjlo. assert (0 <= j * mt_stride mtx) by lnia.
             destruct Hin as [<- | [<- | []]]; cbn; llia.
          -- pose proof (slot_fact_bounds A HW x mtx aibx slx j' st' f Hx Hrx Hj' Hin) as (B1 & B2).
             destruct (Z.lt_total (Z.of_nat j') j) as [Hlt | [Heq | Hgt]].
             ++ right; right; right; right. split; [exact Hmeta|]. left.
                unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
                pose proof (slots_disjoint (mt_mem mtx) (mt_stride mtx) (Z.of_nat j') j HS' ltac:(llia) Hj0 Hlt). llia.
             ++ assert (CASE : f = FCT (slot_end mtx j) 1 0 \/ f_a f + f_n f <= slot_start mtx j \/ slot_end mtx j + 1 <= f_a f).
                { rewrite <- Heq, Nat2Z.id in Hj. rewrite Hj in Hj'. injection Hj' as <-.
                  unfold slot_fields, slot_fields_g in Hin. apply in_app_iff in Hin.
                  unfold slot_start, slot_end. rewrite <- Heq.
                  destruct Hin as [[<- | [<- | []]] | [<- | [<- | []]]]; [right; left | left; reflexivity | right; left | right; left]; cbn [f_a f_n]; unfold slot_start_g, slot_end_g; llia. }
                clear Hin B1 B2.
                destruct CASE as [Ef | [Hlow | Hhigh]];
                  [| right; right; right; right; split; [exact Hmeta | left; unfold gext_lo, slot_start, slot_start_g in *; llia]
                   | right; right; right; right; split; [exact Hmeta | right; llia]].
                destruct (Z.eq_dec (gext_hi mt) (slot_end mtx j)) as [Efill | Hnf].
                ** (* [comment removed for export] *)
                   right; right; left. rewrite Ef.
                   destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32m & _ & Hscm & Hlenm & _).
                   assert (Hcnt : (0 < length slots)%nat) by (unfold mt_cnt in Hlenm; pose proof (w_last_range (mt_w32 mt)); unfold mt_last in Hlenm; llia).
                   destruct (nth_error slots (length slots - 1)) as [stl|] eqn:El.
                   2:{ exfalso. apply (proj2 (nth_error_Some slots (length slots - 1)%nat)); [llia | exact El]. }
                   exists (length slots - 1)%nat, stl. split; [exact El|].
                   replace (slot_end mtx j) with (slot_end mt (Z.of_nat (length slots - 1))).
                   2:{ unfold gext_hi, slot_end, slot_end_g in *. rewrite Nat2Z.inj_sub by llia. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 1) with 1. rewrite Hlenm in *. unfold mt_cnt in *. llia. }
                   unfold slot_fields, slot_fields_g, slot_end. cbn. right. left. reflexivity.
                ** (* [comment removed for export] *)
                   right; right; right; right. split; [exact Hmeta|]. right. rewrite Ef. cbn [f_a].
                   destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32m & _ & Hscm & Hlenm & _ & _ & _ & _ & _ & _ & _ & Hal16m & _).
                   destruct (stride_16 mt) as [q Hq]. destruct (stride_16 mtx) as [q' Hq'].
                   unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g in *.
                   rewrite Hq in *. rewrite Hq' in *.
                   set (u := mt_cnt mt * q) in *. set (u' := j * q') in *.
                   replace (mt_cnt mt * (16 * q)) with (16 * u) in * by llia.
                   replace (j * (16 * q')) with (16 * u') in * by llia.
                   assert (E1 : mt_mem mt = 16 * (mt_mem mt / 16)) by llia.
                   assert (E2 : mt_mem mtx = 16 * (mt_mem mtx / 16)) by llia.
                   rewrite E1, E2 in *. llia.
             ++ (* [comment removed for export] *)
                destruct (slot_fact_cases A HW x mtx aibx slx j' st' f Hx Hrx Hj' Hin) as [Ef | Hf3].
                ** destruct (Z.eq_dec (Z.of_nat j') (j + 1)) as [Ej1 | Hne1].
                   +++ (* [comment removed for export] *)
                       assert (Ee : f = FCT (slot_end mtx j) 1 0).
                       { rewrite Ef. f_equal. unfold slot_start, slot_end, slot_start_g, slot_end_g. rewrite Ej1. llia. }
                       clear Ef. rename Ee into Ef.
                       destruct (Z.eq_dec (gext_hi mt) (slot_end mtx j)) as [Efill | Hnf].
                       *** right; right; left. rewrite Ef.
                           destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32m & _ & Hscm & Hlenm & _).
                           assert (Hcnt : (0 < length slots)%nat) by (unfold mt_cnt in Hlenm; pose proof (w_last_range (mt_w32 mt)); unfold mt_last in Hlenm; llia).
                           destruct (nth_error slots (length slots - 1)) as [stl|] eqn:El.
                           2:{ exfalso. apply (proj2 (nth_error_Some slots (length slots - 1)%nat)); [llia | exact El]. }
                           exists (length slots - 1)%nat, stl. split; [exact El|].
                           replace (slot_end mtx j) with (slot_end mt (Z.of_nat (length slots - 1))).
                           2:{ unfold gext_hi, slot_end, slot_end_g in *. rewrite Nat2Z.inj_sub by llia. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 1) with 1. rewrite Hlenm in *. unfold mt_cnt in *. llia. }
                           unfold slot_fields, slot_fields_g, slot_end. cbn. right. left. reflexivity.
                       *** right; right; right; right. split; [exact Hmeta|]. right. rewrite Ef. cbn [f_a].
                           destruct (wf_grp A HW ma mt aib slots Hma Hr) as (Hw32m & _ & Hscm & Hlenm & _ & _ & _ & _ & _ & _ & _ & Hal16m & _).
                           destruct (stride_16 mt) as [q Hq]. destruct (stride_16 mtx) as [q' Hq'].
                           unfold gext_lo, gext_hi, slot_start, slot_end, slot_start_g, slot_end_g in *.
                           rewrite Hq in *. rewrite Hq' in *.
                           set (u := mt_cnt mt * q) in *. set (u' := j * q') in *.
                           replace (mt_cnt mt * (16 * q)) with (16 * u) in * by llia.
                           replace (j * (16 * q')) with (16 * u') in * by llia.
                           assert (E1 : mt_mem mt = 16 * (mt_mem mt / 16)) by llia.
                           assert (E2 : mt_mem mtx = 16 * (mt_mem mtx / 16)) by llia.
                           rewrite E1, E2 in *. llia.
                   +++ right; right; right; right. split; [exact Hmeta|]. right. rewrite Ef. cbn [f_a].
                       unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
                       pose proof (slots_disjoint (mt_mem mtx) (mt_stride mtx) (j + 1) (Z.of_nat j') HS' ltac:(llia) ltac:(llia) ltac:(llia)). llia.
                ** right; right; right; right. split; [exact Hmeta|]. right.
                   unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
                   pose proof (slots_disjoint (mt_mem mtx) (mt_stride mtx) j (Z.of_nat j') HS' Hj0 ltac:(llia) Hgt). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma other_fact_clear : forall f,
    (has_ctx A f \/ has_area A f \/
     (exists x mtx fl, x <> ma /\ a_meta A x = Some mtx /\ f = FCT (x + moff fl) (mlen fl) (mt_f mtx fl)) \/
     (exists x mtx aibx slx, x <> ma /\ a_meta A x = Some mtx /\ mt_role mtx = RGroup aibx slx /\
        (In f (grp_hdr_fields x mtx aibx) \/ exists j st, nth_error slx j = Some st /\ In f (slot_fields mtx (Z.of_nat j) st)))) ->
    0 < f_n f /\
    (f_a f + f_n f <= ma \/ ma + 40 <= f_a f) /\
    ((f_a f + f_n f <= gext_lo mt \/ gext_hi mt <= f_a f) \/
     (exists j ch, nth_error slots j = Some (SNested ch) /\
        slot_start mt (Z.of_nat j) <= f_a f /\ f_a f + f_n f <= slot_end mt (Z.of_nat j) + 1)).
  Proof using HW Hma Hr MLok. pu_keep (HW, Hma, Hr, MLok).
    intros f Hor.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as
      (Hw32 & Hfr & Hsc & Hlen & Hav & Hfd & Hdis & Haib & Havact & Haibl & Hidle & Hal16 & Hmem & Hfit & Hce & Hpg).
    pose proof (stride_ge16 mt ltac:(llia) Hsc) as HS16.
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & Hself).
    destruct (wf_grp A HW mr mtr aibr slr Hmr Hrr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpgr).
    destruct (Hpgr Hml) as [_ Hheap].
    assert (Hf : has A f).
    { destruct Hor as [H | [H | [(x & mtx & fl & Hne & Hx & ->) | (x & mtx & aibx & slx & Hne & Hx & Hrx & Hin)]]].
      - left; exact H. - right; left; exact H.
      - right; right; left. exists x, mtx, fl. auto.
      - right; right; right. exists x, mtx, aibx, slx. auto. }
    pose proof (has_addr A HW f Hf) as (Hfn & Hf1 & Hf2 & _). split; [llia|].
    destruct Hor as [Hc | [Har | [(x & mtx & fl & Hne & Hx & ->) | (x & mtx & aibx & slx & Hne & Hx & Hrx & Hin)]]].
    - split.
      + destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_introl Hc)); llia.
      + left. pose proof (has_ctx_where A f Hc) as (C1 & C2 & C3). destruct Hc as (k & Hk & ->). cbn in *.
        destruct (heap_avoids_ctx _ _ Hheap k Hk); unfold gext_lo, gext_hi in *; llia.
    - split.
      + destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_introl Har))); llia.
      + left. destruct Har as (pg & Hpga & ->). cbn in *.
        destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - cbn. pose proof (mfield_range fl). split.
      + destruct (other_meta_avoid_meta A HW ma mt Hma x mtx fl Hx Hne); llia.
      + left. destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpga & Hk & ->).
        pose proof (meta_addr_range pg k Hk).
        destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
    - assert (Hgf : has_grp A f) by (exists x, mtx, aibx, slx; auto).
      split.
      { destruct (nonmeta_avoid_meta A HW ma mt Hma f (or_intror (or_intror Hgf))); llia. }
      assert (Hfin : gext_lo mtx <= f_a f /\ f_a f + f_n f <= gext_hi mtx + 1).
      { destruct (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw32' & _ & Hsc' & Hlen' & _).
        pose proof (stride_ge16 mtx ltac:(llia) Hsc') as HS'.
        destruct Hin as [Hin | (j & st & Hj & Hin)].
        - unfold gext_lo, gext_hi. assert (0 <= mt_cnt mtx * mt_stride mtx) by lnia.
          destruct Hin as [<- | [<- | []]]; cbn; llia.
        - pose proof (slot_fields_where A HW x mtx aibx slx j st f Hx Hrx Hj Hin). llia. }
      destruct (wf_laminar A HW ma mt aib slots x mtx aibx slx Hma Hr Hx Hrx ltac:(congruence))
        as [Hd | [Hd | [ (j & ch & Hj0 & Hj & Hjlo & Hjhi) | (j & ch & Hj0 & Hj & Hjlo & Hjhi) ]]].
      + left. llia.
      + left. llia.
      + right. exists (Z.to_nat j), ch. rewrite Z2Nat.id by llia. split; [exact Hj | llia].
      + left.
        destruct (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw32' & _ & Hsc' & Hlen' & _).
        pose proof (stride_ge16 mtx ltac:(llia) Hsc') as HS'.
        destruct Hin as [Hin | (j' & st' & Hj' & Hin)].
        * left. unfold slot_start, slot_start_g in Hjlo. assert (0 <= j * mt_stride mtx) by lnia.
          destruct Hin as [<- | [<- | []]]; cbn; llia.
        * pose proof (slot_fact_bounds A HW x mtx aibx slx j' st' f Hx Hrx Hj' Hin) as (B1 & B2).
          unfold slot_start, slot_end, slot_start_g, slot_end_g in *.
          destruct (Z.lt_total (Z.of_nat j') j) as [Hlt | [Heq | Hgt]].
          -- left. pose proof (slots_disjoint (mt_mem mtx) (mt_stride mtx) (Z.of_nat j') j HS' ltac:(llia) Hj0 Hlt). llia.
          -- rewrite <- Heq, Nat2Z.id in Hj. rewrite Hj in Hj'. injection Hj' as <-.
             unfold slot_fields, slot_fields_g in Hin. apply in_app_iff in Hin.
             destruct Hin as [[<- | [<- | []]] | [<- | [<- | []]]]; cbn [f_a f_n]; unfold slot_start_g, slot_end_g; llia.
          -- right. pose proof (slots_disjoint (mt_mem mtx) (mt_stride mtx) j (Z.of_nat j') HS' Hj0 ltac:(llia) Hgt). llia.
  Qed.

  (* [comment removed for export] *)
  Lemma meta_clear_of_gext : ma + 40 <= gext_lo mt \/ gext_hi mt + 4 <= ma.
  Proof.
    destruct (wf_grp_root A HW ma mt aib slots Hma Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hrlo & Hrhi & Hself).
    destruct (proj1 (wf_meta_dom A HW ma) ltac:(rewrite Hma; discriminate)) as (pg & k & Hpga & Hk & Ema).
    pose proof (meta_addr_range pg k Hk).
    destruct (wf_disj_area_grp A HW pg mr mtr aibr slr Hpga Hmr Hrr Hml); unfold gext_lo, gext_hi in *; llia.
  Qed.
End Locate.

End WithLayout.
