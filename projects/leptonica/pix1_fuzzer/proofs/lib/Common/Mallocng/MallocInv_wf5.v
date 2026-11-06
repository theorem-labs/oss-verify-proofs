(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_wf MallocInv_wf2
  MallocInv_vm MallocInv_ntfree.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Section DissolveRoot.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hml : 0 < mt_maplen mt.
  (* [comment removed for export] *)
  Hypothesis Hidle : forall j st, nth_error slots j = Some st -> st = SIdle \/ st = STaken.
  (* [comment removed for export] *)
  Hypothesis Hnotact : forall sc, ~ In ma (a_active A sc).

  (* [comment removed for export] *)
  Definition mtD : meta_rec := MT (mt_f mt) RDead.

  Definition disA : astate :=
    AST (a_ctx A) (a_areas A) (aupd (a_meta A) ma mtD) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A)
        (a_live A) (a_mblocks A) ((mt_mem mt, grp_map_len mt) :: a_xmaps A).

  Lemma dis_meta : forall x, a_meta disA x = if Z.eq_dec x ma then Some mtD else a_meta A x.
  Proof. intros x. reflexivity. Qed.

  Lemma dis_meta_same : a_meta disA ma = Some mtD.
  Proof. rewrite dis_meta. destruct (Z.eq_dec ma ma); [reflexivity | contradiction]. Qed.

  Lemma dis_meta_inv : forall x mtx, a_meta disA x = Some mtx ->
    (x = ma /\ mtx = mtD) \/ (x <> ma /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. rewrite dis_meta in Hx. destruct (Z.eq_dec x ma) as [-> | Hne]; [left; injection Hx as <-; auto | right; auto].
  Qed.

  Lemma dis_group_inv : forall x mtx aibx slx, a_meta disA x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    a_meta A x = Some mtx /\ x <> ma.
  Proof.
    intros x mtx aibx slx Hx Hrx. destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [| auto].
    unfold mtD in Hrx. rewrite mt_role_MT in Hrx. discriminate Hrx.
  Qed.

  Lemma dis_old : forall x mtx, a_meta A x = Some mtx -> x <> ma -> a_meta disA x = Some mtx.
  Proof. intros x mtx Hx Hne. rewrite dis_meta. destruct (Z.eq_dec x ma); [contradiction | exact Hx]. Qed.

  (* [comment removed for export] *)
  Lemma dis_old_grp : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> ma ->
    a_meta disA x = Some mtx.
  Proof. intros x mtx aibx slx Hx _ Hne. exact (dis_old x mtx Hx Hne). Qed.

  Lemma dis_not_in_fl : ~ In ma (a_freelist A).
  Proof.
    intros Hin. destruct (proj1 (wf_fl_mem A HW ma) Hin) as (mt0 & H0 & Hr0). rewrite Hma in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.

  Lemma dis_dll : forall l, ~ In ma l -> dll A l -> dll disA l.
  Proof.
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R). exists mtx. split; [| exact R].
    apply dis_old; [exact Hx|]. intros ->. apply Hn. eapply nth_error_In. exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma dis_no_nested : forall j ch, nth_error slots j <> Some (SNested ch).
  Proof. intros j ch E. destruct (Hidle _ _ E); discriminate. Qed.

  (* [comment removed for export] *)
  Lemma nested_child_not_ma : forall x mtx aibx slx i ch, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    nth_error slx (Z.to_nat i) = Some (SNested ch) -> 0 <= i -> ch <> ma.
  Proof.
    intros x mtx aibx slx i ch Hx Hrx Hi Hi0 ->.
    destruct (wf_nested A HW x mtx aibx slx i ma Hx Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & Hmlc & _).
    rewrite Hma in Hmc. injection Hmc as <-. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma nested_parent_not_ma : forall x mtx aibx slx i ch, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    nth_error slx (Z.to_nat i) = Some (SNested ch) -> x <> ma.
  Proof.
    intros x mtx aibx slx i ch Hx Hrx Hi ->. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
    exact (dis_no_nested _ _ Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma dis_clear : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> ma ->
    gext_hi mtx <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= gext_lo mtx.
  Proof.
    intros x mtx aibx slx Hx Hrx Hne.
    exact (root_no_nested_clear A HW ma mt aib slots x mtx aibx slx Hma Hr Hml dis_no_nested Hx Hrx Hne).
  Qed.

  Theorem WF_dissolve_root : WF disA.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps disA]; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. unfold aupd.
      destruct (Z.eq_dec x ma) as [-> | Hne]; [rewrite Hma; split; intros _; discriminate | tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply dis_old; [exact Hmk|]. intros E. rewrite E, Hma in Hmk. injection Hmk as <-. rewrite Hr in Hrk. discriminate Hrk.
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [unfold mtD in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [unfold mtD in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply dis_old; [exact Hx|].
        intros ->. rewrite Hma in Hx. injection Hx as ->. rewrite Hr in Hrx. discriminate Hrx.
      + intros (mtx & Hx & Hrx). destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [unfold mtD in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) apply dis_dll; [apply dis_not_in_fl | exact wf_fl_dll0].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx i off n Hx Hrx. destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx i ch Hx Hrx Hi Hi0. destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H _].
      destruct (wf_nested0 x mtx aibx slx i ch H Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & R).
      exists mc, aibc, slc. split; [| split; [exact Hrc | exact R]].
      apply (dis_old_grp _ _ _ _ Hmc Hrc). exact (nested_child_not_ma x mtx aibx slx i ch H Hrx Hi Hi0).
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hmlc. destruct (dis_group_inv ch mc aibc slc Hch Hrc) as [H _].
      destruct (wf_nested_parent0 ch mc aibc slc H Hrc Hmlc) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
      exists x, mtx, aibx, slx, j. split; [| split; [exact Hrx | split; [exact Hj0 | exact Hj]]].
      apply (dis_old_grp _ _ _ _ Hx Hrx). exact (nested_parent_not_ma x mtx aibx slx j ch Hx Hrx Hj).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H Hne].
      destruct (wf_grp_root0 x mtx aibx slx H Hrx) as (mr & mtr & aibr & slr & Hmr & Hrr & Hmlr & Hlo & Hhi & Hself).
      exists mr, mtr, aibr, slr. split; [| split; [exact Hrr | split; [exact Hmlr | split; [exact Hlo | split; [exact Hhi | exact Hself]]]]].
      apply (dis_old_grp _ _ _ _ Hmr Hrr). intros ->.
      rewrite Hma in Hmr. injection Hmr as <-.
      destruct (dis_clear x mtx aibx slx H Hrx Hne) as [D | D].
      + (* [comment removed for export] *)
        pose proof (wf_grp0 x mtx aibx slx H Hrx) as (Hw & _ & Hscx & Hlenx & _).
        pose proof (stride_ge16 mtx ltac:(lia) Hscx). unfold gext_lo, gext_hi, mt_cnt in *.
        pose proof (w_last_range (mt_w32 mtx)). unfold mt_last in *. nia.
      + unfold gext_lo, gext_hi in *. pose proof (wf_grp0 x mtx aibx slx H Hrx) as (Hw & _ & Hscx & _).
        pose proof (stride_ge16 mtx ltac:(lia) Hscx). unfold mt_cnt in *. pose proof (w_last_range (mt_w32 mtx)). unfold mt_last in *. nia.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' Hne.
      destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dis_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros sc Hsc. apply dis_dll; [apply Hnotact | exact (wf_act_dll0 sc Hsc)].
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aibx & slx & Hx & Hrx & R).
      exists mtx, aibx, slx. split; [| auto]. apply (dis_old_grp _ _ _ _ Hx Hrx). intros ->. exact (Hnotact sc Hin).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hne Hx.
      destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (_ & Hx')]; [exfalso; exact (Hnotact sc Hin)|]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hmlx Hx' Hrx'.
      destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dis_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx'.
      destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dis_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map0 q n). unfold is_live. cbn [a_meta disA]. split.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & Hi0 & Hi & E). exists x, mtx, aibx, slx, i, off.
        split; [| auto]. apply (dis_old_grp _ _ _ _ Hx Hrx). intros ->.
        rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
        destruct (Hidle _ _ Hi); discriminate.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & R). destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _].
        exists x, mtx, aibx, slx, i, off. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx aibx slx x' mtx' aibx' slx' Hin Hin' Hx Hrx Hx' Hrx'.
      destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dis_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (dis_group_inv _ _ _ _ Hpa Hpr) as [Hpa0 _]. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [Hx0 _].
      destruct (wf_cover0 pa pm paib psl j ch x mtx aibx slx Hpa0 Hpr Hj0 Hj Hx0 Hrx Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & R).
      exists mtc, aibc, slc. split; [| split; [exact Hrc | exact R]].
      apply (dis_old_grp _ _ _ _ Hch Hrc). exact (nested_child_not_ma pa pm paib psl j ch Hpa0 Hpr Hj Hj0).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dis_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma has_disA : forall f, has disA f -> has A f.
  Proof.
    intros f [Hc | [Har | [Hm | Hg]]].
    - left. exact Hc.
    - right; left. exact Har.
    - right; right; left. destruct Hm as (x & mtx & fl & Hx & ->).
      destruct (dis_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)].
      + exists ma, mt, fl. split; [exact Hma|]. unfold mtD. rewrite mt_f_MT. reflexivity.
      + exists x, mtx, fl. auto.
    - right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H _]. exists x, mtx, aibx, slx. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma dom_disA : forall x, dom disA x -> dom A x.
  Proof.
    intros x [Ha | [(y & mty & aiby & sly & Hy & Hry & Hmly & Hx) | Hp]]; [left; exact Ha | | right; right; exact Hp].
    destruct (dis_group_inv y mty aiby sly Hy Hry) as [H _]. right; left. exists y, mty, aiby, sly. auto.
  Qed.

  Lemma dom_disA_back : forall x, dom A x -> dom disA x \/ (mt_mem mt <= x < mt_mem mt + grp_map_len mt).
  Proof.
    intros x [Ha | [(y & mty & aiby & sly & Hy & Hry & Hmly & Hx) | Hp]]; [left; left; exact Ha | | left; right; right; exact Hp].
    destruct (Z.eq_dec y ma) as [-> | Hne].
    - right. rewrite Hma in Hy. injection Hy as <-. exact Hx.
    - left. right; left. exists y, mty, aiby, sly. split; [exact (dis_old _ _ Hy Hne) | auto].
  Qed.

  Lemma Rep_disA : forall m, Rep A m -> Rep disA m.
  Proof.
    intros m [R1 R2]. constructor.
    - intros x b (f & Hf & Hb). apply R1. exists f. split; [apply has_disA; exact Hf | exact Hb].
    - intros x Hx. apply R2. apply dom_disA. exact Hx.
  Qed.

  Lemma VMok_disA : forall h, VMok A h -> VMok disA h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    constructor; cbn [a_ctx a_areas a_meta a_pages a_mblocks a_xmaps disA]; try assumption.
    - intros x mtx aibx slx Hx Hrx Hmlx. destruct (dis_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - intros b sz Hin. destruct (Vall b sz Hin) as [(y & mty & aiby & sly & Hy & Hry & Hmly & Eb & Esz) | [B | (c & l & Hcl & H1 & H2)]].
      + destruct (Z.eq_dec y ma) as [-> | Hne].
        * right; right. rewrite Hma in Hy. injection Hy as <-. exists (mt_mem mt), (grp_map_len mt).
          split; [apply in_or_app; right; left; reflexivity | lia].
        * left. exists y, mty, aiby, sly. split; [exact (dis_old _ _ Hy Hne) | auto].
      + right; left. exact B.
      + right; right. exists c, l. split; [| auto]. apply in_app_or in Hcl. apply in_or_app.
        destruct Hcl as [Hc | Hx]; [left; exact Hc | right; right; exact Hx].
  Qed.
End DissolveRoot.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DissolveNested.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hml : mt_maplen mt = 0.
  Hypothesis Hidle : forall j st, nth_error slots j = Some st -> st = SIdle \/ st = STaken.
  Hypothesis Hnotact : forall sc, ~ In ma (a_active A sc).
  (* [comment removed for export] *)
  Variables (pa : Z) (pm : meta_rec) (paib : Z) (psl : list slot_st) (j : Z).
  Hypothesis Hpa : a_meta A pa = Some pm.
  Hypothesis Hpr : mt_role pm = RGroup paib psl.
  Hypothesis Hj0 : 0 <= j.
  Hypothesis Hj : nth_error psl (Z.to_nat j) = Some (SNested ma).

  Definition mtDn : meta_rec := MT (mt_f mt) RDead.
  Definition psl' : list slot_st := list_set psl (Z.to_nat j) STaken.
  Definition pm' : meta_rec := MT (mt_f pm) (RGroup paib psl').

  Definition dnA : astate :=
    AST (a_ctx A) (a_areas A) (aupd (aupd (a_meta A) ma mtDn) pa pm') (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A)
        (a_live A) (a_mblocks A) (a_xmaps A).

  Lemma pa_ne_ma : pa <> ma.
  Proof.
    intros E. subst pa. rewrite Hma in Hpa. injection Hpa as E. subst pm. rewrite Hr in Hpr. injection Hpr as E1 E2. subst paib psl.
    destruct (Hidle _ _ Hj); discriminate.
  Qed.

  Lemma dn_meta : forall x, a_meta dnA x = if Z.eq_dec x pa then Some pm' else if Z.eq_dec x ma then Some mtDn else a_meta A x.
  Proof. intros x. reflexivity. Qed.

  Lemma dn_meta_pa : a_meta dnA pa = Some pm'.
  Proof. rewrite dn_meta. destruct (Z.eq_dec pa pa); [reflexivity | contradiction]. Qed.

  Lemma dn_meta_ma : a_meta dnA ma = Some mtDn.
  Proof.
    rewrite dn_meta. destruct (Z.eq_dec ma pa) as [E | _]; [exfalso; exact (pa_ne_ma (eq_sym E))|].
    destruct (Z.eq_dec ma ma); [reflexivity | contradiction].
  Qed.

  Lemma dn_meta_inv : forall x mtx, a_meta dnA x = Some mtx ->
    (x = pa /\ mtx = pm') \/ (x = ma /\ mtx = mtDn) \/ (x <> pa /\ x <> ma /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. rewrite dn_meta in Hx. destruct (Z.eq_dec x pa) as [-> | Hne]; [left; injection Hx as <-; auto|].
    destruct (Z.eq_dec x ma) as [-> | Hne2]; [right; left; injection Hx as <-; auto | right; right; auto].
  Qed.

  Lemma dn_old : forall x mtx, a_meta A x = Some mtx -> x <> pa -> x <> ma -> a_meta dnA x = Some mtx.
  Proof.
    intros x mtx Hx H1 H2. rewrite dn_meta. destruct (Z.eq_dec x pa); [contradiction|]. destruct (Z.eq_dec x ma); [contradiction | exact Hx].
  Qed.

  Lemma pm'_f : forall fl, mt_f pm' fl = mt_f pm fl. Proof. intros fl. unfold pm'. apply mt_f_MT. Qed.
  Lemma pm'_w32 : mt_w32 pm' = mt_w32 pm. Proof. unfold mt_w32. apply pm'_f. Qed.
  Lemma pm'_mem : mt_mem pm' = mt_mem pm. Proof. unfold mt_mem. apply pm'_f. Qed.
  Lemma pm'_prev : mt_prev pm' = mt_prev pm. Proof. unfold mt_prev. apply pm'_f. Qed.
  Lemma pm'_next : mt_next pm' = mt_next pm. Proof. unfold mt_next. apply pm'_f. Qed.
  Lemma pm'_avail : mt_avail pm' = mt_avail pm. Proof. unfold mt_avail. apply pm'_f. Qed.
  Lemma pm'_freed : mt_freed pm' = mt_freed pm. Proof. unfold mt_freed. apply pm'_f. Qed.
  Lemma pm'_last : mt_last pm' = mt_last pm. Proof. unfold mt_last. rewrite pm'_w32. reflexivity. Qed.
  Lemma pm'_maplen : mt_maplen pm' = mt_maplen pm. Proof. unfold mt_maplen. rewrite pm'_w32. reflexivity. Qed.
  Lemma pm'_sc : mt_sc pm' = mt_sc pm. Proof. unfold mt_sc. rewrite pm'_w32. reflexivity. Qed.
  Lemma pm'_stride : mt_stride pm' = mt_stride pm. Proof. unfold mt_stride. rewrite pm'_maplen, pm'_last, pm'_sc. reflexivity. Qed.
  Lemma pm'_cnt : mt_cnt pm' = mt_cnt pm. Proof. unfold mt_cnt. rewrite pm'_last. reflexivity. Qed.
  Lemma pm'_role : mt_role pm' = RGroup paib psl'. Proof. reflexivity. Qed.
  Lemma pm'_gext_lo : gext_lo pm' = gext_lo pm. Proof. unfold gext_lo. apply pm'_mem. Qed.
  Lemma pm'_gext_hi : gext_hi pm' = gext_hi pm. Proof. unfold gext_hi. rewrite pm'_mem, pm'_cnt, pm'_stride. reflexivity. Qed.
  Lemma pm'_slot_start : forall i, slot_start pm' i = slot_start pm i. Proof. intros i. unfold slot_start. rewrite pm'_mem, pm'_stride. reflexivity. Qed.
  Lemma pm'_slot_end : forall i, slot_end pm' i = slot_end pm i. Proof. intros i. unfold slot_end. rewrite pm'_mem, pm'_stride. reflexivity. Qed.
  Lemma pm'_grp_map_len : grp_map_len pm' = grp_map_len pm. Proof. unfold grp_map_len. rewrite pm'_maplen. reflexivity. Qed.
  Lemma pm'_slot_fields : forall i st, slot_fields pm' i st = slot_fields pm i st.
  Proof. intros i st. unfold slot_fields. rewrite pm'_mem, pm'_stride. reflexivity. Qed.

  Lemma Hjlt : (Z.to_nat j < length psl)%nat.
  Proof. apply (proj1 (nth_error_Some psl (Z.to_nat j))). rewrite Hj. discriminate. Qed.

  Lemma psl'_length : length psl' = length psl.
  Proof. unfold psl'. apply list_set_length. Qed.

  Lemma psl'_inv : forall i st, nth_error psl' (Z.to_nat i) = Some st -> 0 <= i ->
    (i = j /\ st = STaken) \/ (i <> j /\ nth_error psl (Z.to_nat i) = Some st).
  Proof.
    intros i st Hi Hi0. unfold psl' in Hi. destruct (list_set_nth_inv _ _ _ _ _ Hi) as [(E & -> & _) | (Hne & H)].
    - left. split; [lia | reflexivity].
    - right. split; [intros ->; exact (Hne eq_refl) | exact H].
  Qed.

  Lemma psl'_inv_nat : forall i st, nth_error psl' i = Some st ->
    (i = Z.to_nat j /\ st = STaken) \/ (i <> Z.to_nat j /\ nth_error psl i = Some st).
  Proof.
    intros i st Hi. unfold psl' in Hi. destruct (list_set_nth_inv _ _ _ _ _ Hi) as [(E & -> & _) | (Hne & H)]; [left; auto | right; auto].
  Qed.

  Lemma psl'_j : nth_error psl' (Z.to_nat j) = Some STaken.
  Proof. unfold psl'. apply list_set_nth_same. exact Hjlt. Qed.

  Lemma psl'_other : forall i, i <> Z.to_nat j -> nth_error psl' i = nth_error psl i.
  Proof. intros i Hne. unfold psl'. apply list_set_nth_other. intros E. apply Hne. symmetry. exact E. Qed.

  (* [comment removed for export] *)
  Lemma nested_parent_unique : forall x mtx aibx slx i,
    a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> 0 <= i -> nth_error slx (Z.to_nat i) = Some (SNested ma) ->
    x = pa /\ i = j.
  Proof.
    intros x mtx aibx slx i Hx Hrx Hi0 Hi.
    destruct (wf_nested A HW x mtx aibx slx i ma Hx Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & _ & Hmem & Hfit).
    rewrite Hma in Hmc. injection Hmc as <-.
    destruct (wf_nested A HW pa pm paib psl j ma Hpa Hpr Hj Hj0) as (mc' & aibc' & slc' & Hmc' & Hrc' & _ & Hmem' & Hfit').
    rewrite Hma in Hmc'. injection Hmc' as <-.
    pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw & _ & Hsc & Hlen & _).
    pose proof (wf_grp A HW pa pm paib psl Hpa Hpr) as (Hw' & _ & Hsc' & Hlen' & _).
    pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hwm & _ & Hscm & Hlenm & _).
    pose proof (stride_ge16 mtx ltac:(lia) Hsc) as HS. pose proof (stride_ge16 pm ltac:(lia) Hsc') as HS'.
    pose proof (stride_ge16 mt ltac:(lia) Hscm) as HSm.
    assert (Hilt : (Z.to_nat i < length slx)%nat) by (apply (proj1 (nth_error_Some slx (Z.to_nat i))); rewrite Hi; discriminate).
    pose proof (w_last_range (mt_w32 mt)) as Lm.
    assert (HiS : 0 <= i * mt_stride mtx /\ i * mt_stride mtx + mt_stride mtx <= mt_cnt mtx * mt_stride mtx) by (clear -HS Hi0 Hilt Hlen; nia).
    assert (HjS : 0 <= j * mt_stride pm /\ j * mt_stride pm + mt_stride pm <= mt_cnt pm * mt_stride pm) by (pose proof Hjlt; clear -HS' Hj0 H Hlen'; nia).
    assert (HcS : 16 <= mt_cnt mt * mt_stride mt) by (unfold mt_cnt, mt_last in *; clear -HSm Lm; nia).
    destruct (Z.eq_dec x pa) as [-> | Hne].
    - rewrite Hpa in Hx. injection Hx as <-. rewrite Hpr in Hrx. injection Hrx as <- <-. split; [reflexivity|].
      unfold slot_start, slot_start_g in Hmem, Hmem'. rewrite Hmem' in Hmem.
      destruct (Z.lt_trichotomy i j) as [L | [E | L]]; [exfalso | exact E | exfalso].
      + assert (i * mt_stride pm + mt_stride pm <= j * mt_stride pm) by (clear -L HS' Hi0; nia). lia.
      + assert (j * mt_stride pm + mt_stride pm <= i * mt_stride pm) by (clear -L HS' Hj0; nia). lia.
    - exfalso.
      destruct (wf_laminar A HW x mtx aibx slx pa pm paib psl Hx Hrx Hpa Hpr Hne) as [D | [D | [D | D]]];
        unfold gext_hi, gext_lo, slot_start, slot_end, slot_start_g, slot_end_g in *.
      + lia.
      + lia.
      + destruct D as (k & ch & Hk0 & Hk & Hlo & Hhi).
        assert (Hklt : (Z.to_nat k < length slx)%nat) by (apply (proj1 (nth_error_Some slx (Z.to_nat k))); rewrite Hk; discriminate).
        assert (HkS : 0 <= k * mt_stride mtx /\ k * mt_stride mtx + mt_stride mtx <= mt_cnt mtx * mt_stride mtx) by (clear -HS Hk0 Hklt Hlen; nia).
        destruct (Z.lt_trichotomy k i) as [L | [-> | L]].
        * assert (k * mt_stride mtx + mt_stride mtx <= i * mt_stride mtx) by (clear -L HS Hk0; nia). lia.
        * lia.
        * assert (i * mt_stride mtx + mt_stride mtx <= k * mt_stride mtx) by (clear -L HS Hi0; nia). lia.
      + destruct D as (k & ch & Hk0 & Hk & Hlo & Hhi).
        assert (Hklt : (Z.to_nat k < length psl)%nat) by (apply (proj1 (nth_error_Some psl (Z.to_nat k))); rewrite Hk; discriminate).
        assert (HkS : 0 <= k * mt_stride pm /\ k * mt_stride pm + mt_stride pm <= mt_cnt pm * mt_stride pm) by (clear -HS' Hk0 Hklt Hlen'; nia).
        destruct (Z.lt_trichotomy k j) as [L | [-> | L]].
        * assert (k * mt_stride pm + mt_stride pm <= j * mt_stride pm) by (clear -L HS' Hk0; nia). lia.
        * lia.
        * assert (j * mt_stride pm + mt_stride pm <= k * mt_stride pm) by (clear -L HS' Hj0; nia). lia.
  Qed.

  Lemma dn_group_inv : forall x mtx aibx slx, a_meta dnA x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    (x = pa /\ mtx = pm' /\ aibx = paib /\ slx = psl') \/ (x <> pa /\ x <> ma /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx aibx slx Hx Hrx. destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | H]]; [left | | right; exact H].
    - rewrite pm'_role in Hrx. injection Hrx as <- <-. auto.
    - unfold mtDn in Hrx. rewrite mt_role_MT in Hrx. discriminate Hrx.
  Qed.

  (* [comment removed for export] *)
  Lemma dn_group_back : forall x mtx aibx slx, a_meta dnA x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    exists mt0 sl0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx sl0 /\ x <> ma /\
      (forall fl, mt_f mtx fl = mt_f mt0 fl) /\ mt_w32 mtx = mt_w32 mt0 /\ mt_mem mtx = mt_mem mt0 /\
      mt_stride mtx = mt_stride mt0 /\ mt_cnt mtx = mt_cnt mt0 /\ mt_maplen mtx = mt_maplen mt0 /\ mt_sc mtx = mt_sc mt0 /\
      mt_last mtx = mt_last mt0 /\ mt_avail mtx = mt_avail mt0 /\ mt_freed mtx = mt_freed mt0 /\
      mt_prev mtx = mt_prev mt0 /\ mt_next mtx = mt_next mt0 /\ gext_lo mtx = gext_lo mt0 /\ gext_hi mtx = gext_hi mt0 /\
      length slx = length sl0 /\
      (forall i st, nth_error slx i = Some st -> nth_error sl0 i = Some st \/ (x = pa /\ i = Z.to_nat j /\ st = STaken /\ nth_error sl0 i = Some (SNested ma))) /\
      (forall i st, nth_error sl0 i = Some st -> st <> SNested ma -> nth_error slx i = Some st).
  Proof.
    intros x mtx aibx slx Hx Hrx. destruct (dn_group_inv x mtx aibx slx Hx Hrx) as [(-> & -> & -> & ->) | (H1 & H2 & H)].
    - exists pm, psl. split; [exact Hpa|]. split; [exact Hpr|]. split; [exact pa_ne_ma|].
      split; [exact pm'_f|]. rewrite pm'_w32, pm'_mem, pm'_stride, pm'_cnt, pm'_maplen, pm'_sc, pm'_last, pm'_avail, pm'_freed,
        pm'_prev, pm'_next, pm'_gext_lo, pm'_gext_hi, psl'_length.
      repeat (split; [reflexivity|]). split.
      + intros i st Hi. destruct (psl'_inv_nat i st Hi) as [(-> & ->) | (Hne & Hi')]; [right; auto | left; exact Hi'].
      + intros i st Hi Hne. rewrite psl'_other; [exact Hi|]. intros ->. rewrite Hj in Hi. injection Hi as <-. exact (Hne eq_refl).
    - exists mtx, slx. split; [exact H|]. split; [exact Hrx|]. split; [exact H2|]. split; [intros fl; reflexivity|].
      repeat (split; [reflexivity|]). split.
      + intros i st Hi. left. exact Hi.
      + intros i st Hi _. exact Hi.
  Qed.

  Lemma dn_not_in_fl : ~ In ma (a_freelist A).
  Proof.
    intros Hin. destruct (proj1 (wf_fl_mem A HW ma) Hin) as (mt0 & H0 & Hr0). rewrite Hma in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.

  Lemma pa_not_in_fl : ~ In pa (a_freelist A).
  Proof.
    intros Hin. destruct (proj1 (wf_fl_mem A HW pa) Hin) as (mt0 & H0 & Hr0). rewrite Hpa in H0. injection H0 as <-.
    rewrite Hpr in Hr0. discriminate Hr0.
  Qed.

  Lemma dn_dll : forall l, ~ In ma l -> dll A l -> dll dnA l.
  Proof.
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R1 & R2).
    destruct (Z.eq_dec x pa) as [-> | Hne].
    - exists pm'. split; [exact dn_meta_pa|]. rewrite pm'_next, pm'_prev. rewrite Hpa in Hx. injection Hx as <-. auto.
    - exists mtx. split; [| auto]. apply dn_old; [exact Hx | exact Hne |]. intros ->. apply Hn. eapply nth_error_In. exact Hk.
  Qed.

  Lemma dn_no_nested : forall i ch, nth_error slots i <> Some (SNested ch).
  Proof. intros i ch E. destruct (Hidle _ _ E); discriminate. Qed.

  (* [comment removed for export] *)
  Lemma dn_fwd : forall y my aiby sly, a_meta A y = Some my -> mt_role my = RGroup aiby sly -> y <> ma ->
    exists my' sly', a_meta dnA y = Some my' /\ mt_role my' = RGroup aiby sly' /\
      (forall fl, mt_f my' fl = mt_f my fl) /\ mt_w32 my' = mt_w32 my /\ mt_mem my' = mt_mem my /\
      mt_stride my' = mt_stride my /\ mt_cnt my' = mt_cnt my /\ mt_maplen my' = mt_maplen my /\ mt_sc my' = mt_sc my /\
      mt_last my' = mt_last my /\ gext_lo my' = gext_lo my /\ gext_hi my' = gext_hi my /\
      (forall i st, nth_error sly i = Some st -> st <> SNested ma -> nth_error sly' i = Some st) /\
      (forall i st, nth_error sly' i = Some st -> nth_error sly i = Some st \/ (y = pa /\ i = Z.to_nat j /\ st = STaken)).
  Proof.
    intros y my aiby sly Hy Hry Hne. destruct (Z.eq_dec y pa) as [-> | Hnp].
    - rewrite Hpa in Hy. injection Hy as <-. rewrite Hpr in Hry. injection Hry as <- <-.
      exists pm', psl'. split; [exact dn_meta_pa|]. split; [reflexivity|]. split; [exact pm'_f|].
      rewrite pm'_w32, pm'_mem, pm'_stride, pm'_cnt, pm'_maplen, pm'_sc, pm'_last, pm'_gext_lo, pm'_gext_hi.
      repeat (split; [reflexivity|]). split.
      + intros i st Hi Hst. rewrite psl'_other; [exact Hi|]. intros ->. rewrite Hj in Hi. injection Hi as <-. exact (Hst eq_refl).
      + intros i st Hi. destruct (psl'_inv_nat i st Hi) as [(-> & ->) | (_ & H)]; [right; auto | left; exact H].
    - exists my, sly. split; [exact (dn_old _ _ Hy Hnp Hne)|]. split; [exact Hry|].
      repeat (split; [reflexivity|]). split; [intros i st Hi _; exact Hi | intros i st Hi; left; exact Hi].
  Qed.

  (* [comment removed for export] *)
  Lemma slot_j_clear : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> x <> ma ->
    ~ (slot_start pm j <= gext_lo mtx /\ gext_hi mtx <= slot_end pm j).
  Proof.
    intros x mtx aibx slx Hx Hrx Hne [Hlo Hhi].
    destruct (wf_cover A HW pa pm paib psl j ma x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi) as (mtc & aibc & slc & Hmc & Hrc & Clo & Chi).
    rewrite Hma in Hmc. injection Hmc as <-. rewrite Hr in Hrc. injection Hrc as <- <-.
    pose proof (wf_grp A HW x mtx aibx slx Hx Hrx) as (Hw & _ & Hsc & Hlen & _).
    pose proof (wf_grp A HW ma mt aib slots Hma Hr) as (Hwm & _ & Hscm & Hlenm & _).
    pose proof (stride_ge16 mtx ltac:(lia) Hsc) as HS. pose proof (stride_ge16 mt ltac:(lia) Hscm) as HSm.
    pose proof (w_last_range (mt_w32 mtx)) as L. pose proof (w_last_range (mt_w32 mt)) as Lm.
    assert (E1 : 16 <= mt_cnt mtx * mt_stride mtx) by (unfold mt_cnt, mt_last; clear -HS L; nia).
    assert (E2 : 16 <= mt_cnt mt * mt_stride mt) by (unfold mt_cnt, mt_last; clear -HSm Lm; nia).
    destruct (wf_laminar A HW ma mt aib slots x mtx aibx slx Hma Hr Hx Hrx ltac:(intros E; apply Hne; symmetry; exact E)) as [D | [D | [D | D]]];
      unfold gext_lo, gext_hi in *.
    - lia.
    - lia.
    - destruct D as (k & ch & _ & Hk & _). exact (dn_no_nested _ _ Hk).
    - destruct D as (k & ch & Hk0 & Hk & Dlo & Dhi).
      assert (Hklt : (Z.to_nat k < length slx)%nat) by (apply (proj1 (nth_error_Some slx (Z.to_nat k))); rewrite Hk; discriminate).
      assert (HkS : 0 <= k * mt_stride mtx /\ k * mt_stride mtx + mt_stride mtx <= mt_cnt mtx * mt_stride mtx) by (clear -HS Hk0 Hklt Hlen; nia).
      unfold slot_start, slot_end, slot_start_g, slot_end_g in Dlo, Dhi. lia.
  Qed.

  Theorem WF_dissolve_nested : WF dnA.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    pose proof dn_group_back as GB.
    constructor; cbn [a_ctx a_areas a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps dnA]; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. unfold dnA. cbn [a_meta]. unfold aupd.
      destruct (Z.eq_dec x pa) as [-> | Hne]; [rewrite Hpa; split; intros _; discriminate|].
      destruct (Z.eq_dec x ma) as [-> | Hne2]; [rewrite Hma; split; intros _; discriminate | tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply dn_old; [exact Hmk | |]; intros E; rewrite E in Hmk;
        [rewrite Hpa in Hmk; injection Hmk as <-; rewrite Hpr in Hrk | rewrite Hma in Hmk; injection Hmk as <-; rewrite Hr in Hrk]; discriminate Hrk.
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]];
        [rewrite pm'_role in Hrx; discriminate Hrx | unfold mtDn in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]];
        [rewrite pm'_role in Hrx; discriminate Hrx | unfold mtDn in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply dn_old; [exact Hx | |]; intros ->;
          [rewrite Hpa in Hx; injection Hx as ->; rewrite Hpr in Hrx | rewrite Hma in Hx; injection Hx as ->; rewrite Hr in Hrx]; discriminate Hrx.
      + intros (mtx & Hx & Hrx). destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]];
          [rewrite pm'_role in Hrx; discriminate Hrx | unfold mtDn in Hrx; rewrite mt_role_MT in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) apply dn_dll; [apply dn_not_in_fl | exact wf_fl_dll0].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & Ef & Ew & Em & Es & Ec & Eml & Esc & El & Eav & Efr & Ep & En & Elo & Ehi & Elen & Hsl & Hsl').
      pose proof (wf_grp0 x mt0 aibx sl0 H0 Hr0) as G. unfold grp_map_len in *. rewrite Ew, Em, Es, Ec, Eml, Esc, El, Eav, Efr, Elen.
      destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
      repeat (split; [assumption|]). split; [| exact G12].
      intros i st Hi Hi0. destruct (Hsl _ _ Hi) as [Hi' | (-> & E & -> & Hi')].
      + exact (G11 i st Hi' Hi0).
      + rewrite (G11 i (SNested ma) Hi' Hi0). split; [intros; discriminate | intros E'; discriminate E'].
    - (* [comment removed for export] *) intros x mtx aibx slx i off n Hx Hrx Hi Hi0.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & Ef & Ew & Em & Es & Ec & Eml & Esc & El & Eav & Efr & Ep & En & Elo & Ehi & Elen & Hsl & Hsl').
      rewrite Es. destruct (Hsl _ _ Hi) as [Hi' | (_ & _ & E & _)]; [| discriminate E]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx i ch Hx Hrx Hi Hi0.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & Hxma & Ef & Ew & Em & Es & Ec & Eml & Esc & El & Eav & Efr & Ep & En & Elo & Ehi & Elen & Hsl & Hsl').
      destruct (Hsl _ _ Hi) as [Hi' | (_ & _ & E & _)]; [| discriminate E].
      destruct (wf_nested0 x mt0 aibx sl0 i ch H0 Hr0 Hi' Hi0) as (mc & aibc & slc & Hmc & Hrc & Hmlc & Hmemc & Hfitc).
      assert (Hch : ch <> ma).
      { intros ->. destruct (nested_parent_unique x mt0 aibx sl0 i H0 Hr0 Hi0 Hi') as [-> ->].
        destruct (dn_group_inv _ _ _ _ Hx Hrx) as [(_ & _ & _ & ->) | (Hne & _)]; [| exact (Hne eq_refl)].
        rewrite psl'_j in Hi. discriminate Hi. }
      destruct (dn_fwd ch mc aibc slc Hmc Hrc Hch) as (mc' & slc' & Hmc' & Hrc' & _ & _ & Emc & Esc' & Ecc & Emlc & _).
      exists mc', aibc, slc'. split; [exact Hmc'|]. split; [exact Hrc'|].
      rewrite Emlc, Emc, Ecc, Esc', Es. unfold slot_start. rewrite Em, Es. auto.
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hmlc.
      destruct (GB ch mc aibc slc Hch Hrc) as (mt0 & sl0 & H0 & Hr0 & Hchma & Ef & Ew & Em & Es & Ec & Eml & _).
      rewrite Eml in Hmlc.
      destruct (wf_nested_parent0 ch mt0 aibc sl0 H0 Hr0 Hmlc) as (y & my & aiby & sly & k & Hy & Hry & Hk0 & Hk).
      assert (Hyma : y <> ma) by (intros ->; rewrite Hma in Hy; injection Hy as <-; rewrite Hr in Hry; injection Hry as <- <-; exact (dn_no_nested _ _ Hk)).
      destruct (dn_fwd y my aiby sly Hy Hry Hyma) as (my' & sly' & Hy' & Hry' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfw & _).
      exists y, my', aiby, sly', k. split; [exact Hy'|]. split; [exact Hry'|]. split; [exact Hk0|].
      apply Hfw; [exact Hk|]. intros E. injection E as ->. exact (Hchma eq_refl).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & Hxma & Ef & Ew & Em & Es & Ec & Eml & Esc & El & Eav & Efr & Ep & En & Elo & Ehi & _).
      destruct (wf_grp_root0 x mt0 aibx sl0 H0 Hr0) as (mr & mtr & aibr & slr & Hmr & Hrr & Hmlr & Hlo & Hhi & Hself).
      assert (Hrma : mr <> ma) by (intros ->; rewrite Hma in Hmr; injection Hmr as <-; lia).
      destruct (dn_fwd mr mtr aibr slr Hmr Hrr Hrma) as (mr' & slr' & Hmr' & Hrr' & _ & _ & Emr & _ & _ & Emlr & _ & _ & _ & _ & _).
      exists mr, mr', aibr, slr'. split; [exact Hmr'|]. split; [exact Hrr'|]. rewrite Emlr, Emr, Elo, Ehi, Eml.
      unfold grp_map_len. rewrite Emlr. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' Hne.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & Hxma & _ & _ & Em & Es & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _ & Hsl & Hsl'0).
      destruct (GB x' mtx' aibx' slx' Hx' Hrx') as (mt0' & sl0' & H0' & Hr0' & Hxma' & _ & _ & Em' & Es' & _ & _ & _ & _ & _ & _ & _ & _ & Elo' & Ehi' & _ & Hsl2 & Hsl2').
      rewrite Elo, Ehi, Elo', Ehi'. unfold slot_start, slot_end. rewrite Em, Es, Em', Es'.
      destruct (wf_laminar0 x mt0 aibx sl0 x' mt0' aibx' sl0' H0 Hr0 H0' Hr0' Hne) as [D | [D | [D | D]]]; [left; exact D | right; left; exact D | |].
      + right; right; left. destruct D as (k & ch & Hk0 & Hk & Dlo & Dhi). exists k, ch. split; [exact Hk0|]. split; [| split; [exact Dlo | exact Dhi]].
        apply Hsl'0; [exact Hk|]. intros E. injection E as ->.
        destruct (nested_parent_unique x mt0 aibx sl0 k H0 Hr0 Hk0 Hk) as [-> ->].
        rewrite Hpa in H0. injection H0 as <-. exact (slot_j_clear x' mt0' aibx' sl0' H0' Hr0' Hxma' (conj Dlo Dhi)).
      + right; right; right. destruct D as (k & ch & Hk0 & Hk & Dlo & Dhi). exists k, ch. split; [exact Hk0|]. split; [| split; [exact Dlo | exact Dhi]].
        apply Hsl2'; [exact Hk|]. intros E. injection E as ->.
        destruct (nested_parent_unique x' mt0' aibx' sl0' k H0' Hr0' Hk0 Hk) as [-> ->].
        rewrite Hpa in H0'. injection H0' as <-. exact (slot_j_clear x mt0 aibx sl0 H0 Hr0 Hxma (conj Dlo Dhi)).
    - (* [comment removed for export] *) intros sc Hsc. apply dn_dll; [apply Hnotact | exact (wf_act_dll0 sc Hsc)].
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aibx & slx & Hx & Hrx & R).
      assert (Hxma : x <> ma) by (intros ->; exact (Hnotact sc Hin)).
      destruct (dn_fwd x mtx aibx slx Hx Hrx Hxma) as (mx' & slx' & Hx' & Hrx' & _ & _ & _ & _ & _ & _ & Esc & _).
      exists mx', aibx, slx'. rewrite Esc. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & _ & _ & _ & Esc & _ & _ & _ & Ep & En & _).
      rewrite Esc, Ep, En. eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hne Hx.
      assert (Hxma : x <> ma) by (intros ->; exact (Hnotact sc Hin)).
      destruct (wf_act_mem0 sc x Hin) as (mt0 & aibx & slx & Hx0 & Hr0 & _).
      destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]]; [| exact (False_ind _ (Hxma eq_refl)) |].
      + rewrite pm'_avail, pm'_freed. eauto.
      + rewrite Hx0 in H. injection H as <-. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & _ & _ & _ & Esc & _ & _ & _ & Ep & En & _).
      rewrite Esc, Ep, En. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _ & _ & Eml & _).
      rewrite Em, Eml. unfold grp_map_len. rewrite Eml. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hmlx Hx' Hrx' Hmlx'.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _ & _ & Eml & _).
      destruct (GB x' mtx' aibx' slx' Hx' Hrx') as (mt0' & sl0' & H0' & Hr0' & _ & _ & _ & Em' & _ & _ & Eml' & _).
      rewrite Em, Em', Eml in *. unfold grp_map_len. rewrite Eml, Eml'. rewrite Eml' in Hmlx'. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx'.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _).
      destruct (GB x' mtx' aibx' slx' Hx' Hrx') as (mt0' & sl0' & H0' & Hr0' & _ & _ & _ & Em' & _).
      rewrite Em, Em'. eauto.
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map0 q n). unfold is_live. split.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & Hi0 & Hi & E).
        assert (Hxma : x <> ma).
        { intros ->. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-. destruct (Hidle _ _ Hi); discriminate. }
        destruct (dn_fwd x mtx aibx slx Hx Hrx Hxma) as (mx' & slx' & Hx' & Hrx' & _ & _ & Em & Es & _ & _ & _ & _ & _ & _ & Hfw & _).
        exists x, mx', aibx, slx', i, off. split; [exact Hx'|]. split; [exact Hrx'|]. split; [exact Hi0|].
        split; [apply Hfw; [exact Hi | intros Ec; discriminate Ec]|]. unfold slot_start. rewrite Em, Es. exact E.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & Hi0 & Hi & E).
        destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & Es & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsl & _).
        destruct (Hsl _ _ Hi) as [Hi' | (_ & _ & Ebad & _)]; [| discriminate Ebad].
        exists x, mt0, aibx, sl0, i, off. unfold slot_start in *. rewrite <- Em, <- Es. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & Es & Ec & _ & _ & El & _). rewrite Es, Ec, El. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & Es & _ & Eml & Esc & El & _). rewrite Es, Eml, Esc, El. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx k Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & _ & _ & _ & _ & El & _ & Efr & _). rewrite El, Efr. eauto.
    - (* [comment removed for export] *) intros sc x mtx aibx slx x' mtx' aibx' slx' Hin Hin' Hx Hrx Hx' Hrx'.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & _ & _ & _ & _ & El & _).
      destruct (GB x' mtx' aibx' slx' Hx' Hrx') as (mt0' & sl0' & H0' & Hr0' & _ & _ & _ & _ & _ & _ & _ & _ & El' & _).
      rewrite El, El'. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & Es & Ec & Eml & _ & El & _). rewrite Es, Ec, Eml, El. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & Es & _ & _ & Esc & _ & Eav & Efr & _). rewrite Es, Esc, Eav, Efr. eauto.
    - (* [comment removed for export] *) intros p0 m0 aib0 sl0x k ch x mtx aibx slx Hp0 Hpr0 Hk0 Hk Hx Hrx Hlo Hhi.
      destruct (GB p0 m0 aib0 sl0x Hp0 Hpr0) as (m00 & sl00 & H00 & Hr00 & Hp0ma & _ & _ & Em0 & Es0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsl0 & _).
      destruct (GB x mtx aibx slx Hx Hrx) as (mt1 & sl1 & H1 & Hr1 & Hxma & _ & _ & Em1 & Es1 & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
      destruct (Hsl0 _ _ Hk) as [Hk' | (_ & _ & E & _)]; [| discriminate E].
      unfold slot_start, slot_end in Hlo, Hhi. rewrite Em0, Es0, Elo1, Ehi1 in *.
      destruct (wf_cover0 p0 m00 aib0 sl00 k ch x mt1 aibx sl1 H00 Hr00 Hk0 Hk' H1 Hr1 Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & Clo & Chi).
      assert (Hchma : ch <> ma).
      { intros ->. destruct (nested_parent_unique p0 m00 aib0 sl00 k H00 Hr00 Hk0 Hk') as [-> ->].
        destruct (dn_group_inv _ _ _ _ Hp0 Hpr0) as [(_ & _ & _ & ->) | (Hne & _)]; [| exact (Hne eq_refl)].
        rewrite psl'_j in Hk. discriminate Hk. }
      destruct (dn_fwd ch mtc aibc slc Hch Hrc Hchma) as (mc' & slc' & Hch' & Hrc' & _ & _ & _ & _ & _ & _ & _ & _ & Eclo & Echi & _).
      exists mc', aibc, slc'. rewrite Eclo, Echi. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & Es & _ & _ & Esc & _). rewrite Es, Esc. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _ & _ & Eml & _).
      rewrite Em, Eml. unfold grp_map_len. rewrite Eml. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (GB x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & _ & _ & _ & _ & Esc & El & _). rewrite Esc, El. eauto.
  Qed.

  Lemma has_dnA : forall f, has dnA f -> has A f.
  Proof.
    intros f [Hc | [Har | [Hm | Hg]]].
    - left. exact Hc.
    - right; left. exact Har.
    - right; right; left. destruct Hm as (x & mtx & fl & Hx & ->).
      destruct (dn_meta_inv x mtx Hx) as [(-> & ->) | [(-> & ->) | (_ & _ & H)]].
      + exists pa, pm, fl. rewrite pm'_f. auto.
      + exists ma, mt, fl. split; [exact Hma|]. unfold mtDn. rewrite mt_f_MT. reflexivity.
      + exists x, mtx, fl. auto.
    - right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      destruct (dn_group_back x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & Ef & Ew & Em & Es & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsl & _).
      exists x, mt0, aibx, sl0. split; [exact H0|]. split; [exact Hr0|].
      destruct R as [Hh | (i & st & Hi & Hin)].
      + left. unfold grp_hdr_fields in *. rewrite Em in Hh. exact Hh.
      + destruct (Hsl _ _ Hi) as [Hi' | (-> & -> & -> & Hi')].
        * right. exists i, st. split; [exact Hi'|]. unfold slot_fields in *. rewrite Em, Es in Hin. exact Hin.
        * right. exists (Z.to_nat j), (SNested ma). split; [exact Hi'|].
          unfold slot_fields, slot_fields_g in *. rewrite Em, Es in Hin.
          apply in_app_iff in Hin. apply in_app_iff. destruct Hin as [Hin | []]; left; exact Hin.
  Qed.

  Lemma dom_dnA : forall x, dom dnA x <-> dom A x.
  Proof.
    intros x. split.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hmly & Hx) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      destruct (dn_group_back y mty aiby sly Hy Hry) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _ & _ & Eml & _).
      right; left. exists y, mt0, aiby, sl0. unfold grp_map_len in *. rewrite <- Em, <- Eml. auto.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & Hmly & Hx) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      assert (Hyma : y <> ma) by (intros ->; rewrite Hma in Hy; injection Hy as <-; lia).
      destruct (dn_fwd y mty aiby sly Hy Hry Hyma) as (my' & sly' & Hy' & Hry' & _ & _ & Em & _ & _ & Eml & _).
      right; left. exists y, my', aiby, sly'. unfold grp_map_len in *. rewrite Em, Eml. auto.
  Qed.

  Lemma Rep_dnA : forall m, Rep A m -> Rep dnA m.
  Proof.
    intros m [R1 R2]. constructor.
    - intros x b (f & Hf & Hb). apply R1. exists f. split; [apply has_dnA; exact Hf | exact Hb].
    - intros x Hx. apply R2. apply (proj1 (dom_dnA x)). exact Hx.
  Qed.

  Lemma VMok_dnA : forall h, VMok A h -> VMok dnA h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    constructor; cbn [a_ctx a_areas a_pages a_mblocks a_xmaps dnA]; try assumption.
    - intros x mtx aibx slx Hx Hrx Hmlx.
      destruct (dn_group_back x mtx aibx slx Hx Hrx) as (mt0 & sl0 & H0 & Hr0 & _ & _ & _ & Em & _ & _ & Eml & _).
      unfold grp_map_len. rewrite Em, Eml. rewrite Eml in Hmlx. eauto.
    - intros b sz Hin. destruct (Vall b sz Hin) as [(y & mty & aiby & sly & Hy & Hry & Hmly & Eb & Esz) | [B | X]]; [| right; left; exact B | right; right; exact X].
      assert (Hyma : y <> ma) by (intros ->; rewrite Hma in Hy; injection Hy as <-; lia).
      destruct (dn_fwd y mty aiby sly Hy Hry Hyma) as (my' & sly' & Hy' & Hry' & _ & _ & Em & _ & _ & Eml & _).
      left. exists y, my', aiby, sly'. unfold grp_map_len in *. rewrite Em, Eml. auto.
  Qed.
End DissolveNested.

End WithLayout.
