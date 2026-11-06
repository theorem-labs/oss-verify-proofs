(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3
  MallocInv_dll MallocInv_coh.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section DeadLocal.
  Variables (A A' : astate) (m : Z) (md md' : meta_rec).
  Hypothesis HW : WF A.
  Hypothesis Hm : a_meta A m = Some md.
  Hypothesis Hr : mt_role md = RDead.
  Hypothesis Hm' : a_meta A' m = Some md'.
  Hypothesis Hr' : mt_role md' = RDead.
  Hypothesis Hoth : forall x, x <> m -> a_meta A' x = a_meta A x.
  Hypothesis Ectx : a_ctx A' = a_ctx A.
  Hypothesis Eareas : a_areas A' = a_areas A.
  Hypothesis Efl : a_freelist A' = a_freelist A.
  Hypothesis Eact : a_active A' = a_active A.
  Hypothesis Epages : a_pages A' = a_pages A.
  Hypothesis Ebrk : a_brk_lo A' = a_brk_lo A.
  Hypothesis Elive : a_live A' = a_live A.
  Hypothesis Emb : a_mblocks A' = a_mblocks A.
  Hypothesis Exm : a_xmaps A' = a_xmaps A.

  Lemma dl_meta_inv : forall x mtx, a_meta A' x = Some mtx -> (x = m /\ mtx = md') \/ (x <> m /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. destruct (Z.eq_dec x m) as [-> | Hne].
    - left. rewrite Hm' in Hx. injection Hx as <-. auto.
    - right. rewrite (Hoth x Hne) in Hx. auto.
  Qed.

  Lemma dl_old : forall x mtx, a_meta A x = Some mtx -> mt_role mtx <> RDead -> a_meta A' x = Some mtx.
  Proof.
    intros x mtx Hx Hrx. destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm in Hx; injection Hx as <-; contradiction|].
    rewrite (Hoth x Hne). exact Hx.
  Qed.

  Lemma dl_old_grp : forall x mtx aibx slx, a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx -> a_meta A' x = Some mtx.
  Proof. intros x mtx aibx slx Hx Hrx. apply (dl_old x mtx Hx). rewrite Hrx. discriminate. Qed.

  Lemma dl_group_inv : forall x mtx aibx slx, a_meta A' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    a_meta A x = Some mtx /\ x <> m.
  Proof.
    intros x mtx aibx slx Hx Hrx. destruct (dl_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [| auto].
    rewrite Hr' in Hrx. discriminate Hrx.
  Qed.

  Lemma dl_role_inv : forall x mtx, a_meta A' x = Some mtx -> mt_role mtx <> RDead -> a_meta A x = Some mtx /\ x <> m.
  Proof.
    intros x mtx Hx Hrx. destruct (dl_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [contradiction | auto].
  Qed.

  Lemma dl_not_in_fl : ~ In m (a_freelist A).
  Proof.
    intros Hin. destruct (proj1 (wf_fl_mem A HW m) Hin) as (mt0 & H0 & Hr0). rewrite Hm in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.

  Lemma dl_not_in_act : forall sc, ~ In m (a_active A sc).
  Proof.
    intros sc Hin. destruct (wf_act_mem A HW sc m Hin) as (mt0 & aib0 & sl0 & H0 & Hr0 & _). rewrite Hm in H0. injection H0 as <-.
    rewrite Hr in Hr0. discriminate Hr0.
  Qed.

  Lemma dl_dll : forall l, ~ In m l -> dll A l -> dll A' l.
  Proof.
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R). exists mtx. split; [| exact R].
    rewrite Hoth; [exact Hx|]. intros ->. apply Hn. eapply nth_error_In. exact Hk.
  Qed.

  Theorem WF_dead_local : WF A'.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; rewrite ?Ectx, ?Eareas, ?Efl, ?Eact, ?Epages, ?Ebrk, ?Elive, ?Emb, ?Exm; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm, Hm'; split; intros _; discriminate | rewrite (Hoth x Hne); tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply (dl_old _ _ Hmk). rewrite Hrk. discriminate.
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dl_role_inv x mtx Hx ltac:(rewrite Hrx; discriminate)) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (dl_role_inv x mtx Hx ltac:(rewrite Hrx; discriminate)) as [H _]. eauto.
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply (dl_old _ _ Hx). rewrite Hrx. discriminate.
      + intros (mtx & Hx & Hrx). destruct (dl_role_inv x mtx Hx ltac:(rewrite Hrx; discriminate)) as [H _]. eauto.
    - (* [comment removed for export] *) apply dl_dll; [apply dl_not_in_fl | exact wf_fl_dll0].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx i off n Hx Hrx. destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx i ch Hx Hrx Hi Hi0. destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _].
      destruct (wf_nested0 x mtx aibx slx i ch H Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & R).
      exists mc, aibc, slc. split; [exact (dl_old_grp _ _ _ _ Hmc Hrc) | split; [exact Hrc | exact R]].
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hmlc. destruct (dl_group_inv ch mc aibc slc Hch Hrc) as [H _].
      destruct (wf_nested_parent0 ch mc aibc slc H Hrc Hmlc) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
      exists x, mtx, aibx, slx, j. split; [exact (dl_old_grp _ _ _ _ Hx Hrx) | split; [exact Hrx | split; [exact Hj0 | exact Hj]]].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _].
      destruct (wf_grp_root0 x mtx aibx slx H Hrx) as (mr & mtr & aibr & slr & Hmr & Hrr & R).
      exists mr, mtr, aibr, slr. split; [exact (dl_old_grp _ _ _ _ Hmr Hrr) | split; [exact Hrr | exact R]].
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx' Hne.
      destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dl_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros sc Hsc. apply dl_dll; [apply dl_not_in_act | exact (wf_act_dll0 sc Hsc)].
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aibx & slx & Hx & Hrx & R).
      exists mtx, aibx, slx. split; [exact (dl_old_grp _ _ _ _ Hx Hrx) | auto].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hne Hx.
      destruct (dl_meta_inv x mtx Hx) as [(-> & ->) | (_ & Hx')]; [exfalso; exact (dl_not_in_act sc Hin)|]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hmlx Hx' Hrx'.
      destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dl_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx x' mtx' aibx' slx' Hx Hrx Hx' Hrx'.
      destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dl_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map0 q n). unfold is_live. split.
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & R). exists x, mtx, aibx, slx, i, off.
        split; [exact (dl_old_grp _ _ _ _ Hx Hrx) | auto].
      + intros (x & mtx & aibx & slx & i & off & Hx & Hrx & R). destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _].
        exists x, mtx, aibx, slx, i, off. auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx aibx slx x' mtx' aibx' slx' Hin Hin' Hx Hrx Hx' Hrx'.
      destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (dl_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (dl_group_inv _ _ _ _ Hpa Hpr) as [Hpa0 _]. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [Hx0 _].
      destruct (wf_cover0 pa pm paib psl j ch x mtx aibx slx Hpa0 Hpr Hj0 Hj Hx0 Hrx Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & R).
      exists mtc, aibc, slc. split; [exact (dl_old_grp _ _ _ _ Hch Hrc) | split; [exact Hrc | exact R]].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx. destruct (dl_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma has_dead_local : forall f, has A' f ->
    (has A f /\ forall fl, f <> FCT (m + moff fl) (mlen fl) (mt_f md fl)) \/ (exists fl, f = FCT (m + moff fl) (mlen fl) (mt_f md' fl)) \/
    (has A f).
  Proof.
    intros f [Hc | [Har | [Hmf | Hg]]].
    - right; right. left. unfold has_ctx in *. rewrite Ectx in Hc. exact Hc.
    - right; right. right; left. unfold has_area in *. rewrite Eareas, Ectx in Har. exact Har.
    - destruct Hmf as (x & mtx & fl & Hx & ->). destruct (dl_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)].
      + right; left. exists fl. reflexivity.
      + right; right. right; right; left. exists x, mtx, fl. auto.
    - right; right. right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _]. exists x, mtx, aibx, slx. auto.
  Qed.

  Lemma has_dead_local_inv : forall f, has A f ->
    has A' f \/ exists fl, f = FCT (m + moff fl) (mlen fl) (mt_f md fl).
  Proof.
    intros f [Hc | [Har | [Hmf | Hg]]].
    - left. left. unfold has_ctx in *. rewrite Ectx. exact Hc.
    - left. right; left. unfold has_area in *. rewrite Eareas, Ectx. exact Har.
    - destruct Hmf as (x & mtx & fl & Hx & ->). destruct (Z.eq_dec x m) as [-> | Hne].
      + right. rewrite Hm in Hx. injection Hx as ->. exists fl. reflexivity.
      + left. right; right; left. exists x, mtx, fl. rewrite (Hoth x Hne). auto.
    - left. right; right; right. destruct Hg as (x & mtx & aibx & slx & Hx & Hrx & R).
      exists x, mtx, aibx, slx. split; [exact (dl_old_grp _ _ _ _ Hx Hrx) | auto].
  Qed.

  Lemma dom_dead_local : forall x, dom A' x <-> dom A x.
  Proof.
    intros x. unfold dom. rewrite Eareas, Epages. split.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & R) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      right; left. destruct (dl_group_inv y mty aiby sly Hy Hry) as [H _]. exists y, mty, aiby, sly. auto.
    - intros [Ha | [(y & mty & aiby & sly & Hy & Hry & R) | Hp]]; [left; exact Ha | | right; right; exact Hp].
      right; left. exists y, mty, aiby, sly. split; [exact (dl_old_grp _ _ _ _ Hy Hry) | auto].
  Qed.

  Lemma VMok_dead_local : forall h, VMok A h -> VMok A' h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop]. constructor; rewrite ?Ectx, ?Eareas, ?Epages, ?Emb, ?Exm; try assumption.
    - intros x mtx aibx slx Hx Hrx Hml. destruct (dl_group_inv x mtx aibx slx Hx Hrx) as [H _]. eauto.
    - intros b sz Hin. destruct (Vall b sz Hin) as [(x & mtx & aibx & slx & Hx & Hrx & R) | Ho]; [left | right; exact Ho].
      exists x, mtx, aibx, slx. split; [exact (dl_old_grp _ _ _ _ Hx Hrx) | auto].
  Qed.

  Lemma meta_usage_dead_local : forall sc x, meta_usage A' sc x = meta_usage A sc x.
  Proof.
    intros sc x. unfold meta_usage. destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm, Hm', Hr, Hr'; reflexivity | rewrite (Hoth x Hne); reflexivity].
  Qed.
End DeadLocal.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition deadupd (A : astate) (m : Z) (md : meta_rec) (fl : mfield) (v : Z) : astate :=
  ameta_upd A m (mupd md fl v).

Section DeadUpd.
  Variables (A : astate) (m : Z) (md : meta_rec) (fl : mfield) (v : Z).
  Hypothesis HW : WF A.
  Hypothesis Hm : a_meta A m = Some md.
  Hypothesis Hr : mt_role md = RDead.

  Let A' := deadupd A m md fl v.

  Lemma du_meta : forall x, a_meta A' x = if Z.eq_dec x m then Some (mupd md fl v) else a_meta A x.
  Proof. intros x. reflexivity. Qed.
  Lemma du_meta_m : a_meta A' m = Some (mupd md fl v).
  Proof. rewrite du_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.
  Lemma du_meta_other : forall x, x <> m -> a_meta A' x = a_meta A x.
  Proof. intros x Hx. rewrite du_meta. destruct (Z.eq_dec x m); [contradiction | reflexivity]. Qed.

  Let Hr' : mt_role (mupd md fl v) = RDead := eq_trans (mupd_role md fl v) Hr.

  Theorem WF_deadupd : WF A'.
  Proof. exact (WF_dead_local A A' m md (mupd md fl v) HW Hm Hr du_meta_m Hr' du_meta_other eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl). Qed.

  Lemma has_deadupd : forall f, has A' f -> has A f \/ exists fl', f = FCT (m + moff fl') (mlen fl') (mt_f (mupd md fl v) fl').
  Proof.
    intros f Hf. destruct (has_dead_local A A' m md (mupd md fl v) du_meta_m Hr' du_meta_other eq_refl eq_refl f Hf) as [[H _] | [H | H]]; auto.
  Qed.

  Lemma has_deadupd_inv : forall f, has A f -> has A' f \/ exists fl', f = FCT (m + moff fl') (mlen fl') (mt_f md fl').
  Proof. intros f Hf. exact (has_dead_local_inv A A' m md Hm Hr du_meta_other eq_refl eq_refl f Hf). Qed.

  Lemma has_deadupd_field : forall fl', has A' (FCT (m + moff fl') (mlen fl') (mt_f (mupd md fl v) fl')).
  Proof. intros fl'. right; right; left. exists m, (mupd md fl v), fl'. split; [exact du_meta_m | reflexivity]. Qed.

  Lemma dom_deadupd : forall x, dom A' x <-> dom A x.
  Proof. exact (dom_dead_local A A' m md (mupd md fl v) Hm Hr du_meta_m Hr' du_meta_other eq_refl eq_refl). Qed.

  Lemma VMok_deadupd : forall h, VMok A h -> VMok A' h.
  Proof. exact (VMok_dead_local A A' m md (mupd md fl v) Hm Hr du_meta_m Hr' du_meta_other eq_refl eq_refl eq_refl eq_refl eq_refl). Qed.

  Lemma meta_usage_deadupd : forall sc x, meta_usage A' sc x = meta_usage A sc x.
  Proof. exact (meta_usage_dead_local A A' m md (mupd md fl v) Hm Hr du_meta_m Hr' du_meta_other). Qed.
End DeadUpd.

End WithLayout.
