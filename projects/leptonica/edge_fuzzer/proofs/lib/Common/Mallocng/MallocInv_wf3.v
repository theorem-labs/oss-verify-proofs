(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_wf MallocInv_dll.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


Definition dflt (d : Z) (o : option Z) : Z := match o with Some v => v | None => d end.

Definition is_head_slot (k : cslot) : Prop := match k with KActive _ | KFmh => True | _ => False end.

Section Relists.
  Variable A : astate.
  Hypothesis HW : WF A.
  (* [comment removed for export] *)
  Variables (P N : Z -> option Z).
  (* [comment removed for export] *)
  Variables (act' : Z -> list Z) (fl' : list Z).
  (* [comment removed for export] *)
  Variable V : option (Z * meta_rec).

  Definition relink (x : Z) (mt : meta_rec) : meta_rec :=
    MT (fun fl => match fl with
                  | FPrev => dflt (mt_f mt FPrev) (P x)
                  | FNext => dflt (mt_f mt FNext) (N x)
                  | _ => mt_f mt fl end) (mt_role mt).

  Definition g' : mmap_t := fun x =>
    match V with
    | Some (v, mtv) => if Z.eq_dec x v then Some mtv else option_map (relink x) (a_meta A x)
    | None => option_map (relink x) (a_meta A x)
    end.

  Definition c' : ctx_rec := fun k =>
    match k with
    | KActive sc => hd 0 (act' sc)
    | KFmh => hd 0 fl'
    | _ => a_ctx A k
    end.

  Definition A' : astate :=
    AST c' (a_areas A) g' fl' act' (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) (a_xmaps A).

  (* [comment removed for export] *)
  Hypothesis R_victim : match V with
    | Some (v, mtv) => exists mt0, a_meta A v = Some mt0 /\
        (mt_role mt0 = RDead \/ mt_role mt0 = RFree) /\ (mt_role mtv = RDead \/ mt_role mtv = RFree)
    | None => True end.

  (* [comment removed for export] *)
  Hypothesis R_fl_nodup : NoDup fl'.
  Hypothesis R_fl_mem : forall x, In x fl' <-> exists mt, g' x = Some mt /\ mt_role mt = RFree.
  Hypothesis R_fl_dll : dll A' fl'.
  Hypothesis R_act_nodup : forall sc, NoDup (act' sc).
  Hypothesis R_act_dll : forall sc, 0 <= sc < 48 -> dll A' (act' sc).
  Hypothesis R_act_mem : forall sc x, In x (act' sc) ->
    exists mt aib slots, g' x = Some mt /\ mt_role mt = RGroup aib slots /\ mt_sc mt = sc.
  Hypothesis R_unlinked : forall x mt aib slots, g' x = Some mt -> mt_role mt = RGroup aib slots ->
    ~ In x (act' (mt_sc mt)) -> mt_prev mt = 0 /\ mt_next mt = 0.
  Hypothesis R_nonhead : forall sc x mt, In x (act' sc) -> x <> hd 0 (act' sc) ->
    g' x = Some mt -> mt_avail mt = 0 /\ mt_freed mt <> 0.
  Hypothesis R_act63 : forall x mt aib slots, g' x = Some mt -> mt_role mt = RGroup aib slots ->
    mt_sc mt = 63 -> mt_prev mt = 0 /\ mt_next mt = 0.
  Hypothesis R_partial : forall sc x mtx aibx slx y mty aiby sly,
    In x (act' sc) -> In y (act' sc) ->
    g' x = Some mtx -> mt_role mtx = RGroup aibx slx ->
    g' y = Some mty -> mt_role mty = RGroup aiby sly ->
    aibx mod 32 < mt_last mtx -> aiby mod 32 < mt_last mty -> x = y.
  Hypothesis R_avail_zero : forall x mt, g' x = Some mt -> mt_role mt = RAvail ->
    mt_prev mt = 0 /\ mt_next mt = 0 /\ mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0.
  Hypothesis R_free_zero : forall x mt, g' x = Some mt -> mt_role mt = RFree ->
    mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0.

  (* [comment removed for export] *)
  Lemma g'_inv : forall x mt', g' x = Some mt' ->
    (exists mtv, V = Some (x, mtv) /\ mt' = mtv) \/
    (exists mt, a_meta A x = Some mt /\ mt' = relink x mt /\ forall mtv, V <> Some (x, mtv)).
  Proof.
    intros x mt' H. unfold g' in H. destruct V as [[v mtv]|].
    - destruct (Z.eq_dec x v) as [-> | Hne].
      + left. exists mtv. injection H as <-. auto.
      + right. destruct (a_meta A x) as [mt|]; [| discriminate]. cbn in H. injection H as <-.
        exists mt. split; [reflexivity|]. split; [reflexivity|]. intros mtv' E. injection E as -> _. apply Hne. reflexivity.
    - right. destruct (a_meta A x) as [mt|]; [| discriminate]. cbn in H. injection H as <-.
      exists mt. split; [reflexivity|]. split; [reflexivity|]. intros mtv E. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma g'_group : forall x mt' aib slots, g' x = Some mt' -> mt_role mt' = RGroup aib slots ->
    exists mt, a_meta A x = Some mt /\ mt_role mt = RGroup aib slots /\ mt' = relink x mt.
  Proof.
    intros x mt' aib slots Hx Hr. destruct (g'_inv x mt' Hx) as [(mtv & EV & ->) | (mt & Hm & -> & _)].
    - exfalso. revert R_victim. rewrite EV. intros (mt0 & _ & _ & [E|E]); rewrite E in Hr; discriminate.
    - exists mt. cbn in Hr. auto.
  Qed.

  Lemma g'_of_group : forall x mt aib slots, a_meta A x = Some mt -> mt_role mt = RGroup aib slots ->
    g' x = Some (relink x mt).
  Proof.
    intros x mt aib slots Hx Hr. unfold g'. destruct V as [[v mtv]|].
    - destruct (Z.eq_dec x v) as [-> | Hne].
      + exfalso. revert R_victim. intros (mt0 & H0 & [E|E] & _); rewrite Hx in H0; injection H0 as <-; rewrite E in Hr; discriminate.
      + rewrite Hx. reflexivity.
    - rewrite Hx. reflexivity.
  Qed.

  Lemma g'_dom : forall x, g' x <> None <-> a_meta A x <> None.
  Proof.
    intros x. unfold g'. destruct V as [[v mtv]|].
    - destruct (Z.eq_dec x v) as [-> | Hne].
      + revert R_victim. intros (mt0 & H0 & _). rewrite H0. split; discriminate.
      + destruct (a_meta A x); cbn; split; auto; discriminate.
    - destruct (a_meta A x); cbn; split; auto; discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_mem : forall x mt, mt_mem (relink x mt) = mt_mem mt. Proof. reflexivity. Qed.
  Lemma rl_w32 : forall x mt, mt_w32 (relink x mt) = mt_w32 mt. Proof. reflexivity. Qed.
  Lemma rl_avail : forall x mt, mt_avail (relink x mt) = mt_avail mt. Proof. reflexivity. Qed.
  Lemma rl_freed : forall x mt, mt_freed (relink x mt) = mt_freed mt. Proof. reflexivity. Qed.
  Lemma rl_stride : forall x mt, mt_stride (relink x mt) = mt_stride mt. Proof. reflexivity. Qed.
  Lemma rl_cnt : forall x mt, mt_cnt (relink x mt) = mt_cnt mt. Proof. reflexivity. Qed.
  Lemma rl_last : forall x mt, mt_last (relink x mt) = mt_last mt. Proof. reflexivity. Qed.
  Lemma rl_maplen : forall x mt, mt_maplen (relink x mt) = mt_maplen mt. Proof. reflexivity. Qed.
  Lemma rl_sc : forall x mt, mt_sc (relink x mt) = mt_sc mt. Proof. reflexivity. Qed.
  Lemma rl_gext_lo : forall x mt, gext_lo (relink x mt) = gext_lo mt. Proof. reflexivity. Qed.
  Lemma rl_gext_hi : forall x mt, gext_hi (relink x mt) = gext_hi mt. Proof. reflexivity. Qed.
  Lemma rl_slot_start : forall x mt j, slot_start (relink x mt) j = slot_start mt j. Proof. reflexivity. Qed.
  Lemma rl_slot_end : forall x mt j, slot_end (relink x mt) j = slot_end mt j. Proof. reflexivity. Qed.
  Lemma rl_grp_map_len : forall x mt, grp_map_len (relink x mt) = grp_map_len mt. Proof. reflexivity. Qed.

  Theorem WF_relists : WF A'.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps A']; try assumption.
    - (* [comment removed for export] *) intros x. rewrite g'_dom. apply wf_meta_dom0.
    - (* [comment removed for export] *) intros H0. destruct (wf_uninit0 H0) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
      assert (NM : forall x, a_meta A x = None).
      { intros x. destruct (a_meta A x) eqn:E; [| reflexivity]. exfalso.
        destruct (proj1 (wf_meta_dom0 x) ltac:(rewrite E; discriminate)) as (pg & k & Hpg & _). rewrite E1 in Hpg. destruct Hpg. }
      assert (Efl : fl' = []).
      { assert (NF : forall x, ~ In x fl').
        { intros x Hin. destruct (proj1 (R_fl_mem x) Hin) as (mt & Hx & _).
          pose proof (proj1 (g'_dom x) ltac:(rewrite Hx; discriminate)) as X. apply X. apply NM. }
        clear -NF. destruct fl' as [|x l]; [reflexivity | exfalso; apply (NF x); left; reflexivity]. }
      assert (Eact : forall sc, act' sc = []).
      { intros sc. assert (NF : forall x, ~ In x (act' sc)).
        { intros x Hin. destruct (R_act_mem sc x Hin) as (mt & aib & slots & Hx & _).
          pose proof (proj1 (g'_dom x) ltac:(rewrite Hx; discriminate)) as X. apply X. apply NM. }
        clear -NF. destruct (act' sc) as [|x l]; [reflexivity | exfalso; apply (NF x); left; reflexivity]. }
      unfold c'. repeat split; auto; try (rewrite -> Efl; reflexivity). intros sc. rewrite Eact. reflexivity.
    - (* [comment removed for export] *) intros Hc. unfold c' in Hc |- *. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg.
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      intros k Hk. destruct (H4 k Hk) as (mt & Hmt & Hr). exists (relink (meta_addr pg k) mt).
      split; [| exact Hr]. unfold g'. destruct V as [[v mtv]|].
      + destruct (Z.eq_dec (meta_addr pg k) v) as [E | Hne]; [| rewrite Hmt; reflexivity].
        exfalso. revert R_victim. intros (mt0 & H0 & [E0|E0] & _); rewrite <- E, Hmt in H0; injection H0 as <-; rewrite E0 in Hr; discriminate.
      + rewrite Hmt. reflexivity.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->).
      exact (wf_grp0 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros x mtx aibx slx j off n Hx Hrx Hj Hj0.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_live0 x mt aibx slx j off n Hm Hr Hj Hj0).
    - (* [comment removed for export] *) intros x mtx aibx slx j ch Hx Hrx Hj Hj0.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->).
      destruct (wf_nested0 x mt aibx slx j ch Hm Hr Hj Hj0) as (mc & aibc & slc & Hmc & Hrc & H1 & H2 & H3).
      exists (relink ch mc), aibc, slc. rewrite (g'_of_group ch mc aibc slc Hmc Hrc).
      split; [reflexivity|]. split; [exact Hrc|]. split; [exact H1|]. split; [exact H2 | exact H3].
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hml.
      destruct (g'_group ch mc aibc slc Hch Hrc) as (mc0 & Hmc0 & Hrc0 & ->). rewrite rl_maplen in Hml.
      destruct (wf_nested_parent0 ch mc0 aibc slc Hmc0 Hrc0 Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & Hj0 & Hj).
      exists x, (relink x mtx), aibx, slx, j. rewrite (g'_of_group x mtx aibx slx Hx Hrx). split; [reflexivity|]. split; [exact Hrx|]. split; [exact Hj0 | exact Hj].
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->).
      destruct (wf_grp_root0 x mt aibx slx Hm Hr) as (mr & mtr & aibr & slr & Hmr & Hrr & Hml & Hlo & Hhi & Hself).
      exists mr, (relink mr mtr), aibr, slr. rewrite (g'_of_group mr mtr aibr slr Hmr Hrr).
      split; [reflexivity|]. split; [exact Hrr|]. split; [exact Hml|]. split; [exact Hlo|]. split; [exact Hhi | exact Hself].
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hxy.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mx & Hmx & Hrmx & ->).
      destruct (g'_group y mty aiby sly Hy Hry) as (my & Hmy & Hrmy & ->).
      exact (wf_laminar0 x mx aibx slx y my aiby sly Hmx Hrmx Hmy Hrmy Hxy).
    - (* [comment removed for export] *) intros sc Hsc. reflexivity.
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx Hml.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_disj_area_grp0 pg x mt aibx slx Hpg Hm Hr Hml).
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hmlx Hy Hry Hmly Hxy.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mx & Hmx & Hrmx & ->).
      destruct (g'_group y mty aiby sly Hy Hry) as (my & Hmy & Hrmy & ->).
      exact (wf_disj_grp_grp0 x mx aibx slx y my aiby sly Hmx Hrmx Hmlx Hmy Hrmy Hmly Hxy).
    - (* [comment removed for export] *) intros x mtx aibx slx y mty aiby sly Hx Hrx Hy Hry Hmm.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mx & Hmx & Hrmx & ->).
      destruct (g'_group y mty aiby sly Hy Hry) as (my & Hmy & Hrmy & ->).
      exact (wf_grp_mem_inj0 x mx aibx slx y my aiby sly Hmx Hrmx Hmy Hrmy Hmm).
    - (* [comment removed for export] *) intros p n. rewrite (wf_live_map0 p n). unfold is_live. cbn. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Ep).
        exists x, (relink x mtx), aibx, slx, j, off. rewrite (g'_of_group x mtx aibx slx Hx Hrx). repeat split; assumption.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & Ep).
        destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->).
        exists x, mt, aibx, slx, j, off. repeat split; assumption.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_span0 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_single0 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros x mtx aibx slx j Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_inactive0 x mt aibx slx j Hm Hr).
    - (* [comment removed for export] *) intros k. unfold c'. destruct k; try apply wf_ctx_nonneg0.
      + (* [comment removed for export] *) destruct fl' as [|x l]; cbn; [llia|].
        destruct (proj1 (R_fl_mem x) ltac:(left; reflexivity)) as (mt & Hx & _).
        pose proof (proj1 (g'_dom x) ltac:(rewrite Hx; discriminate)) as X.
        destruct (a_meta A x) eqn:E; [| exfalso; apply X; reflexivity].
        destruct (proj1 (wf_meta_dom0 x) ltac:(rewrite E; discriminate)) as (pg & k & Hpg & Hk & ->).
        destruct (wf_areas_al0 pg Hpg) as [_ (H1 & _)]. unfold meta_addr. llia.
      + (* [comment removed for export] *) destruct (act' i) as [|x l] eqn:El; cbn; [llia|].
        destruct (R_act_mem i x ltac:(rewrite El; left; reflexivity)) as (mt & aib & slots & Hx & _).
        pose proof (proj1 (g'_dom x) ltac:(rewrite Hx; discriminate)) as X.
        destruct (a_meta A x) eqn:E; [| exfalso; apply X; reflexivity].
        destruct (proj1 (wf_meta_dom0 x) ltac:(rewrite E; discriminate)) as (pg & k & Hpg & Hk & ->).
        destruct (wf_areas_al0 pg Hpg) as [_ (H1 & _)]. unfold meta_addr. llia.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_nested_small0 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_reusable0 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (g'_group pa pm paib psl Hpa Hpr) as (pm0 & Hpm0 & Hpr0 & ->).
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mx0 & Hmx0 & Hrx0 & ->).
      destruct (wf_cover0 pa pm0 paib psl j ch x mx0 aibx slx Hpm0 Hpr0 Hj0 Hj Hmx0 Hrx0 Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & H1 & H2).
      exists (relink ch mtc), aibc, slc. rewrite (g'_of_group ch mtc aibc slc Hch Hrc). repeat split; auto.
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_stride200 x mt aibx slx Hm Hr).
    - (* [comment removed for export] *) intros pg x mtx aibx slx Hpg Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_disj_page_grp0 pg x mt aibx slx Hpg Hm Hr).
    - (* [comment removed for export] *) intros x mtx aibx slx Hx Hrx.
      destruct (g'_group x mtx aibx slx Hx Hrx) as (mt & Hm & Hr & ->). exact (wf_partial_sc0 x mt aibx slx Hm Hr).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma relists_has_grp : forall f, has_grp A' f <-> has_grp A f.
  Proof.
    intros f. split.
    - intros (x & mtx & aib & sl & Hx & Hrx & R). destruct (g'_group x mtx aib sl Hx Hrx) as (mt & Hm & Hr & ->).
      exists x, mt, aib, sl. auto.
    - intros (x & mt & aib & sl & Hx & Hrx & R). exists x, (relink x mt), aib, sl.
      split; [exact (g'_of_group x mt aib sl Hx Hrx) | auto].
  Qed.

  (* [comment removed for export] *)
  Lemma relists_has_inv : forall f, has A' f ->
    (exists k, cvalid k /\ f = FCT (caddr k) (clen k) (c' k)) \/
    has_area A f \/
    (exists x mt' fl, g' x = Some mt' /\ f = FCT (x + moff fl) (mlen fl) (mt_f mt' fl)) \/
    has_grp A f.
  Proof.
    intros f [Hc | [Har | [Hm | Hg]]].
    - left. exact Hc.
    - right; left. exact Har.
    - right; right; left. exact Hm.
    - right; right; right. apply (proj1 (relists_has_grp f)). exact Hg.
  Qed.

  Lemma relists_has_ctx : forall k, cvalid k -> has A' (FCT (caddr k) (clen k) (c' k)).
  Proof. intros k Hk. left. exists k. auto. Qed.

  Lemma relists_has_area : forall f, has_area A f -> has A' f.
  Proof. intros f H. right; left. exact H. Qed.

  Lemma relists_has_meta : forall x mt' fl, g' x = Some mt' -> has A' (FCT (x + moff fl) (mlen fl) (mt_f mt' fl)).
  Proof. intros x mt' fl Hx. right; right; left. exists x, mt', fl. auto. Qed.

  Lemma relists_has_grp_kept : forall f, has_grp A f -> has A' f.
  Proof. intros f H. right; right; right. apply (proj2 (relists_has_grp f)). exact H. Qed.

  Lemma dom_relists : forall x, dom A' x <-> dom A x.
  Proof.
    intros x. unfold dom. cbn [a_areas a_meta a_pages A']. split.
    - intros [Ha | [(y & mty & aib & sl & Hy & Hry & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      destruct (g'_group y mty aib sl Hy Hry) as (mt & Hm & Hr & ->). exists y, mt, aib, sl. auto.
    - intros [Ha | [(y & mt & aib & sl & Hy & Hry & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      exists y, (relink y mt), aib, sl. split; [exact (g'_of_group y mt aib sl Hy Hry) | auto].
  Qed.

  Lemma VMok_relists : forall h, VMok A h -> VMok A' h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vlim]. constructor; cbn [a_ctx a_areas a_pages a_mblocks a_xmaps A' c']; auto.
    - intros x mtx aib sl Hx Hrx. destruct (g'_group x mtx aib sl Hx Hrx) as (mt & Hm & Hr & ->).
      rewrite rl_maplen, rl_mem, rl_grp_map_len. exact (Vg x mt aib sl Hm Hr).
    - intros b sz Hin.
      destruct (Vall b sz Hin) as [(x & mtx & aibx & slx & Hx & Hrx & Hml & Eb & Esz) | [Hbr | Hbl]]; [left | right; left; exact Hbr | right; right; exact Hbl].
      exists x, (relink x mtx), aibx, slx. replace (a_meta A' x) with (g' x) by reflexivity.
      rewrite (g'_of_group x mtx aibx slx Hx Hrx), rl_maplen, rl_mem, rl_grp_map_len. repeat split; auto.
  Qed.
End Relists.

End WithLayout.
