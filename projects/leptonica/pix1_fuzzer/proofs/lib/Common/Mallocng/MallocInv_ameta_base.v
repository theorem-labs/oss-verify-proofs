(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_sep MallocInv_wf MallocInv_wf4 MallocInv_coh.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
Definition mzero (r : mrole) : meta_rec := MT (fun _ => 0) r.
Lemma mt_f_mzero : forall r fl, mt_f (mzero r) fl = 0.
Proof. intros r fl. unfold mzero. apply mt_f_MT. Qed.

(* [comment removed for export] *)
Definition meta_index (p x : Z) : option Z :=
  if (p + 24 <=? x) && (x <? p + 24 + 40 * 101) && ((x - (p + 24)) mod 40 =? 0)
  then Some ((x - (p + 24)) / 40) else None.

Lemma meta_index_spec : forall p x k, meta_index p x = Some k <-> (0 <= k < 101 /\ x = meta_addr p k).
Proof.
  intros p x k. unfold meta_index, meta_addr. split.
  - intros H. destruct (p + 24 <=? x) eqn:E1; [| discriminate H]. destruct (x <? p + 24 + 40 * 101) eqn:E2; [| discriminate H].
    destruct ((x - (p + 24)) mod 40 =? 0) eqn:E3; [| discriminate H]. cbn in H. injection H as <-.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3.
    pose proof (Z.div_mod (x - (p + 24)) 40 ltac:(llia)).
    split; [split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia] | llia].
  - intros [Hk ->].
    rewrite (proj2 (Z.leb_le _ _)) by llia. rewrite (proj2 (Z.ltb_lt _ _)) by llia.
    replace (p + 24 + 40 * k - (p + 24)) with (k * 40) by llia.
    rewrite Z.mod_mul, Z.eqb_refl by llia. cbn [andb]. rewrite Z.div_mul by llia. reflexivity.
Qed.

Lemma meta_index_none : forall p x, meta_index p x = None <-> forall k, 0 <= k < 101 -> x <> meta_addr p k.
Proof.
  intros p x. split.
  - intros H k Hk E. pose proof (proj2 (meta_index_spec p x k) (conj Hk E)). rewrite H in H0. discriminate H0.
  - intros H. destruct (meta_index p x) as [k|] eqn:E; [| reflexivity]. exfalso.
    destruct (proj1 (meta_index_spec p x k) E) as [Hk Ex]. exact (H k Hk Ex).
Qed.

Section AddArea.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variable p : Z.
  (* [comment removed for export] *)
  Variables (aac' aareas' : Z).

  Hypothesis Hal : page_aligned p.
  Hypothesis Hheap : heap_range p (p + 4096).
  Hypothesis Hdisj_area : forall pg, In pg (a_areas A) -> pg + 4096 <= p \/ p + 4096 <= pg.
  Hypothesis Hdisj_grp : forall ma mt aib sl, a_meta A ma = Some mt -> mt_role mt = RGroup aib sl ->
    0 < mt_maplen mt -> p + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= p.
  Hypothesis Hdisj_page : forall pg, In pg (a_pages A) -> pg + 4096 <= p \/ p + 4096 <= pg.
  Hypothesis Hamc0 : a_ctx A KAmc = 0.
  Hypothesis Hinit : a_ctx A KInit = 1.
  Hypothesis Hbrk : a_ctx A KBrk <> 0.
  Hypothesis Haac' : 0 <= aac'.
  Hypothesis Haareas' : 0 <= aareas'.
  (* [comment removed for export] *)
  Hypothesis Haac_acct : a_ctx A KAac <= aac' + 1.

  Definition aa_meta : mmap_t := fun x =>
    match meta_index p x with
    | Some k => Some (mzero (if k =? 0 then RDead else RAvail))
    | None => a_meta A x
    end.

  Definition aa_ctx : ctx_rec := fun k =>
    match k with
    | KAtail => p
    | KAhead => match a_areas A with [] => p | _ => a_ctx A KAhead end
    | KAm => meta_addr p 1
    | KAmc => 100
    | KAac => aac'
    | KAareas => aareas'
    | _ => a_ctx A k
    end.

  Definition aaA : astate :=
    AST aa_ctx (a_areas A ++ [p]) aa_meta (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) (a_xmaps A).

  (* [comment removed for export] *)
  Lemma p_notin : ~ In p (a_areas A).
  Proof. intros Hin. destruct (Hdisj_area p Hin); llia. Qed.

  Lemma old_meta_area : forall x, a_meta A x <> None ->
    exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ x = meta_addr pg k.
  Proof. intros x Hx. exact (proj1 (wf_meta_dom A HW x) Hx). Qed.

  Lemma old_meta_not_new : forall x, a_meta A x <> None -> meta_index p x = None.
  Proof.
    intros x Hx. destruct (old_meta_area x Hx) as (pg & k & Hpg & Hk & ->).
    apply (proj2 (meta_index_none p _)). intros k' Hk' E.
    destruct (Hdisj_area pg Hpg); unfold meta_addr in E; llia.
  Qed.

  Lemma aa_meta_old : forall x mt, a_meta A x = Some mt -> aa_meta x = Some mt.
  Proof.
    intros x mt Hx. unfold aa_meta. rewrite (old_meta_not_new x) by (rewrite Hx; discriminate). exact Hx.
  Qed.

  Lemma aa_meta_new : forall k, 0 <= k < 101 -> aa_meta (meta_addr p k) = Some (mzero (if k =? 0 then RDead else RAvail)).
  Proof.
    intros k Hk. unfold aa_meta. rewrite (proj2 (meta_index_spec p (meta_addr p k) k) (conj Hk eq_refl)). reflexivity.
  Qed.

  Lemma aa_meta_inv : forall x mt, aa_meta x = Some mt ->
    a_meta A x = Some mt \/ (exists k, 0 <= k < 101 /\ x = meta_addr p k /\ mt = mzero (if k =? 0 then RDead else RAvail)).
  Proof.
    intros x mt Hx. unfold aa_meta in Hx. destruct (meta_index p x) as [k|] eqn:E.
    - right. exists k. destruct (proj1 (meta_index_spec p x k) E) as [Hk Ex]. injection Hx as <-. auto.
    - left. exact Hx.
  Qed.

  Lemma aa_group_inv : forall x mt aib sl, aa_meta x = Some mt -> mt_role mt = RGroup aib sl -> a_meta A x = Some mt.
  Proof.
    intros x mt aib sl Hx Hr. destruct (aa_meta_inv x mt Hx) as [H | (k & Hk & -> & ->)]; [exact H|].
    exfalso. cbn in Hr. destruct (k =? 0); discriminate Hr.
  Qed.

  Lemma aa_free_inv : forall x mt, aa_meta x = Some mt -> mt_role mt = RFree -> a_meta A x = Some mt.
  Proof.
    intros x mt Hx Hr. destruct (aa_meta_inv x mt Hx) as [H | (k & Hk & -> & ->)]; [exact H|].
    exfalso. cbn in Hr. destruct (k =? 0); discriminate Hr.
  Qed.

  Lemma last_app1 : forall (l : list Z) x d, last (l ++ [x]) d = x.
  Proof. intros l x d. rewrite last_last. reflexivity. Qed.

  Lemma hd_app1 : forall (l : list Z) x d, hd d (l ++ [x]) = match l with [] => x | y :: _ => y end.
  Proof. intros [|y l] x d; reflexivity. Qed.

  Lemma dll_keptA : forall l, dll A l -> dll aaA l.
  Proof.
    intros l Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & Hn & Hp). exists mtx. split; [apply aa_meta_old; exact Hx | auto].
  Qed.

  Theorem WF_add_area : WF aaA.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    unfold heap_range in Hheap.
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps aaA]; try assumption.
    - (* [comment removed for export] *) apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app;
        [apply (proj1 (NoDup_ListNoDup _)); exact wf_areas_nodup0 | constructor; [intros [] | constructor] |].
      intros x Hx [<- | []]. exact (p_notin Hx).
    - (* [comment removed for export] *) intros pg Hpg. apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]]; [exact (wf_areas_al0 pg Hpg)|].
      split; [exact Hal | unfold heap_range; llia].
    - (* [comment removed for export] *) intros x. split.
      + intros Hx. unfold aa_meta in Hx. destruct (meta_index p x) as [k|] eqn:E.
        * destruct (proj1 (meta_index_spec p x k) E) as [Hk Ex]. exists p, k. split; [apply in_or_app; right; left; reflexivity | auto].
        * destruct (proj1 (wf_meta_dom0 x) Hx) as (pg & k & Hpg & Hk & Ex). exists pg, k. split; [apply in_or_app; left; exact Hpg | auto].
      + intros (pg & k & Hpg & Hk & ->). apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]].
        * destruct (a_meta A (meta_addr pg k)) as [mt|] eqn:E.
          -- rewrite (aa_meta_old (meta_addr pg k) mt E). discriminate.
          -- exfalso. apply (proj2 (wf_meta_dom0 (meta_addr pg k))); [| exact E]. exists pg, k. auto.
        * rewrite aa_meta_new by exact Hk. discriminate.
    - (* [comment removed for export] *) cbn. intros H0. exfalso. rewrite Hinit in H0. discriminate H0.
    - (* [comment removed for export] *) cbn. llia.
    - (* [comment removed for export] *) cbn. intros _. exists p. split; [intros E; destruct (a_areas A); discriminate E|].
      split; [symmetry; apply last_app1|]. split; [reflexivity|].
      intros k Hk. exists (mzero RAvail). split; [| reflexivity].
      rewrite aa_meta_new by llia. destruct (k =? 0) eqn:E; [apply Z.eqb_eq in E; llia | reflexivity].
    - (* [comment removed for export] *) cbn. symmetry. apply last_app1.
    - (* [comment removed for export] *) cbn. rewrite hd_app1. rewrite wf_ahead0. destruct (a_areas A); reflexivity.
    - (* [comment removed for export] *) intros x mt Hx Hr. destruct (aa_meta_inv x mt Hx) as [H | (k & Hk & -> & ->)]; [exact (wf_avail_zero0 x mt H Hr)|].
      cbn. repeat split; reflexivity.
    - (* [comment removed for export] *) intros x mt Hx Hr. pose proof (aa_free_inv x mt Hx Hr) as H. exact (wf_free_zero0 x mt H Hr).
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). split.
      + intros (mt & Hx & Hr). exists mt. split; [apply aa_meta_old; exact Hx | exact Hr].
      + intros (mt & Hx & Hr). exists mt. split; [exact (aa_free_inv x mt Hx Hr) | exact Hr].
    - (* [comment removed for export] *) apply dll_keptA. exact wf_fl_dll0.
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_grp0 x mt aib sl (aa_group_inv x mt aib sl Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl i off n Hx Hr. exact (wf_live0 x mt aib sl i off n (aa_group_inv x mt aib sl Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl i ch Hx Hr Hi Hi0.
      destruct (wf_nested0 x mt aib sl i ch (aa_group_inv x mt aib sl Hx Hr) Hr Hi Hi0) as (mc & aibc & slc & Hmc & R).
      exists mc, aibc, slc. split; [apply aa_meta_old; exact Hmc | exact R].
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hml.
      destruct (wf_nested_parent0 ch mc aibc slc (aa_group_inv ch mc aibc slc Hch Hrc) Hrc Hml) as (x & mtx & aibx & slx & j & Hx & R).
      exists x, mtx, aibx, slx, j. split; [apply aa_meta_old; exact Hx | exact R].
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr.
      destruct (wf_grp_root0 x mt aib sl (aa_group_inv x mt aib sl Hx Hr) Hr) as (mr & mtr & aibr & slr & Hmr & R).
      exists mr, mtr, aibr, slr. split; [apply aa_meta_old; exact Hmr | exact R].
    - (* [comment removed for export] *) intros x mt aib sl x' mt' aib' sl' Hx Hr Hx' Hr' Hne.
      exact (wf_laminar0 x mt aib sl x' mt' aib' sl' (aa_group_inv _ _ _ _ Hx Hr) Hr (aa_group_inv _ _ _ _ Hx' Hr') Hr' Hne).
    - (* [comment removed for export] *) intros sc Hsc. apply dll_keptA. exact (wf_act_dll0 sc Hsc).
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mt & aib & sl & Hx & R). exists mt, aib, sl. split; [apply aa_meta_old; exact Hx | exact R].
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_unlinked0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros sc x mt Hin Hne Hx.
      destruct (wf_act_mem0 sc x Hin) as (mt0 & aib & sl & Hx0 & Hr0 & _).
      rewrite (aa_meta_old x mt0 Hx0) in Hx. injection Hx as <-. exact (wf_act_nonhead0 sc x mt0 Hin Hne Hx0).
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_act630 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros pg x mt aib sl Hpg Hx Hr Hml. apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]].
      + exact (wf_disj_area_grp0 pg x mt aib sl Hpg (aa_group_inv _ _ _ _ Hx Hr) Hr Hml).
      + exact (Hdisj_grp x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr Hml).
    - (* [comment removed for export] *) intros x mt aib sl x' mt' aib' sl' Hx Hr Hml Hx' Hr' Hml' Hne.
      exact (wf_disj_grp_grp0 x mt aib sl x' mt' aib' sl' (aa_group_inv _ _ _ _ Hx Hr) Hr Hml (aa_group_inv _ _ _ _ Hx' Hr') Hr' Hml' Hne).
    - (* [comment removed for export] *) intros x mt aib sl x' mt' aib' sl' Hx Hr Hx' Hr'.
      exact (wf_grp_mem_inj0 x mt aib sl x' mt' aib' sl' (aa_group_inv _ _ _ _ Hx Hr) Hr (aa_group_inv _ _ _ _ Hx' Hr') Hr').
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map0 q n). unfold is_live. cbn [a_meta aaA]. split.
      + intros (x & mt & aib & sl & i & off & Hx & R). exists x, mt, aib, sl, i, off. split; [apply aa_meta_old; exact Hx | exact R].
      + intros (x & mt & aib & sl & i & off & Hx & Hr & R). exists x, mt, aib, sl, i, off. split; [exact (aa_group_inv _ _ _ _ Hx Hr) | split; [exact Hr | exact R]].
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_span0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_single0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl j Hx Hr. exact (wf_inactive0 x mt aib sl j (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros sc x mt aib sl x' mt' aib' sl' Hin Hin' Hx Hr Hx' Hr'.
      exact (wf_partial0 sc x mt aib sl x' mt' aib' sl' Hin Hin' (aa_group_inv _ _ _ _ Hx Hr) Hr (aa_group_inv _ _ _ _ Hx' Hr') Hr').
    - (* [comment removed for export] *) intros k. destruct k; cbn; try apply wf_ctx_nonneg0; try llia.
      + unfold meta_addr. llia.
      + destruct (a_areas A); [llia | apply wf_ctx_nonneg0].
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_nested_small0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_reusable0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (wf_cover0 pa pm paib psl j ch x mtx aibx slx (aa_group_inv _ _ _ _ Hpa Hpr) Hpr Hj0 Hj (aa_group_inv _ _ _ _ Hx Hrx) Hrx Hlo Hhi)
        as (mtc & aibc & slc & Hch & R).
      exists mtc, aibc, slc. split; [apply aa_meta_old; exact Hch | exact R].
    - (* [comment removed for export] *) cbn. intros E. exfalso. destruct (a_areas A); discriminate E.
    - (* [comment removed for export] *) cbn. intros E. exfalso. exact (Hbrk E).
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_stride200 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros pg pg' Hpg Hpg'. apply in_app_or in Hpg'. destruct Hpg' as [Hpg' | [<- | []]].
      + exact (wf_disj_page_area0 pg pg' Hpg Hpg').
      + destruct (Hdisj_page pg Hpg); llia.
    - (* [comment removed for export] *) intros pg x mt aib sl Hpg Hx Hr. exact (wf_disj_page_grp0 pg x mt aib sl Hpg (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) intros x mt aib sl Hx Hr. exact (wf_partial_sc0 x mt aib sl (aa_group_inv _ _ _ _ Hx Hr) Hr).
    - (* [comment removed for export] *) rewrite length_app. cbn [length aa_ctx]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
      destruct (a_ctx A KAac =? 0); destruct (aac' =? 0); llia.
    - (* [comment removed for export] *) destruct wf_shift_acct0 as (Q1 & Q2 & Q3).
      rewrite length_app. cbn [length aa_ctx]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat].
      repeat split; llia.
  Qed.
  (* [comment removed for export] *)
  Lemma has_aaA_inv : forall f, has aaA f ->
    (exists k, cvalid k /\ f = FCT (caddr k) (clen k) (aa_ctx k)) \/
    f = FCT p 8 (a_ctx A KSecret) \/
    (exists k fl, 0 <= k < 101 /\ f = FCT (meta_addr p k + moff fl) (mlen fl) 0) \/
    (has A f /\ ~ has_ctx A f).
  Proof.
    assert (NC : forall f, has_area A f \/ has_meta A f \/ has_grp A f -> ~ has_ctx A f).
    { intros f Hf (k & Hk & E). pose proof (nonctx_fact_avoids_ctx A HW f Hf k Hk) as X.
      pose proof (ctx_slot_range k Hk) as (C1 & C2 & C3). rewrite E in X. cbn in X. llia. }
    intros f [Hc | [Har | [Hm | Hg]]].
    - left. destruct Hc as (k & Hk & ->). exists k. auto.
    - destruct Har as (pg & Hpg & ->). cbn [a_areas a_ctx aaA] in *. apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]].
      + right; right; right. assert (Ha : has_area A (FCT pg 8 (a_ctx A KSecret))) by (exists pg; auto).
        split; [right; left; exact Ha | apply NC; left; exact Ha].
      + right; left. reflexivity.
    - destruct Hm as (ma & mt & fl & Hma & ->). cbn [a_meta aaA] in Hma.
      destruct (aa_meta_inv ma mt Hma) as [Hold | (k & Hk & -> & ->)].
      + right; right; right. assert (Hm : has_meta A (FCT (ma + moff fl) (mlen fl) (mt_f mt fl))) by (exists ma, mt, fl; auto).
        split; [right; right; left; exact Hm | apply NC; right; left; exact Hm].
      + right; right; left. exists k, fl. split; [exact Hk|]. cbn. rewrite mt_f_mzero. reflexivity.
    - right; right; right. destruct Hg as (ma & mt & aib & sl & Hma & Hr & Hin). cbn [a_meta aaA] in Hma.
      pose proof (aa_group_inv ma mt aib sl Hma Hr) as Hold.
      assert (Hg : has_grp A f) by (exists ma, mt, aib, sl; auto).
      split; [right; right; right; exact Hg | apply NC; right; right; exact Hg].
  Qed.

  Lemma has_aaA_ctx : forall k, cvalid k -> has aaA (FCT (caddr k) (clen k) (aa_ctx k)).
  Proof. intros k Hk. left. exists k. auto. Qed.

  Lemma has_aaA_kept : forall f, has A f -> ~ has_ctx A f -> has aaA f.
  Proof.
    intros f [Hc | [Har | [Hm | Hg]]] Hn; [exfalso; exact (Hn Hc) | | |].
    - right; left. destruct Har as (pg & Hpg & ->). exists pg. cbn [a_areas a_ctx aaA]. split; [apply in_or_app; left; exact Hpg | reflexivity].
    - right; right; left. destruct Hm as (ma & mt & fl & Hma & ->). exists ma, mt, fl. split; [apply aa_meta_old; exact Hma | reflexivity].
    - right; right; right. destruct Hg as (ma & mt & aib & sl & Hma & Hr & Hin). exists ma, mt, aib, sl.
      split; [apply aa_meta_old; exact Hma | auto].
  Qed.

  Lemma dom_aaA : forall x, dom aaA x <-> dom A x \/ p <= x < p + 4096.
  Proof.
    intros x. unfold dom. cbn [a_areas a_meta a_pages aaA]. split.
    - intros [(pg & Hpg & Hx) | [(ma & mt & aib & sl & Hma & Hr & Hml & Hx) | Hp]].
      + apply in_app_or in Hpg. destruct Hpg as [Hpg | [<- | []]]; [left; left; exists pg; auto | right; exact Hx].
      + left; right; left. exists ma, mt, aib, sl. split; [exact (aa_group_inv ma mt aib sl Hma Hr) | auto].
      + left; right; right. exact Hp.
    - intros [[(pg & Hpg & Hx) | [(ma & mt & aib & sl & Hma & Hr & Hml & Hx) | Hp]] | Hx].
      + left. exists pg. split; [apply in_or_app; left; exact Hpg | exact Hx].
      + right; left. exists ma, mt, aib, sl. split; [apply aa_meta_old; exact Hma | auto].
      + right; right. exact Hp.
      + left. exists p. split; [apply in_or_app; right; left; reflexivity | exact Hx].
  Qed.
End AddArea.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KillMeta.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (m : Z) (mt : meta_rec).
  Hypothesis Hm : a_meta A m = Some mt.
  Hypothesis Hr : mt_role mt = RAvail \/ mt_role mt = RDead.
  Hypothesis Hnot_am : forall k, a_ctx A KAmc > 0 -> 101 - a_ctx A KAmc <= k < 101 -> m <> meta_addr (last (a_areas A) 0) k.

  Definition kmA : astate := ameta_upd A m (MT (mt_f mt) RDead).

  Lemma km_meta : forall x, a_meta kmA x = if Z.eq_dec x m then Some (MT (mt_f mt) RDead) else a_meta A x.
  Proof. intros x. reflexivity. Qed.

  Lemma km_meta_same : a_meta kmA m = Some (MT (mt_f mt) RDead).
  Proof. rewrite km_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction]. Qed.

  Lemma km_meta_inv : forall x mtx, a_meta kmA x = Some mtx ->
    (x = m /\ mtx = MT (mt_f mt) RDead) \/ (x <> m /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. rewrite km_meta in Hx. destruct (Z.eq_dec x m) as [-> | Hne]; [left; injection Hx as <-; auto | right; auto].
  Qed.

  Lemma km_group_inv : forall x mtx aib sl, a_meta kmA x = Some mtx -> mt_role mtx = RGroup aib sl -> a_meta A x = Some mtx /\ x <> m.
  Proof.
    intros x mtx aib sl Hx Hrx. destruct (km_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | auto].
  Qed.

  Lemma km_old : forall x mtx, a_meta A x = Some mtx -> x <> m -> a_meta kmA x = Some mtx.
  Proof. intros x mtx Hx Hne. rewrite km_meta. destruct (Z.eq_dec x m); [contradiction | exact Hx]. Qed.

  Lemma km_old_grp : forall x mtx aib sl, a_meta A x = Some mtx -> mt_role mtx = RGroup aib sl -> a_meta kmA x = Some mtx.
  Proof.
    intros x mtx aib sl Hx Hrx. apply km_old; [exact Hx|]. intros ->. rewrite Hm in Hx. injection Hx as ->.
    destruct Hr as [E | E]; rewrite E in Hrx; discriminate Hrx.
  Qed.

  Lemma km_not_in_fl : ~ In m (a_freelist A).
  Proof.
    intros Hin. destruct (proj1 (wf_fl_mem A HW m) Hin) as (mt0 & H0 & Hr0). rewrite Hm in H0. injection H0 as <-.
    destruct Hr as [E | E]; rewrite E in Hr0; discriminate Hr0.
  Qed.

  Lemma km_not_in_act : forall sc, ~ In m (a_active A sc).
  Proof.
    intros sc Hin. destruct (wf_act_mem A HW sc m Hin) as (mt0 & aib & sl & H0 & Hr0 & _). rewrite Hm in H0. injection H0 as <-.
    destruct Hr as [E | E]; rewrite E in Hr0; discriminate Hr0.
  Qed.

  Lemma dll_keptK : forall l, (~ In m l) -> dll A l -> dll kmA l.
  Proof.
    intros l Hn Hd k x Hk. destruct (Hd k x Hk) as (mtx & Hx & R). exists mtx. split; [| exact R].
    apply km_old; [exact Hx|]. intros ->. apply Hn. eapply nth_error_In. exact Hk.
  Qed.

  Theorem WF_kill_meta : WF kmA.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps kmA ameta_upd set_meta]; try assumption.
    - (* [comment removed for export] *) intros x. rewrite <- wf_meta_dom0. rewrite km_meta.
      destruct (Z.eq_dec x m) as [-> | Hne]; [rewrite Hm; split; intros _; discriminate | tauto].
    - (* [comment removed for export] *) intros Hc. destruct (wf_am0 Hc) as (pg & H1 & H2 & H3 & H4). exists pg. repeat split; auto.
      intros k Hk. destruct (H4 k Hk) as (mtk & Hmk & Hrk). exists mtk. split; [| exact Hrk].
      apply km_old; [exact Hmk|]. intros E. apply (Hnot_am k Hc Hk). rewrite <- H2. symmetry. exact E.
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (km_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x mtx Hx Hrx. destruct (km_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) intros x. rewrite (wf_fl_mem0 x). split.
      + intros (mtx & Hx & Hrx). exists mtx. split; [| exact Hrx]. apply km_old; [exact Hx|].
        intros ->. rewrite Hm in Hx. injection Hx as ->. destruct Hr as [E | E]; rewrite E in Hrx; discriminate Hrx.
      + intros (mtx & Hx & Hrx). destruct (km_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)]; [cbn in Hrx; discriminate Hrx | eauto].
    - (* [comment removed for export] *) apply dll_keptK; [apply km_not_in_fl | exact wf_fl_dll0].
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv x mtx aib sl Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl i off n Hx Hrx. destruct (km_group_inv x mtx aib sl Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl i ch Hx Hrx Hi Hi0. destruct (km_group_inv x mtx aib sl Hx Hrx) as [H _].
      destruct (wf_nested0 x mtx aib sl i ch H Hrx Hi Hi0) as (mc & aibc & slc & Hmc & Hrc & R).
      exists mc, aibc, slc. split; [exact (km_old_grp _ _ _ _ Hmc Hrc) | split; [exact Hrc | exact R]].
    - (* [comment removed for export] *) intros ch mc aibc slc Hch Hrc Hml. destruct (km_group_inv ch mc aibc slc Hch Hrc) as [H _].
      destruct (wf_nested_parent0 ch mc aibc slc H Hrc Hml) as (x & mtx & aibx & slx & j & Hx & Hrx & R).
      exists x, mtx, aibx, slx, j. split; [exact (km_old_grp _ _ _ _ Hx Hrx) | split; [exact Hrx | exact R]].
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv x mtx aib sl Hx Hrx) as [H _].
      destruct (wf_grp_root0 x mtx aib sl H Hrx) as (mr & mtr & aibr & slr & Hmr & Hrr & R).
      exists mr, mtr, aibr, slr. split; [exact (km_old_grp _ _ _ _ Hmr Hrr) | split; [exact Hrr | exact R]].
    - (* [comment removed for export] *) intros x mtx aib sl x' mtx' aib' sl' Hx Hrx Hx' Hrx' Hne.
      destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (km_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros sc Hsc. apply dll_keptK; [apply km_not_in_act | exact (wf_act_dll0 sc Hsc)].
    - (* [comment removed for export] *) intros sc x Hin. destruct (wf_act_mem0 sc x Hin) as (mtx & aib & sl & Hx & Hrx & R).
      exists mtx, aib, sl. split; [exact (km_old_grp _ _ _ _ Hx Hrx) | auto].
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx Hin Hne Hx. destruct (wf_act_mem0 sc x Hin) as (mt0 & aib & sl & Hx0 & Hr0 & _).
      rewrite (km_old_grp _ _ _ _ Hx0 Hr0) in Hx. injection Hx as <-. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aib sl Hpg Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl x' mtx' aib' sl' Hx Hrx Hml Hx' Hrx'.
      destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (km_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl x' mtx' aib' sl' Hx Hrx Hx' Hrx'.
      destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (km_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros q n. rewrite (wf_live_map0 q n). unfold is_live. cbn [a_meta kmA ameta_upd set_meta]. split.
      + intros (x & mtx & aib & sl & i & off & Hx & Hrx & R). exists x, mtx, aib, sl, i, off.
        split; [exact (km_old_grp _ _ _ _ Hx Hrx) | split; [exact Hrx | exact R]].
      + intros (x & mtx & aib & sl & i & off & Hx & Hrx & R). destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _].
        exists x, mtx, aib, sl, i, off. auto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl j Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros sc x mtx aib sl x' mtx' aib' sl' Hin Hin' Hx Hrx Hx' Hrx'.
      destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. destruct (km_group_inv _ _ _ _ Hx' Hrx') as [H' _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pa pm paib psl j ch x mtx aibx slx Hpa Hpr Hj0 Hj Hx Hrx Hlo Hhi.
      destruct (km_group_inv _ _ _ _ Hpa Hpr) as [Hpa0 _]. destruct (km_group_inv _ _ _ _ Hx Hrx) as [Hx0 _].
      destruct (wf_cover0 pa pm paib psl j ch x mtx aibx slx Hpa0 Hpr Hj0 Hj Hx0 Hrx Hlo Hhi) as (mtc & aibc & slc & Hch & Hrc & R).
      exists mtc, aibc, slc. split; [exact (km_old_grp _ _ _ _ Hch Hrc) | split; [exact Hrc | exact R]].
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros pg x mtx aib sl Hpg Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - (* [comment removed for export] *) intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
  Qed.

  Lemma has_kmA : forall f, has kmA f <-> has A f.
  Proof.
    intros f.
    assert (M : has_meta kmA f <-> has_meta A f).
    { split.
      - intros (x & mtx & fl & Hx & ->). destruct (km_meta_inv x mtx Hx) as [(-> & ->) | (Hne & H)].
        + exists m, mt, fl. auto.
        + exists x, mtx, fl. auto.
      - intros (x & mtx & fl & Hx & ->). destruct (Z.eq_dec x m) as [-> | Hne].
        + rewrite Hm in Hx. injection Hx as <-. exists m, (MT (mt_f mt) RDead), fl. split; [| reflexivity].
          rewrite km_meta. destruct (Z.eq_dec m m); [reflexivity | contradiction].
        + exists x, mtx, fl. split; [apply km_old; assumption | reflexivity]. }
    assert (G : has_grp kmA f <-> has_grp A f).
    { split.
      - intros (x & mtx & aib & sl & Hx & Hrx & R). destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. exists x, mtx, aib, sl. auto.
      - intros (x & mtx & aib & sl & Hx & Hrx & R). exists x, mtx, aib, sl. split; [exact (km_old_grp _ _ _ _ Hx Hrx) | auto]. }
    assert (C : has_ctx kmA f <-> has_ctx A f) by reflexivity.
    assert (Ar : has_area kmA f <-> has_area A f) by reflexivity.
    unfold has. tauto.
  Qed.

  Lemma dom_kmA : forall x, dom kmA x <-> dom A x.
  Proof.
    intros x. unfold dom. cbn [a_areas a_meta a_pages kmA ameta_upd set_meta]. split.
    - intros [Ha | [(y & mty & aib & sl & Hy & Hry & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      destruct (km_group_inv _ _ _ _ Hy Hry) as [H _]. exists y, mty, aib, sl. auto.
    - intros [Ha | [(y & mty & aib & sl & Hy & Hry & R) | Hp]]; [left; exact Ha | right; left | right; right; exact Hp].
      exists y, mty, aib, sl. split; [exact (km_old_grp _ _ _ _ Hy Hry) | auto].
  Qed.

  Lemma VMok_kmA : forall h, VMok A h -> VMok kmA h.
  Proof.
    intros h [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vlim]. constructor; cbn [a_ctx a_areas a_pages a_mblocks a_xmaps kmA ameta_upd set_meta]; auto.
    - intros x mtx aib sl Hx Hrx. destruct (km_group_inv _ _ _ _ Hx Hrx) as [H _]. eauto.
    - intros b sz Hin.
      destruct (Vall b sz Hin) as [(x & mtx & aibx & slx & Hx & Hrx & R) | [Hbr | Hbl]]; [left | right; left; exact Hbr | right; right; exact Hbl].
      exists x, mtx, aibx, slx. split; [exact (km_old_grp _ _ _ _ Hx Hrx) | split; [exact Hrx | exact R]].
  Qed.
End KillMeta.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AddPage.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variable pg : Z.
  Hypothesis Hal : page_aligned pg.
  Hypothesis Hheap : heap_range pg (pg + 4096).
  Hypothesis Hareas : a_areas A = [].
  Hypothesis Hinit : a_ctx A KInit = 1.
  Hypothesis Hbrk : a_ctx A KBrk <> 0.

  Definition apA : astate :=
    AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (pg :: a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) (a_xmaps A).

  Lemma ap_nometa : forall x, a_meta A x = None.
  Proof.
    intros x. destruct (a_meta A x) eqn:E; [| reflexivity]. exfalso.
    destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite E; discriminate)) as (p0 & k & Hp0 & _). rewrite Hareas in Hp0. destruct Hp0.
  Qed.

  Theorem WF_add_page : WF apA.
  Proof.
    pose proof HW as W. destruct HW as [wf_areas_nodup0 wf_areas_al0 wf_meta_dom0 wf_init0 wf_uninit0 wf_amc0 wf_am0 wf_atail0 wf_ahead0 wf_avail_zero0 wf_free_zero0 wf_fl_nodup0 wf_fl_head0 wf_fl_mem0 wf_fl_dll0 wf_grp0 wf_live0 wf_nested0 wf_nested_parent0 wf_grp_root0 wf_laminar0 wf_act_head0 wf_act_nodup0 wf_act_dll0 wf_act_mem0 wf_unlinked0 wf_act_nonhead0 wf_act630 wf_disj_area_grp0 wf_disj_grp_grp0 wf_grp_mem_inj0 wf_live_map0 wf_span0 wf_single0 wf_inactive0 wf_partial0 wf_ctx_nonneg0 wf_nested_small0 wf_reusable0 wf_cover0 wf_shift0 wf_noarea_shift0 wf_brk00 wf_stride200 wf_pages_al0 wf_disj_page_area0 wf_disj_page_grp0 wf_partial_sc0 wf_mblocks_len0 wf_mblocks_sz0 wf_shift_mblocks0 wf_shift_acct0].
    constructor; cbn [a_ctx a_areas a_meta a_freelist a_active a_pages a_brk_lo a_live a_mblocks a_xmaps apA]; try assumption.
    - (* [comment removed for export] *) intros H0. exfalso. rewrite Hinit in H0. discriminate H0.
    - (* [comment removed for export] *) intros H0. exfalso. exact (Hbrk H0).
    - (* [comment removed for export] *) intros p0 [<- | Hp0]; [split; [exact Hal | exact Hheap] | exact (wf_pages_al0 p0 Hp0)].
    - (* [comment removed for export] *) intros p0 p1 Hp0 Hp1. rewrite Hareas in Hp1. destruct Hp1.
    - (* [comment removed for export] *) intros p0 x mt aib sl Hp0 Hx. rewrite ap_nometa in Hx. discriminate Hx.
  Qed.

  Lemma has_apA : forall f, has apA f <-> has A f.
  Proof. intros f. reflexivity. Qed.

  Lemma dom_apA : forall x, dom apA x <-> dom A x \/ pg <= x < pg + 4096.
  Proof.
    intros x. unfold dom. cbn [a_areas a_meta a_pages apA]. split.
    - intros [Ha | [Hg | (p0 & [<- | Hp0] & Hx)]]; [left; left; exact Ha | left; right; left; exact Hg | right; exact Hx | left; right; right; exists p0; auto].
    - intros [[Ha | [Hg | (p0 & Hp0 & Hx)]] | Hx]; [left; exact Ha | right; left; exact Hg | right; right; exists p0; split; [right; exact Hp0 | exact Hx] | right; right; exists pg].
      split; [left; reflexivity | exact Hx].
  Qed.
End AddPage.

End WithLayout.
