(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhQueue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section FreeMeta.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (m : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HU : metaU st m.
  Hypothesis HNG : ~ is_group st m.
  Hypothesis Hunl : ~ listed st m.
  Hypothesis HNF : ~ fresh st m.
  Hypothesis Hlimbo : In m (s_limbo st).
  #[local] Notation l := (s_flist st).
  Definition q_nil : bool := is_nilb (s_flist st).
  #[local] Notation hd := (head_of l).
  #[local] Notation tl := (znth l (zlen l - 1)).

  Definition q_next (x : Z) : Z :=
    if x =? m then (if q_nil then m else hd)
    else if (negb q_nil && (x =? tl))%bool then m else mr_next (s_meta st x).
  Definition q_prev (x : Z) : Z :=
    if x =? m then (if q_nil then m else tl)
    else if (negb q_nil && (x =? hd))%bool then m else mr_prev (s_meta st x).
  Definition q_meta (x : Z) : meta_rec :=
    if x =? m then MR (q_prev m) (q_next m) 0 0 0 0 else mr_set_links (s_meta st x) (q_prev x) (q_next x).
  Definition l' : list Z := l ++ [m].
  Definition st' : mst :=
    MST (cx_set_fhead (s_ctx st) (head_of l'))
        (s_areas st) q_meta l' (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (zremove m (s_limbo st)).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma q_nil_iff : q_nil = true <-> l = []. Proof using. unfold q_nil. apply is_nilb_true. Qed.
  Lemma q_nnil_iff : q_nil = false <-> l <> []. Proof using. unfold q_nil. apply is_nilb_false. Qed.
  Lemma l_dll : dll st l. Proof using HWF L RN. exact (wl_fdll st (WF_lists st L HWF)). Qed.
  Lemma l_nodup : NoDup l. Proof using HWF L RN. exact (wl_fnodup st (WF_lists st L HWF)). Qed.
  Lemma l_mem : forall x, In x l -> metaU st x /\ ~ is_group st x /\ ~ fresh st x /\ listed st x /\ x <> m.
  Proof using Hunl HWF L RN.
    intros x Hin. destruct (wl_fU st (WF_lists st L HWF) x Hin) as (U & NG & NF & _).
    repeat split; try assumption. { left. exact Hin. } intros ->. apply Hunl. left. exact Hin.
  Qed.
  Lemma l_notin : ~ In m l. Proof using Hunl. intros Hin. apply Hunl. left. exact Hin. Qed.
  Lemma hd_in : q_nil = false -> In hd l. Proof using. intros H. apply head_of_In. apply q_nnil_iff. exact H. Qed.
  Lemma tl_in : q_nil = false -> In tl l. Proof using. intros H. apply last_In. apply q_nnil_iff. exact H. Qed.
  Lemma hd_znth : q_nil = false -> hd = znth l 0. Proof using. intros H. apply head_of_znth. apply q_nnil_iff. exact H. Qed.
  Lemma l_len : q_nil = false -> 0 < zlen l. Proof using. intros H. apply zlen_pos. apply q_nnil_iff. exact H. Qed.
  Lemma m_pos : HEAPLO + 24 <= m. Proof using HU HWF L st RN. destruct (metaU_rng st L HWF m HU) as (A & _). exact A. Qed.
  Lemma hd_facts : q_nil = false -> metaU st hd /\ ~ is_group st hd /\ ~ fresh st hd /\ listed st hd /\ hd <> m.
  Proof using Hunl HWF L RN. intros H. exact (l_mem hd (hd_in H)). Qed.
  Lemma tl_facts : q_nil = false -> metaU st tl /\ ~ is_group st tl /\ ~ fresh st tl /\ listed st tl /\ tl <> m.
  Proof using Hunl HWF L RN. intros H. exact (l_mem tl (tl_in H)). Qed.
  Lemma grp_not_m : forall x, is_group st x -> x <> m. Proof using HNG. intros x Hx ->. exact (HNG Hx). Qed.
  Lemma grp_not_tl : forall x, is_group st x -> q_nil = false -> x <> tl.
  Proof using Hunl HWF m L RN. intros x Hx Hn ->. exact (proj1 (proj2 (tl_facts Hn)) Hx). Qed.
  Lemma grp_not_hd : forall x, is_group st x -> q_nil = false -> x <> hd.
  Proof using Hunl HWF m L RN. intros x Hx Hn ->. exact (proj1 (proj2 (hd_facts Hn)) Hx). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = l'. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_slot : s_slot st' = s_slot st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = s_regions st. Proof using. reflexivity. Qed.

  Lemma e_limbo : s_limbo st' = zremove m (s_limbo st). Proof using. reflexivity. Qed.

  Lemma e_next : forall x, mr_next (s_meta st' x) = q_next x.
  Proof using. intros x. cbn. unfold q_meta. destruct (Z.eqb_spec x m); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = q_prev x.
  Proof using. intros x. cbn. unfold q_meta. destruct (Z.eqb_spec x m); [subst; reflexivity | reflexivity]. Qed.
  Lemma e_meta_other : forall x, x <> m -> s_meta st' x = mr_set_links (s_meta st x) (q_prev x) (q_next x).
  Proof using. intros x Hx. cbn. unfold q_meta. destruct (Z.eqb_spec x m); [contradiction | reflexivity]. Qed.
  Lemma e_meta_m : s_meta st' m = MR (q_prev m) (q_next m) 0 0 0 0.
  Proof using. cbn. unfold q_meta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_mem : forall x, x <> m -> mr_mem (s_meta st' x) = mr_mem (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_avail : forall x, x <> m -> mr_avail (s_meta st' x) = mr_avail (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_freed : forall x, x <> m -> mr_freed (s_meta st' x) = mr_freed (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_Wr : forall x, x <> m -> mr_W (s_meta st' x) = mr_W (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_gW : forall x, is_group st x -> g_W st' x = g_W st x. Proof using HNG. intros; unfold g_W; apply e_Wr; apply grp_not_m; assumption. Qed.
  Lemma e_gmem : forall x, is_group st x -> g_mem st' x = g_mem st x. Proof using HNG. intros; unfold g_mem; apply e_mem; apply grp_not_m; assumption. Qed.
  Lemma e_glast : forall x, is_group st x -> g_lastidx st' x = g_lastidx st x. Proof using HNG. intros; unfold g_lastidx; rewrite e_gW by assumption; reflexivity. Qed.
  Lemma e_gcnt : forall x, is_group st x -> g_cnt st' x = g_cnt st x. Proof using HNG. intros; unfold g_cnt; rewrite e_glast by assumption; reflexivity. Qed.
  Lemma e_gsc : forall x, is_group st x -> g_sc st' x = g_sc st x. Proof using HNG. intros; unfold g_sc; rewrite e_gW by assumption; reflexivity. Qed.
  Lemma e_gml : forall x, is_group st x -> g_maplen st' x = g_maplen st x. Proof using HNG. intros; unfold g_maplen; rewrite e_gW by assumption; reflexivity. Qed.
  Lemma e_gstride : forall x, is_group st x -> g_stride st' x = g_stride st x.
  Proof using HNG. intros; unfold g_stride; rewrite e_gml, e_glast, e_gsc by assumption; reflexivity. Qed.
  Lemma e_gss : forall x k, is_group st x -> g_slot_start st' x k = g_slot_start st x k.
  Proof using HNG. intros; unfold g_slot_start; rewrite e_gmem, e_gstride by assumption; reflexivity. Qed.
  Lemma e_ctx_fhead : c_free_head (s_ctx st') = head_of l'. Proof using. reflexivity. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using. intros; unfold fresh; rewrite e_areas; cbn; tauto. Qed.

  Lemma SLf : same_layout st st'.
  Proof using HNG. constructor; intros; try reflexivity; [apply slot_sim_refl | apply e_mem | apply e_Wr]; apply grp_not_m; assumption. Qed.

  Lemma head_l' : head_of l' = if q_nil then m else hd.
  Proof using.
    unfold l'. case_bool q_nil E.
    - apply q_nil_iff in E. rewrite E. reflexivity.
    - apply head_of_app_nonnil. apply q_nnil_iff. exact E.
  Qed.
  Lemma in_l' : forall x, In x l' <-> In x l \/ x = m.
  Proof using.
    intros x. unfold l'. rewrite in_app_iff. cbn. split.
    - intros [H|[H|[]]]; [left; exact H | right; symmetry; exact H].
    - intros [H|H]; [left; exact H | right; left; symmetry; exact H].
  Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x \/ x = m.
  Proof using. intros x. unfold in_flist. rewrite e_flist. apply in_l'. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x \/ x = m.
  Proof using. intros x. unfold listed. rewrite e_in_flist, e_in_alist. tauto. Qed.
  Lemma e_listed_other : forall x, x <> m -> (listed st' x <-> listed st x).
  Proof using. intros x Hx. rewrite e_listed. split; [intros [H| ->]; [exact H | congruence] | tauto]. Qed.

  Lemma q_next_other : forall x, x <> m -> (q_nil = false -> x <> tl) -> q_next x = mr_next (s_meta st x).
  Proof using.
    intros x H1 H2. unfold q_next. destruct (Z.eqb_spec x m); [contradiction|].
    case_bool q_nil E; cbn; [reflexivity|]. destruct (Z.eqb_spec x tl); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma q_prev_other : forall x, x <> m -> (q_nil = false -> x <> hd) -> q_prev x = mr_prev (s_meta st x).
  Proof using.
    intros x H1 H2. unfold q_prev. destruct (Z.eqb_spec x m); [contradiction|].
    case_bool q_nil E; cbn; [reflexivity|]. destruct (Z.eqb_spec x hd); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma q_meta_other : forall x, x <> m -> (q_nil = false -> x <> tl) -> (q_nil = false -> x <> hd) -> s_meta st' x = s_meta st x.
  Proof using.
    intros x H1 H2 H3. rewrite e_meta_other by exact H1. rewrite q_next_other, q_prev_other by assumption. apply mr_set_links_id.
  Qed.
  Lemma q_meta_group : forall x, is_group st x -> s_meta st' x = s_meta st x.
  Proof using Hunl HNG HWF L RN.
    intros x Hx. apply q_meta_other; [apply grp_not_m; exact Hx | apply grp_not_tl; exact Hx | apply grp_not_hd; exact Hx].
  Qed.
  Lemma q_meta_offlist : forall x, x <> m -> ~ In x l -> s_meta st' x = s_meta st x.
  Proof using.
    intros x H1 H2. apply q_meta_other; [exact H1 | intros Hn ->; exact (H2 (tl_in Hn)) | intros Hn ->; exact (H2 (hd_in Hn))].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[head_of l' Z.pow NSLOTS AREAMAX HEAPLO CEIL]; try assumption. reflexivity.
  Qed.

  Lemma t_dll_l' : dll st' l'.
  Proof using Hunl HWF L RN.
    apply (proj2 (dll_dllf st' l')).
    change (dllf (fun x => mr_next (s_meta st' x)) (fun x => mr_prev (s_meta st' x)) l') with
      (dllf (fun x => mr_next (s_meta st' x)) (fun x => mr_prev (s_meta st' x)) l').
    assert (EQ : forall l0, dllf q_next q_prev l0 -> dllf (fun x => mr_next (s_meta st' x)) (fun x => mr_prev (s_meta st' x)) l0).
    { intros l0 D k Hk. rewrite e_next, e_prev. exact (D k Hk). }
    apply EQ. unfold l'. case_bool q_nil E.
    - pose proof (proj1 q_nil_iff E) as El. rewrite El. cbn [app]. apply dllf_single.
      + unfold q_next. rewrite Z.eqb_refl, E. reflexivity.
      + unfold q_prev. rewrite Z.eqb_refl, E. reflexivity.
    - pose proof (l_len E) as Hn. pose proof (proj1 (NoDup_ListNoDup _) l_nodup) as ND. pose proof (proj1 (dll_dllf st l) l_dll) as D.
      apply (dllf_app_tail _ _ q_next q_prev l m D Hn ND l_notin).
      + intros k Hk. unfold q_next.
        assert (znth l k <> m) by (intros Em; apply l_notin; rewrite <- Em; apply znth_In; lia).
        assert (znth l k <> tl) by (intros Et; apply (NoDup_znth_inj l k (zlen l - 1) ND) in Et; lia).
        destruct (Z.eqb_spec (znth l k) m); [contradiction|]. rewrite E. cbn. destruct (Z.eqb_spec (znth l k) tl); [contradiction|reflexivity].
      + unfold q_next. destruct (Z.eqb_spec tl m) as [Em|]; [exfalso; exact (proj2 (proj2 (proj2 (proj2 (tl_facts E)))) Em)|].
        rewrite E, Z.eqb_refl. reflexivity.
      + unfold q_next. rewrite Z.eqb_refl, E. exact (hd_znth E).
      + intros k Hk. unfold q_prev.
        assert (znth l k <> m) by (intros Em; apply l_notin; rewrite <- Em; apply znth_In; lia).
        assert (znth l k <> hd) by (intros Et; rewrite (hd_znth E) in Et; apply (NoDup_znth_inj l k 0 ND) in Et; lia).
        destruct (Z.eqb_spec (znth l k) m); [contradiction|]. rewrite E. cbn. destruct (Z.eqb_spec (znth l k) hd); [contradiction|reflexivity].
      + unfold q_prev. rewrite <- (hd_znth E). destruct (Z.eqb_spec hd m) as [Em|]; [exfalso; exact (proj2 (proj2 (proj2 (proj2 (hd_facts E)))) Em)|].
        rewrite E, Z.eqb_refl. reflexivity.
      + unfold q_prev. rewrite Z.eqb_refl, E. reflexivity.
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using HNF Hunl HNG HU HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist.
    - exact t_dll_l'.
    - unfold l'. apply (proj2 (NoDup_ListNoDup _)). apply List.NoDup_app; [apply (proj1 (NoDup_ListNoDup _)); exact l_nodup | constructor; [intros [] | constructor] |].
      intros a Ha [<-|[]]. exact (l_notin Ha).
    - intros x Hx. change (In x l') in Hx. apply in_l' in Hx. rewrite e_metaU, e_is_group, e_fresh. destruct Hx as [Hx| ->].
      + destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
        destruct (l_mem x Hx) as (_ & _ & _ & _ & Hxm). rewrite e_meta_other by exact Hxm. cbn. repeat split; assumption.
      + rewrite e_meta_m. cbn. repeat split; try assumption; reflexivity.
    - intros s Hs. apply (dll_ext st st'); [|exact (D2 s Hs)]. intros x Hx. rewrite (q_meta_group x (proj1 (proj2 (AU s x Hx)))). split; reflexivity.
    - exact ND2.
    - intros s x Hin. rewrite e_is_group, e_gsc by exact (proj1 (proj2 (AU s x Hin))). exact (AU s x Hin).
    - exact AN.
    - intros x U NL. rewrite e_metaU in U. rewrite e_listed in NL. rewrite e_next, e_prev.
      assert (x <> m) by (intros ->; apply NL; right; reflexivity).
      rewrite q_next_other, q_prev_other; [apply LK; [exact U | intros Hl; apply NL; left; exact Hl] | exact H | | exact H |].
      + intros Hn ->. apply NL. left. exact (proj1 (proj2 (proj2 (proj2 (hd_facts Hn))))).
      + intros Hn ->. apply NL. left. exact (proj1 (proj2 (proj2 (proj2 (tl_facts Hn))))).
    - intros x Hl. rewrite e_next, e_prev. rewrite e_listed in Hl.
      pose proof m_pos as MP.
      assert (Hm0 : m <> 0) by (hsep; unfold HEAPLO in MP; lia).
      assert (Hhd0 : q_nil = false -> hd <> 0).
      { intros Hn E0. pose proof (metaU_rng st L HWF hd (proj1 (hd_facts Hn))). hsep; unfold HEAPLO in *. lia. }
      assert (Htl0 : q_nil = false -> tl <> 0).
      { intros Hn E0. pose proof (metaU_rng st L HWF tl (proj1 (tl_facts Hn))). hsep; unfold HEAPLO in *. lia. }
      assert (OLD : x <> m -> mr_next (s_meta st x) <> 0 /\ mr_prev (s_meta st x) <> 0).
      { intros Hxm. apply LKD. destruct Hl as [Hl| ->]; [exact Hl | congruence]. }
      unfold q_next, q_prev. destruct (Z.eqb_spec x m) as [->|Hxm].
      + case_bool q_nil En; split; auto.
      + specialize (OLD Hxm). destruct OLD as [O1 O2].
        case_bool q_nil En; cbn [negb andb]; [split; assumption|].
        destruct (Z.eqb_spec x tl); destruct (Z.eqb_spec x hd); split; assumption.
    - intros s x Hin Hne. pose proof (proj1 (proj2 (AU s x Hin))) as Hx.
      rewrite e_avail, e_freed by exact (grp_not_m x Hx). exact (RS s x Hin Hne).
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof using HNG HWF RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG. pose proof (grp_not_m x Hx) as Hxm.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_kind, ?e_slot, ?e_alist by exact Hx;
      rewrite ?(e_avail x Hxm), ?(e_freed x Hxm); try assumption.
    - rewrite e_in_flist. intros [F| E]; [exact (Nfr F) | exact (Hxm E)].
    - intros H63 Hl. apply (S63 H63). apply (e_listed_other x Hxm). exact Hl.
    - intros Hall Hne Hl. apply (Full Hall Hne). apply (e_listed_other x Hxm). exact Hl.
    - destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride by (assumption || exact K2).
      assert (HG : is_group st' hm) by (apply e_is_group; exact K2).
      repeat (split; [assumption|]). assumption.
    - intros k Hk. apply (x_slot_wf_same st st' L SLf); [exact Hx|]. exact (Slots k Hk).
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using HNF Hunl HNG HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - exact ND.
    - intros x Hx. apply t_wf_group. exact Hx.
    - intros m1 m2 H1 H2. rewrite !e_ai. rewrite !e_glast, !e_gsc by assumption. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. pose proof (REG b len x Hin) as (A & B & C & D). rewrite e_is_group, e_kind. rewrite e_gmem, e_gml by exact A. exact (REG b len x Hin).
    - intros x F. apply e_fresh in F.
      assert (x <> m) by (intros ->; exact (HNF F)).
      rewrite q_meta_offlist; [exact (FR0 x F) | exact H |]. intros Hin. exact (proj1 (proj2 (proj2 (l_mem x Hin))) F).
    - intros x U NG NFL NFR. rewrite e_metaU in U. rewrite e_in_flist in NFL. rewrite e_fresh in NFR. rewrite e_is_group in NG.
      apply zremove_In. split; [apply (OTH x U NG); [intros F; apply NFL; left; exact F | exact NFR]|].
      intros ->. apply NFL. right. reflexivity.
    - intros x Hl. apply zremove_In in Hl. destruct Hl as [Hl Hxm]. destruct (LIM x Hl) as (A & B & C & D).
      rewrite e_metaU, e_is_group, e_fresh, (e_listed_other x Hxm). repeat split; assumption.
    - intros m1 m2 H1 H2 G1 G2 E. change (is_group st m1) in H1. change (is_group st m2) in H2.
      rewrite !e_gsc in E by assumption. rewrite e_glast in G1 by exact H1. rewrite e_glast in G2 by exact H2. rewrite !e_slot in G1, G2.
      exact (ONEFF m1 m2 H1 H2 G1 G2 E).
  Qed.

  Lemma t_WF : WF st' L.
  Proof using HNF Hunl HNG HU HWF.
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SLf (WF_areas st L HWF))|]. split; [exact t_wf_lists|].
    split; [exact t_wf_groups|]. split; [exact (wf_geom_ext st st' L SLf HWF (WF_geom st L HWF))|].
    split; [exact (wf_live_ext st st' L SLf (WF_live st L HWF)) |]. split; [exact (wf_regions_ext st st' L SLf HWF eq_refl (WF_regions st L HWF)) | exact (wf_img_ext st st' SLf (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition q_wr (a : Z) : Prop :=
    (sp - MSTK <= a < sp) \/ (m <= a < m + 40) \/
    (q_nil = false /\ ((tl + 8 <= a < tl + 16) \/ (hd <= a < hd + 8))) \/
    (q_nil = true /\ ctx_free_meta_head <= a < ctx_free_meta_head + 8).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> q_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMm0 : cell M' m 8 (q_prev m).
  Hypothesis HMm8 : cell M' (m + 8) 8 (q_next m).
  Hypothesis HMm16 : cell M' (m + 16) 8 0.
  Hypothesis HMm24 : cell M' (m + 24) 4 0.
  Hypothesis HMm28 : cell M' (m + 28) 4 0.
  Hypothesis HMm32 : cell M' (m + 32) 8 0.
  Hypothesis HMtl : q_nil = false -> cell M' (tl + 8) 8 m.
  Hypothesis HMhd : q_nil = false -> cell M' hd 8 m.
  Hypothesis HMact : q_nil = true -> cell M' ctx_free_meta_head 8 m.

  (* [comment removed for export] *)
  Lemma m_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL.
  Proof using HU HWF L st. destruct (metaU_rng st L HWF m HU) as (A & B & _). lia. Qed.

  Lemma wr_cases : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    CEIL <= a \/ (exists x, metaU st x /\ (x = m \/ (q_nil = false /\ (x = tl \/ x = hd))) /\ x <= a < x + 40)
    \/ (q_nil = true /\ ctx_free_meta_head <= a < ctx_free_meta_head + 8).
  Proof using HMwr Hsp Hunl HU HWF sp L.
    intros a Hr NE. destruct (HMwr a Hr NE) as [W|[W|[[Hn [W|W]]|W]]].
    - left. ceil; unfold MSTK in *. lia.
    - right; left. exists m. split; [exact HU|]. split; [left; reflexivity | lia].
    - right; left. exists tl. split; [exact (proj1 (tl_facts Hn))|]. split; [right; split; [exact Hn | left; reflexivity] | lia].
    - right; left. exists hd. split; [exact (proj1 (hd_facts Hn))|]. split; [right; split; [exact Hn | right; reflexivity] | lia].
    - right; right. exact W.
  Qed.

  Definition XMf (x : Z) : bool := (x =? m) || (negb q_nil && ((x =? tl) || (x =? hd))).

  Lemma t_rep_meta_m : rep_meta M' m (s_meta st' m).
  Proof using HMm32 HMm28 HMm24 HMm16 HMm8 HMm0.
    rewrite e_meta_m. constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W];
      [exact HMm0 | exact HMm8 | exact HMm16 | exact HMm24 | exact HMm28 | exact HMm32].
  Qed.

  Lemma t_rep_meta_end : forall x, q_nil = false -> (x = tl \/ x = hd) -> rep_meta M' x (s_meta st' x).
  Proof using HMhd HMtl HMwr Hsp Hunl HU HREP HWF sp M L RN.
    intros x Hn Hx.
    assert (Ux : metaU st x) by (destruct Hx as [-> | ->]; [exact (proj1 (tl_facts Hn)) | exact (proj1 (hd_facts Hn))]).
    assert (Hxm : x <> m) by (destruct Hx as [-> | ->]; [exact (proj2 (proj2 (proj2 (proj2 (tl_facts Hn))))) | exact (proj2 (proj2 (proj2 (proj2 (hd_facts Hn)))))]).
    pose proof (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hxa & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa in RM.
    destruct RM as [P N Me Av Fr Wc]. destruct (metaU_rng st L HWF x Ux) as (R1 & R2 & _).
    pose proof (metaU_sep st L HWF x m Ux HU Hxm) as SEPm.
    assert (AG : agree_on (fun a => x <= a < x + 40 /\ ~ (x = hd /\ x <= a < x + 8) /\ ~ (x = tl /\ x + 8 <= a < x + 16)) M M').
    { intros a Hr (Ha & N1 & N2). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|[[_ [W|W]]|[W _]]]].
      - ceil; unfold MSTK in *. lia.
      - lia.
      - destruct (Z.eq_dec x tl) as [E|NEt]; [apply N2; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x tl Ux (proj1 (tl_facts Hn)) NEt); lia.
      - destruct (Z.eq_dec x hd) as [E|NEh]; [apply N1; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x hd Ux (proj1 (hd_facts Hn)) NEh); lia.
      - congruence. }
    rewrite e_meta_other by exact Hxm. unfold mr_set_links, q_next, q_prev. destruct (Z.eqb_spec x m); [contradiction|]. rewrite Hn. cbn [negb andb].
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - destruct (Z.eqb_spec x hd) as [E|NE].
      + rewrite E at 1. exact (HMhd Hn).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact P]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - destruct (Z.eqb_spec x tl) as [E|NE].
      + rewrite E at 1. exact (HMtl Hn).
      + eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact N]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMact HMhd HMtl HMm32 HMm28 HMm24 HMm16 HMm8 HMm0 HMgrow HMwr Hsp Hunl HNG HU HREP HWF sp M L RN.
    pose proof m_rng as [MR1 MR2].
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[_ W]]].
      + ceil; unfold CTX in *; lia.
      + destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX in *; lia.
      + unfold ctx_free_meta_head, CTX in *; lia.
    - apply (rep_ctx_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow) (fun _ => false) q_nil); try reflexivity.
      + intros a Hr (Ha & NA & NF). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|[Hn W]]].
        * ceil; unfold CTX_END, CTX in *; lia.
        * destruct (metaU_rng st L HWF x Ux). hsep; unfold HEAPLO, CTX_END, CTX in *; lia.
        * apply NF. split; [exact Hn | exact W].
      + intros s Hs. right. split; reflexivity.
      + rewrite e_ctx_fhead, head_l'. case_bool q_nil En.
        * left. split; [reflexivity|]. exact (HMact En).
        * right. split; [reflexivity|]. symmetry. exact (wc_fhead st (WF_ctx st L HWF)).
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) XMf); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(x & Ux & Hx & W)|[Hn W]]].
        * ceil; lia.
        * exists x. split; [exact Ux|]. split; [|exact W]. unfold XMf.
          destruct Hx as [->|[Hn [->| ->]]]; rewrite ?Z.eqb_refl, ?Hn; cbn; rewrite ?Bool.orb_true_r; reflexivity.
        * hsep; unfold ctx_free_meta_head, CTX, HEAPLO in *; lia.
      + intros x Ux X. unfold XMf in X. destruct (Z.eqb_spec x m) as [->|Hxm]; [exact t_rep_meta_m|].
        cbn [orb] in X. revert X. case_bool q_nil En; intros X; [discriminate X|]. cbn [negb andb] in X.
        apply t_rep_meta_end; [exact En|].
        destruct (Z.eqb_spec x tl); [left; assumption|]. destruct (Z.eqb_spec x hd); [right; assumption|]. discriminate X.
      + intros x Ux X. unfold XMf in X. apply Bool.orb_false_elim in X. destruct X as [X1 X2].
        apply q_meta_other.
        * intros ->. rewrite Z.eqb_refl in X1. discriminate X1.
        * intros Hn ->. rewrite Hn, Z.eqb_refl in X2. discriminate X2.
        * intros Hn ->. rewrite Hn, Z.eqb_refl, Bool.orb_true_r in X2. discriminate X2.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. apply e_is_group. exact Hx.
      + intros x Hx. apply e_is_group in Hx. rewrite (q_meta_group x Hx). repeat split; reflexivity.
      + intros x Hx E. apply e_is_group in Hx. apply (x_endb st st' L SLf HWF); [exact Hx|]. exact E.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. apply e_is_group in Hx. apply (x_gcell st st' L SLf HWF) in G; [|exact Hx].
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|[(y & Uy & _ & W)|[Hn W]]].
        * ceil; lia.
        * exact (gcell_not_meta st L HWF x y a Hx G Uy W).
        * hsep; unfold ctx_free_meta_head, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. apply (x_gcell st st' L SLf HWF); [apply e_is_group; exact Hx|]. exact G.
  Qed.

  Theorem freemeta_close : WF st' L /\ REP st' M'.
  Proof using HMact HMhd HMtl HMm32 HMm28 HMm24 HMm16 HMm8 HMm0 HMgrow HMwr Hsp HNF Hunl HNG HU HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.
End FreeMeta.
