(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhQueue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FlPop.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  #[local] Notation l := (s_flist st).
  Hypothesis Hnn : s_flist st <> [].
  #[local] Notation fh := (head_of l).
  #[local] Notation nxf := (mr_next (s_meta st fh)).
  #[local] Notation pvf := (mr_prev (s_meta st fh)).
  Definition single : bool := nxf =? fh.
  Definition l' : list Z := match s_flist st with [] => [] | _ :: r => r end.

  Definition p_next (x : Z) : Z :=
    if x =? fh then 0 else if (negb single && (x =? pvf))%bool then nxf else mr_next (s_meta st x).
  Definition p_prev (x : Z) : Z :=
    if x =? fh then 0 else if (negb single && (x =? nxf))%bool then pvf else mr_prev (s_meta st x).
  Definition p_meta (x : Z) : meta_rec :=
    if x =? fh then meta_zero else mr_set_links (s_meta st x) (p_prev x) (p_next x).
  Definition st' : mst :=
    MST (cx_set_fhead (s_ctx st) (head_of l'))
        (s_areas st) p_meta l' (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (fh :: s_limbo st).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma l_dll : dll st l. Proof using HWF L RN. exact (wl_fdll st (WF_lists st L HWF)). Qed.
  Lemma l_nodup : NoDup l. Proof using HWF L RN. exact (wl_fnodup st (WF_lists st L HWF)). Qed.
  Lemma l_ND : List.NoDup l. Proof using HWF L RN. apply NoDup_ListNoDup. exact l_nodup. Qed.
  Lemma l_dllf : dllf (fun x => mr_next (s_meta st x)) (fun x => mr_prev (s_meta st x)) l.
  Proof using HWF L RN. apply dll_dllf. exact l_dll. Qed.
  Lemma l_cons : l = fh :: l'.
  Proof using Hnn. unfold l'. destruct (s_flist st) as [|a r] eqn:E; [exfalso; exact (Hnn eq_refl)|]. reflexivity. Qed.
  Lemma fh_in : In fh l. Proof using Hnn. rewrite l_cons at 2. left. reflexivity. Qed.
  Lemma l_mem : forall x, In x l -> metaU st x /\ ~ is_group st x /\ ~ fresh st x /\ listed st x /\
                               mr_mem (s_meta st x) = 0 /\ mr_avail (s_meta st x) = 0 /\ mr_freed (s_meta st x) = 0 /\ mr_W (s_meta st x) = 0.
  Proof using HWF L RN.
    intros x Hin. destruct (wl_fU st (WF_lists st L HWF) x Hin) as (U & NG & NF & Me & Av & Fr & W).
    repeat split; try assumption. left. exact Hin.
  Qed.
  Lemma fh_facts : metaU st fh /\ ~ is_group st fh /\ ~ fresh st fh /\ listed st fh.
  Proof using Hnn HWF L RN. destruct (l_mem fh fh_in) as (A & B & C & D & _). repeat split; assumption. Qed.
  Lemma nx_in : In nxf l. Proof using Hnn HWF L RN. exact (proj1 (dllf_links_In _ _ l fh l_dllf fh_in)). Qed.
  Lemma pv_in : In pvf l. Proof using Hnn HWF L RN. exact (proj2 (dllf_links_In _ _ l fh l_dllf fh_in)). Qed.
  Lemma single_iff : single = true <-> zlen l = 1.
  Proof using Hnn HWF L RN. unfold single. rewrite Z.eqb_eq. apply (dllf_self_iff _ _ l fh l_dllf l_ND fh_in). Qed.
  Lemma single_nil : single = true <-> l' = [].
  Proof using Hnn HWF L RN.
    rewrite single_iff. rewrite l_cons at 1. rewrite zlen_cons. split.
    - intros H. destruct l' as [|a r]; [reflexivity|]. rewrite zlen_cons in H. pose proof (zlen_nonneg r). lia.
    - intros ->. reflexivity.
  Qed.
  Lemma l'_len : single = false -> 0 < zlen l'.
  Proof using Hnn HWF L RN.
    intros H. destruct l' as [|a r] eqn:E; [|rewrite zlen_cons; pose proof (zlen_nonneg r); lia].
    exfalso. apply single_nil in E. congruence.
  Qed.
  Lemma nx_head : single = false -> nxf = head_of l'.
  Proof using Hnn HWF L RN.
    intros H. pose proof (l'_len H) as Hn. pose proof l_dllf as D. rewrite l_cons in D.
    rewrite (dllf_remove_head _ _ l' fh D Hn). symmetry. apply head_of_znth. intros E0. rewrite E0, zlen_nil in Hn. lia.
  Qed.
  Lemma fh_not_in_l' : ~ In fh l'.
  Proof using Hnn HWF L RN. pose proof l_ND as ND. rewrite l_cons in ND. inversion ND. assumption. Qed.
  Lemma l'_sub : forall x, In x l' -> In x l /\ x <> fh.
  Proof using Hnn HWF L RN. intros x Hx. split; [rewrite l_cons; right; exact Hx|]. intros ->. exact (fh_not_in_l' Hx). Qed.
  Lemma nx_ne : single = false -> nxf <> fh.
  Proof using. intros H E. unfold single in H. rewrite (proj2 (Z.eqb_eq _ _) E) in H. discriminate H. Qed.
  Lemma pv_ne : single = false -> pvf <> fh.
  Proof using Hnn HWF L RN.
    intros H E. apply (dllf_prev_self_iff _ _ l fh l_dllf l_ND fh_in) in E. apply single_iff in E. congruence.
  Qed.
  Lemma nx_facts : metaU st nxf /\ ~ is_group st nxf /\ ~ fresh st nxf /\ listed st nxf.
  Proof using Hnn HWF L RN. destruct (l_mem nxf nx_in) as (A & B & C & D & _). repeat split; assumption. Qed.
  Lemma pv_facts : metaU st pvf /\ ~ is_group st pvf /\ ~ fresh st pvf /\ listed st pvf.
  Proof using Hnn HWF L RN. destruct (l_mem pvf pv_in) as (A & B & C & D & _). repeat split; assumption. Qed.
  Lemma grp_not_fh : forall x, is_group st x -> x <> fh. Proof using Hnn HWF L RN. intros x Hx ->. exact (proj1 (proj2 fh_facts) Hx). Qed.
  Lemma grp_not_nx : forall x, is_group st x -> x <> nxf. Proof using Hnn HWF L RN. intros x Hx ->. exact (proj1 (proj2 nx_facts) Hx). Qed.
  Lemma grp_not_pv : forall x, is_group st x -> x <> pvf. Proof using Hnn HWF L RN. intros x Hx ->. exact (proj1 (proj2 pv_facts) Hx). Qed.



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

  Lemma e_limbo : s_limbo st' = fh :: s_limbo st. Proof using. reflexivity. Qed.


  Lemma e_next : forall x, mr_next (s_meta st' x) = p_next x.
  Proof using. intros x. cbn. unfold p_meta. destruct (Z.eqb_spec x fh) as [E|]; [rewrite E; unfold p_next; rewrite Z.eqb_refl; reflexivity | reflexivity]. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = p_prev x.
  Proof using. intros x. cbn. unfold p_meta. destruct (Z.eqb_spec x fh) as [E|]; [rewrite E; unfold p_prev; rewrite Z.eqb_refl; reflexivity | reflexivity]. Qed.
  Lemma e_meta_other : forall x, x <> fh -> s_meta st' x = mr_set_links (s_meta st x) (p_prev x) (p_next x).
  Proof using. intros x Hx. cbn. unfold p_meta. destruct (Z.eqb_spec x fh); [contradiction | reflexivity]. Qed.
  Lemma e_meta_fh : s_meta st' fh = meta_zero.
  Proof using. cbn. unfold p_meta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_mem : forall x, mr_mem (s_meta st' x) = mr_mem (s_meta st x).
  Proof using Hnn HWF L RN.
    intros x. destruct (Z.eq_dec x fh) as [->|Hx]; [rewrite e_meta_fh; cbn; symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (l_mem fh fh_in))))))|].
    rewrite e_meta_other by exact Hx. reflexivity.
  Qed.
  Lemma e_avail : forall x, mr_avail (s_meta st' x) = mr_avail (s_meta st x).
  Proof using Hnn HWF L RN.
    intros x. destruct (Z.eq_dec x fh) as [->|Hx]; [rewrite e_meta_fh; cbn; symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (l_mem fh fh_in)))))))|].
    rewrite e_meta_other by exact Hx. reflexivity.
  Qed.
  Lemma e_freed : forall x, mr_freed (s_meta st' x) = mr_freed (s_meta st x).
  Proof using Hnn HWF L RN.
    intros x. destruct (Z.eq_dec x fh) as [->|Hx]; [rewrite e_meta_fh; cbn; symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (l_mem fh fh_in))))))))|].
    rewrite e_meta_other by exact Hx. reflexivity.
  Qed.
  Lemma e_Wr : forall x, mr_W (s_meta st' x) = mr_W (s_meta st x).
  Proof using Hnn HWF L RN.
    intros x. destruct (Z.eq_dec x fh) as [->|Hx]; [rewrite e_meta_fh; cbn; symmetry; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (l_mem fh fh_in))))))))|].
    rewrite e_meta_other by exact Hx. reflexivity.
  Qed.
  Lemma e_gW : forall x, g_W st' x = g_W st x. Proof using Hnn HWF L RN. intros; unfold g_W; apply e_Wr. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof using Hnn HWF L RN. intros; unfold g_mem; apply e_mem. Qed.
  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof using Hnn HWF L RN. intros; unfold g_lastidx; rewrite e_gW; reflexivity. Qed.
  Lemma e_gcnt : forall x, g_cnt st' x = g_cnt st x. Proof using Hnn HWF L RN. intros; unfold g_cnt; rewrite e_glast; reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using Hnn HWF L RN. intros; unfold g_sc; rewrite e_gW; reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof using Hnn HWF L RN. intros; unfold g_maplen; rewrite e_gW; reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x.
  Proof using Hnn HWF L RN. intros; unfold g_stride; rewrite e_gml, e_glast, e_gsc; reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k.
  Proof using Hnn HWF L RN. intros; unfold g_slot_start; rewrite e_gmem, e_gstride; reflexivity. Qed.
  Lemma e_ctx_fhead : c_free_head (s_ctx st') = head_of l'. Proof using. reflexivity. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using. intros; unfold fresh; rewrite e_areas; cbn; tauto. Qed.

  Lemma SLp : same_layout st st'.
  Proof using Hnn HWF L RN. constructor; intros; try reflexivity; [apply slot_sim_refl | apply e_mem | apply e_Wr]. Qed.

  Lemma head_l' : head_of l' = if single then 0 else nxf.
  Proof using Hnn HWF L RN.
    case_bool single E.
    - apply single_nil in E. rewrite E. reflexivity.
    - symmetry. apply nx_head. exact E.
  Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x /\ x <> fh.
  Proof using Hnn HWF L RN.
    intros x. unfold in_flist. rewrite e_flist. split; [apply l'_sub|].
    intros [Hin Hne]. rewrite l_cons in Hin. destruct Hin as [E|Hin]; [exfalso; exact (Hne (eq_sym E)) | exact Hin].
  Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x /\ x <> fh.
  Proof using Hnn HWF L RN.
    intros x. unfold listed. rewrite e_in_flist, e_in_alist. split.
    - intros [[A B]|A]; [split; [left; exact A | exact B]|]. split; [right; exact A|].
      intros ->. destruct A as (sc & Hsc & Hin). exact (proj1 (proj2 fh_facts) (proj1 (proj2 (wl_aU st (WF_lists st L HWF) sc _ Hin)))).
    - intros [[A|A] B]; [left; split; assumption | right; exact A].
  Qed.
  Lemma e_listed_other : forall x, x <> fh -> (listed st' x <-> listed st x).
  Proof using Hnn HWF L RN. intros x Hx. rewrite e_listed. tauto. Qed.

  Lemma p_next_other : forall x, x <> fh -> (single = false -> x <> pvf) -> p_next x = mr_next (s_meta st x).
  Proof using.
    intros x H1 H2. unfold p_next. destruct (Z.eqb_spec x fh); [contradiction|].
    case_bool single E; cbn; [reflexivity|]. destruct (Z.eqb_spec x pvf); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma p_prev_other : forall x, x <> fh -> (single = false -> x <> nxf) -> p_prev x = mr_prev (s_meta st x).
  Proof using.
    intros x H1 H2. unfold p_prev. destruct (Z.eqb_spec x fh); [contradiction|].
    case_bool single E; cbn; [reflexivity|]. destruct (Z.eqb_spec x nxf); [exfalso; exact (H2 E e) | reflexivity].
  Qed.
  Lemma p_meta_other : forall x, x <> fh -> (single = false -> x <> pvf) -> (single = false -> x <> nxf) -> s_meta st' x = s_meta st x.
  Proof using.
    intros x H1 H2 H3. rewrite e_meta_other by exact H1. rewrite p_next_other, p_prev_other by assumption. apply mr_set_links_id.
  Qed.
  Lemma p_meta_group : forall x, is_group st x -> s_meta st' x = s_meta st x.
  Proof using Hnn HWF L RN.
    intros x Hx. apply p_meta_other; [apply grp_not_fh; exact Hx | intros _; apply grp_not_pv; exact Hx | intros _; apply grp_not_nx; exact Hx].
  Qed.
  Lemma p_meta_offlist : forall x, ~ In x l -> s_meta st' x = s_meta st x.
  Proof using Hnn HWF L RN.
    intros x H2. apply p_meta_other; [intros ->; exact (H2 fh_in) | intros _ ->; exact (H2 pv_in) | intros _ ->; exact (H2 nx_in)].
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
  Proof using Hnn HWF L RN.
    apply (proj2 (dll_dllf st' l')).
    assert (EQ : forall l0, dllf p_next p_prev l0 -> dllf (fun x => mr_next (s_meta st' x)) (fun x => mr_prev (s_meta st' x)) l0).
    { intros l0 D k Hk. rewrite e_next, e_prev. exact (D k Hk). }
    apply EQ. case_bool single E.
    - pose proof (proj1 single_nil E) as El. rewrite El. intros k Hk. rewrite zlen_nil in Hk. lia.
    - pose proof (l'_len E) as Hn. pose proof l_ND as ND. pose proof l_dllf as D. rewrite l_cons in ND, D.
      apply (dllf_remove _ _ p_next p_prev [] l' fh D ND Hn).
      + intros x Hx Hne. cbn [app] in Hx. apply p_next_other; [intros ->; exact (fh_not_in_l' Hx) | intros _; exact Hne].
      + unfold p_next. destruct (Z.eqb_spec pvf fh) as [Ee|]; [exfalso; exact (pv_ne E Ee)|]. rewrite E, Z.eqb_refl. reflexivity.
      + intros x Hx Hne. cbn [app] in Hx. apply p_prev_other; [intros ->; exact (fh_not_in_l' Hx) | intros _; exact Hne].
      + unfold p_prev. destruct (Z.eqb_spec nxf fh) as [Ee|]; [exfalso; exact (nx_ne E Ee)|]. rewrite E, Z.eqb_refl. reflexivity.
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hnn HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist.
    - exact t_dll_l'.
    - pose proof ND1 as ND. rewrite l_cons in ND. apply NoDup_ListNoDup in ND. inversion ND. apply NoDup_ListNoDup. assumption.
    - intros x Hx. change (In x l') in Hx. destruct (l'_sub x Hx) as [Hin Hne]. rewrite e_metaU, e_is_group, e_fresh.
      destruct (FU x Hin) as (U & NG & NF & Me & Av & Fr & W).
      rewrite e_meta_other by exact Hne. cbn. repeat split; assumption.
    - intros s Hs. apply (dll_ext st st'); [|exact (D2 s Hs)]. intros x Hx. rewrite (p_meta_group x (proj1 (proj2 (AU s x Hx)))). split; reflexivity.
    - exact ND2.
    - intros s x Hin. rewrite e_is_group, e_gsc. exact (AU s x Hin).
    - exact AN.
    - intros x U NL. rewrite e_metaU in U. rewrite e_listed in NL. rewrite e_next, e_prev.
      destruct (Z.eq_dec x fh) as [->|Hxf].
      + unfold p_next, p_prev. rewrite Z.eqb_refl. split; reflexivity.
      + assert (NL0 : ~ listed st x) by (intros Hl; apply NL; split; assumption).
        rewrite p_next_other, p_prev_other; [apply LK; [exact U | exact NL0] | exact Hxf | | exact Hxf |].
        * intros Hn ->. exact (NL0 (proj2 (proj2 (proj2 nx_facts)))).
        * intros Hn ->. exact (NL0 (proj2 (proj2 (proj2 pv_facts)))).
    - intros x Hl. rewrite e_next, e_prev. rewrite e_listed in Hl. destruct Hl as [Hl Hxf].
      destruct (LKD x Hl) as [O1 O2].
      assert (Hnx0 : nxf <> 0) by (intros E0; pose proof (metaU_rng st L HWF nxf (proj1 nx_facts)); unfold HEAPLO in *; lia).
      assert (Hpv0 : pvf <> 0) by (intros E0; pose proof (metaU_rng st L HWF pvf (proj1 pv_facts)); unfold HEAPLO in *; lia).
      unfold p_next, p_prev. destruct (Z.eqb_spec x fh); [contradiction|].
      case_bool single En; cbn [negb andb]; [split; assumption|].
      destruct (Z.eqb_spec x pvf); destruct (Z.eqb_spec x nxf); split; assumption.
    - intros s x Hin Hne. rewrite e_avail, e_freed. exact (RS s x Hin Hne).
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof using Hnn HWF RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG. pose proof (grp_not_fh x Hx) as Hxm.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_kind, ?e_slot, ?e_alist, ?e_avail, ?e_freed; try assumption.
    - rewrite e_in_flist. intros [F _]. exact (Nfr F).
    - intros H63 Hl. apply (S63 H63). apply (e_listed_other x Hxm). exact Hl.
    - intros Hall Hne Hl. apply (Full Hall Hne). apply (e_listed_other x Hxm). exact Hl.
    - destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride.
      assert (HG : is_group st' hm) by (apply e_is_group; exact K2).
      repeat (split; [assumption|]). assumption.
    - intros k Hk. apply (x_slot_wf_same st st' L SLp); [exact Hx|]. exact (Slots k Hk).
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hnn HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - exact ND.
    - intros x Hx. apply t_wf_group. exact Hx.
    - intros m1 m2 H1 H2. rewrite !e_ai. rewrite !e_glast, !e_gsc. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. rewrite e_is_group, e_kind, e_gmem, e_gml. exact (REG b len x Hin).
    - intros x F. apply e_fresh in F. rewrite p_meta_offlist; [exact (FR0 x F)|]. intros Hin. exact (proj1 (proj2 (proj2 (l_mem x Hin))) F).
    - intros x U NG NFL NFR. rewrite e_metaU in U. rewrite e_in_flist in NFL. rewrite e_fresh in NFR. rewrite e_is_group in NG.
      destruct (Z.eq_dec x fh) as [->|Hxf]; [left; reflexivity|]. right.
      apply (OTH x U NG); [intros F; apply NFL; split; assumption | exact NFR].
    - intros x [<-|Hl].
      + rewrite e_metaU, e_is_group, e_fresh, e_listed. pose proof fh_facts as (A & B & C & D). repeat split; try assumption. intros [_ X]. exact (X eq_refl).
      + destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_fresh, e_listed. repeat split; try assumption. intros [X _]. exact (C X).
    - intros m1 m2 H1 H2 G1 G2 E. rewrite !e_gsc in E. rewrite !e_glast in G1, G2. rewrite !e_slot in G1, G2. exact (ONEFF m1 m2 H1 H2 G1 G2 E).
  Qed.

  Lemma t_WF : WF st' L.
  Proof using Hnn HWF.
    split; [exact t_wf_ctx|]. split; [exact (wf_areas_ext st st' SLp (WF_areas st L HWF))|]. split; [exact t_wf_lists|].
    split; [exact t_wf_groups|]. split; [exact (wf_geom_ext st st' L SLp HWF (WF_geom st L HWF))|].
    split; [exact (wf_live_ext st st' L SLp (WF_live st L HWF)) |]. split; [exact (wf_regions_ext st st' L SLp HWF eq_refl (WF_regions st L HWF)) | exact (wf_img_ext st st' SLp (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition p_wr (a : Z) : Prop :=
    (sp - MSTK <= a < sp) \/ (fh <= a < fh + 16) \/
    (single = false /\ ((pvf + 8 <= a < pvf + 16) \/ (nxf <= a < nxf + 8))) \/
    (ctx_free_meta_head <= a < ctx_free_meta_head + 8).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> p_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMm0 : cell M' fh 8 0.
  Hypothesis HMm8 : cell M' (fh + 8) 8 0.
  Hypothesis HMpv : single = false -> cell M' (pvf + 8) 8 nxf.
  Hypothesis HMnx : single = false -> cell M' nxf 8 pvf.
  Hypothesis HMfmh : cell M' ctx_free_meta_head 8 (head_of l').

  Lemma fh_rng : HEAPLO + 24 <= fh /\ fh + 40 <= CEIL.
  Proof using Hnn HWF L. destruct (metaU_rng st L HWF fh (proj1 fh_facts)) as (A & B & _). lia. Qed.

  Lemma wr_cases : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) ->
    CEIL <= a \/ (exists x, metaU st x /\ (x = fh \/ (single = false /\ (x = pvf \/ x = nxf))) /\ x <= a < x + 40)
    \/ (ctx_free_meta_head <= a < ctx_free_meta_head + 8).
  Proof using HMwr Hsp Hnn HWF sp L.
    intros a Hr NE. destruct (HMwr a Hr NE) as [W|[W|[[Hn [W|W]]|W]]].
    - left. ceil; unfold MSTK in *. lia.
    - right; left. exists fh. split; [exact (proj1 fh_facts)|]. split; [left; reflexivity | lia].
    - right; left. exists pvf. split; [exact (proj1 pv_facts)|]. split; [right; split; [exact Hn | left; reflexivity] | lia].
    - right; left. exists nxf. split; [exact (proj1 nx_facts)|]. split; [right; split; [exact Hn | right; reflexivity] | lia].
    - right; right. exact W.
  Qed.

  Definition XMp (x : Z) : bool := (x =? fh) || (negb single && ((x =? pvf) || (x =? nxf))).

  Lemma t_rep_meta_fh : rep_meta M' fh (s_meta st' fh).
  Proof using HMm8 HMm0 HMwr Hsp Hnn HREP HWF sp M L RN.
    rewrite e_meta_fh.
    pose proof (metaU_area st L HWF fh (proj1 fh_facts)) as (ar & k & Har & Hk & Hxa & _).
    pose proof (proj1 fh_facts) as Ufh.
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa in RM.
    destruct RM as [P N Me Av Fr Wc]. destruct fh_rng as [R1 R2].
    destruct (l_mem fh fh_in) as (_ & _ & _ & _ & E16 & E24 & E28 & E32). rewrite E16 in Me. rewrite E24 in Av. rewrite E28 in Fr. rewrite E32 in Wc.
    assert (AG : agree_on (fun a => fh + 16 <= a < fh + 40) M M').
    { intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|[[Hn [W|W]]|W]]].
      - ceil; unfold MSTK in *. lia.
      - lia.
      - destruct (metaU_sep st L HWF fh pvf (proj1 fh_facts) (proj1 pv_facts) (fun E => pv_ne Hn (eq_sym E))); lia.
      - destruct (metaU_sep st L HWF fh nxf (proj1 fh_facts) (proj1 nx_facts) (fun E => nx_ne Hn (eq_sym E))); lia.
      - unfold ctx_free_meta_head, CTX, HEAPLO in *. lia. }
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - exact HMm0.
    - exact HMm8.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  Lemma t_rep_meta_end : forall x, single = false -> (x = pvf \/ x = nxf) -> rep_meta M' x (s_meta st' x).
  Proof using HMnx HMpv HMwr Hsp Hnn HREP HWF sp M L RN.
    intros x Hn Hx.
    assert (Ux : metaU st x) by (destruct Hx as [-> | ->]; [exact (proj1 pv_facts) | exact (proj1 nx_facts)]).
    assert (Hxm : x <> fh) by (destruct Hx as [-> | ->]; [exact (pv_ne Hn) | exact (nx_ne Hn)]).
    pose proof (metaU_area st L HWF x Ux) as (ar & k & Har & Hk & Hxa & _).
    pose proof (ra_metas st M ar (rp_areas st M HREP ar Har) k Hk) as RM. rewrite <- Hxa in RM.
    destruct RM as [P N Me Av Fr Wc]. destruct (metaU_rng st L HWF x Ux) as (R1 & R2 & _).
    pose proof (metaU_sep st L HWF x fh Ux (proj1 fh_facts) Hxm) as SEPm.
    assert (AG : agree_on (fun a => x <= a < x + 40 /\ ~ (x = nxf /\ x <= a < x + 8) /\ ~ (x = pvf /\ x + 8 <= a < x + 16)) M M').
    { intros a Hr (Ha & N1 & N2). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr a Hr NE) as [W|[W|[[_ [W|W]]|W]]].
      - ceil; unfold MSTK in *. lia.
      - lia.
      - destruct (Z.eq_dec x pvf) as [E|NEt]; [apply N2; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x pvf Ux (proj1 pv_facts) NEt); lia.
      - destruct (Z.eq_dec x nxf) as [E|NEh]; [apply N1; split; [exact E | lia]|].
        destruct (metaU_sep st L HWF x nxf Ux (proj1 nx_facts) NEh); lia.
      - unfold ctx_free_meta_head, CTX, HEAPLO in *. lia. }
    rewrite e_meta_other by exact Hxm. unfold mr_set_links, p_next, p_prev. destruct (Z.eqb_spec x fh); [contradiction|]. rewrite Hn. cbn [negb andb].
    constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W].
    - destruct (Z.eqb_spec x nxf) as [E|NE].
      + rewrite E at 1. exact (HMnx Hn).
      + eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact P]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - destruct (Z.eqb_spec x pvf) as [E|NE].
      + rewrite E at 1. exact (HMpv Hn).
      + eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact N]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Me]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Av]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Fr]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
    - eapply cell_agree; [unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Wc]. eapply agree_on_mono; [exact AG|]; cbn; intros; lia.
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMfmh HMnx HMpv HMm8 HMm0 HMgrow HMwr Hsp Hnn HREP HWF sp M L RN.
    pose proof fh_rng as [MR1 MR2].
    constructor.
    - apply (rep_statics_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|W]].
      + ceil; unfold CTX in *; lia.
      + destruct (metaU_rng st L HWF x Ux). unfold HEAPLO, CTX in *; lia.
      + unfold ctx_free_meta_head, CTX in *; lia.
    - apply (rep_ctx_tr st st' M M' HREP (dkeep_of_grows _ _ _ HMgrow) (fun _ => false) true); try reflexivity.
      + intros a Hr (Ha & NA & NF). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a Hr NE) as [W|[(x & Ux & _ & W)|W]].
        * ceil; unfold CTX_END, CTX in *; lia.
        * destruct (metaU_rng st L HWF x Ux). unfold HEAPLO, CTX_END, CTX in *; lia.
        * apply NF. split; [reflexivity | exact W].
      + intros s Hs. right. split; reflexivity.
      + left. split; [reflexivity|]. rewrite e_ctx_fhead. exact HMfmh.
    - apply (rep_areas_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow) XMp); try reflexivity.
      + intros ar a Har Ha NE. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (wr_cases a ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[(x & Ux & Hx & W)|W]].
        * ceil; lia.
        * exists x. split; [exact Ux|]. split; [|exact W]. unfold XMp.
          destruct Hx as [->|[Hn [->| ->]]]; rewrite ?Z.eqb_refl, ?Hn; cbn; rewrite ?Bool.orb_true_r; reflexivity.
        * unfold ctx_free_meta_head, CTX, HEAPLO in *; lia.
      + intros x Ux X. unfold XMp in X. destruct (Z.eqb_spec x fh) as [->|Hxm]; [exact t_rep_meta_fh|].
        cbn [orb] in X. revert X. case_bool single En; intros X; [discriminate X|]. cbn [negb andb] in X.
        apply t_rep_meta_end; [exact En|].
        destruct (Z.eqb_spec x pvf); [left; assumption|]. destruct (Z.eqb_spec x nxf); [right; assumption|]. discriminate X.
      + intros x Ux X. unfold XMp in X. apply Bool.orb_false_elim in X. destruct X as [X1 X2].
        apply p_meta_other.
        * intros ->. rewrite Z.eqb_refl in X1. discriminate X1.
        * intros Hn ->. rewrite Hn, Z.eqb_refl in X2. discriminate X2.
        * intros Hn ->. rewrite Hn, Z.eqb_refl, Bool.orb_true_r in X2. discriminate X2.
    - apply (rep_groups_tr st st' L M M' HWF HREP (dkeep_of_grows _ _ _ HMgrow)).
      + intros x Hx. apply e_is_group. exact Hx.
      + intros x Hx. apply e_is_group in Hx. rewrite (p_meta_group x Hx). repeat split; reflexivity.
      + intros x Hx E. apply e_is_group in Hx. apply (x_endb st st' L SLp HWF); [exact Hx|]. exact E.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. apply e_is_group in Hx. apply (x_gcell st st' L SLp HWF) in G; [|exact Hx].
        pose proof (gcell_in_span st L HWF x a Hx G) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (wr_cases a ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[(y & Uy & _ & W)|W]].
        * ceil; lia.
        * exact (gcell_not_meta st L HWF x y a Hx G Uy W).
        * unfold ctx_free_meta_head, CTX, HEAPLO in *; lia.
      + intros x a Hx G. left. apply (x_gcell st st' L SLp HWF); [apply e_is_group; exact Hx|]. exact G.
  Qed.

  Theorem flpop_close : WF st' L /\ REP st' M'.
  Proof using HMfmh HMnx HMpv HMm8 HMm0 HMgrow HMwr Hsp Hnn HREP HWF sp M. split; [exact t_WF | exact t_REP]. Qed.
End FlPop.
