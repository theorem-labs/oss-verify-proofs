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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhExtS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition cx_set_ctr (cx : ctx_rec) (c : Z) : ctx_rec :=
  CX (c_secret cx) c (c_free_head cx) (c_avail_meta cx) (c_avail_cnt cx)
     (c_area_cnt cx) (c_shift cx) (c_area_head cx) (c_area_tail cx) (c_cursor cx)
     (c_active cx) (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) (c_brk cx).

Section Big.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (m a ml ctr' : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HU : metaU st m.
  Hypothesis HNG : ~ is_group st m.
  Hypothesis Hunl : ~ listed st m.
  Hypothesis HNF : ~ fresh st m.
  Hypothesis Hlimbo : In m (s_limbo st).
  Hypothesis Hmz : s_meta st m = meta_zero.
  Hypothesis Ha : a mod 4096 = 0 /\ HEAPLO <= a /\ a + 4096 * ml <= CEIL.
  Hypothesis Haimg : a + 4096 * ml <= IMG_LO \/ IMG_HI <= a.
  Hypothesis Hml : 0 < ml /\ 4096 * ml <= 2 ^ 35.
  Hypothesis Hapart : forall r, In r (s_regions st) -> rg_base r + rg_len r <= a \/ a + 4096 * ml <= rg_base r.
  Hypothesis Hctr' : 0 <= ctr' < 2 ^ 32.
  #[local] Notation len := (4096 * ml).
  #[local] Notation cx := (s_ctx st).
  #[local] Notation areas := (s_areas st).
  #[local] Notation regions := (s_regions st).

  Definition W : Z := mkW 0 1 63 ml.
  Definition b_meta (x : Z) : meta_rec := if x =? m then MR 0 0 a 0 0 W else s_meta st x.
  Definition b_kind (x : Z) : gkind := if x =? m then GTop else s_kind st x.
  Definition b_ai (x : Z) : Z := if x =? m then 0 else s_ai st x.
  Definition b_slot (x k : Z) : slot_st := if x =? m then SJunk 0 else s_slot st x k.
  Definition r_new : region := RG a len (RGroup m).
  Definition st' : mst :=
    MST (cx_set_ctr cx ctr') areas b_meta (s_flist st) (s_alist st) (m :: s_groups st)
        b_ai b_kind b_slot (r_new :: regions) (s_brk st) (s_canary st) (s_errno st) (zremove m (s_limbo st)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma W_fields : w_lastidx W = 0 /\ w_freeable W = 1 /\ w_sizeclass W = 63 /\ w_maplen W = ml.
  Proof using Hml. unfold W. apply mkW_fields; lia. Qed.
  Lemma W_rng : 0 <= W < 2 ^ 64.
  Proof using Hml. unfold W, mkW. lia. Qed.
  Lemma a_rng : 0 < a /\ a mod 16 = 0 /\ HEAPLO <= a /\ a + len <= CEIL /\ 4096 <= len.
  Proof using Hctr' Hml Ha ctr'.
    destruct Ha as (A1 & A2 & A3). ceil; unfold HEAPLO in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; try lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma m_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0.
  Proof using HU HWF L st. exact (metaU_rng st L HWF m HU). Qed.
  Lemma grp_ne : forall x, is_group st x -> x <> m.
  Proof using HNG. intros x Hx ->. exact (HNG Hx). Qed.
  Lemma grp_neb : forall x, is_group st x -> (x =? m) = false.
  Proof using HNG. intros x Hx. apply Z.eqb_neq. exact (grp_ne x Hx). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_areas : s_areas st' = areas. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = m :: s_groups st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = r_new :: regions. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = zremove m (s_limbo st). Proof using. reflexivity. Qed.


  Lemma e_meta : forall x, s_meta st' x = b_meta x. Proof using. reflexivity. Qed.
  Lemma e_meta_old : forall x, x <> m -> s_meta st' x = s_meta st x.
  Proof using. intros x Hx. rewrite e_meta. unfold b_meta. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_meta_grp : forall x, is_group st x -> s_meta st' x = s_meta st x.
  Proof using HNG. intros x Hx. apply e_meta_old. exact (grp_ne x Hx). Qed.
  Lemma e_meta_m : s_meta st' m = MR 0 0 a 0 0 W.
  Proof using. rewrite e_meta. unfold b_meta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_kind_old : forall x, x <> m -> s_kind st' x = s_kind st x.
  Proof using. intros x Hx. cbn. unfold b_kind. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_kind_m : s_kind st' m = GTop.
  Proof using. cbn. unfold b_kind. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_ai_old : forall x, x <> m -> s_ai st' x = s_ai st x.
  Proof using. intros x Hx. cbn. unfold b_ai. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_ai_m : s_ai st' m = 0.
  Proof using. cbn. unfold b_ai. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_old : forall x k, x <> m -> s_slot st' x k = s_slot st x k.
  Proof using. intros x k Hx. cbn. unfold b_slot. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_slot_m : forall k, s_slot st' m k = SJunk 0.
  Proof using. intros k. cbn. unfold b_slot. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> x = m \/ is_group st x.
  Proof using. intros x. unfold is_group. rewrite e_groups. cbn. split; intros [A|A]; auto. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using Hctr' Hml Haimg Ha RN. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using Hctr' Hml Haimg Ha RN. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using Hctr' Hml Haimg Ha RN. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x.
  Proof using Hctr' Hml Haimg Ha RN. intros x. unfold listed. rewrite e_in_alist, e_in_flist. tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x.
  Proof using Hctr' Hml Haimg Ha RN. intros x. unfold fresh. cbn [s_ctx st' cx_set_ctr c_avail_cnt s_areas]. tauto. Qed.
  Lemma e_areab : forall x, areab st' x <-> areab st x. Proof using Hctr' Hml Haimg Ha RN. intros; unfold areab; rewrite e_areas; tauto. Qed.

  (* [comment removed for export] *)
  Lemma n_gW : g_W st' m = W. Proof using. unfold g_W. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_gmem : g_mem st' m = a. Proof using. unfold g_mem. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_glast : g_lastidx st' m = 0. Proof using Hml. unfold g_lastidx. rewrite n_gW. exact (proj1 W_fields). Qed.
  Lemma n_gcnt : g_cnt st' m = 1. Proof using Hml. unfold g_cnt. rewrite n_glast. reflexivity. Qed.
  Lemma n_gsc : g_sc st' m = 63. Proof using Hml. unfold g_sc. rewrite n_gW. exact (proj1 (proj2 (proj2 W_fields))). Qed.
  Lemma n_gml : g_maplen st' m = ml. Proof using Hml. unfold g_maplen. rewrite n_gW. exact (proj2 (proj2 (proj2 W_fields))). Qed.
  Lemma n_gstride : g_stride st' m = len - 16.
  Proof using Hml.
    unfold g_stride, slot_stride. rewrite n_gml, n_glast, n_gsc.
    replace (negb (ml =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia). cbn [Z.eqb andb]. unfold UNIT. lia.
  Qed.
  Lemma n_gss : forall k, g_slot_start st' m k = a + 16 + (len - 16) * k.
  Proof using Hml. intros k. unfold g_slot_start, UNIT. rewrite n_gmem, n_gstride. reflexivity. Qed.
  Lemma n_gse : forall k, g_slot_end st' m k = a + 16 + (len - 16) * k + (len - 16) - 4.
  Proof using Hml. intros k. unfold g_slot_end, IB. rewrite n_gss, n_gstride. reflexivity. Qed.
  Lemma n_gspan : gspan st' m = a + len - 3.
  Proof using Hml. unfold gspan, g_span_end, UNIT, IB. rewrite n_gmem, n_gstride, n_gcnt. lia. Qed.
  Lemma n_avail : mr_avail (s_meta st' m) = 0. Proof using. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_freed : mr_freed (s_meta st' m) = 0. Proof using. rewrite e_meta_m. reflexivity. Qed.

  Lemma SG : sub_groups st st'.
  Proof using HNG.
    constructor.
    - intros x Hx. apply e_is_group. right. exact Hx.
    - intros x Hx. apply e_kind_old. exact (grp_ne x Hx).
    - intros x k Hx. rewrite e_slot_old by exact (grp_ne x Hx). apply slot_sim_refl.
    - intros x Hx. rewrite e_meta_grp by exact Hx. reflexivity.
    - intros x Hx. rewrite e_meta_grp by exact Hx. reflexivity.
  Qed.
  #[local] Notation yG := (SG).
  Lemma e_gW : forall x, is_group st x -> g_W st' x = g_W st x. Proof using HNG. exact (u_gW st st' yG). Qed.
  Lemma e_gmem : forall x, is_group st x -> g_mem st' x = g_mem st x. Proof using HNG. exact (u_gmem st st' yG). Qed.
  Lemma e_glast : forall x, is_group st x -> g_lastidx st' x = g_lastidx st x. Proof using HNG. exact (u_glast st st' yG). Qed.
  Lemma e_gcnt : forall x, is_group st x -> g_cnt st' x = g_cnt st x. Proof using HNG. exact (u_gcnt st st' yG). Qed.
  Lemma e_gsc : forall x, is_group st x -> g_sc st' x = g_sc st x. Proof using HNG. exact (u_gsc st st' yG). Qed.
  Lemma e_gml : forall x, is_group st x -> g_maplen st' x = g_maplen st x. Proof using HNG. exact (u_gml st st' yG). Qed.
  Lemma e_gstride : forall x, is_group st x -> g_stride st' x = g_stride st x. Proof using HNG. exact (u_gstride st st' yG). Qed.
  Lemma e_gss : forall x k, is_group st x -> g_slot_start st' x k = g_slot_start st x k. Proof using HNG. exact (u_gss st st' yG). Qed.
  Lemma e_gse : forall x k, is_group st x -> g_slot_end st' x k = g_slot_end st x k. Proof using HNG. exact (u_gse st st' yG). Qed.
  Lemma e_gspan : forall x, is_group st x -> gspan st' x = gspan st x. Proof using HNG. exact (u_gspan st st' yG). Qed.
  Lemma e_avail : forall x, is_group st x -> mr_avail (s_meta st' x) = mr_avail (s_meta st x). Proof using HNG. intros; rewrite e_meta_grp by assumption; reflexivity. Qed.
  Lemma e_freed : forall x, is_group st x -> mr_freed (s_meta st' x) = mr_freed (s_meta st x). Proof using HNG. intros; rewrite e_meta_grp by assumption; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma old_apart : forall x, is_group st x -> gspan st x <= a \/ a + len <= g_mem st x.
  Proof using Hapart HWF L RN.
    intros x Hx. destruct (ge_inreg st (WF_geom st L HWF) x Hx) as (r & Hr & R1 & R2).
    destruct (Hapart r Hr); [left | right]; lia.
  Qed.
  Lemma area_apart : forall ar, In ar areas -> ar + 4096 <= a \/ a + len <= ar.
  Proof using Hapart HWF L RN.
    intros ar Har. destruct (area_in_region st L HWF ar Har) as (r & Hr & _ & R1 & R2).
    destruct (Hapart r Hr); [left | right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma n_gcell : forall x, gcell st' m x -> (a <= x < a + 16) \/ x = a + len - 4.
  Proof using Hctr' Hml Ha RN.
    intros x G. pose proof a_rng as (_ & _ & _ & _ & L4). unfold gcell in G.
    rewrite n_gmem, n_gcnt, n_glast in G.
    destruct G as [G|[G|[G|G]]].
    - left. lia.
    - destruct G as (k & Hk & E & _). rewrite n_gss in E.
      assert (k = 0 \/ k = 1) as [->| ->] by lia; [left | right]; lia.
    - destruct G as (k & q & Hk & Hq & R). assert (k = 0) as -> by lia.
      unfold slot_ptr in Hq. rewrite e_slot_m, n_gss in Hq. injection Hq. intros <-. left. lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & _). rewrite e_slot_m in Hs. discriminate Hs.
  Qed.
  Lemma n_garbage : forall k x, garbage st' m k x -> a + 16 <= x < a + len - 4.
  Proof using Hml.
    intros k x G. unfold garbage in G. rewrite n_glast, e_slot_m, n_gss, n_gse in G. destruct G as [Hk G].
    assert (k = 0) as -> by lia. lia.
  Qed.
  Lemma n_nouser : forall x k q n o r, is_group st' x -> ~ is_group st x -> s_slot st' x k <> SUser q n o r.
  Proof using.
    intros x k q n o r Hx NG. apply e_is_group in Hx. destruct Hx as [->|Hx]; [|exfalso; exact (NG Hx)].
    rewrite e_slot_m. discriminate.
  Qed.
  Lemma e_appb : forall x, appb st' x <-> appb st x.
  Proof using HNG.
    intros x. split; [apply (u_appb_back st st' yG); exact n_nouser | apply (u_appb st st' yG)].
  Qed.
  Lemma old_gcell_apart : forall x y, is_group st x -> gcell st x y -> y < a \/ a + len <= y.
  Proof using Hapart HWF L RN.
    intros x y Hx G. pose proof (gcell_in_span st L HWF x y Hx G). destruct (old_apart x Hx); lia.
  Qed.
  Lemma old_garbage_apart : forall x k y, is_group st x -> garbage st x k y -> y < a \/ a + len <= y.
  Proof using Hapart HWF L RN.
    intros x k y Hx G. pose proof (garbage_in_span st L HWF x k y Hx G). destruct (old_apart x Hx); lia.
  Qed.
  Lemma old_appb_apart : forall y, appb st y -> y < a \/ a + len <= y.
  Proof using Hapart HWF L RN.
    intros y Ap. destruct (appb_in_span st L HWF y Ap) as (x & Hx & R). destruct (old_apart x Hx); lia.
  Qed.
  Lemma areab_apart : forall y, areab st y -> y < a \/ a + len <= y.
  Proof using Hapart HWF L RN.
    intros y (ar & Har & R). destruct (area_apart ar Har); lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using Hctr' HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat]; try assumption.
    intros Hac. destruct (A8 Hac) as (b & l & e & Hin & He & E1 & E2). exists b, l, e. split; [right; exact Hin|]. repeat split; assumption.
  Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HWF L.
    destruct (WF_areas st L HWF) as [A B C D]. constructor; rewrite ?e_areas, ?e_regions, ?e_brk; try assumption.
    intros ar Har. destruct (D ar Har) as [(b & l & Hin & H1 & H2 & H3)|(b & l & e & Hin & H1 & H2)].
    - left. exists b, l. split; [right; exact Hin|]. repeat split; assumption.
    - right. exists b, l, e. split; [right; exact Hin|]. split; assumption.
  Qed.

  Lemma listed_ne : forall x, listed st x -> x <> m.
  Proof using Hunl. intros x Hl ->. exact (Hunl Hl). Qed.
  Lemma alist_grp : forall sc x, In x (s_alist st sc) -> is_group st x.
  Proof using HWF L RN. intros sc x Hin. exact (proj1 (proj2 (wl_aU st (WF_lists st L HWF) sc x Hin))). Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hctr' Hml Haimg Ha Hunl HNG HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist.
    - apply (dll_ext st st'); [|exact D1]. intros x Hx. rewrite e_meta_old by (apply listed_ne; left; exact Hx). split; reflexivity.
    - exact ND1.
    - intros x Hx. pose proof (FU x Hx) as (U & NG & NF & R). rewrite e_metaU, e_is_group, e_fresh, e_meta_old by (apply listed_ne; left; exact Hx).
      split; [exact U|]. split; [|split; [exact NF | exact R]]. intros [->|G]; [exact (Hunl (or_introl Hx)) | exact (NG G)].
    - intros sc Hsc. apply (dll_ext st st'); [|exact (D2 sc Hsc)]. intros x Hx. rewrite e_meta_grp by exact (alist_grp sc x Hx). split; reflexivity.
    - exact ND2.
    - intros sc x Hin. rewrite e_is_group, e_gsc by exact (alist_grp sc x Hin). pose proof (AU sc x Hin) as (X1 & X2 & X3). auto.
    - exact AN.
    - intros x U NL. rewrite e_listed in NL. apply e_metaU in U. rewrite e_meta. unfold b_meta.
      destruct (Z.eqb_spec x m) as [->|Hx]; [split; reflexivity | exact (LK x U NL)].
    - intros x Hl. rewrite e_listed in Hl. rewrite e_meta_old by exact (listed_ne x Hl). exact (LKD x Hl).
    - intros sc x Hin Hne. rewrite e_avail, e_freed by exact (alist_grp sc x Hin). exact (RS sc x Hin Hne).
  Qed.

  Lemma t_wf_group_old : forall x, is_group st x -> wf_group st' L x.
  Proof using Hctr' Hml Haimg Ha HNG HWF RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG. pose proof (grp_ne x Hx) as Hxm.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_alist, ?e_avail, ?e_freed by exact Hx;
      rewrite ?(e_ai_old x Hxm), ?(e_kind_old x Hxm); try assumption.
    - intros k Hk. rewrite e_slot_old by exact Hxm. exact (Av k Hk).
    - intros k Hk. rewrite e_slot_old by exact Hxm. exact (Fr k Hk).
    - intros k Hk. rewrite e_slot_old by exact Hxm. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot_old by exact Hxm. exact (High k Hk).
    - intros Hall Hne. rewrite e_listed. apply Full; [|exact Hne]. intros k Hk. rewrite <- (e_slot_old x k Hxm). exact (Hall k Hk).
    - destruct (s_kind st x) as [|hm j hoff].
      + destruct Kind as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [rewrite e_regions; right; exact K2|]. split; assumption.
      + destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride by exact K2. rewrite e_slot_old by exact (grp_ne hm K2).
        assert (HG : is_group st' hm) by (apply e_is_group; right; exact K2).
        repeat (split; [assumption|]). assumption.
    - intros Hall. assert (X : s_kind st x = GTop /\ g_sc st x < 48 /\ In x (s_alist st (g_sc st x))).
      { apply FF. intros k Hk. rewrite <- (e_slot_old x k Hxm). exact (Hall k Hk). }
      exact X.
    - intros k Hk. rewrite e_slot_old by exact Hxm. apply (u_slot_wf_same st st' L yG); [exact Hx|]. exact (Slots k Hk).
    - apply (u_depth st st' L yG HWF); [exact Hx | exact Depth].
    - intros Hsc Hst k Hk. rewrite e_slot_old by exact Hxm. exact (Fit Hsc Hst k Hk).
  Qed.


  Lemma t_wf_group_new : wf_group st' L m.
  Proof using Hctr' Hml Haimg Ha HNF Hunl HU RN.
    pose proof a_rng as (R0 & R16 & Rlo & Rhi & L4). pose proof W_rng as WR. pose proof W_fields as (F1 & F2 & F3 & F4).
    constructor; rewrite ?n_gW, ?n_gmem, ?n_glast, ?n_gcnt, ?n_gsc, ?n_gml, ?n_gstride, ?e_alist, ?n_avail, ?n_freed, ?e_ai_m, ?e_kind_m.
    - apply e_metaU. exact HU.
    - rewrite e_fresh. exact HNF.
    - exact WR.
    - lia.
    - lia.
    - ceil; unfold UNIT in *. split; [lia|]. split; [exact R16 | lia].
    - lia.
    - exact F2.
    - right. split; [reflexivity|]. split; [reflexivity | lia].
    - split; [lia|]. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold HEAPLO in *. clear - Ha Hml. lia.
    - intros k Hk. rewrite Z.bits_0. split; [intros E; discriminate E | intros [_ E]; rewrite e_slot_m in E; discriminate E].
    - intros k Hk. rewrite Z.bits_0. split; [intros E; discriminate E | intros [_ E]; rewrite e_slot_m in E; discriminate E].
    - intros k Hk E. rewrite e_slot_m in E. discriminate E.
    - intros k Hk. lia.
    - intros Hl. exfalso. apply Hunl. right. apply e_in_alist. exact Hl.
    - rewrite e_in_flist. intros F. apply Hunl. left. exact F.
    - intros _. rewrite e_listed. exact Hunl.
    - lia.
    - intros _ _. rewrite e_listed. exact Hunl.
    - split; [lia|]. split; [rewrite e_regions; left; reflexivity|]. split; [exact (proj1 Ha) | unfold UNIT; lia].
    - lia.
    - intros Hall. exfalso. destruct (Hall 0 ltac:(lia)) as [E|E]; rewrite e_slot_m in E; discriminate E.
    - intros k Hk. rewrite e_slot_m. cbn [slot_wf]. rewrite n_gss, n_gstride. split; [lia|]. split; [unfold IB; lia|].
      unfold ptr_ok, inband. rewrite n_gmem, n_gsc, n_gml. unfold UNIT.
      assert (k = 0) as -> by lia.
      replace (a + 16 + (len - 16) * 0 + 16 * 0 - a - 16) with 0 by lia. change (0 / 16) with 0. change (0 mod 16) with 0.
      repeat split; lia.
    - destruct (dbound _); cbn; unfold b_kind; rewrite Z.eqb_refl; exact I.
    - lia.
    - lia.
    - lia.
    - lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hctr' Hml Haimg Ha HNF Hunl HNG HU HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - apply base.NoDup_cons_2; [|exact ND]. intros E. apply HNG. apply (proj1 (base.list_elem_of_In _ _) E).
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx]; [exact t_wf_group_new | exact (t_wf_group_old x Hx)].
    - intros m1 m2 H1 H2. apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; [rewrite e_ai_m, n_glast; intros; lia|].
      destruct H2 as [->|H2]; [rewrite e_ai_m, n_glast; intros; lia|].
      rewrite (e_ai_old m1 (grp_ne m1 H1)), (e_ai_old m2 (grp_ne m2 H2)). rewrite !e_glast, !e_gsc by assumption. exact (ONE m1 m2 H1 H2).
    - intros b l x [E|Hin].
      + unfold r_new in E. injection E. intros <- <- <-. rewrite e_is_group, e_kind_m, n_gmem, n_gml. repeat split; auto.
      + pose proof (REG b l x Hin) as (G & K & E1 & E2).
        rewrite e_is_group, (e_kind_old x (grp_ne x G)), e_gmem, e_gml by exact G. repeat split; auto.
    - intros x F. rewrite e_fresh in F. rewrite e_meta_old; [exact (FR0 x F)|]. intros ->. exact (HNF F).
    - intros x U NG NFL NFR. rewrite e_is_group in NG. apply e_metaU in U. rewrite e_in_flist in NFL. rewrite e_fresh in NFR.
      apply zremove_In. split; [apply (OTH x U); tauto|]. intros ->. apply NG. left. reflexivity.
    - intros x Hl. apply zremove_In in Hl. destruct Hl as [Hl Hxm]. destruct (LIM x Hl) as (A & B & C & D).
      rewrite e_metaU, e_is_group, e_fresh, e_listed. split; [exact A|]. split; [intros [E|E]; [exact (Hxm E) | exact (B E)]|]. split; assumption.
    - intros m1 m2 H1 H2 G1 G2 E. apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; [exfalso; destruct (G1 0 ltac:(rewrite n_glast; lia)) as [F|F]; rewrite e_slot_m in F; discriminate F|].
      destruct H2 as [->|H2]; [exfalso; destruct (G2 0 ltac:(rewrite n_glast; lia)) as [F|F]; rewrite e_slot_m in F; discriminate F|].
      rewrite !e_gsc in E by assumption. rewrite e_glast in G1 by exact H1. rewrite e_glast in G2 by exact H2.
      apply (ONEFF m1 m2 H1 H2); [intros k Hk | intros k Hk | exact E].
      + rewrite <- (e_slot_old m1 k (grp_ne m1 H1)). exact (G1 k Hk).
      + rewrite <- (e_slot_old m2 k (grp_ne m2 H2)). exact (G2 k Hk).
  Qed.
  Lemma t_wf_geom : wf_geom st'.
  Proof using Hctr' Hapart Hml Haimg Ha HNG HWF L RN.
    pose proof a_rng as (R0 & R16 & Rlo & Rhi & L4).
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN]. constructor; rewrite ?e_regions.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + exists r_new. split; [left; reflexivity|]. unfold r_new. cbn [rg_base rg_len]. rewrite n_gmem, n_gspan. lia.
      + rewrite e_gmem, e_gspan by exact Hx.
        destruct (INR x Hx) as (r & Hr & R1 & R2). exists r. split; [right; exact Hr|]. split; assumption.
    - intros m1 m2 y H1 H2 Hne G1 G2. apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; destruct H2 as [->|H2].
      + exact (Hne eq_refl).
      + apply (u_gcell st st' L yG HWF) in G2; [|exact H2]. pose proof (n_gcell y G1). destruct (old_gcell_apart m2 y H2 G2); lia.
      + apply (u_gcell st st' L yG HWF) in G1; [|exact H1]. pose proof (n_gcell y G2). destruct (old_gcell_apart m1 y H1 G1); lia.
      + apply (u_gcell st st' L yG HWF) in G1; [|exact H1]. apply (u_gcell st st' L yG HWF) in G2; [|exact H2]. eauto.
    - intros x y Hx R Ar. apply e_areab in Ar. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + rewrite n_gmem, n_gspan in R. destruct (areab_apart y Ar); lia.
      + rewrite e_gmem, e_gspan in R by exact Hx. exact (AREA x y Hx R Ar).
    - intros x y Hx G Ap. apply e_appb in Ap. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + pose proof (n_gcell y G). destruct (old_appb_apart y Ap); lia.
      + apply (u_gcell st st' L yG HWF) in G; [|exact Hx]. eauto.
    - intros y Ap Ar. apply e_appb in Ap. apply e_areab in Ar. eauto.
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; [rewrite e_slot_m in S1; discriminate S1|].
      destruct H2 as [->|H2]; [rewrite e_slot_m in S2; discriminate S2|].
      rewrite e_glast in Hk1 by exact H1. rewrite e_glast in Hk2 by exact H2.
      rewrite e_slot_old in S1 by exact (grp_ne m1 H1). rewrite e_slot_old in S2 by exact (grp_ne m2 H2). eauto.
    - intros x k y x2 Hx G H2 C. apply e_is_group in Hx. apply e_is_group in H2.
      destruct Hx as [->|Hx]; destruct H2 as [->|H2].
      + pose proof (n_garbage k y G). pose proof (n_gcell y C). lia.
      + pose proof (n_garbage k y G). apply (u_gcell st st' L yG HWF) in C; [|exact H2]. destruct (old_gcell_apart x2 y H2 C); lia.
      + apply (u_garbage st st' L yG HWF) in G; [|exact Hx]. pose proof (n_gcell y C). destruct (old_garbage_apart x k y Hx G); lia.
      + apply (u_garbage st st' L yG HWF) in G; [|exact Hx]. apply (u_gcell st st' L yG HWF) in C; [|exact H2]. eauto.
    - intros x k y Hx G Ap. apply e_appb in Ap. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + pose proof (n_garbage k y G). destruct (old_appb_apart y Ap); lia.
      + apply (u_garbage st st' L yG HWF) in G; [|exact Hx]. eauto.
    - intros x k y Hx G Ar. apply e_areab in Ar. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + pose proof (n_garbage k y G). destruct (areab_apart y Ar); lia.
      + apply (u_garbage st st' L yG HWF) in G; [|exact Hx]. eauto.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + rewrite e_kind_m, n_gspan, n_gmem, n_gml. lia.
      + rewrite (e_kind_old x (grp_ne x Hx)), e_gspan, e_gmem, e_gml by exact Hx.
        pose proof (SPAN x Hx) as SP. destruct (s_kind st x) as [|hm j o] eqn:K; [exact SP|].
        pose proof (u_host_group st L HWF x hm j o Hx K) as Hh. rewrite e_gss, e_gse by exact Hh. exact SP.
  Qed.

  Lemma t_wf_live : wf_live st' L.
  Proof using Hml HNG HWF RN.
    apply (wf_live_sub st st' L yG); [exact n_nouser | | exact (WF_live st L HWF)].
    intros x Hx NG. apply e_is_group in Hx. destruct Hx as [->|Hx]; [exact n_glast | exfalso; exact (NG Hx)].
  Qed.

  Lemma r_new_notin : ~ In r_new regions.
  Proof using Hapart Hml. intros Hin. destruct (Hapart r_new Hin) as [A|A]; unfold r_new in A; cbn [rg_base rg_len] in A; lia. Qed.

  Lemma filter_cons_false : forall (f : region -> bool) r l, f r = false -> List.filter f (r :: l) = List.filter f l.
  Proof using. intros f r l E. cbn. rewrite E. reflexivity. Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using Hctr' Hapart Hml Ha HNG HWF L.
    pose proof a_rng as (R0 & R16 & Rlo & Rhi & L4).
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL]. constructor; rewrite ?e_regions, ?e_brk, ?e_areas.
    - intros r [<-|Hr]; [|exact (RNG r Hr)]. unfold r_new. cbn [rg_base rg_len].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; try lia.
    - intros r1 r2 [<-|H1] [<-|H2] Hne.
      + exact (False_ind _ (Hne eq_refl)).
      + unfold r_new. cbn [rg_base rg_len]. destruct (Hapart r2 H2); lia.
      + unfold r_new. cbn [rg_base rg_len]. destruct (Hapart r1 H1); lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply base.NoDup_cons_2; [|exact ND]. intros E. apply r_new_notin. apply (proj1 (base.list_elem_of_In _ _) E).
    - intros r [<-|Hr]; [unfold r_new; cbn [rg_len]; lia | exact (LEN r Hr)].
    - intros b l x [E|Hin].
      + unfold r_new in E. injection E. intros <- <- <-. rewrite n_gsc. lia.
      + pose proof (proj1 (wG_regions st L (WF_groups st L HWF) b l x Hin)) as G. rewrite e_gsc by exact G. exact (GB b l x Hin).
    - intros b l x [E|Hin].
      + unfold r_new in E. injection E. intros <- <- <-. intros _. right. exists 0. apply e_slot_m.
      + pose proof (proj1 (wG_regions st L (WF_groups st L HWF) b l x Hin)) as G. rewrite e_gsc by exact G.
        intros H63. cbn [s_slot st']. unfold b_slot. rewrite (grp_neb x G). exact (G63 b l x Hin H63).
    - intros b l e [E|Hin]; [unfold r_new in E; discriminate E | exact (MT b l e Hin)].
    - rewrite filter_cons_false by reflexivity. exact MC.
    - destruct (s_brk st) as [|b0 b gk|gd].
      + intros b l [E|Hin]; [unfold r_new in E; discriminate E | exact (BRK b l Hin)].
      + destruct BRK as (B1 & B2 & B3). split; [intros b' l [E|Hin]; [unfold r_new in E; discriminate E | exact (B1 b' l Hin)]|].
        rewrite filter_cons_false by reflexivity. split; [exact B2 | right; exact B3].
      + destruct BRK as [B1 B2]. rewrite filter_cons_false by reflexivity. split; [exact B1|].
        destruct gd as [[b0 gk]|]; [right; exact B2 | exact I].
    - intros b l [E|Hin]; [unfold r_new in E; discriminate E | exact (BL b l Hin)].
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using Haimg HWF L RN.
    destruct (WF_img st L HWF) as [WA WR]. constructor; rewrite ?e_regions, ?e_areas.
    - exact WA.
    - intros r [<-|Hr]; [unfold r_new; cbn [rg_base rg_len]; exact Haimg | exact (WR r Hr)].
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma t_WF : WF st' L.
  Proof using Hctr' Hapart Hml Haimg Ha HNF Hunl HNG HU HWF.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (spl sph : Z).
  Hypothesis Hspl : CEIL <= spl.
  Definition b_wr (y : Z) : Prop :=
    (m <= y < m + 40) \/ (a <= y < a + len) \/ (ctx_mmap_counter <= y < ctx_mmap_counter + 4) \/ (spl <= y < sph).
  Hypothesis HMwr : forall y, 0 <= y < 2 ^ 64 -> M' (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> b_wr y.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMmeta : rep_meta M' m (MR 0 0 a 0 0 W).
  Hypothesis HMa : cell M' a 8 m.
  Hypothesis HMz : forall y, a + 8 <= y < a + len -> M' (Z_to_bv 64 y) = Some (Z_to_bv 8 0).
  Hypothesis HMdef : defined M' a (a + len).
  Hypothesis HMctr : cell M' ctx_mmap_counter 4 ctr'.

  Lemma HMkeep : forall y, dfoot st y -> M (Z_to_bv 64 y) <> None -> M' (Z_to_bv 64 y) <> None.
  Proof using HMgrow. exact (dkeep_of_grows st M M' HMgrow). Qed.

  Lemma HMlow : agree_on (fun y => IMG_LO <= y < CTX) M M'.
  Proof using HMwr Hspl sph spl Hctr' Hml Haimg Ha HU HWF ctr' ml a m L st RN.
    intros y Hr Hy. destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
    pose proof m_rng. pose proof a_rng. cbv beta in Hy.
    destruct (HMwr y Hr NE) as [X|[X|[X|X]]]; ceil; unfold ctx_mmap_counter, CTX, HEAPLO in *; lia.
  Qed.

  Lemma t_rep_statics : rep_statics st' M'.
  Proof using HMgrow HMwr Hspl sph spl Hctr' Hml Haimg Ha HU HREP HWF M L RN. apply (rep_statics_tr st st' M M' HREP HMkeep HMlow); reflexivity. Qed.

  Lemma t_rep_ctx : rep_ctx st' M'.
  Proof using HMctr HMwr Hspl sph spl Hctr' Hml Haimg Ha HU HREP HWF M L RN.
    pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
    pose proof m_rng as MR. pose proof a_rng as AR.
    assert (TR : forall y k v, CTX <= y -> y + Z.of_nat k <= CTX_END ->
              (y + Z.of_nat k <= ctx_mmap_counter \/ ctx_mmap_counter + 4 <= y) ->
              cell M y k v -> cell M' y k v).
    { intros y k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
      intros z Hz Rz. cbv beta in Rz. destruct (decide (M' (Z_to_bv 64 z) = M (Z_to_bv 64 z))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr z Hz NE) as [X|[X|[X|X]]]; ceil; unfold ctx_mmap_counter, CTX_END, CTX, HEAPLO in *; lia. }
    Ltac ctxg TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | eauto ].
    constructor; cbn [s_ctx st' cx_set_ctr c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift c_area_head c_area_tail
                      c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try assumption; try (ctxg TR).
    - intros sc Hsc. ctxg TR.
    - intros sc Hsc. ctxg TR.
    - intros i Hi. ctxg TR.
    - intros i Hi. ctxg TR.
  Qed.

  Lemma t_rep_areas : forall ar, In ar (s_areas st') -> rep_area st' M' ar.
  Proof using HMmeta HMgrow HMwr Hspl sph spl Hctr' Hapart Hml Ha HU HREP HWF M L RN.
    apply (rep_areas_tr st st' L M M' HWF HREP HMkeep (fun x => x =? m)); try reflexivity.
    - intros ar y Har Hy NE. pose proof (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
      pose proof m_rng. pose proof a_rng.
      destruct (HMwr y ltac:(ceil; unfold HEAPLO in *; lia) NE) as [X|[X|[X|X]]].
      + exists m. split; [exact HU|]. split; [apply Z.eqb_refl | exact X].
      + exfalso. destruct (area_apart ar Har); lia.
      + exfalso. unfold ctx_mmap_counter, CTX, HEAPLO in *. lia.
      + exfalso. ceil. lia.
    - intros x Ux X. apply Z.eqb_eq in X. subst x. rewrite e_meta_m. exact HMmeta.
    - intros x Ux X. apply Z.eqb_neq in X. exact (e_meta_old x X).
  Qed.

  Lemma t_rep_group_new : rep_group st' M' m.
  Proof using HMdef HMz HMa Hctr' Hml Ha HU HWF L RN.
    pose proof a_rng as (R0 & R16 & Rlo & Rhi & L4). pose proof m_rng as MR.
    constructor; rewrite ?n_gmem, ?e_ai_m, ?n_gcnt, ?n_glast, ?e_kind_m, ?n_gml.
    - exact HMa.
    - exists 0. split; [lia|]. split; [apply HMz; lia | reflexivity].
    - intros i Hi _. rewrite n_gss. apply HMz. assert (i = 0 \/ i = 1) as [->| ->] by lia; lia.
    - exact HMdef.
    - intros i Hi. rewrite e_slot_m. exact I.
  Qed.
  Lemma t_rep_group_old : forall x, is_group st x -> rep_group st' M' x.
  Proof using HMgrow HMwr Hspl sph spl Hctr' Hapart Hml Ha HNG HU HREP HWF M L RN.
    intros x Hx. pose proof (grp_ne x Hx) as Hxm. destruct (group_range st L HWF x Hx) as [X1 X2].
    pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
    pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
    pose proof m_rng as MR. pose proof a_rng as AR.
    assert (SPAN : 0 <= g_mem st x /\ g_mem st x + 16 <= g_span_end st x /\ g_span_end st x < 2 ^ 64).
    { assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; pose proof (glast_rng st x); nia).
      ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia. }
    apply (rep_group_transport st st' M M' x).
    - exact (e_gmem x Hx).
    - exact (e_gcnt x Hx).
    - exact (e_glast x Hx).
    - intros k. exact (e_gss x k Hx).
    - intros k. exact (e_gse x k Hx).
    - exact (e_ai_old x Hxm).
    - intros q. unfold inband. rewrite (e_gmem x Hx). reflexivity.
    - intros E. apply (u_endb st st' L yG HWF x Hx). exact E.
    - rewrite (e_kind_old x Hxm). destruct (s_kind st x); [split; [reflexivity | exact (e_gml x Hx)] | exact I].
    - intros k Hk. left. exact (e_slot_old x k Hxm).
    - intros y G. apply (u_gcell st st' L yG HWF) in G; [|exact Hx].
      destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      pose proof (gcell_in_span st L HWF x y Hx G) as R.
      destruct (HMwr y ltac:(ceil; unfold HEAPLO in *; lia) NE) as [Xw|[Xw|[Xw|Xw]]].
      + exact (gcell_not_meta st L HWF x m y Hx G HU Xw).
      + destruct (old_apart x Hx); lia.
      + unfold ctx_mmap_counter, CTX, HEAPLO in *. lia.
      + ceil. lia.
    - exact HMgrow.
    - exact SPAN.
    - intros y G. apply (u_gcell st st' L yG HWF) in G; [|exact Hx]. exact (gcell_in_span st L HWF x y Hx G).
    - exact (rp_groups st M HREP x Hx).
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMctr HMdef HMz HMa HMmeta HMgrow HMwr Hspl sph spl Hctr' Hapart Hml Haimg Ha HNG HU HREP HWF M L RN.
    constructor.
    - exact t_rep_statics.
    - exact t_rep_ctx.
    - exact t_rep_areas.
    - intros x Hx. apply e_is_group in Hx. destruct (Z.eq_dec x m) as [->|Hxm]; [exact t_rep_group_new|].
      destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|]. exact (t_rep_group_old x Hx).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_ledger : forall vm, LEDGERX st [(Z_to_bv 64 a, Z_to_bv 64 len)] vm -> LEDGER st' vm.
  Proof using.
    intros vm [LM LN LB LR LMB]. constructor; rewrite ?e_regions, ?e_brk.
    - exact LM.
    - unfold noacc_of in *. rewrite e_brk, e_regions. cbn [flat_map noacc_of_region r_new rg_kind]. exact LN.
    - exact LB.
    - exact LR.
    - exact LMB.
  Qed.

  Theorem big_close : WF st' L /\ REP st' M'.
  Proof using HMctr HMdef HMz HMa HMmeta HMgrow HMwr Hspl sph spl Hctr' Hapart Hml Haimg Ha HNF Hunl HNG HU HREP HWF M. split; [exact t_WF | exact t_REP]. Qed.

  (* [comment removed for export] *)
  Lemma big_facts :
    is_group st' m /\ s_slot st' m 0 = SJunk 0 /\ g_lastidx st' m = 0 /\ g_stride st' m = len - 16 /\
    g_slot_start st' m 0 = a + 16 /\ g_sc st' m = 63 /\ s_kind st' m = GTop /\ g_mem st' m = a /\
    (forall b l, In (RG b l (RGroup m)) (s_regions st') -> l = len) /\
    s_limbo st' = zremove m (s_limbo st) /\ s_regions st' = r_new :: s_regions st /\
    (forall x k, is_group st' x -> (x <> m) -> s_slot st' x k = s_slot st x k) /\
    (forall x, is_group st' x <-> x = m \/ is_group st x).
  Proof using Hml HNG HWF L RN.
    split; [apply e_is_group; left; reflexivity|]. split; [apply e_slot_m|]. split; [exact n_glast|]. split; [exact n_gstride|].
    split; [rewrite n_gss; lia|]. split; [exact n_gsc|]. split; [exact e_kind_m|]. split; [exact n_gmem|].
    split.
    { intros b l [E|Hin]; [unfold r_new in E; injection E; intros; subst; reflexivity|].
      exfalso. exact (HNG (proj1 (wG_regions st L (WF_groups st L HWF) b l m Hin))). }
    split; [reflexivity|]. split; [reflexivity|]. split; [intros x k _ Hxm; exact (e_slot_old x k Hxm) | exact e_is_group].
  Qed.
End Big.
