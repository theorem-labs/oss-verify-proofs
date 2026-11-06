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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; lia ] | lia ] ].
Lemma testbit_add_pow2 : forall fr i j, 0 <= fr -> 0 <= i -> 0 <= j -> Z.testbit fr i = false ->
  Z.testbit (fr + 2 ^ i) j = (Z.eqb i j || Z.testbit fr j)%bool.
Proof.
  intros fr i j Hfr Hi Hj Hb.
  assert (Hl : Z.land fr (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit fr i Hfr Hi)); exact Hb).
  rewrite (Z.add_nocarry_lxor fr (2 ^ i) Hl). rewrite Z.lxor_spec, testbit_pow2 by lia.
  destruct (Z.eqb_spec i j) as [<-|Hne]; cbn.
  - rewrite Hb. reflexivity.
  - rewrite Bool.xorb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bits_all_or_ex : forall x kk, 0 <= kk ->
  (forall j, 0 <= j < kk -> Z.testbit x j = true) \/ (exists j, 0 <= j < kk /\ Z.testbit x j = false).
Proof.
  intros x kk Hkk.
  apply (Z.right_induction (fun kk => (forall j, 0 <= j < kk -> Z.testbit x j = true) \/ (exists j, 0 <= j < kk /\ Z.testbit x j = false))
           ltac:(intros a b Hab; subst; tauto) 0); try lia.
  - left. intros j Hj. lia.
  - intros kk' Hkk' [IH|IH].
    + destruct (Z.testbit x kk') eqn:T.
      * left. intros j Hj. destruct (Z.eq_dec j kk') as [->|]; [exact T | apply IH; lia].
      * right. exists kk'. split; [lia | exact T].
    + right. destruct IH as (j & Hj & F). exists j. split; [lia | exact F].
Qed.

(* [comment removed for export] *)
Lemma clear_bit_below : forall k x, 0 <= k -> 0 <= x < 2 ^ k -> x <> 2 ^ k - 1 ->
  exists j, 0 <= j < k /\ Z.testbit x j = false.
Proof.
  intros k x Hk Hx Hne.
  destruct (bits_all_or_ex x k Hk) as [ALL|EX]; [|exact EX].
  exfalso. apply Hne. apply Z.bits_inj'. intros j Hj.
  replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  destruct (Z.lt_ge_cases j k) as [Hl|Hg].
  - rewrite Z.ones_spec_low, ALL by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_high k x j) by lia. reflexivity.
Qed.

Section SetBit.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Variables (m i off : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SJunk off.
  #[local] Notation jq := (g_slot_start st m i + 16 * off).
  (* [comment removed for export] *)
  Let fr := mr_freed (s_meta st m).
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition sb_wr (a : Z) : Prop := (sp - MSTK <= a < sp) \/ (jq - 3 <= a < jq) \/ (m + 28 <= a < m + 32).
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sb_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMfr : cell M' (m + 28) 4 (fr + 2 ^ i).
  (* [comment removed for export] *)
  Hypothesis H63 : g_sc st m <> 63.
  Hypothesis Hcase : Z.lor (mr_avail (s_meta st m)) fr + 2 ^ i <> 2 * 2 ^ g_lastidx st m - 1
                     \/ (s_kind st m = GTop /\ g_sc st m < 48 /\ s_alist st (g_sc st m) = [m]).
  (* [comment removed for export] *)
  Hypothesis Hnus : g_sc st m < 48 -> UNIT * size_class (g_sc st m) <= g_stride st m.

  (* [comment removed for export] *)
  Definition st1 : mst := set_slot st m i SFreed.
  Definition st' : mst := set_meta st1 m (mr_set_freed (s_meta st m) (fr + 2 ^ i)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_ctx : s_ctx st' = s_ctx st. Proof using. reflexivity. Qed.
  Lemma e_areas : s_areas st' = s_areas st. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = s_regions st. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = if Z.eqb x m then mr_set_freed (s_meta st m) (fr + 2 ^ i) else s_meta st x.
  Proof using. intros x. reflexivity. Qed.
  Lemma e_meta_other : forall x, x <> m -> s_meta st' x = s_meta st x.
  Proof using. intros x Hx. rewrite e_meta. destruct (Z.eqb_spec x m); [contradiction|reflexivity]. Qed.
  Lemma e_next : forall x, mr_next (s_meta st' x) = mr_next (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_prev : forall x, mr_prev (s_meta st' x) = mr_prev (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_mem : forall x, mr_mem (s_meta st' x) = mr_mem (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_avail : forall x, mr_avail (s_meta st' x) = mr_avail (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_Wr : forall x, mr_W (s_meta st' x) = mr_W (s_meta st x).
  Proof using. intros x. rewrite e_meta. destruct (Z.eqb_spec x m); [subst; reflexivity|reflexivity]. Qed.
  Lemma e_freed_m : mr_freed (s_meta st' m) = fr + 2 ^ i.
  Proof using. rewrite e_meta, Z.eqb_refl. reflexivity. Qed.
  Lemma e_freed_other : forall x, x <> m -> mr_freed (s_meta st' x) = mr_freed (s_meta st x).
  Proof using. intros x Hx. rewrite e_meta_other by exact Hx. reflexivity. Qed.
  Lemma e_slot : forall x k, s_slot st' x k = if (Z.eqb x m && Z.eqb k i)%bool then SFreed else s_slot st x k.
  Proof using. intros. reflexivity. Qed.
  Lemma e_slot_mi : s_slot st' m i = SFreed.
  Proof using. rewrite e_slot, !Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_other : forall x k, (x <> m \/ k <> i) -> s_slot st' x k = s_slot st x k.
  Proof using H63 Hi. intros x k H. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn; try reflexivity. exfalso; lia. Qed.

  (* [comment removed for export] *)
  Lemma e_gW : forall x, g_W st' x = g_W st x. Proof using. intros; unfold g_W; apply e_Wr. Qed.
  Lemma e_gmem : forall x, g_mem st' x = g_mem st x. Proof using. intros; unfold g_mem; apply e_mem. Qed.
  Lemma e_glast : forall x, g_lastidx st' x = g_lastidx st x. Proof using. intros; unfold g_lastidx; rewrite e_gW; reflexivity. Qed.
  Lemma e_gcnt : forall x, g_cnt st' x = g_cnt st x. Proof using. intros; unfold g_cnt; rewrite e_glast; reflexivity. Qed.
  Lemma e_gsc : forall x, g_sc st' x = g_sc st x. Proof using. intros; unfold g_sc; rewrite e_gW; reflexivity. Qed.
  Lemma e_gml : forall x, g_maplen st' x = g_maplen st x. Proof using. intros; unfold g_maplen; rewrite e_gW; reflexivity. Qed.
  Lemma e_gstride : forall x, g_stride st' x = g_stride st x.
  Proof using. intros; unfold g_stride; rewrite e_gml, e_glast, e_gsc; reflexivity. Qed.
  Lemma e_gss : forall x k, g_slot_start st' x k = g_slot_start st x k.
  Proof using. intros; unfold g_slot_start; rewrite e_gmem, e_gstride; reflexivity. Qed.
  Lemma e_gse : forall x k, g_slot_end st' x k = g_slot_end st x k.
  Proof using. intros; unfold g_slot_end; rewrite e_gss, e_gstride; reflexivity. Qed.
  Lemma e_gspan : forall x, gspan st' x = gspan st x.
  Proof using. intros; unfold gspan, g_span_end; rewrite e_gmem, e_gstride, e_gcnt; reflexivity. Qed.
  Lemma e_inband : forall x q, inband st' x q = inband st x q.
  Proof using. intros; unfold inband; rewrite e_gmem; reflexivity. Qed.
  Lemma e_ptr_ok : forall x k q, ptr_ok st' x k q <-> ptr_ok st x k q.
  Proof using Hnus Hcase Hi. intros; unfold ptr_ok; rewrite e_gmem, e_inband, e_gsc, e_gml; tauto. Qed.
  Lemma e_endb : forall x, endb_own st' x <-> endb_own st x.
  Proof using Hnus Hcase Hi. intros; unfold endb_own; rewrite e_kind, e_gspan. destruct (s_kind st x); [tauto|]. rewrite e_gse. tauto. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using Hnus Hcase Hi. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using Hnus Hcase Hi. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using Hnus Hcase Hi. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using Hnus Hcase Hi. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x. Proof using Hnus Hcase Hi. intros; unfold listed; rewrite e_in_flist, e_in_alist; tauto. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x. Proof using Hnus Hcase Hi. intros; unfold fresh; rewrite e_ctx, e_areas; tauto. Qed.
  Lemma e_depth : forall f x, nest_depth_le st' f x <-> nest_depth_le st f x.
  Proof using Hnus Hcase Hi.
    induction f as [|f IH]; intros x; cbn; change (s_kind st' x) with (s_kind st x); destruct (s_kind st x); try tauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (U_wfg st L HWF m Hgrp). Qed.
  Lemma t_pure : 0 <= off /\ 16 * off <= g_stride st m - IB /\ ptr_ok st m i jq.
  Proof using Hslot Hi Hgrp HWF L RN. pose proof (wg_slots st L m t_wfg i Hi) as SW. rewrite Hslot in SW. exact SW. Qed.
  Lemma t_masks : 0 <= mr_avail (s_meta st m) < 2 ^ 32 /\ 0 <= fr < 2 ^ 32 /\
                  Z.testbit (mr_avail (s_meta st m)) i = false /\ Z.testbit fr i = false.
  Proof using Hslot Hi Hgrp HWF off L RN.
    pose proof t_wfg as WG. split; [exact (wg_avr st L m WG)|]. split; [exact (wg_frr st L m WG)|]. split.
    - destruct (Z.testbit (mr_avail (s_meta st m)) i) eqn:E; [|reflexivity]. exfalso.
      apply (proj1 (wg_av st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E.
    - destruct (Z.testbit fr i) eqn:E; [|reflexivity]. exfalso.
      apply (proj1 (wg_fr st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E.
  Qed.
  Lemma t_last : 0 <= g_lastidx st m < 32. Proof using fr i. unfold g_lastidx, w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma t_pow : 0 < 2 ^ i <= 2 ^ 31.
  Proof using fr Hi m st. pose proof t_last. split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]. Qed.
  Lemma t_fr' : 0 < fr + 2 ^ i < 2 ^ 32.
  Proof using Hslot Hi Hgrp HWF off L RN.
    destruct t_masks as (_ & F1 & _ & F2). pose proof t_pow. pose proof t_last.
    pose proof (add_pow2_nocarry32 fr i ltac:(lia) ltac:(lia) F2). lia.
  Qed.
  Lemma t_bit : forall j, 0 <= j -> Z.testbit (fr + 2 ^ i) j = (Z.eqb i j || Z.testbit fr j)%bool.
  Proof using Hslot Hi Hgrp HWF off L RN. intros j Hj. destruct t_masks as (_ & F1 & _ & F2). apply testbit_add_pow2; try lia. exact F2. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_dll : forall l, dll st l -> dll st' l.
  Proof using. intros l D k Hk. destruct (D k Hk) as [A B]. rewrite e_next, e_prev. split; assumption. Qed.

  Lemma t_wf_ctx : wf_ctx st'.
  Proof using HWF L. destruct (WF_ctx st L HWF); constructor; assumption. Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HWF L. destruct (WF_areas st L HWF); constructor; assumption. Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hnus Hcase Hslot Hi Hgrp HWF off L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist; try assumption.
    - apply t_dll. exact D1.
    - intros x Hx. destruct (FU x Hx) as (U & NG & NF & Me & Av & Fr & W).
      assert (x <> m) by (intros ->; exact (NG Hgrp)).
      rewrite e_metaU, e_is_group, e_fresh, e_meta_other by assumption. repeat split; assumption.
    - intros sc Hsc. apply t_dll. exact (D2 sc Hsc).
    - intros sc x Hx. rewrite e_is_group, e_gsc. exact (AU sc x Hx).
    - intros x U NL. rewrite e_next, e_prev. apply LK; [apply e_metaU; exact U | intros Hl; apply NL; apply e_listed; exact Hl].
    - intros x Hl. rewrite e_next, e_prev. apply LKD. apply e_listed. exact Hl.
    - intros sc x Hx Hne. rewrite e_avail. destruct (Z.eq_dec x m) as [->|Hxm].
      + rewrite e_freed_m. pose proof t_fr'. split; [|lia]. exact (proj1 (RS sc m Hx Hne)).
      + rewrite e_freed_other by exact Hxm. exact (RS sc x Hx Hne).
  Qed.

  (* [comment removed for export] *)
  Lemma t_slot_wf : forall x k sl, is_group st x -> 0 <= k <= g_lastidx st x -> (x <> m \/ k <> i) ->
    s_slot st x k = sl -> slot_wf st L x k sl -> slot_wf st' L x k sl.
  Proof using Hnus Hcase Hi.
    intros x k sl Hx Hk Hne Hs SW. destruct sl as [| |q2 n2 o2 r2|c o2|o2]; cbn [slot_wf] in *; try exact I.
    - destruct SW as (A & B & C & D & E & F & G). rewrite e_gss, e_gstride. conjs; try assumption; try lia.
      apply e_ptr_ok. exact F.
    - destruct SW as (A & B & C & D & E). rewrite e_gss. conjs; try assumption.
      all: try (apply e_is_group; exact B). all: try (apply e_ptr_ok; exact E).
    - destruct SW as (A & B & C). rewrite e_gss, e_gstride. conjs; try assumption. apply e_ptr_ok. exact C.
  Qed.

  Lemma t_wf_group_other : forall x, is_group st x -> x <> m -> wf_group st' L x.
  Proof using Hnus Hcase H63 Hslot Hi HWF off RN.
    intros x Hx Hxm. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_kind;
      rewrite ?(e_meta_other x Hxm); try assumption.
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Av k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Fr k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Avai k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm). exact (High k Hk).
    - intros Hall Hne Hl. apply Full; [| exact Hne | exact Hl].
      intros k Hk. rewrite <- (e_slot_other x k) by (left; exact Hxm). exact (Hall k Hk).
    - destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride. conjs; try assumption; try lia.
      rewrite e_slot_other; [exact K6|].
      destruct (Z.eq_dec hm m) as [->|]; [right | left; assumption]. intros ->. rewrite Hslot in K6. discriminate K6.
    - intros Hall. apply FF. intros k Hk. rewrite <- (e_slot_other x k) by (left; exact Hxm). exact (Hall k Hk).
    - intros k Hk. rewrite e_slot_other by (left; exact Hxm).
      apply t_slot_wf; [exact Hx | exact Hk | left; exact Hxm | reflexivity | exact (Slots k Hk)].
    - intros Hsc Hst k Hk. rewrite e_slot_other by (left; exact Hxm). exact (Fit Hsc Hst k Hk).
  Qed.

  (* [comment removed for export] *)
  Lemma t_ff_case : (forall k, 0 <= k <= g_lastidx st m -> s_slot st' m k = SAvail \/ s_slot st' m k = SFreed) ->
    s_kind st m = GTop /\ g_sc st m < 48 /\ s_alist st (g_sc st m) = [m].
  Proof using Hcase H63 Hslot Hi Hgrp HWF off L RN.
    pose proof t_wfg as WG. pose proof t_fr' as FR. pose proof t_last as TL. destruct t_masks as (A1 & F1 & A2 & F2).
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    intros Hall. destruct Hcase as [Hnall | Hhead]; [exfalso | exact Hhead].
      set (mask := Z.lor (mr_avail (s_meta st m)) fr) in *.
      assert (HM : 0 <= mask < 2 ^ 32) by (subst mask; apply Z_lor_range32; lia).
      assert (HMb : Z.testbit mask i = false) by (subst mask; rewrite Z.lor_spec, A2, F2; reflexivity).
      assert (Hmhi : forall j, g_lastidx st m < j -> Z.testbit mask j = false).
      { intros j Hj. subst mask. rewrite Z.lor_spec.
        destruct (Z.testbit (mr_avail (s_meta st m)) j) eqn:Ta.
        { apply (proj1 (Av j ltac:(lia))) in Ta. lia. }
        destruct (Z.testbit fr j) eqn:Tf.
        { apply (proj1 (Fr j ltac:(lia))) in Tf. lia. }
        reflexivity. }
      assert (Hlt : mask + 2 ^ i < 2 ^ (g_lastidx st m + 1)).
      { assert (Hl : Z.land mask (2 ^ i) = 0) by (apply (proj2 (land_pow2_testbit mask i ltac:(lia) ltac:(lia))); exact HMb).
        rewrite (Z.add_nocarry_lxor _ _ Hl).
        apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
        intros j Hj. rewrite Z.lxor_spec, Hmhi, testbit_pow2 by lia.
        replace (i =? j) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
      destruct (clear_bit_below (g_lastidx st m + 1) (mask + 2 ^ i) ltac:(lia) ltac:(lia)) as (j & Hj & Hbj).
      { rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. intros E. apply Hnall. subst mask. lia. }
      rewrite (testbit_add_pow2 mask i j) in Hbj; [| lia | lia | lia | exact HMb].
      apply Bool.orb_false_elim in Hbj. destruct Hbj as [Hij Hmj].
      assert (Hji : j <> i) by (intros ->; rewrite Z.eqb_refl in Hij; discriminate Hij).
      subst mask. rewrite Z.lor_spec in Hmj. apply Bool.orb_false_elim in Hmj. destruct Hmj as [Haj Hfj].
      destruct (Hall j ltac:(lia)) as [SA|SF]; rewrite e_slot_other in SA || rewrite e_slot_other in SF; try (right; exact Hji).
      + assert (T : Z.testbit (mr_avail (s_meta st m)) j = true) by (apply (proj2 (Av j ltac:(lia))); split; [lia | exact SA]).
        rewrite Haj in T. discriminate T.
      + assert (T : Z.testbit fr j = true) by (apply (proj2 (Fr j ltac:(lia))); split; [lia | exact SF]).
        rewrite Hfj in T. discriminate T.
  Qed.

  Lemma t_wf_group_m : wf_group st' L m.
  Proof using Hnus Hcase H63 Hslot Hi Hgrp HWF off RN.
    pose proof t_wfg as WG. pose proof t_fr' as FR. pose proof t_last as TL. destruct t_masks as (A1 & F1 & A2 & F2).
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_alist, ?e_kind,
      ?e_avail, ?e_freed_m; try assumption.
    - lia.
    - intros k Hk. rewrite e_slot. rewrite Z.eqb_refl. cbn [andb].
      destruct (Z.eqb_spec k i) as [->|Hki].
      + rewrite A2. split; [intros E; discriminate E | intros [_ E]; discriminate E].
      + exact (Av k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. rewrite t_bit by exact Hk.
      destruct (Z.eqb_spec i k) as [<-|Hik]; cbn [orb].
      + rewrite Z.eqb_refl. split; [intros _; split; [lia|reflexivity] | reflexivity].
      + replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). exact (Fr k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [intros E; discriminate E|]. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [reflexivity|]. exact (High k Hk).
    - intros Hall Hne Hl. exfalso. destruct (Hall i Hi) as [_ C]. apply C. apply e_slot_mi.
    - destruct (s_kind st m) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride. conjs; try assumption; try lia.
      rewrite e_slot_other; [exact K6 | left; congruence].
    - (* [comment removed for export] *)
      intros Hall. destruct (t_ff_case Hall) as (K & S48 & E). split; [exact K|]. split; [exact S48|]. rewrite E. left. reflexivity.
    - intros k Hk. rewrite e_slot, Z.eqb_refl. cbn [andb]. destruct (Z.eqb_spec k i) as [->|Hki]; [exact I|].
      apply t_slot_wf; [exact Hgrp | exact Hk | right; exact Hki | reflexivity | exact (Slots k Hk)].
    - intros Hsc Hst. exfalso. pose proof (Hnus Hsc). lia.
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hnus Hcase H63 Hslot Hi Hgrp HWF off RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups.
    - exact ND.
    - intros x Hx. destruct (Z.eq_dec x m) as [->|Hxm]; [apply t_wf_group_m | apply t_wf_group_other; [exact Hx | exact Hxm]].
    - intros m1 m2 H1 H2. rewrite !e_ai, !e_glast, !e_gsc. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. rewrite e_regions in Hin. rewrite e_is_group, e_kind, e_gmem, e_gml. exact (REG b len x Hin).
    - intros x F. rewrite e_meta_other; [apply FR0; apply e_fresh; exact F|].
      intros ->. apply (wg_notfresh st L m t_wfg). apply e_fresh. exact F.
    - intros x U NG NFL NFR. apply (OTH x); [apply e_metaU; exact U | rewrite <- e_is_group; exact NG
        | rewrite <- e_in_flist; exact NFL | rewrite <- e_fresh; exact NFR].
    - intros x Hl. destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_listed, e_fresh. repeat split; assumption.
    - intros m1 m2 H1 H2 G1 G2 E. rewrite !e_gsc in E. rewrite !e_glast in G1, G2. change (is_group st m1) in H1. change (is_group st m2) in H2.
      assert (OLD : forall x, is_group st x -> x <> m -> (forall k, 0 <= k <= g_lastidx st x -> s_slot st' x k = SAvail \/ s_slot st' x k = SFreed) ->
                    forall k, 0 <= k <= g_lastidx st x -> s_slot st x k = SAvail \/ s_slot st x k = SFreed).
      { intros x Hx Hxm G k Hk. rewrite <- (e_slot_other x k (or_introl Hxm)). exact (G k Hk). }
      destruct (Z.eq_dec m1 m) as [->|N1]; destruct (Z.eq_dec m2 m) as [->|N2].
      + reflexivity.
      + destruct (t_ff_case G1) as (_ & _ & E1).
        pose proof (wg_fullfree st L m2 (EACH m2 H2) (OLD m2 H2 N2 G2)) as (_ & _ & IN2). rewrite <- E, E1 in IN2. destruct IN2 as [<-|[]]. reflexivity.
      + destruct (t_ff_case G2) as (_ & _ & E2).
        pose proof (wg_fullfree st L m1 (EACH m1 H1) (OLD m1 H1 N1 G1)) as (_ & _ & IN1). rewrite E, E2 in IN1. destruct IN1 as [<-|[]]. reflexivity.
      + exact (ONEFF m1 m2 H1 H2 (OLD m1 H1 N1 G1) (OLD m2 H2 N2 G2) E).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_slot_ptr : forall x k, (x <> m \/ k <> i) -> slot_ptr st' x k = slot_ptr st x k.
  Proof using H63 Hi. intros x k H. unfold slot_ptr. rewrite e_slot_other by exact H. rewrite e_gss. reflexivity. Qed.

  Lemma t_gcell_back : forall x a, gcell st' x a -> gcell st x a.
  Proof using Hnus Hcase H63 Hi.
    intros x a G. unfold gcell in *.
    rewrite ?e_gmem, ?e_gcnt, ?e_glast in G.
    destruct G as [G | [G | [G | G]]].
    - left. exact G.
    - right. left. destruct G as (k & Hk & Ha & Hend). exists k. rewrite e_gss in Ha.
      split; [exact Hk|]. split; [exact Ha|]. destruct Hend as [Hend|Hend]; [left; exact Hend | right; apply e_endb; exact Hend].
    - right. right. left. destruct G as (k & q & Hk & Hp & Ha). exists k, q. split; [exact Hk|]. split; [|exact Ha].
      destruct (Z.eq_dec x m) as [->|Hxm].
      + destruct (Z.eq_dec k i) as [->|Hki].
        * unfold slot_ptr in Hp. rewrite e_slot_mi in Hp. discriminate Hp.
        * rewrite <- (e_slot_ptr m k) by (right; exact Hki). exact Hp.
      + rewrite <- (e_slot_ptr x k) by (left; exact Hxm). exact Hp.
    - right. right. right. destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). exists k, q, n2, o2, r2.
      rewrite e_gse in Ha. split; [exact Hk|]. split; [|exact Ha].
      destruct (Z.eq_dec x m) as [->|Hxm].
      + destruct (Z.eq_dec k i) as [->|Hki]; [rewrite e_slot_mi in Hs; discriminate Hs|].
        rewrite e_slot_other in Hs by (right; exact Hki). exact Hs.
      + rewrite e_slot_other in Hs by (left; exact Hxm). exact Hs.
  Qed.


  Lemma t_appb_back : forall a, appb st' a -> appb st a.
  Proof using Hnus Hcase H63 Hi.
    intros a (x & k & q & n2 & o2 & r2 & Hx & Hk & Hs & Ha). rewrite e_glast in Hk. apply e_is_group in Hx.
    assert (Hne : x <> m \/ k <> i).
    { destruct (Z.eq_dec x m) as [->|]; [right | left; assumption]. intros ->. rewrite e_slot_mi in Hs. discriminate Hs. }
    rewrite e_slot_other in Hs by exact Hne.
    exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
  Qed.

  Lemma t_areab : forall a, areab st' a <-> areab st a.
  Proof using Hnus Hcase Hi. intros a. unfold areab. rewrite e_areas. tauto. Qed.

  (* [comment removed for export] *)
  Lemma t_slot_range : forall a, g_slot_start st m i - 3 <= a < g_slot_end st m i ->
    garbage st m i a \/ gcell st m a.
  Proof using fr Hslot Hi Hgrp HWF off L RN.
    intros a Ha. destruct t_pure as (Hoff & Hfit & PO).
    destruct (Z.lt_ge_cases a (jq - 4)) as [A|A].
    { left. unfold garbage. rewrite Hslot. split; [exact Hi|]. left. lia. }
    destruct (Z.lt_ge_cases a jq) as [B|B].
    { right. unfold gcell. right. right. left. exists i, jq. unfold slot_ptr. rewrite Hslot. repeat split; lia. }
    left. unfold garbage. rewrite Hslot. split; [exact Hi|]. right. lia.
  Qed.

  Lemma t_garbage_back : forall x k a, garbage st' x k a ->
    garbage st x k a \/ (x = m /\ k = i /\ g_slot_start st m i - 3 <= a < g_slot_end st m i).
  Proof using H63 Hi.
    intros x k a G. unfold garbage in *. rewrite e_glast, e_gss, e_gse in G. destruct G as [Hk G].
    destruct (Z.eq_dec x m) as [->|Hxm].
    - destruct (Z.eq_dec k i) as [->|Hki].
      + right. rewrite e_slot_mi in G. repeat split; lia.
      + left. rewrite e_slot_other in G by (right; exact Hki). split; [exact Hk|].
        destruct (s_slot st m k); rewrite ?e_gss, ?e_gspan in G; exact G.
    - left. rewrite e_slot_other in G by (left; exact Hxm). split; [exact Hk|].
      destruct (s_slot st x k); rewrite ?e_gss, ?e_gspan in G; exact G.
  Qed.

  (* [comment removed for export] *)
  Lemma slot_sep : forall x k1 k2, 16 <= g_stride st x -> k1 < k2 ->
    g_slot_end st x k1 <= g_slot_start st x k2 - 4.
  Proof using fr i m.
    intros x k1 k2 Hs Hlt. unfold g_slot_end, g_slot_start, IB.
    assert (g_stride st x * (k1 + 1) <= g_stride st x * k2) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma t_gcell_where : forall a, gcell st' m a ->
    (g_mem st m <= a < g_mem st m + 12)
    \/ (exists k, 0 <= k <= g_cnt st m /\ a = g_slot_start st m k - 4)
    \/ (exists k, 0 <= k <= g_lastidx st m /\ k <> i /\ g_slot_start st m k - 4 <= a < g_slot_end st m k).
  Proof using H63 Hslot Hi Hgrp HWF off L RN.
    intros a G. destruct t_pure as (Hoff & Hfit & PO). pose proof (wg_stride st L m t_wfg) as [S16 _].
    unfold gcell in G. rewrite ?e_gmem, ?e_gcnt, ?e_glast in G.
    destruct G as [G | [G | [G | G]]].
    - left. exact G.
    - right. left. destruct G as (k & Hk & Ha & _). exists k. rewrite e_gss in Ha. split; [exact Hk | exact Ha].
    - right. right. destruct G as (k & q & Hk & Hq & Ha).
      assert (Hki : k <> i) by (intros ->; unfold slot_ptr in Hq; rewrite e_slot_mi in Hq; discriminate Hq).
      exists k. split; [exact Hk|]. split; [exact Hki|].
      rewrite e_slot_ptr in Hq by (right; exact Hki). unfold slot_ptr in Hq.
      pose proof (wg_slots st L m t_wfg k Hk) as SW.
      destruct (s_slot st m k) as [| |q2 n2 o2 r2|c o2|o2] eqn:Es; try discriminate Hq; injection Hq; intros <-; cbn [slot_wf] in SW.
      + destruct SW as (A & B & C & D & E & _). unfold g_slot_end, IB in *. lia.
      + destruct SW as (A & B & C & D & (P1 & P2 & P3 & P4 & P5 & P6)).
        pose proof (wg_kind st L c (wG_each st L (WF_groups st L HWF) c B)) as KC. rewrite D in KC.
        destruct KC as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        pose proof (wg_stride st L c (wG_each st L (WF_groups st L HWF) c B)) as [SC _].
        assert (0 <= g_lastidx st c) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
        assert (0 <= g_cnt st c * g_stride st c) by (apply Z.mul_nonneg_nonneg; unfold g_cnt; lia).
        unfold g_slot_end, UNIT, IB in *. lia.
      + destruct SW as (A & B & C). unfold g_slot_end, IB in *. lia.
    - right. right. destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha).
      assert (Hki : k <> i) by (intros ->; rewrite e_slot_mi in Hs; discriminate Hs).
      exists k. split; [exact Hk|]. split; [exact Hki|].
      rewrite e_slot_other in Hs by (right; exact Hki). rewrite e_gse in Ha.
      pose proof (wg_slots st L m t_wfg k Hk) as SW. rewrite Hs in SW. cbn [slot_wf] in SW.
      destruct SW as (A & B & C & D & E & _). unfold g_slot_end, IB in *. lia.
  Qed.

  Lemma t_gcell_m_out : forall a, gcell st' m a -> ~ (g_slot_start st m i - 3 <= a < g_slot_end st m i).
  Proof using H63 Hslot Hi Hgrp HWF off L RN.
    intros a G Ha. pose proof (wg_stride st L m t_wfg) as [S16 _]. pose proof (wg_mem st L m t_wfg) as (M1 & M2 & M3).
    destruct (t_gcell_where a G) as [W | [(k & Hk & Hak) | (k & Hk & Hki & Hak)]].
    - unfold g_slot_end, g_slot_start, UNIT in Ha. assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia). lia.
    - (* [comment removed for export] *)
      unfold g_slot_end, g_slot_start, UNIT, IB in *.
      assert (g_stride st m * i < g_stride st m * k) by lia.
      assert (g_stride st m * k < g_stride st m * (i + 1)) by lia.
      assert (i < k) by (apply (Z.mul_lt_mono_pos_l (g_stride st m)); lia).
      assert (k < i + 1) by (apply (Z.mul_lt_mono_pos_l (g_stride st m)); lia). lia.
    - destruct (Z.lt_ge_cases k i) as [Hl|Hg].
      + pose proof (slot_sep m k i S16 Hl). lia.
      + assert (Hl : i < k) by lia. pose proof (slot_sep m i k S16 Hl). lia.
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using Hnus Hcase H63 Hslot Hi Hgrp HWF off L RN.
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN].
    constructor; rewrite ?e_regions.
    - intros x Hx. apply e_is_group in Hx. rewrite e_gmem, e_gspan. exact (INR x Hx).
    - intros m1 m2 a H1 H2 Hne G1 G2. apply e_is_group in H1. apply e_is_group in H2.
      exact (CELLS m1 m2 a H1 H2 Hne (t_gcell_back m1 a G1) (t_gcell_back m2 a G2)).
    - intros x a Hx Hr Har. apply e_is_group in Hx. rewrite e_gmem, e_gspan in Hr. apply t_areab in Har. exact (AREA x a Hx Hr Har).
    - intros x a Hx G Ap. apply e_is_group in Hx. pose proof (t_appb_back a Ap) as Ap'. exact (APC x a Hx (t_gcell_back x a G) Ap').
    - intros a Ap Ar. pose proof (t_appb_back a Ap) as Ap'. apply t_areab in Ar. exact (APA a Ap' Ar).
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2.
      assert (N1 : m1 <> m \/ k1 <> i).
      { destruct (Z.eq_dec m1 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S1. discriminate S1. }
      assert (N2 : m2 <> m \/ k2 <> i).
      { destruct (Z.eq_dec m2 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S2. discriminate S2. }
      rewrite e_slot_other in S1 by exact N1. rewrite e_slot_other in S2 by exact N2.
      exact (APD m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne).
    - intros x k a x2 Hx G H2 C. apply e_is_group in Hx. apply e_is_group in H2.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)].
      + exact (GC x k a x2 Hx G' H2 (t_gcell_back x2 a C)).
      + destruct (Z.eq_dec x2 m) as [->|Hx2].
        * exact (t_gcell_m_out a C Ha).
        * pose proof (t_gcell_back x2 a C) as C'.
          destruct (t_slot_range a Ha) as [G0 | Cm].
          -- exact (GC m i a x2 Hgrp G0 H2 C').
          -- exact (CELLS m x2 a Hgrp H2 ltac:(congruence) Cm C').
    - intros x k a Hx G Ap. apply e_is_group in Hx. pose proof (t_appb_back a Ap) as Ap'.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)].
      + exact (GA x k a Hx G' Ap').
      + destruct (t_slot_range a Ha) as [G0 | Cm].
        * exact (GA m i a Hgrp G0 Ap').
        * exact (APC m a Hgrp Cm Ap').
    - intros x k a Hx G Ar. apply e_is_group in Hx. apply t_areab in Ar.
      destruct (t_garbage_back x k a G) as [G' | (-> & -> & Ha)].
      + exact (GAR x k a Hx G' Ar).
      + apply (AREA m a Hgrp); [|exact Ar].
        destruct t_pure as (Hoff & Hn & Hp & Hres & Hr & PO & HinL).
        pose proof (wg_stride st L m t_wfg) as [S16 _]. pose proof (wg_mem st L m t_wfg) as (M1 & _).
        unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *.
        assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
        assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
        lia.
    - intros x Hx. apply e_is_group in Hx. rewrite e_kind, e_gspan, e_gmem, e_gml.
      pose proof (SPAN x Hx) as S. destruct (s_kind st x); [exact S|]. rewrite e_gss, e_gse. exact S.
  Qed.

  Lemma t_wf_live : wf_live st' L.
  Proof using Hnus Hcase H63 Hslot Hi HWF off RN.
    destruct (WF_live st L HWF) as [IN ND FUN LEN].
    constructor.
    - intros q2 n2 Hin. destruct (IN q2 n2 Hin) as (x & k & o2 & r2 & Hx & Hk & Hs).
      exists x, k, o2, r2. rewrite e_glast. split; [apply e_is_group; exact Hx|]. split; [exact Hk|].
      rewrite e_slot_other; [exact Hs|].
      destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros ->. rewrite Hslot in Hs. discriminate Hs.
    - exact ND.
    - intros m1 i1 m2 i2 q2 n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      apply e_is_group in H1. apply e_is_group in H2. rewrite e_glast in Hk1, Hk2.
      assert (N1 : m1 <> m \/ i1 <> i).
      { destruct (Z.eq_dec m1 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S1. discriminate S1. }
      assert (N2 : m2 <> m \/ i2 <> i).
      { destruct (Z.eq_dec m2 m) as [->|]; [right|left; assumption]. intros ->. rewrite e_slot_mi in S2. discriminate S2. }
      rewrite e_slot_other in S1 by exact N1. rewrite e_slot_other in S2 by exact N2.
      exact (FUN m1 i1 m2 i2 q2 n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2).
    - exact LEN.
  Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using H63 Hi HWF L.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; rewrite ?e_regions, ?e_brk; try assumption.
    - intros b len x Hin. rewrite e_gsc. exact (GB b len x Hin).
    - intros b len x Hin Hx63. rewrite e_gsc in Hx63.
      assert (Hxm : x <> m) by (intros ->; exact (H63 Hx63)).
      destruct (G63 b len x Hin Hx63) as [(q & n2 & o2 & r2 & Hs & Hlen) | (o2 & Hs)].
      + left. exists q, n2, o2, r2. split; [|exact Hlen]. rewrite e_slot_other; [exact Hs | left; exact Hxm].
      + right. exists o2. rewrite e_slot_other; [exact Hs | left; exact Hxm].
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using HWF L RN. apply (wf_img_same st L HWF); reflexivity. Qed.

  Lemma t_WF : WF st' L.
  Proof using Hnus Hcase H63 Hslot Hi Hgrp HWF off.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_m_area : exists ar k, In ar (s_areas st) /\ 0 <= k < NSLOTS /\ m = meta_addr ar k /\
      ar mod 4096 = 0 /\ HEAPLO <= ar /\ ar + 4096 <= CEIL /\ ar + 24 <= m /\ m + 40 <= ar + 4096.
  Proof using fr Hgrp HWF i L.
    destruct (metaU_area st L HWF m (wg_U st L m t_wfg)) as (ar & k & A & B & C & D & E & F & G & H & _).
    exists ar, k. repeat split; try assumption; lia.
  Qed.

  Lemma t_p_rng : HEAPLO + 16 <= jq /\ jq <= g_slot_end st m i /\ g_slot_end st m i < CEIL /\
                  (g_slot_start st m i - 3 <= jq - 3 /\ g_mem st m + 16 <= jq < gspan st m).
  Proof using fr Hslot Hi Hgrp HWF L.
    destruct t_pure as (Hoff & Hfit & (P1 & P2 & _)).
    destruct (group_range st L HWF m Hgrp) as [G1 G2].
    pose proof (wg_stride st L m t_wfg) as [S16 _].
    assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
    unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma t_agree_low : agree_on (fun a => IMG_LO <= a < IMG_HI) M M'.
  Proof using H63 HMwr Hsp fr Hslot Hi Hgrp HWF sp off i m L st RN.
    apply (agree_of_writes sb_wr); [exact HMwr|]. intros a Ha W.
    destruct t_p_rng as (P1 & _ & _ & _ & P5). destruct t_m_area as (ar & k & _ & _ & _ & _ & Har & _ & Hm1 & _).
    hsep; ceil; unfold sb_wr, HEAPLO, MSTK in *. lia.
  Qed.

  Lemma t_agree_area : forall ar a, In ar (s_areas st) -> ar <= a < ar + 4096 -> ~ (m + 28 <= a < m + 32) ->
    M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof using HMwr Hsp fr Hslot Hi Hgrp HWF sp off i L RN.
    intros ar a Har Ha Hnot. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
    apply (agree_of_writes sb_wr (fun x => x = a)); [exact HMwr| | hsep; ceil; unfold HEAPLO in *; lia |reflexivity].
    intros b -> W. destruct W as [W|[W|W]].
    - ceil; unfold MSTK in *. lia.
    - apply (ge_area st (WF_geom st L HWF) m a Hgrp).
      + destruct t_p_rng as (P1 & P2 & P3 & P4). pose proof (gcell_in_span st L HWF m (jq - 1) Hgrp) as GS.
        assert (GC : gcell st m (jq - 1)).
        { unfold gcell. right. right. left. exists i, jq. unfold slot_ptr. rewrite Hslot. repeat split; lia. }
        specialize (GS GC). destruct (group_range st L HWF m Hgrp). 
        assert (GC2 : gcell st m (jq - 3)).
        { unfold gcell. right. right. left. exists i, jq. unfold slot_ptr. rewrite Hslot. repeat split; lia. }
        pose proof (gcell_in_span st L HWF m (jq - 3) Hgrp GC2). lia.
      + exists ar. split; assumption.
    - exact (Hnot W).
  Qed.

  Lemma t_agree_cell : forall x a, is_group st x -> gcell st' x a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof using Hnus Hcase H63 HMwr Hsp Hslot Hi Hgrp HWF sp off L RN.
    intros x a Hx G. pose proof (t_gcell_back x a G) as G0.
    pose proof (gcell_in_span st L HWF x a Hx G0) as SP. destruct (group_range st L HWF x Hx) as [R1 R2].
    apply (agree_of_writes sb_wr (fun y => y = a)); [exact HMwr| | hsep; ceil; unfold HEAPLO in *; lia |reflexivity].
    intros b -> W.
    destruct W as [W|[W|W]].
    - ceil; unfold MSTK in *. lia.
    - destruct (Z.eq_dec x m) as [->|Hxm].
      + apply (t_gcell_m_out a G). destruct t_p_rng as (P1 & P2 & P3 & P4). lia.
      + apply (ge_cells st (WF_geom st L HWF) m x a Hgrp Hx ltac:(congruence)); [|exact G0].
        unfold gcell. right. right. left. exists i, jq. unfold slot_ptr. rewrite Hslot. repeat split; lia.
    - destruct t_m_area as (ar & k & Har & Hk & Hm & Hal & Hlo & Hhi & H1 & H2).
      apply (ge_area st (WF_geom st L HWF) x a Hx); [lia|]. exists ar. split; [exact Har | lia].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using Hnus Hcase H63 HMfr HMgrow HMwr Hsp Hslot Hi Hgrp HREP HWF sp off M L RN.
    pose proof HREP as [ST CX AR GR].
    assert (LOW : forall a k v, IMG_LO <= a /\ a + Z.of_nat k <= IMG_HI -> 0 <= a -> cell M a k v -> cell M' a k v).
    { intros a k v Hk Ha C. eapply cell_agree; [exact Ha | hsep; unfold HEAPLO in *; lia | | exact C].
      eapply agree_on_mono; [exact t_agree_low|]. cbn. intros; lia. }
    constructor.
    - destruct ST; constructor; try (eapply LOW; [cbn; hsep; unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV, HEAPLO; lia | unfold A_NEED_LOCKS, A_PAGESIZE, MLOCK, A_CANARY, A_GOT_CANARY, A_ERRNO, TPV; lia | eassumption]);
        try (eapply defined_grows; [exact HMgrow | eassumption]).
      + eapply img_clear_agree; [unfold A_TAB_CTZ; lia | unfold A_TAB_CTZ; lia | |eassumption]. eapply agree_on_mono; [exact t_agree_low|]. cbn. hsep; unfold A_TAB_CTZ, HEAPLO. intros; lia.
      + eapply img_clear_agree; [unfold A_TAB_SC; lia | unfold A_TAB_MED; lia | |eassumption]. eapply agree_on_mono; [exact t_agree_low|]. cbn. hsep; unfold A_TAB_SC, A_TAB_MED, HEAPLO. intros; lia.
    - destruct CX; constructor; intros;
        try (eapply LOW; [cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX, HEAPLO; lia
             | unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | eauto]);
        try (eapply defined_grows; [exact HMgrow | eassumption]).
    - intros ar Har. change (In ar (s_areas st)) in Har. pose proof (AR ar Har) as [CK NS DF MT].
      destruct t_m_area as (ar0 & k0 & Har0 & Hk0 & Hm & Hal0 & Hlo0 & Hhi0 & H01 & H02).
      destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
      assert (SEP : ar = ar0 \/ ar + 4096 <= ar0 \/ ar0 + 4096 <= ar).
      { destruct (Z.eq_dec ar ar0) as [->|Hne]; [left; reflexivity|right].
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (ar <> ar0) by exact Hne. lia. }
      hsep; ceil; unfold HEAPLO in Hlo, Hhi, Hlo0, Hhi0.
      constructor.
      + eapply cell_agree; [lia | cbn; lia | | exact CK]. intros a Hra Ha. apply (t_agree_area ar); [exact Har | cbn in Ha; lia |].
        cbn in Ha. unfold meta_addr, AREA_HDR, META_SZ in Hm. lia.
      + eapply cell_agree; [lia | cbn; lia | | exact NS]. intros a Hra Ha. apply (t_agree_area ar); [exact Har | cbn in Ha; lia |].
        cbn in Ha. unfold meta_addr, AREA_HDR, META_SZ in Hm. lia.
      + eapply defined_grows; [exact HMgrow | exact DF].
      + intros k Hk. rewrite e_meta. destruct (Z.eqb_spec (meta_addr ar k) m) as [E|NE].
        * rewrite E. apply (rep_meta_set_freed M M' m (s_meta st m) (fr + 2 ^ i)); [lia | lia | | exact HMfr |].
          -- intros a Hra Ha. apply (t_agree_area ar0); [exact Har0 | lia | lia].
          -- rewrite <- E. exact (MT k Hk).
        * apply (rep_meta_agree M M'); [unfold meta_addr, AREA_HDR, META_SZ; lia | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia | | exact (MT k Hk)].
          intros a Hra Ha. apply (t_agree_area ar); [exact Har | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia |].
          unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *.
          destruct SEP as [-> | SEP]; [|lia].
          assert (k <> k0) by (intros ->; apply NE; rewrite Hm; reflexivity). nia.
    - intros x Hx. change (is_group st x) in Hx.
      destruct (group_range st L HWF x Hx) as [R1 R2]. pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
      pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (X1 & X2 & X3).
      apply (rep_group_transport st st' M M' x); rewrite ?e_gmem, ?e_gcnt, ?e_glast, ?e_ai, ?e_kind, ?e_gml; try reflexivity.
      + exact (e_gss x).
      + exact (e_gse x).
      + exact (e_inband x).
      + intros E. apply (proj1 (e_endb x)). exact E.
      + destruct (s_kind st x); [split; reflexivity | exact I].
      + intros k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool; [right; right; reflexivity | left; reflexivity].
      + intros a G. apply (t_agree_cell x a Hx G).
      + exact HMgrow.
      + assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; assert (0 <= g_lastidx st x) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia); nia).
        hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia.
      + intros a G. apply (gcell_in_span st L HWF x a Hx). apply t_gcell_back. exact G.
      + exact (GR x Hx).
  Qed.

  Theorem setbit_close : WF st' L /\ REP st' M'.
  Proof using Hnus Hcase H63 HMfr HMgrow HMwr Hsp Hslot Hi Hgrp HREP HWF sp off M. split; [exact t_WF | exact t_REP]. Qed.
End SetBit.
