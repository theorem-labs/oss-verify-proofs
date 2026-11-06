(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module MhExtB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record sub_groupsB (st1 st2 : mst) (hx : Z) : Prop := SUBGB {
  sgb_in : forall x, is_group st1 x -> is_group st2 x;
  sgb_kind : forall x, is_group st1 x -> s_kind st2 x = s_kind st1 x;
  sgb_slot : forall x k, is_group st1 x -> x <> hx -> slot_sim (s_slot st1 x k) (s_slot st2 x k);
  sgb_userx : forall k q n o r, s_slot st2 hx k = SUser q n o r <-> s_slot st1 hx k = SUser q n o r;
  sgb_mem : forall x, is_group st1 x -> mr_mem (s_meta st2 x) = mr_mem (s_meta st1 x);
  sgb_W : forall x, is_group st1 x -> mr_W (s_meta st2 x) = mr_W (s_meta st1 x)
}.

Section ExtB.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (L : list (Z * Z)) (hx : Z).
  Hypothesis S : sub_groupsB st1 st2 hx.
  Hypothesis HWF1 : WF st1 L.

  Lemma v_host_group : forall y hm j o, is_group st1 y -> s_kind st1 y = GNest hm j o -> is_group st1 hm.
  Proof using HWF1 L RN.
    intros y hm j o Hy K. pose proof (wg_kind st1 L y (wG_each st1 L (WF_groups st1 L HWF1) y Hy)) as KD.
    rewrite K in KD. exact (proj1 (proj2 KD)).
  Qed.
  Lemma v_child_group : forall x k c o, is_group st1 x -> 0 <= k <= g_lastidx st1 x -> s_slot st1 x k = SHost c o -> is_group st1 c.
  Proof using HWF1 L RN.
    intros x k c o Hx Hk E. pose proof (wg_slots st1 L x (wG_each st1 L (WF_groups st1 L HWF1) x Hx) k Hk) as SW.
    rewrite E in SW. exact (proj1 (proj2 SW)).
  Qed.

  Lemma v_gW : forall x, is_group st1 x -> g_W st2 x = g_W st1 x. Proof using S hx. intros; unfold g_W; apply (sgb_W _ _ _ S); assumption. Qed.
  Lemma v_gmem : forall x, is_group st1 x -> g_mem st2 x = g_mem st1 x. Proof using S hx. intros; unfold g_mem; apply (sgb_mem _ _ _ S); assumption. Qed.
  Lemma v_glast : forall x, is_group st1 x -> g_lastidx st2 x = g_lastidx st1 x. Proof using S hx. intros; unfold g_lastidx; rewrite v_gW by assumption; reflexivity. Qed.
  Lemma v_gcnt : forall x, is_group st1 x -> g_cnt st2 x = g_cnt st1 x. Proof using S hx. intros; unfold g_cnt; rewrite v_glast by assumption; reflexivity. Qed.
  Lemma v_gsc : forall x, is_group st1 x -> g_sc st2 x = g_sc st1 x. Proof using S hx. intros; unfold g_sc; rewrite v_gW by assumption; reflexivity. Qed.
  Lemma v_gml : forall x, is_group st1 x -> g_maplen st2 x = g_maplen st1 x. Proof using S hx. intros; unfold g_maplen; rewrite v_gW by assumption; reflexivity. Qed.
  Lemma v_gstride : forall x, is_group st1 x -> g_stride st2 x = g_stride st1 x.
  Proof using S hx. intros; unfold g_stride; rewrite v_gml, v_glast, v_gsc by assumption; reflexivity. Qed.
  Lemma v_gss : forall x k, is_group st1 x -> g_slot_start st2 x k = g_slot_start st1 x k.
  Proof using S hx. intros; unfold g_slot_start; rewrite v_gmem, v_gstride by assumption; reflexivity. Qed.
  Lemma v_gse : forall x k, is_group st1 x -> g_slot_end st2 x k = g_slot_end st1 x k.
  Proof using S hx. intros; unfold g_slot_end; rewrite v_gss, v_gstride by assumption; reflexivity. Qed.
  Lemma v_gspan : forall x, is_group st1 x -> gspan st2 x = gspan st1 x.
  Proof using S hx. intros; unfold gspan, g_span_end; rewrite v_gmem, v_gstride, v_gcnt by assumption; reflexivity. Qed.
  Lemma v_inband : forall x q, is_group st1 x -> inband st2 x q = inband st1 x q.
  Proof using S hx. intros; unfold inband; rewrite v_gmem by assumption; reflexivity. Qed.
  Lemma v_ptr_ok : forall x k q, is_group st1 x -> (ptr_ok st2 x k q <-> ptr_ok st1 x k q).
  Proof using S hx. intros; unfold ptr_ok; rewrite v_gmem, v_inband, v_gsc, v_gml by assumption; tauto. Qed.
  Lemma v_endb : forall x, is_group st1 x -> (endb_own st2 x <-> endb_own st1 x).
  Proof using HWF1 S hx L RN.
    intros x Hx; unfold endb_own; rewrite (sgb_kind _ _ _ S), v_gspan by assumption.
    destruct (s_kind st1 x) as [|hm j o] eqn:K; [tauto|]. rewrite v_gse by (eapply v_host_group; eassumption). tauto.
  Qed.
  Lemma v_is_group : forall x, is_group st1 x -> is_group st2 x. Proof using S hx. exact (sgb_in _ _ _ S). Qed.
  Lemma v_slot_cases : forall x k, is_group st1 x -> x <> hx -> s_slot st2 x k = s_slot st1 x k \/
    ((s_slot st1 x k = SAvail \/ s_slot st1 x k = SFreed) /\ (s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed)).
  Proof using S. intros x k Hx Hne. destruct (sgb_slot _ _ _ S x k Hx Hne) as [E|E]; [left; symmetry; exact E | right; exact E]. Qed.
  Lemma v_slot_ptr : forall x k, is_group st1 x -> x <> hx -> slot_ptr st2 x k = slot_ptr st1 x k.
  Proof using S.
    intros x k Hx Hne; unfold slot_ptr. rewrite v_gss by assumption.
    destruct (v_slot_cases x k Hx Hne) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; reflexivity.
  Qed.
  Lemma v_user : forall x k q n o r, is_group st1 x -> s_slot st2 x k = SUser q n o r <-> s_slot st1 x k = SUser q n o r.
  Proof using S hx.
    intros x k q n o r Hx. destruct (Z.eq_dec x hx) as [->|Hne]; [exact (sgb_userx _ _ _ S k q n o r)|].
    destruct (v_slot_cases x k Hx Hne) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; split; intro H; try exact H; discriminate.
  Qed.


  Lemma v_gcell : forall x a, is_group st1 x -> x <> hx -> (gcell st2 x a <-> gcell st1 x a).
  Proof using HWF1 S L RN.
    intros x a Hx Hne. unfold gcell. rewrite v_gmem, v_gcnt, v_glast by assumption.
    assert (E2 : forall k, (k < g_cnt st1 x \/ endb_own st2 x) <-> (k < g_cnt st1 x \/ endb_own st1 x)) by (intros; rewrite v_endb by assumption; tauto).
    split; intros [G|[G|[G|G]]].
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite v_gss in B by assumption. rewrite <- E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite v_slot_ptr in B by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite v_user in B by assumption. rewrite v_gse in C by assumption. tauto.
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite v_gss by assumption. rewrite E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite v_slot_ptr by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite v_user, v_gse by assumption. tauto.
  Qed.
  Lemma v_appb : forall a, appb st1 a -> appb st2 a.
  Proof using S hx.
    intros a (x & k & q & n & o & r & A & B & C & D).
    exists x, k, q, n, o, r. rewrite v_glast, v_user by exact A. split; [apply v_is_group; exact A | tauto].
  Qed.
  (* [comment removed for export] *)
  Lemma v_appb_back : (forall x k q n o r, is_group st2 x -> ~ is_group st1 x -> s_slot st2 x k <> SUser q n o r) ->
    forall a, appb st2 a -> appb st1 a.
  Proof using S hx.
    intros NU a (x & k & q & n & o & r & A & B & C & D).
    destruct (in_dec Z.eq_dec x (s_groups st1)) as [Hx|Hx]; [|exfalso; exact (NU x k q n o r A Hx C)].
    exists x, k, q, n, o, r. rewrite v_glast, v_user in * by exact Hx. tauto.
  Qed.
  Lemma v_garbage : forall x k a, is_group st1 x -> x <> hx -> (garbage st2 x k a <-> garbage st1 x k a).
  Proof using HWF1 S L RN.
    intros x k a Hx Hne. unfold garbage. rewrite v_glast, v_gss, v_gse by assumption.
    destruct (v_slot_cases x k Hx Hne) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; [|tauto..].
    destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; try tauto.
    destruct (Z.le_gt_cases 0 k) as [Hk0|Hk0]; [|split; intros [Hk _]; lia].
    destruct (Z.le_gt_cases k (g_lastidx st1 x)) as [Hk1|Hk1]; [|split; intros [Hk _]; lia].
    rewrite v_gspan by (eapply (v_child_group x k); [exact Hx | lia | exact Sk]). tauto.
  Qed.
  Lemma v_depth : forall f x, is_group st1 x -> (nest_depth_le st2 f x <-> nest_depth_le st1 f x).
  Proof using HWF1 S hx L RN.
    induction f as [|f IH]; intros x Hx; cbn; rewrite (sgb_kind _ _ _ S) by exact Hx; destruct (s_kind st1 x) as [|hm j o] eqn:K; try tauto.
    apply IH. exact (v_host_group x hm j o Hx K).
  Qed.

  Lemma v_slot_wf_same : forall x k sl, is_group st1 x -> slot_wf st1 L x k sl -> slot_wf st2 L x k sl.
  Proof using S hx.
    intros x k sl Hx SW. destruct sl as [| |q n o r|c o|o]; cbn [slot_wf] in *; try exact I.
    - rewrite v_gss, v_gstride by assumption. destruct SW as (A & B & C & D & E & F & G). repeat (split; [assumption|]).
      split; [apply v_ptr_ok; [exact Hx | exact F] | exact G].
    - destruct SW as (A & B & C & D & E). rewrite v_gss, (sgb_kind _ _ _ S) by assumption. repeat (split; [first [assumption | apply v_is_group; assumption]|]).
      apply v_ptr_ok; [exact Hx | exact E].
    - rewrite v_gss, v_gstride by assumption. destruct SW as (A & B & C). split; [exact A|]. split; [exact B|]. apply v_ptr_ok; [exact Hx | exact C].
  Qed.




  Lemma wf_live_subB : (forall x k q n o r, is_group st2 x -> ~ is_group st1 x -> s_slot st2 x k <> SUser q n o r) ->
    wf_live st1 L -> wf_live st2 L.
  Proof using S hx.
    intros NU [IN ND FUN LEN]. constructor.
    - intros p n Hin. destruct (IN p n Hin) as (x & k & o & r & A & B & C). exists x, k, o, r.
      rewrite v_glast, v_user by exact A. split; [apply v_is_group; exact A | tauto].
    - exact ND.
    - intros m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      destruct (in_dec Z.eq_dec m1 (s_groups st1)) as [G1|G1]; [|exfalso; exact (NU m1 i1 p n1 o1 r1 H1 G1 S1)].
      destruct (in_dec Z.eq_dec m2 (s_groups st1)) as [G2|G2]; [|exfalso; exact (NU m2 i2 p n2 o2 r2 H2 G2 S2)].
      rewrite v_glast in Hk1 by exact G1. rewrite v_glast in Hk2 by exact G2.
      rewrite v_user in S1 by exact G1. rewrite v_user in S2 by exact G2. eauto.
    - exact LEN.
  Qed.

End ExtB.
End MhExtB.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhScrib OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKTop. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt MhExtB OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhScrib OSSVerify.Proofs.glaze.binary_reflection.lib.MhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhASlotKTop.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; lia ] | lia ] ].
Section NewNest.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (m hg hi off : Z) (sc cnt aidx usage' : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HU : metaU st m.
  Hypothesis HNG : ~ is_group st m.
  Hypothesis Hunl : ~ listed st m.
  Hypothesis HNF : ~ fresh st m.
  Hypothesis Hlimbo : In m (s_limbo st).
  Hypothesis Hmz : s_meta st m = meta_zero.
  Hypothesis Hhg : is_group st hg.
  Hypothesis Hhi : 0 <= hi <= g_lastidx st hg.
  Hypothesis Hslot : s_slot st hg hi = SJunk 0.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hscj : sc < g_sc st hg /\ g_sc st hg < 48.
  Hypothesis Hnil : s_alist st sc = [].
  Hypothesis Hcnt : 2 <= cnt <= 32.
  Hypothesis Haidx : 0 <= aidx <= cnt - 1.
  Hypothesis Husage : 0 <= usage' < 2 ^ 64.
  #[local] Notation strideH := (g_stride st hg).
  #[local] Notation start := (g_slot_start st hg hi).
  #[local] Notation size := (slot_stride 0 (cnt - 1) sc).
  Hypothesis Hoff : 0 <= off.
  Hypothesis Hroom : UNIT + cnt * size + 16 * off <= strideH.
  Hypothesis H2048 : UNIT + cnt * size <= 2048.
  Hypothesis Hpnd : aidx < cnt - 1 -> 4096 mod size <> 0.
  Definition p : Z := start + 16 * off.
  Hypothesis Hptr : ptr_ok st hg hi p.
  #[local] Notation cx := (s_ctx st).
  #[local] Notation areas := (s_areas st).
  #[local] Notation regions := (s_regions st).

  Definition W : Z := mkW (cnt - 1) 1 sc 0.
  #[local] Notation av := (av_of aidx).
  #[local] Notation fr := (fr_of cnt aidx).
  #[local] Notation nslot := (nslot_of aidx).
  Definition b_meta (x : Z) : meta_rec := if x =? m then MR m m p av fr W else s_meta st x.
  Definition b_kind (x : Z) : gkind := if x =? m then GNest hg hi off else s_kind st x.
  Definition b_ai (x : Z) : Z := if x =? m then aidx else s_ai st x.
  Definition b_slot (x k : Z) : slot_st :=
    if x =? m then nslot k else if ((x =? hg) && (k =? hi))%bool then SHost m off else s_slot st x k.
  Definition st' : mst :=
    MST (cx_set_grp cx (c_mmap_ctr cx) sc m usage') areas b_meta (s_flist st) (fupd (s_alist st) sc [m]) (m :: s_groups st)
        b_ai b_kind b_slot regions (s_brk st) (s_canary st) (s_errno st) (zremove m (s_limbo st)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma size_eq : size = UNIT * size_class sc. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma W_fields : w_lastidx W = cnt - 1 /\ w_freeable W = 1 /\ w_sizeclass W = sc /\ w_maplen W = 0.
  Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold W. apply mkW_fields; lia. Qed.
  Lemma W_rng : 0 <= W < 2 ^ 64. Proof using Hcnt Hscj Hsc hg st. clear - Hcnt Hscj Hsc hg st. unfold W, mkW. lia. Qed.
  Lemma size_facts : 16 <= size /\ size mod 16 = 0 /\ size <= 1016.
  Proof using H2048 Husage Hcnt Hsc usage'. clear - H2048 Husage Hcnt Hsc usage'.
    pose proof H2048 as B. rewrite size_eq in B |- *. pose proof (size_class_pos sc Hsc) as [S1 S2]. unfold UNIT in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (2 * (16 * size_class sc) <= cnt * (16 * size_class sc)) by (apply Z.mul_le_mono_nonneg_r; lia).
    split; [lia|]. split; [lia | lia].
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Lemma m_rng : HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0.
  Proof using HU HWF L st. clear - HU HWF L st. exact (metaU_rng st L HWF m HU). Qed.
  Lemma grp_ne : forall x, is_group st x -> x <> m.
  Proof using HNG. clear - HNG. intros x Hx ->. exact (HNG Hx). Qed.
  Lemma grp_neb : forall x, is_group st x -> (x =? m) = false.
  Proof using HNG. clear - HNG. intros x Hx. apply Z.eqb_neq. exact (grp_ne x Hx). Qed.
  Lemma hg_ne : hg <> m. Proof using Hhg HNG st. clear - Hhg HNG st. exact (grp_ne hg Hhg). Qed.
  Lemma hg_neb : (hg =? m) = false. Proof using Hhg HNG st. clear - Hhg HNG st. exact (grp_neb hg Hhg). Qed.
  Lemma h_wfg : wf_group st L hg. Proof using Hhg HWF RN. clear - Hhg HWF RN. exact (wG_each st L (WF_groups st L HWF) hg Hhg). Qed.
  Lemma h_str : 16 <= strideH /\ strideH mod 16 = 0. Proof using Hhg HWF L RN. clear - Hhg HWF L RN. exact (wg_stride st L hg h_wfg). Qed.
  Lemma Ess : start = g_mem st hg + 16 + strideH * hi. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. unfold g_slot_start, UNIT. reflexivity. Qed.
  Lemma Ese : g_slot_end st hg hi = start + strideH - 4. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. unfold g_slot_end, IB. reflexivity. Qed.
  Lemma h_rng : HEAPLO + 16 <= start /\ start + strideH - 4 < gspan st hg /\ gspan st hg <= CEIL /\ 0 <= strideH * hi.
  Proof using Hhi Hhg HWF L. clear - Hhi Hhg HWF L. exact (MhEnfr.t_rng st L hg hi HWF Hhg Hhi). Qed.
  Lemma h_ess : start = g_mem st hg + 16 + strideH * hi.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. unfold g_slot_start, UNIT. reflexivity. Qed.
  Lemma p_rng : start <= p /\ p + 16 + size * cnt <= start + strideH /\ HEAPLO + 16 <= p /\ p + 16 + size * cnt <= CEIL + 3 /\ p mod 16 = 0.
  Proof using Hptr Hroom Hoff Hhi Hhg HWF L. clear - Hptr Hroom Hoff Hhi Hhg HWF L.
    pose proof h_rng as (R1 & R2 & R3 & R4). destruct Hptr as (P16 & _). pose proof Hroom as RM. unfold p, UNIT in *.
    rewrite (Z.mul_comm cnt size) in RM.
    split. { clear -Hoff. lia. } split. { clear -RM Hoff. lia. } split. { clear -R1 Hoff. lia. } split. { clear - RM R1 R2 R3 Hoff. lia. } exact P16.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_areas : s_areas st' = areas. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_flist : s_flist st' = s_flist st. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_alist : forall s0, s_alist st' s0 = if s0 =? sc then [m] else s_alist st s0. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_alist_sc : s_alist st' sc = [m]. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. rewrite e_alist, Z.eqb_refl. reflexivity. Qed.
  Lemma e_groups : s_groups st' = m :: s_groups st. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_regions : s_regions st' = regions. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_brk : s_brk st' = s_brk st. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = zremove m (s_limbo st). Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_meta : forall x, s_meta st' x = b_meta x. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.
  Lemma e_meta_old : forall x, x <> m -> s_meta st' x = s_meta st x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros x Hx. rewrite e_meta. unfold b_meta. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_meta_grp : forall x, is_group st x -> s_meta st' x = s_meta st x.
  Proof using HNG. clear - HNG. intros x Hx. apply e_meta_old. exact (grp_ne x Hx). Qed.
  Lemma e_meta_m : s_meta st' m = MR m m p av fr W.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. rewrite e_meta. unfold b_meta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_kind_old : forall x, x <> m -> s_kind st' x = s_kind st x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros x Hx. cbn. unfold b_kind. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_kind_m : s_kind st' m = GNest hg hi off.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. cbn. unfold b_kind. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_ai_old : forall x, x <> m -> s_ai st' x = s_ai st x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros x Hx. cbn. unfold b_ai. rewrite (proj2 (Z.eqb_neq x m) Hx). reflexivity. Qed.
  Lemma e_ai_m : s_ai st' m = aidx.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. cbn. unfold b_ai. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_m : forall k, s_slot st' m k = nslot k.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros k. cbn. unfold b_slot. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_hi : s_slot st' hg hi = SHost m off.
  Proof using Hhg HNG. clear - Hhg HNG. cbn. unfold b_slot. rewrite hg_neb, !Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_old : forall x k, x <> m -> (x <> hg \/ k <> hi) -> s_slot st' x k = s_slot st x k.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros x k Hx H. cbn. unfold b_slot. rewrite (proj2 (Z.eqb_neq x m) Hx).
    destruct (Z.eqb_spec x hg); destruct (Z.eqb_spec k hi); cbn; try reflexivity. exfalso; lia.
  Qed.
  Lemma e_slot_other : forall x k, is_group st x -> x <> hg -> s_slot st' x k = s_slot st x k.
  Proof using HNG. clear - HNG. intros x k Hx Hne. apply e_slot_old; [exact (grp_ne x Hx) | left; exact Hne]. Qed.
  Lemma e_slot_hg : forall k, k <> hi -> s_slot st' hg k = s_slot st hg k.
  Proof using Hhg HNG. clear - Hhg HNG. intros k Hk. apply e_slot_old; [exact hg_ne | right; exact Hk]. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> x = m \/ is_group st x.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros x. unfold is_group. rewrite e_groups. cbn. split; intros [A|A]; auto. Qed.
  Lemma n_is_group : is_group st' m. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. apply e_is_group. left. reflexivity. Qed.
  Lemma h_is_group : is_group st' hg. Proof using Hhg. clear - Hhg. apply e_is_group. right. exact Hhg. Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x. Proof using Husage Haidx Hcnt Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hscj Hsc Hhi. intros; unfold metaU; rewrite e_areas; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x \/ x = m.
  Proof using Hnil Hsc. clear - Hnil Hsc.
    intros x. unfold in_alist. split.
    - intros (s0 & Hs & Hin). rewrite e_alist in Hin. destruct (Z.eqb_spec s0 sc) as [->|Hne]; [destruct Hin as [<-|[]]; right; reflexivity | left; exists s0; split; assumption].
    - intros [(s0 & Hs & Hin)| ->].
      + exists s0. split; [exact Hs|]. rewrite e_alist. destruct (Z.eqb_spec s0 sc) as [->|Hne]; [rewrite Hnil in Hin; destruct Hin | exact Hin].
      + exists sc. split; [exact Hsc|]. rewrite e_alist_sc. left. reflexivity.
  Qed.
  Lemma e_in_flist : forall x, in_flist st' x <-> in_flist st x. Proof using Husage Haidx Hcnt Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hscj Hsc Hhi. intros; unfold in_flist; rewrite e_flist; tauto. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x \/ x = m.
  Proof using Husage Haidx Hcnt Hnil Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hnil Hscj Hsc Hhi. intros x. unfold listed. rewrite e_in_alist, e_in_flist. tauto. Qed.
  Lemma e_listed_other : forall x, x <> m -> (listed st' x <-> listed st x).
  Proof using Husage Haidx Hcnt Hnil Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hnil Hscj Hsc Hhi. intros x Hx. rewrite e_listed. split; [intros [A| ->]; [exact A | exfalso; exact (Hx eq_refl)] | intros A; left; exact A]. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> fresh st x.
  Proof using Husage Haidx Hcnt Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hscj Hsc Hhi. intros x. unfold fresh. cbn [s_ctx st' cx_set_grp c_avail_cnt s_areas]. tauto. Qed.
  Lemma e_areab : forall x, areab st' x <-> areab st x. Proof using Husage Haidx Hcnt Hscj Hsc Hhi. clear - Husage Haidx Hcnt Hscj Hsc Hhi. intros; unfold areab; rewrite e_areas; tauto. Qed.
  Lemma listed_ne : forall x, listed st x -> x <> m.
  Proof using Hunl. clear - Hunl. intros x Hl ->. exact (Hunl Hl). Qed.
  Lemma alist_grp : forall s0 x, In x (s_alist st s0) -> is_group st x.
  Proof using HWF L RN. clear - HWF L RN. intros s0 x Hin. exact (proj1 (proj2 (wl_aU st (WF_lists st L HWF) s0 x Hin))). Qed.

  (* [comment removed for export] *)
  Lemma n_gW : g_W st' m = W. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. unfold g_W. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_gmem : g_mem st' m = p. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. unfold g_mem. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_glast : g_lastidx st' m = cnt - 1. Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold g_lastidx. rewrite n_gW. exact (proj1 W_fields). Qed.
  Lemma n_gcnt : g_cnt st' m = cnt. Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold g_cnt. rewrite n_glast. lia. Qed.
  Lemma n_gsc : g_sc st' m = sc. Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold g_sc. rewrite n_gW. exact (proj1 (proj2 (proj2 W_fields))). Qed.
  Lemma n_gml : g_maplen st' m = 0. Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold g_maplen. rewrite n_gW. exact (proj2 (proj2 (proj2 W_fields))). Qed.
  Lemma n_gstride : g_stride st' m = size.
  Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold g_stride. rewrite n_gml, n_glast, n_gsc. reflexivity. Qed.
  Lemma n_gss : forall k, g_slot_start st' m k = p + 16 + size * k.
  Proof using Hcnt Hsc. clear - Hcnt Hsc. intros k. unfold g_slot_start, UNIT. rewrite n_gmem, n_gstride. reflexivity. Qed.
  Lemma n_gse : forall k, g_slot_end st' m k = p + 16 + size * k + size - 4.
  Proof using Hcnt Hsc. clear - Hcnt Hsc. intros k. unfold g_slot_end, IB. rewrite n_gss, n_gstride. reflexivity. Qed.
  Lemma n_gspan : gspan st' m = p + 16 + size * cnt - 3.
  Proof using Hcnt Hsc. clear - Hcnt Hsc. unfold gspan, g_span_end, UNIT, IB. rewrite n_gmem, n_gstride, n_gcnt. lia. Qed.
  Lemma n_avail : mr_avail (s_meta st' m) = av. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. rewrite e_meta_m. reflexivity. Qed.
  Lemma n_freed : mr_freed (s_meta st' m) = fr. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. rewrite e_meta_m. reflexivity. Qed.

  Lemma SGB : sub_groupsB st st' hg.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG.
    constructor.
    - intros x Hx. apply e_is_group. right. exact Hx.
    - intros x Hx. apply e_kind_old. exact (grp_ne x Hx).
    - intros x k Hx Hne. rewrite e_slot_other by assumption. apply slot_sim_refl.
    - intros k q n o r. destruct (Z.eq_dec k hi) as [->|Hk]; [rewrite e_slot_hi, Hslot; split; intros X; discriminate X|].
      rewrite e_slot_hg by exact Hk. tauto.
    - intros x Hx. rewrite e_meta_grp by exact Hx. reflexivity.
    - intros x Hx. rewrite e_meta_grp by exact Hx. reflexivity.
  Qed.
  #[local] Notation yG := (SGB).
  Lemma e_gW : forall x, is_group st x -> g_W st' x = g_W st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gW st st' hg yG). Qed.
  Lemma e_gmem : forall x, is_group st x -> g_mem st' x = g_mem st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gmem st st' hg yG). Qed.
  Lemma e_glast : forall x, is_group st x -> g_lastidx st' x = g_lastidx st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_glast st st' hg yG). Qed.
  Lemma e_gcnt : forall x, is_group st x -> g_cnt st' x = g_cnt st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gcnt st st' hg yG). Qed.
  Lemma e_gsc : forall x, is_group st x -> g_sc st' x = g_sc st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gsc st st' hg yG). Qed.
  Lemma e_gml : forall x, is_group st x -> g_maplen st' x = g_maplen st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gml st st' hg yG). Qed.
  Lemma e_gstride : forall x, is_group st x -> g_stride st' x = g_stride st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gstride st st' hg yG). Qed.
  Lemma e_gss : forall x k, is_group st x -> g_slot_start st' x k = g_slot_start st x k. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gss st st' hg yG). Qed.
  Lemma e_gse : forall x k, is_group st x -> g_slot_end st' x k = g_slot_end st x k. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gse st st' hg yG). Qed.
  Lemma e_gspan : forall x, is_group st x -> gspan st' x = gspan st x. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_gspan st st' hg yG). Qed.
  Lemma e_inband : forall x q, is_group st x -> inband st' x q = inband st x q. Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. exact (v_inband st st' hg yG). Qed.
  Lemma e_endb : forall x, is_group st x -> (endb_own st' x <-> endb_own st x). Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. exact (v_endb st st' L hg yG HWF). Qed.
  Lemma e_avail : forall x, is_group st x -> mr_avail (s_meta st' x) = mr_avail (s_meta st x). Proof using HNG. clear - HNG. intros; rewrite e_meta_grp by assumption; reflexivity. Qed.
  Lemma e_freed : forall x, is_group st x -> mr_freed (s_meta st' x) = mr_freed (s_meta st x). Proof using HNG. clear - HNG. intros; rewrite e_meta_grp by assumption; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma n_endb : endb_own st' m <-> p + 12 + size * cnt < start + strideH - 4.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. unfold endb_own. rewrite e_kind_m, n_gspan, (e_gse hg hi Hhg), Ese. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation Zn y := (start - 3 <= y < start + strideH - 4).
  Lemma n_gcell : forall y, gcell st' m y -> p <= y <= p + 12 + size * cnt /\ y < start + strideH - 4.
  Proof using Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    intros y G. pose proof p_rng as (P1 & P2 & _). pose proof size_facts as (S16 & _).
    assert (0 <= size * cnt) by (apply Z.mul_nonneg_nonneg; lia).
    unfold gcell in G. rewrite n_gmem, n_gcnt, n_glast in G.
    destruct G as [G|[G|[G|G]]].
    - lia.
    - destruct G as (k & Hk & E & C). rewrite n_gss in E.
      assert (0 <= size * k <= size * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
      destruct C as [C|C].
      + assert (size * (k + 1) <= size * cnt) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
      + apply n_endb in C. lia.
    - destruct G as (k & q & Hk & Hp & R). unfold slot_ptr in Hp. rewrite e_slot_m, n_gss in Hp.
      destruct (nslot_cases aidx k) as [[-> E]|[( _ & _ & E)|(_ & _ & E)]]; rewrite E in Hp; try discriminate Hp. injection Hp. intros <-. lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & _). rewrite e_slot_m in Hs. exfalso. exact (nslot_nouser aidx k _ _ _ _ Hs).
  Qed.
  Lemma n_garbage_k : forall k y, garbage st' m k y ->
    0 <= k <= cnt - 1 /\ p + 13 + size * k <= y /\ y < p + 12 + size * (k + 1) /\ p + 16 <= y.
  Proof using H2048 Husage Hcnt Hsc. clear - H2048 Husage Hcnt Hsc.
    intros k y G. pose proof size_facts as (S16 & _).
    unfold garbage in G. rewrite n_glast, e_slot_m, n_gss, n_gse in G. destruct G as [Hk G].
    destruct (nslot_cases aidx k) as [[-> E]|[(K0 & _ & E)|(K0 & _ & E)]]; rewrite E in G.
    - rewrite !Z.mul_0_r, !Z.add_0_r in G. rewrite Z.mul_0_r, Z.mul_1_r. lia.
    - assert (size * 1 <= size * k) by (apply Z.mul_le_mono_nonneg_l; lia). rewrite Z.mul_add_distr_l, Z.mul_1_r. lia.
    - assert (size * 1 <= size * k) by (apply Z.mul_le_mono_nonneg_l; lia). rewrite Z.mul_add_distr_l, Z.mul_1_r. lia.
  Qed.
  Lemma n_garbage : forall k y, garbage st' m k y -> p + 16 <= y < p + 12 + size * cnt.
  Proof using H2048 Husage Hcnt Hsc. clear - H2048 Husage Hcnt Hsc.
    intros k y G. destruct (n_garbage_k k y G) as (Hk & R1 & R2 & R3). pose proof size_facts as (S16 & _).
    assert (size * (k + 1) <= size * cnt) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.
  Lemma n_gcell_where : forall y, gcell st' m y -> y < p + 16 \/ exists k', 0 <= k' <= cnt /\ y = p + 12 + size * k'.
  Proof using Hcnt Hsc. clear - Hcnt Hsc.
    intros y G. unfold gcell in G. rewrite n_gmem, n_gcnt, n_glast in G.
    destruct G as [G|[G|[G|G]]].
    - left. lia.
    - destruct G as (k & Hk & E & _). rewrite n_gss in E. right. exists k. split; [exact Hk | lia].
    - destruct G as (k & q & Hk & Hp & R). unfold slot_ptr in Hp. rewrite e_slot_m, n_gss in Hp.
      destruct (nslot_cases aidx k) as [[-> E]|[( _ & _ & E)|(_ & _ & E)]]; rewrite E in Hp; try discriminate Hp. injection Hp. intros <-. left. lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & _). rewrite e_slot_m in Hs. exfalso. exact (nslot_nouser aidx k _ _ _ _ Hs).
  Qed.
  Lemma n_garb_cell : forall k y, garbage st' m k y -> gcell st' m y -> False.
  Proof using H2048 Husage Hcnt Hsc. clear - H2048 Husage Hcnt Hsc.
    intros k y G C. pose proof size_facts as (S16 & _). destruct (n_garbage_k k y G) as (Hk & R1 & R2 & R3).
    destruct (n_gcell_where y C) as [Y|(k' & Hk' & ->)]; [lia|].
    apply (no_mult_between size k k'); lia.
  Qed.
  Lemma n_nouser : forall x k q n o r, is_group st' x -> ~ is_group st x -> s_slot st' x k <> SUser q n o r.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros x k q n o r Hx NG. apply e_is_group in Hx. destruct Hx as [->|Hx]; [|exfalso; exact (NG Hx)].
    rewrite e_slot_m. apply nslot_nouser.
  Qed.
  Lemma e_appb : forall x, appb st' x <-> appb st x.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG.
    intros x. split; [apply (v_appb_back st st' hg yG); exact n_nouser | apply (v_appb st st' hg yG)].
  Qed.

  (* [comment removed for export] *)
  Lemma z_other_cell : forall x a, is_group st x -> x <> hg -> gcell st x a -> Zn a -> False.
  Proof using Hslot Hhi Hhg HWF L RN. clear - Hslot Hhi Hhg HWF L RN. exact (MhEnfr.frame_other_cell st L hg hi HWF Hhg Hhi Hslot). Qed.
  Lemma z_own_cell : forall a, gcell st hg a -> Zn a -> start - 3 <= a < start.
  Proof using Hslot Hhi Hhg HWF L RN. clear - Hslot Hhi Hhg HWF L RN. exact (MhEnfr.frame_own_cell st L hg hi HWF Hhg Hhi Hslot). Qed.
  Lemma z_app : forall a, appb st a -> Zn a -> False.
  Proof using Hslot Hhi Hhg HWF L RN. clear - Hslot Hhi Hhg HWF L RN. exact (MhEnfr.frame_app st L hg hi HWF Hhg Hhi Hslot). Qed.
  Lemma z_area : forall a, areab st a -> Zn a -> False.
  Proof using Hhi Hhg HWF L RN. clear - Hhi Hhg HWF L RN. exact (MhEnfr.frame_area st L hg hi HWF Hhg Hhi). Qed.
  Lemma z_hdr_cell : forall a, start - 4 <= a < start -> gcell st hg a.
  Proof using Hslot Hhi L. clear - Hslot Hhi L. exact (MhEnfr.junk_hdr_cell st L hg hi Hhi Hslot). Qed.
  (* [comment removed for export] *)
  Lemma z_garbage : forall x k a, is_group st x -> garbage st x k a -> (x <> hg \/ k <> hi) -> start - 3 <= a < start + strideH - 4 + 1 -> False.
  Proof using Hslot Hhi Hhg HWF L RN. clear - Hslot Hhi Hhg HWF L RN.
    intros x k a Hx G NE Ra. rewrite <- Ese in Ra.
    apply (garbage_private st L HWF x k hg hi a Hx Hhg G Hhi); [|exact NE|exact Ra].
    intros c o E. rewrite Hslot in E. discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma h_slots_apart_lo : forall k, 0 <= k -> k < hi -> g_slot_end st hg k + 1 <= start - 3.
  Proof using Hhg HWF L RN. clear - Hhg HWF L RN. intros k Hk Hlt. exact (slots_apart st L HWF hg k hi Hhg Hk Hlt). Qed.
  Lemma h_slots_apart_hi : forall k, hi < k -> start + strideH - 4 + 1 <= g_slot_start st hg k - 3.
  Proof using Hhi Hhg HWF cnt sc L RN. clear - Hhi Hhg HWF cnt sc L RN. intros k Hlt. rewrite <- Ese. exact (slots_apart st L HWF hg hi k Hhg ltac:(lia) Hlt). Qed.

  Lemma h_gcell : forall y, gcell st' hg y -> (gcell st hg y /\ (y <= start - 4 \/ start + strideH - 4 <= y)) \/ (p - 4 <= y < p).
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    intros y G. pose proof h_str as [S16 _]. pose proof h_rng as (R1 & R2 & R3 & R4). pose proof (glast_rng st hg) as GL.
    unfold gcell in G. rewrite (e_gmem hg Hhg), (e_gcnt hg Hhg), (e_glast hg Hhg) in G.
    destruct G as [G|[G|[G|G]]].
    - left. split; [unfold gcell; left; exact G|]. left. rewrite Ess. lia.
    - destruct G as (k & Hk & E & C). rewrite (e_gss hg k Hhg) in E. rewrite (e_endb hg Hhg) in C.
      left. split; [unfold gcell; right; left; exists k; split; [exact Hk | split; [exact E | exact C]]|].
      rewrite E. destruct (Z.le_gt_cases k hi) as [A|A].
      + left. assert (g_stride st hg * k <= g_stride st hg * hi) by (apply Z.mul_le_mono_nonneg_l; lia). unfold g_slot_start in *. lia.
      + right. assert (g_stride st hg * (hi + 1) <= g_stride st hg * k) by (apply Z.mul_le_mono_nonneg_l; lia). unfold g_slot_start in *. lia.
    - destruct G as (k & q & Hk & Hp & R). destruct (Z.eq_dec k hi) as [->|Hk'].
      + unfold slot_ptr in Hp. rewrite e_slot_hi, (e_gss hg hi Hhg) in Hp. injection Hp. intros <-. right. unfold p in *. lia.
      + unfold slot_ptr in Hp. rewrite (e_slot_hg k Hk'), (e_gss hg k Hhg) in Hp.
        left. split; [unfold gcell; right; right; left; exists k, q; split; [exact Hk | split; [unfold slot_ptr; exact Hp | exact R]]|].
        (* [comment removed for export] *)
        pose proof (wg_slots st L hg h_wfg k Hk) as SW.
        assert (QR : g_slot_start st hg k - 4 <= q - 4 /\ q <= g_slot_end st hg k).
        { destruct (s_slot st hg k) as [| |q2 n2 o2 r2|c o2|o2]; try discriminate Hp; injection Hp; intros <-; cbn [slot_wf] in SW.
          - destruct SW as (A1 & A2 & A3 & A4 & A5 & _). unfold g_slot_end, IB in *. lia.
          - destruct SW as (A1 & Hc & _ & Kc & _).
            destruct (nest_facts st L HWF c hg k o2 Hc Kc) as (_ & _ & _ & _ & _ & Emc & Spc & _ & _).
            pose proof (gspan_gt st L HWF c Hc). lia.
          - destruct SW as (A1 & A2 & _). unfold g_slot_end, IB in *. lia. }
        destruct (Z.lt_ge_cases k hi) as [A|A].
        * left. pose proof (h_slots_apart_lo k ltac:(lia) A). lia.
        * right. pose proof (h_slots_apart_hi k ltac:(lia)). lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). destruct (Z.eq_dec k hi) as [->|Hk']; [rewrite e_slot_hi in Hs; discriminate Hs|].
      rewrite (e_slot_hg k Hk') in Hs. rewrite (e_gse hg k Hhg) in Ha.
      left. split; [unfold gcell; right; right; right; exists k, q, n2, o2, r2; split; [exact Hk | split; [exact Hs | exact Ha]]|].
      pose proof (wg_slots st L hg h_wfg k Hk) as SW. rewrite Hs in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & A3 & A4 & _).
      assert (QR : g_slot_start st hg k <= q /\ q + n2 <= g_slot_end st hg k) by (unfold g_slot_end, IB in *; lia).
      assert (EK : g_slot_end st hg k = g_slot_start st hg k + strideH - 4) by (unfold g_slot_end, IB; reflexivity).
      destruct (Z.lt_ge_cases k hi) as [A|A].
      * left. pose proof (h_slots_apart_lo k ltac:(lia) A). lia.
      * right. pose proof (h_slots_apart_hi k ltac:(lia)). lia.
  Qed.

  Lemma h_garbage : forall k y, garbage st' hg k y ->
    (k <> hi /\ garbage st hg k y) \/ (k = hi /\ ((start - 3 <= y < p - 4) \/ (p + 13 + size * cnt <= y < start + strideH - 4))).
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    intros k y G. destruct (Z.eq_dec k hi) as [->|Hk].
    - right. split; [reflexivity|]. unfold garbage in G. rewrite e_slot_hi, (e_glast hg Hhg), (e_gss hg hi Hhg), (e_gse hg hi Hhg), n_gspan, Ese in G.
      destruct G as [_ [G|G]]; unfold p in *; [left | right]; lia.
    - left. split; [exact Hk|]. unfold garbage in G |- *.
      rewrite (e_glast hg Hhg), (e_gss hg k Hhg), (e_gse hg k Hhg), (e_slot_hg k Hk) in G. destruct G as [Hkr G]. split; [exact Hkr|].
      destruct (s_slot st hg k) as [| |q n o r|c o|o] eqn:Sk; try exact G.
      rewrite (e_gspan c) in G; [exact G|]. exact (proj1 (child_facts st L HWF hg k c o Hhg Hkr Sk)).
  Qed.

  (* [comment removed for export] *)
  Lemma any_cell : forall x a, is_group st' x -> gcell st' x a ->
    (is_group st x /\ gcell st x a /\ (x = hg -> a <= start - 4 \/ start + strideH - 4 <= a)) \/
    (x = m /\ p <= a <= p + 12 + size * cnt /\ a < start + strideH - 4) \/
    (x = hg /\ p - 4 <= a < p).
  Proof using Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    intros x a Hx G. apply e_is_group in Hx. destruct (Z.eq_dec x m) as [->|Hxm].
    - right; left. split; [reflexivity | exact (n_gcell a G)].
    - destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|]. destruct (Z.eq_dec x hg) as [->|Hxh].
      + destruct (h_gcell a G) as [[G0 R]|R]; [left | right; right]; [split; [exact Hhg | split; [exact G0 | intros _; exact R]] | split; [reflexivity | exact R]].
      + left. split; [exact Hx|]. split; [apply (v_gcell st st' L hg yG HWF x a Hx Hxh); exact G | intros E; exfalso; exact (Hxh E)].
  Qed.
  Lemma any_garb : forall x k a, is_group st' x -> garbage st' x k a ->
    (is_group st x /\ garbage st x k a /\ (x <> hg \/ k <> hi)) \/
    (x = m /\ p + 16 <= a < p + 12 + size * cnt) \/
    (x = hg /\ k = hi /\ ((start - 3 <= a < p - 4) \/ (p + 13 + size * cnt <= a < start + strideH - 4))).
  Proof using H2048 Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - H2048 Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    intros x k a Hx G. apply e_is_group in Hx. destruct (Z.eq_dec x m) as [->|Hxm].
    - right; left. split; [reflexivity | exact (n_garbage k a G)].
    - destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|]. destruct (Z.eq_dec x hg) as [->|Hxh].
      + destruct (h_garbage k a G) as [[Hk G0]|R]; [left | right; right]; [split; [exact Hhg | split; [exact G0 | right; exact Hk]] | split; [reflexivity | exact R]].
      + left. split; [exact Hx|]. split; [apply (v_garbage st st' L hg yG HWF x k a Hx Hxh); exact G | left; exact Hxh].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_ctx : wf_ctx st'.
  Proof using Husage HWF L. clear - Husage HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat fupd]; try assumption.
    - intros s0 Hs0. unfold fupd. destruct (Z.eqb_spec s0 sc) as [->|NE]; [reflexivity | exact (A4 s0 Hs0)].
    - intros s0. unfold fupd. destruct (Z.eqb_spec s0 sc); [exact Husage | exact (A13 s0)].
  Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HWF L. clear - HWF L. destruct (WF_areas st L HWF) as [A B C D]. constructor; rewrite ?e_areas, ?e_regions, ?e_brk; assumption. Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg Hunl HNG HU HWF L RN. clear - Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg Hunl HNG HU HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist.
    - apply (dll_ext st st'); [|exact D1]. intros x Hx. rewrite e_meta_old by (apply listed_ne; left; exact Hx). split; reflexivity.
    - exact ND1.
    - intros x Hx. pose proof (FU x Hx) as (U & NG & NF & R). rewrite e_metaU, e_is_group, e_fresh, e_meta_old by (apply listed_ne; left; exact Hx).
      split; [exact U|]. split; [|split; [exact NF | exact R]]. intros [E|G]; [apply Hunl; left; rewrite <- E; exact Hx | exact (NG G)].
    - intros s0 Hs0. rewrite e_alist. destruct (Z.eqb_spec s0 sc) as [->|Hne].
      + apply (proj2 (dll_dllf st' [m])). apply dllf_single; rewrite e_meta_m; reflexivity.
      + apply (dll_ext st st'); [|exact (D2 s0 Hs0)]. intros x Hx. rewrite e_meta_grp by exact (alist_grp s0 x Hx). split; reflexivity.
    - intros s0. rewrite e_alist. destruct (Z.eqb_spec s0 sc) as [->|Hne]; [|exact (ND2 s0)].
      apply base.NoDup_cons_2; [|apply base.NoDup_nil_2]. intros E. destruct (proj1 (base.list_elem_of_In _ _) E).
    - intros s0 x Hin. rewrite e_alist in Hin. destruct (Z.eqb_spec s0 sc) as [->|Hne].
      + destruct Hin as [<-|[]]. rewrite e_is_group, n_gsc. split; [exact Hsc|]. split; [left; reflexivity | reflexivity].
      + rewrite e_is_group, e_gsc by exact (alist_grp s0 x Hin). pose proof (AU s0 x Hin) as (X1 & X2 & X3). auto.
    - intros s0 Hs0. rewrite e_alist. destruct (Z.eqb_spec s0 sc) as [->|Hne]; [exfalso; lia | exact (AN s0 Hs0)].
    - intros x U NL. rewrite e_listed in NL. apply e_metaU in U. rewrite e_meta. unfold b_meta.
      destruct (Z.eqb_spec x m) as [->|Hx]; [exfalso; apply NL; right; reflexivity|].
      apply (LK x U). intros Hl. apply NL. left. exact Hl.
    - intros x Hl. rewrite e_listed in Hl. rewrite e_meta. unfold b_meta. destruct (Z.eqb_spec x m) as [->|Hx].
      + cbn [mr_next mr_prev]. pose proof m_rng. unfold HEAPLO in *. lia.
      + destruct Hl as [Hl|E]; [exact (LKD x Hl) | exfalso; exact (Hx E)].
    - intros s0 x Hin Hne. rewrite e_alist in Hin, Hne. destruct (Z.eqb_spec s0 sc) as [->|Hs].
      + exfalso. destruct Hin as [<-|[]]. apply Hne. reflexivity.
      + rewrite e_avail, e_freed by exact (alist_grp s0 x Hin). exact (RS s0 x Hin Hne).
  Qed.

  Lemma t_wf_group_old : forall x, is_group st x -> x <> hg -> wf_group st' L x.
  Proof using Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNG HWF RN. clear - Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNG HWF RN.
    intros x Hx Hxh. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG. pose proof (grp_ne x Hx) as Hxm.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_alist, ?e_avail, ?e_freed by exact Hx;
      rewrite ?(e_ai_old x Hxm), ?(e_kind_old x Hxm); try assumption.
    - intros k Hk. rewrite e_slot_other by assumption. exact (Av k Hk).
    - intros k Hk. rewrite e_slot_other by assumption. exact (Fr k Hk).
    - intros k Hk. rewrite e_slot_other by assumption. exact (Avai k Hk).
    - intros k Hk. rewrite e_slot_other by assumption. exact (High k Hk).
    - intros Hl. apply e_in_alist in Hl. destruct Hl as [Hl|E]; [|exfalso; exact (Hxm E)]. pose proof (Lsc Hl) as Hin.
      destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [rewrite E, Hnil in Hin; destruct Hin | exact Hin].
    - intros H63 Hl. apply (e_listed_other x Hxm) in Hl. exact (S63 H63 Hl).
    - intros Hp. pose proof (Part Hp) as Hin. destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [rewrite E, Hnil in Hin; destruct Hin | exact Hin].
    - intros Hall Hne. rewrite (e_listed_other x Hxm). apply Full.
      + intros k Hk. rewrite <- (e_slot_other x k Hx Hxh). exact (Hall k Hk).
      + destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [|exact Hne]. rewrite E, Hnil. cbn [head_of].
        pose proof (group_pos st L HWF x Hx) as GP. unfold HEAPLO in GP. clear -GP. lia.
    - destruct (s_kind st x) as [|hm j hoff].
      + destruct Kind as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [rewrite e_regions; exact K2|]. split; assumption.
      + destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride by exact K2.
        assert (HG : is_group st' hm) by (apply e_is_group; right; exact K2).
        assert (SL : s_slot st' hm j = SHost x hoff).
        { rewrite e_slot_old; [exact K6 | exact (grp_ne hm K2) |]. destruct (Z.eq_dec hm hg) as [->|NE]; [right | left; exact NE].
          intros ->. rewrite Hslot in K6. discriminate K6. }
        repeat (split; [assumption|]). assumption.
    - intros Hall. assert (X : s_kind st x = GTop /\ g_sc st x < 48 /\ In x (s_alist st (g_sc st x))).
      { apply FF. intros k Hk. rewrite <- (e_slot_other x k Hx Hxh). exact (Hall k Hk). }
      destruct X as (X1 & X2 & X3). destruct (Z.eqb_spec (g_sc st x) sc) as [E|NE]; [rewrite E, Hnil in X3; destruct X3|].
      split; [exact X1 | split; [exact X2 | exact X3]].
    - intros k Hk. rewrite e_slot_other by assumption. apply (v_slot_wf_same st st' L hg yG); [exact Hx|]. exact (Slots k Hk).
    - apply (v_depth st st' L hg yG HWF); [exact Hx | exact Depth].
    - intros Hsc0 Hst k Hk. rewrite e_slot_other by assumption. exact (Fit Hsc0 Hst k Hk).
  Qed.

  Lemma gsc_hg_neb : (g_sc st hg =? sc) = false.
  Proof using Hscj cnt. clear - Hscj cnt. apply Z.eqb_neq. lia. Qed.

  Lemma t_wf_group_hg : wf_group st' L hg.
  Proof using Hptr Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNG HWF RN. clear - Hptr Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNG HWF RN.
    pose proof h_wfg as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_alist, ?e_avail, ?e_freed by exact Hhg;
      rewrite ?(e_ai_old hg hg_ne), ?(e_kind_old hg hg_ne), ?gsc_hg_neb; try assumption.
    - intros k Hk. destruct (Z.eq_dec k hi) as [->|NE]; [|rewrite e_slot_hg by exact NE; exact (Av k Hk)].
      rewrite e_slot_hi. split; [intros T; destruct (proj1 (Av hi Hk) T) as [_ E]; rewrite Hslot in E; discriminate E | intros [_ E]; discriminate E].
    - intros k Hk. destruct (Z.eq_dec k hi) as [->|NE]; [|rewrite e_slot_hg by exact NE; exact (Fr k Hk)].
      rewrite e_slot_hi. split; [intros T; destruct (proj1 (Fr hi Hk) T) as [_ E]; rewrite Hslot in E; discriminate E | intros [_ E]; discriminate E].
    - intros k Hk E. destruct (Z.eq_dec k hi) as [->|NE]; [rewrite e_slot_hi in E; discriminate E | rewrite e_slot_hg in E by exact NE; exact (Avai k Hk E)].
    - intros k Hk. destruct (Z.eq_dec k hi) as [->|NE]; [exfalso; pose proof (High hi Hk) as E; rewrite Hslot in E; discriminate E | rewrite e_slot_hg by exact NE; exact (High k Hk)].
    - intros Hl. apply e_in_alist in Hl. destruct Hl as [Hl|E]; [exact (Lsc Hl) | exfalso; exact (hg_ne E)].
    - intros H63. exfalso. lia.
    - intros Hall Hne. rewrite (e_listed_other hg hg_ne). apply Full; [|exact Hne].
      intros k Hk. destruct (Z.eq_dec k hi) as [->|NE]; [rewrite Hslot; split; discriminate | rewrite <- (e_slot_hg k NE); exact (Hall k Hk)].
    - destruct (s_kind st hg) as [|hm j hoff].
      + destruct Kind as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [rewrite e_regions; exact K2|]. split; assumption.
      + destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride by exact K2.
        assert (HG : is_group st' hm) by (apply e_is_group; right; exact K2).
        assert (SL : s_slot st' hm j = SHost hg hoff) by (rewrite e_slot_other; [exact K6 | exact K2 | exact K3]).
        repeat (split; [assumption|]). assumption.
    - intros Hall. exfalso. destruct (Hall hi Hhi) as [E|E]; rewrite e_slot_hi in E; discriminate E.
    - intros k Hk. destruct (Z.eq_dec k hi) as [->|NE].
      + rewrite e_slot_hi. cbn [slot_wf]. rewrite (e_gss hg hi Hhg), e_kind_m.
        split; [exact Hoff|]. split; [exact n_is_group|]. split; [exact (fun E => hg_ne (eq_sym E))|]. split; [reflexivity|].
        apply (v_ptr_ok st st' hg yG hg hi); [exact Hhg|]. exact Hptr.
      + rewrite e_slot_hg by exact NE. apply (v_slot_wf_same st st' L hg yG); [exact Hhg|]. exact (Slots k Hk).
    - apply (v_depth st st' L hg yG HWF); [exact Hhg | exact Depth].
    - intros Hsc0 Hst k Hk. destruct (Z.eq_dec k hi) as [->|NE]; [rewrite e_slot_hi; split; discriminate | rewrite e_slot_hg by exact NE; exact (Fit Hsc0 Hst k Hk)].
  Qed.

  (* [comment removed for export] *)
  Lemma log2_half : forall x, 2 <= x -> Z.log2 (x / 2) = Z.log2 x - 1.
  Proof using cnt sc. clear - cnt sc.
    intros x Hx.
    assert (E : x / 2 = Z.shiftr x 1) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    rewrite E, Z.log2_shiftr by lia.
    assert (1 <= Z.log2 x) by (apply Z.log2_le_pow2; [lia | change (2 ^ 1) with 2; lia]). lia.
  Qed.
  Lemma dbound_host : forall s t, 16 <= s <= 1016 -> 2 * s + 16 <= t -> (S (dbound t) <= dbound s)%nat.
  Proof using cnt sc. clear - cnt sc.
    intros s t Hs Ht. unfold dbound.
    set (x := 2064 / (s + 16)).
    assert (X2 : 2 <= x). { subst x. apply Z.div_le_lower_bound; lia. }
    assert (HT : 2064 / (t + 16) <= x / 2).
    { subst x. rewrite Z.div_div by lia. apply Z.div_le_compat_l; lia. }
    assert (L1 : Z.log2 (2064 / (t + 16)) <= Z.log2 (x / 2)) by (apply Z.log2_le_mono; exact HT).
    rewrite log2_half in L1 by exact X2.
    pose proof (Z.log2_nonneg (2064 / (t + 16))). lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma t_wf_group_new : wf_group st' L m.
  Proof using Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF RN. clear - Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF RN.
    pose proof p_rng as (P0 & P1 & P2 & P3 & P16). pose proof W_rng as WR. pose proof W_fields as (F1 & F2 & F3 & F4).
    pose proof size_facts as (S16 & Smod & S1016). pose proof (size_class_pos sc Hsc) as [SC1 SC2]. pose proof h_str as [H16 _].
    assert (HC1 : 1 <= cnt <= 32) by lia.
    constructor; rewrite ?n_gW, ?n_gmem, ?n_glast, ?n_gcnt, ?n_gsc, ?n_gml, ?n_gstride, ?e_alist_sc, ?n_avail, ?n_freed, ?e_ai_m, ?e_kind_m.
    - apply e_metaU. exact HU.
    - rewrite e_fresh. exact HNF.
    - exact WR.
    - exact (av_rng cnt aidx HC1 Haidx).
    - exact (fr_rng cnt aidx HC1 Haidx).
    - ceil; unfold UNIT, HEAPLO in *. split; [lia|]. split; [exact P16 | lia].
    - lia.
    - exact F2.
    - left. lia.
    - split; [exact S16 | exact Smod].
    - intros k Hk. rewrite e_slot_m. exact (av_slot cnt aidx Haidx k Hk).
    - intros k Hk. rewrite e_slot_m. exact (fr_slot cnt aidx Haidx k Hk).
    - intros k Hk E. rewrite e_slot_m in E. destruct (nslot_cases aidx k) as [[-> E']|[(A & B & E')|(A & B & E')]]; rewrite E' in E; try discriminate E. lia.
    - intros k Hk. rewrite e_slot_m. destruct (nslot_cases aidx k) as [[-> E']|[(A & B & E')|(A & B & E')]]; [lia | lia | exact E'].
    - intros _. left. reflexivity.
    - rewrite e_in_flist. intros F. apply Hunl. left. exact F.
    - lia.
    - intros _. left. reflexivity.
    - intros _ Hne. exfalso. apply Hne. reflexivity.
    - (* [comment removed for export] *)
      rewrite (e_glast hg Hhg), (e_gsc hg Hhg), (e_gss hg hi Hhg), (e_gstride hg Hhg), e_slot_hi.
      split; [reflexivity|]. split; [exact h_is_group|]. split; [exact hg_ne|]. split; [exact Hhi|]. split; [exact Hoff|].
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. unfold UNIT, IB in *. split; [lia|]. split; [lia | lia].
    - intros _ Hlt. exfalso. rewrite size_eq in Hlt. lia.
    - intros Hall. exfalso. destruct (Hall 0 ltac:(lia)) as [E|E]; rewrite e_slot_m in E; discriminate E.
    - intros k Hk. rewrite e_slot_m. destruct (nslot_cases aidx k) as [[-> E']|[(A & B & E')|(A & B & E')]]; rewrite E'; [|exact I|exact I].
      cbn [slot_wf]. rewrite n_gss, n_gstride. split; [lia|]. split; [unfold IB; lia|].
      unfold ptr_ok, inband. rewrite n_gmem, n_gsc, n_gml. unfold UNIT. rewrite !Z.mul_0_r, !Z.add_0_r.
      replace (p + 16 - p - 16) with 0 by lia. change (0 / 16) with 0. change (0 mod 16) with 0.
      repeat split; try lia.
    - (* [comment removed for export] *)
      pose proof (dbound_host size strideH ltac:(lia) ltac:(unfold UNIT in Hroom; nia)) as DB.
      destruct (dbound size) as [|f] eqn:E; [lia|]. cbn. unfold b_kind. rewrite Z.eqb_refl.
      apply (v_depth st st' L hg yG HWF f hg Hhg). apply (nest_depth_mono st (dbound strideH)); [lia|].
      exact (wg_dbound st L hg h_wfg).
    - intros _ Hlt k Hk. exfalso. rewrite size_eq in Hlt. lia.
    - intros K. exfalso. discriminate K.
    - intros _. pose proof H2048 as B. unfold UNIT in B. rewrite (Z.mul_comm size cnt). clear -B. lia.
    - exact Hpnd.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma old_slot : forall x k, is_group st x -> s_slot st' x k = s_slot st x k \/ (x = hg /\ k = hi).
  Proof using Hhg HNG. clear - Hhg HNG.
    intros x k Hx. destruct (Z.eq_dec x hg) as [->|NE]; [|left; exact (e_slot_other x k Hx NE)].
    destruct (Z.eq_dec k hi) as [->|NK]; [right; split; reflexivity | left; exact (e_slot_hg k NK)].
  Qed.
  Lemma old_not_ff : forall x, is_group st x ->
    (forall k, 0 <= k <= g_lastidx st' x -> s_slot st' x k = SAvail \/ s_slot st' x k = SFreed) ->
    forall k, 0 <= k <= g_lastidx st x -> s_slot st x k = SAvail \/ s_slot st x k = SFreed.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG.
    intros x Hx ALL k Hk. rewrite (e_glast x Hx) in ALL. pose proof (ALL k Hk) as A.
    destruct (old_slot x k Hx) as [E|[-> ->]]; [rewrite <- E; exact A|]. rewrite e_slot_hi in A. destruct A as [A|A]; discriminate A.
  Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF RN. clear - Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - apply base.NoDup_cons_2; [|exact ND]. intros E. apply HNG. apply (proj1 (base.list_elem_of_In _ _) E).
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx]; [exact t_wf_group_new|].
      destruct (Z.eq_dec x hg) as [->|NE]; [exact t_wf_group_hg | exact (t_wf_group_old x Hx NE)].
    - intros m1 m2 H1 H2. apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; destruct H2 as [->|H2].
      + intros; reflexivity.
      + rewrite e_ai_m, n_glast, n_gsc, (e_ai_old m2 (grp_ne m2 H2)). rewrite e_glast, e_gsc by exact H2. intros _ P2 E. exfalso.
        pose proof (wg_partial st L m2 (wG_each st L (WF_groups st L HWF) m2 H2) P2) as Hin. rewrite <- E, Hnil in Hin. destruct Hin.
      + rewrite e_ai_m, n_glast, n_gsc, (e_ai_old m1 (grp_ne m1 H1)). rewrite e_glast, e_gsc by exact H1. intros P1 _ E. exfalso.
        pose proof (wg_partial st L m1 (wG_each st L (WF_groups st L HWF) m1 H1) P1) as Hin. rewrite E, Hnil in Hin. destruct Hin.
      + rewrite (e_ai_old m1 (grp_ne m1 H1)), (e_ai_old m2 (grp_ne m2 H2)). rewrite !e_glast, !e_gsc by assumption. exact (ONE m1 m2 H1 H2).
    - intros b l x Hin. pose proof (REG b l x Hin) as (G & K & E1 & E2).
      rewrite e_is_group, (e_kind_old x (grp_ne x G)), e_gmem, e_gml by exact G. repeat split; auto.
    - intros x F. rewrite e_fresh in F. rewrite e_meta_old; [exact (FR0 x F)|]. intros ->. exact (HNF F).
    - intros x U NG NFL NFR. rewrite e_is_group in NG. apply e_metaU in U. rewrite e_in_flist in NFL. rewrite e_fresh in NFR.
      apply zremove_In. split; [apply (OTH x U); tauto|]. intros ->. apply NG. left. reflexivity.
    - intros x Hl. apply zremove_In in Hl. destruct Hl as [Hl Hxm]. destruct (LIM x Hl) as (A & B & C & D).
      rewrite e_metaU, e_is_group, e_fresh, e_listed. split; [exact A|]. split; [intros [E|E]; [exact (Hxm E) | exact (B E)]|].
      split; [intros [E|E]; [exact (C E) | exact (Hxm E)] | exact D].
    - intros m1 m2 H1 H2 G1 G2 E. apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; [exfalso; destruct (G1 0 ltac:(rewrite n_glast; lia)) as [F|F]; rewrite e_slot_m in F; discriminate F|].
      destruct H2 as [->|H2]; [exfalso; destruct (G2 0 ltac:(rewrite n_glast; lia)) as [F|F]; rewrite e_slot_m in F; discriminate F|].
      rewrite !e_gsc in E by assumption.
      exact (ONEFF m1 m2 H1 H2 (old_not_ff m1 H1 G1) (old_not_ff m2 H2 G2) E).
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN. clear - Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L RN.
    pose proof p_rng as (P0 & P1 & P2 & P3 & P16). pose proof h_rng as (R1 & R2 & R3 & R4). pose proof size_facts as (S16 & _).
    assert (SC0 : 0 <= size * cnt) by (apply Z.mul_nonneg_nonneg; lia).
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN]. constructor; rewrite ?e_regions.
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + destruct (INR hg Hhg) as (r & Hr & Q1 & Q2). exists r. split; [exact Hr|]. rewrite n_gmem, n_gspan.
        pose proof (slot_in_span st L HWF hg hi Hhg Hhi) as [SI1 SI2]. rewrite Ese in SI2. lia.
      + rewrite e_gmem, e_gspan by exact Hx. exact (INR x Hx).
    - intros m1 m2 y H1 H2 Hne G1 G2.
      destruct (any_cell m1 y H1 G1) as [(O1 & C1 & S1)|[(-> & C1 & C1')|(-> & C1)]];
      destruct (any_cell m2 y H2 G2) as [(O2 & C2 & S2)|[(-> & C2 & C2')|(-> & C2)]]; try lia.
      + exact (CELLS m1 m2 y O1 O2 Hne C1 C2).
      + destruct (Z.eq_dec m1 hg) as [->|NE]; [pose proof (z_own_cell y C1 ltac:(lia)); lia | exact (z_other_cell m1 y O1 NE C1 ltac:(lia))].
      + destruct (Z.eq_dec m1 hg) as [->|NE]; [exact (Hne eq_refl)|].
        destruct (Z_lt_le_dec y (start - 3)) as [LO|HI]; [|exact (z_other_cell m1 y O1 NE C1 ltac:(lia))].
        exact (CELLS m1 hg y O1 Hhg NE C1 (z_hdr_cell y ltac:(lia))).
      + destruct (Z.eq_dec m2 hg) as [->|NE]; [pose proof (z_own_cell y C2 ltac:(lia)); lia | exact (z_other_cell m2 y O2 NE C2 ltac:(lia))].
      + destruct (Z.eq_dec m2 hg) as [->|NE]; [exact (Hne eq_refl)|].
        destruct (Z_lt_le_dec y (start - 3)) as [LO|HI]; [|exact (z_other_cell m2 y O2 NE C2 ltac:(lia))].
        exact (CELLS m2 hg y O2 Hhg NE C2 (z_hdr_cell y ltac:(lia))).
    - intros x y Hx R Ar. apply e_areab in Ar. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + rewrite n_gmem, n_gspan in R. apply (AREA hg y Hhg); [|exact Ar]. pose proof Ess. lia.
      + rewrite e_gmem, e_gspan in R by exact Hx. exact (AREA x y Hx R Ar).
    - intros x y Hx G Ap. apply e_appb in Ap.
      destruct (any_cell x y Hx G) as [(O1 & C1 & S1)|[(-> & C1 & C1')|(-> & C1)]].
      + exact (APC x y O1 C1 Ap).
      + exact (z_app y Ap ltac:(lia)).
      + destruct (Z_lt_le_dec y (start - 3)) as [LO|HI]; [|exact (z_app y Ap ltac:(lia))].
        exact (APC hg y Hhg (z_hdr_cell y ltac:(lia)) Ap).
    - intros y Ap Ar. apply e_appb in Ap. apply e_areab in Ar. eauto.
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2.
      destruct H1 as [->|H1]; [rewrite e_slot_m in S1; exfalso; exact (nslot_nouser aidx _ _ _ _ _ S1)|].
      destruct H2 as [->|H2]; [rewrite e_slot_m in S2; exfalso; exact (nslot_nouser aidx _ _ _ _ _ S2)|].
      rewrite e_glast in Hk1 by exact H1. rewrite e_glast in Hk2 by exact H2.
      apply (v_user st st' hg yG) in S1; [|exact H1]. apply (v_user st st' hg yG) in S2; [|exact H2]. eauto.
    - intros x k y x2 Hx G H2 C.
      destruct (any_garb x k y Hx G) as [(O1 & G1 & N1)|[(-> & G1)|(-> & -> & G1)]];
      destruct (any_cell x2 y H2 C) as [(O2 & C2 & S2)|[(-> & C2 & C2')|(-> & C2)]]; try lia.
      + exact (GC x k y x2 O1 G1 O2 C2).
      + exact (z_garbage x k y O1 G1 N1 ltac:(lia)).
      + destruct (Z_lt_le_dec y (start - 3)) as [LO|HI]; [|exact (z_garbage x k y O1 G1 N1 ltac:(lia))].
        exact (GC x k y hg O1 G1 Hhg (z_hdr_cell y ltac:(lia))).
      + destruct (Z.eq_dec x2 hg) as [->|NE]; [pose proof (z_own_cell y C2 ltac:(lia)); lia | exact (z_other_cell x2 y O2 NE C2 ltac:(lia))].
      + exact (n_garb_cell k y G C).
      + destruct (Z.eq_dec x2 hg) as [->|NE]; [destruct (S2 eq_refl); lia | exact (z_other_cell x2 y O2 NE C2 ltac:(lia))].
    - intros x k y Hx G Ap. apply e_appb in Ap.
      destruct (any_garb x k y Hx G) as [(O1 & G1 & N1)|[(-> & G1)|(-> & -> & G1)]].
      + exact (GA x k y O1 G1 Ap).
      + exact (z_app y Ap ltac:(lia)).
      + exact (z_app y Ap ltac:(lia)).
    - intros x k y Hx G Ar. apply e_areab in Ar.
      destruct (any_garb x k y Hx G) as [(O1 & G1 & N1)|[(-> & G1)|(-> & -> & G1)]].
      + exact (GAR x k y O1 G1 Ar).
      + exact (z_area y Ar ltac:(lia)).
      + exact (z_area y Ar ltac:(lia)).
    - intros x Hx. apply e_is_group in Hx. destruct Hx as [->|Hx].
      + rewrite e_kind_m, (e_gss hg hi Hhg), (e_gse hg hi Hhg), n_gmem, n_gspan, Ese. split; [reflexivity | lia].
      + rewrite (e_kind_old x (grp_ne x Hx)), e_gspan, e_gmem, e_gml by exact Hx.
        pose proof (SPAN x Hx) as SP. destruct (s_kind st x) as [|hm j o] eqn:K; [exact SP|].
        pose proof (v_host_group st L HWF x hm j o Hx K) as Hh. rewrite e_gss, e_gse by exact Hh. exact SP.
  Qed.

  Lemma t_wf_live : wf_live st' L.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF RN. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF RN. exact (wf_live_subB st st' L hg yG n_nouser (WF_live st L HWF)). Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L. clear - Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HWF L.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL]. constructor; rewrite ?e_regions, ?e_brk, ?e_areas; try assumption.
    - intros b l x Hin. pose proof (proj1 (wG_regions st L (WF_groups st L HWF) b l x Hin)) as G. rewrite e_gsc by exact G. exact (GB b l x Hin).
    - intros b l x Hin. pose proof (wG_regions st L (WF_groups st L HWF) b l x Hin) as (G & K & _). rewrite e_gsc by exact G.
      intros H63. assert (NE : x <> hg) by (intros ->; lia).
      rewrite !(e_slot_other x 0 G NE). exact (G63 b l x Hin H63).
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using HWF L RN. clear - HWF L RN. apply (wf_img_same st L HWF); reflexivity. Qed.

  Lemma t_WF : WF st' L.
  Proof using Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF. clear - Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HWF.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (spl sph : Z).
  Hypothesis Hspl : CEIL <= spl.
  Definition b_wr (y : Z) : Prop :=
    (m <= y < m + 40) \/ (start - 3 <= y < start + strideH - 4) \/
    (ctx_usage sc <= y < ctx_usage sc + 8) \/ (ctx_active sc <= y < ctx_active sc + 8) \/ (spl <= y < sph).
  Hypothesis HMwr : forall y, 0 <= y < 2 ^ 64 -> M' (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> b_wr y.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMmeta : rep_meta M' m (MR m m p av fr W).
  Hypothesis HMh4 : byte_at M' (p - 4) 0.
  Hypothesis HMh3 : byte_at M' (p - 3) (hi + 32 * 6).
  Hypothesis HMh2 : cell M' (p - 2) 2 (inband st hg p).
  Hypothesis HMp : cell M' p 8 m.
  Hypothesis HMai : exists b, 0 <= b < 256 /\ byte_at M' (p + 8) b /\ b mod 32 = aidx.
  Hypothesis HMz : forall k, 0 <= k <= cnt -> (k < cnt \/ p + 12 + size * cnt < start + strideH - 4) -> byte_at M' (p + 12 + size * k) 0.
  Hypothesis HMusage : cell M' (ctx_usage sc) 8 usage'.
  Hypothesis HMact : cell M' (ctx_active sc) 8 m.

  Lemma HMkeep : forall y, dfoot st y -> M (Z_to_bv 64 y) <> None -> M' (Z_to_bv 64 y) <> None.
  Proof using HMgrow. clear - HMgrow. exact (dkeep_of_grows st M M' HMgrow). Qed.

  Lemma HMlow : agree_on (fun y => IMG_LO <= y < CTX) M M'.
  Proof using HMwr Hspl sph spl Hsc Hhi Hhg HU HWF cnt sc hi hg m L st RN. clear - HMwr Hspl sph spl Hsc Hhi Hhg HU HWF cnt sc hi hg m L st RN.
    intros y Hr Hy. destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
    pose proof m_rng. pose proof h_rng. pose proof h_ess. cbv beta in Hy.
    destruct (HMwr y Hr NE) as [X|[X|[X|[X|X]]]]; ceil; unfold ctx_usage, ctx_active, CTX, HEAPLO in *; lia.
  Qed.

  Lemma t_rep_statics : rep_statics st' M'.
  Proof using HMgrow HMwr Hspl sph spl Hsc Hhi Hhg HU HREP HWF M L RN. clear - HMgrow HMwr Hspl sph spl Hsc Hhi Hhg HU HREP HWF M L RN. apply (rep_statics_tr st st' M M' HREP HMkeep HMlow); reflexivity. Qed.

  Lemma t_rep_ctx : rep_ctx st' M'.
  Proof using HMact HMusage HMwr Hspl sph spl Hscj Hsc Hhi Hhg HU HREP HWF M L RN. clear - HMact HMusage HMwr Hspl sph spl Hscj Hsc Hhi Hhg HU HREP HWF M L RN.
    pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
    pose proof m_rng as MR. pose proof h_rng as AR. pose proof h_ess as AE.
    assert (TR : forall y k v, CTX <= y -> y + Z.of_nat k <= CTX_END ->
              (y + Z.of_nat k <= ctx_usage sc \/ ctx_usage sc + 8 <= y) ->
              (y + Z.of_nat k <= ctx_active sc \/ ctx_active sc + 8 <= y) ->
              cell M y k v -> cell M' y k v).
    { intros y k v H1 H2 H4 H5 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
      intros z Hz Rz. cbv beta in Rz. destruct (decide (M' (Z_to_bv 64 z) = M (Z_to_bv 64 z))) as [E|NE]; [exact E|]. exfalso.
      destruct (HMwr z Hz NE) as [X|[X|[X|[X|X]]]]; ceil; unfold ctx_usage, ctx_active, CTX_END, CTX, HEAPLO in *; lia. }
    Ltac ctxg2 TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | eauto ].
    constructor; cbn [s_ctx st' cx_set_grp c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift c_area_head c_area_tail
                      c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try assumption; try (ctxg2 TR).
    - intros s0 Hs0. unfold fupd. destruct (Z.eqb_spec s0 sc) as [->|NE]; [exact HMact | ctxg2 TR].
    - intros s0 Hs0. unfold fupd. destruct (Z.eqb_spec s0 sc) as [->|NE]; [exact HMusage | ctxg2 TR].
    - intros i Hi. ctxg2 TR.
    - intros i Hi. ctxg2 TR.
  Qed.

  Lemma t_rep_areas : forall ar, In ar (s_areas st') -> rep_area st' M' ar.
  Proof using HMmeta HMgrow HMwr Hspl sph spl Hscj Hsc Hhi Hhg HU HREP HWF M L RN. clear - HMmeta HMgrow HMwr Hspl sph spl Hscj Hsc Hhi Hhg HU HREP HWF M L RN.
    apply (rep_areas_tr st st' L M M' HWF HREP HMkeep (fun x => x =? m)); try reflexivity.
    - intros ar y Har Hy NE. pose proof (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
      pose proof m_rng. pose proof h_rng. pose proof h_ess.
      destruct (HMwr y ltac:(ceil; unfold HEAPLO in *; lia) NE) as [X|[X|[X|[X|X]]]].
      + exists m. split; [exact HU|]. split; [apply Z.eqb_refl | exact X].
      + exfalso. apply (z_area y); [exists ar; split; [exact Har | exact Hy] | exact X].
      + exfalso. unfold ctx_usage, CTX, HEAPLO in *. lia.
      + exfalso. unfold ctx_active, CTX, HEAPLO in *. lia.
      + exfalso. ceil. lia.
    - intros x Ux X. apply Z.eqb_eq in X. subst x. rewrite e_meta_m. exact HMmeta.
    - intros x Ux X. apply Z.eqb_neq in X. exact (e_meta_old x X).
  Qed.

  Lemma t_rep_group_new : rep_group st' M' m.
  Proof using HMz HMai HMp Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HWF L RN. clear - HMz HMai HMp Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HWF L RN.
    pose proof p_rng as (P0 & P1 & P2 & P3 & P16). pose proof m_rng as MR. pose proof size_facts as (S16 & _).
    constructor; rewrite ?n_gmem, ?e_ai_m, ?n_gcnt, ?n_glast, ?e_kind_m, ?n_gml.
    - exact HMp.
    - exact HMai.
    - intros i Hi Hend. rewrite n_gss. replace (p + 16 + size * i - 4) with (p + 12 + size * i) by lia. apply HMz; [exact Hi|].
      destruct Hend as [H|H]; [left; exact H | right; apply n_endb; exact H].
    - exact I.
    - intros i Hi. rewrite e_slot_m. destruct (nslot_cases aidx i) as [[-> E]|[( _ & _ & E)|(_ & _ & E)]]; rewrite E; exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma old_cell_same : forall x y, is_group st x -> x <> hg -> gcell st x y -> M' (Z_to_bv 64 y) = M (Z_to_bv 64 y).
  Proof using HMwr Hspl sph spl Hscj Hsc Hslot Hhi Hhg HU HWF cnt sc hi m L RN. clear - HMwr Hspl sph spl Hscj Hsc Hslot Hhi Hhg HU HWF cnt sc hi m L RN.
    intros x y Hx Hxh G. destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
    pose proof (gcell_in_span st L HWF x y Hx G) as R. destruct (group_range st L HWF x Hx) as [X1 X2].
    destruct (HMwr y ltac:(ceil; unfold HEAPLO in *; lia) NE) as [Xw|[Xw|[Xw|[Xw|Xw]]]].
    - exact (gcell_not_meta st L HWF x m y Hx G HU Xw).
    - exact (z_other_cell x y Hx Hxh G Xw).
    - unfold ctx_usage, CTX, HEAPLO in *. lia.
    - unfold ctx_active, CTX, HEAPLO in *. lia.
    - ceil. lia.
  Qed.

  Lemma t_rep_group_old : forall x, is_group st x -> x <> hg -> rep_group st' M' x.
  Proof using HMgrow HMwr Hspl sph spl Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN. clear - HMgrow HMwr Hspl sph spl Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN.
    intros x Hx Hxh. pose proof (grp_ne x Hx) as Hxm. destruct (group_range st L HWF x Hx) as [X1 X2].
    pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
    pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
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
    - intros q. exact (e_inband x q Hx).
    - intros E. apply (e_endb x Hx). exact E.
    - rewrite (e_kind_old x Hxm). destruct (s_kind st x); [split; [reflexivity | exact (e_gml x Hx)] | exact I].
    - intros k Hk. left. exact (e_slot_other x k Hx Hxh).
    - intros y G. apply (v_gcell st st' L hg yG HWF x y Hx Hxh) in G. exact (old_cell_same x y Hx Hxh G).
    - exact HMgrow.
    - exact SPAN.
    - intros y G. apply (v_gcell st st' L hg yG HWF x y Hx Hxh) in G. exact (gcell_in_span st L HWF x y Hx G).
    - exact (rp_groups st M HREP x Hx).
  Qed.

  (* [comment removed for export] *)
  #[local] Notation stF := (MhScrib.stF st hg hi).
  Lemma f_agree : forall y, gcell stF hg y -> M' (Z_to_bv 64 y) = M (Z_to_bv 64 y).
  Proof using HMwr Hspl sph spl Hscj Hsc Hslot Hhi Hhg HU HWF cnt sc m L RN. clear - HMwr Hspl sph spl Hscj Hsc Hslot Hhi Hhg HU HWF cnt sc m L RN.
    intros y G. destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
    pose proof (MhScrib.f_gcell_back st hg hi y G) as G0.
    pose proof (gcell_in_span st L HWF hg y Hhg G0) as R. destruct (group_range st L HWF hg Hhg) as [X1 X2].
    destruct (HMwr y ltac:(ceil; unfold HEAPLO in *; lia) NE) as [Xw|[Xw|[Xw|[Xw|Xw]]]].
    - exact (gcell_not_meta st L HWF hg m y Hhg G0 HU Xw).
    - exact (MhEnfr.f_out st L hg hi HWF Hhg Hhi Hslot y G Xw).
    - unfold ctx_usage, CTX, HEAPLO in *. lia.
    - unfold ctx_active, CTX, HEAPLO in *. lia.
    - ceil. lia.
  Qed.
  Lemma t_rep_group_hg : rep_group st' M' hg.
  Proof using HMh2 HMh3 HMh4 HMgrow HMwr Hspl sph spl Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN. clear - HMh2 HMh3 HMh4 HMgrow HMwr Hspl sph spl Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN.
    destruct (group_range st L HWF hg Hhg) as [X1 X2]. pose proof h_str as [S16 _].
    pose proof (wg_mem st L hg h_wfg) as (Y1 & Y2 & Y3).
    assert (SPAN : 0 <= g_mem st hg /\ g_mem st hg + 16 <= g_span_end st hg /\ g_span_end st hg < 2 ^ 64).
    { assert (16 <= g_stride st hg * g_cnt st hg) by (unfold g_cnt; pose proof (glast_rng st hg); nia).
      ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia. }
    assert (RGF : rep_group stF M' hg).
    { apply (rep_group_transport st stF M M' hg); try reflexivity.
      - intros E; exact E.
      - change (s_kind stF hg) with (s_kind st hg). change (g_maplen stF hg) with (g_maplen st hg).
        destruct (s_kind st hg); [split; reflexivity | exact I].
      - intros k Hk. unfold MhScrib.stF. rewrite s_slot_set_slot, Z.eqb_refl.
        destruct (Z.eqb k hi); [right; right; reflexivity | left; reflexivity].
      - exact f_agree.
      - exact HMgrow.
      - exact SPAN.
      - intros y G. apply (gcell_in_span st L HWF hg y Hhg). exact (MhScrib.f_gcell_back st hg hi y G).
      - exact (rp_groups st M HREP hg Hhg). }
    destruct RGF as [F1 F2 F3 F4 F5]. constructor.
    - rewrite (e_gmem hg Hhg). exact F1.
    - rewrite (e_gmem hg Hhg), (e_ai_old hg hg_ne). exact F2.
    - intros k Hk Hend. rewrite (e_gcnt hg Hhg) in Hk, Hend. rewrite (e_gss hg k Hhg). apply F3; [exact Hk|].
      destruct Hend as [H|H]; [left; exact H | right]. apply (proj1 (e_endb hg Hhg)) in H. exact H.
    - rewrite (e_kind_old hg hg_ne), (e_gmem hg Hhg), (e_gml hg Hhg). pose proof F4 as D.
      change (s_kind stF hg) with (s_kind st hg) in D. destruct (s_kind st hg); [exact D | exact I].
    - intros k Hk. rewrite (e_glast hg Hhg) in Hk. destruct (Z.eq_dec k hi) as [->|NE].
      + rewrite e_slot_hi. cbn [rep_slot]. exists 6. split; [lia|]. rewrite (e_gss hg hi Hhg). constructor.
        * exact HMh4.
        * exact HMh3.
        * rewrite (e_inband hg _ Hhg). exact HMh2.
      + rewrite (e_slot_hg k NE). pose proof (F5 k Hk) as RS. unfold MhScrib.stF in RS. rewrite s_slot_set_slot, Z.eqb_refl in RS.
        rewrite (proj2 (Z.eqb_neq k hi) NE) in RS. cbn [andb] in RS.
        destruct (s_slot st hg k) as [| |q3 n3 o3 r3|c o3|o3]; cbn [rep_slot] in RS |- *; try exact I.
        * rewrite (e_gse hg k Hhg). destruct RS as ([A B C] & Rz & R5).
          split; [constructor; [exact A | exact B | rewrite (e_inband hg q3 Hhg); exact C]|]. split; [exact Rz | exact R5].
        * rewrite (e_gss hg k Hhg). destruct RS as (rc & Hrc & [A B C]). exists rc. split; [exact Hrc|].
          constructor; [exact A | exact B | rewrite (e_inband hg _ Hhg); exact C].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMact HMusage HMz HMai HMp HMh2 HMh3 HMh4 HMmeta HMgrow HMwr Hspl sph spl Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN. clear - HMact HMusage HMz HMai HMp HMh2 HMh3 HMh4 HMmeta HMgrow HMwr Hspl sph spl Hptr H2048 Hroom Hoff Husage Haidx Hcnt Hscj Hsc Hslot Hhi Hhg HNG HU HREP HWF M L RN.
    constructor.
    - exact t_rep_statics.
    - exact t_rep_ctx.
    - exact t_rep_areas.
    - intros x Hx. apply e_is_group in Hx. destruct (Z.eq_dec x m) as [->|Hxm]; [exact t_rep_group_new|].
      destruct Hx as [E|Hx]; [exfalso; exact (Hxm E)|].
      destruct (Z.eq_dec x hg) as [->|Hxh]; [exact t_rep_group_hg | exact (t_rep_group_old x Hx Hxh)].
  Qed.

  Lemma t_ledger : forall vm, LEDGER st vm -> LEDGER st' vm.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros vm [LM LN LB LR LMB]. constructor; rewrite ?e_regions, ?e_brk; try assumption. Qed.

  Theorem newnest_close : WF st' L /\ REP st' M'.
  Proof using HMact HMusage HMz HMai HMp HMh2 HMh3 HMh4 HMmeta HMgrow HMwr Hspl sph spl Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HREP HWF M. clear - HMact HMusage HMz HMai HMp HMh2 HMh3 HMh4 HMmeta HMgrow HMwr Hspl sph spl Hptr Hpnd H2048 Hroom Hoff Husage Haidx Hcnt Hnil Hscj Hsc Hslot Hhi Hhg HNF Hunl HNG HU HREP HWF M. split; [exact t_WF | exact t_REP]. Qed.

  (* [comment removed for export] *)
  Lemma newnest_facts :
    is_group st' m /\ s_slot st' m 0 = SJunk 0 /\ g_lastidx st' m = cnt - 1 /\ g_stride st' m = size /\
    g_slot_start st' m 0 = p + 16 /\ g_sc st' m = sc /\ s_kind st' m = GNest hg hi off /\ g_mem st' m = p /\ g_maplen st' m = 0 /\
    s_alist st' sc = [m] /\ c_active (s_ctx st') sc = m /\
    s_limbo st' = zremove m (s_limbo st) /\ s_regions st' = s_regions st /\ s_brk st' = s_brk st /\
    (forall x k, is_group st' x -> x <> m -> (x <> hg \/ k <> hi) -> s_slot st' x k = s_slot st x k) /\
    (forall x, is_group st' x <-> x = m \/ is_group st x).
  Proof using Hcnt Hsc. clear - Hcnt Hsc.
    split; [exact n_is_group|]. split; [apply e_slot_m|]. split; [exact n_glast|]. split; [exact n_gstride|].
    split; [rewrite n_gss; lia|]. split; [exact n_gsc|]. split; [exact e_kind_m|]. split; [exact n_gmem|]. split; [exact n_gml|].
    split; [exact e_alist_sc|]. split; [cbn; unfold fupd; rewrite Z.eqb_refl; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros x k _ Hxm H; exact (e_slot_old x k Hxm H) | exact e_is_group].
  Qed.
End NewNest.
