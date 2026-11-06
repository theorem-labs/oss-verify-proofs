(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module MhExtG.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Record same_groups (st1 st2 : mst) : Prop := SG {
  sg_groups : s_groups st2 = s_groups st1;
  sg_kind : forall x, s_kind st2 x = s_kind st1 x;
  sg_slot : forall x k, slot_sim (s_slot st1 x k) (s_slot st2 x k);
  sg_mem : forall x, is_group st1 x -> mr_mem (s_meta st2 x) = mr_mem (s_meta st1 x);
  sg_W : forall x, is_group st1 x -> mr_W (s_meta st2 x) = mr_W (s_meta st1 x)
}.


Section ExtG.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (L : list (Z * Z)).
  Hypothesis S : same_groups st1 st2.
  Hypothesis HWF1 : WF st1 L.

  Lemma y_host_group : forall y hm j o, is_group st1 y -> s_kind st1 y = GNest hm j o -> is_group st1 hm.
  Proof using HWF1 L RN.
    intros y hm j o Hy K. pose proof (wg_kind st1 L y (wG_each st1 L (WF_groups st1 L HWF1) y Hy)) as KD.
    rewrite K in KD. exact (proj1 (proj2 KD)).
  Qed.
  Lemma y_child_group : forall x k c o, is_group st1 x -> 0 <= k <= g_lastidx st1 x -> s_slot st1 x k = SHost c o -> is_group st1 c.
  Proof using HWF1 L RN.
    intros x k c o Hx Hk E. pose proof (wg_slots st1 L x (wG_each st1 L (WF_groups st1 L HWF1) x Hx) k Hk) as SW.
    rewrite E in SW. exact (proj1 (proj2 SW)).
  Qed.

  Lemma y_gW : forall x, is_group st1 x -> g_W st2 x = g_W st1 x. Proof using S. intros; unfold g_W; apply (sg_W _ _ S); assumption. Qed.
  Lemma y_gmem : forall x, is_group st1 x -> g_mem st2 x = g_mem st1 x. Proof using S. intros; unfold g_mem; apply (sg_mem _ _ S); assumption. Qed.
  Lemma y_glast : forall x, is_group st1 x -> g_lastidx st2 x = g_lastidx st1 x. Proof using S. intros; unfold g_lastidx; rewrite y_gW by assumption; reflexivity. Qed.
  Lemma y_gcnt : forall x, is_group st1 x -> g_cnt st2 x = g_cnt st1 x. Proof using S. intros; unfold g_cnt; rewrite y_glast by assumption; reflexivity. Qed.
  Lemma y_gsc : forall x, is_group st1 x -> g_sc st2 x = g_sc st1 x. Proof using S. intros; unfold g_sc; rewrite y_gW by assumption; reflexivity. Qed.
  Lemma y_gml : forall x, is_group st1 x -> g_maplen st2 x = g_maplen st1 x. Proof using S. intros; unfold g_maplen; rewrite y_gW by assumption; reflexivity. Qed.
  Lemma y_gstride : forall x, is_group st1 x -> g_stride st2 x = g_stride st1 x.
  Proof using S. intros; unfold g_stride; rewrite y_gml, y_glast, y_gsc by assumption; reflexivity. Qed.
  Lemma y_gss : forall x k, is_group st1 x -> g_slot_start st2 x k = g_slot_start st1 x k.
  Proof using S. intros; unfold g_slot_start; rewrite y_gmem, y_gstride by assumption; reflexivity. Qed.
  Lemma y_gse : forall x k, is_group st1 x -> g_slot_end st2 x k = g_slot_end st1 x k.
  Proof using S. intros; unfold g_slot_end; rewrite y_gss, y_gstride by assumption; reflexivity. Qed.
  Lemma y_gspan : forall x, is_group st1 x -> gspan st2 x = gspan st1 x.
  Proof using S. intros; unfold gspan, g_span_end; rewrite y_gmem, y_gstride, y_gcnt by assumption; reflexivity. Qed.
  Lemma y_inband : forall x q, is_group st1 x -> inband st2 x q = inband st1 x q.
  Proof using S. intros; unfold inband; rewrite y_gmem by assumption; reflexivity. Qed.
  Lemma y_ptr_ok : forall x k q, is_group st1 x -> (ptr_ok st2 x k q <-> ptr_ok st1 x k q).
  Proof using S. intros; unfold ptr_ok; rewrite y_gmem, y_inband, y_gsc, y_gml by assumption; tauto. Qed.
  Lemma y_endb : forall x, is_group st1 x -> (endb_own st2 x <-> endb_own st1 x).
  Proof using HWF1 S L RN.
    intros x Hx; unfold endb_own; rewrite (sg_kind _ _ S), y_gspan by assumption.
    destruct (s_kind st1 x) as [|hm j o] eqn:K; [tauto|]. rewrite y_gse by (eapply y_host_group; eassumption). tauto.
  Qed.
  Lemma y_is_group : forall x, is_group st2 x <-> is_group st1 x. Proof using S. intros; unfold is_group; rewrite (sg_groups _ _ S); tauto. Qed.
  Lemma y_slot_cases : forall x k, s_slot st2 x k = s_slot st1 x k \/
    ((s_slot st1 x k = SAvail \/ s_slot st1 x k = SFreed) /\ (s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed)).
  Proof using S. intros x k. destruct (sg_slot _ _ S x k) as [E|E]; [left; symmetry; exact E | right; exact E]. Qed.
  Lemma y_slot_ptr : forall x k, is_group st1 x -> slot_ptr st2 x k = slot_ptr st1 x k.
  Proof using S.
    intros x k Hx; unfold slot_ptr. rewrite y_gss by assumption.
    destruct (y_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; reflexivity.
  Qed.
  Lemma y_user : forall x k q n o r, s_slot st2 x k = SUser q n o r <-> s_slot st1 x k = SUser q n o r.
  Proof using S.
    intros x k q n o r. destruct (y_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; split; intro H; try exact H; discriminate.
  Qed.


  Lemma y_gcell : forall x a, is_group st1 x -> (gcell st2 x a <-> gcell st1 x a).
  Proof using HWF1 S L RN.
    intros x a Hx. unfold gcell. rewrite y_gmem, y_gcnt, y_glast by assumption.
    assert (E2 : forall k, (k < g_cnt st1 x \/ endb_own st2 x) <-> (k < g_cnt st1 x \/ endb_own st1 x)) by (intros; rewrite y_endb by assumption; tauto).
    split; intros [G|[G|[G|G]]].
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite y_gss in B by assumption. rewrite <- E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite y_slot_ptr in B by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite y_user in B. rewrite y_gse in C by assumption. tauto.
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite y_gss by assumption. rewrite E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite y_slot_ptr by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite y_user, y_gse by assumption. tauto.
  Qed.
  Lemma y_appb : forall a, appb st2 a <-> appb st1 a.
  Proof using S.
    intros a. unfold appb. split; intros (x & k & q & n & o & r & A & B & C & D).
    - apply y_is_group in A. exists x, k, q, n, o, r. rewrite y_glast in B by exact A. rewrite y_user in C. tauto.
    - exists x, k, q, n, o, r. rewrite y_glast, y_user by exact A. split; [apply y_is_group; exact A | tauto].
  Qed.
  Lemma y_garbage : forall x k a, is_group st1 x -> (garbage st2 x k a <-> garbage st1 x k a).
  Proof using HWF1 S L RN.
    intros x k a Hx. unfold garbage. rewrite y_glast, y_gss, y_gse by assumption.
    destruct (y_slot_cases x k) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; [|tauto..].
    destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; try tauto.
    destruct (Z.le_gt_cases 0 k) as [Hk0|Hk0]; [|split; intros [Hk _]; lia].
    destruct (Z.le_gt_cases k (g_lastidx st1 x)) as [Hk1|Hk1]; [|split; intros [Hk _]; lia].
    rewrite y_gspan by (eapply (y_child_group x k); [exact Hx | lia | exact Sk]). tauto.
  Qed.


  Lemma y_slot_wf_same : forall x k sl, is_group st1 x -> slot_wf st1 L x k sl -> slot_wf st2 L x k sl.
  Proof using S.
    intros x k sl Hx SW. destruct sl as [| |q n o r|c o|o]; cbn [slot_wf] in *; try exact I.
    - rewrite y_gss, y_gstride by assumption. destruct SW as (A & B & C & D & E & F & G). repeat (split; [assumption|]).
      split; [apply y_ptr_ok; [exact Hx | exact F] | exact G].
    - rewrite y_gss, (sg_kind _ _ S) by assumption. destruct SW as (A & B & C & D & E). repeat (split; [first [assumption | apply y_is_group; assumption]|]).
      apply y_ptr_ok; [exact Hx | exact E].
    - rewrite y_gss, y_gstride by assumption. destruct SW as (A & B & C). split; [exact A|]. split; [exact B|]. apply y_ptr_ok; [exact Hx | exact C].
  Qed.




  Lemma wf_live_ext : wf_live st1 L -> wf_live st2 L.
  Proof using S.
    intros [IN ND FUN LEN]. constructor.
    - intros p n Hin. destruct (IN p n Hin) as (x & k & o & r & A & B & C). exists x, k, o, r.
      rewrite y_glast, y_user by exact A. split; [apply y_is_group; exact A | tauto].
    - exact ND.
    - intros m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      apply y_is_group in H1. apply y_is_group in H2. rewrite y_glast in Hk1 by exact H1. rewrite y_glast in Hk2 by exact H2.
      rewrite y_user in S1, S2. eauto.
    - exact LEN.
  Qed.

End ExtG.
End MhExtG.
Module MhExtS.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record sub_groups (st1 st2 : mst) : Prop := SUBG {
  sg_in : forall x, is_group st1 x -> is_group st2 x;
  sg_kind : forall x, is_group st1 x -> s_kind st2 x = s_kind st1 x;
  sg_slot : forall x k, is_group st1 x -> slot_sim (s_slot st1 x k) (s_slot st2 x k);
  sg_mem : forall x, is_group st1 x -> mr_mem (s_meta st2 x) = mr_mem (s_meta st1 x);
  sg_W : forall x, is_group st1 x -> mr_W (s_meta st2 x) = mr_W (s_meta st1 x)
}.

Section ExtS.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (L : list (Z * Z)).
  Hypothesis S : sub_groups st1 st2.
  Hypothesis HWF1 : WF st1 L.

  Lemma u_host_group : forall y hm j o, is_group st1 y -> s_kind st1 y = GNest hm j o -> is_group st1 hm.
  Proof using HWF1 L RN.
    intros y hm j o Hy K. pose proof (wg_kind st1 L y (wG_each st1 L (WF_groups st1 L HWF1) y Hy)) as KD.
    rewrite K in KD. exact (proj1 (proj2 KD)).
  Qed.
  Lemma u_child_group : forall x k c o, is_group st1 x -> 0 <= k <= g_lastidx st1 x -> s_slot st1 x k = SHost c o -> is_group st1 c.
  Proof using HWF1 L RN.
    intros x k c o Hx Hk E. pose proof (wg_slots st1 L x (wG_each st1 L (WF_groups st1 L HWF1) x Hx) k Hk) as SW.
    rewrite E in SW. exact (proj1 (proj2 SW)).
  Qed.

  Lemma u_gW : forall x, is_group st1 x -> g_W st2 x = g_W st1 x. Proof using S. intros; unfold g_W; apply (sg_W _ _ S); assumption. Qed.
  Lemma u_gmem : forall x, is_group st1 x -> g_mem st2 x = g_mem st1 x. Proof using S. intros; unfold g_mem; apply (sg_mem _ _ S); assumption. Qed.
  Lemma u_glast : forall x, is_group st1 x -> g_lastidx st2 x = g_lastidx st1 x. Proof using S. intros; unfold g_lastidx; rewrite u_gW by assumption; reflexivity. Qed.
  Lemma u_gcnt : forall x, is_group st1 x -> g_cnt st2 x = g_cnt st1 x. Proof using S. intros; unfold g_cnt; rewrite u_glast by assumption; reflexivity. Qed.
  Lemma u_gsc : forall x, is_group st1 x -> g_sc st2 x = g_sc st1 x. Proof using S. intros; unfold g_sc; rewrite u_gW by assumption; reflexivity. Qed.
  Lemma u_gml : forall x, is_group st1 x -> g_maplen st2 x = g_maplen st1 x. Proof using S. intros; unfold g_maplen; rewrite u_gW by assumption; reflexivity. Qed.
  Lemma u_gstride : forall x, is_group st1 x -> g_stride st2 x = g_stride st1 x.
  Proof using S. intros; unfold g_stride; rewrite u_gml, u_glast, u_gsc by assumption; reflexivity. Qed.
  Lemma u_gss : forall x k, is_group st1 x -> g_slot_start st2 x k = g_slot_start st1 x k.
  Proof using S. intros; unfold g_slot_start; rewrite u_gmem, u_gstride by assumption; reflexivity. Qed.
  Lemma u_gse : forall x k, is_group st1 x -> g_slot_end st2 x k = g_slot_end st1 x k.
  Proof using S. intros; unfold g_slot_end; rewrite u_gss, u_gstride by assumption; reflexivity. Qed.
  Lemma u_gspan : forall x, is_group st1 x -> gspan st2 x = gspan st1 x.
  Proof using S. intros; unfold gspan, g_span_end; rewrite u_gmem, u_gstride, u_gcnt by assumption; reflexivity. Qed.
  Lemma u_inband : forall x q, is_group st1 x -> inband st2 x q = inband st1 x q.
  Proof using S. intros; unfold inband; rewrite u_gmem by assumption; reflexivity. Qed.
  Lemma u_ptr_ok : forall x k q, is_group st1 x -> (ptr_ok st2 x k q <-> ptr_ok st1 x k q).
  Proof using S. intros; unfold ptr_ok; rewrite u_gmem, u_inband, u_gsc, u_gml by assumption; tauto. Qed.
  Lemma u_endb : forall x, is_group st1 x -> (endb_own st2 x <-> endb_own st1 x).
  Proof using HWF1 S L RN.
    intros x Hx; unfold endb_own; rewrite (sg_kind _ _ S), u_gspan by assumption.
    destruct (s_kind st1 x) as [|hm j o] eqn:K; [tauto|]. rewrite u_gse by (eapply u_host_group; eassumption). tauto.
  Qed.
  Lemma u_is_group : forall x, is_group st1 x -> is_group st2 x. Proof using S. exact (sg_in _ _ S). Qed.
  Lemma u_slot_cases : forall x k, is_group st1 x -> s_slot st2 x k = s_slot st1 x k \/
    ((s_slot st1 x k = SAvail \/ s_slot st1 x k = SFreed) /\ (s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed)).
  Proof using S. intros x k Hx. destruct (sg_slot _ _ S x k Hx) as [E|E]; [left; symmetry; exact E | right; exact E]. Qed.
  Lemma u_slot_ptr : forall x k, is_group st1 x -> slot_ptr st2 x k = slot_ptr st1 x k.
  Proof using S.
    intros x k Hx; unfold slot_ptr. rewrite u_gss by assumption.
    destruct (u_slot_cases x k Hx) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; reflexivity.
  Qed.
  Lemma u_user : forall x k q n o r, is_group st1 x -> s_slot st2 x k = SUser q n o r <-> s_slot st1 x k = SUser q n o r.
  Proof using S.
    intros x k q n o r Hx. destruct (u_slot_cases x k Hx) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; split; intro H; try exact H; discriminate.
  Qed.


  Lemma u_gcell : forall x a, is_group st1 x -> (gcell st2 x a <-> gcell st1 x a).
  Proof using HWF1 S L RN.
    intros x a Hx. unfold gcell. rewrite u_gmem, u_gcnt, u_glast by assumption.
    assert (E2 : forall k, (k < g_cnt st1 x \/ endb_own st2 x) <-> (k < g_cnt st1 x \/ endb_own st1 x)) by (intros; rewrite u_endb by assumption; tauto).
    split; intros [G|[G|[G|G]]].
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite u_gss in B by assumption. rewrite <- E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite u_slot_ptr in B by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite u_user in B by assumption. rewrite u_gse in C by assumption. tauto.
    - left; exact G.
    - right; left. destruct G as (k & A & B & C). exists k. rewrite u_gss by assumption. rewrite E2. tauto.
    - right; right; left. destruct G as (k & q & A & B & C). exists k, q. rewrite u_slot_ptr by assumption. tauto.
    - right; right; right. destruct G as (k & q & n & o & r & A & B & C). exists k, q, n, o, r.
      rewrite u_user, u_gse by assumption. tauto.
  Qed.
  Lemma u_appb : forall a, appb st1 a -> appb st2 a.
  Proof using S.
    intros a (x & k & q & n & o & r & A & B & C & D).
    exists x, k, q, n, o, r. rewrite u_glast, u_user by exact A. split; [apply u_is_group; exact A | tauto].
  Qed.
  (* [comment removed for export] *)
  Lemma u_appb_back : (forall x k q n o r, is_group st2 x -> ~ is_group st1 x -> s_slot st2 x k <> SUser q n o r) ->
    forall a, appb st2 a -> appb st1 a.
  Proof using S.
    intros NU a (x & k & q & n & o & r & A & B & C & D).
    destruct (in_dec Z.eq_dec x (s_groups st1)) as [Hx|Hx]; [|exfalso; exact (NU x k q n o r A Hx C)].
    exists x, k, q, n, o, r. rewrite u_glast, u_user in * by exact Hx. tauto.
  Qed.
  Lemma u_garbage : forall x k a, is_group st1 x -> (garbage st2 x k a <-> garbage st1 x k a).
  Proof using HWF1 S L RN.
    intros x k a Hx. unfold garbage. rewrite u_glast, u_gss, u_gse by assumption.
    destruct (u_slot_cases x k Hx) as [E|[[E1|E1] [E2|E2]]]; rewrite ?E, ?E1, ?E2; [|tauto..].
    destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; try tauto.
    destruct (Z.le_gt_cases 0 k) as [Hk0|Hk0]; [|split; intros [Hk _]; lia].
    destruct (Z.le_gt_cases k (g_lastidx st1 x)) as [Hk1|Hk1]; [|split; intros [Hk _]; lia].
    rewrite u_gspan by (eapply (u_child_group x k); [exact Hx | lia | exact Sk]). tauto.
  Qed.
  Lemma u_depth : forall f x, is_group st1 x -> (nest_depth_le st2 f x <-> nest_depth_le st1 f x).
  Proof using HWF1 S L RN.
    induction f as [|f IH]; intros x Hx; cbn; rewrite (sg_kind _ _ S) by exact Hx; destruct (s_kind st1 x) as [|hm j o] eqn:K; try tauto.
    apply IH. exact (u_host_group x hm j o Hx K).
  Qed.

  Lemma u_slot_wf_same : forall x k sl, is_group st1 x -> slot_wf st1 L x k sl -> slot_wf st2 L x k sl.
  Proof using S.
    intros x k sl Hx SW. destruct sl as [| |q n o r|c o|o]; cbn [slot_wf] in *; try exact I.
    - rewrite u_gss, u_gstride by assumption. destruct SW as (A & B & C & D & E & F & G). repeat (split; [assumption|]).
      split; [apply u_ptr_ok; [exact Hx | exact F] | exact G].
    - destruct SW as (A & B & C & D & E). rewrite u_gss, (sg_kind _ _ S) by assumption. repeat (split; [first [assumption | apply u_is_group; assumption]|]).
      apply u_ptr_ok; [exact Hx | exact E].
    - rewrite u_gss, u_gstride by assumption. destruct SW as (A & B & C). split; [exact A|]. split; [exact B|]. apply u_ptr_ok; [exact Hx | exact C].
  Qed.




  Lemma wf_live_sub : (forall x k q n o r, is_group st2 x -> ~ is_group st1 x -> s_slot st2 x k <> SUser q n o r) ->
    (forall x, is_group st2 x -> ~ is_group st1 x -> g_lastidx st2 x = 0) ->
    wf_live st1 L -> wf_live st2 L.
  Proof using S.
    intros NU NL [IN ND FUN LEN]. constructor.
    - intros p n Hin. destruct (IN p n Hin) as (x & k & o & r & A & B & C). exists x, k, o, r.
      rewrite u_glast, u_user by exact A. split; [apply u_is_group; exact A | tauto].
    - exact ND.
    - intros m1 i1 m2 i2 p n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      destruct (in_dec Z.eq_dec m1 (s_groups st1)) as [G1|G1]; [|exfalso; exact (NU m1 i1 p n1 o1 r1 H1 G1 S1)].
      destruct (in_dec Z.eq_dec m2 (s_groups st1)) as [G2|G2]; [|exfalso; exact (NU m2 i2 p n2 o2 r2 H2 G2 S2)].
      rewrite u_glast in Hk1 by exact G1. rewrite u_glast in Hk2 by exact G2.
      rewrite u_user in S1 by exact G1. rewrite u_user in S2 by exact G2. eauto.
    - exact LEN.
  Qed.

End ExtS.
End MhExtS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MhNtfLib.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.MhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Lib.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.

  (* [comment removed for export] *)
  Lemma cell1_rdn : forall a v, 0 <= v < 256 -> cell M a 1 v -> rdn RSEGS M (Z_to_bv 64 a) 1%nat = Some [Z_to_bv 8 v].
  Proof using.
    intros a v Hv C. unfold cell in C. rewrite C. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    rewrite (u_Z2bv v) by lia. reflexivity.
  Qed.

  Lemma sz_img_of_REP : sz_img M.
  Proof using HREP st. intros a Ha. apply (rc_tab_sc st M (rp_statics st M HREP)). unfold A_TAB_SC, A_TAB_MED. lia. Qed.

  (* [comment removed for export] *)
  Lemma G_meta_cells : forall m, is_group st m ->
    exists ar k, In ar (s_areas st) /\ 0 <= k < NSLOTS /\ m = meta_addr ar k /\ m - m mod 4096 = ar /\
      HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0 /\
      rep_meta M m (s_meta st m) /\ cell M ar 8 (c_secret (s_ctx st)) /\ defined M ar (ar + 4096).
  Proof using HREP HWF L.
    intros m Hm.
    destruct (metaU_area st L HWF m (group_metaU st L HWF m Hm)) as (ar & k & Hin & Hk & E & Hal & Hlo & Hhi & H1 & H2 & H3).
    pose proof (rp_areas st M HREP ar Hin) as RA. destruct (metaU_rng st L HWF m (group_metaU st L HWF m Hm)) as (_ & _ & M8).
    exists ar, k. conjs; try assumption; try lia.
    - rewrite E. exact (ra_metas st M ar RA k Hk).
    - exact (ra_check st M ar RA).
    - exact (ra_def st M ar RA).
  Qed.

  Lemma meta_cells : forall m, metaU st m ->
    exists ar k, In ar (s_areas st) /\ 0 <= k < NSLOTS /\ m = meta_addr ar k /\
      HEAPLO + 24 <= m /\ m + 40 <= CEIL /\ m mod 8 = 0 /\
      rep_meta M m (s_meta st m) /\ defined M ar (ar + 4096) /\ ar + 24 <= m /\ m + 40 <= ar + 4096.
  Proof using HREP HWF L.
    intros m U.
    destruct (metaU_area st L HWF m U) as (ar & k & Hin & Hk & E & Hal & Hlo & Hhi & H1 & H2 & H3).
    pose proof (rp_areas st M HREP ar Hin) as RA. destruct (metaU_rng st L HWF m U) as (_ & _ & M8).
    exists ar, k. conjs; try assumption; try lia.
    - rewrite E. exact (ra_metas st M ar RA k Hk).
    - exact (ra_def st M ar RA).
  Qed.

  Lemma meta_store_ok : forall m, metaU st m -> store_ok RSEGS M (Z_to_bv 64 m) 40%nat = true.
  Proof using HREP HWF L RN.
    intros m U. destruct (meta_cells m U) as (ar & k & Hin & Hk & E & Hlo & Hhi & _ & _ & DF & A1 & A2).
    destruct (wa_rng st (WF_areas st L HWF) ar Hin) as (_ & Rlo & Rhi).
    eapply store_ok_defined; [exact DF | lia | cbn; lia | hsep; unfold HEAPLO in *; lia | ceil; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ctx_store_ok : store_ok RSEGS M (Z_to_bv 64 CTX) 928%nat = true.
  Proof using HREP st. pose proof HREP as _R. apply store_ok_wseg. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma garbage_in_span : forall x k a, is_group st x -> garbage st x k a -> g_mem st x + 12 < a < gspan st x.
  Proof using HWF L RN.
    intros x k a Hx G. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (wg_stride st L x WG) as [S16 _]. pose proof (glast_rng st x) as GL.
    unfold garbage in G. destruct G as [Hk G].
    assert (Ess : forall j, g_slot_start st x j = g_mem st x + 16 + g_stride st x * j) by (intros; unfold g_slot_start, UNIT; lia).
    assert (Ese : forall j, g_slot_end st x j = g_mem st x + 16 + g_stride st x * j + g_stride st x - 4) by (intros; unfold g_slot_end, IB; rewrite Ess; lia).
    assert (Esp : gspan st x = g_mem st x + 16 + g_stride st x * (g_lastidx st x + 1) - 3) by (unfold gspan, g_span_end, g_cnt, UNIT, IB; lia).
    assert (LO : g_mem st x + 12 < g_slot_start st x k - 3) by (rewrite Ess; nia).
    assert (HI : g_slot_end st x k < gspan st x) by (rewrite Ese, Esp; nia).
    pose proof (wg_slots st L x WG k Hk) as SW. pose proof (Ess k) as Ek. pose proof (Ese k) as EEk.
    destruct (s_slot st x k) as [| |q n o r|c o|o] eqn:Sk; try lia; cbn [slot_wf] in SW.
    { destruct SW as (A1 & A2 & A3 & A4 & A5 & _). unfold IB in A4. destruct G as [G|[G|G]]; lia. }
    2:{ destruct SW as (A1 & A2 & _). unfold IB in A2. destruct G as [G|G]; lia. }
    (* [comment removed for export] *)
    destruct SW as (Ho & Hc & _ & Kc & _).
    pose proof (span_in_host st L HWF c x k o Hc Kc) as (_ & _ & LOc & HIc).
    pose proof (ge_span st (WF_geom st L HWF) c Hc) as SP. rewrite Kc in SP. destruct SP as [SP1 SP2].
    pose proof (wg_stride st L c (wG_each st L (WF_groups st L HWF) c Hc)) as [S16c _]. pose proof (glast_rng st c) as GLc.
    assert (g_mem st c + 16 <= gspan st c) by (unfold gspan, g_span_end, g_cnt, UNIT, IB; nia).
    destruct G as [G|G]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma REP_frame : forall M', mem_grows M M' ->
    (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> CEIL <= a \/ exists x k, is_group st x /\ garbage st x k a) ->
    REP st M'.
  Proof using HREP HWF L.
    intros M' HG HW.
    assert (SL : same_layout st st) by (constructor; intros; try reflexivity; apply slot_sim_refl).
    assert (GB : forall a x k, is_group st x -> garbage st x k a -> HEAPLO + 12 < a < CEIL /\ g_mem st x + 12 < a < gspan st x).
    { intros a x k Hx G. pose proof (garbage_in_span x k a Hx G). destruct (group_range st L HWF x Hx). lia. }
    constructor.
    - apply (rep_statics_tr st st M M' HREP (dkeep_of_grows _ _ _ HG)); [|reflexivity|reflexivity].
      intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      destruct (HW a Hr NE) as [W|(x & k & Hx & G)]; [ceil; unfold CTX in *; lia|]. pose proof (GB a x k Hx G). hsep; unfold HEAPLO, CTX in *; lia.
    - apply (rep_ctx_tr st st M M' HREP (dkeep_of_grows _ _ _ HG) (fun _ => false) false); try reflexivity.
      + intros a Hr (Ha & _). destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (HW a Hr NE) as [W|(x & k & Hx & G)]; [ceil; unfold CTX_END, CTX in *; lia|]. pose proof (GB a x k Hx G). hsep; unfold HEAPLO, CTX_END, CTX in *; lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st L M M' HWF HREP (dkeep_of_grows _ _ _ HG) (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Hlo & Hhi).
        destruct (HW a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|(x & k & Hx & G)]; [ceil; lia|].
        apply (ge_garb_area st (WF_geom st L HWF) x k a Hx G). exists ar. split; [exact Har | lia].
      + intros x Ux X. discriminate X.
    - apply (rep_groups_tr st st L M M' HWF HREP (dkeep_of_grows _ _ _ HG)); try (intros; assumption).
      + intros; repeat split; reflexivity.
      + intros x k Hx Hk. left. reflexivity.
      + intros x a Hx G. pose proof (gcell_in_span st L HWF x a Hx G). destruct (group_range st L HWF x Hx).
        destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
        destruct (HW a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|(x2 & k & Hx2 & G2)]; [ceil; lia|].
        exact (ge_garb_cell st (WF_geom st L HWF) x2 k a x Hx2 G2 Hx G).
      + intros x a Hx G. left. exact G.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma J_gm_pre : forall hm hi o rc, is_group st hm -> 0 <= hi <= g_lastidx st hm -> s_slot st hm hi = SJunk o ->
    0 <= rc < 8 ->
    let p := g_slot_start st hm hi + 16 * o in
    byte_at M (p - 4) 0 -> byte_at M (p - 3) (hi + 32 * rc) -> cell M (p - 2) 2 (inband st hm p) ->
      gm_reads M p (g_mem st hm) hm hi rc (inband st hm p) (g_W st hm) (mr_avail (s_meta st hm)) (mr_freed (s_meta st hm))
               (Z_to_bv 64 (c_secret (s_ctx st))) /\
      gm_pure p (g_mem st hm) hm hi rc (inband st hm p) (g_W st hm) (mr_avail (s_meta st hm)) (mr_freed (s_meta st hm)).
  Proof using HREP HWF L RN.
    intros hm hi o rc Hhm Hhi Hs Hrc p B4 B3 B2.
    pose proof (wG_each st L (WF_groups st L HWF) hm Hhm) as WG. pose proof (rp_groups st M HREP hm Hhm) as RG.
    pose proof (wg_slots st L hm WG hi Hhi) as SW. rewrite Hs in SW. cbn [slot_wf] in SW. destruct SW as (Ho & Hfit & PO).
    destruct (G_meta_cells hm Hhm) as (ar & k & Har & Hk & Em & Ear & Mlo & Mhi & M8 & RM & CK & DF).
    destruct RM as [Rp Rn Rme Rav Rfr RW].
    destruct PO as (Pal & Pge & Pmod & Pq & Psc & Pml).
    pose proof (wg_mem st L hm WG) as (G1 & G2 & G3). pose proof (wg_stride st L hm WG) as [S16 Smod].
    pose proof (glast_rng st hm) as GL. pose proof (wg_Wr st L hm WG) as WR.
    pose proof (wg_avr st L hm WG) as AVR. pose proof (wg_frr st L hm WG) as FRR.
    assert (Hp : p = g_mem st hm + 16 + 16 * inband st hm p).
    { unfold inband in *. unfold UNIT in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      pose proof (Z.div_mod (g_slot_start st hm hi + 16 * o - g_mem st hm - 16) 16 ltac:(lia)) as D. rewrite Pmod in D. clear - D. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split.
    - constructor.
      + exact B4.
      + exact B3.
      + exact B2.
      + exact (rg_meta st M hm RG).
      + exact Rme.
      + exact RW.
      + exact Rav.
      + exact Rfr.
      + rewrite Ear. unfold cell in CK. rewrite CK. reflexivity.
      + pose proof (rc_secret st M (rp_ctx st M HREP)) as CS. unfold cell, ctx_secret, CTX in CS. exact CS.
      + exact sz_img_of_REP.
    - constructor; try assumption; try lia.
      + hsep; ceil; unfold HEAPLO in *. subst p. unfold g_slot_start, UNIT in *.
        assert (g_stride st hm * (hi + 1) <= g_stride st hm * (g_lastidx st hm + 1)) by nia.
        unfold g_cnt in G3. unfold IB in Hfit. nia.
      + hsep; unfold HEAPLO in *; lia.
      + ceil; lia.
      + destruct (Z.testbit (mr_avail (s_meta st hm)) hi) eqn:T; [|reflexivity]. exfalso.
        apply (proj1 (wg_av st L hm WG hi ltac:(lia))) in T. destruct T as [_ T]. rewrite Hs in T. discriminate T.
      + destruct (Z.testbit (mr_freed (s_meta st hm)) hi) eqn:T; [|reflexivity]. exfalso.
        apply (proj1 (wg_fr st L hm WG hi ltac:(lia))) in T. destruct T as [_ T]. rewrite Hs in T. discriminate T.
      + destruct (wg_sc st L hm WG) as [H48|(H63 & Hl0 & Hml)].
        * left. split; [exact H48 | exact (Psc H48)].
        * right. split; [exact H63|]. split; [unfold g_maplen in Hml; lia | unfold g_lastidx in Hl0; exact Hl0].
  Qed.
End Lib.
End MhNtfLib.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt MhExtG OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma head_of_app : forall l p, head_of (l ++ [p]) = match l with [] => p | a :: _ => a end.
Proof. intros [|a l] p; reflexivity. Qed.

Lemma In_last : forall (l : list Z) d, l <> [] -> In (last l d) l.
Proof.
  intros l d H. rewrite (app_removelast_last d H) at 2. apply in_app_iff. right. left. reflexivity.
Qed.

Section NewArea.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hfl : s_flist st = [].
  Hypothesis Hac0 : c_avail_cnt (s_ctx st) = 0.
  Variables (p : Z) (regions' : list region) (brk' : brk_state) (ac' sh' cb' : Z).
  Hypothesis Hp : p mod 4096 = 0 /\ HEAPLO <= p /\ p + 4096 <= CEIL.
  Hypothesis Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= p \/ p + 4096 <= a.
  Hypothesis Hp_groups : forall x, is_group st x -> gspan st x <= p \/ p + 4096 <= g_mem st x.
  #[local] Notation cx := (s_ctx st).
  #[local] Notation areas := (s_areas st).
  Definition m : Z := p + 24.
  Definition in_pageb (x : Z) : bool := (p <=? x) && (x <? p + 4096).
  Definition n_meta (x : Z) : meta_rec := if in_pageb x then meta_zero else s_meta st x.
  Definition areas' : list Z := areas ++ [p].
  Definition cx' : ctx_rec :=
    CX (c_secret cx) (c_mmap_ctr cx) (c_free_head cx) (p + 64) 100 ac' sh' (head_of areas') p (p + 4096)
       (c_active cx) (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) cb'.
  Definition st' : mst :=
    MST cx' areas' n_meta [] (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) regions' brk' (s_canary st) (s_errno st) (m :: s_limbo st).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma in_pageb_spec : forall x, in_pageb x = true <-> p <= x < p + 4096.
  Proof using Hp RN. intros x. unfold in_pageb. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
  Lemma meta_addr_in_page : forall k, 0 <= k < NSLOTS -> in_pageb (meta_addr p k) = true.
  Proof using Hp RN. intros k Hk. apply in_pageb_spec. unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *. lia. Qed.
  Lemma old_metaU_out : forall x, metaU st x -> in_pageb x = false.
  Proof using Hp_areas Hp HWF L RN.
    intros x U. destruct (metaU_area st L HWF x U) as (ar & k & Har & Hk & Hx & _ & _ & _ & H1 & H2 & _).
    destruct (in_pageb x) eqn:E; [|reflexivity]. exfalso. apply in_pageb_spec in E. destruct (Hp_areas ar Har); lia.
  Qed.
  Lemma n_meta_old : forall x, metaU st x -> n_meta x = s_meta st x.
  Proof using Hp_areas Hp HWF L RN. intros x U. unfold n_meta. rewrite (old_metaU_out x U). reflexivity. Qed.
  Lemma n_meta_grp : forall x, is_group st x -> n_meta x = s_meta st x.
  Proof using Hp_areas Hp HWF L RN. intros x Hx. apply n_meta_old. exact (group_metaU st L HWF x Hx). Qed.
  Lemma n_meta_page : forall k, 0 <= k < NSLOTS -> n_meta (meta_addr p k) = meta_zero.
  Proof using Hp RN. intros k Hk. unfold n_meta. rewrite (meta_addr_in_page k Hk). reflexivity. Qed.
  Lemma p_notin : ~ In p areas.
  Proof using Hp_areas. intros Hin. destruct (Hp_areas p Hin); lia. Qed.
  Lemma areas_rng : forall a, In a areas -> a mod 4096 = 0 /\ HEAPLO <= a /\ a + 4096 <= CEIL.
  Proof using HWF L. intros a Ha. exact (wa_rng st (WF_areas st L HWF) a Ha). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_areas : s_areas st' = areas ++ [p]. Proof using. reflexivity. Qed.
  Lemma e_flist : s_flist st' = []. Proof using. reflexivity. Qed.
  Lemma e_alist : s_alist st' = s_alist st. Proof using. reflexivity. Qed.
  Lemma e_groups : s_groups st' = s_groups st. Proof using. reflexivity. Qed.
  Lemma e_ai : s_ai st' = s_ai st. Proof using. reflexivity. Qed.
  Lemma e_kind : s_kind st' = s_kind st. Proof using. reflexivity. Qed.
  Lemma e_slot : s_slot st' = s_slot st. Proof using. reflexivity. Qed.
  Lemma e_regions : s_regions st' = regions'. Proof using. reflexivity. Qed.
  Lemma e_brk : s_brk st' = brk'. Proof using. reflexivity. Qed.
  Lemma e_limbo : s_limbo st' = m :: s_limbo st. Proof using. reflexivity. Qed.


  Lemma e_meta : forall x, s_meta st' x = n_meta x. Proof using. reflexivity. Qed.
  Lemma e_is_group : forall x, is_group st' x <-> is_group st x. Proof using Hp RN. intros; unfold is_group; rewrite e_groups; tauto. Qed.
  Lemma e_in_alist : forall x, in_alist st' x <-> in_alist st x. Proof using Hp RN. intros; unfold in_alist; rewrite e_alist; tauto. Qed.
  Lemma e_in_flist : forall x, ~ in_flist st' x. Proof using. intros x H. exact H. Qed.
  Lemma o_in_flist : forall x, ~ in_flist st x. Proof using Hfl. intros x H. unfold in_flist in H. rewrite Hfl in H. exact H. Qed.
  Lemma e_listed : forall x, listed st' x <-> listed st x.
  Proof using Hp Hfl RN.
    intros x. unfold listed. rewrite e_in_alist. split; intros [A|A]; try (right; exact A).
    - exfalso; exact (e_in_flist x A).
    - exfalso; exact (o_in_flist x A).
  Qed.
  Lemma o_fresh : forall x, ~ fresh st x.
  Proof using Hac0. intros x [A _]. rewrite Hac0 in A. lia. Qed.
  Lemma e_fresh : forall x, fresh st' x <-> exists k, 1 <= k < NSLOTS /\ x = meta_addr p k.
  Proof using.
    intros x. unfold fresh. cbn [s_ctx st' c_avail_cnt cx' s_areas]. unfold areas'. rewrite last_last. unfold NSLOTS.
    split.
    - intros [_ (k & Hk & E)]. exists k. split; [lia | exact E].
    - intros (k & Hk & E). split; [lia|]. exists k. split; [lia | exact E].
  Qed.
  Lemma e_metaU : forall x, metaU st' x <-> metaU st x \/ exists k, 0 <= k < NSLOTS /\ x = meta_addr p k.
  Proof using Hp RN.
    intros x. unfold metaU, is_meta_of. rewrite e_areas. split.
    - intros (a & k & Ha & Hk & E). apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]].
      + left. exists a, k. tauto.
      + right. exists k. tauto.
    - intros [(a & k & Ha & Hk & E)|(k & Hk & E)].
      + exists a, k. rewrite in_app_iff. tauto.
      + exists p, k. rewrite in_app_iff. cbn. tauto.
  Qed.
  Lemma listed_metaU : forall x, listed st x -> metaU st x.
  Proof using Hfl HWF L RN.
    intros x [A|(sc & Hsc & Hin)]; [exfalso; exact (o_in_flist x A)|].
    exact (proj1 (proj2 (proj2 (proj2 (alist_member st L HWF sc x Hin))))).
  Qed.

  Lemma e_gW : forall x, is_group st x -> g_W st' x = g_W st x. Proof using Hp_areas Hp HWF L RN. intros; unfold g_W; rewrite e_meta, n_meta_grp by assumption; reflexivity. Qed.
  Lemma e_gmem : forall x, is_group st x -> g_mem st' x = g_mem st x. Proof using Hp_areas Hp HWF L RN. intros; unfold g_mem; rewrite e_meta, n_meta_grp by assumption; reflexivity. Qed.
  Lemma e_avail : forall x, is_group st x -> mr_avail (s_meta st' x) = mr_avail (s_meta st x). Proof using Hp_areas Hp HWF L RN. intros; rewrite e_meta, n_meta_grp by assumption; reflexivity. Qed.
  Lemma e_freed : forall x, is_group st x -> mr_freed (s_meta st' x) = mr_freed (s_meta st x). Proof using Hp_areas Hp HWF L RN. intros; rewrite e_meta, n_meta_grp by assumption; reflexivity. Qed.

  Lemma SG : same_groups st st'.
  Proof using Hp_areas Hp HWF L RN.
    constructor; intros; try reflexivity; [apply slot_sim_refl | |]; rewrite e_meta, n_meta_grp by assumption; reflexivity.
  Qed.
  #[local] Notation yG := (SG).
  Lemma e_glast : forall x, is_group st x -> g_lastidx st' x = g_lastidx st x. Proof using Hp_areas Hp HWF L RN. exact (y_glast st st' yG). Qed.
  Lemma e_gcnt : forall x, is_group st x -> g_cnt st' x = g_cnt st x. Proof using Hp_areas Hp HWF L RN. exact (y_gcnt st st' yG). Qed.
  Lemma e_gsc : forall x, is_group st x -> g_sc st' x = g_sc st x. Proof using Hp_areas Hp HWF L RN. exact (y_gsc st st' yG). Qed.
  Lemma e_gml : forall x, is_group st x -> g_maplen st' x = g_maplen st x. Proof using Hp_areas Hp HWF L RN. exact (y_gml st st' yG). Qed.
  Lemma e_gstride : forall x, is_group st x -> g_stride st' x = g_stride st x. Proof using Hp_areas Hp HWF L RN. exact (y_gstride st st' yG). Qed.
  Lemma e_gss : forall x k, is_group st x -> g_slot_start st' x k = g_slot_start st x k. Proof using Hp_areas Hp HWF L RN. exact (y_gss st st' yG). Qed.



  Lemma e_areab : forall a, areab st' a <-> areab st a \/ p <= a < p + 4096.
  Proof using Hp RN.
    intros a. unfold areab. rewrite e_areas. split.
    - intros (ar & Har & R). apply in_app_iff in Har. destruct Har as [Har|[<-|[]]]; [left; exists ar; tauto | right; exact R].
    - intros [(ar & Har & R)|R]; [exists ar; rewrite in_app_iff; tauto | exists p; rewrite in_app_iff; cbn; tauto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HRgrp : forall b len x, In (RG b len (RGroup x)) regions' <-> In (RG b len (RGroup x)) (s_regions st).
  Hypothesis HRsub : forall r, In r (s_regions st) -> exists r', In r' regions' /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
  Definition INREG (a : Z) : Prop :=
      (exists b len, In (RG b len RBrk) regions' /\ b <= a /\ a + 4096 <= b + len /\
                     match guard_of brk' with Some b0 => b0 + 4096 <= a | None => True end)
      \/ (exists b len e, In (RG b len (RMeta e)) regions' /\ b + 4096 <= a /\ a + 4096 <= b + 4096 * (1 + e)).
  Hypothesis HRold : forall a, In a (s_areas st) -> INREG a.
  Hypothesis HRnew : INREG p.
  Hypothesis Hac' : 0 <= ac'.
  Hypothesis Hcur' : ac' > 0 -> exists b len e, In (RG b len (RMeta e)) regions' /\ 0 <= e /\
                       p + 4096 = b + 4096 * (1 + e) /\ p + 4096 + 4096 * ac' = b + len.
  Hypothesis Hsh' : 0 <= sh' /\ sh' <= Z.of_nat (length (s_areas st)) + 2 /\ (ac' = 0 -> sh' <= Z.of_nat (length (s_areas st)) + 1).
  Hypothesis Hshacc' : 2 ^ (sh' + 1) <= Z.of_nat (length (s_areas st)) + 1 + ac' + sh' + 2.
  Hypothesis Hbrk' : match brk' with
                     | BrkUntried => cb' = 0
                     | BrkLive b0 b _ => cb' = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL
                     | BrkDead _ => cb' = 2 ^ 64 - 1
                     end.

  Lemma t_wf_ctx : wf_ctx st'.
  Proof using Hbrk' Hshacc' Hsh' Hcur' Hac' Hfl HWF L.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of areas' Z.of_nat]; try assumption.
    - rewrite A3, Hfl. reflexivity.
    - unfold NSLOTS. lia.
    - intros _. unfold areas'. rewrite last_last. split; [intros E; apply app_eq_nil in E; destruct E as [_ E]; discriminate E|].
      unfold meta_addr, NSLOTS, AREA_HDR, META_SZ. lia.
    - unfold areas'. rewrite length_app. cbn [length]. lia.
    - reflexivity.
    - unfold areas'. rewrite last_last. reflexivity.
    - unfold areas'. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  Qed.

  Lemma t_wf_areas : wf_areas st'.
  Proof using HRnew HRold Hcnt Hp_areas Hp HWF L.
    destruct (WF_areas st L HWF) as [A B C D]. constructor; rewrite ?e_areas, ?e_regions, ?e_brk.
    - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (A a Ha) | exact Hp].
    - apply NoDup_ListNoDup. apply List.NoDup_app; [apply NoDup_ListNoDup; exact B | constructor; [intros [] | constructor] |].
      intros x Hx [<-|[]]. exact (p_notin Hx).
    - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - intros a Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [exact (HRold a Ha) | exact HRnew].
  Qed.

  Lemma t_wf_lists : wf_lists st'.
  Proof using Hp_areas Hp Hfl HWF L RN.
    destruct (WF_lists st L HWF) as [D1 ND1 FU D2 ND2 AU AN LK LKD RS].
    constructor; rewrite ?e_flist, ?e_alist.
    - intros k Hk. rewrite zlen_nil in Hk. lia.
    - constructor.
    - intros x [].
    - intros sc Hsc. apply (dll_ext st st'); [|exact (D2 sc Hsc)]. intros x Hx. rewrite e_meta, n_meta_grp by exact (proj1 (proj2 (AU sc x Hx))). split; reflexivity.
    - exact ND2.
    - intros sc x Hin. rewrite e_is_group, e_gsc by exact (proj1 (proj2 (AU sc x Hin))). exact (AU sc x Hin).
    - exact AN.
    - intros x U NL. rewrite e_listed in NL. apply e_metaU in U. rewrite e_meta. destruct U as [U|(k & Hk & ->)].
      + rewrite n_meta_old by exact U. exact (LK x U NL).
      + rewrite n_meta_page by exact Hk. split; reflexivity.
    - intros x Hl. rewrite e_listed in Hl. rewrite e_meta, n_meta_old by (apply listed_metaU; exact Hl). exact (LKD x Hl).
    - intros sc x Hin Hne. rewrite e_avail, e_freed by exact (proj1 (proj2 (AU sc x Hin))). exact (RS sc x Hin Hne).
  Qed.

  Lemma grp_not_fresh : forall x, is_group st x -> ~ fresh st' x.
  Proof using Hac' Hp_areas Hp HWF L RN.
    intros x Hx F. apply e_fresh in F. destruct F as (k & Hk & E).
    pose proof (old_metaU_out x (group_metaU st L HWF x Hx)) as O. rewrite E, meta_addr_in_page in O by (unfold NSLOTS in *; lia). discriminate O.
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof using Hac' HRgrp Hp_areas Hp Hfl HWF RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; rewrite ?e_gW, ?e_gmem, ?e_glast, ?e_gcnt, ?e_gsc, ?e_gml, ?e_gstride, ?e_ai, ?e_kind, ?e_slot, ?e_alist, ?e_avail, ?e_freed by exact Hx; try assumption.
    - apply e_metaU. left. exact U.
    - apply grp_not_fresh. exact Hx.
    - apply e_in_flist.
    - intros H63 Hl. apply (S63 H63). apply e_listed. exact Hl.
    - intros Hall Hne Hl. apply (Full Hall Hne). apply e_listed. exact Hl.
    - destruct (s_kind st x) as [|hm j hoff]; [|].
      + destruct Kind as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [apply HRgrp; exact K2|]. split; assumption.
      + destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        rewrite ?e_glast, ?e_gsc, ?e_gss, ?e_gstride by exact K2.
        assert (HG : is_group st' hm) by (apply e_is_group; exact K2).
        repeat (split; [assumption|]). assumption.
    - intros k Hk. apply (y_slot_wf_same st st' L yG); [exact Hx|]. exact (Slots k Hk).
  Qed.

  Lemma m_is_meta0 : m = meta_addr p 0. Proof using st. unfold m, meta_addr, AREA_HDR, META_SZ. lia. Qed.
  Lemma meta_addr_inj : forall k k', meta_addr p k = meta_addr p k' -> k = k'.
  Proof using Hac' ac' st. intros k k' E. unfold meta_addr, META_SZ in E. lia. Qed.

  Lemma t_wf_groups : wf_groups st' L.
  Proof using Hac' HRgrp Hp_areas Hp Hac0 Hfl HWF RN.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; rewrite ?e_groups, ?e_limbo, ?e_regions.
    - exact ND.
    - intros x Hx. apply t_wf_group. exact Hx.
    - intros m1 m2 H1 H2. rewrite !e_ai. rewrite !e_glast, !e_gsc by assumption. exact (ONE m1 m2 H1 H2).
    - intros b len x Hin. apply HRgrp in Hin. pose proof (REG b len x Hin) as (G & K & E1 & E2).
      rewrite e_is_group, e_kind, e_gmem, e_gml by exact G. repeat split; assumption.
    - intros x F. apply e_fresh in F. destruct F as (k & Hk & ->). rewrite e_meta. apply n_meta_page. unfold NSLOTS in *; lia.
    - intros x U NG NFL NFR. rewrite e_is_group in NG. apply e_metaU in U. destruct U as [U|(k & Hk & ->)].
      + right. apply (OTH x U NG (o_in_flist x) (o_fresh x)).
      + destruct (Z.eq_dec k 0) as [->|Hk0]; [left; exact m_is_meta0|].
        exfalso. apply NFR. apply e_fresh. exists k. split; [lia | reflexivity].
    - intros x [<-|Hl].
      + rewrite e_metaU, e_is_group, e_fresh, e_listed. split; [right; exists 0; split; [unfold NSLOTS; lia | exact m_is_meta0]|].
        assert (NU : ~ metaU st m).
        { intros U. pose proof (old_metaU_out m U) as O. rewrite m_is_meta0, meta_addr_in_page in O by (unfold NSLOTS; lia). discriminate O. }
        split; [intros G; exact (NU (group_metaU st L HWF m G))|].
        split; [intros Hl; exact (NU (listed_metaU m Hl))|].
        intros (k & Hk & E). rewrite m_is_meta0 in E. apply meta_addr_inj in E. lia.
      + destruct (LIM x Hl) as (A & B & C & D). rewrite e_metaU, e_is_group, e_fresh, e_listed. split; [left; exact A|]. split; [exact B|]. split; [exact C|].
        intros (k & Hk & E). pose proof (old_metaU_out x A) as O. rewrite E, meta_addr_in_page in O by (unfold NSLOTS in *; lia). discriminate O.
    - intros m1 m2 H1 H2 G1 G2 E. change (is_group st m1) in H1. change (is_group st m2) in H2.
      rewrite !e_gsc in E by assumption. rewrite e_glast in G1 by exact H1. rewrite e_glast in G2 by exact H2. rewrite !e_slot in G1, G2.
      exact (ONEFF m1 m2 H1 H2 G1 G2 E).
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using Hac' HRsub Hp_groups Hp_areas Hp HWF L RN.
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN]. constructor; rewrite ?e_regions.
    - intros x Hx. apply e_is_group in Hx. rewrite (y_gmem st st' yG), (y_gspan st st' yG) by exact Hx.
      destruct (INR x Hx) as (r & Hr & R1 & R2). destruct (HRsub r Hr) as (r' & Hr' & E1 & E2). exists r'. rewrite E1, E2. repeat split; assumption.
    - intros m1 m2 a H1 H2 Hne G1 G2. apply e_is_group in H1. apply e_is_group in H2.
      apply (y_gcell st st' L yG HWF) in G1; [|exact H1]. apply (y_gcell st st' L yG HWF) in G2; [|exact H2]. eauto.
    - intros x a Hx R Ar. apply e_is_group in Hx. rewrite (y_gmem st st' yG), (y_gspan st st' yG) in R by exact Hx.
      apply e_areab in Ar. destruct Ar as [Ar|Ar]; [exact (AREA x a Hx R Ar)|]. destruct (Hp_groups x Hx); lia.
    - intros x a Hx G Ap. apply e_is_group in Hx. apply (y_gcell st st' L yG HWF) in G; [|exact Hx]. apply (y_appb st st' yG) in Ap. eauto.
    - intros a Ap Ar. apply (y_appb st st' yG) in Ap. apply e_areab in Ar. destruct Ar as [Ar|Ar]; [exact (APA a Ap Ar)|].
      destruct (appb_in_span st L HWF a Ap) as (x & Hx & R). destruct (Hp_groups x Hx); lia.
    - intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      apply e_is_group in H1. apply e_is_group in H2. rewrite (y_glast st st' yG) in Hk1 by exact H1. rewrite (y_glast st st' yG) in Hk2 by exact H2.
      rewrite e_slot in S1, S2. eauto.
    - intros x k a x2 Hx G H2 C. apply e_is_group in Hx. apply e_is_group in H2.
      apply (y_garbage st st' L yG HWF) in G; [|exact Hx]. apply (y_gcell st st' L yG HWF) in C; [|exact H2]. eauto.
    - intros x k a Hx G Ap. apply e_is_group in Hx. apply (y_garbage st st' L yG HWF) in G; [|exact Hx]. apply (y_appb st st' yG) in Ap. eauto.
    - intros x k a Hx G Ar. apply e_is_group in Hx. apply (y_garbage st st' L yG HWF) in G; [|exact Hx]. apply e_areab in Ar.
      destruct Ar as [Ar|Ar]; [exact (GAR x k a Hx G Ar)|].
      pose proof (garbage_in_span st L HWF x k a Hx G) as R. destruct (Hp_groups x Hx); lia.
    - intros x Hx. apply e_is_group in Hx. rewrite e_kind, (y_gspan st st' yG), (y_gmem st st' yG), (y_gml st st' yG) by exact Hx.
      pose proof (SPAN x Hx) as SP. destruct (s_kind st x) as [|hm j o] eqn:K; [exact SP|].
      pose proof (y_host_group st L HWF x hm j o Hx K) as Hh. rewrite (y_gss st st' yG), (y_gse st st' yG) by exact Hh. exact SP.
  Qed.

  (* [comment removed for export] *)
  Hypothesis HWR' : wf_regions st'.
  Hypothesis HWI' : wf_img st'.

  Lemma t_WF : WF st' L.
  Proof using HWI' HWR' Hbrk' Hshacc' Hsh' Hcur' Hac' HRnew HRold HRsub HRgrp Hcnt Hp_groups Hp_areas Hp Hac0 Hfl HWF.
    split; [exact t_wf_ctx|]. split; [exact t_wf_areas|]. split; [exact t_wf_lists|]. split; [exact t_wf_groups|].
    split; [exact t_wf_geom|]. split; [exact (wf_live_ext st st' L yG (WF_live st L HWF)) |]. split; [exact HWR' | exact HWI'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation tl := (c_area_tail cx).
  Definition ctxW (a : Z) : Prop :=
    (ctx_avail_meta <= a < ctx_avail_meta + 16) \/ (ctx_avail_meta_area_count <= a < ctx_avail_meta_area_count + 40) \/
    (ctx_brk <= a < ctx_brk + 8).
  (* [comment removed for export] *)
  Hypothesis HMlow : agree_on (fun a => IMG_LO <= a < CTX) M M'.
  Hypothesis HMctx : agree_on (fun a => CTX <= a < CTX_END /\ ~ ctxW a) M M'.
  Hypothesis HMam : cell M' ctx_avail_meta 8 (p + 64).
  Hypothesis HMamc : cell M' ctx_avail_meta_count 8 100.
  Hypothesis HMac : cell M' ctx_avail_meta_area_count 8 ac'.
  Hypothesis HMsh : cell M' ctx_meta_alloc_shift 8 sh'.
  Hypothesis HMhd : cell M' ctx_meta_area_head 8 (head_of areas').
  Hypothesis HMtl : cell M' ctx_meta_area_tail 8 p.
  Hypothesis HMcur : cell M' ctx_avail_meta_areas 8 (p + 4096).
  Hypothesis HMcb : cell M' ctx_brk 8 cb'.
  Hypothesis HMkeep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Hypothesis HMareas : forall ar a, In ar areas -> ar <= a < ar + 4096 -> ~ (tl + 8 <= a < tl + 16) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Hypothesis HMgrp : forall t a, is_group st t -> s_kind st t = GTop -> g_mem st t <= a < g_map_end st t -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Hypothesis HMpdef : defined M' p (p + 4096).
  Hypothesis HMchk : cell M' p 8 (c_secret cx).
  Hypothesis HMns : cell M' (p + 16) 4 NSLOTS.
  Hypothesis HMpz : forall a, p + 24 <= a < p + 4096 -> M' (Z_to_bv 64 a) = Some (Z_to_bv 8 0).

  Lemma tl_val : tl = last areas 0. Proof using HWF L RN. exact (wc_tail st (WF_ctx st L HWF)). Qed.

  Lemma t_rep_statics : rep_statics st' M'.
  Proof using HMkeep HMlow HREP M. apply (rep_statics_tr st st' M M' HREP HMkeep HMlow); reflexivity. Qed.

  Lemma t_rep_ctx : rep_ctx st' M'.
  Proof using HMcb HMcur HMtl HMhd HMsh HMac HMamc HMam HMctx Hac' HREP M.
    pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
    assert (TR : forall a k v, CTX <= a -> a + Z.of_nat k <= CTX_END ->
              (a + Z.of_nat k <= ctx_avail_meta \/ (ctx_avail_meta + 16 <= a /\ a + Z.of_nat k <= ctx_avail_meta_area_count) \/
               (ctx_avail_meta_area_count + 40 <= a /\ a + Z.of_nat k <= ctx_brk)) ->
              cell M a k v -> cell M' a k v).
    { intros a k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
      eapply agree_on_mono; [exact HMctx|]. cbn. intros b Hb. split; [lia|]. unfold ctxW.
      unfold ctx_avail_meta, ctx_avail_meta_area_count, ctx_brk, CTX, CTX_END in *. lia. }
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
    constructor; cbn [s_ctx st' cx' c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift c_area_head c_area_tail
                      c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try assumption; try (ctxg TR).
    - intros sc Hsc. ctxg TR.
    - intros sc Hsc. ctxg TR.
    - intros i Hi. ctxg TR.
    - intros i Hi. ctxg TR.
  Qed.

  Lemma tl_facts : areas <> [] -> In tl areas /\ tl mod 4096 = 0 /\ HEAPLO <= tl /\ tl + 4096 <= CEIL.
  Proof using HWF L.
    intros Hne. rewrite tl_val.
    assert (Hin : In (last areas 0) areas) by (apply In_last; exact Hne).
    split; [exact Hin | exact (areas_rng _ Hin)].
  Qed.

  Lemma t_rep_area_old : forall ar, In ar areas -> rep_area st' M' ar.
  Proof using HMareas HMkeep Hsh' Hac' Hp_areas Hp HREP HWF M L RN.
    intros ar Har. pose proof (rp_areas st M HREP ar Har) as [CK NS DF MT].
    destruct (areas_rng ar Har) as (Hal & Hlo & Hhi). ceil; unfold HEAPLO in Hlo, Hhi.
    assert (NE : areas <> []) by (intros E; rewrite E in Har; exact Har).
    destruct (tl_facts NE) as (Tin & Tal & Tlo & Thi). ceil; unfold HEAPLO in Tlo, Thi.
    assert (SEP : ar = tl \/ ar + 4096 <= tl \/ tl + 4096 <= ar).
    { destruct (Z.eq_dec ar tl) as [E|Hne]; [left; exact E | right].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (AG : agree_on (fun a => ar <= a < ar + 4096 /\ ~ (ar + 8 <= a < ar + 16)) M M').
    { intros a Hr [Ha Hn]. apply (HMareas ar a Har Ha). intros Ht. destruct SEP as [E|[D|D]]; [subst; tauto | lia | lia]. }
    constructor.
    - cbn [s_ctx st' cx' c_secret]. eapply cell_agree; [lia | cbn; lia | | exact CK]. eapply agree_on_mono; [exact AG|]. cbn; intros; lia.
    - eapply cell_agree; [lia | cbn; lia | | exact NS]. eapply agree_on_mono; [exact AG|]. cbn; intros; lia.
    - intros a Ha. destruct (decide (ar + 8 <= a < ar + 16)) as [Hh|Hh].
      + destruct SEP as [E|[D|D]].
        * (* [comment removed for export] *)
          apply (HMkeep a); [right; right; left; exists ar; split; [exact Har | lia] | exact (DF a Ha)].
        * rewrite (HMareas ar a Har Ha) by lia. exact (DF a Ha).
        * rewrite (HMareas ar a Har Ha) by lia. exact (DF a Ha).
      + rewrite (HMareas ar a Har Ha); [exact (DF a Ha)|]. intros Ht. destruct SEP as [E|[D|D]]; [subst; tauto | lia | lia].
    - intros k Hk. rewrite e_meta, n_meta_old by (exists ar, k; repeat split; try assumption; lia).
      eapply rep_meta_agree; [| | | exact (MT k Hk)]; [unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia |].
      eapply agree_on_mono; [exact AG|]. cbn. unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *. intros; lia.
  Qed.

  Lemma t_rep_area_new : rep_area st' M' p.
  Proof using HMpz HMns HMchk HMpdef Hac' Hp RN.
    destruct Hp as (Hal & Hlo & Hhi). ceil; unfold HEAPLO in Hlo, Hhi.
    constructor.
    - cbn [s_ctx st' cx' c_secret]. exact HMchk.
    - exact HMns.
    - exact HMpdef.
    - intros k Hk. rewrite e_meta, n_meta_page by exact Hk.
      apply rep_meta_zero; [unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia | unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia |].
      intros i Hi. apply HMpz. unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *. lia.
  Qed.

  Lemma t_rep_groups : forall x, is_group st' x -> rep_group st' M' x.
  Proof using HMgrp HMkeep Hac' Hp_areas Hp HREP HWF M L RN.
    apply (rep_groups_tr st st' L M M' HWF HREP HMkeep).
    - intros x Hx. apply e_is_group. exact Hx.
    - intros x Hx. apply e_is_group in Hx. rewrite e_meta, n_meta_grp by exact Hx. repeat split; reflexivity.
    - intros x Hx E. apply e_is_group in Hx. apply (y_endb st st' L yG HWF); [exact Hx | exact E].
    - intros x k Hx Hk. left. reflexivity.
    - intros x a Hx G. apply e_is_group in Hx. apply (y_gcell st st' L yG HWF) in G; [|exact Hx].
      destruct (group_in_top st L HWF x Hx) as (t & Ht & Kt & T1 & T2 & _).
      pose proof (gcell_in_span st L HWF x a Hx G). apply (HMgrp t a Ht Kt). lia.
    - intros x a Hx G. left. apply (y_gcell st st' L yG HWF); [apply e_is_group; exact Hx | exact G].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HMpz HMns HMchk HMpdef HMgrp HMareas HMkeep HMcb HMcur HMtl HMhd HMsh HMac HMamc HMam HMctx HMlow Hsh' Hac' Hp_areas Hp HREP HWF M L RN.
    constructor.
    - exact t_rep_statics.
    - exact t_rep_ctx.
    - intros a Ha. rewrite e_areas in Ha. apply in_app_iff in Ha. destruct Ha as [Ha|[<-|[]]]; [apply t_rep_area_old; exact Ha | exact t_rep_area_new].
    - exact t_rep_groups.
  Qed.

  Theorem newarea_close : WF st' L /\ REP st' M'.
  Proof using HMpz HMns HMchk HMpdef HMgrp HMareas HMkeep HMcb HMcur HMtl HMhd HMsh HMac HMamc HMam HMctx HMlow HWI' HWR' Hbrk' Hshacc' Hsh' Hcur' Hac' HRnew HRold HRsub HRgrp Hcnt Hp_groups Hp_areas Hp Hac0 Hfl HREP HWF M. split; [exact t_WF | exact t_REP]. Qed.
End NewArea.
