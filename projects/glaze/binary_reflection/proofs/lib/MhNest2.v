(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module MhNest.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.glaze.binary_reflection.images.Plain.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Nest.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  (* [comment removed for export] *)
  Lemma group_in_top_fuel : forall fuel x, nest_depth_le st fuel x -> is_group st x ->
    exists t, is_group st t /\ s_kind st t = GTop /\ g_mem st t <= g_mem st x /\ gspan st x <= g_map_end st t.
  Proof using HWF L RN.
    induction fuel as [|f IH]; intros x D Hx.
    - cbn in D. destruct (s_kind st x) as [|hm j o] eqn:Kx; [|destruct D].
      exists x. pose proof (ge_span st (WF_geom st L HWF) x Hx) as SP. rewrite Kx in SP.
      split; [exact Hx|]. split; [exact Kx|]. unfold g_map_end. split; [lia | exact SP].
    - cbn in D. destruct (s_kind st x) as [|hm j o] eqn:Kx.
      + apply (IH x); [destruct f; cbn; rewrite Kx; exact I | exact Hx].
      + destruct (span_in_host st L HWF x hm j o Hx Kx) as (Hh & _ & LO & HI).
        destruct (IH hm D Hh) as (t & Ht & Kt & T1 & T2). exists t. repeat split; try assumption; lia.
  Qed.

  Lemma group_in_top : forall x, is_group st x ->
    exists t, is_group st t /\ s_kind st t = GTop /\ g_mem st t <= g_mem st x /\ gspan st x <= g_map_end st t /\
              In (RG (g_mem st t) (4096 * g_maplen st t) (RGroup t)) (s_regions st).
  Proof using HWF L RN.
    intros x Hx. destruct (group_in_top_fuel 8 x (wg_depth st L x (wG_each st L (WF_groups st L HWF) x Hx)) Hx) as (t & Ht & Kt & T1 & T2).
    exists t. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as K. rewrite Kt in K.
    destruct K as (_ & Hin & _). repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma group_apart_region : forall x r, is_group st x -> In r (s_regions st) ->
    (forall m, rg_kind r <> RGroup m) ->
    gspan st x <= rg_base r \/ rg_base r + rg_len r <= g_mem st x.
  Proof using HWF L RN.
    intros x r Hx Hr Hk. destruct (group_in_top x Hx) as (t & Ht & Kt & T1 & T2 & Hin).
    assert (Hne : RG (g_mem st t) (4096 * g_maplen st t) (RGroup t) <> r) by (intros <-; exact (Hk t eq_refl)).
    destruct (wr_disj st (WF_regions st L HWF) _ _ Hin Hr Hne) as [D|D]; cbn [rg_base rg_len] in D; unfold g_map_end in T2; [left | right]; lia.
  Qed.

  Lemma gspan_gt : forall x, is_group st x -> g_mem st x + 16 < gspan st x.
  Proof using HWF L RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (wg_stride st L x WG) as [S16 _]. pose proof (glast_rng st x).
    assert (g_stride st x * 1 <= g_stride st x * g_cnt st x) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    unfold gspan, g_span_end, UNIT, IB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma appb_in_span : forall a, appb st a -> exists x, is_group st x /\ g_mem st x + 16 <= a < gspan st x.
  Proof using HWF L RN.
    intros a (x & k & p & n & off & res & Hx & Hk & Sk & Ha). exists x. split; [exact Hx|].
    pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    pose proof (wg_slots st L x WG k Hk) as SW. rewrite Sk in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & A3 & A4 & A5 & _).
    pose proof (wg_stride st L x WG) as [S16 _].
    assert (g_stride st x * (k + 1) <= g_stride st x * g_cnt st x) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    assert (0 <= g_stride st x * k) by (apply Z.mul_nonneg_nonneg; lia).
    unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma area_in_region : forall a, In a (s_areas st) ->
    exists r, In r (s_regions st) /\ (forall m, rg_kind r <> RGroup m) /\ rg_base r <= a /\ a + 4096 <= rg_base r + rg_len r.
  Proof using HWF L RN.
    intros a Ha. destruct (wa_inreg st (WF_areas st L HWF) a Ha) as [(b & len & Hin & H1 & H2 & _)|(b & len & e & Hin & H1 & H2)].
    - exists (RG b len RBrk). cbn. repeat split; try assumption. intros m E; discriminate E.
    - exists (RG b len (RMeta e)). cbn. destruct (wr_meta st (WF_regions st L HWF) b len e Hin) as (E1 & E2 & E3).
      repeat split; try assumption; try lia. intros m E; discriminate E.
  Qed.

  Lemma area_apart_group : forall a x, In a (s_areas st) -> is_group st x ->
    gspan st x <= a \/ a + 4096 <= g_mem st x.
  Proof using HWF L RN.
    intros a x Ha Hx. destruct (area_in_region a Ha) as (r & Hr & Hk & R1 & R2).
    destruct (group_apart_region x r Hx Hr Hk); lia.
  Qed.
End Nest.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Zero.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma rdn_const_zero : forall n (M : mem) (a : word),
    bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> M x = Some (Z_to_bv 8 0)) ->
    rdn RSEGS M a n = Some (repeat (Z_to_bv 8 0) n).
  Proof using.
    induction n as [|n IH]; intros M a Hnw Hz; [reflexivity|].
    cbn [rdn repeat]. rewrite (Hz a) by (pose proof (u64_range a); lia).
    destruct n as [|n'].
    - reflexivity.
    - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      rewrite (IH M (a + 1)%bv); [reflexivity | rewrite Hu1; lia | intros x Hx; rewrite Hu1 in Hx; apply Hz; lia].
  Qed.

  Lemma cell_zero8 : forall (M : mem) a, 0 <= a -> a + 8 <= 2 ^ 64 ->
    (forall i, a <= i < a + 8 -> M (Z_to_bv 64 i) = Some (Z_to_bv 8 0)) -> cell M a 8 0.
  Proof using.
    intros M a Ha Hnw Hz. unfold cell. rewrite (rdn_const_zero 8 M (Z_to_bv 64 a)); [reflexivity | rewrite u_Z2bv by lia; cbn; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite <- (Hz (bv_unsigned x)) by (cbn in Hx; lia).
    f_equal. symmetry. apply bv_eq. rewrite u_Z2bv by (pose proof (u64_range x); lia). reflexivity.
  Qed.

  Lemma cell_zero4 : forall (M : mem) a, 0 <= a -> a + 4 <= 2 ^ 64 ->
    (forall i, a <= i < a + 4 -> M (Z_to_bv 64 i) = Some (Z_to_bv 8 0)) -> cell M a 4 0.
  Proof using.
    intros M a Ha Hnw Hz. unfold cell. rewrite (rdn_const_zero 4 M (Z_to_bv 64 a)); [reflexivity | rewrite u_Z2bv by lia; cbn; lia |].
    intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite <- (Hz (bv_unsigned x)) by (cbn in Hx; lia).
    f_equal. symmetry. apply bv_eq. rewrite u_Z2bv by (pose proof (u64_range x); lia). reflexivity.
  Qed.

  Lemma rep_meta_zero : forall (M : mem) x, 0 <= x -> x + 40 <= 2 ^ 64 ->
    (forall i, x <= i < x + 40 -> M (Z_to_bv 64 i) = Some (Z_to_bv 8 0)) -> rep_meta M x meta_zero.
  Proof using.
    intros M x Hx Hnw Hz. constructor; cbn [mr_prev mr_next mr_mem mr_avail mr_freed mr_W meta_zero];
      first [apply cell_zero8 | apply cell_zero4]; try lia; intros i Hi; apply Hz; lia.
  Qed.
End Zero.
End MhNest.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover MhNest.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Nest2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)).
  Hypothesis HWF : WF st L.

  (* [comment removed for export] *)
  Definition hosted (x y : Z) : Prop :=
    exists k c o, 0 <= k <= g_lastidx st x /\ s_slot st x k = SHost c o /\ is_group st c /\
      s_kind st c = GNest x k o /\ g_mem st c <= g_mem st y /\ gspan st y <= gspan st c.

  Definition dich (x y : Z) : Prop :=
    gspan st x <= g_mem st y \/ gspan st y <= g_mem st x \/ hosted x y \/ hosted y x.

  Lemma dich_sym : forall x y, dich x y -> dich y x.
  Proof using. intros x y [A|[A|[A|A]]]; unfold dich; tauto. Qed.

  Lemma Ess : forall x k, g_slot_start st x k = g_mem st x + 16 + g_stride st x * k.
  Proof using. intros; unfold g_slot_start, UNIT; lia. Qed.
  Lemma Ese : forall x k, g_slot_end st x k = g_mem st x + 16 + g_stride st x * k + g_stride st x - 4.
  Proof using. intros; unfold g_slot_end, IB; rewrite Ess; lia. Qed.
  Lemma Esp : forall x, gspan st x = g_mem st x + 16 + g_stride st x * (g_lastidx st x + 1) - 3.
  Proof using. intros; unfold gspan, g_span_end, g_cnt, UNIT, IB; lia. Qed.

  Lemma WG : forall x, is_group st x -> wf_group st L x.
  Proof using HWF RN. intros x Hx. exact (wG_each st L (WF_groups st L HWF) x Hx). Qed.

  Lemma str16 : forall x, is_group st x -> 16 <= g_stride st x.
  Proof using HWF L RN. intros x Hx. exact (proj1 (wg_stride st L x (WG x Hx))). Qed.

  (* [comment removed for export] *)
  Lemma nest_facts : forall x hm j o, is_group st x -> s_kind st x = GNest hm j o ->
    is_group st hm /\ hm <> x /\ 0 <= j <= g_lastidx st hm /\ s_slot st hm j = SHost x o /\ 0 <= o /\
    g_mem st x = g_slot_start st hm j + 16 * o /\ gspan st x <= g_slot_end st hm j + 1 /\
    g_mem st hm + 16 <= g_mem st x /\ gspan st x <= gspan st hm.
  Proof using HWF L RN.
    intros x hm j o Hx Kx.
    pose proof (wg_kind st L x (WG x Hx)) as KD. rewrite Kx in KD.
    destruct KD as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
    pose proof (ge_span st (WF_geom st L HWF) x Hx) as SP. rewrite Kx in SP. destruct SP as [SP1 SP2].
    destruct (span_in_host st L HWF x hm j o Hx Kx) as (_ & _ & LO & HI).
    repeat split; try assumption; lia.
  Qed.

  Lemma child_facts : forall x k c o, is_group st x -> 0 <= k <= g_lastidx st x -> s_slot st x k = SHost c o ->
    is_group st c /\ s_kind st c = GNest x k o.
  Proof using HWF L RN.
    intros x k c o Hx Hk Sk. pose proof (wg_slots st L x (WG x Hx) k Hk) as SW. rewrite Sk in SW.
    cbn [slot_wf] in SW. destruct SW as (_ & Hc & _ & Kc & _). split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma slots_apart : forall x k1 k2, is_group st x -> 0 <= k1 -> k1 < k2 ->
    g_slot_end st x k1 + 1 <= g_slot_start st x k2 - 3.
  Proof using HWF L RN.
    intros x k1 k2 Hx Hk1 Hlt. pose proof (str16 x Hx). rewrite Ese, Ess.
    assert (g_stride st x * (k1 + 1) <= g_stride st x * k2) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  Lemma slot_in_span : forall x k, is_group st x -> 0 <= k <= g_lastidx st x ->
    g_mem st x + 13 <= g_slot_start st x k - 3 /\ g_slot_end st x k + 1 <= gspan st x.
  Proof using HWF L RN.
    intros x k Hx Hk. pose proof (str16 x Hx). rewrite Ese, Ess, Esp.
    assert (0 <= g_stride st x * k) by (apply Z.mul_nonneg_nonneg; lia).
    assert (g_stride st x * (k + 1) <= g_stride st x * (g_lastidx st x + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  Lemma top_top : forall x y, is_group st x -> is_group st y -> x <> y -> s_kind st x = GTop -> s_kind st y = GTop ->
    gspan st x <= g_mem st y \/ gspan st y <= g_mem st x.
  Proof using HWF L RN.
    intros x y Hx Hy Hne Kx Ky.
    pose proof (wg_kind st L x (WG x Hx)) as KX. rewrite Kx in KX.
    pose proof (wg_kind st L y (WG y Hy)) as KY. rewrite Ky in KY.
    destruct KX as (X1 & X2 & X3 & X4). destruct KY as (Y1 & Y2 & Y3 & Y4).
    pose proof (ge_span st (WF_geom st L HWF) x Hx) as SPx. rewrite Kx in SPx.
    pose proof (ge_span st (WF_geom st L HWF) y Hy) as SPy. rewrite Ky in SPy.
    pose proof (wr_disj st (WF_regions st L HWF) _ _ X2 Y2 ltac:(intros E; injection E; intros; exact (Hne ltac:(assumption)))) as DJ.
    cbn [rg_base rg_len] in DJ. lia.
  Qed.

  Lemma same_mem : forall x y, is_group st x -> is_group st y -> x <> y -> g_mem st x = g_mem st y -> False.
  Proof using HWF L RN.
    intros x y Hx Hy Hne E. apply (ge_cells st (WF_geom st L HWF) x y (g_mem st x) Hx Hy Hne); unfold gcell; left; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma top_not_inside : forall x y, is_group st x -> is_group st y -> x <> y -> s_kind st x = GTop ->
    g_mem st y <= g_mem st x -> gspan st x <= gspan st y -> False.
  Proof using HWF L RN.
    intros x y Hx Hy Hne Kx C1 C2.
    destruct (group_in_top st L HWF y Hy) as (t & Ht & Kt & T1 & T2 & Hin).
    pose proof (wg_kind st L x (WG x Hx)) as KX. rewrite Kx in KX. destruct KX as (X1 & X2 & X3 & X4).
    pose proof (gspan_gt st L HWF x Hx). pose proof (gspan_gt st L HWF y Hy).
    destruct (Z.eq_dec t x) as [->|Htx].
    - exact (same_mem x y Hx Hy Hne ltac:(lia)).
    - pose proof (wr_disj st (WF_regions st L HWF) _ _ Hin X2 ltac:(intros E; injection E; intros; exact (Htx ltac:(assumption)))) as DJ.
      cbn [rg_base rg_len] in DJ. unfold g_map_end in T2. lia.
  Qed.

  Lemma depth_top : forall f x, s_kind st x = GTop -> nest_depth_le st f x.
  Proof using. intros f x K. destruct f; cbn; rewrite K; exact I. Qed.
  Lemma depth_nest : forall f x hm j o, s_kind st x = GNest hm j o -> nest_depth_le st f hm -> nest_depth_le st (S f) x.
  Proof using. intros f x hm j o K D. cbn. rewrite K. exact D. Qed.

  Lemma dich_main : forall n fa fb x y, (fa + fb <= n)%nat ->
    nest_depth_le st fa x -> nest_depth_le st fb y -> is_group st x -> is_group st y -> x <> y -> dich x y.
  Proof using HWF L RN.
    induction n as [|n IH]; intros fa fb x y Hn Dx Dy Hx Hy Hne.
    - destruct fa; [|lia]. destruct fb; [|lia]. cbn in Dx, Dy.
      destruct (s_kind st x) eqn:Kx; [|destruct Dx]. destruct (s_kind st y) eqn:Ky; [|destruct Dy].
      destruct (top_top x y Hx Hy Hne Kx Ky); unfold dich; tauto.
    - (* [comment removed for export] *)
      assert (STEP : forall fa' fb x y hm j o, (fa' + fb <= n)%nat -> s_kind st x = GNest hm j o ->
                nest_depth_le st fa' hm -> nest_depth_le st fb y -> is_group st x -> is_group st y -> x <> y -> dich x y).
      { clear fa fb x y Hn Dx Dy Hx Hy Hne. intros fa' fb x y hm j o Hn Kx Dhm Dy Hx Hy Hne.
        destruct (nest_facts x hm j o Hx Kx) as (Hh & Hhx & Hj & Sj & Ho & Emx & Spx & LOx & HIx).
        pose proof (gspan_gt st L HWF x Hx) as NEx. pose proof (gspan_gt st L HWF y Hy) as NEy.
        destruct (Z.eq_dec hm y) as [->|Hhy].
        { right; right; right. exists j, x, o. repeat split; try assumption; lia. }
        destruct (IH fa' fb hm y Hn Dhm Dy Hh Hy Hhy) as [A|[A|[A|A]]].
        - left. lia.
        - right; left. lia.
        - destruct A as (k & c & oc & Hk & Sk & Hc & Kc & C1 & C2).
          destruct (Z.eq_dec k j) as [->|Hkj].
          + rewrite Sj in Sk. injection Sk. intros <- <-.
            (* [comment removed for export] *)
            destruct fb as [|fb'].
            { cbn in Dy. destruct (s_kind st y) eqn:Ky; [|destruct Dy].
              exfalso. exact (top_not_inside y x Hy Hx (fun E => Hne (eq_sym E)) Ky C1 C2). }
            cbn in Dy. destruct (s_kind st y) as [|hy jy oy] eqn:Ky.
            { exfalso. exact (top_not_inside y x Hy Hx (fun E => Hne (eq_sym E)) Ky C1 C2). }
            destruct (nest_facts y hy jy oy Hy Ky) as (Hhy' & Hhyy & Hjy & Sjy & Hoy & Emy & Spy & LOy & HIy).
            destruct (Z.eq_dec hy x) as [->|Hhyx].
            { right; right; left. exists jy, y, oy. repeat split; try assumption; lia. }
            destruct (IH (S fa') fb' x hy ltac:(lia) (depth_nest fa' x hm j o Kx Dhm) Dy Hx Hhy' (fun E => Hhyx (eq_sym E)))
              as [B|[B|[B|B]]].
            * exfalso. lia.
            * exfalso. lia.
            * destruct B as (k' & c' & o' & Hk' & Sk' & Hc' & Kc' & D1 & D2).
              right; right; left. exists k', c', o'. repeat split; try assumption; lia.
            * destruct B as (k' & c' & o' & Hk' & Sk' & Hc' & Kc' & D1 & D2). exfalso.
              destruct (Z.eq_dec k' jy) as [->|NE].
              -- rewrite Sjy in Sk'. injection Sk'. intros <- <-. exact (same_mem x y Hx Hy Hne ltac:(lia)).
              -- destruct (nest_facts c' hy k' o' Hc' Kc') as (_ & _ & _ & _ & Ho' & Emc & Spc & _ & _).
                 destruct (Z.lt_ge_cases k' jy) as [LT|GE].
                 ++ pose proof (slots_apart hy k' jy Hhy' ltac:(lia) LT). lia.
                 ++ pose proof (slots_apart hy jy k' Hhy' ltac:(lia) ltac:(lia)). lia.
          + (* [comment removed for export] *)
            destruct (nest_facts c hm k oc Hc Kc) as (_ & _ & _ & _ & Hoc & Emc & Spc & _ & _).
            pose proof (gspan_gt st L HWF c Hc).
            destruct (Z.lt_ge_cases k j) as [LT|GE].
            * pose proof (slots_apart hm k j Hh ltac:(lia) LT). right; left. lia.
            * pose proof (slots_apart hm j k Hh ltac:(lia) ltac:(lia)). left. lia.
        - destruct A as (k & c & oc & Hk & Sk & Hc & Kc & C1 & C2).
          right; right; right. exists k, c, oc. repeat split; try assumption; lia. }
      destruct fa as [|fa'].
      + cbn in Dx. destruct (s_kind st x) eqn:Kx; [|destruct Dx].
        destruct fb as [|fb'].
        * cbn in Dy. destruct (s_kind st y) eqn:Ky; [|destruct Dy].
          destruct (top_top x y Hx Hy Hne Kx Ky); unfold dich; tauto.
        * cbn in Dy. destruct (s_kind st y) as [|hy jy oy] eqn:Ky.
          -- destruct (top_top x y Hx Hy Hne Kx Ky); unfold dich; tauto.
          -- apply dich_sym. apply (STEP fb' 0%nat y x hy jy oy); try assumption; [lia | exact (depth_top 0 x Kx) | exact (fun E => Hne (eq_sym E))].
      + cbn in Dx. destruct (s_kind st x) as [|hm j o] eqn:Kx.
        * destruct fb as [|fb'].
          -- cbn in Dy. destruct (s_kind st y) eqn:Ky; [|destruct Dy].
             destruct (top_top x y Hx Hy Hne Kx Ky); unfold dich; tauto.
          -- cbn in Dy. destruct (s_kind st y) as [|hy jy oy] eqn:Ky.
             ++ destruct (top_top x y Hx Hy Hne Kx Ky); unfold dich; tauto.
             ++ apply dich_sym. apply (STEP fb' 0%nat y x hy jy oy); try assumption; [lia | exact (depth_top 0 x Kx) | exact (fun E => Hne (eq_sym E))].
        * apply (STEP fa' fb x y hm j o); try assumption. lia.
  Qed.

  Theorem span_dich : forall x y, is_group st x -> is_group st y -> x <> y -> dich x y.
  Proof using HWF L RN.
    intros x y Hx Hy Hne. apply (dich_main 16 8 8 x y); try assumption; [cbn; lia | |].
    - exact (wg_depth st L x (WG x Hx)).
    - exact (wg_depth st L y (WG y Hy)).
  Qed.

  (* [comment removed for export] *)
  Lemma garbage_in_slot : forall x k a, is_group st x -> garbage st x k a ->
    0 <= k <= g_lastidx st x /\ g_slot_start st x k - 3 <= a < g_slot_end st x k.
  Proof using HWF L RN.
    intros x k a Hx G. pose proof (str16 x Hx) as S16.
    unfold garbage in G. destruct G as [Hk G]. split; [exact Hk|].
    pose proof (wg_slots st L x (WG x Hx) k Hk) as SW. pose proof (Ess x k) as Ek. pose proof (Ese x k) as EEk.
    destruct (s_slot st x k) as [| |q n o r|c o|o] eqn:Sk; try lia; cbn [slot_wf] in SW.
    - destruct SW as (A1 & A2 & A3 & A4 & A5 & _). unfold IB in A4. destruct G as [G|[G|G]]; lia.
    - destruct SW as (Ho & Hc & _ & Kc & _).
      destruct (nest_facts c x k o Hc Kc) as (_ & _ & _ & _ & _ & Emc & Spc & _ & _).
      pose proof (gspan_gt st L HWF c Hc). destruct G as [G|G]; lia.
    - destruct SW as (A1 & A2 & _). unfold IB in A2. destruct G as [G|G]; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem garbage_private : forall x k m i a, is_group st x -> is_group st m -> garbage st x k a ->
    0 <= i <= g_lastidx st m -> (forall c o, s_slot st m i <> SHost c o) -> (x <> m \/ k <> i) ->
    g_slot_start st m i - 3 <= a < g_slot_end st m i + 1 -> False.
  Proof using HWF L RN.
    intros x k m i a Hx Hm G Hi NH NE Ra.
    destruct (garbage_in_slot x k a Hx G) as (Hk & GK1 & GK2).
    destruct (slot_in_span m i Hm Hi) as [SI1 SI2]. destruct (slot_in_span x k Hx Hk) as [GS1 GS2].
    destruct (Z.eq_dec x m) as [->|Hxm].
    - destruct NE as [NE|NE]; [exact (NE eq_refl)|].
      destruct (Z.lt_ge_cases k i) as [LT|GE].
      + pose proof (slots_apart m k i Hm ltac:(lia) LT). lia.
      + pose proof (slots_apart m i k Hm ltac:(lia) ltac:(lia)). lia.
    - destruct (span_dich x m Hx Hm Hxm) as [A|[A|[A|A]]].
      + lia.
      + lia.
      + destruct A as (k' & c & o & Hk' & Sk' & Hc & Kc & C1 & C2).
        destruct (nest_facts c x k' o Hc Kc) as (_ & _ & _ & _ & Ho & Emc & Spc & _ & _).
        destruct (Z.eq_dec k' k) as [->|Hkk].
        * unfold garbage in G. rewrite Sk' in G. destruct G as [_ [G|G]]; lia.
        * destruct (Z.lt_ge_cases k k') as [LT|GE].
          -- pose proof (slots_apart x k k' Hx ltac:(lia) LT). lia.
          -- pose proof (slots_apart x k' k Hx ltac:(lia) ltac:(lia)). lia.
      + destruct A as (k' & c & o & Hk' & Sk' & Hc & Kc & C1 & C2).
        destruct (Z.eq_dec k' i) as [->|Hki]; [exact (NH c o Sk')|].
        destruct (nest_facts c m k' o Hc Kc) as (_ & _ & _ & _ & Ho & Emc & Spc & _ & _).
        destruct (Z.lt_ge_cases i k') as [LT|GE].
        * pose proof (slots_apart m i k' Hm ltac:(lia) LT). lia.
        * pose proof (slots_apart m k' i Hm ltac:(lia) ltac:(lia)). lia.
  Qed.
End Nest2.
