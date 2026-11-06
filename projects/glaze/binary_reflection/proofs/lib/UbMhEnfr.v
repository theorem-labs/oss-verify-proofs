(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhScrib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhScrib.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zlia ::= zlia_nd. #[local] Ltac znia ::= znia_nd.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Enfr.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Variables (m i n off : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SJunk 0.
  #[local] Notation stride := (g_stride st m).
  #[local] Notation start := (g_slot_start st m i).
  Hypothesis Hn : 0 <= n /\ n + 4 <= stride.
  Hypothesis Hsn : stride - n < 2 ^ 31.
  Hypothesis POST : enframe_post M' i n stride start off.
  Hypothesis HMfr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> start - 3 <= a < start + stride - 4.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis H63 : g_sc st m = 63 -> forall b len, In (RG b len (RGroup m)) (s_regions st) -> len <= n + 4116.
  Hypothesis HLlen : Z.of_nat (length L) + 1 <= LMAX.
  (* [comment removed for export] *)
  Hypothesis HX : g_sc st m < 48 -> s_kind st m = GTop -> g_lastidx st m = 0 -> size_class (g_sc st m) <= 255 ->
                  stride - 4 - n < 16 * size_class (g_sc st m).

  Definition p : Z := start + 16 * off.
  Definition res : Z := stride - 4 - n - 16 * off.
  Definition st' : mst := set_slot st m i (SUser p n off res).
  Definition L' : list (Z * Z) := (p, n) :: L.

  Lemma t_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) m Hgrp). Qed.
  Lemma t_str : 16 <= stride /\ stride mod 16 = 0. Proof using Hgrp HWF L RN. exact (wg_stride st L m t_wfg). Qed.
  Lemma t_mem : 0 < g_mem st m /\ g_mem st m mod 16 = 0 /\ g_mem st m + UNIT + stride * g_cnt st m < 2 ^ 47.
  Proof using Hgrp HWF L RN. exact (wg_mem st L m t_wfg). Qed.
  Lemma t_last : 0 <= g_lastidx st m < 32. Proof using. exact (glast_rng st m). Qed.
  Lemma t_post : 0 <= res /\ 0 <= off <= 255 /\ 0 <= stride * i / 16 + off < 65536.
  Proof using POST M'. pose proof (Pr _ _ _ _ _ _ POST) as X. unfold res. exact X. Qed.
  Lemma Ess : start = g_mem st m + 16 + stride * i. Proof using. unfold g_slot_start, UNIT. reflexivity. Qed.
  Lemma Ese : g_slot_end st m i = start + stride - 4. Proof using. unfold g_slot_end, IB. reflexivity. Qed.
  Lemma t_rng : HEAPLO + 16 <= start /\ start + stride - 4 < gspan st m /\ gspan st m <= CEIL /\ 0 <= stride * i.
  Proof using Hi Hgrp HWF L.
    pose proof t_str as [S16 _]. pose proof t_last. destruct (group_range st L HWF m Hgrp) as [R1 R2].
    assert (0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
    assert (stride * (i + 1) <= stride * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    unfold gspan, g_span_end, g_slot_start, UNIT, IB in *. lia.
  Qed.
  Lemma p_rng : start <= p /\ p + n + res = start + stride - 4 /\ 0 <= res.
  Proof using POST M' L. pose proof t_post as X. unfold p, res in *. lia. Qed.

  Lemma e_slot : forall x k, s_slot st' x k = if (Z.eqb x m && Z.eqb k i)%bool then SUser p n off res else s_slot st x k.
  Proof using. intros. reflexivity. Qed.
  Lemma e_slot_mi : s_slot st' m i = SUser p n off res.
  Proof using. rewrite e_slot, !Z.eqb_refl. reflexivity. Qed.
  Lemma e_slot_other : forall x k, (x <> m \/ k <> i) -> s_slot st' x k = s_slot st x k.
  Proof using L. intros x k H. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn; try reflexivity. exfalso; lia. Qed.

  (* [comment removed for export] *)
  Lemma junk_garbage : forall a, start <= a < start + stride - 4 -> garbage st m i a.
  Proof using Hslot Hi L. intros a Ha. unfold garbage. rewrite Hslot. split; [exact Hi|]. right. rewrite Ese. lia. Qed.
  Lemma junk_hdr_cell : forall a, start - 4 <= a < start -> gcell st m a.
  Proof using Hslot Hi L.
    intros a Ha. unfold gcell. destruct (Z.eq_dec a (start - 4)) as [->|NE].
    - right; left. exists i. split; [unfold g_cnt; lia|]. split; [reflexivity|]. left. unfold g_cnt. lia.
    - right; right; left. exists i, (start + 16 * 0). unfold slot_ptr. rewrite Hslot. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_other_cell : forall x a, is_group st x -> x <> m -> gcell st x a -> start - 3 <= a < start + stride - 4 -> False.
  Proof using Hslot Hi Hgrp HWF L RN.
    intros x a Hx Hne G Ha. destruct (Z_lt_le_dec a start) as [LO|HI].
    - exact (ge_cells st (WF_geom st L HWF) m x a Hgrp Hx (fun E => Hne (eq_sym E)) (junk_hdr_cell a ltac:(lia)) G).
    - exact (ge_garb_cell st (WF_geom st L HWF) m i a x Hgrp (junk_garbage a ltac:(lia)) Hx G).
  Qed.
  Lemma frame_own_cell : forall a, gcell st m a -> start - 3 <= a < start + stride - 4 -> start - 3 <= a < start.
  Proof using Hslot Hi Hgrp HWF L RN.
    intros a G Ha. destruct (Z_lt_le_dec a start) as [LO|HI]; [lia|].
    exfalso. exact (ge_garb_cell st (WF_geom st L HWF) m i a m Hgrp (junk_garbage a ltac:(lia)) Hgrp G).
  Qed.
  Lemma frame_app : forall a, appb st a -> start - 3 <= a < start + stride - 4 -> False.
  Proof using Hslot Hi Hgrp HWF L RN.
    intros a Ap Ha. destruct (Z_lt_le_dec a start) as [LO|HI].
    - exact (ge_app_cell st (WF_geom st L HWF) m a Hgrp (junk_hdr_cell a ltac:(lia)) Ap).
    - exact (ge_garb_app st (WF_geom st L HWF) m i a Hgrp (junk_garbage a ltac:(lia)) Ap).
  Qed.
  Lemma frame_area : forall a, areab st a -> start - 3 <= a < start + stride - 4 -> False.
  Proof using Hi Hgrp HWF L RN.
    intros a Ar Ha. pose proof t_rng as (R1 & R2 & R3 & R4).
    apply (ge_area st (WF_geom st L HWF) m a Hgrp); [|exact Ar]. unfold gspan, g_span_end, g_slot_start, UNIT, IB in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma p_unique : forall x k q n2 o2 r2, is_group st x -> 0 <= k <= g_lastidx st x -> s_slot st x k = SUser q n2 o2 r2 -> q <> p.
  Proof using POST Hn Hslot Hi Hgrp HWF n M' L RN.
    intros x k q n2 o2 r2 Hx Hk Hs ->.
    pose proof (wg_slots st L x (wG_each st L (WF_groups st L HWF) x Hx) k Hk) as SW. rewrite Hs in SW. cbn [slot_wf] in SW.
    destruct SW as (A1 & A2 & A3 & A4 & A5 & A6 & A7). pose proof t_post as (_ & O & _).
    (* [comment removed for export] *)
    assert (Gx : gcell st x (p - 1)).
    { unfold gcell. right; right; left. exists k, p. unfold slot_ptr. rewrite Hs. repeat split; try lia. }
    destruct (Z.eq_dec off 0) as [E0|NE0].
    - assert (Ep : p = start) by (unfold p; lia).
      destruct (Z.eq_dec x m) as [->|Hxm].
      + (* [comment removed for export] *)
        destruct (Z.eq_dec k i) as [->|Hki]; [rewrite Hslot in Hs; discriminate Hs|].
        pose proof t_str as [S16 _]. rewrite Ep, Ess in A3.
        assert (16 * o2 <= g_stride st m - 4 - n2) by (unfold IB in A4; lia).
        destruct (Z.lt_ge_cases k i).
        * assert (g_stride st m * (k + 1) <= g_stride st m * i) by (apply Z.mul_le_mono_nonneg_l; lia).
          unfold g_slot_start, UNIT in A3. lia.
        * assert (g_stride st m * (i + 1) <= g_stride st m * k) by (apply Z.mul_le_mono_nonneg_l; lia).
          unfold g_slot_start, UNIT in A3. lia.
      + exact (ge_cells st (WF_geom st L HWF) m x (p - 1) Hgrp Hx (fun E => Hxm (eq_sym E)) (junk_hdr_cell (p - 1) ltac:(rewrite Ep; lia)) Gx).
    - pose proof p_rng as (P1 & P2 & P3).
      assert (GB : garbage st m i (p - 1)) by (apply junk_garbage; unfold p in *; lia).
      exact (ge_garb_cell st (WF_geom st L HWF) m i (p - 1) x Hgrp GB Hx Gx).
  Qed.

  Lemma p_notin_L : ~ In (p, n) L.
  Proof using POST Hn Hslot Hi Hgrp HWF M' RN.
    intros Hin. destruct (wL_in st L (WF_live st L HWF) p n Hin) as (x & k & o2 & r2 & Hx & Hk & Hs).
    exact (p_unique x k p n o2 r2 Hx Hk Hs eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_slot_ptr_other : forall x k, (x <> m \/ k <> i) -> slot_ptr st' x k = slot_ptr st x k.
  Proof using L. intros x k H. unfold slot_ptr. change (g_slot_start st' x k) with (g_slot_start st x k). rewrite e_slot_other by exact H. reflexivity. Qed.
  Lemma e_slot_ptr_mi : slot_ptr st' m i = Some p.
  Proof using. unfold slot_ptr. rewrite e_slot_mi. reflexivity. Qed.
  Lemma o_slot_ptr_mi : slot_ptr st m i = Some start.
  Proof using Hslot L. unfold slot_ptr. rewrite Hslot. f_equal. lia. Qed.

  Lemma t_gcell_back : forall x a, gcell st' x a -> gcell st x a \/ (x = m /\ start - 3 <= a < start + stride - 4 /\ ~ (p <= a < p + n)).
  Proof using POST Hn Hslot M' L.
    intros x a G. pose proof p_rng as (P1 & P2 & P3). unfold gcell in G |- *.
    change (g_mem st' x) with (g_mem st x) in G. change (g_cnt st' x) with (g_cnt st x) in G. change (g_lastidx st' x) with (g_lastidx st x) in G.
    destruct G as [G | [G | [G | G]]].
    - left. left. exact G.
    - left. right. left. exact G.
    - destruct G as (k & q & Hk & Hq & Ha).
      destruct (decide (x = m /\ k = i)) as [[-> ->]|NE].
      + rewrite e_slot_ptr_mi in Hq. injection Hq. intros <-.
        destruct (Z.eq_dec off 0) as [E0|NE0].
        * left. right; right; left. exists i, start. split; [exact Hk|]. split; [exact o_slot_ptr_mi | unfold p in Ha; lia].
        * right. split; [reflexivity|]. unfold p in *. lia.
      + left. right; right; left. exists k, q. rewrite e_slot_ptr_other in Hq by lia. repeat split; try assumption; lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). change (g_slot_end st' x k) with (g_slot_end st x k) in Ha.
      rewrite e_slot in Hs. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hs.
      + injection Hs. intros <- <- <- <-. subst. right. split; [reflexivity|]. rewrite Ese in Ha. lia.
      + left. right; right; right. exists k, q, n2, o2, r2. repeat split; try assumption; lia.
      + left. right; right; right. exists k, q, n2, o2, r2. repeat split; try assumption; lia.
      + left. right; right; right. exists k, q, n2, o2, r2. repeat split; try assumption; lia.
  Qed.


  Lemma t_appb_back : forall a, appb st' a -> appb st a \/ p <= a < p + n.
  Proof using L.
    intros a (x & k & q & n2 & o2 & r2 & Hx & Hk & Hs & Ha).
    change (g_lastidx st' x) with (g_lastidx st x) in Hk. change (is_group st x) in Hx.
    rewrite e_slot in Hs. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hs.
    - injection Hs. intros; subst. right. exact Ha.
    - left. exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
    - left. exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
    - left. exists x, k, q, n2, o2, r2. repeat split; try assumption; lia.
  Qed.


  Lemma t_garbage_back : forall x k a, garbage st' x k a -> garbage st x k a \/ (x = m /\ k = i /\ start - 3 <= a < start).
  Proof using POST Hn Hslot Hi M' L.
    intros x k a [Hk G]. pose proof p_rng as (P1 & P2 & P3). unfold garbage.
    change (g_lastidx st' x) with (g_lastidx st x) in Hk.
    change (g_slot_start st' x k) with (g_slot_start st x k) in G. change (g_slot_end st' x k) with (g_slot_end st x k) in G.
    rewrite e_slot in G. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in G.
    - subst. rewrite Hslot. rewrite Ese in G. destruct (Z_lt_le_dec a start) as [LO|HI]; [right; repeat split; lia | left]. split; [exact Hi|]. right. rewrite Ese. lia.
    - left. split; [exact Hk|]. destruct (s_slot st x k); exact G.
    - left. split; [exact Hk|]. destruct (s_slot st x k); exact G.
    - left. split; [exact Hk|]. destruct (s_slot st x k); exact G.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma e_inband : inband st m p = stride * i / 16 + off.
  Proof using Hgrp HWF L RN.
    pose proof t_str as [S16 Smod].
    unfold inband, p. rewrite Ess. unfold UNIT. replace (g_mem st m + 16 + stride * i + 16 * off - g_mem st m - 16) with (off * 16 + stride * i) by lia.
    rewrite Z.div_add_l by lia. lia.
  Qed.

  Lemma t_ptr_ok : ptr_ok st m i p.
  Proof using HX POST Hn Hi Hgrp HWF n M' L RN.
    pose proof t_str as [S16 Smod]. pose proof t_mem as (M1 & M2 & M3). pose proof t_post as (P1 & P2 & P3). pose proof t_rng as (R1 & R2 & R3 & R4).
    pose proof t_wfg as WG. pose proof e_inband as EI.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Dm : stride * i mod 16 = 0) by (rewrite Z.mul_mod, Smod by lia; reflexivity).
    unfold ptr_ok. rewrite EI. unfold p. rewrite Ess. unfold UNIT. split; [|split; [lia | split; [|split; [lia | split]]]].
    - clear - M2 Dm P2. lia.
    - clear - M2 Dm P2. lia.
    - intros Hsc. (* [comment removed for export] *)
      assert (SCR : 0 <= g_sc st m) by (unfold g_sc, w_sizeclass; apply Z.mod_pos_bound; lia).
      pose proof (size_class_pos (g_sc st m) ltac:(lia)) as [SC1 SC2].
      assert (O16 : 16 * off <= stride - 4 - n) by (pose proof P1 as P1'; unfold res in P1'; lia).
      assert (ES : (g_maplen st m <> 0 /\ g_lastidx st m = 0 /\ stride = g_maplen st m * 4096 - UNIT) \/ stride = UNIT * size_class (g_sc st m)).
      { unfold g_stride, slot_stride. destruct (negb (g_maplen st m =? 0) && (g_lastidx st m =? 0))%bool eqn:B.
        - left. apply Bool.andb_true_iff in B. destruct B as [B1 B2]. apply Bool.negb_true_iff in B1. apply Z.eqb_neq in B1. apply Z.eqb_eq in B2.
          split; [exact B1 | split; [exact B2 | reflexivity]].
        - right. reflexivity. }
      destruct ES as [(ML & L0 & ES)|ES].
      + assert (I0 : i = 0) by lia.
        assert (E0 : stride * i / 16 = 0) by (rewrite I0, Z.mul_0_r; reflexivity). rewrite E0.
        assert (KT : s_kind st m = GTop).
        { pose proof (wg_kind st L m WG) as KD. destruct (s_kind st m) as [|hm j ho]; [reflexivity|]. destruct KD as (K1 & _). exfalso. exact (ML K1). }
        destruct (Z_lt_le_dec 255 (size_class (g_sc st m))) as [BIG|SMALL]; [nia|].
        pose proof (HX Hsc KT L0 SMALL). nia.
      + rewrite ES. unfold UNIT. replace (16 * size_class (g_sc st m) * i) with (size_class (g_sc st m) * i * 16) by lia.
        rewrite Z.div_mul by lia. unfold UNIT in *. rewrite ES in O16. nia.
    - intros Hml. (* [comment removed for export] *)
      pose proof (wg_kind st L m WG) as KD. destruct (s_kind st m) as [|hm j ho] eqn:K.
      + destruct KD as (K1 & K2 & K3 & K4). unfold UNIT in K4.
        assert (stride * (i + 1) <= stride * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
        assert (16 * ((stride * i) / 16) <= stride * i) by (apply Z.mul_div_le; lia).
        unfold res in P1. clear - H0 P1 H K4 K1 Hn.
        lia.
      + destruct KD as (K1 & _). lia.
  Qed.

  Lemma t_slot_wf_mi : slot_wf st' L' m i (SUser p n off res).
  Proof using HX POST Hsn Hn Hi Hgrp HWF M' RN.
    pose proof t_post as (P1 & P2 & P3). cbn [slot_wf].
    change (g_slot_start st' m i) with start. change (g_stride st' m) with stride.
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [unfold res, IB; lia|]. split; [unfold res in *; lia|].
    split; [exact t_ptr_ok | left; reflexivity].
  Qed.

  Lemma t_slot_wf_other : forall x k sl, is_group st x -> slot_wf st L x k sl -> slot_wf st' L' x k sl.
  Proof using.
    intros x k sl Hx SW. destruct sl as [| |q n2 o2 r2|c o2|o2]; cbn [slot_wf] in *; try exact I; try exact SW.
    destruct SW as (A & B & C & D & E & F & G). repeat (split; [assumption|]). right. exact G.
  Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L' x.
  Proof using HX POST Hsn Hn Hslot Hi Hgrp HWF M' RN.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; try assumption.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (Av k Hk).
      subst. rewrite (Av i ltac:(lia)), Hslot. split; intros [A B]; split; try assumption; discriminate B.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (Fr k Hk).
      subst. rewrite (Fr i ltac:(lia)), Hslot. split; intros [A B]; split; try assumption; discriminate B.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool; [intros E; discriminate E | exact (Avai k Hk)].
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb]; try exact (High k Hk).
      subst. pose proof (High i Hk) as E. rewrite Hslot in E. discriminate E.
    - intros Hall. apply Full. intros k Hk. specialize (Hall k Hk). rewrite e_slot in Hall.
      destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hall; try exact Hall.
      subst. rewrite Hslot. split; intros E; discriminate E.
    - change (s_kind st' x) with (s_kind st x). destruct (s_kind st x) as [|hm j hoff]; [exact Kind|].
      destruct Kind as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
      repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); assumption].
      rewrite e_slot_other; [exact K6|].
      destruct (Z.eq_dec hm m) as [->|]; [right | left; assumption]. intros ->. rewrite Hslot in K6. discriminate K6.
    - intros Hall. apply FF. intros k Hk. specialize (Hall k Hk). rewrite e_slot in Hall.
      destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb] in Hall; try exact Hall.
      destruct Hall as [E|E]; discriminate E.
    - intros k Hk. rewrite e_slot. destruct (Z.eqb_spec x m); destruct (Z.eqb_spec k i); cbn [andb].
      + subst. exact t_slot_wf_mi.
      + apply t_slot_wf_other; [exact Hx | exact (Slots k Hk)].
      + apply t_slot_wf_other; [exact Hx | exact (Slots k Hk)].
      + apply t_slot_wf_other; [exact Hx | exact (Slots k Hk)].
    - intros Hsc Hst k Hk. rewrite e_slot. destruct (Z.eqb x m && Z.eqb k i)%bool; [split; intros E; discriminate E | exact (Fit Hsc Hst k Hk)].
  Qed.

  #[local] Notation stF := (UbMhScrib.stF st m i).

  (* [comment removed for export] *)
  Lemma f_out : forall a, gcell stF m a -> ~ (start - 3 <= a < start + stride - 4).
  Proof using Hslot Hi Hgrp HWF L RN.
    intros a G Ha. pose proof t_str as [S16 Smod]. pose proof t_mem as (M1 & M2 & M3). pose proof t_last.
    destruct (UbMhScrib.f_gcell_where st L m i 0 HWF Hgrp Hi Hslot a G) as [W | [(k & Hk & Hak) | (k & Hk & Hki & Hak)]].
    - rewrite Ess in Ha. pose proof t_rng as (_ & _ & _ & R4). lia.
    - rewrite Ess in Ha. unfold g_slot_start, UNIT in Hak.
      destruct (Z.lt_ge_cases k (i + 1)).
      + assert (g_stride st m * k <= g_stride st m * i) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
      + assert (g_stride st m * (i + 1) <= g_stride st m * k) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
    - destruct (Z.lt_ge_cases k i) as [Hl|Hg].
      + pose proof (slots_apart st L HWF m k i Hgrp ltac:(lia) Hl). lia.
      + pose proof (slots_apart st L HWF m i k Hgrp ltac:(lia) ltac:(lia)). rewrite Ese in *. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma t_gcell_split : forall a, gcell st' m a ->
    gcell stF m a \/ (p - 4 <= a < p) \/ (0 < res /\ a = p + n) \/ (5 <= res /\ g_slot_end st m i - 5 <= a < g_slot_end st m i).
  Proof using L.
    intros a G. unfold gcell in G |- *.
    destruct G as [G|[G|[G|G]]].
    - left. left. exact G.
    - left. right. left. destruct G as (k & Hk & Ha & E). exists k. split; [exact Hk|]. split; [exact Ha|].
      destruct E as [E|E]; [left; exact E | right; exact E].
    - destruct G as (k & q & Hk & Hq & Ha). destruct (Z.eq_dec k i) as [->|Hki].
      + rewrite e_slot_ptr_mi in Hq. injection Hq. intros <-. right; left. exact Ha.
      + left. right; right; left. exists k, q. split; [exact Hk|]. split; [|exact Ha].
        rewrite e_slot_ptr_other in Hq by (right; exact Hki). unfold slot_ptr, UbMhScrib.stF in *.
        rewrite s_slot_set_slot, Z.eqb_refl, (proj2 (Z.eqb_neq k i) Hki). cbn [andb]. exact Hq.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). rewrite e_slot, Z.eqb_refl in Hs. cbn [andb] in Hs.
      destruct (Z.eqb_spec k i) as [->|Hki].
      + injection Hs. intros E4 E3 E2 E1. subst q n2 o2 r2. right; right.
        change (g_slot_end st' m i) with (g_slot_end st m i) in Ha. exact Ha.
      + left. right; right; right. exists k, q, n2, o2, r2. split; [exact Hk|]. split; [|exact Ha].
        unfold UbMhScrib.stF. rewrite s_slot_set_slot, Z.eqb_refl, (proj2 (Z.eqb_neq k i) Hki). cbn [andb]. exact Hs.
  Qed.

  (* [comment removed for export] *)
  Lemma new_garb_no_cell : forall a, garbage st' m i a -> start - 3 <= a < start -> gcell st' m a -> False.
  Proof using POST Hn Hslot Hi Hgrp HWF M' L RN.
    intros a G Ra C. pose proof p_rng as (P1 & P2 & P3). pose proof t_str as [S16 _].
    assert (A4 : a < p - 4).
    { unfold garbage in G. rewrite e_slot_mi in G. change (g_slot_start st' m i) with start in G.
      change (g_slot_end st' m i) with (g_slot_end st m i) in G. destruct G as [_ [G|[G|G]]]; lia. }
    destruct (t_gcell_split a C) as [F|[H|[H|H]]].
    - exact (f_out a F ltac:(lia)).
    - lia.
    - lia.
    - rewrite Ese in H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma old_user_apart : forall x k q nq o r, is_group st x -> 0 <= k <= g_lastidx st x ->
    s_slot st x k = SUser q nq o r -> q + nq <= p \/ p + n <= q.
  Proof using POST Hn Hslot Hi Hgrp HWF M' L RN.
    intros x k q nq o r Hx Hk Hs. pose proof p_rng as (P1 & P2 & P3).
    destruct (Z_lt_le_dec p (q + nq)) as [A|A]; [|left; lia].
    destruct (Z_lt_le_dec q (p + n)) as [B|B]; [|right; lia].
    exfalso. pose proof (p_unique x k q nq o r Hx Hk Hs) as NE.
    destruct (Z_lt_le_dec q p) as [C|C].
    - apply (frame_app (p - 1)); [exists x, k, q, nq, o, r; repeat split; try assumption; lia | unfold p in *; lia].
    - assert (Gx : gcell st x (q - 1)) by (unfold gcell; right; right; left; exists k, q; unfold slot_ptr; rewrite Hs; repeat split; lia).
      destruct (Z.eq_dec x m) as [->|Hxm].
      + pose proof (frame_own_cell (q - 1) Gx ltac:(unfold p in *; lia)). unfold p in *. lia.
      + exact (frame_other_cell x (q - 1) Hx Hxm Gx ltac:(unfold p in *; lia)).
  Qed.

  Lemma L_apart : forall b k, In (b, k) L -> p + n <= b \/ b + k <= p.
  Proof using POST Hn Hslot Hi Hgrp HWF M' RN.
    intros b k Hin. destruct (wL_in st L (WF_live st L HWF) b k Hin) as (x & j & o2 & r2 & Hx & Hj & Hs).
    destruct (old_user_apart x j b k o2 r2 Hx Hj Hs); [right | left]; assumption.
  Qed.

  Lemma t_wf_geom : wf_geom st'.
  Proof using HMfr POST Hn Hslot Hi Hgrp HWF M' M L RN.
    pose proof p_rng as (P1 & P2 & P3). pose proof t_rng as (R1 & R2 & R3 & R4).
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN].
    constructor; try assumption.
    - (* [comment removed for export] *)
      intros m1 m2 a H1 H2 Hne G1 G2.
      destruct (t_gcell_back m1 a G1) as [G1'|(-> & Ra1 & _)]; destruct (t_gcell_back m2 a G2) as [G2'|(-> & Ra2 & _)].
      + exact (CELLS m1 m2 a H1 H2 Hne G1' G2').
      + exact (frame_other_cell m1 a H1 Hne G1' Ra2).
      + exact (frame_other_cell m2 a H2 (fun E => Hne (eq_sym E)) G2' Ra1).
      + exact (Hne eq_refl).
    - (* [comment removed for export] *)
      intros x a Hx G Ap. destruct (t_appb_back a Ap) as [Ap'|Pa]; destruct (t_gcell_back x a G) as [G'|(-> & Ra & NP)].
      + exact (APC x a Hx G' Ap').
      + exact (frame_app a Ap' Ra).
      + destruct (Z.eq_dec x m) as [->|Hne].
        * destruct (frame_own_cell a G' ltac:(lia)). unfold p in Pa. pose proof t_post. lia.
        * exact (frame_other_cell x a Hx Hne G' ltac:(lia)).
      + exact (NP Pa).
    - intros a Ap Ar. destruct (t_appb_back a Ap) as [Ap'|Pa]; [exact (APA a Ap' Ar) | exact (frame_area a Ar ltac:(lia))].
    - (* [comment removed for export] *)
      intros m1 k1 m2 k2 p1 n1 o1 r1 p2 n2 o2 r2 H1 H2 Hk1 Hk2 S1 S2 Hne.
      change (g_lastidx st' m1) with (g_lastidx st m1) in Hk1. change (g_lastidx st' m2) with (g_lastidx st m2) in Hk2.
      rewrite e_slot in S1, S2.
      pose proof old_user_apart as OLD.
      destruct (Z.eqb_spec m1 m); destruct (Z.eqb_spec k1 i); destruct (Z.eqb_spec m2 m); destruct (Z.eqb_spec k2 i); cbn [andb] in S1, S2;
        try (injection S1; intros <- <- <- <-); try (injection S2; intros <- <- <- <-); subst; try (exfalso; exact (Hne eq_refl)).
      all: try exact (APD _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hk1 Hk2 S1 S2 Hne).
      all: try (destruct (OLD _ _ _ _ _ _ H2 Hk2 S2); [right | left]; lia).
      all: try (destruct (OLD _ _ _ _ _ _ H1 Hk1 S1); [left | right]; lia).
    - (* [comment removed for export] *)
      intros x k a x2 Hx G H2 C.
      destruct (t_garbage_back x k a G) as [G'|(-> & -> & Ra)]; destruct (t_gcell_back x2 a C) as [C'|(-> & Rc & NP)].
      + exact (GC x k a x2 Hx G' H2 C').
      + (* [comment removed for export] *)
        destruct (Z_lt_le_dec a start) as [LO|HI].
        * exact (GC x k a m Hx G' Hgrp (junk_hdr_cell a ltac:(lia))).
        * (* [comment removed for export] *)
          pose proof (junk_garbage a ltac:(lia)) as Gm.
          (* [comment removed for export] *)
          destruct (Z.eq_dec x m) as [->|NEx]; [destruct (Z.eq_dec k i) as [->|NEk]|].
          -- (* [comment removed for export] *)
             unfold garbage in G. rewrite e_slot_mi in G. change (g_slot_start st' m i) with start in G. change (g_slot_end st' m i) with (g_slot_end st m i) in G.
             rewrite Ese in G. destruct G as [_ G].
             unfold gcell in C. change (g_mem st' m) with (g_mem st m) in C. change (g_cnt st' m) with (g_cnt st m) in C. change (g_lastidx st' m) with (g_lastidx st m) in C.
             destruct C as [C|[C|[C|C]]].
             ++ pose proof t_mem. rewrite Ess in *. lia.
             ++ destruct C as (k2 & Hk2 & Ea & _). change (g_slot_start st' m k2) with (g_slot_start st m k2) in Ea.
                pose proof t_str as [S16 _].
                destruct (Z.lt_ge_cases k2 (i + 1)); [destruct (Z.lt_ge_cases k2 i)|].
                ** assert (g_stride st m * (k2 + 1) <= g_stride st m * i) by (apply Z.mul_le_mono_nonneg_l; lia). unfold g_slot_start, UNIT in *. lia.
                ** assert (k2 = i) by lia. subst k2. unfold g_slot_start, UNIT in *. lia.
                ** assert (g_stride st m * (i + 1) <= g_stride st m * k2) by (apply Z.mul_le_mono_nonneg_l; lia). unfold g_slot_start, UNIT in *. lia.
             ++ destruct C as (k2 & q & Hk2 & Hq & Ha2).
                destruct (Z.eq_dec k2 i) as [->|Hk2i].
                ** rewrite e_slot_ptr_mi in Hq. injection Hq. intros <-. unfold p in *. lia.
                ** rewrite e_slot_ptr_other in Hq by lia.
                   assert (Gx : gcell st m a) by (unfold gcell; right; right; left; exists k2, q; split; [exact Hk2 | split; [exact Hq | exact Ha2]]).
                   exact (ge_garb_cell st (WF_geom st L HWF) m i a m Hgrp Gm Hgrp Gx).
             ++ destruct C as (k2 & q & n2 & o2 & r2 & Hk2 & Hs & Ha2). change (g_slot_end st' m k2) with (g_slot_end st m k2) in Ha2.
                rewrite e_slot in Hs. rewrite Z.eqb_refl in Hs. cbn [andb] in Hs. destruct (Z.eqb_spec k2 i).
                ** injection Hs. intros <- <- <- <-. subst. rewrite Ese in Ha2. unfold p, res in *. lia.
                ** assert (Gx : gcell st m a) by (unfold gcell; right; right; right; exists k2, q, n2, o2, r2; split; [exact Hk2 | split; [exact Hs | exact Ha2]]).
                   exact (ge_garb_cell st (WF_geom st L HWF) m i a m Hgrp Gm Hgrp Gx).
          -- exfalso. apply (garbage_private st L HWF m k m i a Hgrp Hgrp G' Hi); [intros c o E; rewrite Hslot in E; discriminate E | right; exact NEk | rewrite Ese; lia].
          -- exfalso. apply (garbage_private st L HWF x k m i a Hx Hgrp G' Hi); [intros c o E; rewrite Hslot in E; discriminate E | left; exact NEx | rewrite Ese; lia].
      + destruct (Z.eq_dec x2 m) as [->|NE2].
        * exact (new_garb_no_cell a G Ra C).
        * exact (CELLS m x2 a Hgrp H2 (fun E => NE2 (eq_sym E)) (junk_hdr_cell a ltac:(lia)) C').
      + exact (new_garb_no_cell a G Ra C).
    - (* [comment removed for export] *)
      intros x k a Hx G Ap. destruct (t_appb_back a Ap) as [Ap'|Pa]; destruct (t_garbage_back x k a G) as [G'|(-> & -> & Ra)].
      + exact (GA x k a Hx G' Ap').
      + exact (frame_app a Ap' ltac:(lia)).
      + (* [comment removed for export] *)
        destruct (Z.eq_dec x m) as [->|NEx]; [destruct (Z.eq_dec k i) as [->|NEk]|].
        * unfold garbage in G. rewrite e_slot_mi in G. change (g_slot_start st' m i) with start in G.
          change (g_slot_end st' m i) with (g_slot_end st m i) in G. rewrite Ese in G. destruct G as [_ G]. unfold p, res in *. lia.
        * exfalso. apply (garbage_private st L HWF m k m i a Hgrp Hgrp G' Hi); [intros c o E; rewrite Hslot in E; discriminate E | right; exact NEk | rewrite Ese; unfold p in *; lia].
        * exfalso. apply (garbage_private st L HWF x k m i a Hx Hgrp G' Hi); [intros c o E; rewrite Hslot in E; discriminate E | left; exact NEx | rewrite Ese; unfold p in *; lia].
      + unfold p in *. pose proof t_post. lia.
    - intros x k a Hx G Ar. destruct (t_garbage_back x k a G) as [G'|(-> & -> & Ra)]; [exact (GAR x k a Hx G' Ar) | exact (frame_area a Ar ltac:(lia))].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_wf_live : wf_live st' L'.
  Proof using HLlen POST Hn Hslot Hi Hgrp HWF M' RN.
    destruct (WF_live st L HWF) as [IN ND FUN LEN].
    constructor.
    - intros q n2 [E|Hin].
      + injection E. intros <- <-. exists m, i, off, res. split; [exact Hgrp|]. split; [exact Hi | exact e_slot_mi].
      + destruct (IN q n2 Hin) as (x & k & o2 & r2 & Hx & Hk & Hs).
        exists x, k, o2, r2. split; [exact Hx|]. split; [exact Hk|]. rewrite e_slot_other; [exact Hs|].
        destruct (Z.eq_dec x m) as [->|]; [right|left; assumption]. intros ->. rewrite Hslot in Hs. discriminate Hs.
    - apply base.NoDup_cons_2; [|exact ND]. intros E. apply p_notin_L. apply (proj1 (base.list_elem_of_In _ _) E).
    - intros m1 i1 m2 i2 q n1 n2 o1 o2 r1 r2 H1 H2 Hk1 Hk2 S1 S2.
      change (g_lastidx st' m1) with (g_lastidx st m1) in Hk1. change (g_lastidx st' m2) with (g_lastidx st m2) in Hk2.
      rewrite e_slot in S1, S2.
      destruct (Z.eqb_spec m1 m); destruct (Z.eqb_spec i1 i); destruct (Z.eqb_spec m2 m); destruct (Z.eqb_spec i2 i); cbn [andb] in S1, S2;
        try (injection S1; intros E1 E2 E3 E4); try (injection S2; intros F1 F2 F3 F4); subst; try (split; reflexivity).
      all: try (exfalso; exact (p_unique _ _ _ _ _ _ H2 Hk2 S2 eq_refl)).
      all: try (exfalso; exact (p_unique _ _ _ _ _ _ H1 Hk1 S1 eq_refl)).
      all: exact (FUN _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hk1 Hk2 S1 S2).
    - unfold L'. cbn [length]. rewrite Nat2Z.inj_succ. pose proof HLlen. lia.
  Qed.

  Lemma t_wf_regions : wf_regions st'.
  Proof using H63 Hslot HWF L.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; try assumption.
    intros b len x Hin Hx63.
    destruct (G63 b len x Hin Hx63) as [(q & n2 & o2 & r2 & Hs & Hlen) | (o2 & Hs)].
    - left. rewrite e_slot. destruct (Z.eqb_spec x m) as [Ex|Nx]; destruct (Z.eqb_spec 0 i) as [Ei|Ni]; cbn [andb].
      + subst x. rewrite Ei, Hslot in Hs. discriminate Hs.
      + exists q, n2, o2, r2. split; assumption.
      + exists q, n2, o2, r2. split; assumption.
      + exists q, n2, o2, r2. split; assumption.
    - rewrite e_slot. destruct (Z.eqb_spec x m) as [Ex|Nx]; destruct (Z.eqb_spec 0 i) as [Ei|Ni]; cbn [andb].
      + left. exists p, n, off, res. split; [reflexivity|]. subst x. exact (H63 Hx63 b len Hin).
      + right. exists o2. exact Hs.
      + right. exists o2. exact Hs.
      + right. exists o2. exact Hs.
  Qed.

  Lemma t_wf_img : wf_img st'.
  Proof using HWF L RN. apply (wf_img_same st L HWF); reflexivity. Qed.

  Lemma t_WF : WF st' L'.
  Proof using HX HLlen H63 HMfr POST Hsn Hn Hslot Hi Hgrp HWF M' M.
    pose proof HWF as W. destruct W as (C & A & Ls & G & Ge & Lv & R).
    split; [destruct C; constructor; assumption|]. split; [destruct A; constructor; assumption|].
    split; [destruct Ls; constructor; assumption|]. split.
    - destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      + intros x Hx. apply t_wf_group. exact Hx.
      + intros m1 m2 H1 H2 F1 F2 E. apply (ONEFF m1 m2 H1 H2); [intros k Hk | intros k Hk | exact E].
        * specialize (F1 k Hk). rewrite e_slot in F1. destruct (Z.eqb m1 m && Z.eqb k i)%bool; [destruct F1 as [F|F]; discriminate F | exact F1].
        * specialize (F2 k Hk). rewrite e_slot in F2. destruct (Z.eqb m2 m && Z.eqb k i)%bool; [destruct F2 as [F|F]; discriminate F | exact F2].
    - split; [exact t_wf_geom|]. split; [exact t_wf_live |]. split; [exact t_wf_regions | exact t_wf_img].
  Qed.

  Lemma e_ledger : forall vm, LEDGER st vm -> LEDGER st' vm.
  Proof using. intros vm [A B C D E]. constructor; assumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma f_agree : forall a, gcell stF m a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Proof using HMfr Hslot Hi Hgrp HWF L RN.
    intros a G. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
    pose proof (gcell_in_span st L HWF m a Hgrp (UbMhScrib.f_gcell_back st m i a G)). destruct (group_range st L HWF m Hgrp).
    exact (f_out a G (HMfr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE)).
  Qed.

  Lemma t_keep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Proof using HMgrow. exact (dkeep_of_grows st M M' HMgrow). Qed.

  Lemma t_agree_low : agree_on (fun a => IMG_LO <= a < IMG_HI) M M'.
  Proof using HMfr Hi Hgrp HWF i m L st RN.
    intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
    pose proof t_rng as (R1 & R2 & _). pose proof (HMfr a Hr NE). pose proof Ess. pose proof t_rng as (_ & _ & _ & R4). cbv beta in Ha. hsep. lia.
  Qed.

  Lemma t_REP : REP st' M'.
  Proof using HX HMgrow HMfr POST Hn Hslot Hi Hgrp HREP HWF M L RN.
    pose proof t_rng as (R1 & R2 & R3 & R4). destruct (group_range st L HWF m Hgrp) as [GR1 GR2].
    pose proof p_rng as (P1 & P2 & P3). pose proof t_post as (Q1 & Q2 & Q3).
    constructor.
    - apply (rep_statics_tr st st' M M' HREP t_keep); [|reflexivity|reflexivity].
      eapply agree_on_mono; [exact t_agree_low|]. intros a Ha. cbv beta in Ha |- *. hsep; unfold CTX, HEAPLO in *. lia.
    - apply (rep_ctx_tr st st' M M' HREP t_keep (fun _ => false) false); try reflexivity.
      + eapply agree_on_mono; [exact t_agree_low|]. intros a (Ha & _). cbv beta. hsep; unfold CTX_END, CTX, HEAPLO in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP t_keep (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        apply (frame_area a); [exists ar; split; [exact Har | exact Ha]|].
        exact (HMfr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE).
      + intros x Ux X. discriminate X.
    - intros x Hx. change (is_group st x) in Hx. destruct (group_range st L HWF x Hx) as [X1 X2].
      pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
      pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
      assert (SPAN : 0 <= g_mem st x /\ g_mem st x + 16 <= g_span_end st x /\ g_span_end st x < 2 ^ 64).
      { assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; pose proof (glast_rng st x); nia).
        hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia. }
      destruct (Z.eq_dec x m) as [->|Hxm].
      + (* [comment removed for export] *)
        assert (RGF : rep_group stF M' m).
        { apply (rep_group_transport st stF M M' m); try reflexivity.
          - intros E; exact E.
          - change (s_kind stF m) with (s_kind st m). change (g_maplen stF m) with (g_maplen st m).
            destruct (s_kind st m); [split; reflexivity | exact I].
          - intros k Hk. unfold UbMhScrib.stF. rewrite s_slot_set_slot, Z.eqb_refl.
            destruct (Z.eqb k i); [right; right; reflexivity | left; reflexivity].
          - exact f_agree.
          - exact HMgrow.
          - exact SPAN.
          - intros a G. apply (gcell_in_span st L HWF m a Hgrp). exact (UbMhScrib.f_gcell_back st m i a G).
          - exact (rp_groups st M HREP m Hgrp). }
        destruct RGF as [F1 F2 F3 F4 F5]. constructor.
        * exact F1.
        * exact F2.
        * intros k Hk Hend. apply F3; [exact Hk | exact Hend].
        * exact F4.
        * intros k Hk. change (g_lastidx st' m) with (g_lastidx st m) in Hk. rewrite e_slot, Z.eqb_refl. cbn [andb].
          destruct (Z.eqb_spec k i) as [->|Hki].
          -- (* [comment removed for export] *)
             cbn [rep_slot]. change (g_slot_end st' m i) with (g_slot_end st m i). rewrite Ese.
             split; [|split].
             ++ constructor.
                ** exact (Pm4 _ _ _ _ _ _ POST).
                ** pose proof (Pm3 _ _ _ _ _ _ POST) as X. unfold p, res. exact X.
                ** change (inband st' m p) with (inband st m p). rewrite e_inband. exact (Pm2 _ _ _ _ _ _ POST).
             ++ intros Hr. pose proof (Pzr _ _ _ _ _ _ POST) as X. unfold p. apply X. unfold res in Hr. exact Hr.
             ++ intros Hr. split.
                ** pose proof (Pe4 _ _ _ _ _ _ POST ltac:(unfold res in Hr; exact Hr)) as X. unfold res.
                   replace (start + stride - 4 - 4) with (start + stride - 4 - 4) by lia. exact X.
                ** exact (Pe5 _ _ _ _ _ _ POST ltac:(unfold res in Hr; exact Hr)).
          -- pose proof (F5 k Hk) as RS. unfold UbMhScrib.stF in RS. rewrite s_slot_set_slot, Z.eqb_refl in RS.
             rewrite (proj2 (Z.eqb_neq k i) Hki) in RS. cbn [andb] in RS.
             destruct (s_slot st m k) as [| |q3 n3 o3 r3|c o3|o3]; cbn [rep_slot] in RS |- *; try exact I.
             ++ destruct RS as ([A B C] & Rz & R5). split; [constructor; [exact A | exact B | exact C]|]. split; [exact Rz | exact R5].
             ++ destruct RS as (rc & Hrc & [A B C]). exists rc. split; [exact Hrc|]. constructor; [exact A | exact B | exact C].
      + apply (rep_group_transport st st' M M' x); try reflexivity.
        * intros E; exact E.
        * change (s_kind st' x) with (s_kind st x). change (g_maplen st' x) with (g_maplen st x).
          destruct (s_kind st x); [split; reflexivity | exact I].
        * intros k Hk. left. apply e_slot_other. left. exact Hxm.
        * intros a G. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          assert (G0 : gcell st x a).
          { destruct (t_gcell_back x a G) as [G0|(E & _)]; [exact G0 | exact (False_ind _ (Hxm E))]. }
          pose proof (gcell_in_span st L HWF x a Hx G0).
          exact (frame_other_cell x a Hx Hxm G0 (HMfr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE)).
        * exact HMgrow.
        * exact SPAN.
        * intros a G. assert (G0 : gcell st x a).
          { destruct (t_gcell_back x a G) as [G0|(E & _)]; [exact G0 | exact (False_ind _ (Hxm E))]. }
          exact (gcell_in_span st L HWF x a Hx G0).
        * exact (rp_groups st M HREP x Hx).
  Qed.

  Theorem enframe_close : WF st' L' /\ REP st' M'.
  Proof using HX HLlen H63 HMgrow HMfr POST Hsn Hn Hslot Hi Hgrp HREP HWF M. split; [exact t_WF | exact t_REP]. Qed.
End Enfr.
