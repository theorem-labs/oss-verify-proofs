(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.MhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhFreeA.MhFreePro OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Open.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.

  Lemma WF_ctx : wf_ctx st. Proof using HWF L. exact (proj1 HWF). Qed.
  Lemma WF_areas : wf_areas st. Proof using HWF L. exact (proj1 (proj2 HWF)). Qed.
  Lemma WF_lists : wf_lists st. Proof using HWF L RN. exact (proj1 (proj2 (proj2 HWF))). Qed.
  Lemma WF_groups : wf_groups st L. Proof using HWF RN. exact (proj1 (proj2 (proj2 (proj2 HWF)))). Qed.
  Lemma WF_geom : wf_geom st. Proof using HWF L RN. exact (proj1 (proj2 (proj2 (proj2 (proj2 HWF))))). Qed.
  Lemma WF_live : wf_live st L. Proof using HWF RN. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))). Qed.
  Lemma WF_regions : wf_regions st. Proof using HWF L. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF))))))). Qed.
  Lemma WF_img : wf_img st. Proof using HWF L RN. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF))))))). Qed.

  (* [comment removed for export] *)
  Lemma wf_img_same : forall st', s_areas st' = s_areas st -> s_regions st' = s_regions st -> wf_img st'.
  Proof using HWF L RN.
    intros st' EA ER. constructor.
    - intros a Ha. rewrite EA in Ha. exact (wi_areas st WF_img a Ha).
    - intros r Hr. rewrite ER in Hr. exact (wi_regions st WF_img r Hr).
  Qed.
  (* [comment removed for export] *)
  Lemma wf_img_sub : forall st',
    (forall a, In a (s_areas st') -> In a (s_areas st) \/ img_free a (a + 4096)) ->
    (forall r, In r (s_regions st') -> In r (s_regions st) \/ img_free (rg_base r) (rg_base r + rg_len r)) ->
    wf_img st'.
  Proof using HWF L RN.
    intros st' HA HR. constructor.
    - intros a Ha. destruct (HA a Ha) as [X|X]; [exact (wi_areas st WF_img a X) | exact X].
    - intros r Hr. destruct (HR r Hr) as [X|X]; [exact (wi_regions st WF_img r X) | exact X].
  Qed.

  (* [comment removed for export] *)
  Lemma metaU_area : forall m, metaU st m ->
    exists ar k, In ar (s_areas st) /\ 0 <= k < NSLOTS /\ m = meta_addr ar k /\
                 ar mod 4096 = 0 /\ HEAPLO <= ar /\ ar + 4096 <= CEIL /\ ar + 24 <= m /\ m + 40 <= ar + 4096 /\
                 m - m mod 4096 = ar.
  Proof using HWF L.
    intros m (ar & k & Hin & Hk & ->).
    destruct (wa_rng st WF_areas ar Hin) as (Hal & Hlo & Hhi).
    exists ar, k. unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *. repeat split; try assumption; try lia.
  Qed.

  Section User.
    Variables (p n m i off res : Z).
    Hypothesis Hgrp : is_group st m.
    Hypothesis Hi : 0 <= i <= g_lastidx st m.
    Hypothesis Hslot : s_slot st m i = SUser p n off res.

    Let G := g_mem st m.
    Let stride := g_stride st m.
    Let W := g_W st m.
    Let av := mr_avail (s_meta st m).
    Let fr := mr_freed (s_meta st m).
    Let q := inband st m p.
    Let e := g_slot_end st m i.
    Let sec := c_secret (s_ctx st).

    Lemma U_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (wG_each st L WF_groups m Hgrp). Qed.
    Lemma U_repg : rep_group st M m. Proof using Hgrp HREP. exact (rp_groups st M HREP m Hgrp). Qed.
    Lemma U_slotwf : slot_wf st L m i (SUser p n off res).
    Proof using Hslot Hi Hgrp HWF RN. rewrite <- Hslot. exact (wg_slots st L m U_wfg i Hi). Qed.
    Lemma U_reps : rep_slot st M m i (SUser p n off res).
    Proof using Hslot Hi Hgrp HREP. rewrite <- Hslot. exact (rg_slots st M m U_repg i Hi). Qed.

    Lemma U_last : 0 <= g_lastidx st m < 32.
    Proof using sec e q fr av W stride G i p. unfold g_lastidx, w_lastidx. apply Z.mod_pos_bound. lia. Qed.

    Lemma U_pure :
      0 <= off /\ 0 <= n /\ p = g_slot_start st m i + 16 * off /\ res = stride - IB - n - 16 * off /\ 0 <= res < 2 ^ 31 /\
      ptr_ok st m i p /\ In (p, n) L.
    Proof using Hslot Hi Hgrp HWF RN. exact U_slotwf. Qed.

    Lemma U_stride : 16 <= stride /\ stride mod 16 = 0.
    Proof using Hgrp HWF L RN. exact (wg_stride st L m U_wfg). Qed.

    Lemma U_mem : 0 < G /\ G mod 16 = 0 /\ G + UNIT + stride * g_cnt st m < 2 ^ 47.
    Proof using Hgrp HWF L RN. exact (wg_mem st L m U_wfg). Qed.

    Lemma U_q : q = stride * i / 16 + off /\ 0 <= q < 2 ^ 16.
    Proof using sec e fr av W G Hslot Hi Hgrp res n HWF L RN.
      destruct U_pure as (Hoff & Hn & Hp & Hres & Hr & (Hal & Hge & Hmod & Hq & _) & _).
      destruct U_stride as (S1 & S2). subst q. unfold inband in *. fold G in Hp, Hge, Hmod, Hq |- *.
      unfold g_slot_start in Hp. fold G stride in Hp. unfold UNIT in *.
      split; [|exact Hq]. rewrite Hp.
      replace (G + 16 + stride * i + 16 * off - G - 16) with (stride * i + off * 16) by lia.
      rewrite Z.div_add by lia. reflexivity.
    Qed.

    Lemma U_masks : 0 <= av < 2 ^ 32 /\ 0 <= fr < 2 ^ 32 /\ Z.testbit av i = false /\ Z.testbit fr i = false.
    Proof using sec e q W stride G Hslot Hi Hgrp res off n p HWF L RN.
      pose proof U_wfg as WG.
      split; [exact (wg_avr st L m WG)|]. split; [exact (wg_frr st L m WG)|].
      split.
      - destruct (Z.testbit av i) eqn:E; [|reflexivity]. exfalso.
        apply (proj1 (wg_av st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E.
      - destruct (Z.testbit fr i) eqn:E; [|reflexivity]. exfalso.
        apply (proj1 (wg_fr st L m WG i ltac:(lia))) in E. destruct E as [_ E]. rewrite Hslot in E. discriminate E.
    Qed.

    (* [comment removed for export] *)
    Lemma U_meta_cells :
      exists ar k, In ar (s_areas st) /\ m = meta_addr ar k /\ m - m mod 4096 = ar /\ HEAPLO + 24 <= m /\ m + 40 <= CEIL /\
        rep_meta M m (s_meta st m) /\ cell M ar 8 sec /\ defined M ar (ar + 4096).
    Proof using e q fr av W stride G Hgrp i p HREP HWF L.
      destruct (metaU_area m (wg_U st L m U_wfg)) as (ar & k & Hin & Hk & Hm & Hal & Hlo & Hhi & H1 & H2 & H3).
      pose proof (rp_areas st M HREP ar Hin) as RA.
      exists ar, k. conjs; try assumption; try lia.
      - rewrite Hm. exact (ra_metas st M ar RA k Hk).
      - exact (ra_check st M ar RA).
      - exact (ra_def st M ar RA).
    Qed.

    (* [comment removed for export] *)
    Lemma end_byte_zero_gen : forall fuel g k, nest_depth_le st fuel g -> is_group st g -> 0 <= k <= g_lastidx st g ->
      byte_at M (g_slot_end st g k) 0.
    Proof using sec e q fr av W stride G i m p HREP HWF L RN.
      induction fuel as [|fuel IH]; intros g k Hd Hg Hk.
      - pose proof (wG_each st L WF_groups g Hg) as WG. pose proof (rp_groups st M HREP g Hg) as RG.
        cbn [nest_depth_le] in Hd.
        replace (g_slot_end st g k) with (g_slot_start st g (k + 1) - 4) by (unfold g_slot_end, g_slot_start, IB; lia).
        apply (rg_hdr0 st M g RG (k + 1)); [unfold g_cnt; lia|].
        destruct (Z.lt_ge_cases (k + 1) (g_cnt st g)) as [Hl|Hge]; [left; exact Hl | right].
        unfold endb_own. destruct (s_kind st g); [exact I | destruct Hd].
      - pose proof (wG_each st L WF_groups g Hg) as WG. pose proof (rp_groups st M HREP g Hg) as RG.
        replace (g_slot_end st g k) with (g_slot_start st g (k + 1) - 4) by (unfold g_slot_end, g_slot_start, IB; lia).
        destruct (Z.lt_ge_cases (k + 1) (g_cnt st g)) as [Hl|Hge].
        + apply (rg_hdr0 st M g RG (k + 1)); [unfold g_cnt; lia | left; exact Hl].
        + assert (Hk1 : k + 1 = g_cnt st g) by (unfold g_cnt in *; lia).
          pose proof (wg_kind st L g WG) as KD. pose proof (ge_span st WF_geom g Hg) as SP.
          cbn [nest_depth_le] in Hd. unfold endb_own in *.
          destruct (s_kind st g) as [|hm j hoff] eqn:EK.
          * apply (rg_hdr0 st M g RG (k + 1)); [unfold g_cnt; lia | right]. unfold endb_own. rewrite EK. exact I.
          * destruct SP as [Sb Se]. destruct KD as (Kml & Khm & Kne & Kj & Khoff & Ksl & _).
            destruct (Z.lt_ge_cases (gspan st g - 1) (g_slot_end st hm j)) as [Hlt|Hge2].
            -- apply (rg_hdr0 st M g RG (k + 1)); [unfold g_cnt; lia | right]. unfold endb_own. rewrite EK. exact Hlt.
            -- assert (E : g_slot_start st g (k + 1) - 4 = g_slot_end st hm j).
               { rewrite Hk1. unfold gspan, g_span_end, g_slot_start, IB in *. lia. }
               rewrite E. apply IH; [exact Hd | exact Khm | exact Kj].
    Qed.

    Lemma U_end_zero : byte_at M e 0.
    Proof using sec q fr av W stride G Hi Hgrp p HREP HWF L RN. apply (end_byte_zero_gen 8); [exact (wg_depth st L m U_wfg) | exact Hgrp | exact Hi]. Qed.

    (* [comment removed for export] *)
    Lemma U_free_pre : forall sp,
      CEIL + 96 <= sp < 2 ^ 64 ->
      store_ok RSEGS M (Z_to_bv 64 (sp - 48)) 48%nat = true ->
      free_pre M sp p e G m i off n stride res q W av fr (Z_to_bv 64 sec).
    Proof using Hslot Hi Hgrp HREP HWF L.
      intros sp Hsp SOK.
      destruct U_pure as (Hoff & Hn & Hp & Hres & Hr & (Hal & Hge & Hmod & Hq & Hsc & Hml) & HinL).
      destruct U_stride as (S1 & S2). destruct U_mem as (G1 & G2 & G3). pose proof U_last as HL.
      destruct U_q as (Q1 & Q2). destruct U_masks as (A1 & F1 & A2 & F2).
      destruct U_meta_cells as (ar & k & Har & Hmk & Harea & Hmlo & Hmhi & RM & Hchk & Hdef).
      destruct U_reps as (RH & Rzr & R5). destruct RH as [Rm4 Rm3 Rm2].
      pose proof U_repg as RG. pose proof U_wfg as WG.
      pose proof (ge_inreg st WF_geom m Hgrp) as (rg & Hrg & Rb & Re).
      destruct (wr_rng st WF_regions rg Hrg) as (Rlo & Rhi & _).
      assert (He : e = G + 16 + stride * i + stride - 4) by reflexivity.
      assert (Hcnt : i + 1 <= g_cnt st m) by (unfold g_cnt; lia).
      assert (Hspan : e + 1 <= gspan st m).
      { unfold gspan, g_span_end. rewrite He. fold G stride. unfold UNIT, IB.
        assert (stride * (i + 1) <= stride * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      ceil; unfold HEAPLO in *.
      constructor; try assumption;
        try (lazymatch goal with |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ /\ _) => idtac end;
             subst; unfold g_slot_end, g_slot_start, UNIT, IB in *; lia).
      - (* [comment removed for export] *) reflexivity.
      - (* [comment removed for export] *) exact (wg_Wr st L m WG).
      - (* [comment removed for export] *) destruct (wg_sc st L m WG) as [H48 | (H63 & Hl0 & Hml0)].
        + left. split; [exact H48|]. exact (Hsc H48).
        + right. split; [exact H63|]. split; [change (g_maplen st m <> 0); lia | exact Hl0].
      - (* [comment removed for export] *) intros H5. exact (proj2 (R5 H5)).
      - (* [comment removed for export] *) intros H5. exact (proj1 (R5 H5)).
      - (* [comment removed for export] *) exact U_end_zero.
      - (* [comment removed for export] *) exact (rg_meta st M m RG).
      - (* [comment removed for export] *) exact (rm_mem M m _ RM).
      - exact (rm_W M m _ RM).
      - exact (rm_avail M m _ RM).
      - exact (rm_freed M m _ RM).
      - (* [comment removed for export] *) rewrite Harea. exact Hchk.
      - (* [comment removed for export] *) exact (rc_secret st M (rp_ctx st M HREP)).
      - (* [comment removed for export] *) intros a Ha. apply (rc_tab_sc st M (rp_statics st M HREP)). unfold A_TAB_SC, A_TAB_MED. lia.
    Qed.
  End User.

  (* [comment removed for export] *)
  Lemma gcell_in_span : forall x a, is_group st x -> gcell st x a -> g_mem st x <= a < gspan st x.
  Proof using HWF L RN.
    intros x a Hx G. pose proof (wG_each st L WF_groups x Hx) as WG.
    pose proof (wg_stride st L x WG) as [S16 _]. pose proof (wg_mem st L x WG) as (M1 & M2 & M3).
    assert (HL : 0 <= g_lastidx st x < 32) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
    unfold gspan, g_span_end.
    destruct G as [G | [G | [G | G]]].
    - assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; nia). unfold UNIT, IB. lia.
    - destruct G as (k & Hk & -> & _). unfold g_slot_start, UNIT, IB.
      assert (0 <= g_stride st x * k) by nia. assert (g_stride st x * k <= g_stride st x * g_cnt st x) by nia. lia.
    - destruct G as (k & q & Hk & Hq & Ha). pose proof (wg_slots st L x WG k Hk) as SW. unfold slot_ptr in Hq.
      assert (Hkc : g_stride st x * (k + 1) <= g_stride st x * g_cnt st x) by (unfold g_cnt; nia).
      assert (0 <= g_stride st x * k) by nia.
      destruct (s_slot st x k) as [| |q2 n2 o2 r2|c o2|o2] eqn:Es; try discriminate Hq; injection Hq; intros <-; cbn [slot_wf] in SW.
      + destruct SW as (A & B & C & D & E & _). unfold g_slot_start, UNIT, IB in *. lia.
      + destruct SW as (A & B & C & D & E).
        pose proof (wg_kind st L c (wG_each st L WF_groups c B)) as KC. rewrite D in KC.
        destruct KC as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
        pose proof (wg_stride st L c (wG_each st L WF_groups c B)) as [SC _].
        assert (0 <= g_lastidx st c) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
        assert (0 <= g_cnt st c * g_stride st c) by (apply Z.mul_nonneg_nonneg; unfold g_cnt; lia).
        unfold g_slot_start, UNIT, IB in *. lia.
      + destruct SW as (A & B & C). unfold g_slot_start, UNIT, IB in *. lia.
    - destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha). pose proof (wg_slots st L x WG k Hk) as SW.
      rewrite Hs in SW. cbn [slot_wf] in SW. destruct SW as (A & B & C & D & E & _).
      assert (g_stride st x * (k + 1) <= g_stride st x * g_cnt st x) by (unfold g_cnt; nia).
      assert (0 <= g_stride st x * k) by nia.
      unfold g_slot_end, g_slot_start, UNIT, IB in *. lia.
  Qed.

  Lemma group_range : forall x, is_group st x -> HEAPLO <= g_mem st x /\ gspan st x <= CEIL.
  Proof using HWF L.
    intros x Hx. destruct (ge_inreg st WF_geom x Hx) as (r & Hr & B & E).
    destruct (wr_rng st WF_regions r Hr) as (R1 & R2 & _). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma group_img : forall x, is_group st x ->
    (gspan st x <= IMG_LO \/ IMG_HI <= g_mem st x) /\ g_mem st x + 29 <= gspan st x.
  Proof using HWF L RN.
    intros x Hx. destruct (ge_inreg st WF_geom x Hx) as (r & Hr & B & E).
    pose proof (wG_each st L WF_groups x Hx) as WG. pose proof (wg_stride st L x WG) as [S16 _].
    assert (HL : 0 <= g_lastidx st x < 32) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia).
    assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; nia).
    split; [| unfold gspan, g_span_end, UNIT, IB; lia].
    destruct (wi_regions st WF_img r Hr) as [X|X]; [left | right]; lia.
  Qed.
  Lemma area_img : forall a, In a (s_areas st) -> a + 4096 <= IMG_LO \/ IMG_HI <= a.
  Proof using HWF L RN. intros a Ha. exact (wi_areas st WF_img a Ha). Qed.
  Lemma region_img : forall r, In r (s_regions st) -> rg_base r + rg_len r <= IMG_LO \/ IMG_HI <= rg_base r.
  Proof using HWF L RN. intros r Hr. exact (wi_regions st WF_img r Hr). Qed.
  Lemma metaU_img : forall x, metaU st x -> x + 40 <= IMG_LO \/ IMG_HI + 24 <= x.
  Proof using HWF L RN.
    intros x U. destruct (metaU_area x U) as (ar & k & Har & Hk & Hx & Hal & Hlo & Hhi & H1 & H2 & _).
    destruct (wi_areas st WF_img ar Har) as [X|X]; [left | right]; lia.
  Qed.
End Open.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac hsep_with W st L :=
  repeat match goal with
  | G : is_group _ ?x |- _ =>
      lazymatch goal with
      | _ : (gspan st x <= IMG_LO \/ IMG_HI <= g_mem st x) |- _ => fail
      | _ => let a := fresh "gi" in let b := fresh "gi" in destruct (group_img st L W x G) as [a b];
             try (lazymatch goal with
                  | _ : x + 40 <= IMG_LO \/ IMG_HI + 24 <= x |- _ => idtac
                  | _ => pose proof (metaU_img st L W x (wg_U st L x (wG_each st L (WF_groups st L W) x G)))
                  end)
      end
  | A : In ?a (s_areas _) |- _ =>
      lazymatch goal with
      | _ : a + 4096 <= IMG_LO \/ IMG_HI <= a |- _ => fail
      | _ => pose proof (area_img st L W a A)
      end
  | R : In ?r (s_regions _) |- _ =>
      lazymatch goal with
      | _ : rg_base r + rg_len r <= IMG_LO \/ IMG_HI <= rg_base r |- _ => fail
      | _ => pose proof (region_img st L W r R)
      end
  | U : metaU _ ?x |- _ =>
      lazymatch goal with
      | _ : x + 40 <= IMG_LO \/ IMG_HI + 24 <= x |- _ => fail
      | _ => pose proof (metaU_img st L W x U)
      end
  end.
(* [comment removed for export] *)
Ltac hsep :=
  repeat match goal with W : WF ?st ?L |- _ => progress (hsep_with W st L) end.
(* [comment removed for export] *)
Ltac lia_hsep ::= hsep.
