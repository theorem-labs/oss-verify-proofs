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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Scribble.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (m i off : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st m.
  Hypothesis Hi : 0 <= i <= g_lastidx st m.
  Hypothesis Hslot : s_slot st m i = SJunk off.
  #[local] Notation jq := (g_slot_start st m i + 16 * off).
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (jq - 3 <= a < jq) \/ CEIL <= a.

  (* [comment removed for export] *)
  Definition stF : mst := set_slot st m i SFreed.

  Lemma f_wfg : wf_group st L m. Proof using Hgrp HWF RN. exact (wG_each st L (WF_groups st L HWF) m Hgrp). Qed.
  Lemma f_pure : 0 <= off /\ 16 * off <= g_stride st m - IB /\ ptr_ok st m i jq.
  Proof using Hslot Hi Hgrp HWF L RN. pose proof (wg_slots st L m f_wfg i Hi) as SW. rewrite Hslot in SW. exact SW. Qed.
  Lemma f_p_rng : HEAPLO + 16 <= jq /\ jq <= g_slot_end st m i /\ g_slot_end st m i < CEIL /\ (g_slot_start st m i <= jq /\ g_mem st m + 16 <= jq < gspan st m).
  Proof using Hslot Hi Hgrp HWF L.
    destruct f_pure as (Hoff & Hfit & (P1 & P2 & _)).
    destruct (group_range st L HWF m Hgrp) as [G1 G2].
    pose proof (wg_stride st L m f_wfg) as [S16 _].
    assert (g_stride st m * (i + 1) <= g_stride st m * g_cnt st m) by (apply Z.mul_le_mono_nonneg_l; unfold g_cnt; lia).
    assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia).
    unfold gspan, g_span_end, g_slot_end, g_slot_start, UNIT, IB in *. lia.
  Qed.

  Lemma slot_sep : forall x k1 k2, 16 <= g_stride st x -> k1 < k2 ->
    g_slot_end st x k1 <= g_slot_start st x k2 - 4.
  Proof using.
    intros x k1 k2 Hs Hlt. unfold g_slot_end, g_slot_start, IB.
    assert (g_stride st x * (k1 + 1) <= g_stride st x * k2) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma f_gcell_where : forall a, gcell stF m a ->
    (g_mem st m <= a < g_mem st m + 12)
    \/ (exists k, 0 <= k <= g_cnt st m /\ a = g_slot_start st m k - 4)
    \/ (exists k, 0 <= k <= g_lastidx st m /\ k <> i /\ g_slot_start st m k - 4 <= a < g_slot_end st m k).
  Proof using Hslot Hi Hgrp HWF off L RN.
    intros a G. destruct f_pure as (Hoff & Hfit & PO). pose proof (wg_stride st L m f_wfg) as [S16 _].
    unfold gcell in G. change (g_mem stF m) with (g_mem st m) in G. change (g_cnt stF m) with (g_cnt st m) in G.
    change (g_lastidx stF m) with (g_lastidx st m) in G.
    change (g_slot_start stF m) with (g_slot_start st m) in G. change (g_slot_end stF m) with (g_slot_end st m) in G.
    destruct G as [G | [G | [G | G]]].
    - left. exact G.
    - right. left. destruct G as (k & Hk & Ha & _). exists k. split; [exact Hk | exact Ha].
    - right. right. destruct G as (k & q & Hk & Hq & Ha).
      unfold slot_ptr, stF in Hq. rewrite s_slot_set_slot in Hq. rewrite Z.eqb_refl in Hq.
      destruct (Z.eqb_spec k i) as [->|Hki]; [cbn in Hq; discriminate Hq|]. cbn [andb] in Hq.
      change (g_slot_start (set_slot st m i SFreed) m k) with (g_slot_start st m k) in Hq.
      exists k. split; [exact Hk|]. split; [exact Hki|].
      pose proof (wg_slots st L m f_wfg k Hk) as SW.
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
      unfold stF in Hs. rewrite s_slot_set_slot, Z.eqb_refl in Hs.
      destruct (Z.eqb_spec k i) as [->|Hki]; [cbn in Hs; discriminate Hs|]. cbn [andb] in Hs.
      exists k. split; [exact Hk|]. split; [exact Hki|].
      pose proof (wg_slots st L m f_wfg k Hk) as SW. rewrite Hs in SW. cbn [slot_wf] in SW.
      destruct SW as (A & B & C & D & E & _). unfold g_slot_end, IB in *. lia.
  Qed.

  Lemma f_gcell_out : forall a, gcell stF m a -> ~ (jq - 3 <= a < jq).
  Proof using Hslot Hi Hgrp HWF L RN.
    intros a G Ha. pose proof (wg_stride st L m f_wfg) as [S16 Smod]. pose proof (wg_mem st L m f_wfg) as (M1 & M2 & M3).
    destruct f_pure as (Hoff & Hfit & (P1 & P2 & P3 & _)). destruct f_p_rng as (R1 & R2 & R3 & R4).
    destruct (f_gcell_where a G) as [W | [(k & Hk & Hak) | (k & Hk & Hki & Hak)]].
    - unfold g_slot_start, UNIT in *. assert (0 <= g_stride st m * i) by (apply Z.mul_nonneg_nonneg; lia). lia.
    - (* [comment removed for export] *)
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      (* [comment removed for export] *)
      unfold g_slot_start, UNIT, IB in *. lia.
    - destruct (Z.lt_ge_cases k i) as [Hl|Hg].
      + pose proof (slot_sep m k i S16 Hl). lia.
      + assert (Hl : i < k) by lia. pose proof (slot_sep m i k S16 Hl). unfold g_slot_end, IB in *. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma f_hdr_gcell : forall a, jq - 3 <= a < jq -> gcell st m a.
  Proof using Hslot Hi.
    intros a Ha. unfold gcell. right. right. left. exists i, jq. unfold slot_ptr. rewrite Hslot. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma f_gcell_back : forall a, gcell stF m a -> gcell st m a.
  Proof using.
    intros a G. unfold gcell in G |- *.
    change (g_mem stF m) with (g_mem st m) in G. change (g_cnt stF m) with (g_cnt st m) in G.
    change (g_lastidx stF m) with (g_lastidx st m) in G.
    change (g_slot_start stF m) with (g_slot_start st m) in G. change (g_slot_end stF m) with (g_slot_end st m) in G.
    destruct G as [G|[G|[G|G]]].
    - left. exact G.
    - right; left. destruct G as (k & Hk & Ha & E). exists k. split; [exact Hk|]. split; [exact Ha|].
      destruct E as [E|E]; [left; exact E | right]. unfold endb_own in E |- *.
      change (s_kind stF m) with (s_kind st m) in E. destruct (s_kind st m); [exact I | exact E].
    - right; right; left. destruct G as (k & q & Hk & Hq & Ha). exists k, q. split; [exact Hk|]. split; [|exact Ha].
      unfold slot_ptr, stF in Hq. rewrite s_slot_set_slot, Z.eqb_refl in Hq.
      destruct (Z.eqb k i); [cbn in Hq; discriminate Hq|]. cbn [andb] in Hq.
      change (g_slot_start (set_slot st m i SFreed) m k) with (g_slot_start st m k) in Hq.
      unfold slot_ptr. destruct (s_slot st m k); try exact Hq.
    - right; right; right. destruct G as (k & q & n2 & o2 & r2 & Hk & Hs & Ha).
      unfold stF in Hs. rewrite s_slot_set_slot, Z.eqb_refl in Hs. destruct (Z.eqb k i); [cbn in Hs; discriminate Hs|]. cbn [andb] in Hs.
      exists k, q, n2, o2, r2. split; [exact Hk|]. split; [exact Hs | exact Ha].
  Qed.

  Lemma f_agree_low : agree_on (fun a => IMG_LO <= a < IMG_HI) M M'.
  Proof using HMwr Hslot Hi Hgrp HWF off i m L st RN.
    intros a Hr Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
    destruct f_p_rng as (R1 & _ & _ & _ & R5). destruct (HMwr a Hr NE) as [W|W]; hsep; ceil; unfold HEAPLO in *; lia.
  Qed.

  Lemma f_keep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Proof using HMgrow. exact (dkeep_of_grows st M M' HMgrow). Qed.

  Theorem REP_scribble : REP st M'.
  Proof using HMwr HMgrow Hslot Hi Hgrp HREP HWF off i m M L RN.
    destruct f_p_rng as (R1 & R2 & R3 & R4). destruct (group_range st L HWF m Hgrp) as [GR1 GR2].
    constructor.
    - apply (rep_statics_tr st st M M' HREP f_keep); [|reflexivity|reflexivity].
      eapply agree_on_mono; [exact f_agree_low|]. intros a Ha. cbv beta in Ha |- *. hsep; unfold CTX, HEAPLO in *. lia.
    - apply (rep_ctx_tr st st M M' HREP f_keep (fun _ => false) false); try reflexivity.
      + eapply agree_on_mono; [exact f_agree_low|]. intros a (Ha & _). cbv beta. hsep; unfold CTX_END, CTX, HEAPLO in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st L M M' HWF HREP f_keep (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        destruct (HMwr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [|ceil; lia].
        apply (ge_area st (WF_geom st L HWF) m a Hgrp); [|exists ar; split; [exact Har | exact Ha]].
        apply (gcell_in_span st L HWF m a Hgrp). apply f_hdr_gcell. exact W.
      + intros x Ux X. discriminate X.
    - intros x Hx. destruct (group_range st L HWF x Hx) as [X1 X2].
      pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
      pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
      assert (SPAN : 0 <= g_mem st x /\ g_mem st x + 16 <= g_span_end st x /\ g_span_end st x < 2 ^ 64).
      { assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; assert (0 <= g_lastidx st x) by (unfold g_lastidx, w_lastidx; apply Z.mod_pos_bound; lia); nia).
        hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia. }
      destruct (Z.eq_dec x m) as [->|Hxm].
      + (* [comment removed for export] *)
        assert (RGF : rep_group stF M' m).
        { apply (rep_group_transport st stF M M' m); try reflexivity.
          - intros E; exact E.
          - change (s_kind stF m) with (s_kind st m). change (g_maplen stF m) with (g_maplen st m).
            destruct (s_kind st m); [split; reflexivity | exact I].
          - intros k Hk. unfold stF. rewrite s_slot_set_slot, Z.eqb_refl.
            destruct (Z.eqb k i); [right; right; reflexivity | left; reflexivity].
          - intros a G. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            pose proof (f_gcell_back a G) as G0.
            pose proof (gcell_in_span st L HWF m a Hgrp G0).
            destruct (HMwr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [exact (f_gcell_out a G W) | ceil; lia].
          - exact HMgrow.
          - exact SPAN.
          - intros a G. apply (gcell_in_span st L HWF m a Hgrp). exact (f_gcell_back a G).
          - exact (rp_groups st M HREP m Hgrp). }
        destruct RGF as [F1 F2 F3 F4 F5]. constructor.
        * exact F1.
        * exact F2.
        * intros k Hk Hend. apply F3; [exact Hk | exact Hend].
        * exact F4.
        * intros k Hk. destruct (Z.eq_dec k i) as [->|Hki]; [rewrite Hslot; exact I|].
          pose proof (F5 k Hk) as RS. unfold stF in RS. rewrite s_slot_set_slot, Z.eqb_refl in RS.
          rewrite (proj2 (Z.eqb_neq k i) Hki) in RS. cbn [andb] in RS.
          destruct (s_slot st m k) as [| |q3 n3 o3 r3|c o3|o3]; cbn [rep_slot] in RS |- *; try exact I.
          -- destruct RS as ([A B C] & Rz & R5). split; [constructor; [exact A | exact B | exact C]|]. split; [exact Rz | exact R5].
          -- destruct RS as (rc & Hrc & [A B C]). exists rc. split; [exact Hrc|]. constructor; [exact A | exact B | exact C].
      + apply (rep_group_transport st st M M' x); try reflexivity.
        * intros E; exact E.
        * destruct (s_kind st x); [split; reflexivity | exact I].
        * intros k Hk. left. reflexivity.
        * intros a G. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          pose proof (gcell_in_span st L HWF x a Hx G).
          destruct (HMwr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [|ceil; lia].
          exact (ge_cells st (WF_geom st L HWF) m x a Hgrp Hx (fun E => Hxm (eq_sym E)) (f_hdr_gcell a W) G).
        * exact HMgrow.
        * exact SPAN.
        * intros a G. exact (gcell_in_span st L HWF x a Hx G).
        * exact (rp_groups st M HREP x Hx).
  Qed.
End Scribble.
