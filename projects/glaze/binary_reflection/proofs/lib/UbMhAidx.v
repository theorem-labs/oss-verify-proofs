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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Aidx.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem) (h ai' b' : Z) (sp : Z).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis Hgrp : is_group st h.
  Hypothesis Hlisted : In h (s_alist st (g_sc st h)).
  Hypothesis Hai' : s_ai st h <= ai' <= g_lastidx st h.
  (* [comment removed for export] *)
  Hypothesis Hpart : forall x, is_group st x -> x <> h -> g_sc st x = g_sc st h -> s_ai st x = g_lastidx st x.
  Definition st' : mst :=
    MST (s_ctx st) (s_areas st) (s_meta st) (s_flist st) (s_alist st) (s_groups st) (fupd (s_ai st) h ai') (s_kind st)
        (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).
  (* [comment removed for export] *)
  Hypothesis Hsp : CEIL + MSTK <= sp.
  Definition x_wr (a : Z) : Prop := (sp - MSTK <= a < sp) \/ a = g_mem st h + 8.
  Hypothesis HMwr : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> x_wr a.
  Hypothesis HMgrow : mem_grows M M'.
  Hypothesis Hb' : 0 <= b' < 256 /\ b' mod 32 = ai'.
  Hypothesis HMb : byte_at M' (g_mem st h + 8) b'.

  Lemma SL : same_layout st st'.
  Proof. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.
  Lemma e_ai : forall x, s_ai st' x = if x =? h then ai' else s_ai st x. Proof. reflexivity. Qed.
  Lemma e_ai_h : s_ai st' h = ai'. Proof. rewrite e_ai, Z.eqb_refl. reflexivity. Qed.
  Lemma e_ai_other : forall x, x <> h -> s_ai st' x = s_ai st x.
  Proof. intros x Hx. rewrite e_ai. destruct (Z.eqb_spec x h); [contradiction | reflexivity]. Qed.
  Lemma h_wfg : wf_group st L h. Proof. exact (wG_each st L (WF_groups st L HWF) h Hgrp). Qed.

  Lemma t_wf_group : forall x, is_group st x -> wf_group st' L x.
  Proof.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    destruct (Z.eq_dec x h) as [->|Hxh].
    - constructor; try assumption; rewrite ?e_ai_h; change (g_lastidx st' h) with (g_lastidx st h) in *; change (g_sc st' h) with (g_sc st h) in *.
      + lia.
      + intros k Hk SA. pose proof (Avai k Hk SA). lia.
      + intros k Hk. apply High. lia.
      + intros _. exact Hlisted.
      + intros Hp. apply Pnd. lia.
    - constructor; try assumption; rewrite ?(e_ai_other x Hxh); assumption.
  Qed.

  Lemma t_WF : WF st' L.
  Proof.
    pose proof HWF as (C & A & Ls & G & Ge & Lv & R & WI).
    split; [destruct C; constructor; assumption|]. split; [exact (wf_areas_ext st st' SL A)|].
    split; [destruct Ls; constructor; assumption|].
    split.
    { destruct G as [ND EACH ONE REG FR0 OTH LIM ONEFF]. constructor; try assumption.
      - intros x Hx. apply t_wf_group. exact Hx.
      - intros m1 m2 H1 H2 P1 P2 E. rewrite e_ai in P1, P2. change (g_lastidx st' m1) with (g_lastidx st m1) in P1. change (g_lastidx st' m2) with (g_lastidx st m2) in P2.
        change (g_sc st' m1 = g_sc st' m2) with (g_sc st m1 = g_sc st m2) in E.
        destruct (Z.eqb_spec m1 h) as [->|N1]; destruct (Z.eqb_spec m2 h) as [->|N2]; [reflexivity | | | exact (ONE m1 m2 H1 H2 P1 P2 E)].
        + exfalso. pose proof (Hpart m2 H2 N2 (eq_sym E)). lia.
        + exfalso. pose proof (Hpart m1 H1 N1 E). lia. }
    split; [exact (wf_geom_ext st st' L SL HWF Ge)|].
    split; [exact (wf_live_ext st st' L SL Lv) |]. split; [exact (wf_regions_ext st st' L SL HWF eq_refl R) | exact (wf_img_ext st st' SL (WF_img st L HWF))].
  Qed.

  (* [comment removed for export] *)
  Lemma HMkeep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Proof. exact (dkeep_of_grows st M M' HMgrow). Qed.
  Lemma h_mem_rng : HEAPLO <= g_mem st h /\ g_mem st h + 16 < CEIL.
  Proof. destruct (group_range st L HWF h Hgrp) as [A B]. pose proof (gspan_gt st L HWF h Hgrp). lia. Qed.
  Lemma t_agree : agree_on (fun a => a < CEIL /\ a <> g_mem st h + 8) M M'.
  Proof.
    intros a Hr [Ha Hn]. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
    destruct (HMwr a Hr NE) as [W|W]; [ceil; unfold MSTK in *; lia | exact (Hn W)].
  Qed.

  Lemma t_REP : REP st' M'.
  Proof.
    pose proof h_mem_rng as [R1 R2].
    constructor.
    - apply (rep_statics_tr st st' M M' HREP HMkeep); [|reflexivity|reflexivity].
      eapply agree_on_mono; [exact t_agree|]. intros a Ha. cbv beta in Ha. hsep; ceil; unfold HEAPLO, CTX in *. lia.
    - apply (rep_ctx_tr st st' M M' HREP HMkeep (fun _ => false) false); try reflexivity.
      + eapply agree_on_mono; [exact t_agree|]. intros a (Ha & _). cbv beta. hsep; ceil; unfold CTX_END, CTX, HEAPLO in *. lia.
      + intros; right; split; reflexivity.
      + right; split; reflexivity.
    - apply (rep_areas_tr st st' L M M' HWF HREP HMkeep (fun _ => false)); try reflexivity.
      + intros ar a Har Ha NE. exfalso. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Hal & Rlo & Rhi).
        destruct (HMwr a ltac:(hsep; ceil; unfold HEAPLO in *; lia) NE) as [W|W]; [ceil; unfold MSTK in *; lia|].
        apply (area_apart_group st L HWF ar h Har) in Hgrp as AP. pose proof (gspan_gt st L HWF h Hgrp). lia.
      + intros x Ux X. discriminate X.
    - intros x Hx. change (is_group st x) in Hx. pose proof (rp_groups st M HREP x Hx) as [Gm Gai Gh Gd Gs].
      destruct (group_range st L HWF x Hx) as [X1 X2].
      assert (AGx : x <> h -> forall a, gcell st x a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros Hxh a G. pose proof (gcell_in_span st L HWF x a Hx G). apply t_agree; [hsep; ceil; unfold HEAPLO in *; lia|]. split; [lia|].
        intros ->. apply (ge_cells st (WF_geom st L HWF) x h (g_mem st h + 8) Hx Hgrp Hxh G). unfold gcell. left. lia. }
      destruct (Z.eq_dec x h) as [->|Hxh].
      + constructor; rewrite ?e_ai_h;
          change (g_mem st' h) with (g_mem st h); change (g_cnt st' h) with (g_cnt st h); change (g_lastidx st' h) with (g_lastidx st h);
          change (g_maplen st' h) with (g_maplen st h); change (s_kind st' h) with (s_kind st h).
        * eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact Gm]. eapply agree_on_mono; [exact t_agree|]. cbn. intros; ceil; lia.
        * exists b'. split; [exact (proj1 Hb')|]. split; [exact HMb | exact (proj2 Hb')].
        * intros k Hk Hend. change (g_slot_start st' h k) with (g_slot_start st h k). change (endb_own st' h) with (endb_own st h) in Hend.
          apply (byte_agree M M'); [| |exact (Gh k Hk Hend)].
          -- pose proof (gcell_in_span st L HWF h (g_slot_start st h k - 4) Hgrp ltac:(unfold gcell; right; left; exists k; repeat split; try lia; exact Hend)). hsep; ceil; unfold HEAPLO in *. lia.
          -- eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->.
             pose proof (gcell_in_span st L HWF h (g_slot_start st h k - 4) Hgrp ltac:(unfold gcell; right; left; exists k; repeat split; try lia; exact Hend)).
             pose proof (wg_stride st L h h_wfg) as [S16 _]. assert (0 <= g_stride st h * k) by (apply Z.mul_nonneg_nonneg; lia).
             ceil; unfold g_slot_start, UNIT in *. split; lia.
        * destruct (s_kind st h); [|exact I]. eapply defined_grows; [exact HMgrow | exact Gd].
        * intros k Hk. change (s_slot st' h k) with (s_slot st h k).
          pose proof (Gs k Hk) as RS.
          assert (AG : forall a, gcell st h a -> a <> g_mem st h + 8 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
          { intros a G Hne. pose proof (gcell_in_span st L HWF h a Hgrp G). apply t_agree; [hsep; ceil; unfold HEAPLO in *; lia | split; [lia | exact Hne]]. }
          destruct (s_slot st h k) as [| |q n o r|c o|o] eqn:Sk; cbn [rep_slot] in RS |- *; try exact I.
          -- change (g_slot_end st' h k) with (g_slot_end st h k).
             pose proof (wg_slots st L h h_wfg k Hk) as SW. rewrite Sk in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & A3 & A4 & A5 & PO & _).
             pose proof (wg_stride st L h h_wfg) as [S16 _]. assert (0 <= g_stride st h * k) by (apply Z.mul_nonneg_nonneg; lia).
             assert (Hq16 : g_mem st h + 16 <= q) by (rewrite A3; unfold g_slot_start, UNIT; lia).
             assert (GH : forall a, q - 4 <= a < q -> gcell st h a) by (intros a Ha; unfold gcell; right; right; left; exists k, q; unfold slot_ptr; rewrite Sk; repeat split; lia).
             assert (GF : forall a, ((0 < r /\ a = q + n) \/ (5 <= r /\ g_slot_end st h k - 5 <= a < g_slot_end st h k)) -> gcell st h a).
             { intros a Ha. unfold gcell. right; right; right. exists k, q, n, o, r. split; [exact Hk|]. split; [exact Sk | exact Ha]. }
             pose proof (gcell_in_span st L HWF h (q - 1) Hgrp (GH (q - 1) ltac:(lia))) as GS1.
             destruct RS as ([B4 B3 B2] & Rz & R5). split; [constructor|split].
             ++ apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact B4]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil. split; lia.
             ++ apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact B3]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil. split; lia.
             ++ eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact B2]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a Ha. ceil. split; lia.
             ++ intros Hr. pose proof (gcell_in_span st L HWF h (q + n) Hgrp (GF (q + n) (or_introl (conj Hr eq_refl)))) as GS2.
                apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact (Rz Hr)]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil. split; lia.
             ++ intros Hr. destruct (R5 Hr) as [C5 B5]. pose proof (gcell_in_span st L HWF h _ Hgrp (GF (g_slot_end st h k - 5) ltac:(right; lia))).
                pose proof (gcell_in_span st L HWF h _ Hgrp (GF (g_slot_end st h k - 1) ltac:(right; lia))).
                split.
                ** eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact C5]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a Ha. ceil; unfold g_slot_end, g_slot_start, UNIT, IB in *. split; lia.
                ** apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact B5]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil; unfold g_slot_end, g_slot_start, UNIT, IB in *. split; lia.
          -- change (g_slot_start st' h k) with (g_slot_start st h k). destruct RS as (rc & Hrc & [B4 B3 B2]). exists rc. split; [exact Hrc|].
             pose proof (wg_slots st L h h_wfg k Hk) as SW. rewrite Sk in SW. cbn [slot_wf] in SW. destruct SW as (A1 & A2 & _).
             pose proof (wg_stride st L h h_wfg) as [S16 _]. assert (0 <= g_stride st h * k) by (apply Z.mul_nonneg_nonneg; lia).
             assert (Hq16 : g_mem st h + 16 <= g_slot_start st h k + 16 * o) by (unfold g_slot_start, UNIT; lia).
             assert (GH : forall a, g_slot_start st h k + 16 * o - 4 <= a < g_slot_start st h k + 16 * o -> gcell st h a).
             { intros a Ha; unfold gcell; right; right; left. exists k, (g_slot_start st h k + 16 * o). unfold slot_ptr; rewrite Sk. repeat split; lia. }
             pose proof (gcell_in_span st L HWF h _ Hgrp (GH (g_slot_start st h k + 16 * o - 1) ltac:(lia))).
             constructor.
             ++ apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact B4]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil. split; lia.
             ++ apply (byte_agree M M'); [hsep; ceil; unfold HEAPLO in *; lia | | exact B3]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a ->. ceil. split; lia.
             ++ eapply cell_agree; [hsep; unfold HEAPLO in *; lia | ceil; cbn; lia | | exact B2]. eapply agree_on_mono; [exact t_agree|]. cbn. intros a Ha. ceil. split; lia.
      + apply (rep_group_transport st st' M M' x); try reflexivity.
        * exact (e_ai_other x Hxh).
        * intros E; exact E.
        * cbn. destruct (s_kind st x); [split; reflexivity | exact I].
        * intros k Hk. left. reflexivity.
        * intros a G. exact (AGx Hxh a G).
        * exact HMgrow.
        * pose proof (wg_stride st L x (wG_each st L (WF_groups st L HWF) x Hx)) as [S16 _].
          pose proof (wg_mem st L x (wG_each st L (WF_groups st L HWF) x Hx)) as (Y1 & Y2 & Y3).
          assert (16 <= g_stride st x * g_cnt st x) by (unfold g_cnt; pose proof (glast_rng st x); nia).
          hsep; ceil; unfold gspan, g_span_end, UNIT, IB, HEAPLO in *. lia.
        * intros a G. exact (gcell_in_span st L HWF x a Hx G).
        * exact (rp_groups st M HREP x Hx).
  Qed.

  Theorem aidx_close : WF st' L /\ REP st' M'.
  Proof. split; [exact t_WF | exact t_REP]. Qed.
End Aidx.
