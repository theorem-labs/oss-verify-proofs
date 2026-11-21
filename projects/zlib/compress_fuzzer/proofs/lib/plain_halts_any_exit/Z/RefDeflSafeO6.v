(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import OverlayIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Export OverlayTF.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeO2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeO3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeO5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section OT.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.
Let TP : TPF s := tree_phase s OP.
Let N := nsym s.

Lemma wsum_L : zsum (fun u => arr_get (tree_fc (ov_X0 s) TL) u) 0 (Z.to_nat (sd_elems TL)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc0L _ TP). cbn [sd_elems].
  pose proof (fubini_L s OP (fun _ => 1)) as F. cbv beta in F.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_ltree_fc s) c * 1) (fun u => arr_get (ds_dyn_ltree_fc s) u)) in F by (intros; lia).
  rewrite zsum_const1 in F. pose proof (op_nsym _ OP). pose proof (op_lbs _ OP). unfold L_CODES in *. rewrite F. lia.
Qed.

Lemma wsum_D : zsum (fun u => arr_get (tree_fc (ov_X1 s) TD) u) 0 (Z.to_nat (sd_elems TD)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc1D _ TP). cbn [sd_elems].
  pose proof (fubini_D s OP (fun _ => 1)) as F. cbv beta in F.
  rewrite (zsum_ext (fun c => arr_get (ds_dyn_dtree_fc s) c * 1) (fun u => arr_get (ds_dyn_dtree_fc s) u)) in F by (intros; lia).
  pose proof (zsum_mono (fun j => zind (sym_isdist s j) * 1) (fun _ => 1) 0 (Z.to_nat (nsym s)) ltac:(intros; cbv beta; destruct (sym_isdist s _); cbn; lia)) as M.
  rewrite zsum_const1 in M. pose proof (op_nsym _ OP). pose proof (op_lbs _ OP). unfold D_CODES in *. rewrite F. lia.
Qed.

Lemma wsum_B : zsum (fun u => arr_get (tree_fc (ov_X4 s) TB) u) 0 (Z.to_nat (sd_elems TB)) + 2 < 2 ^ 16.
Proof.
  rewrite (tp_fc4B _ TP). cbn [sd_elems].
  pose proof (tp_lmax _ TP) as RL. pose proof (tp_dmax _ TP) as RD. unfold L_CODES, D_CODES in RL, RD.
  pose proof (zsum_bound (fun u => arr_get (ov_BC s) u) 0 (Z.to_nat BL_CODES) 636 ltac:(lia)) as B.
  assert (X : forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat BL_CODES) -> 0 <= arr_get (ov_BC s) i <= 636).
  { intros i Hi. unfold BL_CODES in Hi. rewrite (tp_BC _ TP) by lia.
    pose proof (TDcnt_nonneg (fun j => Len (ov_X6 s) TL j) (ds_l_max_code (ov_X6 s)) i). pose proof (TDcnt_le (fun j => Len (ov_X6 s) TL j) (ds_l_max_code (ov_X6 s)) i ltac:(lia)).
    pose proof (TDcnt_nonneg (fun j => Len (ov_X6 s) TD j) (ds_d_max_code (ov_X6 s)) i). pose proof (TDcnt_le (fun j => Len (ov_X6 s) TD j) (ds_d_max_code (ov_X6 s)) i ltac:(lia)). lia. }
  specialize (B X). unfold BL_CODES in *. lia.
Qed.

Theorem ot_facts : exists zL zD zB FlL FlD FlB,
     tree_facts zL 286 15 (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL
  /\ tree_facts zD 30 15 (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD
  /\ tree_facts zB 19 7 (fun x => arr_get (ov_BC s) x) FlB
  /\ zt_kraft zL /\ zt_kraft zD /\ zt_kraft zB

  /\ (forall c, zt_len zL c = arr_get (tree_dl (ov_X1 s) TL) c)
  /\ (forall d, zt_len zD d = arr_get (tree_dl (ov_X2 s) TD) d)
  /\ (forall x, zt_len zB x = arr_get (tree_dl (ov_X5 s) TB) x)
  /\ (forall c, c <> ds_l_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TL c = zt_len zL c)
  /\ (forall d, d <> ds_d_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TD d = zt_len zD d)
  /\ (forall x, Len (ov_X6 s) TB x = zt_len zB x)
  /\ Len (ov_X6 s) TL (ds_l_max_code (ov_X6 s) + 1) = 65535
  /\ Len (ov_X6 s) TD (ds_d_max_code (ov_X6 s) + 1) = 65535

  /\ (ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL (ds_l_max_code (ov_X6 s)) <> 0
      /\ forall c, 0 <= c < 286 -> ffreq (fun c => arr_get (ds_dyn_ltree_fc s) c) FlL c <> 0 -> c <= ds_l_max_code (ov_X6 s))
  /\ (ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD (ds_d_max_code (ov_X6 s)) <> 0
      /\ forall d, 0 <= d < 30 -> ffreq (fun d => arr_get (ds_dyn_dtree_fc s) d) FlD d <> 0 -> d <= ds_d_max_code (ov_X6 s))

  /\ (1 <= nsym s -> FlL = []).
Proof.
  pose proof (op_hist _ OP) as (FHL & FHD & FHB). pose proof (op_nsym _ OP) as RN.

  destruct (build_tree_ztree (ov_X0 s) TL (bt_pre_X0 s OP) wsum_L)
    as (FlL & L1 & mc1 & FCf1 & DLf1 & HPf1 & DPf1 & DL21 & Wg1 & DLq1 & FCg1 & BCq1 & OLq1 & SLq1 & EB1 & EDL1 & EMC1 & LF1 & ND1 & FF1 & FCE1 & NOF1 & TWO1 & HR1 & GF1 & DLI1 & ZOK1 & KRF1 & USED1 & WT1).
  change (build_tree (ov_X0 s) TL) with (ov_X1 s) in EB1, EDL1, EMC1.
  rewrite (tp_fc0L _ TP) in HR1, GF1, DLI1, FF1, FCE1, NOF1, TWO1, USED1, WT1. cbn [sd_elems] in FF1, NOF1, TWO1, USED1, WT1.
  rewrite (tp_mc1 _ TP) in EMC1.

  destruct (build_tree_ztree (ov_X1 s) TD (tp_bp1 _ TP) wsum_D)
    as (FlD & L2 & mc2 & FCf2 & DLf2 & HPf2 & DPf2 & DL22 & Wg2 & DLq2 & FCg2 & BCq2 & OLq2 & SLq2 & EB2 & EDL2 & EMC2 & LF2 & ND2 & FF2 & FCE2 & NOF2 & TWO2 & HR2 & GF2 & DLI2 & ZOK2 & KRF2 & USED2 & WT2).
  change (build_tree (ov_X1 s) TD) with (ov_X2 s) in EB2, EDL2, EMC2.
  rewrite (tp_fc1D _ TP) in HR2, GF2, DLI2, FF2, FCE2, NOF2, TWO2, USED2, WT2. cbn [sd_elems] in FF2, NOF2, TWO2, USED2, WT2.
  rewrite (tp_mc2 _ TP) in EMC2.

  destruct (build_tree_ztree (ov_X4 s) TB (tp_bp4 _ TP) wsum_B)
    as (FlB & L5 & mc5 & FCf5 & DLf5 & HPf5 & DPf5 & DL25 & Wg5 & DLq5 & FCg5 & BCq5 & OLq5 & SLq5 & EB5 & EDL5 & EMC5 & LF5 & ND5 & FF5 & FCE5 & NOF5 & TWO5 & HR5 & GF5 & DLI5 & ZOK5 & KRF5 & USED5 & WT5).
  change (build_tree (ov_X4 s) TB) with (ov_X5 s) in EB5, EDL5, EMC5.
  rewrite (tp_fc4B _ TP) in HR5, GF5, DLI5, FF5, FCE5, NOF5, TWO5, USED5, WT5. cbn [sd_elems] in FF5, NOF5, TWO5, USED5, WT5.
  exists (ztree_of TL L1 HPf1 Wg1 DLq1), (ztree_of TD L2 HPf2 Wg2 DLq2), (ztree_of TB L5 HPf5 Wg5 DLq5), FlL, FlD, FlB.
  assert (PKG : forall t L HPf Wg DLq Fl (F : arr) FC2 DL2 mc FCf DLf DPf,
            heap_result t FC2 DL2 L mc FCf DLf HPf DPf ->
            (length Fl <= 2)%nat -> NoDup Fl -> (forall f, In f Fl -> 0 <= f < sd_elems t /\ arr_get F f = 0 /\ f <= 2) ->
            (forall i, arr_get FC2 i = if existsb (Z.eqb i) Fl then 1 else arr_get F i) ->
            (forall a b, 0 <= a < sd_elems t -> 0 <= b < sd_elems t -> a <> b -> arr_get F a <> 0 -> arr_get F b <> 0 -> Fl = []) ->
            (exists a b, 0 <= a < sd_elems t /\ 0 <= b < sd_elems t /\ a <> b /\ arr_get FC2 a <> 0 /\ arr_get FC2 b <> 0) ->
            ztree_ok (ztree_of t L HPf Wg DLq) ->
            (forall c, 0 <= c < sd_elems t -> (zt_used (ztree_of t L HPf Wg DLq) c <-> arr_get FC2 c <> 0)) ->
            (forall i, 574 - 2 * L <= i <= 572 -> leafb t HPf i = true -> g_wt (gtree_of t L HPf Wg) i = arr_get FC2 (nd HPf i) /\ 0 <= nd HPf i < sd_elems t) ->
            tree_facts (ztree_of t L HPf Wg DLq) (sd_elems t) (sd_max_length t) (fun c => arr_get F c) Fl
            /\ (ffreq (fun c => arr_get F c) Fl mc <> 0 /\ forall c, 0 <= c < sd_elems t -> ffreq (fun c => arr_get F c) Fl c <> 0 -> c <= mc)).
  { intros t L HPf Wg DLq Fl F FC2 DL2 mc FCf DLf DPf HR LF ND FF FCE NOF TWO ZOK USED WT.
    assert (FQ : forall c, ffreq (fun c => arr_get F c) Fl c = arr_get FC2 c) by (intros c; unfold ffreq; rewrite FCE; reflexivity).
    split.
    - constructor.
      + exact ZOK.
      + reflexivity.
      + reflexivity.
      + split; [exact LF|]. split; [exact ND|]. intros f Hf. destruct (FF f Hf) as (A & B & C0). lia.
      + exact NOF.
      + destruct TWO as (a & b' & Ha & Hb & Nab & Fa & Fb). exists a, b'. rewrite !FQ. repeat split; assumption || lia.
      + intros c Hc. rewrite FQ. apply USED. exact Hc.
      + intros i Hi Li. unfold g_pos in Hi. cbn [zt_g ztree_of g_lo g_hi g_leaf g_code RefDeflSafeO3.gtree_of] in Hi, Li |- *.
        unfold RefDeflSafeB3.HM in Hi. destruct (WT i Hi Li) as [A B]. rewrite FQ. split; [exact B|].
        cbn [g_wt RefDeflSafeO3.gtree_of] in A. exact A.
    - split; [rewrite FQ; apply (hr_mc_in _ _ _ _ _ _ _ _ _ HR)|]. intros c Hc. rewrite FQ. apply (hr_mc_max _ _ _ _ _ _ _ _ _ HR). exact Hc. }
  destruct (PKG TL L1 HPf1 Wg1 DLq1 FlL (ds_dyn_ltree_fc s) _ DL21 mc1 FCf1 DLf1 DPf1 HR1 LF1 ND1 FF1 FCE1 NOF1 TWO1 ZOK1 USED1 WT1) as [TF1 MX1].
  destruct (PKG TD L2 HPf2 Wg2 DLq2 FlD (ds_dyn_dtree_fc s) _ DL22 mc2 FCf2 DLf2 DPf2 HR2 LF2 ND2 FF2 FCE2 NOF2 TWO2 ZOK2 USED2 WT2) as [TF2 MX2].
  destruct (PKG TB L5 HPf5 Wg5 DLq5 FlB (ov_BC s) _ DL25 mc5 FCf5 DLf5 DPf5 HR5 LF5 ND5 FF5 FCE5 NOF5 TWO5 ZOK5 USED5 WT5) as [TF5 MX5].
  cbn [sd_elems sd_max_length] in TF1, MX1, TF2, MX2, TF5, MX5.
  split; [exact TF1|]. split; [exact TF2|]. split; [exact TF5|].
  split; [exact KRF1|]. split; [exact KRF2|]. split; [exact KRF5|].
  split; [intros c; cbn [zt_len ztree_of]; rewrite <- EDL1; reflexivity|].
  split; [intros d; cbn [zt_len ztree_of]; rewrite <- EDL2; reflexivity|].
  split; [intros x; cbn [zt_len ztree_of]; rewrite <- EDL5; reflexivity|].
  split; [intros c Hc; cbn [zt_len ztree_of]; rewrite <- EDL1; exact (tp_len1 _ TP c Hc)|].
  split; [intros d Hd; cbn [zt_len ztree_of]; rewrite <- EDL2; exact (tp_len2 _ TP d Hd)|].
  split; [intros x; cbn [zt_len ztree_of]; rewrite <- EDL5; exact (tp_len5 _ TP x)|].
  split; [exact (tp_guard1 _ TP)|]. split; [exact (tp_guard2 _ TP)|].
  split; [rewrite EMC1; exact MX1|]. split; [rewrite EMC2; exact MX2|].

  intros HN. pose proof (sym_codes s OP 0 ltac:(lia)) as (A & _ & _ & Lit & M).
  assert (F0 : arr_get (ds_dyn_ltree_fc s) (sym_lcode s 0) <> 0).
  { rewrite (FHL (sym_lcode s 0)) by exact A.
    pose proof (zsum_ge_point (fun j => zind (sym_lcode s j =? sym_lcode s 0)) 0 (Z.to_nat (nsym s)) 0 ltac:(intros; apply (proj1 (zind_le1 _))) ltac:(lia)) as X.
    cbv beta in X. rewrite Z.eqb_refl in X. cbn [zind] in X. pose proof (zind_le1 (sym_lcode s 0 =? END_BLOCK)). lia. }
  assert (FE : arr_get (ds_dyn_ltree_fc s) END_BLOCK <> 0).
  { rewrite (FHL END_BLOCK) by (unfold END_BLOCK, L_CODES; lia). rewrite Z.eqb_refl. cbn [zind].
    pose proof (zsum_nonneg (fun j => zind (sym_lcode s j =? END_BLOCK)) 0 (Z.to_nat (nsym s)) ltac:(intros; apply (proj1 (zind_le1 _)))). lia. }
  assert (NE : sym_lcode s 0 <> END_BLOCK).
  { unfold END_BLOCK. destruct (sym_isdist s 0); [pose proof (M eq_refl) | pose proof (Lit eq_refl)]; lia. }
  unfold L_CODES in A. exact (NOF1 (sym_lcode s 0) END_BLOCK ltac:(unfold L_CODES; lia) ltac:(unfold END_BLOCK, L_CODES; lia) NE F0 FE).
Qed.

End OT.
