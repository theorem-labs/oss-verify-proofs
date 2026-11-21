(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBT2.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma aeq_AG_lt (E : Z) a b : aeq (fun i => i < E) a b -> E <= arr_len a -> AG (fun i => 0 <= i < E) a b.
Proof. intros [L H] HE. split; [exact L|]. intros i Hi. apply H; lia. Qed.
Lemma AG_aeq_lt (E : Z) a b : AG (fun i => 0 <= i < E) a b -> aeq (fun i => i < E) a b.
Proof. intros [L H]. split; [exact L|]. intros i Hi Pi. apply H. lia. Qed.

Section Rel.
Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Local Notation RELx := (REL W C B bnd ms pm).

Lemma rel_bt_upd t x1 x2 FC1 FC2 DL1 DL2 HP1 HP2 HL HM DP1 DP2 BC1 BC2 OL SL MC :
  RELx x1 x2 -> AG (fun i => 0 <= i < sd_elems t) FC1 FC2 ->
  RELx (bt_upd x1 t FC1 DL1 HP1 HL HM DP1 BC1 OL SL MC) (bt_upd x2 t FC2 DL2 HP2 HL HM DP2 BC2 OL SL MC).
Proof.
  intros R A. rewrite !bt_upd_setters.
  destruct t; cbn [set_tree_fc set_tree_dl set_max_code sd_elems] in *;
    [apply rel_set_l_max_code | apply rel_set_d_max_code | apply rel_set_bl_max_code];
    apply rel_set_static_len; apply rel_set_opt_len; apply rel_set_bl_count; apply rel_set_depth;
    apply rel_set_heap_max; apply rel_set_heap_len; apply rel_set_heap;
    [apply rel_set_dyn_ltree_dl; apply rel_set_dyn_ltree_fc | apply rel_set_dyn_dtree_dl; apply rel_set_dyn_dtree_fc | apply rel_set_bl_tree_dl; apply rel_set_bl_tree_fc];
    first [exact R | apply AG_aeq_lt; exact A].
Qed.

Lemma rel_fc_AG t x1 x2 : RELx x1 x2 -> tree_lens x1 -> AG (fun i => 0 <= i < sd_elems t) (tree_fc x1 t) (tree_fc x2 t).
Proof.
  intros R TLn. pose proof (tree_lens_fc x1 t TLn) as L.
  destruct t; cbn [tree_fc sd_elems tsize] in *;
    [apply (aeq_AG_lt L_CODES); [exact (r_lfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold L_CODES; lia]
    |apply (aeq_AG_lt D_CODES); [exact (r_dfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold D_CODES; lia]
    |apply (aeq_AG_lt BL_CODES); [exact (r_bfc _ _ _ _ _ _ _ _ R) | rewrite L; unfold BL_CODES; lia]].
Qed.


Record TAG (t : tree_id) (G : Z -> Prop) (x1 x2 : deflate_state) : Prop := {
  tg_fc : AG (fun i => 0 <= i < sd_elems t) (tree_fc x1 t) (tree_fc x2 t);
  tg_dl : AG G (tree_dl x1 t) (tree_dl x2 t);
  tg_mc : max_code x2 t = max_code x1 t }.

Lemma build_tree_stage t x1 x2 :
  RELx x1 x2 -> bt_pre x1 t -> tree_lens x2 ->
  RELx (build_tree x1 t) (build_tree x2 t)
  /\ TAG t (fun i => 0 <= i < sd_elems t) (build_tree x1 t) (build_tree x2 t)
  /\ (forall t' G, t' <> t -> TAG t' G x1 x2 -> TAG t' G (build_tree x1 t) (build_tree x2 t))
  /\ AG (fun i => 0 <= i < 16) (ds_bl_count (build_tree x1 t)) (ds_bl_count (build_tree x2 t))
  /\ 0 <= max_code (build_tree x1 t) t < sd_elems t
  /\ ds_opt_len (build_tree x2 t) = ds_opt_len (build_tree x1 t)
  /\ ds_static_len (build_tree x2 t) = ds_static_len (build_tree x1 t)
  /\ tree_lens (build_tree x1 t) /\ tree_lens (build_tree x2 t)
  /\ (forall t', t' <> t -> tree_fc (build_tree x1 t) t' = tree_fc x1 t' /\ tree_fc (build_tree x2 t) t' = tree_fc x2 t'
                          /\ tree_dl (build_tree x1 t) t' = tree_dl x1 t' /\ tree_dl (build_tree x2 t) t' = tree_dl x2 t').
Proof.
  intros R HP TL2. pose proof (bp_tl _ _ HP) as TL1.
  pose proof (rel_fc_AG t x1 x2 R TL1) as AFC.
  pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC.
  assert (EO : ds_opt_len x2 = ds_opt_len x1) by (symmetry; apply (clean_eq_fieldT ds_opt_len _ _ EC); reflexivity).
  assert (ES : ds_static_len x2 = ds_static_len x1) by (symmetry; apply (clean_eq_fieldT ds_static_len _ _ EC); reflexivity).
  pose proof TL1 as T1'. pose proof TL2 as T2'. unfold tree_lens in T1', T2'.
  destruct (build_tree_relU t x1 x2 TL1 TL2 (tree_fc x1 t) (tree_dl x1 t) (ds_heap x1) (ds_depth x1) (ds_bl_count x1)
              (ds_heap_len x1) (ds_heap_max x1) (max_code x1 t)
              (tree_fc x2 t) (tree_dl x2 t) (ds_heap x2) (ds_depth x2) (ds_bl_count x2)
              (ds_heap_len x2) (ds_heap_max x2) (max_code x2 t) (ds_opt_len x1) (ds_static_len x1)
              (tree_lens_fc _ _ TL1) (tree_lens_dl _ _ TL1) ltac:(tauto) ltac:(tauto) ltac:(tauto)
              (tree_lens_fc _ _ TL2) (tree_lens_dl _ _ TL2) ltac:(tauto) ltac:(tauto) ltac:(tauto)
              (bp_fc _ _ HP) (bp_dl _ _ HP) (bp_depth _ _ HP) (bp_ol _ _ HP) (bp_sl _ _ HP) AFC)
    as (FC1' & DL1' & HP1' & DP1' & BC1' & FC2' & DL2' & HP2' & DP2' & BC2' & HMf & OLf & SLf & mc & E1 & E2 & A1 & A2 & A3 & Hmc & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
  rewrite bt_upd_self in E1. rewrite <- EO, <- ES in E2. rewrite bt_upd_self in E2.
  rewrite E1, E2.
  split; [apply rel_bt_upd; [exact R | exact A1]|].
  split; [constructor; autorewrite with btupd; [exact A1 | exact A2 | reflexivity]|].
  split.
  { intros t' G Ht [F D M]. constructor.
    - rewrite !bt_tree_fc_other by exact Ht. exact F.
    - rewrite !bt_tree_dl_other by exact Ht. exact D.
    - rewrite !max_code_bt_other by exact Ht. exact M. }
  autorewrite with btupd. split; [exact A3|]. split; [exact Hmc|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply bt_tree_lens; try assumption; lia|]. split; [apply bt_tree_lens; try assumption; lia|].
  intros t' Ht. rewrite !bt_tree_fc_other, !bt_tree_dl_other by exact Ht. repeat split; reflexivity.
Qed.


Lemma td_cnt_ext : forall f L1 L2 mc n p q k mx mn x,
  0 <= n -> (forall i, 0 <= i <= mc + 1 -> L1 i = L2 i) ->
  td_cnt L1 mc f n p q k mx mn x = td_cnt L2 mc f n p q k mx mn x.
Proof.
  induction f as [|f IH]; intros L1 L2 mc n p q k mx mn x Hn HL; [reflexivity|].
  cbn [td_cnt]. destruct (Z.leb_spec n mc) as [Cn|Cn]; [|reflexivity].
  rewrite (HL (n + 1)) by lia.
  destruct (_ && _); [apply IH; [lia | exact HL]|].
  destruct (tree_counts _ _). rewrite (IH L1 L2) by (first [lia | exact HL]). reflexivity.
Qed.

Lemma TDcnt_ext : forall L1 L2 mc x, (forall i, 0 <= i <= mc + 1 -> L1 i = L2 i) -> TDcnt L1 mc x = TDcnt L2 mc x.
Proof.
  intros L1 L2 mc x HL. unfold TDcnt.
  destruct (Z_lt_le_dec mc (-1)) as [Hm|Hm].
  - unfold cnts0. destruct (L1 0 =? 0); destruct (L2 0 =? 0); replace (Z.to_nat (mc + 1)) with 0%nat by lia; reflexivity.
  - rewrite (HL 0) by lia. unfold cnts0. destruct (L2 0 =? 0); apply td_cnt_ext; first [lia | exact HL].
Qed.

Lemma scan_stage t x1 x2 :
  RELx x1 x2 -> t <> TB -> tree_lens x1 -> tree_lens x2 ->
  TAG t (fun i => 0 <= i < sd_elems t) x1 x2 ->
  0 <= max_code x1 t < sd_elems t ->
  (forall i, 0 <= i <= max_code x1 t -> 0 <= Len x1 t i <= 15) ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get (ds_bl_tree_fc x1) y /\ arr_get (ds_bl_tree_fc x1) y + 2 * (max_code x1 t + 1) < 65536) ->
  (forall y, 0 <= y < 19 -> 0 <= arr_get (ds_bl_tree_fc x2) y /\ arr_get (ds_bl_tree_fc x2) y + 2 * (max_code x1 t + 1) < 65536) ->
  let mc := max_code x1 t in
  let y1 := scan_tree x1 t mc in let y2 := scan_tree x2 t mc in
  exists b1 b2,
    y1 = set_bl_tree_fc (set_Len x1 t (mc + 1) 65535) b1 /\ y2 = set_bl_tree_fc (set_Len x2 t (mc + 1) 65535) b2
    /\ RELx y1 y2
    /\ TAG t (fun i => 0 <= i < sd_elems t \/ i = mc + 1) y1 y2
    /\ (forall t' G, t' <> t -> t' <> TB -> TAG t' G x1 x2 -> TAG t' G y1 y2)
    /\ tree_lens y1 /\ tree_lens y2
    /\ (forall i, 0 <= i <= mc -> Len y1 t i = Len x1 t i) /\ Len y1 t (mc + 1) = 65535
    /\ (forall x, 0 <= x < 19 -> 0 <= arr_get b1 x <= arr_get (ds_bl_tree_fc x1) x + 2 * (mc + 1)
                                /\ 0 <= arr_get b2 x <= arr_get (ds_bl_tree_fc x2) x + 2 * (mc + 1)).
Proof.
  intros R Ht T1 T2 [AF AD EM] Hmc HL15 HB1 HB2 mc y1 y2.
  pose proof (tree_lens_dl x1 t T1) as LD1. pose proof (tree_lens_dl x2 t T2) as LD2.
  assert (HTS : sd_elems t < tsize t /\ 39 <= 573) by (destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia).
  assert (Lb1 : arr_len (ds_bl_tree_fc x1) = 39) by (unfold tree_lens in T1; tauto).
  assert (Lb2 : arr_len (ds_bl_tree_fc x2) = 39) by (unfold tree_lens in T2; tauto).
  assert (HL15' : forall i, 0 <= i <= mc -> 0 <= Len x2 t i <= 15).
  { intros i Hi. unfold Len. rewrite <- (AG_get _ _ _ i AD) by lia. apply HL15. exact Hi. }
  destruct (scan_tree_cnt x1 (ds_bl_tree_fc x1) t mc Ht ltac:(lia) ltac:(rewrite LD1; lia) HL15 ltac:(lia)
              ltac:(intros y Hy; apply (HB1 y Hy)) ltac:(intros y Hy; apply (HB1 y Hy))) as (b1 & EX1 & Lb1' & Gb1 & EL1 & GL1).
  destruct (scan_tree_cnt x2 (ds_bl_tree_fc x2) t mc Ht ltac:(lia) ltac:(rewrite LD2; lia) HL15' ltac:(lia)
              ltac:(intros y Hy; apply (HB2 y Hy)) ltac:(intros y Hy; apply (HB2 y Hy))) as (b2 & EX2 & Lb2' & Gb2 & EL2 & GL2).
  rewrite sbf_self in EX1, EX2. subst y1 y2. rewrite EX1, EX2.
  assert (ADg : AG (fun i => 0 <= i < sd_elems t \/ i = mc + 1) (tree_dl (set_Len x1 t (mc + 1) 65535) t) (tree_dl (set_Len x2 t (mc + 1) 65535) t)).
  { unfold set_Len, set_Dad. destruct t; cbn [tree_dl set_tree_dl sd_elems] in *; dsr; apply AG_set_ext; first [exact AD | lia]. }
  assert (ELg : forall i, 0 <= i <= mc + 1 -> Len (set_Len x1 t (mc + 1) 65535) t i = Len (set_Len x2 t (mc + 1) 65535) t i).
  { intros i Hi. unfold Len. apply (AG_get _ _ _ i ADg). lia. }
  assert (Ab : aeq (fun i => i < BL_CODES) b1 b2).
  { split; [lia|]. intros i Hi Pi. rewrite Gb1, Gb2. unfold BL_CODES in Pi.
    rewrite (aeq_get _ _ _ i (r_bfc _ _ _ _ _ _ _ _ R)) by (first [lia | unfold BL_CODES; lia]).
    rewrite (TDcnt_ext (fun j => Len (set_Len x1 t (mc + 1) 65535) t j) (fun j => Len (set_Len x2 t (mc + 1) 65535) t j) mc i ELg). reflexivity. }
  exists b1, b2. split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply rel_set_bl_tree_fc; [| exact Ab]. unfold set_Len, set_Dad.
    destruct t; cbn [tree_dl set_tree_dl]; [apply rel_set_dyn_ltree_dl | apply rel_set_dyn_dtree_dl | exfalso; exact (Ht eq_refl)]; exact R. }
  split.
  { constructor.
    - rewrite !(sbf_tree_fc _ _ _ Ht), !tree_fc_set_Len. exact AF.
    - rewrite !sbf_tree_dl. exact ADg.
    - rewrite !max_code_sbf, !max_code_set_Len. exact EM. }
  split.
  { intros t' G Ht' HtB [F D M]. constructor.
    - rewrite !(sbf_tree_fc _ _ _ HtB), !tree_fc_set_Len. exact F.
    - rewrite !sbf_tree_dl, !(tree_dl_set_Len_other _ _ _ _ _ Ht'). exact D.
    - rewrite !max_code_sbf, !max_code_set_Len. exact M. }
  split; [apply tree_lens_sbf; [apply tree_lens_set_Len; exact T1 | lia]|].
  split; [apply tree_lens_sbf; [apply tree_lens_set_Len; exact T2 | lia]|].
  split; [intros i Hi; rewrite sbf_Len; apply EL1; exact Hi |]. split; [rewrite sbf_Len; exact GL1|].
  intros x Hx. rewrite Gb1, Gb2.
  pose proof (TDcnt_nonneg (fun i => Len (set_Len x1 t (mc + 1) 65535) t i) mc x).
  pose proof (TDcnt_le (fun i => Len (set_Len x1 t (mc + 1) 65535) t i) mc x ltac:(lia)).
  pose proof (TDcnt_nonneg (fun i => Len (set_Len x2 t (mc + 1) 65535) t i) mc x).
  pose proof (TDcnt_le (fun i => Len (set_Len x2 t (mc + 1) 65535) t i) mc x ltac:(lia)).
  pose proof (HB1 x Hx). pose proof (HB2 x Hx). lia.
Qed.


Lemma mb_rel : forall f x1 x2 mb, (forall c, 0 <= c < 19 -> Len x2 TB c = Len x1 TB c) -> mb <= 18 ->
  build_bl_tree_loop f x2 mb = build_bl_tree_loop f x1 mb.
Proof.
  induction f as [|f IH]; intros x1 x2 mb HL Hmb; [reflexivity|].
  cbn [build_bl_tree_loop]. destruct (Z.leb_spec 3 mb) as [Hc|Hc]; [|reflexivity].
  pose proof (bl_order_bound mb). rewrite HL by lia.
  destruct (negb _); [reflexivity|]. apply IH; [exact HL | lia].
Qed.

Lemma detect_loop1_rel : forall f x1 x2 n m, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) -> 0 <= n ->
  detect_loop1 f x2 n m = detect_loop1 f x1 n m.
Proof.
  induction f as [|f IH]; intros x1 x2 n m HF Hn; [reflexivity|].
  cbn [detect_loop1]. destruct (Z.leb_spec n 31) as [Hc|Hc]; [|reflexivity].
  rewrite HF by lia. destruct (_ && _); [reflexivity|]. apply IH; [exact HF | lia].
Qed.
Lemma detect_loop2_rel : forall f x1 x2 n, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) -> 0 <= n ->
  detect_loop2 f x2 n = detect_loop2 f x1 n.
Proof.
  induction f as [|f IH]; intros x1 x2 n HF Hn; [reflexivity|].
  cbn [detect_loop2]. destruct (Z.ltb_spec n LITERALS) as [Hc|Hc]; [|reflexivity]. unfold LITERALS in Hc.
  rewrite HF by lia. destruct (negb _); [reflexivity|]. apply IH; [exact HF | lia].
Qed.
Lemma detect_rel : forall x1 x2, (forall c, 0 <= c < 256 -> Freq x2 TL c = Freq x1 TL c) ->
  detect_data_type x2 = detect_data_type x1.
Proof.
  intros x1 x2 HF. unfold detect_data_type.
  rewrite (detect_loop1_rel 32 x1 x2) by (first [exact HF | lia]).
  destruct (detect_loop1 _ _ _ _); [reflexivity|].
  rewrite !HF by lia. rewrite (detect_loop2_rel 224 x1 x2) by (first [exact HF | lia]). reflexivity.
Qed.

Lemma X0_stage s1 s2 : RELx s1 s2 -> tree_lens s1 ->
  RELx (ov_X0 s1) (ov_X0 s2) /\ (exists c, ov_X0 s1 = set_strm s1 c /\ ov_X0 s2 = set_strm s2 c).
Proof.
  intros R T1. pose proof (rel_fc_AG TL s1 s2 R T1) as AF. cbn [sd_elems tree_fc] in AF.
  unfold ov_X0, tfb_X0. rewrite (rel_level _ _ _ _ _ _ _ _ R), (rel_strm _ _ _ _ _ _ _ _ R).
  rewrite (detect_rel s1 s2) by (intros c Hc; unfold Freq; cbn [tree_fc]; symmetry; apply (AG_get _ _ _ c AF); unfold L_CODES; lia).
  destruct (_ && _).
  - split; [apply rel_set_strm; exact R | eexists; split; reflexivity].
  - split; [exact R|]. exists (ds_strm s1). rewrite <- (rel_strm _ _ _ _ _ _ _ _ R) at 2.
    split; [destruct s1; reflexivity | destruct s2; reflexivity].
Qed.

Lemma tree_fc_set_opt_len x v t : tree_fc (set_opt_len x v) t = tree_fc x t. Proof. destruct t; reflexivity. Qed.
Lemma tree_dl_set_opt_len x v t : tree_dl (set_opt_len x v) t = tree_dl x t. Proof. destruct t; reflexivity. Qed.
Lemma max_code_set_opt_len x v t : max_code (set_opt_len x v) t = max_code x t. Proof. destruct t; reflexivity. Qed.
Lemma TAG_set_opt_len t G x1 x2 v1 v2 : TAG t G x1 x2 -> TAG t G (set_opt_len x1 v1) (set_opt_len x2 v2).
Proof. intros [F D M]. constructor; rewrite ?tree_fc_set_opt_len, ?tree_dl_set_opt_len, ?max_code_set_opt_len; assumption. Qed.

Record TPR (s1 s2 : deflate_state) : Prop := {
  tr_rel : RELx (ov_X6 s1) (ov_X6 s2);
  tr_L : TAG TL (fun i => 0 <= i < L_CODES \/ i = ds_l_max_code (ov_X6 s1) + 1) (ov_X6 s1) (ov_X6 s2);
  tr_D : TAG TD (fun i => 0 <= i < D_CODES \/ i = ds_d_max_code (ov_X6 s1) + 1) (ov_X6 s1) (ov_X6 s2);
  tr_B : TAG TB (fun i => 0 <= i < BL_CODES) (ov_X6 s1) (ov_X6 s2);
  tr_mb : ov_mb s2 = ov_mb s1 }.

Theorem tree_phase_rel s1 s2 last : RELx s1 s2 -> fb_entry s1 last -> fb_entry s2 last -> TPR s1 s2.
Proof.
  intros R FE1 FE2.
  pose proof (OP s1 last FE1) as OP1. pose proof (OP s2 last FE2) as OP2.
  pose proof (tree_phase s1 OP1) as TP1. pose proof (tree_phase s2 OP2) as TP2.
  pose proof (fe_tl _ _ FE1) as T1. pose proof (fe_tl _ _ FE2) as T2.
  destruct (X0_stage s1 s2 R T1) as [R0 (c & E01 & E02)].
  pose proof (bt_pre_X0 s1 OP1) as BP0. pose proof (bp_tl _ _ (bt_pre_X0 s2 OP2)) as T02.
  destruct (build_tree_stage TL _ _ R0 BP0 T02) as (R1 & GL1 & K1 & _ & ML1 & _ & _ & T11 & T12 & F1).
  change (build_tree (ov_X0 s1) TL) with (ov_X1 s1) in *. change (build_tree (ov_X0 s2) TL) with (ov_X1 s2) in *.
  destruct (build_tree_stage TD _ _ R1 (tp_bp1 _ TP1) T12) as (R2 & GD2 & K2 & _ & MD2 & _ & _ & T21 & T22 & F2).
  change (build_tree (ov_X1 s1) TD) with (ov_X2 s1) in *. change (build_tree (ov_X1 s2) TD) with (ov_X2 s2) in *.
  pose proof (K2 TL _ ltac:(discriminate) GL1) as GL2.
  assert (HB2 : forall x, (x = ov_X2 s1 /\ fb_entry s1 last) \/ (x = ov_X2 s2 /\ fb_entry s2 last) ->
                forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc x) y = 0).
  { intros x Hx y Hy.
    assert (EB : forall s, ds_bl_tree_fc (ov_X2 s) = ds_bl_tree_fc s -> fb_entry s last -> arr_get (ds_bl_tree_fc (ov_X2 s)) y = 0).
    { intros s Es FE. rewrite Es. destruct (fe_hist _ _ FE) as (_ & _ & HB). apply HB. unfold BL_CODES. exact Hy. }
    destruct (F2 TB ltac:(discriminate)) as (A1 & A2 & _). destruct (F1 TB ltac:(discriminate)) as (B1 & B2 & _).
    rewrite !tree_fc_TB in A1, A2, B1, B2.
    destruct Hx as [[-> FE]|[-> FE]]; apply EB; try exact FE.
    - rewrite A1, B1, E01. destruct s1; reflexivity.
    - rewrite A2, B2, E02. destruct s2; reflexivity. }
  pose proof (tp_h3 _ TP1) as EL3. pose proof (tp_lmax _ TP1) as RLm. rewrite <- EL3 in RLm. unfold L_CODES in RLm.
  destruct (scan_stage TL _ _ R2 ltac:(discriminate) T21 T22 GL2 ltac:(rewrite max_code_TL; exact RLm)
              ltac:(rewrite max_code_TL; exact (tp_h4 _ TP1))
              ltac:(intros y Hy; rewrite (HB2 _ (or_introl (conj eq_refl FE1)) y Hy); rewrite max_code_TL; lia)
              ltac:(intros y Hy; rewrite (HB2 _ (or_intror (conj eq_refl FE2)) y Hy); rewrite max_code_TL; lia))
    as (b31 & b32 & EX31 & EX32 & R3 & GL3 & K3 & T31 & T32 & EL31 & GD31 & Hb3).
  rewrite !max_code_TL in *.
  assert (D31 : scan_tree (ov_X2 s1) TL (ds_l_max_code (ov_X2 s1)) = ov_X3 s1) by reflexivity.
  assert (D32 : scan_tree (ov_X2 s2) TL (ds_l_max_code (ov_X2 s1)) = ov_X3 s2).
  { unfold ov_X3. rewrite <- !max_code_TL. rewrite (tg_mc _ _ _ _ GL2). reflexivity. }
  rewrite D31, D32 in *.
  pose proof (K3 TD _ ltac:(discriminate) ltac:(discriminate) GD2) as GD3.
  pose proof (tp_h7 _ TP1) as ED4. pose proof (tp_dmax _ TP1) as RDm. rewrite <- ED4 in RDm. unfold D_CODES in RDm.
  assert (Eb31 : ds_bl_tree_fc (ov_X3 s1) = b31) by (rewrite EX31; apply sbf_get).
  assert (Eb32 : ds_bl_tree_fc (ov_X3 s2) = b32) by (rewrite EX32; apply sbf_get).
  destruct (scan_stage TD _ _ R3 ltac:(discriminate) T31 T32 GD3 ltac:(rewrite max_code_TD; exact RDm)
              ltac:(rewrite max_code_TD; exact (tp_h8 _ TP1))
              ltac:(intros y Hy; rewrite Eb31, max_code_TD; pose proof (Hb3 y Hy); rewrite (HB2 _ (or_introl (conj eq_refl FE1)) y Hy) in *; lia)
              ltac:(intros y Hy; rewrite Eb32, max_code_TD; pose proof (Hb3 y Hy); rewrite (HB2 _ (or_intror (conj eq_refl FE2)) y Hy) in *; lia))
    as (b41 & b42 & EX41 & EX42 & R4 & GD4 & K4 & T41 & T42 & EL41 & GD41 & Hb4).
  rewrite !max_code_TD in *.
  assert (D41 : scan_tree (ov_X3 s1) TD (ds_d_max_code (ov_X3 s1)) = ov_X4 s1) by reflexivity.
  assert (D42 : scan_tree (ov_X3 s2) TD (ds_d_max_code (ov_X3 s1)) = ov_X4 s2).
  { unfold ov_X4. rewrite <- !max_code_TD. rewrite (tg_mc _ _ _ _ GD3). reflexivity. }
  rewrite D41, D42 in *.
  pose proof (K4 TL _ ltac:(discriminate) ltac:(discriminate) GL3) as GL4.
  destruct (build_tree_stage TB _ _ R4 (tp_bp4 _ TP1) T42) as (R5 & GB5 & K5 & _ & MB5 & EO5 & _ & T51 & T52 & F5).
  change (build_tree (ov_X4 s1) TB) with (ov_X5 s1) in *. change (build_tree (ov_X4 s2) TB) with (ov_X5 s2) in *.
  pose proof (K5 TL _ ltac:(discriminate) GL4) as GL5. pose proof (K5 TD _ ltac:(discriminate) GD4) as GD5.
  assert (Emb : ov_mb s2 = ov_mb s1).
  { unfold ov_mb, tfb_mb. apply mb_rel; [| lia]. intros c0 Hc. unfold Len. symmetry. apply (AG_get _ _ _ c0 (tg_dl _ _ _ _ GB5)). cbn. unfold BL_CODES. exact Hc. }
  assert (E62 : ov_X6 s2 = set_opt_len (ov_X5 s2) (wrap64 (ds_opt_len (ov_X5 s1) + 3 * (ov_mb s1 + 1) + 5 + 5 + 4))).
  { unfold ov_X6, tfb_X6. rewrite Emb, EO5. reflexivity. }
  assert (E61 : ov_X6 s1 = set_opt_len (ov_X5 s1) (wrap64 (ds_opt_len (ov_X5 s1) + 3 * (ov_mb s1 + 1) + 5 + 5 + 4))) by reflexivity.
  pose proof (proj1 (tp_h15 _ TP1)) as EL6. pose proof (proj1 (proj2 (tp_h15 _ TP1))) as ED6.
  constructor.
  - rewrite E61, E62. apply rel_set_opt_len. exact R5.
  - rewrite <- EL3. rewrite E61, E62. apply TAG_set_opt_len. exact GL5.
  - rewrite <- ED4. rewrite E61, E62. apply TAG_set_opt_len. exact GD5.
  - rewrite E61, E62. apply TAG_set_opt_len. exact GB5.
  - exact Emb.
Qed.


Lemma sbs_rel cs : forall Bq s1 s2, REL W C Bq bnd ms pm s1 s2 ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (sbs_run s1 cs))) bnd ms pm (sbs_run s1 cs) (sbs_run s2 cs).
Proof.
  induction cs as [|[v l] cs IH]; intros Bq s1 s2 R; cbn [sbs_run].
  - apply rel_Bx_same. exact R.
  - pose proof (send_bits_rel _ _ _ _ _ _ _ _ v l R) as R1.
    pose proof (IH _ _ _ R1) as R2.
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending (send_bits s1 v l))); [exact R2|].
    pose proof (send_bits_pending_mono s1 v l). pose proof (sbs_pending_mono cs (send_bits s1 v l)). lia.
Qed.

Lemma d_code_bound d : 0 <= d_code d < 30.
Proof. unfold d_code. destruct (Z.ltb d 256); apply dist_code_bound. Qed.

Lemma send_loop_pending_mono : forall f s t mc n p q k mx mn, 1 <= mn ->
  ds_pending s <= ds_pending (send_tree_loop f s t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros s t mc n p q k mx mn Hmn; [cbn [send_tree_loop]; lia|].
  rewrite (send_loop_S f) by exact Hmn. destruct (n <=? mc); [|lia]. cbv zeta.
  destruct (_ && _); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:ETC. pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
  pose proof (sbs_pending_mono (st_calls s mn q p (k + 1)) s).
  pose proof (IH (sbs_run s (st_calls s mn q p (k + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' ltac:(lia)). lia.
Qed.

Lemma send_loop_rel : forall f t mc Bq s1 s2 n p q k mx mn,
  REL W C Bq bnd ms pm s1 s2 -> 1 <= mn -> 0 <= n ->
  (forall i, 0 <= i <= mc + 1 -> Len s2 t i = Len s1 t i) ->
  (forall c, 0 <= c < 19 -> Code s2 TB c = Code s1 TB c /\ Len s2 TB c = Len s1 TB c) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s1 t i <= 15) -> (n <= mc -> 0 <= q <= 15) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (send_tree_loop f s1 t mc n p q k mx mn))) bnd ms pm
      (send_tree_loop f s1 t mc n p q k mx mn) (send_tree_loop f s2 t mc n p q k mx mn).
Proof.
  induction f as [|f IH]; intros t mc Bq s1 s2 n p q k mx mn R Hmn Hn HL HB HL15 Hq.
  - cbn [send_tree_loop]. apply rel_Bx_same. exact R.
  - rewrite !(send_loop_S f) by exact Hmn.
    destruct (Z.leb_spec n mc) as [Cn|Cn]; [| apply rel_Bx_same; exact R]. cbv zeta.
    rewrite (HL (n + 1)) by lia.
    destruct ((k + 1 <? mx) && (q =? Len s1 t (n + 1))).
    + apply IH; try assumption; try lia. intros Hn1. apply HL15. lia.
    + destruct (tree_counts q (Len s1 t (n + 1))) as [mx' mn'] eqn:ETC.
      pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
      assert (Est : st_calls s2 mn q p (k + 1) = st_calls s1 mn q p (k + 1)).
      { unfold st_calls, blc. pose proof (Hq Cn) as Rq.
        destruct (HB q ltac:(lia)) as [-> ->]. unfold REP_3_6, REPZ_3_10, REPZ_11_138.
        destruct (HB 16 ltac:(lia)) as [-> ->]. destruct (HB 17 ltac:(lia)) as [-> ->]. destruct (HB 18 ltac:(lia)) as [-> ->]. reflexivity. }
      rewrite Est.
      pose proof (sbs_rel (st_calls s1 mn q p (k + 1)) Bq s1 s2 R) as R1.
      eapply rel_Bx_merge.
      * apply IH; [exact R1 | lia | lia | | | |].
        -- intros i Hi. rewrite !sbs_Len. apply HL. exact Hi.
        -- intros c0 Hc. rewrite !sbs_Code, !sbs_Len. apply HB. exact Hc.
        -- intros i Hi. rewrite sbs_Len. apply HL15. exact Hi.
        -- intros Hn1. apply HL15. lia.
      * pose proof (sbs_pending_mono (st_calls s1 mn q p (k + 1)) s1).
        pose proof (send_loop_pending_mono f (sbs_run s1 (st_calls s1 mn q p (k + 1))) t mc (n + 1) q (Len s1 t (n + 1)) 0 mx' mn' ltac:(lia)). lia.
Qed.

Lemma send_tree_rel : forall t mc Bq s1 s2,
  REL W C Bq bnd ms pm s1 s2 -> 0 <= mc ->
  (forall i, 0 <= i <= mc + 1 -> Len s2 t i = Len s1 t i) ->
  (forall c, 0 <= c < 19 -> Code s2 TB c = Code s1 TB c /\ Len s2 TB c = Len s1 TB c) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s1 t i <= 15) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (send_tree s1 t mc))) bnd ms pm (send_tree s1 t mc) (send_tree s2 t mc).
Proof.
  intros t mc Bq s1 s2 R Hmc HL HB HL15. unfold send_tree. rewrite (HL 0) by lia.
  destruct (Len s1 t 0 =? 0); (apply send_loop_rel; [exact R | lia | lia | exact HL | exact HB | exact HL15 | intros _; apply HL15; lia]).
Qed.

Lemma send_tree_pending_mono : forall s t mc, ds_pending s <= ds_pending (send_tree s t mc).
Proof. intros. unfold send_tree. destruct (_ =? 0); apply send_loop_pending_mono; lia. Qed.

Lemma bl_calls_rel : forall n s1 s2 r, (forall c, 0 <= c < 19 -> Len s2 TB c = Len s1 TB c) -> 0 <= r ->
  bl_calls s2 r n = bl_calls s1 r n.
Proof.
  induction n as [|n IH]; intros s1 s2 r HB Hr; [reflexivity|]. cbn [bl_calls].
  pose proof (bl_order_bound r). rewrite HB by lia. rewrite (IH s1 s2) by (first [exact HB | lia]). reflexivity.
Qed.

Definition TBL (lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 : arr) : Prop :=
  (forall c, 0 <= c < L_CODES -> arr_get lfc2 c = arr_get lfc1 c /\ arr_get ldl2 c = arr_get ldl1 c)
  /\ (forall d, 0 <= d < D_CODES -> arr_get dfc2 d = arr_get dfc1 d /\ arr_get ddl2 d = arr_get ddl1 d).

Lemma sym_calls_rel : forall s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx,
  TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  sym_buf_get s2 sx = sym_buf_get s1 sx -> sym_buf_get s2 (sx + 1) = sym_buf_get s1 (sx + 1) ->
  sym_buf_get s2 (sx + 1 + 1) = sym_buf_get s1 (sx + 1 + 1) -> 0 <= sym_buf_get s1 (sx + 1 + 1) < 256 ->
  sym_calls s2 lfc2 ldl2 dfc2 ddl2 sx = sym_calls s1 lfc1 ldl1 dfc1 ddl1 sx.
Proof.
  intros * [TL TD] E0 E1 E2 Hlc. unfold sym_calls, sym_dist, sym_d0, sym_d1, sym_lc. rewrite E0, E1, E2.
  cbv zeta. destruct (_ =? 0).
  - destruct (TL (sym_buf_get s1 (sx + 1 + 1)) ltac:(unfold L_CODES; lia)) as [-> ->]. reflexivity.
  - pose proof (length_code_bound (sym_buf_get s1 (sx + 1 + 1))) as LB.
    destruct (TL (arr_get length_code_a (sym_buf_get s1 (sx + 1 + 1)) + LITERALS + 1) ltac:(unfold L_CODES, LITERALS; lia)) as [-> ->].
    match goal with |- context [d_code ?d] => pose proof (d_code_bound d) as DB; destruct (TD (d_code d) ltac:(unfold D_CODES; lia)) as [-> ->] end.
    reflexivity.
Qed.

Lemma cb_loop_pending_mono : forall f s lfc ldl dfc ddl sx, ds_pending s <= ds_pending (compress_block_loop f s lfc ldl dfc ddl sx).
Proof.
  induction f as [|f IH]; intros; [cbn [compress_block_loop]; lia|].
  rewrite cb_loop_S. cbv zeta. pose proof (sbs_pending_mono (sym_calls s lfc ldl dfc ddl sx) s).
  destruct (_ <? _); [| lia].
  pose proof (IH (sbs_run s (sym_calls s lfc ldl dfc ddl sx)) lfc ldl dfc ddl (sx + 1 + 1 + 1)). lia.
Qed.

Lemma cb_loop_rel : forall f Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx,
  REL W C Bq bnd ms pm s1 s2 -> TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  PBB s1 -> 0 <= sx -> sx mod 3 = 0 -> ds_sym_next s1 mod 3 = 0 -> sx < ds_sym_next s1 ->
  0 <= ds_lit_bufsize s1 -> ds_lit_bufsize s1 + ds_sym_next s1 <= arr_len (ds_pending_buf s1) ->
  (forall i, ds_lit_bufsize s1 <= i < ds_lit_bufsize s1 + ds_sym_next s1 -> Bq i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (compress_block_loop f s1 lfc1 ldl1 dfc1 ddl1 sx))) bnd ms pm
      (compress_block_loop f s1 lfc1 ldl1 dfc1 ddl1 sx) (compress_block_loop f s2 lfc2 ldl2 dfc2 ddl2 sx).
Proof.
  induction f as [|f IH]; intros Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx R HT PB Hsx Hm3 Hn3 Hlt Hlbs Hlen HS.
  - cbn [compress_block_loop]. apply rel_Bx_same. exact R.
  - rewrite !cb_loop_S. cbv zeta.
    assert (Hsx2 : sx + 2 < ds_sym_next s1) by (Z.to_euclidean_division_equations; lia).
    assert (EG : forall i, sx <= i <= sx + 2 -> sym_buf_get s2 i = sym_buf_get s1 i).
    { intros i Hi. unfold sym_buf_get. rewrite (rel_lbs _ _ _ _ _ _ _ _ R). symmetry.
      apply (aeq_get _ _ _ _ (r_pb _ _ _ _ _ _ _ _ R)); [lia | apply HS; lia]. }
    assert (Hlc : 0 <= sym_buf_get s1 (sx + 1 + 1) < 256) by (unfold sym_buf_get; apply PB; lia).
    rewrite (sym_calls_rel s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 sx HT) by (first [apply EG; lia | exact Hlc]).
    set (cs := sym_calls s1 lfc1 ldl1 dfc1 ddl1 sx).
    pose proof (sbs_rel cs Bq s1 s2 R) as R1.
    rewrite !sbs_sym_next. rewrite (rel_sym_next _ _ _ _ _ _ _ _ R).
    destruct (Z.ltb_spec (sx + 1 + 1 + 1) (ds_sym_next s1)) as [Cl|Cl].
    + eapply rel_Bx_merge.
      * apply (IH _ _ _ _ _ _ _ _ _ _ _ _ R1 HT); rewrite ?sbs_sym_next, ?sbs_lit_bufsize, ?sbs_pbl; try assumption; try lia.
        all: try (apply sbs_PBB; exact PB).
        all: try (Z.to_euclidean_division_equations; lia).
        all: intros i Hi; left; apply HS; exact Hi.
      * pose proof (sbs_pending_mono cs s1). pose proof (cb_loop_pending_mono f (sbs_run s1 cs) lfc1 ldl1 dfc1 ddl1 (sx + 1 + 1 + 1)). lia.
    + exact R1.
Qed.

Lemma compress_block_rel : forall Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2,
  REL W C Bq bnd ms pm s1 s2 -> TBL lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 ->
  PBB s1 -> ds_sym_next s1 mod 3 = 0 -> 0 <= ds_sym_next s1 ->
  0 <= ds_lit_bufsize s1 -> ds_lit_bufsize s1 + ds_sym_next s1 <= arr_len (ds_pending_buf s1) ->
  (forall i, ds_lit_bufsize s1 <= i < ds_lit_bufsize s1 + ds_sym_next s1 -> Bq i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (compress_block s1 lfc1 ldl1 dfc1 ddl1))) bnd ms pm
      (compress_block s1 lfc1 ldl1 dfc1 ddl1) (compress_block s2 lfc2 ldl2 dfc2 ddl2).
Proof.
  intros * R HT PB Hn3 Hsn Hlbs Hlen HS. unfold compress_block, send_code.
  rewrite (rel_sym_next _ _ _ _ _ _ _ _ R).
  destruct (proj1 HT END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)) as [-> ->].
  destruct (Z.eqb_spec (ds_sym_next s1) 0) as [Z0|NZ]; cbn [negb].
  - apply send_bits_rel. exact R.
  - pose proof (cb_loop_rel (Z.to_nat (ds_sym_next s1)) Bq s1 s2 lfc1 ldl1 dfc1 ddl1 lfc2 ldl2 dfc2 ddl2 0 R HT PB
                  ltac:(lia) ltac:(reflexivity) Hn3 ltac:(lia) Hlbs Hlen HS) as R1.
    eapply rel_Bx_merge; [apply send_bits_rel; exact R1|].
    pose proof (cb_loop_pending_mono (Z.to_nat (ds_sym_next s1)) s1 lfc1 ldl1 dfc1 ddl1 0).
    pose proof (send_bits_pending_mono (compress_block_loop (Z.to_nat (ds_sym_next s1)) s1 lfc1 ldl1 dfc1 ddl1 0) (arr_get lfc1 END_BLOCK) (arr_get ldl1 END_BLOCK)). lia.
Qed.

Lemma compress_block_pending_mono s lfc ldl dfc ddl : ds_pending s <= ds_pending (compress_block s lfc ldl dfc ddl).
Proof.
  unfold compress_block, send_code. destruct (negb _).
  - pose proof (cb_loop_pending_mono (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0).
    pose proof (send_bits_pending_mono (compress_block_loop (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0) (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)). lia.
  - pose proof (send_bits_pending_mono s (arr_get lfc END_BLOCK) (arr_get ldl END_BLOCK)). lia.
Qed.


Lemma aeq_blit2 (P Q : Z -> Prop) d1 d2 sr1 sr2 dofs sofs n :
  aeq P d1 d2 -> aeq Q sr1 sr2 -> 0 <= sofs -> sofs + n <= arr_len sr1 -> (forall k, 0 <= k < n -> Q (sofs + k)) ->
  aeq (fun j => P j \/ dofs <= j < dofs + n) (arr_blit d1 dofs sr1 sofs n) (arr_blit d2 dofs sr2 sofs n).
Proof.
  intros [L H] [LS HS] Hs Hsn SP. split; [rewrite !arr_len_blit; exact L|].
  intros j Hj Pj. rewrite arr_len_blit in Hj. rewrite !arr_get_blit. unfold arr_inb. rewrite <- L.
  replace ((0 <=? j) && (j <? arr_len d1)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec dofs j); destruct (Z.ltb_spec j (dofs + Z.max 0 n)); cbn [andb].
  - apply HS; [lia|]. replace (sofs + (j - dofs)) with (sofs + (j - dofs)) by lia. apply SP. lia.
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
Qed.

Lemma bi_windup_pending_mono s : ds_pending s <= ds_pending (bi_windup s) <= ds_pending s + 2.
Proof. rewrite bi_windup_pending. destruct (_ <? _); [|destruct (_ <? _)]; lia. Qed.

Lemma pend_set_pending s v : ds_pending (set_pending s v) = v. Proof. reflexivity. Qed.
Lemma pend_set_pending_buf s a : ds_pending (set_pending_buf s a) = ds_pending s. Proof. reflexivity. Qed.

Lemma tr_stored_block_pending s buf len last :
  ds_pending (tr_stored_block s buf len last) = ds_pending (bi_windup (send_bits s (Z.shiftl STORED_BLOCK 1 + last) 3)) + 4 + len.
Proof.
  unfold tr_stored_block. destruct (negb _); [destruct buf|]; rewrite pend_set_pending, ?pend_set_pending_buf, !put_short_pending; lia.
Qed.

Lemma tr_stored_block_rel0 : forall Bq s1 s2 buf len last,
  REL W C Bq bnd ms pm s1 s2 -> 0 <= len -> (buf = None -> len = 0) ->
  (forall off, buf = Some off -> len <> 0 -> 0 <= off /\ off + len <= arr_len (ds_window s1) /\ forall i, off <= i < off + len -> W i) ->
  REL W C (Bx Bq (ds_pending s1) (ds_pending (tr_stored_block s1 buf len last))) bnd ms pm
      (tr_stored_block s1 buf len last) (tr_stored_block s2 buf len last).
Proof.
  intros Bq s1 s2 buf len last R Hlen Hnone Hbuf. rewrite tr_stored_block_pending. unfold tr_stored_block.
  pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl STORED_BLOCK 1 + last) 3 R) as R1.
  pose proof (send_bits_pending_mono s1 (Z.shiftl STORED_BLOCK 1 + last) 3) as P1.
  set (a1 := send_bits s1 _ 3) in *. set (a2 := send_bits s2 _ 3) in *.
  assert (Wa1 : ds_window a1 = ds_window s1) by (subst a1; apply (k_send_bits ds_window true true keeps_window eq_refl)).
  clearbody a1 a2.
  pose proof (bi_windup_rel _ _ _ _ _ _ _ _ R1) as R2. pose proof (bi_windup_pending_mono a1) as P2.
  set (b1 := bi_windup a1) in *. set (b2 := bi_windup a2) in *.
  assert (Wb1 : ds_window b1 = ds_window s1) by (subst b1; rewrite (k_bi_windup ds_window true true keeps_window eq_refl); exact Wa1).
  clearbody b1 b2.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R2 ltac:(lia)) as R2'. clear R1 R2.
  pose proof (put_short_rel _ _ _ _ _ _ _ _ (wrap16 len) R2') as R3.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R3 ltac:(rewrite put_short_pending; lia)) as R3'. clear R3.
  pose proof (put_short_rel _ _ _ _ _ _ _ _ (wrap16 (Z.lnot len)) R3') as R4.
  pose proof (rel_Bx_merge _ _ _ _ _ _ _ _ _ _ _ R4 ltac:(rewrite !put_short_pending; lia)) as R4'. clear R4 R3' R2'.
  rewrite !put_short_pending in R4'. replace (ds_pending b1 + 2 + 2) with (ds_pending b1 + 4) in R4' by lia.
  set (c1 := put_short (put_short b1 _) _) in *. set (c2 := put_short (put_short b2 _) _) in *.
  assert (Pc : ds_pending c1 = ds_pending b1 + 4) by (subst c1; rewrite !put_short_pending; lia).
  pose proof (rel_pending _ _ _ _ _ _ _ _ R4') as Epc.
  assert (Ew : aeq W (ds_window c1) (ds_window c2)) by exact (r_win _ _ _ _ _ _ _ _ R4').
  assert (Ew1 : ds_window c1 = ds_window s1).
  { subst c1. rewrite !(k_put_short ds_window true true keeps_window eq_refl), <- Wb1. reflexivity. }
  clearbody c1 c2.
  destruct (Z.eqb_spec len 0) as [L0|L0]; cbn [negb].
  - rewrite Epc, L0, Z.add_0_r. apply rel_set_pending. exact R4'.
  - destruct buf as [off|]; [| exfalso; exact (L0 (Hnone eq_refl))].
    destruct (Hbuf off eq_refl L0) as (Ho & Hol & HW). rewrite !pend_set_pending_buf. rewrite Epc.
    rewrite <- (rel_pending_out _ _ _ _ _ _ _ _ R4') at 1 || idtac.
    replace (ds_window c2) with (ds_window c2) by reflexivity.
    apply rel_set_pending.
    pose proof (aeq_blit2 (Bx Bq (ds_pending s1) (ds_pending b1 + 4)) W _ _ _ _ (ds_pending c1) off len
                  (r_pb _ _ _ _ _ _ _ _ R4') Ew Ho ltac:(rewrite Ew1; exact Hol) ltac:(intros k Hk; apply HW; lia)) as AB.
    eapply rel_set_pending_buf; [exact R4'|].
    eapply aeq_mono; [exact AB|].
    intros i. unfold Bx. rewrite Pc. intros [X|X]; [left; left; exact X |].
    destruct (Z_lt_le_dec i (ds_pending b1 + 4)); [left; right; lia | right; lia].
Qed.


Lemma init_block_rel : forall Bq s1 s2, REL W C Bq bnd ms pm s1 s2 -> REL W C Bq bnd ms pm (init_block s1) (init_block s2).
Proof.
  intros Bq s1 s2 R. unfold init_block, set_Freq. cbn [tree_fc set_tree_fc]. dsr.
  apply rel_set_matches. apply rel_set_sym_next. apply rel_set_static_len. apply rel_set_opt_len.
  apply rel_set_dyn_ltree_fc; [| apply aeq_set_keep; eapply aeq_mono; [apply aeq_fill; exact (r_lfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_bl_tree_fc; [| eapply aeq_mono; [apply aeq_fill; exact (r_bfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_dyn_dtree_fc; [| eapply aeq_mono; [apply aeq_fill; exact (r_dfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
  apply rel_set_dyn_ltree_fc; [exact R | eapply aeq_mono; [apply aeq_fill; exact (r_lfc _ _ _ _ _ _ _ _ R) | intros i Hi; left; exact Hi]].
Qed.


Lemma trees8_inv a b : trees8 b = trees8 a ->
  (forall t, tree_fc b t = tree_fc a t /\ tree_dl b t = tree_dl a t) /\ ds_l_max_code b = ds_l_max_code a /\ ds_d_max_code b = ds_d_max_code a.
Proof.
  intros E. unfold trees8 in E. injection E as E1 E2 E3 E4 E5 E6 E7 E8.
  split; [| split; assumption]. intros [| |]; cbn [tree_fc tree_dl]; split; assumption.
Qed.

Lemma trees8_fc a b t : trees8 b = trees8 a -> tree_fc b t = tree_fc a t.
Proof. intros E. exact (proj1 (proj1 (trees8_inv a b E) t)). Qed.
Lemma trees8_dl a b t : trees8 b = trees8 a -> tree_dl b t = tree_dl a t.
Proof. intros E. exact (proj2 (proj1 (trees8_inv a b E) t)). Qed.

Lemma l_max_code_send_bits x v l : ds_l_max_code (send_bits x v l) = ds_l_max_code x.
Proof. exact (proj1 (proj2 (trees8_inv _ _ (trees8_send_bits x v l)))). Qed.
Lemma d_max_code_send_bits x v l : ds_d_max_code (send_bits x v l) = ds_d_max_code x.
Proof. exact (proj2 (proj2 (trees8_inv _ _ (trees8_send_bits x v l)))). Qed.

Definition SYMB (B0 : Z -> Prop) (s : deflate_state) : Prop :=
  forall i, ds_lit_bufsize s <= i < ds_lit_bufsize s + ds_sym_next s -> B0 i.
End Rel.

Definition FLUSH_BLOCK_REL : Prop :=
  forall W C B bnd ms pm s1 s2 last,
    REL W C B bnd ms pm s1 s2 -> fb_entry s1 last -> fb_entry s2 last ->
    SYMB B s1 -> (forall i, i < WHI s1 -> W i) -> ds_block_start s1 <= ds_strstart s1 ->
    let s1' := tr_flush_block s1 (fb_buf s1) (fb_len s1) last in
    let s2' := tr_flush_block s2 (fb_buf s2) (fb_len s2) last in
    REL W C (Bx B 0 (ds_pending s1')) bnd ms pm s1' s2'.

Lemma send_loop_keep : forall f s t mc n p q k mx mn, 1 <= mn ->
  (PBB s -> PBB (send_tree_loop f s t mc n p q k mx mn))
  /\ arr_len (ds_pending_buf (send_tree_loop f s t mc n p q k mx mn)) = arr_len (ds_pending_buf s)
  /\ ds_sym_next (send_tree_loop f s t mc n p q k mx mn) = ds_sym_next s
  /\ ds_lit_bufsize (send_tree_loop f s t mc n p q k mx mn) = ds_lit_bufsize s.
Proof.
  induction f as [|f IH]; intros s t mc n p q k mx mn Hmn; [cbn [send_tree_loop]; split; [intros H; exact H|]; repeat split; reflexivity|].
  rewrite send_loop_S by exact Hmn. destruct (n <=? mc); [| split; [intros H; exact H|]; repeat split; reflexivity]. cbv zeta.
  destruct (_ && _); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:ETC. pose proof (tree_counts_range _ _ _ _ ETC) as [_ Hmn'].
  destruct (IH (sbs_run s (st_calls s mn q p (k + 1))) t mc (n + 1) q (Len s t (n + 1)) 0 mx' mn' ltac:(lia)) as (A1 & A2 & A3 & A4).
  rewrite A2, A3, A4, sbs_pbl, sbs_sym_next, sbs_lit_bufsize.
  split; [intros PB; apply A1; apply sbs_PBB; exact PB|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma send_tree_keep : forall s t mc,
  (PBB s -> PBB (send_tree s t mc)) /\ arr_len (ds_pending_buf (send_tree s t mc)) = arr_len (ds_pending_buf s)
  /\ ds_sym_next (send_tree s t mc) = ds_sym_next s /\ ds_lit_bufsize (send_tree s t mc) = ds_lit_bufsize s.
Proof. intros. unfold send_tree. destruct (_ =? 0); apply send_loop_keep; lia. Qed.

Section Flush.
Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
Variable last : Z.
Hypothesis R : REL W C B bnd ms pm s1 s2.
Hypothesis FE1 : fb_entry s1 last.
Hypothesis FE2 : fb_entry s2 last.
Hypothesis HS : SYMB B s1.
Hypothesis HW : forall i, i < WHI s1 -> W i.
Hypothesis Hbs : ds_block_start s1 <= ds_strstart s1.

Let TP1 : TPF s1 := tree_phase s1 (OP s1 last FE1).
Let TR : TPR W C B bnd ms pm s1 s2 := tree_phase_rel W C B bnd ms pm s1 s2 last R FE1 FE2.
Local Notation X61 := (ov_X6 s1).
Local Notation X62 := (ov_X6 s2).

Lemma X6_facts :
  ds_pending X61 = 0 /\ ds_pending_buf X61 = ds_pending_buf s1 /\ ds_sym_next X61 = ds_sym_next s1
  /\ ds_lit_bufsize X61 = ds_lit_bufsize s1 /\ ds_window X61 = ds_window s1
  /\ PBB X61 /\ ds_sym_next s1 = 3 * nsym s1 /\ 0 <= nsym s1 /\ 128 <= ds_lit_bufsize s1
  /\ arr_len (ds_pending_buf s1) = ds_lit_bufsize s1 * 4 /\ ds_sym_next s1 <= 3 * (ds_lit_bufsize s1 - 1)
  /\ arr_len (ds_window s1) = 2 * ds_w_size s1 /\ 0 <= ds_strstart s1 <= 2 * ds_w_size s1
  /\ 0 <= ds_strstart s1 - ds_block_start s1 < 2 ^ 32 /\ ds_w_size s1 <= 32768.
Proof.
  pose proof (nt_view_facts _ _ (tp_nt6 _ TP1)) as (Epb & Epd & _ & _ & Elbs & Esn & _ & _ & _ & _ & _ & _ & Ewin & _).
  pose proof FE1 as F. destruct F.
  rewrite Epd, Epb, Esn, Elbs, Ewin.
  split; [exact fe_pending|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [unfold PBB; rewrite Epb; exact fe_pbb|]. split; [exact fe_sn|]. split; [lia|]. split; [lia|]. split; [exact fe_pbl|].
  split; [lia|]. split; [exact fe_wl|]. split; [exact fe_str|]. split; [exact fe_diff | lia].
Qed.

Lemma sd_elems_TL : sd_elems TL = L_CODES. Proof. reflexivity. Qed.
Lemma sd_elems_TD : sd_elems TD = D_CODES. Proof. reflexivity. Qed.
Lemma sd_elems_TB : sd_elems TB = BL_CODES. Proof. reflexivity. Qed.
Lemma Code_eq x t i : Code x t i = arr_get (tree_fc x t) i. Proof. reflexivity. Qed.

Lemma tfb_branch_2 X buf len : (tfb_branch X buf len =? 2) = true -> exists off, buf = Some off.
Proof.
  unfold tfb_branch. cbv zeta. destruct buf as [off|]; [intros _; exists off; reflexivity|].
  cbn [is_some]. rewrite andb_false_r.
  match goal with |- ((if ?c then 0 else 1) =? 2) = true -> _ => destruct c end; cbn; intros HH; discriminate HH.
Qed.

Lemma Len_tr a b t i : trees8 b = trees8 a -> Len b t i = Len a t i.
Proof. intros E. unfold Len. rewrite (trees8_dl _ _ t E). reflexivity. Qed.
Lemma Code_tr a b t i : trees8 b = trees8 a -> Code b t i = Code a t i.
Proof. intros E. unfold Code. rewrite (trees8_fc _ _ t E). reflexivity. Qed.

Lemma X6_agree :
  (forall i, 0 <= i <= ds_l_max_code X61 + 1 -> Len X62 TL i = Len X61 TL i)
  /\ (forall i, 0 <= i <= ds_d_max_code X61 + 1 -> Len X62 TD i = Len X61 TD i)
  /\ (forall c, 0 <= c < 19 -> Code X62 TB c = Code X61 TB c /\ Len X62 TB c = Len X61 TB c)
  /\ TBL (tree_fc X61 TL) (tree_dl X61 TL) (tree_fc X61 TD) (tree_dl X61 TD)
         (tree_fc X62 TL) (tree_dl X62 TL) (tree_fc X62 TD) (tree_dl X62 TD)
  /\ ds_l_max_code X62 = ds_l_max_code X61 /\ ds_d_max_code X62 = ds_d_max_code X61
  /\ (forall i, 0 <= i <= ds_l_max_code X61 -> 0 <= Len X61 TL i <= 15)
  /\ (forall i, 0 <= i <= ds_d_max_code X61 -> 0 <= Len X61 TD i <= 15)
  /\ 0 <= ds_l_max_code X61 < L_CODES /\ 0 <= ds_d_max_code X61 < D_CODES /\ 2 <= ov_mb s1 <= 18.
Proof.
  pose proof TR as [R6 [FL DL ML] [FD DD MD] [FB DB MB] Emb].
  pose proof (tp_lmax _ TP1) as RLm. pose proof (tp_dmax _ TP1) as RDm.
  rewrite !max_code_TL in ML. rewrite !max_code_TD in MD.
  rewrite sd_elems_TL in FL. rewrite sd_elems_TD in FD. rewrite sd_elems_TB in FB. unfold TBL.
  split; [intros i Hi; rewrite !Len_eq; symmetry; apply (AG_get _ _ _ i DL); unfold L_CODES in *; lia|].
  split; [intros i Hi; rewrite !Len_eq; symmetry; apply (AG_get _ _ _ i DD); unfold D_CODES in *; lia|].
  split; [intros c Hc; rewrite !Code_eq, !Len_eq; split; symmetry; [apply (AG_get _ _ _ c FB) | apply (AG_get _ _ _ c DB)]; unfold BL_CODES; lia|].
  split.
  { split.
    - intros c Hc. split; symmetry; [apply (AG_get _ _ _ c FL) | apply (AG_get _ _ _ c DL)]; lia.
    - intros d Hd. split; symmetry; [apply (AG_get _ _ _ d FD) | apply (AG_get _ _ _ d DD)]; lia. }
  split; [exact ML|]. split; [exact MD|]. split; [exact (tp_LD _ TP1)|]. split; [exact (tp_DD _ TP1)|].
  split; [exact RLm|]. split; [exact RDm | exact (tp_mb _ TP1)].
Qed.

Lemma emit_rel :
  let buf := fb_buf s1 in let len := fb_len s1 in let mb := ov_mb s1 in let d := tfb_branch X61 buf len in
  REL W C (Bx B 0 (ds_pending (tfb_emit d X61 mb buf len last))) bnd ms pm
      (tfb_emit d X61 mb buf len last) (tfb_emit d X62 mb buf len last).
Proof.
  intros buf len mb d. pose proof TR as [R6 _ _ _ Emb].
  pose proof X6_facts as (P0 & Epb & Esn & Elbs & Ewin & PB6 & Hsn3 & Hns & Hlbs & Hpbl & Hsnb & Hwl & Hstr & Hdiff & Hws).
  pose proof X6_agree as (AL & AD & AB & HT & EML & EMD & L15 & D15 & RLm & RDm & Rmb).
  assert (HSX : forall Bq : Z -> Prop, (forall i, B i -> Bq i) ->
            forall i, ds_lit_bufsize X61 <= i < ds_lit_bufsize X61 + ds_sym_next X61 -> Bq i).
  { intros Bq HBq i Hi. apply HBq. apply HS. rewrite <- Elbs, <- Esn. exact Hi. }
  unfold tfb_emit. replace (Bx B 0) with (Bx B (ds_pending X61)) by (rewrite P0; reflexivity).
  destruct (d =? 2) eqn:Ed.
  {
    destruct (tfb_branch_2 _ _ _ Ed) as [off Eoff].
    apply tr_stored_block_rel0; [exact R6 | subst len; unfold fb_len; apply wrap64_range | intros HH; rewrite Eoff in HH; discriminate HH |].
    intros off' Eo' Hl0. rewrite Eoff in Eo'. injection Eo' as <-.
    subst buf len. unfold fb_buf, fb_len in *. destruct (Z.leb_spec 0 (ds_block_start s1)) as [Hb0|Hb0]; [| discriminate Eoff].
    injection Eoff as Eoff. rewrite wrap32_mod, Z.mod_small in Eoff by lia. subst off.
    rewrite wrap64_mod, Z.mod_small by lia. rewrite Ewin, Hwl.
    split; [lia|]. split; [lia|]. intros i Hi. apply HW. unfold WHI. pose proof (fe_look _ _ FE1). lia. }
  destruct (d =? 0) eqn:Ed0.
  {
    pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl STATIC_TREES 1 + last) 3 R6) as R7.
    eapply rel_Bx_merge.
    - apply (compress_block_rel W C B bnd ms pm (Bx B (ds_pending X61) (ds_pending (send_bits X61 (Z.shiftl STATIC_TREES 1 + last) 3)))); try exact R7.
      + split; intros; split; reflexivity.
      + apply send_bits_PBB. exact PB6.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), Esn, Hsn3. rewrite Z.mul_comm. apply Z_mod_mult.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), Esn. lia.
      + rewrite (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl), Elbs. lia.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl), sb_pbl, Esn, Elbs, Epb. lia.
      + rewrite (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl).
        apply HSX. intros i Hi. left. exact Hi.
    - pose proof (send_bits_pending_mono X61 (Z.shiftl STATIC_TREES 1 + last) 3).
      pose proof (compress_block_pending_mono (send_bits X61 (Z.shiftl STATIC_TREES 1 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl). lia. }
  cbv zeta. rewrite !l_max_code_send_bits, !d_max_code_send_bits, EML, EMD.
  set (Y1 := send_bits X61 (Z.shiftl DYN_TREES 1 + last) 3). set (Y2 := send_bits X62 (Z.shiftl DYN_TREES 1 + last) 3).
  pose proof (send_bits_rel _ _ _ _ _ _ _ _ (Z.shiftl DYN_TREES 1 + last) 3 R6) as R7. fold Y1 Y2 in R7.
  pose proof (send_bits_pending_mono X61 (Z.shiftl DYN_TREES 1 + last) 3) as M7. fold Y1 in M7.
  assert (T71 : trees8 Y1 = trees8 X61) by (subst Y1; apply trees8_send_bits).
  assert (T72 : trees8 Y2 = trees8 X62) by (subst Y2; apply trees8_send_bits).
  assert (STEP : forall (Bq : Z -> Prop) (a1 a2 : deflate_state) (f : deflate_state -> deflate_state),
            REL W C Bq bnd ms pm a1 a2 ->
            REL W C (Bx Bq (ds_pending a1) (ds_pending (f a1))) bnd ms pm (f a1) (f a2) ->
            True) by (intros; exact I).
  pose proof (l_max_code_send_bits X61 (Z.shiftl DYN_TREES 1 + last) 3) as ELY. fold Y1 in ELY.
  unfold send_all_trees.
  set (lc := ds_l_max_code X61 + 1). set (dc := ds_d_max_code X61 + 1).
  assert (E4 : forall Y, trees8 Y = trees8 X61 \/ trees8 Y = trees8 X62 ->
            send_all_trees_loop 19 (send_bits (send_bits (send_bits Y (lc - 257) 5) (dc - 1) 5) (mb + 1 - 4) 4) (mb + 1) 0
            = sbs_run Y ([(lc - 257, 5); (dc - 1, 5); (mb + 1 - 4, 4)] ++ bl_calls X61 0 (Z.to_nat (mb + 1)))).
  { intros Y TY. rewrite send_all_loop_fuel by lia. rewrite Z.sub_0_r. rewrite sbs_run_app. cbn [sbs_run].
    f_equal. apply bl_calls_rel; [| lia]. intros c Hc.
    rewrite !(Len_tr _ _ _ _ (trees8_send_bits _ _ _)).
    destruct TY as [TY|TY]; rewrite (Len_tr _ _ _ _ TY); [reflexivity | apply AB; exact Hc]. }
  rewrite (E4 Y1 (or_introl T71)), (E4 Y2 (or_intror T72)).
  set (cs4 := [(lc - 257, 5); (dc - 1, 5); (mb + 1 - 4, 4)] ++ bl_calls X61 0 (Z.to_nat (mb + 1))).
  pose proof (sbs_rel W C bnd ms pm cs4 _ _ _ R7) as R8. pose proof (sbs_pending_mono cs4 Y1) as M8.
  assert (T81 : trees8 (sbs_run Y1 cs4) = trees8 X61) by (rewrite trees8_sbs_run; exact T71).
  assert (T82 : trees8 (sbs_run Y2 cs4) = trees8 X62) by (rewrite trees8_sbs_run; exact T72).
  set (Z1 := sbs_run Y1 cs4) in *. set (Z2 := sbs_run Y2 cs4) in *.
  assert (R9 := send_tree_rel W C bnd ms pm TL (lc - 1) _ Z1 Z2 R8 ltac:(subst lc; lia)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T81), (Len_tr _ _ _ _ T82); apply AL; subst lc; lia)
            ltac:(intros c Hc; rewrite (Code_tr _ _ _ _ T81), (Code_tr _ _ _ _ T82), (Len_tr _ _ _ _ T81), (Len_tr _ _ _ _ T82); apply AB; exact Hc)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T81); apply L15; subst lc; lia)).
  pose proof (send_tree_pending_mono Z1 TL (lc - 1)) as M9.
  assert (T91 : trees8 (send_tree Z1 TL (lc - 1)) = trees8 X61) by (rewrite trees8_send_tree; exact T81).
  assert (T92 : trees8 (send_tree Z2 TL (lc - 1)) = trees8 X62) by (rewrite trees8_send_tree; exact T82).
  set (V1 := send_tree Z1 TL (lc - 1)) in *. set (V2 := send_tree Z2 TL (lc - 1)) in *.
  assert (R10 := send_tree_rel W C bnd ms pm TD (dc - 1) _ V1 V2 R9 ltac:(subst dc; lia)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T91), (Len_tr _ _ _ _ T92); apply AD; subst dc; lia)
            ltac:(intros c Hc; rewrite (Code_tr _ _ _ _ T91), (Code_tr _ _ _ _ T92), (Len_tr _ _ _ _ T91), (Len_tr _ _ _ _ T92); apply AB; exact Hc)
            ltac:(intros i Hi; rewrite (Len_tr _ _ _ _ T91); apply D15; subst dc; lia)).
  pose proof (send_tree_pending_mono V1 TD (dc - 1)) as M10.
  assert (T101 : trees8 (send_tree V1 TD (dc - 1)) = trees8 X61) by (rewrite trees8_send_tree; exact T91).
  assert (T102 : trees8 (send_tree V2 TD (dc - 1)) = trees8 X62) by (rewrite trees8_send_tree; exact T92).
  set (U1 := send_tree V1 TD (dc - 1)) in *. set (U2 := send_tree V2 TD (dc - 1)) in *.
  destruct (send_tree_keep V1 TD (dc - 1)) as (KU1 & KU2 & KU3 & KU4). fold U1 in KU1, KU2, KU3, KU4.
  destruct (send_tree_keep Z1 TL (lc - 1)) as (KV1 & KV2 & KV3 & KV4). fold V1 in KV1, KV2, KV3, KV4.
  assert (KZ : PBB Z1 /\ arr_len (ds_pending_buf Z1) = arr_len (ds_pending_buf X61) /\ ds_sym_next Z1 = ds_sym_next X61 /\ ds_lit_bufsize Z1 = ds_lit_bufsize X61).
  { subst Z1 Y1. rewrite sbs_pbl, sbs_sym_next, sbs_lit_bufsize, sb_pbl,
      (k_send_bits ds_sym_next true false keeps_sym_next eq_refl), (k_send_bits ds_lit_bufsize true true keeps_lit_bufsize eq_refl).
    split; [apply sbs_PBB; apply send_bits_PBB; exact PB6 | repeat split; reflexivity]. }
  destruct KZ as (KZ1 & KZ2 & KZ3 & KZ4).
  rewrite <- (tree_fc_TL U1), <- (tree_dl_TL U1), <- (tree_fc_TD U1), <- (tree_dl_TD U1).
  rewrite <- (tree_fc_TL U2), <- (tree_dl_TL U2), <- (tree_fc_TD U2), <- (tree_dl_TD U2).
  rewrite (trees8_fc _ _ TL T101), (trees8_dl _ _ TL T101), (trees8_fc _ _ TD T101), (trees8_dl _ _ TD T101).
  rewrite (trees8_fc _ _ TL T102), (trees8_dl _ _ TL T102), (trees8_fc _ _ TD T102), (trees8_dl _ _ TD T102).
  assert (R10' : REL W C (Bx B (ds_pending X61) (ds_pending U1)) bnd ms pm U1 U2).
  { apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending Y1)); [| lia].
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending Z1)); [| lia].
    apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending V1)); [| lia]. exact R10. }
  eapply rel_Bx_merge.
  - apply (compress_block_rel W C B bnd ms pm _ U1 U2); try exact R10'; try exact HT.
    + apply KU1, KV1. exact KZ1.
    + rewrite KU3, KV3, KZ3, Esn, Hsn3. rewrite Z.mul_comm. apply Z_mod_mult.
    + rewrite KU3, KV3, KZ3, Esn. lia.
    + rewrite KU4, KV4, KZ4, Elbs. lia.
    + rewrite KU2, KV2, KZ2, KU3, KV3, KZ3, KU4, KV4, KZ4, Esn, Elbs, Epb. lia.
    + rewrite KU3, KV3, KZ3, KU4, KV4, KZ4. apply HSX. intros i Hi. unfold Bx. left. exact Hi.
  - pose proof (compress_block_pending_mono U1 (tree_fc X61 TL) (tree_dl X61 TL) (tree_fc X61 TD) (tree_dl X61 TD)). lia.
Qed.

Lemma keeps_pending : keeps ds_pending false true.
Proof.
  constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end;
  match goal with ss : deflate_state |- _ => destruct ss; reflexivity end.
Qed.
Lemma init_block_pending e : ds_pending (init_block e) = ds_pending e.
Proof. exact (k_init_block ds_pending false true keeps_pending eq_refl e). Qed.

Lemma fin_rel : forall Bq e1 e2, REL W C Bq bnd ms pm e1 e2 ->
  REL W C (Bx Bq (ds_pending e1) (ds_pending (tfb_fin last e1))) bnd ms pm (tfb_fin last e1) (tfb_fin last e2).
Proof.
  intros Bq e1 e2 Re. unfold tfb_fin. cbv zeta.
  pose proof (init_block_rel W C bnd ms pm Bq e1 e2 Re) as Ri.
  pose proof (init_block_pending e1) as Ep.
  destruct (negb (last =? 0)).
  - rewrite <- Ep. apply bi_windup_rel. exact Ri.
  - rewrite <- Ep at 1. apply rel_Bx_same. exact Ri.
Qed.

Lemma fin_pending_mono e : ds_pending e <= ds_pending (tfb_fin last e) <= ds_pending e + 2.
Proof.
  unfold tfb_fin. cbv zeta. destruct (negb (last =? 0)).
  - pose proof (bi_windup_pending_mono (init_block e)). rewrite init_block_pending in H. exact H.
  - rewrite init_block_pending. lia.
Qed.

Lemma send_all_trees_loop_pending_mono f : forall s bc r, ds_pending s <= ds_pending (send_all_trees_loop f s bc r).
Proof.
  induction f as [|f IH]; intros; cbn [send_all_trees_loop]; [lia|].
  destruct (r <? bc); [|lia].
  eapply Z.le_trans; [| apply IH]. apply (proj1 (send_bits_pending_mono _ _ _)).
Qed.

Lemma tfb_emit_pending_mono d X mb buf len : 0 <= len ->
  ds_pending X <= ds_pending (tfb_emit d X mb buf len last).
Proof.
  intros Hlen. unfold tfb_emit. destruct (d =? 2).
  { rewrite tr_stored_block_pending.
    pose proof (send_bits_pending_mono X (Z.shiftl STORED_BLOCK 1 + last) 3).
    pose proof (bi_windup_pending_mono (send_bits X (Z.shiftl STORED_BLOCK 1 + last) 3)). lia. }
  destruct (d =? 0).
  { eapply Z.le_trans; [apply (proj1 (send_bits_pending_mono X (Z.shiftl STATIC_TREES 1 + last) 3))|].
    apply compress_block_pending_mono. }
  cbv zeta. unfold send_all_trees.
  eapply Z.le_trans; [apply (proj1 (send_bits_pending_mono X (Z.shiftl DYN_TREES 1 + last) 3))|].
  eapply Z.le_trans; [| apply compress_block_pending_mono].
  eapply Z.le_trans; [| apply send_tree_pending_mono].
  eapply Z.le_trans; [| apply send_tree_pending_mono].
  eapply Z.le_trans; [| apply send_all_trees_loop_pending_mono].
  eapply Z.le_trans; [| apply (proj1 (send_bits_pending_mono _ _ _))].
  eapply Z.le_trans; [| apply (proj1 (send_bits_pending_mono _ _ _))].
  apply (proj1 (send_bits_pending_mono _ _ _)).
Qed.
End Flush.

Theorem flush_block_rel : FLUSH_BLOCK_REL.
Proof.
  intros W C B bnd ms pm s1 s2 last R FE1 FE2 HS HW Hbs. cbv zeta.
  pose proof (tree_phase_rel W C B bnd ms pm s1 s2 last R FE1 FE2) as [R6 _ _ _ Emb].
  rewrite !tr_flush_block_eq. unfold tfb_pre.
  replace (0 <? ds_level s1) with true by (symmetry; apply Z.ltb_lt; pose proof (fe_level _ _ FE1); lia).
  replace (0 <? ds_level s2) with true by (symmetry; apply Z.ltb_lt; pose proof (fe_level _ _ FE2); lia).
  cbv zeta.
  change (tfb_X5 (tfb_X0 s1)) with (ov_X5 s1). change (tfb_X5 (tfb_X0 s2)) with (ov_X5 s2).
  change (tfb_mb (ov_X5 s1)) with (ov_mb s1). change (tfb_mb (ov_X5 s2)) with (ov_mb s2).
  change (tfb_X6 (ov_X5 s1) (ov_mb s1)) with (ov_X6 s1). change (tfb_X6 (ov_X5 s2) (ov_mb s2)) with (ov_X6 s2).
  rewrite Emb.
  assert (Ebuf : fb_buf s2 = fb_buf s1) by (unfold fb_buf; rewrite (rel_block_start _ _ _ _ _ _ _ _ R); reflexivity).
  assert (Elen : fb_len s2 = fb_len s1) by (unfold fb_len; rewrite (rel_block_start _ _ _ _ _ _ _ _ R), (rel_strstart _ _ _ _ _ _ _ _ R); reflexivity).
  rewrite Ebuf, Elen.
  assert (Ebr : tfb_branch (ov_X6 s2) (fb_buf s1) (fb_len s1) = tfb_branch (ov_X6 s1) (fb_buf s1) (fb_len s1)).
  { unfold tfb_branch. pose proof (r_clean _ _ _ _ _ _ _ _ R6) as EC.
    rewrite (clean_eq_fieldT ds_opt_len _ _ EC), (clean_eq_fieldT ds_static_len _ _ EC), (clean_eq_fieldT ds_strategy _ _ EC) by reflexivity.
    reflexivity. }
  rewrite Ebr.
  pose proof (emit_rel W C B bnd ms pm s1 s2 last R FE1 FE2 HS HW Hbs) as RE. cbv zeta in RE.
  pose proof (fin_rel W C bnd ms pm last _ _ _ RE) as RF.
  eapply rel_Bx_merge; [exact RF|].
  split; [| apply (proj1 (fin_pending_mono _ _))].
  pose proof (proj1 (X6_facts s1 last FE1)) as P0. rewrite <- P0.
  apply tfb_emit_pending_mono. unfold fb_len. apply wrap64_range.
Qed.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require  DeflateTaintBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Theorem flush_block_rel_blk : DeflateTaintBlk.FLUSH_BLOCK_REL.
Proof. exact flush_block_rel. Qed.
