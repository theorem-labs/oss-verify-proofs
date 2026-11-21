(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout FillWinMem TreeMem BitsModel BitsModel2 MemFill BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees LmatchModel FillWinModel TreeModel SendModel BuildTreeModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition dsc_off (t : tree_id) : Z := match t with TL => 2904 | TD => 2928 | TB => 2952 end.

Section WithImage.
Variable segs : list Segment.
Variables AL AD AB : Z.
Local Abbreviation dscal := (dsl_scalars segs AL AD AB).
Local Abbreviation darr := (dsl_arrays segs).


Lemma dsl_upd_l_max_code : forall mem S p ds v,
  dscal mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes mem (zw (S + 2912)) (Z_to_le_bytes 4 v)) S p (set_l_max_code ds v).
Proof.
  intros mem S p ds v H HS0 HS1. unfold dsl_SIZE in *.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 38 2912 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.
Lemma dsl_upd_d_max_code : forall mem S p ds v,
  dscal mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes mem (zw (S + 2936)) (Z_to_le_bytes 4 v)) S p (set_d_max_code ds v).
Proof.
  intros mem S p ds v H HS0 HS1. unfold dsl_SIZE in *.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 41 2936 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.
Lemma dsl_upd_bl_max_code : forall mem S p ds v,
  dscal mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes mem (zw (S + 2960)) (Z_to_le_bytes 4 v)) S p (set_bl_max_code ds v).
Proof.
  intros mem S p ds v H HS0 HS1. unfold dsl_SIZE in *.
  exact (fields_write_field segs mem S _ _ dsl_SIZE 44 2960 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) dsl_layout_within HS0 HS1).
Qed.

Lemma dsl_upd_max_code : forall mem S p ds t v,
  dscal mem S p ds -> 0 <= S -> S + dsl_SIZE <= 2 ^ 64 ->
  dscal (wbytes mem (zw (S + dsc_off t + 8)) (Z_to_le_bytes 4 v)) S p (set_max_code ds t v).
Proof.
  intros mem S p ds [| |] v H HS0 HS1; cbn [dsc_off set_max_code].
  - replace (S + 2904 + 8) with (S + 2912) by lia. apply dsl_upd_l_max_code; assumption.
  - replace (S + 2928 + 8) with (S + 2936) by lia. apply dsl_upd_d_max_code; assumption.
  - replace (S + 2952 + 8) with (S + 2960) by lia. apply dsl_upd_bl_max_code; assumption.
Qed.

Lemma dsc_off_range : forall t, 2904 <= dsc_off t <= 2952.
Proof. intros [| |]; cbn; lia. Qed.


Section RelT.
Variables (F : franges) (mem0 : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation BR := (BR segs AL AD AB F mem0 S p PBL).
Hypothesis HL : BRH F S p PBL.
Hypothesis HFS : sub_franges F S dsl_SIZE.

Variables (s : deflate_state) (t : tree_id).
Local Abbreviation U FC DL HP HL' HM DP BC OL SL MC := (bt_upd s t FC DL HP HL' HM DP BC OL SL MC).

Lemma BRT_start : forall m, BR m s ->
  BR m (bt_upd s t (tree_fc s t) (tree_dl s t) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s)
               (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t)).
Proof. intros m H. rewrite bt_upd_self. exact H. Qed.

Lemma BRT_max_code : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + dsc_off t + 8 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 4 v)) (U FC DL HP HL' HM DP BC OL SL v).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v (A & B & C & D & E & G & H & I & J) ->.
  rewrite <- (bt_set_max_code s t FC DL HP HL' HM DP BC OL SL MC v).
  destruct HL as (HS & HPB & Hdisj & _). pose proof (dsc_off_range t) as Hd. unfold BR, dsl_SIZE in *.
  split; [apply dsl_upd_max_code; unfold dsl_SIZE; try lia; exact A|].
  split; [replace (dsl_arrays segs (wbytes m (zw (S + dsc_off t + 8)) (Z_to_le_bytes 4 v)) S (set_max_code _ t v))
            with (dsl_arrays segs (wbytes m (zw (S + dsc_off t + 8)) (Z_to_le_bytes 4 v)) S (bt_upd s t FC DL HP HL' HM DP BC OL SL MC))
            by (destruct t; reflexivity);
          apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|].
  split; [rewrite bt_set_max_code; revert C; unfold tree_lens; destruct t; cbn; tauto|].
  split; [rewrite bt_set_max_code, bt_pending_buf in *; apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact D|].
  split; [rewrite bt_set_max_code, bt_pending_buf in *; exact E|].
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply HFS; cbn in Hx; lia]|].
  split; [apply mapped_wbytes; exact H|]. split; [apply mapped_wbytes; exact I|].
  intros x Hx. apply wbytes_grows. exact (J x Hx).
Qed.

Lemma BRT_heap : forall m FC DL HP HL' HM DP BC OL SL MC a i v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 3008 + 4 * i -> 0 <= i < 573 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 4 v)) (U FC DL (arr_set HP i v) HL' HM DP BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a i v H -> Hi.
  rewrite <- bt_heap_set.
  apply (BR_st_heap segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_depth : forall m FC DL HP HL' HM DP BC OL SL MC a i v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5308 + i -> 0 <= i < 573 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 1 v)) (U FC DL HP HL' HM (arr_set DP i (wrap8 v)) BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a i v H -> Hi.
  rewrite <- bt_depth_set.
  apply (BR_st_depth segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_bl_count : forall m FC DL HP HL' HM DP BC OL SL MC a i v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 2976 + 2 * i -> 0 <= i < 16 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 2 v)) (U FC DL HP HL' HM DP (arr_set BC i (wrap16 v)) OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a i v H -> Hi.
  rewrite <- bt_bl_count_set.
  apply (BR_st_bl_count segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_fc : forall m FC DL HP HL' HM DP BC OL SL MC a i v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + toff t + 4 * i -> 0 <= i < tsize t ->
  BR (wbytes m (zw a) (Z_to_le_bytes 2 v)) (U (arr_set FC i (wrap16 v)) DL HP HL' HM DP BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a i v H -> Hi.
  replace (bt_upd s t (arr_set FC i (wrap16 v)) DL HP HL' HM DP BC OL SL MC)
    with (set_tree_fc (bt_upd s t FC DL HP HL' HM DP BC OL SL MC) t
            (arr_set (tree_fc (bt_upd s t FC DL HP HL' HM DP BC OL SL MC) t) i (wrap16 v)))
    by (rewrite bt_tree_fc, bt_set_tree_fc; reflexivity).
  apply (BR_st_fc segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_dl : forall m FC DL HP HL' HM DP BC OL SL MC a i v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + toff t + 4 * i + 2 -> 0 <= i < tsize t ->
  BR (wbytes m (zw a) (Z_to_le_bytes 2 v)) (U FC (arr_set DL i (wrap16 v)) HP HL' HM DP BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a i v H -> Hi.
  replace (bt_upd s t FC (arr_set DL i (wrap16 v)) HP HL' HM DP BC OL SL MC)
    with (set_tree_dl (bt_upd s t FC DL HP HL' HM DP BC OL SL MC) t
            (arr_set (tree_dl (bt_upd s t FC DL HP HL' HM DP BC OL SL MC) t) i (wrap16 v)))
    by (rewrite bt_tree_dl, bt_set_tree_dl; reflexivity).
  apply (BR_st_dl segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_heap_len : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5300 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 4 v)) (U FC DL HP v HM DP BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H ->. rewrite <- (bt_set_heap_len s t FC DL HP HL' HM DP BC OL SL MC v).
  apply (BR_st_heap_len segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_heap_max : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5304 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 4 v)) (U FC DL HP HL' v DP BC OL SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H ->. rewrite <- (bt_set_heap_max s t FC DL HP HL' HM DP BC OL SL MC v).
  apply (BR_st_heap_max segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_opt_len : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5912 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 8 v)) (U FC DL HP HL' HM DP BC v SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H ->. rewrite <- (bt_set_opt_len s t FC DL HP HL' HM DP BC OL SL MC v).
  apply (BR_st_opt_len segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.

Lemma BRT_static_len : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5920 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 8 v)) (U FC DL HP HL' HM DP BC OL v MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H ->. rewrite <- (bt_set_static_len s t FC DL HP HL' HM DP BC OL SL MC v).
  apply (BR_st_static_len segs AL AD AB F mem0 S p PBL HL HFS); assumption.
Qed.


Lemma BRT_opt_len_w : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5912 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 8 v)) (U FC DL HP HL' HM DP BC (wrap64 v) SL MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H Ha.
  rewrite (Z_to_le_bytes_eqm 8 v (wrap64 v)) by (rewrite wrap64_mod; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity).
  apply BRT_opt_len with (OL := OL); assumption.
Qed.
Lemma BRT_static_len_w : forall m FC DL HP HL' HM DP BC OL SL MC a v,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> a = S + 5920 ->
  BR (wbytes m (zw a) (Z_to_le_bytes 8 v)) (U FC DL HP HL' HM DP BC OL (wrap64 v) MC).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC a v H Ha.
  rewrite (Z_to_le_bytes_eqm 8 v (wrap64 v)) by (rewrite wrap64_mod; change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite Z.mod_mod by lia; reflexivity).
  apply BRT_static_len with (SL := SL); assumption.
Qed.

Lemma BRT_other : forall m FC DL HP HL' HM DP BC OL SL MC (b : Z) bs,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + dsl_SIZE <= b \/ b + Z.of_nat (length bs) <= S) ->
  (PB + PBL <= b \/ b + Z.of_nat (length bs) <= PB) ->
  sub_franges F b (Z.of_nat (length bs)) ->
  BR (wbytes m (zw b) bs) (U FC DL HP HL' HM DP BC OL SL MC).
Proof. intros. apply (BR_st_other segs AL AD AB F mem0 S p PBL HL); assumption. Qed.

Lemma BRT_parts : forall (LF : franges) m m' FC DL HP HL' HM DP BC OL SL MC FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC',
  BR m (U FC DL HP HL' HM DP BC OL SL MC) ->
  dscal m' S p (U FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC') ->
  darr m' S (U FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC') ->
  tree_lens (U FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC') ->
  agree_out LF m m' ->
  (forall x, in_franges LF x -> S <= x < S + dsl_SIZE) ->
  mapped m' S dsl_SIZE -> (forall x, m x <> None -> m' x <> None) ->
  BR m' (U FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC').
Proof.
  intros LF m m' FC DL HP HL' HM DP BC OL SL MC FC' DL' HP' HL'' HM' DP' BC' OL' SL' MC'
         (A & B & C & D & E & G & H & I & J) A' B' C' Hag HLF Hm' Hg.
  destruct HL as (HS & HPB & Hdisj & _). unfold BR, dsl_SIZE in *.
  rewrite bt_pending_buf in *.
  split; [exact A'|]. split; [exact B'|]. split; [exact C'|].
  split.
  { intros i Hi. apply (cell_agree_out segs LF m m'); [exact Hag | | lia | cbn; lia | exact (D i Hi)].
    intros x Hx Hin. specialize (HLF x Hin). lia. }
  split; [exact E|].
  split.
  { intros x Hx. rewrite (Hag x); [exact (G x Hx)|]. intros Hin. apply Hx. apply HFS. unfold dsl_SIZE. exact (HLF _ Hin). }
  split; [exact Hm'|]. split; [intros x Hx; apply Hg; exact (I x Hx)|].
  intros x Hx. apply Hg. exact (J x Hx).
Qed.


Lemma fields_agree_gap : forall G mem mem' Sb L vs size lo hi,
  fields segs mem Sb L vs -> layout_within L size = true -> layout_gap L lo hi = true ->
  agree_out G mem mem' -> (forall x, in_franges G x -> Sb + lo <= x < Sb + hi) ->
  0 <= Sb -> Sb + size <= 2 ^ 64 ->
  fields segs mem' Sb L vs.
Proof.
  intros G mem mem' Sb L. induction L as [|[o w] L' IH]; intros vs size lo hi Hf HW HG Hag HF HS0 HS1.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within layout_gap] in HW, HG.
    apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply andb_prop in HG as [HG HG'].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH vs' size lo hi Hf' HW' HG' Hag HF HS0 HS1)].
    apply (cell_agree_out segs G mem mem' _ w _ Hag); [| lia | lia | exact Hc].
    intros x Hx Hin. specialize (HF x Hin). apply Bool.orb_prop in HG as [HG|HG]; apply Z.leb_le in HG; lia.
Qed.

Lemma BRT_blc_fill : forall m m' FC DL HP HL' HM DP BC OL SL MC,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) -> arr_len BC = 16 ->
  filled m' (S + 2976) (S + 2976 + 32) (ms_bb 0) -> same_outside m m' (S + 2976) (S + 2976 + 32) ->
  (forall x, m x <> None -> m' x <> None) ->
  BR m' (U FC DL HP HL' HM DP (arr_fill BC 0 16 0) OL SL MC).
Proof.
  intros m m' FC DL HP HL' HM DP BC OL SL MC HB LBC Hfill Hsame Hgr.
  pose proof HB as (A & B & C & D & E & G & H & I & J).
  destruct HL as (HS & HPB & Hdisj & _). unfold dsl_SIZE in HS, H.
  set (F' := [(S + 2976, 32)] : franges).
  assert (Hag : agree_out F' m m').
  { apply (same_outside_agree_out m m' (S + 2976) (S + 2976 + 32)); [exact Hsame|]. intros x Hx. left. cbn. lia. }
  assert (HF' : forall x, in_franges F' x -> S + 2976 <= x < S + 3008) by (intros x [Hx|[]]; cbn in Hx; lia).
  apply (BRT_parts F' m m' FC DL HP HL' HM DP BC OL SL MC); try assumption.
  -
    rewrite <- (bt_set_bl_count s t FC DL HP HL' HM DP BC OL SL MC).
    unfold dsl_scalars in *.
    match goal with |- fields _ _ _ _ ?vs => replace vs with (dsl_vals AL AD AB (bt_upd s t FC DL HP HL' HM DP BC OL SL MC) p S) by reflexivity end.
    eapply (fields_agree_gap F' m m' S dsl_layout _ dsl_SIZE 2976 5300 A dsl_layout_within dsl_gap_heap Hag); unfold dsl_SIZE; try lia.
    intros x Hx. specialize (HF' x Hx). lia.
  -
    unfold darr, dsl_arrays in *. destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    rewrite <- (bt_set_bl_count s t FC DL HP HL' HM DP BC OL SL MC).
    cbn [ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_bl_count].
    assert (G' : forall P st w n f, cells segs m P st w n f -> Z.of_nat w <= st -> 0 <= n ->
              (P + st * n <= S + 2976 \/ S + 3008 <= P) -> S <= P -> P + st * n <= S + 5968 -> cells segs m' P st w n f).
    { intros P st w n f Hc Hw Hn Hd HP1 HP2.
      refine (cells_agree_out segs F' m m' P st w n f Hag _ Hw ltac:(lia) ltac:(lia) Hc).
      intros x Hx Hin. specialize (HF' x Hin). nia. }
    repeat split.
    + apply (G' _ _ _ _ _ B1); cbn; lia.
    + apply (G' _ _ _ _ _ B2); cbn; lia.
    + apply (G' _ _ _ _ _ B3); cbn; lia.
    + apply (G' _ _ _ _ _ B4); cbn; lia.
    + apply (G' _ _ _ _ _ B5); cbn; lia.
    + apply (G' _ _ _ _ _ B6); cbn; lia.
    + intros i Hi. rewrite arr_get_fill. unfold arr_inb. rewrite LBC.
      replace ((0 <=? i) && (i <? 0 + Z.max 0 16) && ((0 <=? i) && (i <? 16))) with true
        by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
      unfold cell. cbn [rdn Z_to_le_bytes].
      rewrite (Hfill (zw (S + 2976 + 2 * i))) by (rewrite u_zw_small by lia; lia).
      rewrite (zw_succ (S + 2976 + 2 * i)) by lia.
      rewrite (Hfill (zw (S + 2976 + 2 * i + 1))) by (rewrite u_zw_small by lia; lia).
      reflexivity.
    + apply (G' _ _ _ _ _ B8); cbn; lia.
    + apply (G' _ _ _ _ _ B9); cbn; lia.
  -
    rewrite <- (bt_set_bl_count s t FC DL HP HL' HM DP BC OL SL MC). unfold tree_lens in *.
    cbn [ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth set_bl_count].
    rewrite arr_len_fill. rewrite bt_bl_count in C. exact C.
  - intros x Hx. specialize (HF' x Hx). unfold dsl_SIZE. lia.
  - intros x Hx. apply Hgr. apply H. exact Hx.
Qed.

Lemma BRT_cells : forall m FC DL HP HL' HM DP BC OL SL MC,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) ->
  cells segs m (S + toff t) 4 2 (tsize t) (arr_get FC)
  /\ cells segs m (S + toff t + 2) 4 2 (tsize t) (arr_get DL)
  /\ cells segs m (S + 3008) 4 4 573 (arr_get HP)
  /\ cells segs m (S + 5308) 1 1 573 (arr_get DP)
  /\ cells segs m (S + 2976) 2 2 16 (arr_get BC)
  /\ cell segs m (S + 5300) 4 HL' /\ cell segs m (S + 5304) 4 HM
  /\ cell segs m (S + 5912) 8 OL /\ cell segs m (S + 5920) 8 SL
  /\ cell segs m (S + dsc_off t + 8) 4 MC.
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC (A & B & _).
  unfold darr in B.
  pose proof (arrays_fc segs _ _ _ t B) as X1. rewrite bt_tree_fc in X1.
  pose proof (arrays_dl segs _ _ _ t B) as X2. rewrite bt_tree_dl in X2.
  pose proof (arrays_heap segs _ _ _ B) as X3. rewrite bt_heap in X3.
  pose proof (arrays_depth segs _ _ _ B) as X4. rewrite bt_depth in X4.
  pose proof (arrays_bl_count segs _ _ _ B) as X5. rewrite bt_bl_count in X5.
  pose proof (dsl_heap_len _ _ _ _ _ _ _ _ A) as X6. rewrite bt_heap_len in X6.
  pose proof (dsl_heap_max _ _ _ _ _ _ _ _ A) as X7. rewrite bt_heap_max in X7.
  pose proof (dsl_opt_len _ _ _ _ _ _ _ _ A) as X8. rewrite bt_opt_len in X8.
  pose proof (dsl_static_len _ _ _ _ _ _ _ _ A) as X9. rewrite bt_static_len in X9.
  assert (X10 : cell segs m (S + dsc_off t + 8) 4 MC).
  { rewrite <- (bt_max_code s t FC DL HP HL' HM DP BC OL SL MC). destruct t; cbn [dsc_off max_code].
    - replace (S + 2904 + 8) with (S + 2912) by lia. exact (dsl_l_desc_max_code _ _ _ _ _ _ _ _ A).
    - replace (S + 2928 + 8) with (S + 2936) by lia. exact (dsl_d_desc_max_code _ _ _ _ _ _ _ _ A).
    - replace (S + 2952 + 8) with (S + 2960) by lia. exact (dsl_bl_desc_max_code _ _ _ _ _ _ _ _ A). }
  repeat (split; [assumption|]). exact X10.
Qed.

Lemma BRT_desc : forall m FC DL HP HL' HM DP BC OL SL MC,
  BR m (U FC DL HP HL' HM DP BC OL SL MC) ->
  cell segs m (S + dsc_off t) 8 (S + toff t)
  /\ cell segs m (S + dsc_off t + 16) 8 (match t with TL => AL | TD => AD | TB => AB end).
Proof.
  intros m FC DL HP HL' HM DP BC OL SL MC (A & _).
  destruct t; cbn [dsc_off toff].
  - split; [exact (dsl_l_desc_dyn_tree _ _ _ _ _ _ _ _ A)|]. replace (S + 2904 + 16) with (S + 2920) by lia. exact (dsl_l_desc_stat_desc _ _ _ _ _ _ _ _ A).
  - split; [exact (dsl_d_desc_dyn_tree _ _ _ _ _ _ _ _ A)|]. replace (S + 2928 + 16) with (S + 2944) by lia. exact (dsl_d_desc_stat_desc _ _ _ _ _ _ _ _ A).
  - split; [exact (dsl_bl_desc_dyn_tree _ _ _ _ _ _ _ _ A)|]. replace (S + 2952 + 16) with (S + 2968) by lia. exact (dsl_bl_desc_stat_desc _ _ _ _ _ _ _ _ A).
Qed.

End RelT.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

End WithImage.

End FXG.
Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Inductive skind := KFc (i : Z) | KDl (i : Z) | KHeap (i : Z) | KDepth (i : Z) | KBlc (i : Z)
                 | KHl | KHm | KOpt | KStat | KOptW | KStatW | KMc | KOther.

End FXG.
Ltac brT_one H1 H2 IM F mem0 S p PBL HL HFS M1 a v k :=
  lazymatch type of H1 with
  | BR _ _ _ _ _ _ _ _ _ _ (bt_upd ?s ?t ?FC ?DL ?HP ?HLn ?HM ?DP ?BC ?OL ?SL ?MC) =>
      lazymatch k with
      | KFc ?i => pose proof (BRT_fc _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a i v H1 ltac:(lia) ltac:(lia)) as H2
      | KDl ?i => pose proof (BRT_dl _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a i v H1 ltac:(lia) ltac:(lia)) as H2
      | KHeap ?i => pose proof (BRT_heap _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a i v H1 ltac:(lia) ltac:(lia)) as H2
      | KDepth ?i => pose proof (BRT_depth _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a i v H1 ltac:(lia) ltac:(lia)) as H2
      | KBlc ?i => pose proof (BRT_bl_count _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a i v H1 ltac:(lia) ltac:(lia)) as H2
      | KHl => pose proof (BRT_heap_len _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KHm => pose proof (BRT_heap_max _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KOpt => pose proof (BRT_opt_len _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KStat => pose proof (BRT_static_len _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KOptW => pose proof (BRT_opt_len_w _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KStatW => pose proof (BRT_static_len_w _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      | KMc => pose proof (BRT_max_code _ _ _ _ F mem0 S p PBL HL HFS s t M1 FC DL HP HLn HM DP BC OL SL MC a v H1 ltac:(lia)) as H2
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac br_fwdT_rec HB M ks oth :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      lazymatch ks with
      | ?k :: ?rest =>
          br_fwdT_rec HB M1 rest oth;
          lazymatch goal with
          | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 (bt_upd _ _ _ _ _ _ _ _ _ _ _ _),
            HL : BRH ?F ?S ?p ?PBL, HFS : sub_franges ?F ?S dsl_SIZE |- _ =>
              let H2 := fresh "HBT" in
              lazymatch k with
              | KOther =>
                  pose proof (BRT_other sg AL AD AB F mem0 S p PBL HL _ _ M1 _ _ _ _ _ _ _ _ _ _ a bs H1) as H2;
                  specialize (H2 ltac:(oth) ltac:(oth) ltac:(oth) ltac:(oth) ltac:(oth))
              | _ => lazymatch bs with Z_to_le_bytes _ ?v => brT_one H1 H2 sg F mem0 S p PBL HL HFS M1 a v k end
              end;
              clear H1
          end
      end
  | _ =>
      let H := fresh "HBT" in
      lazymatch type of HB with
      | BR _ _ _ _ _ _ _ _ _ _ (bt_upd _ _ _ _ _ _ _ _ _ _ _ _) => pose proof HB as H
      | BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL _ ?s =>
          lazymatch goal with
          | |- context [bt_upd _ ?t _ _ _ _ _ _ _ _ _ _] => pose proof (BRT_start sg AL AD AB F mem0 S p PBL s t _ HB) as H
          end
      end
  end.
Ltac br_fwdT HB M ks oth :=
  let ksr := eval cbv beta iota zeta delta [List.rev List.app] in (List.rev ks) in
  br_fwdT_rec HB M ksr oth.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac st_eqT :=
  autorewrite with btupd;
  lazymatch goal with
  | |- bt_upd ?s ?t _ _ _ _ _ _ _ _ _ _ = bt_upd ?s ?t _ _ _ _ _ _ _ _ _ _ => apply bt_upd_congr
  end.
