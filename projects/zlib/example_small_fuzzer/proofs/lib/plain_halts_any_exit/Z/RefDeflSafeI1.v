(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition dmode (s : deflate_state) : Z :=
  if ds_level s =? 0 then 0
  else if ds_strategy s =? Z_HUFFMAN_ONLY then 1
  else if ds_strategy s =? Z_RLE then 2
  else if ds_level s <=? 3 then 3 else 4.

Lemma run_compress_func_dmode : forall s flush,
  run_compress_func s flush =
  match dmode s with
  | 0 => deflate_stored s flush | 1 => deflate_huff s flush | 2 => deflate_rle s flush
  | 3 => deflate_fast s flush | _ => deflate_slow s flush
  end.
Proof.
  intros s flush. unfold run_compress_func, dmode.
  destruct (ds_level s =? 0); [reflexivity|]. destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [reflexivity|].
  destruct (ds_strategy s =? Z_RLE); [reflexivity|]. destruct (ds_level s <=? 3); reflexivity.
Qed.

Lemma dmode_range : forall s, 0 <= dmode s <= 4.
Proof. intros s. unfold dmode. repeat (destruct (_ =? _) || destruct (_ <=? _)); lia. Qed.


Record DX (s : deflate_state) : Prop := {
  dx_cfg : (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s) = configuration_table (ds_level s);
  dx_insh : 0 <= ds_ins_h s < 65536;
  dx_ins : ds_insert s <= ds_w_size s;
  dx_ml : 0 <= ds_match_length s <= MAX_MATCH;
  dx_pl : 0 <= ds_prev_length s <= MAX_MATCH;
  dx_ma : ds_match_available s = 0 \/ ds_match_available s = 1;
  dx_pm : 0 <= ds_prev_match s < 2 ^ 32;
  dx_matches : 0 <= ds_matches s <= nsym s + 2;
  dx_hw : ds_high_water s <= ds_window_size s;
  dx_fast : dmode s = 3 -> ds_prev_length s = 2 /\ ds_match_length s < MIN_MATCH;
  dx_notslow : dmode s <> 4 -> ds_match_available s = 0;
  dx_slow : dmode s = 4 -> 2 <= ds_match_length s
             /\ (ds_match_available s = 1 -> 1 <= ds_strstart s)
             /\ (MIN_MATCH <= ds_match_length s -> ds_match_length s <= ds_lookahead s + 1 /\ 1 <= ds_strstart s
                                                 /\ 2 <= wrap32 (ds_strstart s - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD + 1);
  dx_st0 : dmode s = 0 -> ds_lookahead s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_sym_next s = 0 /\ ds_matches s <= 2;
  dx_wrapneg : ds_wrap s < 0 -> ds_status s = FINISH_STATE;
  dx_fin : ds_status s = FINISH_STATE -> ds_lookahead s = 0;
  dx_sn : ds_sym_next s = 3 * nsym s;
  dx_nsym : 0 <= nsym s <= ds_lit_bufsize s - 2;
  dx_syms : forall j, 0 <= j < nsym s -> sym_okb s j;
  dx_hist : freq_hist s;
  dx_opt : ds_opt_len s = 0;
  dx_stat : ds_static_len s = 0;
  dx_ext : dmode s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s;
  dx_tfc : forall t i, 0 <= arr_get (tree_fc s t) i < 65536;
  dx_tdl : forall t i, 0 <= arr_get (tree_dl s t) i < 65536;
  dx_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  dx_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536;
  dx_chain : dmode s <> 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1);
  dx_pout0 : ds_pending s = 0 -> ds_pending_out s = 0;
  dx_biv : ds_bi_valid s <= 7 }.

Definition DD (s : deflate_state) : Prop := dwf s /\ DX s.


Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

Record SV (c0 : cstrm) (s : deflate_state) : Prop := {
  sv_input : cs_input (ds_strm s) = cs_input c0;
  sv_nin : 0 <= cs_next_in (ds_strm s);
  sv_inlen : cs_next_in (ds_strm s) + cs_avail_in (ds_strm s) = arr_len (cs_input c0);
  sv_ain : 0 <= cs_avail_in (ds_strm s) < 2 ^ 32;
  sv_out : zlen (cs_out_rev (ds_strm s)) + cs_avail_out (ds_strm s) = zlen (cs_out_rev c0) + cs_avail_out c0;
  sv_aout : 0 <= cs_avail_out (ds_strm s);
  sv_grow : (length (cs_out_rev c0) <= length (cs_out_rev (ds_strm s)))%nat;
  sv_outb : Forall (fun b => 0 <= b < 256) (cs_out_rev (ds_strm s));
  sv_tin : 0 <= cs_total_in (ds_strm s) < 2 ^ 64;
  sv_tout : cs_total_out (ds_strm s) = wrap64 (cs_total_out c0 + zlen (cs_out_rev (ds_strm s)) - zlen (cs_out_rev c0));
  sv_adler : 0 <= cs_adler (ds_strm s) < 2 ^ 64;
  sv_dt : - 2 ^ 31 <= cs_data_type (ds_strm s) < 2 ^ 31;
  sv_ib : forall i, 0 <= i < arr_len (cs_input (ds_strm s)) -> 0 <= arr_get (cs_input (ds_strm s)) i < 256 }.

Record C0OK (c0 : cstrm) : Prop := {
  c0_out : cs_out_rev c0 = [];
  c0_aout : 0 <= cs_avail_out c0 < 2 ^ 32;
  c0_tout : 0 <= cs_total_out c0 < 2 ^ 64;
  c0_len : arr_len (cs_input c0) < 2 ^ 32 }.

Definition DC (c0 : cstrm) (s : deflate_state) : Prop := DD s /\ SV c0 s.


Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l.
Proof. intros A l. unfold zlen. lia. Qed.

Lemma wrap64_range' : forall z, 0 <= wrap64 z < 2 ^ 64.
Proof. intros z. apply wrap64_range. Qed.

Lemma nsym_sym_next : forall s, ds_sym_next s = 3 * nsym s -> nsym s = ds_sym_next s / 3.
Proof. intros s E. unfold nsym. reflexivity. Qed.

Lemma arr_get_of_list' : forall l i, 0 <= i < zlength l -> arr_get (arr_of_list l) i = znth 0 l i.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list. rewrite (arr_get_upd l _ 0 i 0).
  unfold arr_inb, arr_make. rewrite arr_len_init.
  replace ((0 <=? i) && (i <? 0 + zlength l) && ((0 <=? i) && (i <? zlength l))) with true
    by (symmetry; rewrite !andb_true_iff; rewrite !Z.leb_le, !Z.ltb_lt; lia).
  unfold znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia. rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma bytes_okP_get : forall l i, bytes_okP l -> 0 <= i < zlength l -> 0 <= arr_get (arr_of_list l) i < 256.
Proof.
  intros l i Hb Hi. rewrite arr_get_of_list' by exact Hi. unfold znth. rewrite (proj2 (Z.ltb_ge i 0)) by lia.
  unfold bytes_okP in Hb. rewrite Forall_forall in Hb. apply Hb. apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma C0OK_of_call : forall zc, dcall_wf zc -> C0OK (cstrm_of_call zc).
Proof.
  intros zc (Hz & Hao & Hlen & Hb). destruct Hz as (Ht1 & Ht2 & Had & Hdt).
  constructor; cbn [cstrm_of_call cs_out_rev cs_avail_out cs_total_out cs_input].
  - reflexivity.
  - exact Hao.
  - exact Ht2.
  - rewrite arr_len_of_list. unfold zlength in Hlen. exact Hlen.
Qed.

Lemma SV_entry : forall s zc, dcall_wf zc -> SV (cstrm_of_call zc) (set_strm s (cstrm_of_call zc)).
Proof.
  intros s zc (Hz & Hao & Hlen & Hb). destruct Hz as (Ht1 & Ht2 & Had & Hdt).
  constructor; unfold set_strm; cbn [ds_strm cstrm_of_call cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out
                                      cs_total_in cs_total_out cs_adler cs_data_type].
  - reflexivity.
  - lia.
  - rewrite arr_len_of_list. unfold zlength. lia.
  - unfold zlength in *. lia.
  - reflexivity.
  - lia.
  - apply le_n.
  - constructor.
  - exact Ht1.
  - unfold zlen. cbn [length Z.of_nat]. rewrite wrap64_id by lia. f_equal. lia.
  - exact Had.
  - exact Hdt.
  - intros i Hi. rewrite arr_len_of_list in Hi. apply bytes_okP_get; [exact Hb | exact Hi].
Qed.

Lemma DC_DOK : forall c0 s, C0OK c0 -> DC c0 s -> DOK s.
Proof.
  intros c0 s HC0 [[D X] V].
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh).
  pose proof (sv_out _ _ V) as Ho. pose proof (c0_out _ HC0) as E0. rewrite E0 in Ho. unfold zlen in Ho. cbn [length Z.of_nat] in Ho.
  pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Hz. unfold zlen in Hz.
  constructor.
  - pose proof (df_st4 _ D) as H4. unfold st4, INIT_STATE, GZIP_STATE, BUSY_STATE, FINISH_STATE. exact H4.
  - exact (df_wrap _ D).
  - pose proof (df_lf _ D). lia.
  - exact (df_gzhead _ D).
  - exact (df_level _ D).
  - pose proof (df_strategy _ D) as H. unfold Z_FIXED in H. exact H.
  - exact (df_wbits _ D).
  - exact (df_pend _ D).
  - exact (df_bi _ D).
  - exact (df_strstart _ D).
  - pose proof (df_look _ D). pose proof (df_sl _ D). pose proof (df_strstart _ D). lia.
  - pose proof (dx_ext _ X) as He. pose proof (dx_st0 _ X) as H0. pose proof (df_strstart _ D). pose proof (dx_nsym _ X).
    pose proof (dx_ma _ X). pose proof (dmode_range s).
    destruct (Z.eq_dec (dmode s) 0) as [E|E]; [specialize (H0 E); lia | specialize (He E); lia].
  - pose proof (df_ins _ D). pose proof (df_strstart _ D). lia.
  - pose proof (dx_sn _ X). pose proof (dx_nsym _ X). lia.
  - exact (sv_ain _ _ V).
  - pose proof (sv_aout _ _ V). pose proof (c0_aout _ HC0). lia.
  - split; [exact (sv_nin _ _ V)|]. rewrite (sv_inlen _ _ V), (sv_input _ _ V). reflexivity.
  - exact (sv_tin _ _ V).
  - rewrite (sv_tout _ _ V). apply wrap64_range'.
  - exact (sv_adler _ _ V).
  - exact (sv_dt _ _ V).
Qed.


Lemma SV_strm : forall c0 s s', ds_strm s' = ds_strm s -> SV c0 s -> SV c0 s'.
Proof. intros c0 s s' E V. destruct V; constructor; rewrite ?E; assumption. Qed.

Definition dx_core (s : deflate_state) :=
  (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s,
   ds_ins_h s, ds_insert s, ds_w_size s, ds_match_length s, ds_prev_length s, ds_match_available s, ds_prev_match s,
   ds_matches s, ds_high_water s, ds_window_size s, ds_lookahead s, ds_block_start s, ds_strstart s,
   (ds_sym_next s, ds_wrap s, ds_status s, ds_lit_bufsize s, ds_pending_buf s, ds_dyn_ltree_fc s, ds_dyn_dtree_fc s, ds_bl_tree_fc s,
    ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s, ds_depth s, ds_bl_count s, ds_opt_len s, ds_static_len s,
    ds_head s, ds_prev s, ds_hash_size s, ds_w_mask s, ds_bi_valid s, ds_match_start s)).
Definition dx_view (s : deflate_state) := (dx_core s, (ds_pending s, ds_pending_out s)).

Lemma dx_view_set_strm : forall s c, dx_view (set_strm s c) = dx_view s.
Proof. intros s c. reflexivity. Qed.
Lemma dx_view_set_last_flush : forall s v, dx_view (set_last_flush s v) = dx_view s.
Proof. intros s v. reflexivity. Qed.

Lemma sym_buf_get_pb : forall s s' i, ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  sym_buf_get s' i = sym_buf_get s i.
Proof. intros s s' i E1 E2. unfold sym_buf_get. rewrite E1, E2. reflexivity. Qed.

Lemma dx_core_fields : forall s s', dx_core s' = dx_core s ->
  ds_good_match s' = ds_good_match s /\ ds_max_lazy_match s' = ds_max_lazy_match s /\ ds_nice_match s' = ds_nice_match s
  /\ ds_max_chain_length s' = ds_max_chain_length s /\ ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s
  /\ ds_ins_h s' = ds_ins_h s /\ ds_insert s' = ds_insert s /\ ds_w_size s' = ds_w_size s /\ ds_match_length s' = ds_match_length s
  /\ ds_prev_length s' = ds_prev_length s /\ ds_match_available s' = ds_match_available s /\ ds_prev_match s' = ds_prev_match s
  /\ ds_matches s' = ds_matches s /\ ds_high_water s' = ds_high_water s /\ ds_window_size s' = ds_window_size s
  /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_block_start s /\ ds_strstart s' = ds_strstart s
  /\ ds_sym_next s' = ds_sym_next s /\ ds_wrap s' = ds_wrap s /\ ds_status s' = ds_status s /\ ds_lit_bufsize s' = ds_lit_bufsize s
  /\ ds_pending_buf s' = ds_pending_buf s /\ ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s
  /\ ds_bl_tree_fc s' = ds_bl_tree_fc s /\ ds_dyn_ltree_dl s' = ds_dyn_ltree_dl s /\ ds_dyn_dtree_dl s' = ds_dyn_dtree_dl s
  /\ ds_bl_tree_dl s' = ds_bl_tree_dl s /\ ds_depth s' = ds_depth s /\ ds_bl_count s' = ds_bl_count s
  /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s /\ ds_head s' = ds_head s /\ ds_prev s' = ds_prev s
  /\ ds_hash_size s' = ds_hash_size s /\ ds_w_mask s' = ds_w_mask s /\ ds_bi_valid s' = ds_bi_valid s /\ ds_match_start s' = ds_match_start s.
Proof.
  intros s s' E. unfold dx_core in E.
  repeat match type of E with
  | (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?]
  end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma nsym_same : forall s s', ds_sym_next s' = ds_sym_next s -> nsym s' = nsym s.
Proof. intros s s' E. unfold nsym. rewrite E. reflexivity. Qed.

Lemma sym_fields_same : forall s s', ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  (forall j, sym_lc s' j = sym_lc s j) /\ (forall j, sym_dist s' j = sym_dist s j).
Proof.
  intros s s' E1 E2. unfold sym_lc, sym_dist, sym_d0, sym_d1.
  split; intros j; rewrite !(sym_buf_get_pb s s') by assumption; reflexivity.
Qed.

Lemma sym_okb_same : forall s s' j, ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  sym_okb s j -> sym_okb s' j.
Proof.
  intros s s' j E1 E2 H. destruct (sym_fields_same s s' E1 E2) as [L Dd]. unfold sym_okb in *. rewrite L, Dd. exact H.
Qed.

Lemma sym_codes_same : forall s s', ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  (forall j, sym_lcode s' j = sym_lcode s j) /\ (forall j, sym_isdist s' j = sym_isdist s j) /\ (forall j, sym_dcode s' j = sym_dcode s j).
Proof.
  intros s s' E1 E2. destruct (sym_fields_same s s' E1 E2) as [L Dd].
  unfold sym_lcode, sym_isdist, sym_dcode. repeat split; intros j; rewrite ?L, ?Dd; reflexivity.
Qed.

Lemma freq_hist_same : forall s s',
  ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s -> ds_sym_next s' = ds_sym_next s ->
  ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s -> ds_bl_tree_fc s' = ds_bl_tree_fc s ->
  freq_hist s -> freq_hist s'.
Proof.
  intros s s' E1 E2 E3 E4 E5 E6 (H1 & H2 & H3). destruct (sym_codes_same s s' E1 E2) as (La & Lb & Lc).
  unfold freq_hist. rewrite (nsym_same s s' E3), E4, E5, E6.
  split; [|split; [|exact H3]].
  - intros c Hc. rewrite (H1 c Hc). f_equal. apply zsum_ext. intros j Hj. rewrite La. reflexivity.
  - intros d Hd. rewrite (H2 d Hd). apply zsum_ext. intros j Hj. rewrite Lb, Lc. reflexivity.
Qed.

Lemma DX_core_same : forall s s', dx_core s' = dx_core s -> (ds_pending s' = 0 -> ds_pending_out s' = 0) -> DX s -> DX s'.
Proof.
  intros s s' E Hp X. pose proof (dx_core_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F41 & F42).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  assert (En : nsym s' = nsym s) by (apply nsym_same; exact F20).
  pose proof (dx_syms _ X) as Xsyms. pose proof (dx_hist _ X) as Xhist. pose proof (dx_tfc _ X) as Xtfc. pose proof (dx_tdl _ X) as Xtdl.
  pose proof (dx_depth _ X) as Xdepth. pose proof (dx_blc _ X) as Xblc. pose proof (dx_chain _ X) as Xchain.
  destruct X; constructor; rewrite ?Em, ?En, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15, ?F16,
    ?F17, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F33, ?F34, ?F41, ?F42; try assumption.
  - intros j Hj. apply (sym_okb_same s s' j F24 F23). apply Xsyms. exact Hj.
  - apply (freq_hist_same s s' F24 F23 F20 F25 F26 F27). exact Xhist.
  - intros t i. destruct t; cbn [tree_fc]; rewrite ?F25, ?F26, ?F27; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
  - intros t i. destruct t; cbn [tree_dl]; rewrite ?F28, ?F29, ?F30; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
  - intros i. rewrite F31. apply Xdepth.
  - intros i Hi. rewrite F32. apply Xblc. exact Hi.
  - intros Hm. apply (CHAIN_same s s'); [exact F35 | exact F36 | exact F37 | exact F9 | exact F38 |]. apply Xchain. exact Hm.
Qed.

Lemma DX_same : forall s s', dx_view s' = dx_view s -> DX s -> DX s'.
Proof.
  intros s s' E X. unfold dx_view in E. apply pair_equal_spec in E. destruct E as [Ec Ep].
  apply pair_equal_spec in Ep. destruct Ep as [E1 E2].
  apply (DX_core_same s s' Ec); [| exact X]. rewrite E1, E2. exact (dx_pout0 _ X).
Qed.

Lemma DX_set_strm : forall s c, DX s -> DX (set_strm s c).
Proof. intros s c X. exact (DX_same s _ (dx_view_set_strm s c) X). Qed.
Lemma DX_set_last_flush : forall s v, DX s -> DX (set_last_flush s v).
Proof. intros s v X. exact (DX_same s _ (dx_view_set_last_flush s v) X). Qed.

Lemma dwf_set_last_flush : forall s v, - 2 <= v <= 5 -> dwf s -> dwf (set_last_flush s v).
Proof. intros s v Hv D. destruct D; constructor; dsred; try assumption. Qed.

Lemma DD_set_strm : forall s c, DD s -> DD (set_strm s c).
Proof. intros s c [D X]. split; [apply dwf_set_strm; exact D | apply DX_set_strm; exact X]. Qed.
Lemma DD_set_last_flush : forall s v, - 2 <= v <= 5 -> DD s -> DD (set_last_flush s v).
Proof. intros s v Hv [D X]. split; [apply dwf_set_last_flush; [exact Hv | exact D] | apply DX_set_last_flush; exact X]. Qed.

Lemma err_return_fst : forall s e, fst (err_return s e) = set_strm s (cset_msg (ds_strm s) (MSG_ERR e)).
Proof. intros s e. reflexivity. Qed.

Lemma SV_set_msg : forall c0 s m, SV c0 s -> SV c0 (set_strm s (cset_msg (ds_strm s) m)).
Proof. intros c0 s m V. destruct V; constructor; unfold set_strm, cset_msg; dsred; cbn; assumption. Qed.

Lemma DC_err_return : forall c0 s e, DC c0 s -> DC c0 (fst (err_return s e)).
Proof.
  intros c0 s e [DDs V]. rewrite err_return_fst. split; [apply DD_set_strm; exact DDs | apply SV_set_msg; exact V].
Qed.

Lemma DC_set_last_flush : forall c0 s v, - 2 <= v <= 5 -> DC c0 s -> DC c0 (set_last_flush s v).
Proof.
  intros c0 s v Hv [DDs V]. split; [apply DD_set_last_flush; [exact Hv | exact DDs]|].
  apply (SV_strm c0 s); [reflexivity | exact V].
Qed.
