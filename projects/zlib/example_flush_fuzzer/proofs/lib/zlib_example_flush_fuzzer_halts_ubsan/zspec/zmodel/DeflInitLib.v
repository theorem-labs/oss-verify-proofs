(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees DeflateLz Deflate
  TreeModel AdlerModel FillWinModel RefDeflateRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).






Definition cfg_good (lv : Z) : Z := let '(g, _, _, _) := configuration_table lv in g.

Definition cfg_lazy (lv : Z) : Z := let '(_, l, _, _) := configuration_table lv in l.

Definition cfg_nice (lv : Z) : Z := let '(_, _, n, _) := configuration_table lv in n.

Definition cfg_chain (lv : Z) : Z := let '(_, _, _, c) := configuration_table lv in c.



Definition RK0 (s : deflate_state) : deflate_state :=
  let st := ds_strm s in
  let st := cset_total_in st 0 in
  let st := cset_total_out st 0 in
  let st := cset_msg st MSG_NULL in
  let st := cset_data_type st Z_UNKNOWN in
  let s := set_strm s st in
  let s := set_pending s 0 in
  let s := set_pending_out s 0 in
  let s := set_status s (if Z.eqb (ds_wrap s) 2 then GZIP_STATE else INIT_STATE) in
  let s := set_strm s (cset_adler (ds_strm s) (if Z.eqb (ds_wrap s) 2 then crc32_init else adler32_init)) in
  set_last_flush s (-2).

Definition LM (s : deflate_state) : deflate_state :=
  let s := set_window_size s (2 * ds_w_size s) in
  let s := clear_hash s in
  let s := set_max_lazy_match s (cfg_lazy (ds_level s)) in
  let s := set_good_match s (cfg_good (ds_level s)) in
  let s := set_nice_match s (cfg_nice (ds_level s)) in
  let s := set_max_chain_length s (cfg_chain (ds_level s)) in
  let s := set_strstart s 0 in
  let s := set_block_start s 0 in
  let s := set_lookahead s 0 in
  let s := set_insert s 0 in
  let s := set_prev_length s (MIN_MATCH - 1) in
  let s := set_match_length s (MIN_MATCH - 1) in
  let s := set_match_available s 0 in
  set_ins_h s 0.















Section Proj.
  Variables (g0 : Z -> Z) (b0 : blk) (cs : cstrm) (wrap wbits memLevel : Z).
  Let s1 := s_setup g0 b0 cs wrap wbits memLevel.

End Proj.

Section Blks.
  Variables (s1 : deflate_state) (rw rp rh rb : option (blk * (Z -> Z))) (memLevel : Z).
  Let s5 := s_pb (s_lbs (s_hd (s_prv (s_win s1 rw) rp) rh) memLevel) rb.











End Blks.

Ltac vals_nf :=
  lazy -[Z.pow Z.sub Z.add Z.mul Z.div Z.shiftl Z.opp Z.eqb Z.ltb Z.leb init_u8 init_u16 init_u32 init_u64 swrap32 swrap64 wrap8 wrap16
         cfg_lazy cfg_good cfg_nice cfg_chain arr_u16_of arr_s32_of arr_u8_of blk_bytes blk_ush arr_fill arr_set arr_make arr_len arr_get
         cset_total_in cset_total_out cset_msg cset_data_type cset_adler].

Lemma head_clearedg : forall g hs i, 0 < hs -> 0 <= i < hs ->
  arr_get (arr_fill (arr_set (blk_ush g hs) (hs - 1) 0) 0 (hs - 1) 0) i = 0.
Proof.
  intros g hs i Hh Hi. rewrite arr_get_fill.
  assert (L : arr_len (arr_set (blk_ush g hs) (hs - 1) 0) = hs) by (rewrite arr_len_set; unfold blk_ush; apply arr_len_init).
  unfold arr_inb. rewrite L.
  destruct (Z.eq_dec i (hs - 1)) as [->|Hne].
  - replace ((0 <=? hs - 1) && (hs - 1 <? 0 + Z.max 0 (hs - 1)) && ((0 <=? hs - 1) && (hs - 1 <? hs))) with false by
      (symmetry; apply Bool.andb_false_iff; left; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
    apply arr_get_set_same. unfold blk_ush. rewrite arr_len_init. lia.
  - replace ((0 <=? i) && (i <? 0 + Z.max 0 (hs - 1)) && ((0 <=? i) && (i <? hs))) with true by
      (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
    reflexivity.
Qed.

Lemma init_u8_range : forall g b i, 0 <= init_u8 g b i < 256.
Proof. intros g b i. unfold init_u8. apply wrap8_range. Qed.

Lemma init_u16_range : forall g b i, 0 <= init_u16 g b i < 65536.
Proof. intros g b i. unfold init_u16. pose proof (wrap8_range (g (b + 2 * i))). pose proof (wrap8_range (g (b + 2 * i + 1))). lia. Qed.

Lemma init_u32_range : forall g b i, 0 <= init_u32 g b i < 2 ^ 32.
Proof. intros g b i. unfold init_u32. pose proof (init_u16_range g b (2 * i)). pose proof (init_u16_range g b (2 * i + 1)). lia. Qed.

Lemma init_u64_range : forall g b i, 0 <= init_u64 g b i < 2 ^ 64.
Proof. intros g b i. unfold init_u64. pose proof (init_u32_range g b (2 * i)). pose proof (init_u32_range g b (2 * i + 1)). lia. Qed.


Section V.
  Variables (g0 gw gp gh gb : Z -> Z).
  Variables (b0 bw bp bh bb : blk) (cs : cstrm) (wrp wb9 meml lv strat method : Z).

  Definition sI1 : deflate_state := s_setup g0 b0 cs wrp wb9 meml.
  Definition sI5 : deflate_state :=
    s_pb (s_lbs (s_hd (s_prv (s_win sI1 (Some (bw, gw))) (Some (bp, gp))) (Some (bh, gh))) meml) (Some (bb, gb)).
  Definition sIF : deflate_state := s_fin sI5 lv strat method.
  Definition sRK : deflate_state := RK0 sIF.
  Definition sTI : deflate_state := tr_init sRK.
  Definition sLM : deflate_state := LM sTI.


  Definition rk_status' : Z := if wrp =? 2 then 57 else 42.
  Definition rk_adler' : Z := if wrp =? 2 then 0 else 1.

  Lemma scalars_LM :
    ds_strstart sLM = 0 /\ ds_lookahead sLM = 0 /\ ds_insert sLM = 0 /\ ds_block_start sLM = 0 /\ ds_high_water sLM = 0
    /\ ds_ins_h sLM = 0 /\ ds_match_start sLM = init_u32 g0 176 0 /\ ds_prev_match sLM = init_u32 g0 164 0
    /\ ds_match_length sLM = 2 /\ ds_prev_length sLM = 2 /\ ds_match_available sLM = 0 /\ ds_matches sLM = 0
    /\ ds_sym_next sLM = 0 /\ ds_bi_valid sLM = 0 /\ ds_bi_buf sLM = 0 /\ ds_pending sLM = 0 /\ ds_pending_out sLM = 0
    /\ ds_last_flush sLM = -2 /\ ds_opt_len sLM = 0 /\ ds_static_len sLM = 0
    /\ ds_good_match sLM = cfg_good lv /\ ds_max_lazy_match sLM = cfg_lazy lv /\ ds_nice_match sLM = cfg_nice lv
    /\ ds_max_chain_length sLM = cfg_chain lv.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma arrs_LM :
    ds_dyn_ltree_fc sLM = arr_set (arr_fill (arr_u16_of g0 212 4 573) 0 L_CODES 0) END_BLOCK 1
    /\ ds_dyn_ltree_dl sLM = arr_u16_of g0 214 4 573
    /\ ds_dyn_dtree_fc sLM = arr_fill (arr_u16_of g0 2504 4 61) 0 D_CODES 0 /\ ds_dyn_dtree_dl sLM = arr_u16_of g0 2506 4 61
    /\ ds_bl_tree_fc sLM = arr_fill (arr_u16_of g0 2748 4 39) 0 BL_CODES 0 /\ ds_bl_tree_dl sLM = arr_u16_of g0 2750 4 39
    /\ ds_bl_count sLM = arr_u16_of g0 2976 2 16 /\ ds_heap sLM = arr_s32_of g0 3008 4 573
    /\ ds_depth sLM = arr_u8_of g0 5308 1 573
    /\ ds_pending_buf sLM = blk_bytes gb (Z.shiftl 1 (meml + 6) * 4)
    /\ ds_window sLM = blk_bytes gw (2 * Z.shiftl 1 wb9) /\ ds_prev sLM = blk_ush gp (Z.shiftl 1 wb9)
    /\ ds_head sLM = arr_fill (arr_set (blk_ush gh (Z.shiftl 1 (meml + 7))) (Z.shiftl 1 (meml + 7) - 1) 0) 0 (Z.shiftl 1 (meml + 7) - 1) 0.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma tree_lens_LM : tree_lens sLM.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma sizes_LM :
    ds_w_size sLM = Z.shiftl 1 wb9 /\ ds_hash_size sLM = Z.shiftl 1 (meml + 7) /\ ds_lit_bufsize sLM = Z.shiftl 1 (meml + 6)
    /\ ds_w_bits sLM = wb9 /\ ds_hash_bits sLM = meml + 7 /\ ds_level sLM = lv /\ ds_strategy sLM = strat
    /\ ds_method sLM = wrap8 method /\ ds_wrap sLM = wrp /\ ds_status sLM = rk_status' /\ ds_gzhead sLM = 0
    /\ ds_w_mask sLM = Z.shiftl 1 wb9 - 1 /\ ds_window_size sLM = 2 * Z.shiftl 1 wb9
    /\ ds_hash_mask sLM = Z.shiftl 1 (meml + 7) - 1 /\ ds_hash_shift sLM = (meml + 7 + 3 - 1) / 3
    /\ ds_pending_buf_size sLM = Z.shiftl 1 (meml + 6) * 4 /\ ds_sym_end sLM = (Z.shiftl 1 (meml + 6) - 1) * 3.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma blks_LM :
    ds_self_blk sLM = b0 /\ ds_window_blk sLM = Some bw /\ ds_prev_blk sLM = Some bp /\ ds_head_blk sLM = Some bh
    /\ ds_pending_buf_blk sLM = Some bb.
  Proof. vals_nf. repeat split; reflexivity. Qed.

  Lemma strm_LM :
    ds_strm sLM = cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN) rk_adler'.
  Proof. vals_nf. reflexivity. Qed.

  Lemma zret_LM : forall rc, cs_next_in cs = 0 -> cs_out_rev cs = [] ->
    zr_consumed (zret_of_cs (ds_strm sLM) rc) = 0 /\ zr_output (zret_of_cs (ds_strm sLM) rc) = []
    /\ zr_rc (zret_of_cs (ds_strm sLM) rc) = rc
    /\ zs_total_in (zr_strm (zret_of_cs (ds_strm sLM) rc)) = 0
    /\ zs_total_out (zr_strm (zret_of_cs (ds_strm sLM) rc)) = 0
    /\ zs_adler (zr_strm (zret_of_cs (ds_strm sLM) rc)) = rk_adler'
    /\ zs_data_type (zr_strm (zret_of_cs (ds_strm sLM) rc)) = Z_UNKNOWN.
  Proof.
    intros rc H1 H2. rewrite strm_LM. unfold zret_of_cs, zstrm_of_cs, cs_output. destruct cs; cbn in H1, H2 |- *. subst. repeat split; reflexivity.
  Qed.



  Lemma dwf_LM : 9 <= wb9 <= 15 -> 1 <= meml <= 9 -> 0 <= lv <= 9 -> 0 <= strat <= 4 -> method = 8 -> 0 <= wrp <= 2 ->
    dwf sLM.
  Proof.
    intros Hwb Hml Hlv Hst Hm Hwr.
    pose proof sizes_LM as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17).
    pose proof blks_LM as (B1 & B2 & B3 & B4 & B5).
    pose proof arrs_LM as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
    assert (Hp1 : 0 < Z.shiftl 1 wb9) by (rewrite Z.shiftl_1_l; apply Z.pow_pos_nonneg; lia).
    assert (Hp2 : 0 < Z.shiftl 1 (meml + 7)) by (rewrite Z.shiftl_1_l; apply Z.pow_pos_nonneg; lia).
    constructor.
    - unfold deflateStateCheck. rewrite E10. unfold rk_status'. destruct (wrp =? 2); reflexivity.
    - rewrite B2. discriminate.
    - rewrite B3. discriminate.
    - rewrite B4. discriminate.
    - rewrite B5. discriminate.
    - rewrite E4. lia.
    - rewrite E1, E4, Z.shiftl_1_l. reflexivity.
    - rewrite E12, E1. reflexivity.
    - rewrite E13, E1. reflexivity.
    - rewrite E5. lia.
    - rewrite E2, E5, Z.shiftl_1_l. reflexivity.
    - rewrite E14, E2. reflexivity.
    - rewrite E15, E5. reflexivity.
    - rewrite E3, E5, Z.shiftl_1_l. replace (meml + 7 - 1) with (meml + 6) by lia. reflexivity.
    - rewrite E16, E3. reflexivity.
    - rewrite E17, E3. reflexivity.
    - rewrite A11, E1. unfold blk_bytes. rewrite arr_len_init. reflexivity.
    - rewrite A12, E1. unfold blk_ush. rewrite arr_len_init. reflexivity.
    - rewrite A13, E2. rewrite arr_len_fill, arr_len_set. unfold blk_ush. rewrite arr_len_init. reflexivity.
    - rewrite A10, E3. unfold blk_bytes. rewrite arr_len_init. reflexivity.
    - exact tree_lens_LM.
    - exact E11.
    - rewrite E8, Hm. reflexivity.
    - rewrite E6. exact Hlv.
    - rewrite E7. unfold Z_FIXED. exact Hst.
    - rewrite E9. lia.
    - replace (ds_strstart sLM) with 0 by (vals_nf; reflexivity). lia.
    - replace (ds_insert sLM) with 0 by (vals_nf; reflexivity). replace (ds_strstart sLM) with 0 by (vals_nf; reflexivity). lia.
    - replace (ds_lookahead sLM) with 0 by (vals_nf; reflexivity). lia.
    - replace (ds_strstart sLM) with 0 by (vals_nf; reflexivity). replace (ds_lookahead sLM) with 0 by (vals_nf; reflexivity). rewrite E1. lia.
    - replace (ds_match_start sLM) with (init_u32 g0 176 0) by (vals_nf; reflexivity). apply init_u32_range.
    - replace (ds_ins_h sLM) with 0 by (vals_nf; reflexivity). lia.
    - replace (ds_high_water sLM) with 0 by (vals_nf; reflexivity). lia.
    - replace (ds_block_start sLM) with 0 by (vals_nf; reflexivity). lia.
    - rewrite A11, E1. intros i Hi. unfold blk_bytes. rewrite arr_get_init. apply init_u8_range.
    - rewrite A12, E1. intros i Hi. unfold blk_ush. rewrite arr_get_init. apply init_u16_range.
    - rewrite A13, E2. intros i Hi. rewrite head_clearedg by lia. lia.
  Qed.

End V.
