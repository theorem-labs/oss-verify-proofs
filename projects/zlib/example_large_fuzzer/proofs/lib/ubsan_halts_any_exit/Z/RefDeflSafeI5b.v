(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma wrap8_range' : forall z, 0 <= wrap8 z < 256.
Proof. intros z. pose proof (wrap8_range z). change (2 ^ 8) with 256 in H. lia. Qed.
Lemma init_u8_range : forall g b i, 0 <= init_u8 g b i < 256.
Proof. intros. unfold init_u8. apply wrap8_range'. Qed.
Lemma init_u16_range : forall g b i, 0 <= init_u16 g b i < 65536.
Proof. intros. unfold init_u16. pose proof (wrap8_range' (g (b + 2 * i))). pose proof (wrap8_range' (g (b + 2 * i + 1))). lia. Qed.
Lemma init_u32_range : forall g b i, 0 <= init_u32 g b i < 2 ^ 32.
Proof. intros. unfold init_u32. pose proof (init_u16_range g b (2 * i)). pose proof (init_u16_range g b (2 * i + 1)). lia. Qed.

Lemma cleared_get : forall (a : arr) n h, arr_len a = n -> 0 <= h < n ->
  arr_get (arr_fill (arr_set a (n - 1) NIL) 0 (n - 1) 0) h = 0.
Proof.
  intros a n h Hl Hh. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hl.
  destruct (Z_lt_le_dec h (n - 1)).
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (n - 1)) && ((0 <=? h) && (h <? n))) with true
      by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  - replace ((0 <=? h) && (h <? 0 + Z.max 0 (n - 1)) && ((0 <=? h) && (h <? n))) with false
      by (symmetry; apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    replace h with (n - 1) by lia. rewrite arr_get_set_same by (rewrite Hl; lia). reflexivity.
Qed.

Section InitState.
  Variable b0 : blk.
Variable bw : blk.
Variable bp : blk.
Variable bh : blk.
Variable bb : blk.
Variable g0 : Z -> Z.
Variable gw : Z -> Z.
Variable gp : Z -> Z.
Variable gh : Z -> Z.
Variable gb : Z -> Z.
Variable cs : cstrm.
Variable wrap : Z.
Variable wb9 : Z.
Variable meml : Z.
Variable lv : Z.
Variable strat : Z.
Variable method : Z.

  Definition S5g : deflate_state :=
    s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 meml) (Some (bw, gw))) (Some (bp, gp))) (Some (bh, gh))) meml) (Some (bb, gb)).

  Definition dFg : deflate_state :=
   {| ds_status := if wrap =? 2 then GZIP_STATE else INIT_STATE;
      ds_pending_buf := blk_bytes gb (Z.shiftl 1 (meml + 6) * 4);
      ds_pending_buf_size := Z.shiftl 1 (meml + 6) * 4;
      ds_pending_out := 0;
      ds_pending := 0;
      ds_wrap := wrap;
      ds_gzhead := 0;
      ds_gzindex := init_u64 g0 64 0;
      ds_method := wrap8 method;
      ds_last_flush := -2;
      ds_w_size := Z.shiftl 1 wb9;
      ds_w_bits := wb9;
      ds_w_mask := Z.shiftl 1 wb9 - 1;
      ds_window := blk_bytes gw (2 * Z.shiftl 1 wb9);
      ds_window_size := 2 * Z.shiftl 1 wb9;
      ds_prev := blk_ush gp (Z.shiftl 1 wb9);
      ds_head := arr_fill (arr_set (blk_ush gh (Z.shiftl 1 (meml + 7))) (Z.shiftl 1 (meml + 7) - 1) 0) 0 (Z.shiftl 1 (meml + 7) - 1) 0;
      ds_ins_h := 0;
      ds_hash_size := Z.shiftl 1 (meml + 7);
      ds_hash_bits := meml + 7;
      ds_hash_mask := Z.shiftl 1 (meml + 7) - 1;
      ds_hash_shift := (meml + 7 + MIN_MATCH - 1) / MIN_MATCH;
      ds_block_start := 0;
      ds_match_length := MIN_MATCH - 1;
      ds_prev_match := init_u32 g0 164 0;
      ds_match_available := 0;
      ds_strstart := 0;
      ds_match_start := init_u32 g0 176 0;
      ds_lookahead := 0;
      ds_prev_length := MIN_MATCH - 1;
      ds_max_chain_length := cfg_chain lv;
      ds_max_lazy_match := cfg_lazy lv;
      ds_level := lv;
      ds_strategy := strat;
      ds_good_match := cfg_good lv;
      ds_nice_match := cfg_nice lv;
      ds_dyn_ltree_fc := arr_set (arr_fill (arr_u16_of g0 212 4 573) 0 L_CODES 0) END_BLOCK (wrap16 1);
      ds_dyn_ltree_dl := arr_u16_of g0 214 4 573;
      ds_dyn_dtree_fc := arr_fill (arr_u16_of g0 2504 4 61) 0 D_CODES 0;
      ds_dyn_dtree_dl := arr_u16_of g0 2506 4 61;
      ds_bl_tree_fc := arr_fill (arr_u16_of g0 2748 4 39) 0 BL_CODES 0;
      ds_bl_tree_dl := arr_u16_of g0 2750 4 39;
      ds_l_max_code := swrap32 (init_u32 g0 2912 0);
      ds_d_max_code := swrap32 (init_u32 g0 2936 0);
      ds_bl_max_code := swrap32 (init_u32 g0 2960 0);
      ds_bl_count := arr_u16_of g0 2976 2 16;
      ds_heap := arr_s32_of g0 3008 4 573;
      ds_heap_len := swrap32 (init_u32 g0 5300 0);
      ds_heap_max := swrap32 (init_u32 g0 5304 0);
      ds_depth := arr_u8_of g0 5308 1 573;
      ds_lit_bufsize := Z.shiftl 1 (meml + 6);
      ds_sym_next := 0;
      ds_sym_end := (Z.shiftl 1 (meml + 6) - 1) * 3;
      ds_opt_len := 0;
      ds_static_len := 0;
      ds_matches := 0;
      ds_insert := 0;
      ds_bi_buf := 0;
      ds_bi_valid := 0;
      ds_high_water := 0;
      ds_self_blk := b0;
      ds_window_blk := Some bw;
      ds_prev_blk := Some bp;
      ds_head_blk := Some bh;
      ds_pending_buf_blk := Some bb;
      ds_strm := cset_adler (cset_data_type (cset_msg (cset_total_out (cset_total_in cs 0) 0) MSG_NULL) Z_UNKNOWN)
                            (if wrap =? 2 then crc32_init else adler32_init) |}.

  Lemma dFg_eq : LM (tr_init (RK0 (s_fin S5g lv strat method))) = dFg.
  Proof. reflexivity. Qed.

  Lemma reset_S5g : 0 <= wrap -> deflateReset (s_fin S5g lv strat method) = (dFg, Z_OK).
  Proof.
    intros Hw. rewrite deflateReset_eq; [| reflexivity | exact Hw].
    rewrite dFg_eq. reflexivity.
  Qed.

  Hypothesis H1 : 9 <= wb9 <= 15.
  Hypothesis H2 : 5 <= meml <= 9.
  Hypothesis H3 : 0 <= lv <= 9.
  Hypothesis H4 : 0 <= strat <= 4.
  Hypothesis H5 : 0 <= wrap <= 2.
  Hypothesis H6 : method = 8.

  Let Ews : Z.shiftl 1 wb9 = 2 ^ wb9 := Z.shiftl_1_l wb9.
  Let Ehs : Z.shiftl 1 (meml + 7) = 2 ^ (meml + 7) := Z.shiftl_1_l (meml + 7).
  Let Elbs : Z.shiftl 1 (meml + 6) = 2 ^ (meml + 6) := Z.shiftl_1_l (meml + 6).

  Lemma dFg_head0 : forall h, 0 <= h < Z.shiftl 1 (meml + 7) -> arr_get (ds_head dFg) h = 0.
  Proof.
    intros h Hh. cbn [ds_head dFg]. apply (cleared_get (blk_ush gh (Z.shiftl 1 (meml + 7)))); [| exact Hh].
    unfold blk_ush. rewrite arr_len_init. reflexivity.
  Qed.

  Lemma dFg_dwf : dwf dFg.
  Proof.
    pose proof (pow2_range_9_15 wb9 H1) as R1. pose proof (pow2_range_8_16 (meml + 7) ltac:(lia)) as R2. pose proof (pow2_range_7_15 (meml + 6) ltac:(lia)) as R3.
    pose proof dFg_head0 as Hh0. cbn [ds_head dFg] in Hh0.
    constructor; cbn [ds_status ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_w_bits ds_w_size ds_w_mask ds_window_size
                      ds_hash_bits ds_hash_size ds_hash_mask ds_hash_shift ds_lit_bufsize ds_pending_buf_size ds_sym_end ds_window ds_prev ds_head
                      ds_pending_buf ds_gzhead ds_method ds_level ds_strategy ds_wrap ds_strstart
                      ds_insert ds_lookahead ds_match_start ds_ins_h ds_high_water
                      ds_last_flush ds_pending ds_pending_out ds_bi_buf ds_bi_valid dFg];
      rewrite ?Ews, ?Ehs, ?Elbs in *;
      try discriminate; try lia;
      first
      [ unfold deflateStateCheck; cbn [ds_status dFg]; destruct (wrap =? 2); reflexivity
      | unfold GZIP_STATE, INIT_STATE; destruct (wrap =? 2); lia
      | replace (meml + 7 - 1) with (meml + 6) by lia; reflexivity
      | unfold blk_bytes; rewrite arr_len_init; lia
      | unfold blk_ush; rewrite arr_len_init; lia
      | rewrite arr_len_fill, arr_len_set; unfold blk_ush; rewrite arr_len_init; lia
      | unfold tree_lens; cbn [ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth dFg];
        rewrite ?arr_len_set, ?arr_len_fill; unfold arr_u16_of, arr_s32_of, arr_u8_of; rewrite !arr_len_init; unfold HEAP_SIZE, L_CODES, D_CODES, BL_CODES, MAX_BITS; lia
      | rewrite H6; reflexivity
      | unfold Z_FIXED; lia
      | pose proof (init_u32_range g0 176 0); lia
      | vm_compute; split; [discriminate | reflexivity]
      | intros i Hi; unfold blk_bytes; rewrite arr_get_init; apply init_u8_range
      | intros i Hi; unfold blk_ush; rewrite arr_get_init; apply init_u16_range
      | intros i Hi; rewrite (Hh0 i Hi); lia
      | match goal with |- ?g => idtac "DWFLEFT" g end ].
  Qed.

  Lemma dFg_BQ : BQ dFg /\ nsym dFg = 0.
  Proof.
    apply BQ_fresh; cbn [ds_sym_next ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc dFg].
    - reflexivity.
    - intros c Hc. unfold L_CODES, LITERALS, LENGTH_CODES in *. rewrite arr_get_set. unfold arr_inb. rewrite arr_len_fill. unfold arr_u16_of. rewrite arr_len_init.
      unfold END_BLOCK. destruct (Z.eqb_spec 256 c) as [<-|Hne].
      + replace ((256 =? 256) && ((0 <=? 256) && (256 <? 573))) with true by reflexivity. reflexivity.
      + replace (256 =? c) with false by (symmetry; apply Z.eqb_neq; exact Hne). cbn [andb].
        rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_init.
        replace ((0 <=? c) && (c <? 0 + Z.max 0 286) && ((0 <=? c) && (c <? 573))) with true
          by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        try replace (c =? 256) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    - intros d Hd. unfold D_CODES in *. rewrite arr_get_fill. unfold arr_inb, arr_u16_of. rewrite arr_len_init.
      replace ((0 <=? d) && (d <? 0 + Z.max 0 30) && ((0 <=? d) && (d <? 61))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - intros b Hb. unfold BL_CODES in *. rewrite arr_get_fill. unfold arr_inb, arr_u16_of. rewrite arr_len_init.
      replace ((0 <=? b) && (b <? 0 + Z.max 0 19) && ((0 <=? b) && (b <? 39))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
  Qed.

  Lemma u16_cells : forall g off st n i, 0 <= arr_get (arr_u16_of g off st n) i < 65536.
  Proof. intros. unfold arr_u16_of. rewrite arr_get_init. apply init_u16_range. Qed.

  Lemma fill_cells : forall (a : arr) ofs n i, (forall j, 0 <= arr_get a j < 65536) -> 0 <= arr_get (arr_fill a ofs n 0) i < 65536.
  Proof. intros a ofs n i Ha. rewrite arr_get_fill. destruct (_ && _); [lia | apply Ha]. Qed.

  Lemma dFg_DX : DX dFg.
  Proof.
    pose proof (pow2_range_9_15 wb9 H1) as R1. pose proof (pow2_range_8_16 (meml + 7) ltac:(lia)) as R2. pose proof (pow2_range_7_15 (meml + 6) ltac:(lia)) as R3.
    destruct dFg_BQ as [(Q1 & Q2 & Q3 & Q4) Qn].
    assert (Hm : 0 <= dmode dFg <= 4) by (apply dmode_range).
    constructor; rewrite ?Qn;
      cbn [ds_good_match ds_max_lazy_match ds_nice_match ds_max_chain_length ds_level ds_ins_h ds_insert ds_w_size ds_match_length ds_prev_length
           ds_match_available ds_prev_match ds_matches ds_high_water ds_window_size ds_lookahead ds_strstart ds_match_start ds_block_start
           ds_sym_next ds_wrap ds_status ds_lit_bufsize ds_opt_len ds_static_len ds_depth ds_bl_count ds_pending ds_pending_out ds_bi_valid dFg];
      rewrite ?Ews, ?Ehs, ?Elbs in *; unfold MIN_MATCH, MAX_MATCH; try lia.
    - symmetry. apply cfg_eta.
    - pose proof (init_u32_range g0 164 0). lia.
    - exact Q4.
    - intros t i. destruct t; cbn [tree_fc ds_dyn_ltree_fc ds_dyn_dtree_fc ds_bl_tree_fc dFg].
      + rewrite arr_get_set. destruct (_ && _); [pose proof (wrap16_range 1) as W; change (2 ^ 16) with 65536 in W; lia | apply fill_cells; intros j; apply u16_cells].
      + apply fill_cells; intros j; apply u16_cells.
      + apply fill_cells; intros j; apply u16_cells.
    - intros t i. destruct t; cbn [tree_dl ds_dyn_ltree_dl ds_dyn_dtree_dl ds_bl_tree_dl dFg]; apply u16_cells.
    - intros i. unfold arr_u8_of. rewrite arr_get_init. apply init_u8_range.
    - intros i Hi. apply u16_cells.
    - intros _. apply CHAIN_heads0. cbn [ds_hash_size dFg]. exact dFg_head0.
  Qed.

  Lemma dFg_DD : DD dFg.
  Proof. split; [exact dFg_dwf | exact dFg_DX]. Qed.
End InitState.


Definition ohd (chs : DCH) : option (blk * (Z -> Z)) := match chs with [] => None | c :: _ => c end.
Definition otl (chs : DCH) : DCH := match chs with [] => [] | _ :: t => t end.

Lemma dhooks_zalloc : forall a b chs, zalloc dhooks a b chs = MRet (ohd chs, otl chs).
Proof. intros a b [|c t]; reflexivity. Qed.

Definition dend_rc (s : deflate_state) : Z := if ds_status s =? BUSY_STATE then Z_DATA_ERROR else Z_OK.
Lemma dhooks_end : forall s chs, deflateEnd_core dhooks s chs = MRet (dend_rc s, chs).
Proof.
  intros s chs. unfold deflateEnd_core, try_free.
  destruct (ds_pending_buf_blk s), (ds_head_blk s), (ds_prev_blk s), (ds_window_blk s); reflexivity.
Qed.

Lemma dpure_sbind' : forall A B (m : SM DCH A) (f : A -> SM DCH B) chs a chs',
  m chs = MRet (a, chs') -> dpure (sbind m f) chs = dpure (f a) chs'.
Proof. intros A B m f chs a chs' H. unfold dpure, sbind. rewrite H. reflexivity. Qed.

Ltac dpeel' name :=
  lazymatch goal with
  | |- dpure (let x := ?v in @?b x) ?c = ?r => set (name := v); change (dpure (b name) c = r); cbv beta
  end.

Definition S5og (b0 : blk) (g0 : Z -> Z) (cs : cstrm) (wrap wb9 meml : Z) (rw rp rh rb : option (blk * (Z -> Z))) : deflate_state :=
  s_pb (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 cs wrap wb9 meml) rw) rp) rh) meml) rb.

Lemma S5og_proj : forall b0 g0 cs wrap wb9 meml rw rp rh rb,
  let s := S5og b0 g0 cs wrap wb9 meml rw rp rh rb in
  ds_window_blk s = option_map fst rw /\ ds_prev_blk s = option_map fst rp /\ ds_head_blk s = option_map fst rh
  /\ ds_pending_buf_blk s = option_map fst rb.
Proof.
  intros. subst s. unfold S5og.
  split; [apply s5_window_blk|]. split; [apply s5_prev_blk|]. split; [apply s5_head_blk | apply s5_pending_buf_blk].
Qed.

Lemma some_pair_fst : forall {A B} (a : A * B) (x : A) (y : B), Some a = Some (x, y) -> fst a = x.
Proof. intros A B a x y H. injection H as H'. subst a. reflexivity. Qed.
Lemma some_pair_inj1 : forall {A B} (x1 x2 : A) (y1 y2 : B), Some (x1, y1) = Some (x2, y2) -> x1 = x2.
Proof. intros A B x1 x2 y1 y2 H. injection H as H1 H2. exact H1. Qed.

Section Run.
  Variable zc : ZCall.
Variable level : Z.
Variable method : Z.
Variable wb : Z.
Variable meml : Z.
Variable strategy : Z.
  Hypothesis HML5 : 5 <= meml.

  Definition dinit_body (s5 : deflate_state) : option deflate_state * ZRet :=
    if all_some s5
    then (Some (fst (deflateReset (s_fin s5 (di_level level) strategy method))),
          zret_of_cs (ds_strm (fst (deflateReset (s_fin s5 (di_level level) strategy method))))
                     (snd (deflateReset (s_fin s5 (di_level level) strategy method))))
    else (None, zret_of_cs (ds_strm (s_fail s5)) Z_MEM_ERROR).

  Lemma dinit_run_bad : forall chs, di_bad level method wb meml strategy = true ->
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (None, zret_of_cs (cs_init zc) Z_STREAM_ERROR).
  Proof.
    intros chs Hbad. unfold di_bad in Hbad.
    cbv delta [deflateInit2_m]. cbv beta.
    dpeel' csX. dpeel' lvX. rewrite di_triple. cbv beta iota.
    lazymatch goal with |- dpure (if _ then _ else if ?c then _ else _) _ = _ => replace c with (di_chk level method wb meml strategy) by reflexivity end.
    apply Bool.orb_true_iff in Hbad. destruct ((wb <? 0) && (wb <? -15)) eqn:Hb0.
    - cbv beta iota delta [dpure sret fst]. subst csX. reflexivity.
    - destruct Hbad as [Hbad|Hbad]; [discriminate Hbad|]. rewrite Hbad. cbv beta iota delta [dpure sret fst]. subst csX. reflexivity.
  Qed.

  Lemma dinit_run : forall chs, di_bad level method wb meml strategy = false ->
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs =
    Some (match ohd chs with
          | None => (None, zret_of_cs (cs_init zc) Z_MEM_ERROR)
          | Some (b0, g0) =>
            dinit_body (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml
                          (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs))))))
          end).
  Proof.
    intros chs Hbad. unfold di_bad in Hbad. apply Bool.orb_false_iff in Hbad as [Hb0 Hchk].
    cbv delta [deflateInit2_m]. cbv beta.
    dpeel' csX. dpeel' lvX. rewrite di_triple. cbv beta iota. rewrite Hb0.
    lazymatch goal with |- dpure (if ?c then _ else _) _ = _ => replace c with (di_chk level method wb meml strategy) by reflexivity end.
    rewrite Hchk. dpeel' wb9X.
    erewrite dpure_sbind' by apply dhooks_zalloc.
    destruct (ohd chs) as [[b0 g0]|].
    2: { cbv beta iota delta [dpure sret fst]. subst csX. reflexivity. }
    cbv beta iota.
    dpeel' s0'. dpeel' s1'. dpeel' s2'. dpeel' s3'. dpeel' s4'. dpeel' s5'. dpeel' s6'. dpeel' s7'. dpeel' s8'. dpeel' s9'. dpeel' s10'.
    replace s10' with (s_setup g0 b0 csX (di_wrap wb) wb9X meml) by reflexivity. clear s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s11'.
    replace s11' with (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) by reflexivity. clear s11'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s12'.
    replace s12' with (s_prv (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) (ohd (otl (otl chs)))) by reflexivity. clear s12'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s13'. dpeel' s14'. dpeel' s15'.
    replace s15' with (s_lbs (s_hd (s_prv (s_win (s_setup g0 b0 csX (di_wrap wb) wb9X meml) (ohd (otl chs))) (ohd (otl (otl chs)))) (ohd (otl (otl (otl chs))))) meml) by reflexivity.
    clear s15' s14' s13'.
    erewrite dpure_sbind' by apply dhooks_zalloc. cbv beta. dpeel' s16'. dpeel' s17'.
    replace s17' with (S5og b0 g0 csX (di_wrap wb) wb9X meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) by reflexivity.
    clear s17' s16'.
    subst csX lvX wb9X. change (cset_msg (cstrm_of_call zc) MSG_NULL) with (cs_init zc).
    change (if level =? Z_DEFAULT_COMPRESSION then 6 else level) with (di_level level).
    change (if di_wb wb =? 8 then 9 else di_wb wb) with (di_wb9 wb).
    remember (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as S5 eqn:ES5.
    pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as PJ.
    cbv zeta in PJ. rewrite <- ES5 in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
    unfold dinit_body, all_some. rewrite Ew, Ep, Eh, Eb.
    destruct (ohd (otl chs)) as [[bw gw]|]; [destruct (ohd (otl (otl chs))) as [[bp gp]|]; [destruct (ohd (otl (otl (otl chs)))) as [[bh gh]|];
      [destruct (ohd (otl (otl (otl (otl chs))))) as [[bb gb]|]|]|]|]; cbv beta iota delta [option_map].
    1: { change (set_method (set_strategy (set_level (set_sym_end S5 ((ds_lit_bufsize S5 - 1) * 3)) (di_level level)) strategy) (wrap8 method))
           with (s_fin S5 (di_level level) strategy method).
         destruct (deflateReset (s_fin S5 (di_level level) strategy method)) as [s' rc'].
         cbv beta iota delta [dpure sret fst snd]. reflexivity. }
    all: change (set_strm (set_status S5 FINISH_STATE) (cset_msg (ds_strm (set_status S5 FINISH_STATE)) (MSG_ERR Z_MEM_ERROR))) with (s_fail S5);
         erewrite dpure_sbind' by apply dhooks_end; cbv beta iota delta [dpure sret fst]; reflexivity.
  Qed.

  Lemma dinit_some : forall chs s zr,
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (Some s, zr) ->
    di_bad level method wb meml strategy = false
    /\ exists b0 g0 bw gw bp gp bh gh bb gb,
         s = fst (deflateReset (s_fin (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml) (di_level level) strategy method)).
  Proof.
    intros chs s zr H.
    destruct (di_bad level method wb meml strategy) eqn:Hbad.
    { rewrite (dinit_run_bad chs Hbad) in H. exfalso. apply some_pair_fst in H. cbn [fst] in H. discriminate H. }
    split; [reflexivity|].
    rewrite (dinit_run chs Hbad) in H.
    destruct (ohd chs) as [[b0 g0]|]; [| exfalso; apply some_pair_fst in H; cbn [fst] in H; discriminate H].
    cbv beta iota in H.
    remember (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as S5 eqn:ES5.
    pose proof (S5og_proj b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (ohd (otl chs)) (ohd (otl (otl chs))) (ohd (otl (otl (otl chs)))) (ohd (otl (otl (otl (otl chs)))))) as PJ.
    cbv zeta in PJ. rewrite <- ES5 in PJ. destruct PJ as (Ew & Ep & Eh & Eb).
    unfold dinit_body, all_some in H. rewrite Ew, Ep, Eh, Eb in H.
    destruct (ohd (otl chs)) as [[bw gw]|]; [destruct (ohd (otl (otl chs))) as [[bp gp]|]; [destruct (ohd (otl (otl (otl chs)))) as [[bh gh]|];
      [destruct (ohd (otl (otl (otl (otl chs))))) as [[bb gb]|]|]|]|]; cbv beta iota delta [option_map] in H.
    1: { apply some_pair_inj1 in H. injection H as H1.
         exists b0, g0, bw, gw, bp, gp, bh, gh, bb, gb.
         change (S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml)
           with (S5og b0 g0 (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (Some (bw, gw)) (Some (bp, gp)) (Some (bh, gh)) (Some (bb, gb))).
         rewrite <- ES5. symmetry. exact H1. }
    all: exfalso; apply some_pair_inj1 in H; discriminate H.
  Qed.

  Theorem dinit_DD : forall chs s zr,
    dpure (deflateInit2_m dhooks zc level method wb meml strategy) chs = Some (Some s, zr) -> DD s.
  Proof.
    intros chs s zr H. destruct (dinit_some chs s zr H) as [Hbad (b0 & g0 & bw & gw & bp & gp & bh & gh & bb & gb & Es)].
    unfold di_bad in Hbad. apply Bool.orb_false_iff in Hbad as [Hb0 Hc].
    unfold di_chk, MAX_MEM_LEVEL, Z_DEFLATED, Z_FIXED in Hc.
    apply Bool.orb_false_iff in Hc as [Hc C10].
    apply Bool.orb_false_iff in Hc as [Hc C9]. apply Z.ltb_ge in C9.
    apply Bool.orb_false_iff in Hc as [Hc C8]. apply Z.ltb_ge in C8.
    apply Bool.orb_false_iff in Hc as [Hc C7]. apply Z.ltb_ge in C7.
    apply Bool.orb_false_iff in Hc as [Hc C6]. apply Z.ltb_ge in C6.
    apply Bool.orb_false_iff in Hc as [Hc C5]. apply Z.ltb_ge in C5.
    apply Bool.orb_false_iff in Hc as [Hc C4]. apply Z.ltb_ge in C4.
    apply Bool.orb_false_iff in Hc as [Hc C3]. apply Bool.negb_false_iff in C3. apply Z.eqb_eq in C3.
    apply Bool.orb_false_iff in Hc as [C1 C2]. apply Z.ltb_ge in C1. apply Z.ltb_ge in C2.
    pose proof (di_wrap_range wb) as Hwr.
    assert (H9 : 9 <= di_wb9 wb <= 15).
    { unfold di_wb9. destruct (Z.eqb_spec (di_wb wb) 8) as [E8|N8]; lia. }
    rewrite (reset_S5g b0 bw bp bh bb g0 gw gp gh gb (cs_init zc) (di_wrap wb) (di_wb9 wb) meml (di_level level) strategy method (proj1 Hwr)) in Es.
    cbn [fst] in Es. subst s.
    apply dFg_DD; try assumption; lia.
  Qed.
End Run.
