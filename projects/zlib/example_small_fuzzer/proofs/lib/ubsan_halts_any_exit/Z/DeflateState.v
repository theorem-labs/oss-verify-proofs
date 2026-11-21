(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import NArith.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition STORED_BLOCK : Z := 0.
Definition STATIC_TREES : Z := 1.
Definition DYN_TREES : Z := 2.
Definition MIN_MATCH : Z := 3.
Definition MAX_MATCH : Z := 258.
Definition PRESET_DICT : Z := 32.
Definition OS_CODE : Z := 3.
Definition ERR_MSG (err : Z) : Z := MSG_ERR err.

Definition LENGTH_CODES : Z := 29.
Definition LITERALS : Z := 256.
Definition L_CODES : Z := 286.
Definition D_CODES : Z := 30.
Definition BL_CODES : Z := 19.
Definition HEAP_SIZE : Z := 573.
Definition MAX_BITS : Z := 15.
Definition Buf_size : Z := 16.
Definition INIT_STATE : Z := 42.
Definition GZIP_STATE : Z := 57.
Definition EXTRA_STATE : Z := 69.
Definition NAME_STATE : Z := 73.
Definition COMMENT_STATE : Z := 91.
Definition HCRC_STATE : Z := 103.
Definition BUSY_STATE : Z := 113.
Definition FINISH_STATE : Z := 666.
Definition MIN_LOOKAHEAD : Z := MAX_MATCH + MIN_MATCH + 1.
Definition WIN_INIT : Z := MAX_MATCH.
Definition MAX_BL_BITS : Z := 7.
Definition END_BLOCK : Z := 256.
Definition REP_3_6 : Z := 16.
Definition REPZ_3_10 : Z := 17.
Definition REPZ_11_138 : Z := 18.
Definition DIST_CODE_LEN : Z := 512.
Definition SMALLEST : Z := 1.
Definition NIL : Z := 0.
Definition TOO_FAR : Z := 4096.
Definition MAX_STORED : Z := 65535.
Definition LIT_BUFS : Z := 4.
Definition SIZEOF_deflate_state : Z := 5952.


Definition static_ltree_code_l : list Z := [
  12;140;76;204;44;172;108;236;28;156;92;220;60;188;124;252;2;130;66;194;34;
  162;98;226;18;146;82;210;50;178;114;242;10;138;74;202;42;170;106;234;26;154;
  90;218;58;186;122;250;6;134;70;198;38;166;102;230;22;150;86;214;54;182;118;
  246;14;142;78;206;46;174;110;238;30;158;94;222;62;190;126;254;1;129;65;193;
  33;161;97;225;17;145;81;209;49;177;113;241;9;137;73;201;41;169;105;233;25;
  153;89;217;57;185;121;249;5;133;69;197;37;165;101;229;21;149;85;213;53;181;
  117;245;13;141;77;205;45;173;109;237;29;157;93;221;61;189;125;253;19;275;
  147;403;83;339;211;467;51;307;179;435;115;371;243;499;11;267;139;395;75;331;
  203;459;43;299;171;427;107;363;235;491;27;283;155;411;91;347;219;475;59;315;
  187;443;123;379;251;507;7;263;135;391;71;327;199;455;39;295;167;423;103;359;
  231;487;23;279;151;407;87;343;215;471;55;311;183;439;119;375;247;503;15;271;
  143;399;79;335;207;463;47;303;175;431;111;367;239;495;31;287;159;415;95;351;
  223;479;63;319;191;447;127;383;255;511;0;64;32;96;16;80;48;112;8;72;40;104;
  24;88;56;120;4;68;36;100;20;84;52;116;3;131;67;195;35;163;99;227].

Definition static_ltree_len_l : list Z := [
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;
  8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;9;9;9;9;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;
  9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;9;7;7;7;7;7;7;7;7;7;7;
  7;7;7;7;7;7;7;7;7;7;7;7;7;7;8;8;8;8;8;8;8;8].

Definition static_dtree_code_l : list Z := [
  0;16;8;24;4;20;12;28;2;18;10;26;6;22;14;30;1;17;9;25;5;21;13;29;3;19;11;27;
  7;23].

Definition static_dtree_len_l : list Z := [
  5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5;5].

Definition dist_code_l : list Z := [
  0;1;2;3;4;4;5;5;6;6;6;6;7;7;7;7;8;8;8;8;8;8;8;8;9;9;9;9;9;9;9;9;10;10;10;10;
  10;10;10;10;10;10;10;10;10;10;10;10;11;11;11;11;11;11;11;11;11;11;11;11;11;
  11;11;11;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;12;
  12;12;12;12;12;12;12;12;12;12;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;
  13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;13;14;14;14;14;14;14;14;14;
  14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;
  14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;14;
  14;14;14;14;14;14;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;
  15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;
  15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;15;0;0;16;17;18;18;
  19;19;20;20;20;20;21;21;21;21;22;22;22;22;22;22;22;22;23;23;23;23;23;23;23;
  23;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;25;25;25;25;25;25;25;25;
  25;25;25;25;25;25;25;25;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;
  26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;27;27;27;27;27;27;27;27;27;27;
  27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;28;28;28;
  28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;
  28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;28;
  28;28;28;28;28;28;28;28;28;28;28;29;29;29;29;29;29;29;29;29;29;29;29;29;29;
  29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;
  29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29;29].

Definition length_code_l : list Z := [
  0;1;2;3;4;5;6;7;8;8;9;9;10;10;11;11;12;12;12;12;13;13;13;13;14;14;14;14;15;
  15;15;15;16;16;16;16;16;16;16;16;17;17;17;17;17;17;17;17;18;18;18;18;18;18;
  18;18;19;19;19;19;19;19;19;19;20;20;20;20;20;20;20;20;20;20;20;20;20;20;20;
  20;21;21;21;21;21;21;21;21;21;21;21;21;21;21;21;21;22;22;22;22;22;22;22;22;
  22;22;22;22;22;22;22;22;23;23;23;23;23;23;23;23;23;23;23;23;23;23;23;23;24;
  24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;24;
  24;24;24;24;24;24;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;25;
  25;25;25;25;25;25;25;25;25;25;25;25;25;26;26;26;26;26;26;26;26;26;26;26;26;
  26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;26;27;27;27;27;27;
  27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;27;
  27;28].

Definition base_length_l : list Z := [
  0;1;2;3;4;5;6;7;8;10;12;14;16;20;24;28;32;40;48;56;64;80;96;112;128;160;192;
  224;0].

Definition base_dist_l : list Z := [
  0;1;2;3;4;6;8;12;16;24;32;48;64;96;128;192;256;384;512;768;1024;1536;2048;
  3072;4096;6144;8192;12288;16384;24576].

Definition extra_lbits_l : list Z := [
  0;0;0;0;0;0;0;0;1;1;1;1;2;2;2;2;3;3;3;3;4;4;4;4;5;5;5;5;0].

Definition extra_dbits_l : list Z := [
  0;0;0;0;1;1;2;2;3;3;4;4;5;5;6;6;7;7;8;8;9;9;10;10;11;11;12;12;13;13].

Definition extra_blbits_l : list Z := [
  0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;2;3;7].

Definition bl_order_l : list Z := [
  16;17;18;0;8;7;9;6;10;5;11;4;12;3;13;2;14;1;15].

Definition static_ltree_fc : arr := arr_of_list static_ltree_code_l.
Definition static_ltree_dl : arr := arr_of_list static_ltree_len_l.
Definition static_dtree_fc : arr := arr_of_list static_dtree_code_l.
Definition static_dtree_dl : arr := arr_of_list static_dtree_len_l.
Definition dist_code_a : arr := arr_of_list dist_code_l.
Definition length_code_a : arr := arr_of_list length_code_l.
Definition base_length_a : arr := arr_of_list base_length_l.
Definition base_dist_a : arr := arr_of_list base_dist_l.
Definition extra_lbits_a : arr := arr_of_list extra_lbits_l.
Definition extra_dbits_a : arr := arr_of_list extra_dbits_l.
Definition extra_blbits_a : arr := arr_of_list extra_blbits_l.
Definition bl_order_a : arr := arr_of_list bl_order_l.

Definition d_code (dist : Z) : Z :=
  if Z.ltb dist 256 then arr_get dist_code_a dist
  else arr_get dist_code_a (256 + Z.shiftr dist 7).


Definition arr_u8_of (g : Z -> Z) (off stride n : Z) : arr :=
  arr_init n (fun i => init_u8 g (off + stride * i) 0).
Definition arr_u16_of (g : Z -> Z) (off stride n : Z) : arr :=
  arr_init n (fun i => init_u16 g (off + stride * i) 0).
Definition arr_s32_of (g : Z -> Z) (off stride n : Z) : arr :=
  arr_init n (fun i => swrap32 (init_u32 g (off + stride * i) 0)).


Record cstrm : Type := mkCS {
  cs_input : arr ;
  cs_next_in : Z ;
  cs_avail_in : Z ;
  cs_out_rev : list Z ;
  cs_avail_out : Z ;
  cs_total_in : Z ;
  cs_total_out : Z ;
  cs_msg : Z ;
  cs_data_type : Z ;
  cs_adler : Z
}.

Definition cset_input (s : cstrm) (v : arr) : cstrm :=
  mkCS v (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_next_in (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) v (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_avail_in (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) v (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_out_rev (s : cstrm) (v : list Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) v (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_avail_out (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) v (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_total_in (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) v (cs_total_out s) (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_total_out (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) v (cs_msg s) (cs_data_type s) (cs_adler s).
Definition cset_msg (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) v (cs_data_type s) (cs_adler s).
Definition cset_data_type (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) v (cs_adler s).
Definition cset_adler (s : cstrm) (v : Z) : cstrm :=
  mkCS (cs_input s) (cs_next_in s) (cs_avail_in s) (cs_out_rev s) (cs_avail_out s) (cs_total_in s) (cs_total_out s) (cs_msg s) (cs_data_type s) v.

Definition cs_in_at (st : cstrm) (k : Z) : Z := arr_get (cs_input st) (cs_next_in st + k).

Definition cs_emit (st : cstrm) (l : list Z) : cstrm :=
  cset_out_rev st (List.rev_append l (cs_out_rev st)).

Definition cs_output (st : cstrm) : list Z := List.rev_append (cs_out_rev st) [].

Definition cstrm_of_call (c : ZCall) : cstrm :=
  mkCS (arr_of_list (zc_input c)) 0 (zlength (zc_input c)) [] (zc_avail_out c)
       (zs_total_in (zc_strm c)) (zs_total_out (zc_strm c)) (zs_msg (zc_strm c))
       (zs_data_type (zc_strm c)) (zs_adler (zc_strm c)).

Definition zstrm_of_cs (st : cstrm) : zstrm :=
  ZIface.mkZS (cs_total_in st) (cs_total_out st) (cs_adler st) (cs_data_type st) (cs_msg st).
Definition zret_of_cs (st : cstrm) (rc : Z) : ZRet :=
  mkZRet (cs_next_in st) (cs_output st) (zstrm_of_cs st) rc.


Record deflate_state : Type := mkDS {
  ds_status : Z ;
  ds_pending_buf : arr ;
  ds_pending_buf_size : Z ;
  ds_pending_out : Z ;
  ds_pending : Z ;
  ds_wrap : Z ;
  ds_gzhead : Z ;
  ds_gzindex : Z ;
  ds_method : Z ;
  ds_last_flush : Z ;
  ds_w_size : Z ;
  ds_w_bits : Z ;
  ds_w_mask : Z ;
  ds_window : arr ;
  ds_window_size : Z ;
  ds_prev : arr ;
  ds_head : arr ;
  ds_ins_h : Z ;
  ds_hash_size : Z ;
  ds_hash_bits : Z ;
  ds_hash_mask : Z ;
  ds_hash_shift : Z ;
  ds_block_start : Z ;
  ds_match_length : Z ;
  ds_prev_match : Z ;
  ds_match_available : Z ;
  ds_strstart : Z ;
  ds_match_start : Z ;
  ds_lookahead : Z ;
  ds_prev_length : Z ;
  ds_max_chain_length : Z ;
  ds_max_lazy_match : Z ;
  ds_level : Z ;
  ds_strategy : Z ;
  ds_good_match : Z ;
  ds_nice_match : Z ;
  ds_dyn_ltree_fc : arr ;
  ds_dyn_ltree_dl : arr ;
  ds_dyn_dtree_fc : arr ;
  ds_dyn_dtree_dl : arr ;
  ds_bl_tree_fc : arr ;
  ds_bl_tree_dl : arr ;
  ds_l_max_code : Z ;
  ds_d_max_code : Z ;
  ds_bl_max_code : Z ;
  ds_bl_count : arr ;
  ds_heap : arr ;
  ds_heap_len : Z ;
  ds_heap_max : Z ;
  ds_depth : arr ;
  ds_lit_bufsize : Z ;
  ds_sym_next : Z ;
  ds_sym_end : Z ;
  ds_opt_len : Z ;
  ds_static_len : Z ;
  ds_matches : Z ;
  ds_insert : Z ;
  ds_bi_buf : Z ;
  ds_bi_valid : Z ;
  ds_high_water : Z ;
  ds_self_blk : blk ;
  ds_window_blk : option blk ;
  ds_prev_blk : option blk ;
  ds_head_blk : option blk ;
  ds_pending_buf_blk : option blk ;
  ds_strm : cstrm
}.

Definition set_status (s : deflate_state) (v : Z) : deflate_state :=
  mkDS v (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_pending_buf (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) v (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_pending_buf_size (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) v (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_pending_out (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) v (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_pending (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) v (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_wrap (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) v (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_gzhead (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) v (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_gzindex (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) v (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_method (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) v (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_last_flush (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) v (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_w_size (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) v (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_w_bits (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) v (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_w_mask (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) v (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_window (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) v (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_window_size (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) v (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_prev (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) v (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_head (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) v (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_ins_h (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) v (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_hash_size (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) v (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_hash_bits (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) v (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_hash_mask (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) v (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_hash_shift (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) v (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_block_start (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) v (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_match_length (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) v (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_prev_match (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) v (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_match_available (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) v (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_strstart (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) v (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_match_start (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) v (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_lookahead (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) v (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_prev_length (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) v (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_max_chain_length (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) v (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_max_lazy_match (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) v (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_level (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) v (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_strategy (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) v (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_good_match (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) v (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_nice_match (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) v (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_dyn_ltree_fc (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) v (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_dyn_ltree_dl (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) v (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_dyn_dtree_fc (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) v (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_dyn_dtree_dl (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) v (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bl_tree_fc (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) v (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bl_tree_dl (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) v (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_l_max_code (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) v (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_d_max_code (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) v (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bl_max_code (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) v (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bl_count (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) v (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_heap (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) v (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_heap_len (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) v (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_heap_max (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) v (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_depth (s : deflate_state) (v : arr) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) v (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_lit_bufsize (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) v (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_sym_next (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) v (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_sym_end (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) v (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_opt_len (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) v (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_static_len (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) v (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_matches (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) v (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_insert (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) v (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bi_buf (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) v (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_bi_valid (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) v (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_high_water (s : deflate_state) (v : Z) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) v (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_self_blk (s : deflate_state) (v : blk) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) v (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_window_blk (s : deflate_state) (v : option blk) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) v (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_prev_blk (s : deflate_state) (v : option blk) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) v (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).
Definition set_head_blk (s : deflate_state) (v : option blk) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) v (ds_pending_buf_blk s) (ds_strm s).
Definition set_pending_buf_blk (s : deflate_state) (v : option blk) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) v (ds_strm s).
Definition set_strm (s : deflate_state) (v : cstrm) : deflate_state :=
  mkDS (ds_status s) (ds_pending_buf s) (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s) (ds_gzindex s) (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) (ds_window s) (ds_window_size s) (ds_prev s) (ds_head s) (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s) (ds_match_length s) (ds_prev_match s) (ds_match_available s) (ds_strstart s) (ds_match_start s) (ds_lookahead s) (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s) (ds_nice_match s) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (ds_l_max_code s) (ds_d_max_code s) (ds_bl_max_code s) (ds_bl_count s) (ds_heap s) (ds_heap_len s) (ds_heap_max s) (ds_depth s) (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s) (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s) (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) v.

Definition ds_of_oracle (g : Z -> Z) (self : blk) (st : cstrm) : deflate_state :=
  mkDS
    (swrap32 (init_u32 g 8 0)) (arr_make 0 0) (init_u64 g 24 0) 0
    (init_u64 g 40 0) (swrap32 (init_u32 g 48 0)) 0 (init_u64 g 64 0)
    (init_u8 g 72 0) (swrap32 (init_u32 g 76 0)) (init_u32 g 80 0)
    (init_u32 g 84 0) (init_u32 g 88 0) (arr_make 0 0) (init_u64 g 104 0)
    (arr_make 0 0) (arr_make 0 0) (init_u32 g 128 0) (init_u32 g 132 0)
    (init_u32 g 136 0) (init_u32 g 140 0) (init_u32 g 144 0)
    (swrap64 (init_u64 g 152 0)) (init_u32 g 160 0) (init_u32 g 164 0)
    (swrap32 (init_u32 g 168 0)) (init_u32 g 172 0) (init_u32 g 176 0)
    (init_u32 g 180 0) (init_u32 g 184 0) (init_u32 g 188 0)
    (init_u32 g 192 0) (swrap32 (init_u32 g 196 0))
    (swrap32 (init_u32 g 200 0)) (init_u32 g 204 0)
    (swrap32 (init_u32 g 208 0)) (arr_u16_of g 212 4 573)
    (arr_u16_of g 214 4 573) (arr_u16_of g 2504 4 61) (arr_u16_of g 2506 4 61)
    (arr_u16_of g 2748 4 39) (arr_u16_of g 2750 4 39)
    (swrap32 (init_u32 g 2912 0)) (swrap32 (init_u32 g 2936 0))
    (swrap32 (init_u32 g 2960 0)) (arr_u16_of g 2976 2 16)
    (arr_s32_of g 3008 4 573) (swrap32 (init_u32 g 5300 0))
    (swrap32 (init_u32 g 5304 0)) (arr_u8_of g 5308 1 573) (init_u32 g 5896 0)
    (init_u32 g 5900 0) (init_u32 g 5904 0) (init_u64 g 5912 0)
    (init_u64 g 5920 0) (init_u32 g 5928 0) (init_u32 g 5932 0)
    (init_u16 g 5936 0) (swrap32 (init_u32 g 5940 0)) (init_u64 g 5944 0) self
    None None None None st.

Inductive tree_id : Set := TL | TD | TB .

Definition tree_fc (s : deflate_state) (t : tree_id) : arr :=
  match t with TL => ds_dyn_ltree_fc s | TD => ds_dyn_dtree_fc s | TB => ds_bl_tree_fc s end.
Definition tree_dl (s : deflate_state) (t : tree_id) : arr :=
  match t with TL => ds_dyn_ltree_dl s | TD => ds_dyn_dtree_dl s | TB => ds_bl_tree_dl s end.
Definition set_tree_fc (s : deflate_state) (t : tree_id) (a : arr) : deflate_state :=
  match t with TL => set_dyn_ltree_fc s a | TD => set_dyn_dtree_fc s a | TB => set_bl_tree_fc s a end.
Definition set_tree_dl (s : deflate_state) (t : tree_id) (a : arr) : deflate_state :=
  match t with TL => set_dyn_ltree_dl s a | TD => set_dyn_dtree_dl s a | TB => set_bl_tree_dl s a end.

Definition Freq (s : deflate_state) (t : tree_id) (n : Z) : Z := arr_get (tree_fc s t) n.
Definition Code (s : deflate_state) (t : tree_id) (n : Z) : Z := arr_get (tree_fc s t) n.
Definition Dad (s : deflate_state) (t : tree_id) (n : Z) : Z := arr_get (tree_dl s t) n.
Definition Len (s : deflate_state) (t : tree_id) (n : Z) : Z := arr_get (tree_dl s t) n.
Definition set_Freq (s : deflate_state) (t : tree_id) (n v : Z) : deflate_state :=
  set_tree_fc s t (arr_set (tree_fc s t) n (wrap16 v)).
Definition set_Code := set_Freq.
Definition set_Dad (s : deflate_state) (t : tree_id) (n v : Z) : deflate_state :=
  set_tree_dl s t (arr_set (tree_dl s t) n (wrap16 v)).
Definition set_Len := set_Dad.

Definition max_code (s : deflate_state) (t : tree_id) : Z :=
  match t with TL => ds_l_max_code s | TD => ds_d_max_code s | TB => ds_bl_max_code s end.
Definition set_max_code (s : deflate_state) (t : tree_id) (v : Z) : deflate_state :=
  match t with TL => set_l_max_code s v | TD => set_d_max_code s v | TB => set_bl_max_code s v end.

Definition stree_has (t : tree_id) : bool := match t with TB => false | _ => true end.
Definition stree_Len (t : tree_id) (n : Z) : Z :=
  match t with TL => arr_get static_ltree_dl n | TD => arr_get static_dtree_dl n | TB => 0 end.
Definition sd_extra_bits (t : tree_id) : arr :=
  match t with TL => extra_lbits_a | TD => extra_dbits_a | TB => extra_blbits_a end.
Definition sd_extra_base (t : tree_id) : Z := match t with TL => LITERALS + 1 | _ => 0 end.
Definition sd_elems (t : tree_id) : Z := match t with TL => L_CODES | TD => D_CODES | TB => BL_CODES end.
Definition sd_max_length (t : tree_id) : Z := match t with TB => MAX_BL_BITS | _ => MAX_BITS end.

Definition sym_buf_get (s : deflate_state) (i : Z) : Z :=
  arr_get (ds_pending_buf s) (ds_lit_bufsize s + i).
Definition sym_buf_set (s : deflate_state) (i v : Z) : deflate_state :=
  set_pending_buf s (arr_set (ds_pending_buf s) (ds_lit_bufsize s + i) (wrap8 v)).

Definition put_byte (s : deflate_state) (c : Z) : deflate_state :=
  let s := set_pending_buf s (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 c)) in
  set_pending s (ds_pending s + 1).
