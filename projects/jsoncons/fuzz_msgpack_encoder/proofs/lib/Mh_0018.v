(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List.
Module PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record pm_addrs : Type := PA {
  (* [comment removed for export] *)
  pa_harness : Z;          (* [comment removed for export] *)
  pa_str_ctor : Z;         (* [comment removed for export] *)
  pa_iss_ctor : Z;         (* [comment removed for export] *)
  pa_strbuf_ctor : Z;      (* [comment removed for export] *)
  pa_init_buf_ptrs : Z;    (* [comment removed for export] *)
  pa_str_copy : Z;         (* [comment removed for export] *)
  pa_ios_init : Z;         (* [comment removed for export] *)
  pa_locale_ctor : Z;      (* [comment removed for export] *)
  pa_locale_dtor : Z;      (* [comment removed for export] *)
  pa_reader_ctor : Z;      (* [comment removed for export] *)
  pa_src_ctor : Z;         (* [comment removed for export] *)
  pa_nullis_ctor : Z;      (* [comment removed for export] *)
  pa_vec_alloc : Z;        (* [comment removed for export] *)
  pa_splitbuf_dtor : Z;    (* [comment removed for export] *)
  pa_syscat : Z;           (* [comment removed for export] *)
  pa_reset : Z;            (* [comment removed for export] *)
  pa_parse : Z;            (* [comment removed for export] *)
  pa_rtv : Z;              (* [comment removed for export] *)
  pa_read_value : Z;
  pa_get_length : Z;
  pa_read_key : Z;
  pa_begin_array : Z;
  pa_begin_object : Z;
  pa_end_array : Z;
  pa_end_object : Z;
  pa_peek : Z;             (* [comment removed for export] *)
  pa_ignore : Z;           (* [comment removed for export] *)
  pa_src_read : Z;         (* [comment removed for export] *)
  pa_fill_buffer : Z;      (* [comment removed for export] *)
  pa_read_span : Z;        (* [comment removed for export] *)
  pa_srd_read : Z;         (* [comment removed for export] *)
  pa_validate : Z;         (* [comment removed for export] *)
  pa_is_base10 : Z;
  pa_make_ec : Z;          (* [comment removed for export] *)
  pa_str_resize : Z;       (* [comment removed for export] *)
  pa_str_append : Z;       (* [comment removed for export] *)
  pa_xsgetn : Z;           (* [comment removed for export] *)
  pa_uflow : Z;            (* [comment removed for export] *)
  pa_underflow : Z;        (* [comment removed for export] *)
  pa_ios_clear : Z;        (* [comment removed for export] *)
  pa_src_dtor : Z;         (* [comment removed for export] *)
  pa_istream_dtor : Z;     (* [comment removed for export] *)
  pa_ios_dtor : Z;         (* [comment removed for export] *)
  pa_iosbase_dtor : Z;     (* [comment removed for export] *)
  pa_reader_read : Z;      (* [comment removed for export] *)
  pa_vec_dtor : Z;         (* [comment removed for export] *)
  pa_opnew : Z;            (* [comment removed for export] *)
  pa_opdel : Z;            (* [comment removed for export] *)
  pa_opdel_sized : Z;      (* [comment removed for export] *)
  pa_memcpy : Z; pa_memmove : Z; pa_memset : Z;
  pa_guard_acquire : Z; pa_guard_release : Z;   (* [comment removed for export] *)
  pa_cxa_atexit : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_vp_visitor : Z;       (* [comment removed for export] *)
  pa_vp_parser : Z;        (* [comment removed for export] *)
  pa_vp_iss : Z;           (* [comment removed for export] *)
  pa_vp_strbuf : Z;        (* [comment removed for export] *)
  pa_vp_iss_ios : Z;       (* [comment removed for export] *)
  pa_vp_nullis : Z;        (* [comment removed for export] *)
  pa_vp_nullbuf : Z;       (* [comment removed for export] *)
  pa_vp_nullis_ios : Z;    (* [comment removed for export] *)
  pa_vp_opts : Z;          (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_errcat_guard : Z;     (* [comment removed for export] *)
  pa_errcat_obj : Z;       (* [comment removed for export] *)
  pa_errcat_dtor : Z;      (* [comment removed for export] *)
  pa_dso : Z;              (* [comment removed for export] *)
  pa_syscat_guard : Z;     (* [comment removed for export] *)
  pa_syscat_obj : Z;       (* [comment removed for export] *)
  pa_glocale : Z;          (* [comment removed for export] *)
  pa_classic_imp : Z;      (* [comment removed for export] *)
  pa_loc_foot : list (Z * Z);  (* [comment removed for export] *)
  pa_atexit : Z;           (* [comment removed for export] *)
  pa_need_locks : Z;       (* [comment removed for export] *)
  pa_locale_lock : Z;      (* [comment removed for export] *)
  pa_canary : Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_frame : Z;            (* [comment removed for export] *)
  pa_off_opts : Z;         (* [comment removed for export] *)
  pa_off_ec : Z;           (* [comment removed for export] *)
  pa_off_p : Z;            (* [comment removed for export] *)
  pa_off_v : Z;            (* [comment removed for export] *)
  pa_off_is : Z;           (* [comment removed for export] *)
  pa_off_s : Z;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_rw_lo : Z;            (* [comment removed for export] *)
  pa_gp : Z;
  pa_tp : Z
}.

(* [comment removed for export] *)
Definition pm_foot (A : pm_addrs) : list (Z * Z) :=
  [(pa_errcat_guard A, pa_errcat_guard A + 2); (pa_syscat_guard A, pa_syscat_guard A + 2)]
  ++ pa_loc_foot A ++ [(pa_atexit A, pa_atexit A + 544)].
(* [comment removed for export] *)
Definition pm_initc (A : pm_addrs) : list (Z * Z) :=
  [(pa_need_locks A, pa_need_locks A + 1); (pa_locale_lock A, pa_locale_lock A + 4)].

End PmLayout.
Module PnLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNL.
Record pn_addrs : Type := PNA {
  pn_reader_ctor : Z;   (* [comment removed for export] *)
  pn_reader_dtor : Z;   (* [comment removed for export] *)
  pn_reader_read : Z;   (* [comment removed for export] *)
  pn_reset : Z;   (* [comment removed for export] *)
  pn_parse : Z;   (* [comment removed for export] *)
  pn_begin_document : Z;
  pn_end_document : Z;
  pn_begin_array : Z;
  pn_end_array : Z;
  pn_read_e_name : Z;
  pn_read_cstring : Z;   (* [comment removed for export] *)
  pn_read_string : Z;
  pn_read_value : Z;   (* [comment removed for export] *)
  pn_read_span_v : Z;   (* [comment removed for export] *)
  pn_srd_read_v : Z;   (* [comment removed for export] *)
  pn_vu8_resize : Z;
  pn_vu8_append : Z;   (* [comment removed for export] *)
  pn_vu8_dtor : Z;   (* [comment removed for export] *)
  pn_vu8_recommend : Z;   (* [comment removed for export] *)
  pn_sbu8_ctor : Z;   (* [comment removed for export] *)
  pn_sbu8_construct : Z;   (* [comment removed for export] *)
  pn_vu8_swap_out : Z;   (* [comment removed for export] *)
  pn_sbu8_dtor : Z;   (* [comment removed for export] *)
  pn_vec_alloc : Z;   (* [comment removed for export] *)
  pn_splitbuf_dtor : Z;
  pn_vec_dtor : Z;   (* [comment removed for export] *)
  pn_esp_mii : Z;   (* [comment removed for export] *)
  pn_esp_mis : Z;   (* [comment removed for export] *)
  pn_sb_ctor : Z;   (* [comment removed for export] *)
  pn_swap_out : Z;   (* [comment removed for export] *)
  pn_dec128 : Z;
  pn_from_int : Z;
  pn_hex_pairs : Z;   (* [comment removed for export] *)
  pn_str_push_back : Z;   (* [comment removed for export] *)
  pn_str_cstr : Z;   (* [comment removed for export] *)
  pn_str_dtor : Z;   (* [comment removed for export] *)
  pn_strlen : Z;   (* [comment removed for export] *)
  pn_vbs_tag : Z;   (* [comment removed for export] *)
  pn_vbs_ext : Z;
  pn_strlen_icpt : Z;   (* [comment removed for export] *)
  pn_wrap_strlen : Z;   (* [comment removed for export] *)
  pn_wrap_cxa_atexit : Z;   (* [comment removed for export] *)
  pn_inf_guard : Z;   (* [comment removed for export] *)
  pn_inf_obj : Z;   (* [comment removed for export] *)
  pn_inf_lit : Z;   (* [comment removed for export] *)
  pn_nan_guard : Z;   (* [comment removed for export] *)
  pn_nan_obj : Z;
  pn_nan_lit : Z;
  pn_str_dtor_slot : Z;   (* [comment removed for export] *)
  pn_drv_call : Z;   (* [comment removed for export] *)
  pn_drv_guard : Z   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition pn_d128_foot (N : pn_addrs) : list (Z * Z) :=
  [(pn_inf_guard N, pn_inf_guard N + 8); (pn_inf_obj N, pn_inf_obj N + 24); (pn_nan_guard N, pn_nan_guard N + 8); (pn_nan_obj N, pn_nan_obj N + 24)].
End PNL.

End PnLayout.
Module PnLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ADDR_S : pm_addrs := {|
  pa_harness := 0x390cc;   (* [comment removed for export] *)
  pa_str_ctor := 0x392e8;   (* [comment removed for export] *)
  pa_iss_ctor := 0x393a0;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0x3fabc;   (* [comment removed for export] *)
  pa_init_buf_ptrs := 0x3fba8;   (* [comment removed for export] *)
  pa_str_copy := 0x66878;   (* [comment removed for export] *)
  pa_ios_init := 0x6b5e4;   (* [comment removed for export] *)
  pa_locale_ctor := 0x900bc;   (* [comment removed for export] *)
  pa_locale_dtor := 0x90194;   (* [comment removed for export] *)
  pa_reader_ctor := 0x394b0;   (* [comment removed for export] *)
  pa_src_ctor := 0x45198;   (* [comment removed for export] *)
  pa_nullis_ctor := 0x4522c;   (* [comment removed for export] *)
  pa_vec_alloc := 0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0;   (* [comment removed for export] *)
  pa_syscat := 0x6a734;   (* [comment removed for export] *)
  pa_reset := 0;   (* [comment removed for export] *)
  pa_parse := 0;   (* [comment removed for export] *)
  pa_rtv := 0;   (* [comment removed for export] *)
  pa_read_value := 0;   (* [comment removed for export] *)
  pa_get_length := 0;   (* [comment removed for export] *)
  pa_read_key := 0;   (* [comment removed for export] *)
  pa_begin_array := 0;   (* [comment removed for export] *)
  pa_begin_object := 0;   (* [comment removed for export] *)
  pa_end_array := 0;   (* [comment removed for export] *)
  pa_end_object := 0;   (* [comment removed for export] *)
  pa_peek := 0;   (* [comment removed for export] *)
  pa_ignore := 0;   (* [comment removed for export] *)
  pa_src_read := 0x4629c;   (* [comment removed for export] *)
  pa_fill_buffer := 0x47114;   (* [comment removed for export] *)
  pa_read_span := 0;   (* [comment removed for export] *)
  pa_srd_read := 0;   (* [comment removed for export] *)
  pa_validate := 0x468cc;   (* [comment removed for export] *)
  pa_is_base10 := 0;   (* [comment removed for export] *)
  pa_make_ec := 0x41a54;   (* [comment removed for export] *)
  pa_str_resize := 0x66c1c;   (* [comment removed for export] *)
  pa_str_append := 0x66590;   (* [comment removed for export] *)
  pa_xsgetn := 0x6ba54;   (* [comment removed for export] *)
  pa_uflow := 0x6bb68;   (* [comment removed for export] *)
  pa_underflow := 0x6bd24;   (* [comment removed for export] *)
  pa_ios_clear := 0x6b50c;   (* [comment removed for export] *)
  pa_src_dtor := 0x3f784;   (* [comment removed for export] *)
  pa_istream_dtor := 0x6bc9c;   (* [comment removed for export] *)
  pa_ios_dtor := 0x6b9b0;   (* [comment removed for export] *)
  pa_iosbase_dtor := 0x6b404;   (* [comment removed for export] *)
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0;   (* [comment removed for export] *)
  pa_opnew := 0xbe8b0;   (* [comment removed for export] *)
  pa_opdel := 0x63dc4;   (* [comment removed for export] *)
  pa_opdel_sized := 0x63dc0;   (* [comment removed for export] *)
  pa_memcpy := 0xb9978;   (* [comment removed for export] *)
  pa_memmove := 0xb9d7c;   (* [comment removed for export] *)
  pa_memset := 0xb9ef8;   (* [comment removed for export] *)
  pa_guard_acquire := 0x474a4;   (* [comment removed for export] *)
  pa_guard_release := 0x474f4;   (* [comment removed for export] *)
  pa_cxa_atexit := 0xa90f0;   (* [comment removed for export] *)
  pa_vp_visitor := 0xc0108;   (* [comment removed for export] *)
  pa_vp_parser := 0xbfce8;   (* [comment removed for export] *)
  pa_vp_iss := 0xc3688;   (* [comment removed for export] *)
  pa_vp_strbuf := 0xc3598;   (* [comment removed for export] *)
  pa_vp_iss_ios := 0xc36b0;   (* [comment removed for export] *)
  pa_vp_nullis := 0xbfd60;   (* [comment removed for export] *)
  pa_vp_nullbuf := 0xc0070;   (* [comment removed for export] *)
  pa_vp_nullis_ios := 0xbfd88;   (* [comment removed for export] *)
  pa_vp_opts := 0xbfa08;   (* [comment removed for export] *)
  pa_errcat_guard := 0xd6e50;   (* [comment removed for export] *)
  pa_errcat_obj := 0xc6b10;   (* [comment removed for export] *)
  pa_errcat_dtor := 0x6553c;   (* [comment removed for export] *)
  pa_dso := 0xc6ae8;   (* [comment removed for export] *)
  pa_syscat_guard := 0xd7080;   (* [comment removed for export] *)
  pa_syscat_obj := 0xc6b48;   (* [comment removed for export] *)
  pa_glocale := 0xd7258;   (* [comment removed for export] *)
  pa_classic_imp := 0xd7690;   (* [comment removed for export] *)
  pa_loc_foot := [(0xd7082, 0xd77c0); (0xd7ee8, 0xd7f40)];   (* [comment removed for export] *)
  pa_atexit := 0xf8898;   (* [comment removed for export] *)
  pa_need_locks := 0xf8ae3;   (* [comment removed for export] *)
  pa_locale_lock := 0xf8bb8;   (* [comment removed for export] *)
  pa_canary := 0xf8ac0;   (* [comment removed for export] *)
  pa_frame := 928;   (* [comment removed for export] *)
  pa_off_opts := 8;   (* [comment removed for export] *)
  pa_off_ec := 8;   (* [comment removed for export] *)
  pa_off_p := 32;   (* [comment removed for export] *)
  pa_off_v := 536;   (* [comment removed for export] *)
  pa_off_is := 616;   (* [comment removed for export] *)
  pa_off_s := 888;   (* [comment removed for export] *)
  pa_rw_lo := 0xc6cc0;   (* [comment removed for export] *)
  pa_gp := 0x10800;   (* [comment removed for export] *)
  pa_tp := 0xd8850   (* [comment removed for export] *)
|}.

(* [comment removed for export] *)
Definition NADDR_S : PNL.pn_addrs := {|
  PNL.pn_reader_ctor := 0;   (* [comment removed for export] *)
  PNL.pn_reader_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_reader_read := 0;   (* [comment removed for export] *)
  PNL.pn_reset := 0;   (* [comment removed for export] *)
  PNL.pn_parse := 0;   (* [comment removed for export] *)
  PNL.pn_begin_document := 0;   (* [comment removed for export] *)
  PNL.pn_end_document := 0;   (* [comment removed for export] *)
  PNL.pn_begin_array := 0;   (* [comment removed for export] *)
  PNL.pn_end_array := 0;   (* [comment removed for export] *)
  PNL.pn_read_e_name := 0;   (* [comment removed for export] *)
  PNL.pn_read_cstring := 0;   (* [comment removed for export] *)
  PNL.pn_read_string := 0;   (* [comment removed for export] *)
  PNL.pn_read_value := 0;   (* [comment removed for export] *)
  PNL.pn_read_span_v := 0x46804;   (* [comment removed for export] *)
  PNL.pn_srd_read_v := 0x471f8;   (* [comment removed for export] *)
  PNL.pn_vu8_resize := 0x47338;   (* [comment removed for export] *)
  PNL.pn_vu8_append := 0x47360;   (* [comment removed for export] *)
  PNL.pn_vu8_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_vu8_recommend := 0;   (* [comment removed for export] *)
  PNL.pn_sbu8_ctor := 0;   (* [comment removed for export] *)
  PNL.pn_sbu8_construct := 0;   (* [comment removed for export] *)
  PNL.pn_vu8_swap_out := 0;   (* [comment removed for export] *)
  PNL.pn_sbu8_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_vec_alloc := 0;   (* [comment removed for export] *)
  PNL.pn_splitbuf_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_vec_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_esp_mii := 0;   (* [comment removed for export] *)
  PNL.pn_esp_mis := 0;   (* [comment removed for export] *)
  PNL.pn_sb_ctor := 0;   (* [comment removed for export] *)
  PNL.pn_swap_out := 0;   (* [comment removed for export] *)
  PNL.pn_dec128 := 0;   (* [comment removed for export] *)
  PNL.pn_from_int := 0;   (* [comment removed for export] *)
  PNL.pn_hex_pairs := 0;   (* [comment removed for export] *)
  PNL.pn_str_push_back := 0x66444;   (* [comment removed for export] *)
  PNL.pn_str_cstr := 0x3ca90;   (* [comment removed for export] *)
  PNL.pn_str_dtor := 0x65ad4;   (* [comment removed for export] *)
  PNL.pn_strlen := 0xba3dc;   (* [comment removed for export] *)
  PNL.pn_vbs_tag := 0x45450;   (* [comment removed for export] *)
  PNL.pn_vbs_ext := 0x41a2c;   (* [comment removed for export] *)
  PNL.pn_strlen_icpt := 0;   (* [comment removed for export] *)
  PNL.pn_wrap_strlen := 0;   (* [comment removed for export] *)
  PNL.pn_wrap_cxa_atexit := 0;   (* [comment removed for export] *)
  PNL.pn_inf_guard := 0;   (* [comment removed for export] *)
  PNL.pn_inf_obj := 0;   (* [comment removed for export] *)
  PNL.pn_inf_lit := 0;   (* [comment removed for export] *)
  PNL.pn_nan_guard := 0;   (* [comment removed for export] *)
  PNL.pn_nan_obj := 0;   (* [comment removed for export] *)
  PNL.pn_nan_lit := 0;   (* [comment removed for export] *)
  PNL.pn_str_dtor_slot := 0xc5a80;   (* [comment removed for export] *)
  PNL.pn_drv_call := 0xa927c;   (* [comment removed for export] *)
  PNL.pn_drv_guard := 0x39054   (* [comment removed for export] *)
|}.

End PnLayoutS.
Module NemLayout.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Record ne_addrs : Type := NEA {
  (* [comment removed for export] *)
  ne_vt : Z;                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  ne_off_begin_arr_len : Z;  (* [comment removed for export] *)
  ne_off_end_arr : Z;        (* [comment removed for export] *)
  ne_off_uint64 : Z;         (* [comment removed for export] *)
  ne_off_int64 : Z;          (* [comment removed for export] *)
  ne_off_double : Z;         (* [comment removed for export] *)
  ne_off_flush : Z;          (* [comment removed for export] *)
  ne_off_begin_obj_len : Z;  (* [comment removed for export] *)
  ne_off_end_obj : Z;        (* [comment removed for export] *)
  ne_off_key : Z;            (* [comment removed for export] *)
  ne_off_null : Z;           (* [comment removed for export] *)
  ne_off_bool : Z;           (* [comment removed for export] *)
  ne_off_string : Z;         (* [comment removed for export] *)
  ne_off_bstr_tag : Z;       (* [comment removed for export] *)
  ne_off_bstr_raw : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  ne_begin_arr_len : Z;      (* [comment removed for export] *)
  ne_end_arr : Z;            (* [comment removed for export] *)
  ne_uint64 : Z;             (* [comment removed for export] *)
  ne_int64 : Z;              (* [comment removed for export] *)
  ne_double : Z;             (* [comment removed for export] *)
  ne_flush : Z;              (* [comment removed for export] *)
  ne_begin_obj_len : Z;      (* [comment removed for export] *)
  ne_end_obj : Z;            (* [comment removed for export] *)
  ne_key : Z;                (* [comment removed for export] *)
  ne_null : Z;               (* [comment removed for export] *)
  ne_bool : Z;               (* [comment removed for export] *)
  ne_string : Z;             (* [comment removed for export] *)
  ne_bstr_tag : Z;           (* [comment removed for export] *)
  ne_bstr_raw : Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  ne_push_back : Z;          (* [comment removed for export] *)
  ne_evec_alloc : Z;         (* [comment removed for export] *)
  ne_evec_sbdtor : Z;        (* [comment removed for export] *)
  ne_ntb_u16 : Z; ne_ntb_u32 : Z; ne_ntb_u64 : Z;        (* [comment removed for export] *)
  ne_ntb_i8 : Z; ne_ntb_i16 : Z; ne_ntb_i32 : Z; ne_ntb_i64 : Z;   (* [comment removed for export] *)
  ne_ntb_f32 : Z; ne_ntb_f64 : Z;                      (* [comment removed for export] *)
  ne_write_timestamp : Z;    (* [comment removed for export] *)
  ne_write_string_value : Z; (* [comment removed for export] *)
  ne_validate_enc : Z;       (* [comment removed for export] *)
  ne_to_bigint : Z; ne_to_bigint_d : Z; ne_to_bigint_h : Z;   (* [comment removed for export] *)
  ne_ts_helper : Z;          (* [comment removed for export] *)
  ne_divide : Z;             (* [comment removed for export] *)
  ne_make_ec : Z;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  ne_off_sink : Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  ne_spare : Z
}.

End NemLayout.
From Stdlib Require ZArith.
Module NemLayoutS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition NEADDR_S : ne_addrs := {|
  ne_vt                 := 0xbfe30;   (* [comment removed for export] *)
  ne_off_begin_arr_len  := 0x10;   (* [comment removed for export] *)
  ne_off_end_arr        := 0x18;
  ne_off_uint64         := 0x20;
  ne_off_int64          := 0x28;
  ne_off_double         := 0x30;
  ne_off_flush          := 0x38;
  ne_off_begin_obj_len  := 0x48;
  ne_off_end_obj        := 0x50;
  ne_off_key            := 0x60;
  ne_off_null           := 0x68;
  ne_off_bool           := 0x70;
  ne_off_string         := 0x78;
  ne_off_bstr_tag       := 0x80;
  ne_off_bstr_raw       := 0x88;
  ne_begin_arr_len      := 0x3fd28;   (* [comment removed for export] *)
  ne_end_arr            := 0x3ff0c;
  ne_uint64             := 0x40010;
  ne_int64              := 0x401c0;
  ne_double             := 0x40438;
  ne_flush              := 0x404e4;
  ne_begin_obj_len      := 0x4050c;
  ne_end_obj            := 0x406e8;
  ne_key                := 0x40810;
  ne_null               := 0x40838;
  ne_bool               := 0x40888;
  ne_string             := 0x408d8;
  ne_bstr_tag           := 0x40cfc;
  ne_bstr_raw           := 0x40e10;
  ne_push_back          := 0x41d04;   (* [comment removed for export] *)
  ne_evec_alloc         := 0x41cc0;   (* [comment removed for export] *)
  ne_evec_sbdtor        := 0x41c54;   (* [comment removed for export] *)
  ne_ntb_u16            := 0x41aec;
  ne_ntb_u32            := 0x41b50;
  ne_ntb_u64            := 0x41f34;
  ne_ntb_i8             := 0;   (* [comment removed for export] *)
  ne_ntb_i16            := 0x41ff0;   (* [comment removed for export] *)
  ne_ntb_i32            := 0x42058;   (* [comment removed for export] *)
  ne_ntb_i64            := 0x420dc;   (* [comment removed for export] *)
  ne_ntb_f32            := 0x42198;   (* [comment removed for export] *)
  ne_ntb_f64            := 0x42220;   (* [comment removed for export] *)
  ne_write_timestamp    := 0x41e18;   (* [comment removed for export] *)
  ne_write_string_value := 0x42b3c;
  ne_validate_enc       := 0x4472c;   (* [comment removed for export] *)
  ne_to_bigint          := 0x42384;
  ne_to_bigint_d        := 0x42f30;
  ne_to_bigint_h        := 0x43114;
  ne_ts_helper          := 0x423dc;
  ne_divide             := 0x42450;   (* [comment removed for export] *)
  ne_make_ec            := 0x41a54;   (* [comment removed for export] *)
  ne_off_sink           := 592;   (* [comment removed for export] *)
  ne_spare              := 0
|}.

End NemLayoutS.
Module PnLayoutQ.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record pq_addrs : Type := PQA {
  (* [comment removed for export] *)
  qa_vp_adaptor : Z;       (* [comment removed for export] *)
  qa_off_a : Z;            (* [comment removed for export] *)
  qa_off_vref : Z;         (* [comment removed for export] *)
  (* [comment removed for export] *)
  qa_parser_ctor : Z; qa_adaptor_ctor : Z; qa_reader_dtor : Z;
  qa_reset : Z; qa_parse : Z; qa_read_item : Z; qa_begin_array : Z; qa_begin_object : Z; qa_get_size : Z;
  qa_ps_alloc : Z;         (* [comment removed for export] *)
  qa_ps_sbdtor : Z;        (* [comment removed for export] *)
  (* [comment removed for export] *)
  qa_read_span_v : Z; qa_srd_read_v : Z; qa_vu8_resize : Z; qa_vu8_append : Z;
  (* [comment removed for export] *)
  qa_v_begin_array : Z;    (* [comment removed for export] *)
  qa_v_end_array : Z;      (* [comment removed for export] *)
  qa_v_uint64 : Z;         (* [comment removed for export] *)
  qa_v_int64 : Z;          (* [comment removed for export] *)
  qa_v_double : Z;         (* [comment removed for export] *)
  qa_v_flush : Z;          (* [comment removed for export] *)
  qa_v_begin_object : Z;   (* [comment removed for export] *)
  qa_v_end_object : Z;     (* [comment removed for export] *)
  qa_v_null : Z;           (* [comment removed for export] *)
  qa_v_bool : Z;           (* [comment removed for export] *)
  qa_v_string : Z;         (* [comment removed for export] *)
  qa_v_bstr_tag : Z;       (* [comment removed for export] *)
  qa_v_bstr_raw : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  qa_js_alloc : Z;         (* [comment removed for export] *)
  qa_js_sbdtor : Z;        (* [comment removed for export] *)
  qa_from_u64 : Z; qa_from_i64 : Z;     (* [comment removed for export] *)
  qa_str_insert : Z;       (* [comment removed for export] *)
  qa_str_append : Z;       (* [comment removed for export] *)
  qa_b64url : Z; qa_b64disp : Z;        (* [comment removed for export] *)
  qa_push_back : Z;        (* [comment removed for export] *)
  qa_write_double : Z;     (* [comment removed for export] *)
  qa_localeconv : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  qa_ts_list : list Z;     (* [comment removed for export] *)
  (* [comment removed for export] *)
  qa_drv_call : Z;         (* [comment removed for export] *)
  qa_drv_guard : Z         (* [comment removed for export] *)
}.

End PnLayoutQ.
Module PnLayoutQS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QADDR_S : pq_addrs := {|
  qa_vp_adaptor := 0xbfa88; qa_off_a := 400; qa_off_vref := 496;
  qa_parser_ctor := 0x44ed4; qa_adaptor_ctor := 0x4504c; qa_reader_dtor := 0x3952c;
  qa_reset := 0x45460; qa_parse := 0x455a0; qa_read_item := 0x457a8; qa_begin_array := 0x4663c; qa_begin_object := 0x46474;
  qa_get_size := 0x46ad8; qa_ps_alloc := 0x453a4; qa_ps_sbdtor := 0x45338;
  qa_read_span_v := 0x46804; qa_srd_read_v := 0x471f8; qa_vu8_resize := 0x47338; qa_vu8_append := 0x47360;
  qa_v_begin_array := 0x39868; qa_v_end_array := 0x39c7c; qa_v_uint64 := 0x39ef8; qa_v_int64 := 0x3a15c; qa_v_double := 0x3a3c0;
  qa_v_flush := 0x3a658; qa_v_begin_object := 0x3a990; qa_v_end_object := 0x3ada4; qa_v_null := 0x3b424; qa_v_bool := 0x3b694;
  qa_v_string := 0x3b934; qa_v_bstr_tag := 0x3bae0; qa_v_bstr_raw := 0x3bdb4;
  qa_js_alloc := 0x3ca18; qa_js_sbdtor := 0x3c924; qa_from_u64 := 0x3cbc8; qa_from_i64 := 0x3d128;
  qa_str_insert := 0x3ccec; qa_str_append := 0x3e908; qa_b64url := 0x3ecac; qa_b64disp := 0x3ec10;
  qa_push_back := 0x66444; qa_write_double := 0x3d2cc; qa_localeconv := 0xa9eb8;
  qa_ts_list := [0x4446c; 0x43208; 0x46c40; 0x46f08; 0x43888; 0x46f7c];
  qa_drv_call := 0xa927c; qa_drv_guard := 0x39054
|}.

End PnLayoutQS.
