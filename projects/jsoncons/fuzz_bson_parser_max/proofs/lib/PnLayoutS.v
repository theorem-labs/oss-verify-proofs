(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PnLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ADDR_S : pm_addrs := {|
  pa_harness := 0x343f4;   (* [comment removed for export] *)
  pa_str_ctor := 0x34600;   (* [comment removed for export] *)
  pa_iss_ctor := 0x346b8;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0x3583c;   (* [comment removed for export] *)
  pa_init_buf_ptrs := 0x35928;   (* [comment removed for export] *)
  pa_str_copy := 0x57784;   (* [comment removed for export] *)
  pa_ios_init := 0x5bb1c;   (* [comment removed for export] *)
  pa_locale_ctor := 0x805f4;   (* [comment removed for export] *)
  pa_locale_dtor := 0x806cc;   (* [comment removed for export] *)
  pa_reader_ctor := 0;   (* [comment removed for export] *)
  pa_src_ctor := 0x35bfc;   (* [comment removed for export] *)
  pa_nullis_ctor := 0x35c90;   (* [comment removed for export] *)
  pa_vec_alloc := 0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0;   (* [comment removed for export] *)
  pa_syscat := 0x5ac98;   (* [comment removed for export] *)
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
  pa_src_read := 0x364b4;   (* [comment removed for export] *)
  pa_fill_buffer := 0x37338;   (* [comment removed for export] *)
  pa_read_span := 0x38118;   (* [comment removed for export] *)
  pa_srd_read := 0x38214;   (* [comment removed for export] *)
  pa_validate := 0x374c4;   (* [comment removed for export] *)
  pa_is_base10 := 0;   (* [comment removed for export] *)
  pa_make_ec := 0x36248;   (* [comment removed for export] *)
  pa_str_resize := 0x57a18;   (* [comment removed for export] *)
  pa_str_append := 0x5749c;   (* [comment removed for export] *)
  pa_xsgetn := 0x5bf8c;   (* [comment removed for export] *)
  pa_uflow := 0x5c0a0;   (* [comment removed for export] *)
  pa_underflow := 0x5c25c;   (* [comment removed for export] *)
  pa_ios_clear := 0x5ba44;   (* [comment removed for export] *)
  pa_src_dtor := 0x35408;   (* [comment removed for export] *)
  pa_istream_dtor := 0x5c1d4;   (* [comment removed for export] *)
  pa_ios_dtor := 0x5bee8;   (* [comment removed for export] *)
  pa_iosbase_dtor := 0x5b93c;   (* [comment removed for export] *)
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0;   (* [comment removed for export] *)
  pa_opnew := 0xaedd0;   (* [comment removed for export] *)
  pa_opdel := 0x55138;   (* [comment removed for export] *)
  pa_opdel_sized := 0x55134;   (* [comment removed for export] *)
  pa_memcpy := 0xa9e98;   (* [comment removed for export] *)
  pa_memmove := 0xaa29c;   (* [comment removed for export] *)
  pa_memset := 0xaa418;   (* [comment removed for export] *)
  pa_guard_acquire := 0x3882c;   (* [comment removed for export] *)
  pa_guard_release := 0x3887c;   (* [comment removed for export] *)
  pa_cxa_atexit := 0x99628;   (* [comment removed for export] *)
  pa_vp_visitor := 0xaff20;   (* [comment removed for export] *)
  pa_vp_parser := 0xb00f8;   (* [comment removed for export] *)
  pa_vp_iss := 0xb37d0;   (* [comment removed for export] *)
  pa_vp_strbuf := 0xb36e0;   (* [comment removed for export] *)
  pa_vp_iss_ios := 0xb37f8;   (* [comment removed for export] *)
  pa_vp_nullis := 0xb0170;   (* [comment removed for export] *)
  pa_vp_nullbuf := 0xb0240;   (* [comment removed for export] *)
  pa_vp_nullis_ios := 0xb0198;   (* [comment removed for export] *)
  pa_vp_opts := 0xb0078;   (* [comment removed for export] *)
  pa_errcat_guard := 0xc6fa0;   (* [comment removed for export] *)
  pa_errcat_obj := 0xb6c58;   (* [comment removed for export] *)
  pa_errcat_dtor := 0x568b0;   (* [comment removed for export] *)
  pa_dso := 0xb6c30;   (* [comment removed for export] *)
  pa_syscat_guard := 0xc7210;   (* [comment removed for export] *)
  pa_syscat_obj := 0xb6c90;   (* [comment removed for export] *)
  pa_glocale := 0xc73e8;   (* [comment removed for export] *)
  pa_classic_imp := 0xc7820;   (* [comment removed for export] *)
  pa_loc_foot := [(0xc7212, 0xc7950); (0xc8078, 0xc80d0)];   (* [comment removed for export] *)
  pa_atexit := 0xe8a28;   (* [comment removed for export] *)
  pa_need_locks := 0xe8c73;   (* [comment removed for export] *)
  pa_locale_lock := 0xe8d48;   (* [comment removed for export] *)
  pa_canary := 0xe8c50;   (* [comment removed for export] *)
  pa_frame := 784;   (* [comment removed for export] *)
  pa_off_opts := 16;   (* [comment removed for export] *)
  pa_off_ec := 16;   (* [comment removed for export] *)
  pa_off_p := 40;   (* [comment removed for export] *)
  pa_off_v := 464;   (* [comment removed for export] *)
  pa_off_is := 472;   (* [comment removed for export] *)
  pa_off_s := 744;   (* [comment removed for export] *)
  pa_rw_lo := 0xb6e08;   (* [comment removed for export] *)
  pa_gp := 0x10800;   (* [comment removed for export] *)
  pa_tp := 0xc89e0   (* [comment removed for export] *)
|}.

Definition NADDR_S : PNL.pn_addrs := {|
  PNL.pn_reader_ctor := 0x35a68;
  PNL.pn_reader_dtor := 0x347cc;
  PNL.pn_reader_read := 0;
  PNL.pn_reset := 0x35e4c;
  PNL.pn_parse := 0x35fb4;
  PNL.pn_begin_document := 0x362e0;
  PNL.pn_end_document := 0x367a4;
  PNL.pn_begin_array := 0x377bc;
  PNL.pn_end_array := 0x3707c;
  PNL.pn_read_e_name := 0x3668c;
  PNL.pn_read_cstring := 0x3741c;
  PNL.pn_read_string := 0x376d0;
  PNL.pn_read_value := 0x368ec;
  PNL.pn_read_span_v := 0x37998;
  PNL.pn_srd_read_v := 0x38394;
  PNL.pn_vu8_resize := 0x384d4;
  PNL.pn_vu8_append := 0x384fc;
  PNL.pn_vu8_dtor := 0;
  PNL.pn_vu8_recommend := 0;
  PNL.pn_sbu8_ctor := 0;
  PNL.pn_sbu8_construct := 0;
  PNL.pn_vu8_swap_out := 0;
  PNL.pn_sbu8_dtor := 0;
  PNL.pn_vec_alloc := 0x35e0c;
  PNL.pn_splitbuf_dtor := 0x35d9c;
  PNL.pn_vec_dtor := 0;
  PNL.pn_esp_mii := 0;
  PNL.pn_esp_mis := 0;
  PNL.pn_sb_ctor := 0;
  PNL.pn_swap_out := 0;
  PNL.pn_dec128 := 0x37a60;
  PNL.pn_from_int := 0x38654;
  PNL.pn_hex_pairs := 0;
  PNL.pn_str_push_back := 0x57350;
  PNL.pn_str_cstr := 0x371c4;
  PNL.pn_str_dtor := 0x56e48;
  PNL.pn_strlen := 0xaa8fc;
  PNL.pn_vbs_tag := 0x349c8;
  PNL.pn_vbs_ext := 0x349d0;
  PNL.pn_strlen_icpt := 0;
  PNL.pn_wrap_strlen := 0;
  PNL.pn_wrap_cxa_atexit := 0;
  PNL.pn_inf_guard := 0xc6fc0;
  PNL.pn_inf_obj := 0xc6fa8;
  PNL.pn_inf_lit := 0x131ef;
  PNL.pn_nan_guard := 0xc6fe0;
  PNL.pn_nan_obj := 0xc6fc8;
  PNL.pn_nan_lit := 0x11f67;
  PNL.pn_str_dtor_slot := 0xb5b20;
  PNL.pn_drv_call := 0x997b4;   (* [comment removed for export] *)
  PNL.pn_drv_guard := 0x3437c   (* [comment removed for export] *)
|}.

