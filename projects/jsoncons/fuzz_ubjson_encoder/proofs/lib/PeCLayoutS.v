(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeCLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CADDR_S : pm_addrs := {|
  pa_harness := 0x349e4;
  pa_str_ctor := 0x34c4c;
  pa_iss_ctor := 0x34d04;
  pa_strbuf_ctor := 0x353bc;
  pa_init_buf_ptrs := 0x354a8;
  pa_str_copy := 0x593a0;
  pa_ios_init := 0x5e10c;
  pa_locale_ctor := 0x82be4;
  pa_locale_dtor := 0x82cbc;
  pa_reader_ctor := 0x3808c;   (* [comment removed for export] *)
  pa_src_ctor := 0x381f0;
  pa_nullis_ctor := 0x38284;
  pa_vec_alloc := 0x383e0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0x38390;   (* [comment removed for export] *)
  pa_syscat := 0x5d25c;
  pa_reset := 0x38418;   (* [comment removed for export] *)
  pa_parse := 0x38540;   (* [comment removed for export] *)
  pa_rtv := 0x388c4;   (* [comment removed for export] *)
  pa_read_value := 0x389d0;   (* [comment removed for export] *)
  pa_get_length := 0x39600;   (* [comment removed for export] *)
  pa_read_key := 0x38fec;   (* [comment removed for export] *)
  pa_begin_array := 0x39998;   (* [comment removed for export] *)
  pa_begin_object := 0x39da8;   (* [comment removed for export] *)
  pa_end_array := 0x3895c;   (* [comment removed for export] *)
  pa_end_object := 0x390c4;   (* [comment removed for export] *)
  pa_peek := 0x38ed0;   (* [comment removed for export] *)
  pa_ignore := 0x38f24;   (* [comment removed for export] *)
  pa_src_read := 0x39138;   (* [comment removed for export] *)
  pa_fill_buffer := 0x39310;   (* [comment removed for export] *)
  pa_read_span := 0x3980c;   (* [comment removed for export] *)
  pa_srd_read := 0x3a1cc;   (* [comment removed for export] *)
  pa_validate := 0x393f4;   (* [comment removed for export] *)
  pa_is_base10 := 0x39908;   (* [comment removed for export] *)
  pa_make_ec := 0x36f18;   (* [comment removed for export] *)
  pa_str_resize := 0x59744;
  pa_str_append := 0x590b8;
  pa_xsgetn := 0x5e57c;
  pa_uflow := 0x5e690;
  pa_underflow := 0x5e84c;
  pa_ios_clear := 0x5e034;
  pa_src_dtor := 0x34fbc;
  pa_istream_dtor := 0x5e7c4;
  pa_ios_dtor := 0x5e4d8;
  pa_iosbase_dtor := 0x5df2c;
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0;   (* [comment removed for export] *)
  pa_opnew := 0xb13c4;
  pa_opdel := 0x56c58;
  pa_opdel_sized := 0x56c54;
  pa_memcpy := 0xac48c;
  pa_memmove := 0xac890;
  pa_memset := 0xaca0c;
  pa_guard_acquire := 0x3a34c;
  pa_guard_release := 0x3a39c;
  pa_cxa_atexit := 0x9bc18;
  pa_vp_visitor := 0xb26e0;   (* [comment removed for export] *)
  pa_vp_parser := 0xb2598;   (* [comment removed for export] *)
  pa_vp_iss := 0xb5e70;
  pa_vp_strbuf := 0xb5d80;
  pa_vp_iss_ios := 0xb5e98;
  pa_vp_nullis := 0xb2610;
  pa_vp_nullbuf := 0xb2980;
  pa_vp_nullis_ios := 0xb2638;
  pa_vp_opts := 0xb2518;   (* [comment removed for export] *)
  pa_errcat_guard := 0xc9640;
  pa_errcat_obj := 0xb92f8;
  pa_errcat_dtor := 0x583d0;
  pa_dso := 0xb92d0;
  pa_syscat_guard := 0xc9870;
  pa_syscat_obj := 0xb9330;
  pa_glocale := 0xc9a48;
  pa_classic_imp := 0xc9e80;
  pa_loc_foot := [(0xc9872, 0xc9fb0); (0xca6d8, 0xca730)];
  pa_atexit := 0xeb088;
  pa_need_locks := 0xeb2d3;
  pa_locale_lock := 0xeb3a8;
  pa_canary := 0xeb2b0;
  pa_frame := 832;   (* [comment removed for export] *)
  pa_off_opts := 16;   (* [comment removed for export] *)
  pa_off_ec := 16;   (* [comment removed for export] *)
  pa_off_p := 48;   (* [comment removed for export] *)
  pa_off_v := 440;   (* [comment removed for export] *)
  pa_off_is := 520;   (* [comment removed for export] *)
  pa_off_s := 792;   (* [comment removed for export] *)
  pa_rw_lo := 0xb94a8;
  pa_gp := 0x10800;
  pa_tp := 0xcb040
|}.

Definition EADDR_S : pe_addrs := {|
  pe_vt := 0xb26e0;
  pe_off_begin_obj := 0x40;
  pe_off_begin_obj_len := 0x48;
  pe_off_end_obj := 0x50;
  pe_off_begin_arr := 0x58;
  pe_off_begin_arr_len := 0x10;
  pe_off_end_arr := 0x18;
  pe_off_key := 0x60;
  pe_off_null := 0x68;
  pe_off_bool := 0x70;
  pe_off_string := 0x78;
  pe_off_uint64 := 0x20;
  pe_off_int64 := 0x28;
  pe_off_double := 0x30;
  pe_off_flush := 0x38;
  pe_begin_obj := 0x35c24;
  pe_begin_obj_len := 0x35d9c;
  pe_end_obj := 0x35f30;
  pe_begin_arr := 0x36058;
  pe_begin_arr_len := 0x35628;
  pe_end_arr := 0x357c4;
  pe_key := 0x361d0;
  pe_null := 0x3626c;
  pe_bool := 0x362bc;
  pe_string := 0x36318;
  pe_uint64 := 0x358ec;
  pe_int64 := 0x359f8;
  pe_double := 0x35b74;
  pe_flush := 0x35c20;
  pe_put_length := 0x36fb0;
  pe_push_back := 0x372d8;
  pe_evec_alloc := 0x37294;
  pe_evec_sbdtor := 0x37228;
  pe_validate_enc := 0x37e80;
  pe_off_sink := 496;
  pe_frame := 832;
  pe_drv_call := 0x9bda4;
  pe_drv_guard := 0x3496c
|}.
