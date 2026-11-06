(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA PeCLayout.
Import ListNotations.
Open Scope Z_scope.

Definition CADDR_A : pm_addrs := {|
  pa_harness := 0xa8928;
  pa_str_ctor := 0xa9484;   (* [comment removed for export] *)
  pa_iss_ctor := 0xa95dc;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0xaa830;
  pa_init_buf_ptrs := 0xaa9e8;
  pa_str_copy := 0xd71a8;
  pa_ios_init := 0xdbf14;
  pa_locale_ctor := 0x1009ec;
  pa_locale_dtor := 0x100ac4;
  pa_reader_ctor := 0xb153c;   (* [comment removed for export] *)
  pa_src_ctor := 0xb1808;   (* [comment removed for export] *)
  pa_nullis_ctor := 0xb1cf8;
  pa_vec_alloc := 0xb223c;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0xb2150;   (* [comment removed for export] *)
  pa_syscat := 0xdb064;
  pa_reset := 0xb2304;   (* [comment removed for export] *)
  pa_parse := 0xb24ec;   (* [comment removed for export] *)
  pa_rtv := 0xb34e4;   (* [comment removed for export] *)
  pa_read_value := 0xb395c;   (* [comment removed for export] *)
  pa_get_length := 0xb5f04;   (* [comment removed for export] *)
  pa_read_key := 0xb4f10;   (* [comment removed for export] *)
  pa_begin_array := 0xb693c;   (* [comment removed for export] *)
  pa_begin_object := 0xb6f9c;   (* [comment removed for export] *)
  pa_end_array := 0xb37a4;   (* [comment removed for export] *)
  pa_end_object := 0xb5254;   (* [comment removed for export] *)
  pa_peek := 0xb4bd0;   (* [comment removed for export] *)
  pa_ignore := 0xb4cf4;   (* [comment removed for export] *)
  pa_src_read := 0xb540c;   (* [comment removed for export] *)
  pa_fill_buffer := 0xb58c8;   (* [comment removed for export] *)
  pa_read_span := 0xb6500;   (* [comment removed for export] *)
  pa_srd_read := 0xb763c;   (* [comment removed for export] *)
  pa_validate := 0xb5b60;   (* [comment removed for export] *)
  pa_is_base10 := 0xb67f4;   (* [comment removed for export] *)
  pa_make_ec := 0xae310;   (* [comment removed for export] *)
  pa_str_resize := 0xd754c;
  pa_str_append := 0xd6ec0;
  pa_xsgetn := 0xdc384;
  pa_uflow := 0xdc498;
  pa_underflow := 0xdc654;
  pa_ios_clear := 0xdbe3c;
  pa_src_dtor := 0xa9c58;   (* [comment removed for export] *)
  pa_istream_dtor := 0xdc5cc;
  pa_ios_dtor := 0xdc2e0;
  pa_iosbase_dtor := 0xdbd34;
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0xa9ec0;   (* [comment removed for export] *)
  pa_opnew := 0x131ec0;
  pa_opdel := 0xd4a60;
  pa_opdel_sized := 0xd4a5c;
  pa_memcpy := 0x12b488;
  pa_memmove := 0x78610;
  pa_memset := 0x12b88c;
  pa_guard_acquire := 0xb8154;
  pa_guard_release := 0xb81a4;
  pa_cxa_atexit := 0x11a21c;
  pa_vp_visitor := 0x1335f0;   (* [comment removed for export] *)
  pa_vp_parser := 0x1334a8;   (* [comment removed for export] *)
  pa_vp_iss := 0x136e28;
  pa_vp_strbuf := 0x136d38;
  pa_vp_iss_ios := 0x136e50;
  pa_vp_nullis := 0x133520;
  pa_vp_nullbuf := 0x133890;
  pa_vp_nullis_ios := 0x133548;
  pa_vp_opts := 0x133428;   (* [comment removed for export] *)
  pa_errcat_guard := 0x674080;
  pa_errcat_obj := 0x13d8f0;
  pa_errcat_dtor := 0xd61d8;
  pa_dso := 0x13afc8;
  pa_syscat_guard := 0x6742b0;
  pa_syscat_obj := 0x13d928;
  pa_glocale := 0x674488;
  pa_classic_imp := 0x6748c0;
  pa_loc_foot := [(0x6742b2, 0x6749f0); (0x675118, 0x675170)];
  pa_atexit := 0x695ad0;
  pa_need_locks := 0x695d13;
  pa_locale_lock := 0x695df0;
  pa_canary := 0x695ac0;
  pa_frame := 1152;   (* [comment removed for export] *)
  pa_off_opts := 1056;   (* [comment removed for export] *)
  pa_off_ec := 1120;   (* [comment removed for export] *)
  pa_off_p := 592;   (* [comment removed for export] *)
  pa_off_v := 496;   (* [comment removed for export] *)
  pa_off_is := 96;   (* [comment removed for export] *)
  pa_off_s := 32;   (* [comment removed for export] *)
  pa_rw_lo := 0x13a000;
  pa_gp := 0x10800;
  pa_tp := 0x675a80
|}.

Definition CAADDR_A : pm_asan_addrs := {|
  paa_annotate := 0x7c400;
  paa_ann_new := 0xb1f3c;   (* [comment removed for export] *)
  paa_ann_delete := 0xa9fe4;   (* [comment removed for export] *)
  paa_ann_shrink := 0xaa084;   (* [comment removed for export] *)
  paa_ann_helper := 0xb2278;   (* [comment removed for export] *)
  paa_ann_increase := 0;   (* [comment removed for export] *)
  paa_esp_mi := 0xb1990;   (* [comment removed for export] *)
  paa_esp_miu := 0xb3128;   (* [comment removed for export] *)
  paa_esp_msu := 0xb79f8;   (* [comment removed for export] *)
  paa_esp_ms := 0xb7d9c;   (* [comment removed for export] *)
  paa_swap_out := 0xb1fe4;   (* [comment removed for export] *)
  paa_set_shadow_f5 := 0x7c290;
  paa_wrap_memset := 0x7860c;
  paa_cxa_atexit_icpt := 0x6e39c;
  paa_at_cxa_atexit := 0x6e420;
  paa_atexit_f0 := 0x11a3a8;
  paa_atexit_a0 := 0x97ee8;
  paa_vec_clear := 0;   (* [comment removed for export] *)
  paa_pop_back := 0;   (* [comment removed for export] *)
  paa_eb_mi := 0;   (* [comment removed for export] *)
  paa_eb_miu := 0;   (* [comment removed for export] *)
  paa_eb_msu := 0;   (* [comment removed for export] *)
  paa_eb_ms := 0;   (* [comment removed for export] *)
  paa_src_eof := 0   (* [comment removed for export] *)
|}.

Definition EADDR_A : pe_addrs := {|
  pe_vt := 0x1335f0;
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
  pe_begin_obj := 0xab904;
  pe_begin_obj_len := 0xab9e8;
  pe_end_obj := 0xabb0c;
  pe_begin_arr := 0xabff4;
  pe_begin_arr_len := 0xaad68;
  pe_end_arr := 0xaae90;
  pe_key := 0xac0d8;
  pe_null := 0xac244;
  pe_bool := 0xac308;
  pe_string := 0xac3d8;
  pe_uint64 := 0xab378;
  pe_int64 := 0xab55c;
  pe_double := 0xab7e0;
  pe_flush := 0xab900;
  pe_put_length := 0xae710;
  pe_push_back := 0xaf02c;
  pe_evec_alloc := 0;
  pe_evec_sbdtor := 0;
  pe_validate_enc := 0xb1068;
  pe_off_sink := 432;
  pe_frame := 1152;
  pe_drv_call := 0x11a3a8;
  pe_drv_guard := 0xa88b0
|}.
