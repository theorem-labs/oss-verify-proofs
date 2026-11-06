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

Definition CADDR_B : pm_addrs := {|
  pa_harness := 0xa9150;
  pa_str_ctor := 0xa9ca0;   (* [comment removed for export] *)
  pa_iss_ctor := 0xa9e08;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0xab374;
  pa_init_buf_ptrs := 0xab53c;
  pa_str_copy := 0xdb950;
  pa_ios_init := 0xe06bc;
  pa_locale_ctor := 0x105194;
  pa_locale_dtor := 0x10526c;
  pa_reader_ctor := 0xb4954;   (* [comment removed for export] *)
  pa_src_ctor := 0xb4cdc;   (* [comment removed for export] *)
  pa_nullis_ctor := 0xb4e70;
  pa_vec_alloc := 0xb5aec;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0xb59b4;   (* [comment removed for export] *)
  pa_syscat := 0xdf80c;
  pa_reset := 0xb5bd0;   (* [comment removed for export] *)
  pa_parse := 0xb5e2c;   (* [comment removed for export] *)
  pa_rtv := 0xb6f0c;   (* [comment removed for export] *)
  pa_read_value := 0xb73bc;   (* [comment removed for export] *)
  pa_get_length := 0xba0f8;   (* [comment removed for export] *)
  pa_read_key := 0xb8c1c;   (* [comment removed for export] *)
  pa_begin_array := 0xbab88;   (* [comment removed for export] *)
  pa_begin_object := 0xbb3f0;   (* [comment removed for export] *)
  pa_end_array := 0xb71e0;   (* [comment removed for export] *)
  pa_end_object := 0xb8f6c;   (* [comment removed for export] *)
  pa_peek := 0xb8690;   (* [comment removed for export] *)
  pa_ignore := 0xb87bc;   (* [comment removed for export] *)
  pa_src_read := 0xb9148;   (* [comment removed for export] *)
  pa_fill_buffer := 0xb9944;   (* [comment removed for export] *)
  pa_read_span := 0xba6f4;   (* [comment removed for export] *)
  pa_srd_read := 0xbbca0;   (* [comment removed for export] *)
  pa_validate := 0xb9cb4;   (* [comment removed for export] *)
  pa_is_base10 := 0xbaa14;   (* [comment removed for export] *)
  pa_make_ec := 0xafda8;   (* [comment removed for export] *)
  pa_str_resize := 0xdbcf4;
  pa_str_append := 0xdb668;
  pa_xsgetn := 0xe0b2c;
  pa_uflow := 0xe0c40;
  pa_underflow := 0xe0dfc;
  pa_ios_clear := 0xe05e4;
  pa_src_dtor := 0xaa500;   (* [comment removed for export] *)
  pa_istream_dtor := 0xe0d74;
  pa_ios_dtor := 0xe0a88;
  pa_iosbase_dtor := 0xe04dc;
  pa_reader_read := 0xaa0ac;   (* [comment removed for export] *)
  pa_vec_dtor := 0xaa768;   (* [comment removed for export] *)
  pa_opnew := 0x136668;
  pa_opdel := 0xd9208;
  pa_opdel_sized := 0xd9204;
  pa_memcpy := 0x12fc30;
  pa_memmove := 0x78e38;
  pa_memset := 0x130034;
  pa_guard_acquire := 0xbc8e8;
  pa_guard_release := 0xbc938;
  pa_cxa_atexit := 0x11e9c4;
  pa_vp_visitor := 0x137d80;   (* [comment removed for export] *)
  pa_vp_parser := 0x137c38;   (* [comment removed for export] *)
  pa_vp_iss := 0x13b538;
  pa_vp_strbuf := 0x13b448;
  pa_vp_iss_ios := 0x13b560;
  pa_vp_nullis := 0x137cb0;
  pa_vp_nullbuf := 0x138048;
  pa_vp_nullis_ios := 0x137cd8;
  pa_vp_opts := 0x137bb8;   (* [comment removed for export] *)
  pa_errcat_guard := 0x678780;
  pa_errcat_obj := 0x142000;
  pa_errcat_dtor := 0xda980;
  pa_dso := 0x13f6d8;
  pa_syscat_guard := 0x6789b0;
  pa_syscat_obj := 0x142038;
  pa_glocale := 0x678b88;
  pa_classic_imp := 0x678fc0;
  pa_loc_foot := [(0x6789b2, 0x6790f0); (0x679818, 0x679870)];
  pa_atexit := 0x69a1d0;
  pa_need_locks := 0x69a413;
  pa_locale_lock := 0x69a4f0;
  pa_canary := 0x69a1c0;
  pa_frame := 1152;   (* [comment removed for export] *)
  pa_off_opts := 1056;   (* [comment removed for export] *)
  pa_off_ec := 1120;   (* [comment removed for export] *)
  pa_off_p := 592;   (* [comment removed for export] *)
  pa_off_v := 496;   (* [comment removed for export] *)
  pa_off_is := 96;   (* [comment removed for export] *)
  pa_off_s := 32;   (* [comment removed for export] *)
  pa_rw_lo := 0x13f000;
  pa_gp := 0x10800;
  pa_tp := 0x67a180
|}.

Definition CAADDR_B : pm_asan_addrs := {|
  paa_annotate := 0x7cc28;
  paa_ann_new := 0xb562c;   (* [comment removed for export] *)
  paa_ann_delete := 0xaa9d8;   (* [comment removed for export] *)
  paa_ann_shrink := 0xaaa90;   (* [comment removed for export] *)
  paa_ann_helper := 0xb5b18;   (* [comment removed for export] *)
  paa_ann_increase := 0xb5490;   (* [comment removed for export] *)
  paa_esp_mi := 0xb5250;   (* [comment removed for export] *)
  paa_esp_miu := 0xb6c9c;   (* [comment removed for export] *)
  paa_esp_msu := 0xbc26c;   (* [comment removed for export] *)
  paa_esp_ms := 0xbc64c;   (* [comment removed for export] *)
  paa_swap_out := 0xb579c;   (* [comment removed for export] *)
  paa_set_shadow_f5 := 0x7cab8;
  paa_wrap_memset := 0x78e34;
  paa_cxa_atexit_icpt := 0x6ebc4;
  paa_at_cxa_atexit := 0x6ec48;
  paa_atexit_f0 := 0x11eb50;
  paa_atexit_a0 := 0x98710;
  paa_vec_clear := 0xaa888;   (* [comment removed for export] *)
  paa_pop_back := 0xb9c1c;   (* [comment removed for export] *)
  paa_eb_mi := 0xb50c8;   (* [comment removed for export] *)
  paa_eb_miu := 0xb6ae4;   (* [comment removed for export] *)
  paa_eb_msu := 0xbc0c0;   (* [comment removed for export] *)
  paa_eb_ms := 0xbc4d0;   (* [comment removed for export] *)
  paa_src_eof := 0xbbfd8   (* [comment removed for export] *)
|}.

Definition EADDR_B : pe_addrs := {|
  pe_vt := 0x137d80;
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
  pe_begin_obj := 0xac964;
  pe_begin_obj_len := 0xacb14;
  pe_end_obj := 0xacd0c;
  pe_begin_arr := 0xad238;
  pe_begin_arr_len := 0xab900;
  pe_end_arr := 0xabafc;
  pe_key := 0xad3e8;
  pe_null := 0xad588;
  pe_bool := 0xad7ac;
  pe_string := 0xad8a8;
  pe_uint64 := 0xac028;
  pe_int64 := 0xac3a0;
  pe_double := 0xac808;
  pe_flush := 0xac960;
  pe_put_length := 0xafe84;
  pe_push_back := 0xb120c;
  pe_evec_alloc := 0;
  pe_evec_sbdtor := 0;
  pe_validate_enc := 0xb4350;
  pe_off_sink := 432;
  pe_frame := 1152;
  pe_drv_call := 0x11eb50;
  pe_drv_guard := 0xa90d8
|}.
