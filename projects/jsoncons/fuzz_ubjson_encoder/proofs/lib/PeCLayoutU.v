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

Definition CADDR_U : pm_addrs := {|
  pa_harness := 0x34eec;
  pa_str_ctor := 0x35124;
  pa_iss_ctor := 0x351ec;
  pa_strbuf_ctor := 0x359ac;
  pa_init_buf_ptrs := 0x35a98;
  pa_str_copy := 0x5af1c;
  pa_ios_init := 0x5fc88;
  pa_locale_ctor := 0x84760;
  pa_locale_dtor := 0x84838;
  pa_reader_ctor := 0x39560;   (* [comment removed for export] *)
  pa_src_ctor := 0x396d4;
  pa_nullis_ctor := 0x39774;
  pa_vec_alloc := 0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0;   (* [comment removed for export] *)
  pa_syscat := 0x5edd8;
  pa_reset := 0x39aac;   (* [comment removed for export] *)
  pa_parse := 0x39c18;   (* [comment removed for export] *)
  pa_rtv := 0x3a060;   (* [comment removed for export] *)
  pa_read_value := 0x3a1a0;   (* [comment removed for export] *)
  pa_get_length := 0x3afac;   (* [comment removed for export] *)
  pa_read_key := 0x3a844;   (* [comment removed for export] *)
  pa_begin_array := 0x3b380;   (* [comment removed for export] *)
  pa_begin_object := 0x3b82c;   (* [comment removed for export] *)
  pa_end_array := 0x3a10c;   (* [comment removed for export] *)
  pa_end_object := 0x3a92c;   (* [comment removed for export] *)
  pa_peek := 0x3a6f4;   (* [comment removed for export] *)
  pa_ignore := 0x3a750;   (* [comment removed for export] *)
  pa_src_read := 0x3a9c0;   (* [comment removed for export] *)
  pa_fill_buffer := 0x3ac28;   (* [comment removed for export] *)
  pa_read_span := 0x3b1b8;   (* [comment removed for export] *)
  pa_srd_read := 0x3bcf4;   (* [comment removed for export] *)
  pa_validate := 0x3ad4c;   (* [comment removed for export] *)
  pa_is_base10 := 0x3b2c0;   (* [comment removed for export] *)
  pa_make_ec := 0x37ca8;   (* [comment removed for export] *)
  pa_str_resize := 0x5b2c0;
  pa_str_append := 0x5ac34;
  pa_xsgetn := 0x600f8;
  pa_uflow := 0x6020c;
  pa_underflow := 0x603c8;
  pa_ios_clear := 0x5fbb0;
  pa_src_dtor := 0x354ec;
  pa_istream_dtor := 0x60340;
  pa_ios_dtor := 0x60054;
  pa_iosbase_dtor := 0x5faa8;
  pa_reader_read := 0x35300;   (* [comment removed for export] *)
  pa_vec_dtor := 0x35620;   (* [comment removed for export] *)
  pa_opnew := 0xb2f40;
  pa_opdel := 0x587d4;
  pa_opdel_sized := 0x587d0;
  pa_memcpy := 0xae008;
  pa_memmove := 0xae40c;
  pa_memset := 0xae588;
  pa_guard_acquire := 0x3bec8;
  pa_guard_release := 0x3bf18;
  pa_cxa_atexit := 0x9d794;
  pa_vp_visitor := 0xb4260;   (* [comment removed for export] *)
  pa_vp_parser := 0xb4118;   (* [comment removed for export] *)
  pa_vp_iss := 0xb79f0;
  pa_vp_strbuf := 0xb7900;
  pa_vp_iss_ios := 0xb7a18;
  pa_vp_nullis := 0xb4190;
  pa_vp_nullbuf := 0xb4500;
  pa_vp_nullis_ios := 0xb41b8;
  pa_vp_opts := 0xb4098;   (* [comment removed for export] *)
  pa_errcat_guard := 0xcb1c0;
  pa_errcat_obj := 0xbae78;
  pa_errcat_dtor := 0x59f4c;
  pa_dso := 0xbae50;
  pa_syscat_guard := 0xcb3f0;
  pa_syscat_obj := 0xbaeb0;
  pa_glocale := 0xcb5c8;
  pa_classic_imp := 0xcba00;
  pa_loc_foot := [(0xcb3f2, 0xcbb30); (0xcc258, 0xcc2b0)];
  pa_atexit := 0xecc08;
  pa_need_locks := 0xece53;
  pa_locale_lock := 0xecf28;
  pa_canary := 0xece30;
  pa_frame := 832;   (* [comment removed for export] *)
  pa_off_opts := 8;   (* [comment removed for export] *)
  pa_off_ec := 8;   (* [comment removed for export] *)
  pa_off_p := 40;   (* [comment removed for export] *)
  pa_off_v := 432;   (* [comment removed for export] *)
  pa_off_is := 512;   (* [comment removed for export] *)
  pa_off_s := 784;   (* [comment removed for export] *)
  pa_rw_lo := 0xbb028;
  pa_gp := 0x10800;
  pa_tp := 0xccbc0
|}.

Definition EADDR_U : pe_addrs := {|
  pe_vt := 0xb4260;
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
  pe_begin_obj := 0x36374;
  pe_begin_obj_len := 0x3644c;
  pe_end_obj := 0x36610;
  pe_begin_arr := 0x36798;
  pe_begin_arr_len := 0x35c3c;
  pe_end_arr := 0x35e08;
  pe_key := 0x36870;
  pe_null := 0x36948;
  pe_bool := 0x369bc;
  pe_string := 0x36a40;
  pe_uint64 := 0x35f90;
  pe_int64 := 0x360f0;
  pe_double := 0x36290;
  pe_flush := 0x36370;
  pe_put_length := 0x37d40;
  pe_push_back := 0x38348;
  pe_evec_alloc := 0x391b0;
  pe_evec_sbdtor := 0;
  pe_validate_enc := 0x392b4;
  pe_off_sink := 488;
  pe_frame := 832;
  pe_drv_call := 0x9d920;
  pe_drv_guard := 0x34e74
|}.
