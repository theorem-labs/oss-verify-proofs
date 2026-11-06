(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ADDR_U : pm_addrs := {|
pa_harness := 0x342bc; pa_str_ctor := 0x34488; pa_iss_ctor := 0x34550; pa_strbuf_ctor := 0x35c68; pa_init_buf_ptrs := 0x35d54;
pa_str_copy := 0x57aa0; pa_ios_init := 0x5be38; pa_locale_ctor := 0x80910; pa_locale_dtor := 0x809e8;
pa_reader_ctor := 0x35ebc; pa_src_ctor := 0x36030; pa_nullis_ctor := 0x360d0; pa_vec_alloc := 0x363cc; pa_splitbuf_dtor := 0x36364;
pa_syscat := 0x5afb4; pa_reset := 0x36408; pa_parse := 0x36574; pa_rtv := 0x369bc; pa_read_value := 0x36afc; pa_get_length := 0x37aa4;
pa_read_key := 0x37238; pa_begin_array := 0x37e78; pa_begin_object := 0x38324; pa_end_array := 0x36a68; pa_end_object := 0x37320;
pa_peek := 0x37050; pa_ignore := 0x37144; pa_src_read := 0x374b8; pa_fill_buffer := 0x37720; pa_read_span := 0x37cb0; pa_srd_read := 0x387ec;
pa_validate := 0x37844; pa_is_base10 := 0x37db8; pa_make_ec := 0x370ac; pa_str_resize := 0x57d34; pa_str_append := 0x577b8;
pa_xsgetn := 0x5c2a8; pa_uflow := 0x5c3bc; pa_underflow := 0x5c578; pa_ios_clear := 0x5bd60;
pa_src_dtor := 0x357f4; pa_istream_dtor := 0x5c4f0; pa_ios_dtor := 0x5c204; pa_iosbase_dtor := 0x5bc58;
pa_reader_read := 0x34664; pa_vec_dtor := 0x35928;
pa_opnew := 0xaf0ec; pa_opdel := 0x55454; pa_opdel_sized := 0x55450;
pa_memcpy := 0xaa1b4; pa_memmove := 0xaa5b8; pa_memset := 0xaa734;
pa_guard_acquire := 0x38b48; pa_guard_release := 0x38b98; pa_cxa_atexit := 0x99944;
pa_vp_visitor := 0xb0238; pa_vp_parser := 0xb0410;
pa_vp_iss := 0xb3ae8; pa_vp_strbuf := 0xb39f8; pa_vp_iss_ios := 0xb3b10;
pa_vp_nullis := 0xb0488; pa_vp_nullbuf := 0xb0558; pa_vp_nullis_ios := 0xb04b0; pa_vp_opts := 0xb0390;
pa_errcat_guard := 0xc72b0; pa_errcat_obj := 0xb6f70; pa_errcat_dtor := 0x56bcc; pa_dso := 0xb6f48;
pa_syscat_guard := 0xc74e0; pa_syscat_obj := 0xb6fa8;
pa_glocale := 0xc76b8; pa_classic_imp := 0xc7af0;
pa_loc_foot := [(0xc74e2, 0xc7c20); (0xc8348, 0xc83a0)];
pa_atexit := 0xe8cf8; pa_atexit_call := 0x99ad0; pa_exit_guard := 0x34244;
pa_need_locks := 0xe8f43; pa_locale_lock := 0xe9018; pa_canary := 0xe8f20;
pa_frame := 752; pa_off_opts := 8; pa_off_ec := 8; pa_off_p := 40; pa_off_v := 432; pa_off_is := 440; pa_off_s := 712;
pa_rw_lo := 0xb7120; pa_gp := 0x10800; pa_tp := 0xc8cb0
|}.
