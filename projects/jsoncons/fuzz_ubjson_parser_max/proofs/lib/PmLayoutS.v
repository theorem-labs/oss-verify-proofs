(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ADDR_S : pm_addrs := {|
pa_harness := 0x3404c; pa_str_ctor := 0x3422c; pa_iss_ctor := 0x342e4; pa_strbuf_ctor := 0x353cc; pa_init_buf_ptrs := 0x354b8;
pa_str_copy := 0x56a4c; pa_ios_init := 0x5ade4; pa_locale_ctor := 0x7f8bc; pa_locale_dtor := 0x7f994;
pa_reader_ctor := 0x355f8; pa_src_ctor := 0x3575c; pa_nullis_ctor := 0x357f0; pa_vec_alloc := 0x3594c; pa_splitbuf_dtor := 0x358fc;
pa_syscat := 0x59f60; pa_reset := 0x35984; pa_parse := 0x35aac; pa_rtv := 0x35e30; pa_read_value := 0x35f3c; pa_get_length := 0x36cf8;
pa_read_key := 0x365f0; pa_begin_array := 0x37090; pa_begin_object := 0x374a0; pa_end_array := 0x35ec8; pa_end_object := 0x366c8;
pa_peek := 0x3643c; pa_ignore := 0x36528; pa_src_read := 0x36830; pa_fill_buffer := 0x36a08; pa_read_span := 0x36f04; pa_srd_read := 0x378c4;
pa_validate := 0x36aec; pa_is_base10 := 0x37000; pa_make_ec := 0x36490; pa_str_resize := 0x56ce0; pa_str_append := 0x56764;
pa_xsgetn := 0x5b254; pa_uflow := 0x5b368; pa_underflow := 0x5b524; pa_ios_clear := 0x5ad0c;
pa_src_dtor := 0x34fcc; pa_istream_dtor := 0x5b49c; pa_ios_dtor := 0x5b1b0; pa_iosbase_dtor := 0x5ac04;
pa_reader_read := 0; pa_vec_dtor := 0;
pa_opnew := 0xae098; pa_opdel := 0x54400; pa_opdel_sized := 0x543fc;
pa_memcpy := 0xa9160; pa_memmove := 0xa9564; pa_memset := 0xa96e0;
pa_guard_acquire := 0x37af4; pa_guard_release := 0x37b44; pa_cxa_atexit := 0x988f0;
pa_vp_visitor := 0xaf1e8; pa_vp_parser := 0xaf3c0;
pa_vp_iss := 0xb2a98; pa_vp_strbuf := 0xb29a8; pa_vp_iss_ios := 0xb2ac0;
pa_vp_nullis := 0xaf438; pa_vp_nullbuf := 0xaf508; pa_vp_nullis_ios := 0xaf460; pa_vp_opts := 0xaf340;
pa_errcat_guard := 0xc6260; pa_errcat_obj := 0xb5f20; pa_errcat_dtor := 0x55b78; pa_dso := 0xb5ef8;
pa_syscat_guard := 0xc6490; pa_syscat_obj := 0xb5f58;
pa_glocale := 0xc6668; pa_classic_imp := 0xc6aa0;
pa_loc_foot := [(0xc6492, 0xc6bd0); (0xc72f8, 0xc7350)];
pa_atexit := 0xe7ca8; pa_atexit_call := 0x98a7c; pa_exit_guard := 0x33fd4;
pa_need_locks := 0xe7ef3; pa_locale_lock := 0xe7fc8; pa_canary := 0xe7ed0;
pa_frame := 752; pa_off_opts := 8; pa_off_ec := 8; pa_off_p := 40; pa_off_v := 432; pa_off_is := 440; pa_off_s := 712;
pa_rw_lo := 0xb60d0; pa_gp := 0x10800; pa_tp := 0xc7c60
|}.
