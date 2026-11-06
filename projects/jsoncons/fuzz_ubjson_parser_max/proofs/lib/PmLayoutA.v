(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition ADDR_A : pm_addrs := {|
pa_harness := 0xa764c; pa_str_ctor := 0xa8068; pa_iss_ctor := 0xa81c0; pa_strbuf_ctor := 0xaacc0; pa_init_buf_ptrs := 0xaae78;
pa_str_copy := 0xd10a4; pa_ios_init := 0xd543c; pa_locale_ctor := 0xf9f14; pa_locale_dtor := 0xf9fec;
pa_reader_ctor := 0xab1bc; pa_src_ctor := 0xab488; pa_nullis_ctor := 0xab978; pa_vec_alloc := 0xabebc; pa_splitbuf_dtor := 0xabdd0;
pa_syscat := 0xd45b8; pa_reset := 0xabf84; pa_parse := 0xac16c; pa_rtv := 0xad164; pa_read_value := 0xad5dc; pa_get_length := 0xafe2c;
pa_read_key := 0xaec6c; pa_begin_array := 0xb0864; pa_begin_object := 0xb0ec4; pa_end_array := 0xad424; pa_end_object := 0xaefb0;
pa_peek := 0xae850; pa_ignore := 0xaea50; pa_src_read := 0xaf334; pa_fill_buffer := 0xaf7f0; pa_read_span := 0xb0428; pa_srd_read := 0xb1564;
pa_validate := 0xafa88; pa_is_base10 := 0xb071c; pa_make_ec := 0xae974; pa_str_resize := 0xd1338; pa_str_append := 0xd0dbc;
pa_xsgetn := 0xd58ac; pa_uflow := 0xd59c0; pa_underflow := 0xd5b7c; pa_ios_clear := 0xd5364;
pa_src_dtor := 0xaa34c; pa_istream_dtor := 0xd5af4; pa_ios_dtor := 0xd5808; pa_iosbase_dtor := 0xd525c;
pa_reader_read := 0; pa_vec_dtor := 0xaa5b4;
pa_opnew := 0x12b3e4; pa_opdel := 0xcea58; pa_opdel_sized := 0xcea54;
pa_memcpy := 0x1249ac; pa_memmove := 0x77334; pa_memset := 0x124db0;
pa_guard_acquire := 0xb214c; pa_guard_release := 0xb219c; pa_cxa_atexit := 0x113744;
pa_vp_visitor := 0x12c940; pa_vp_parser := 0x12cb18;
pa_vp_iss := 0x1302a8; pa_vp_strbuf := 0x1301b8; pa_vp_iss_ios := 0x1302d0;
pa_vp_nullis := 0x12cb90; pa_vp_nullbuf := 0x12cc60; pa_vp_nullis_ios := 0x12cbb8; pa_vp_opts := 0x12ca98;
pa_errcat_guard := 0x66d380; pa_errcat_obj := 0x136d70; pa_errcat_dtor := 0xd01d0; pa_dso := 0x134448;
pa_syscat_guard := 0x66d5b0; pa_syscat_obj := 0x136da8;
pa_glocale := 0x66d788; pa_classic_imp := 0x66dbc0;
pa_loc_foot := [(0x66d5b2, 0x66dcf0); (0x66e418, 0x66e470)];
pa_atexit := 0x68edd0; pa_atexit_call := 0x1138d0; pa_exit_guard := 0xa75d4;
pa_need_locks := 0x68f013; pa_locale_lock := 0x68f0f0; pa_canary := 0x68edc0;
pa_frame := 1024; pa_off_opts := 928; pa_off_ec := 992; pa_off_p := 464; pa_off_v := 432; pa_off_is := 96; pa_off_s := 32;
pa_rw_lo := 0x134000; pa_gp := 0x10800; pa_tp := 0x66ed80
|}.
Definition ADDR_B : pm_addrs := {|
pa_harness := 0xa791c; pa_str_ctor := 0xa832c; pa_iss_ctor := 0xa8494; pa_strbuf_ctor := 0xab660; pa_init_buf_ptrs := 0xab828;
pa_str_copy := 0xd2edc; pa_ios_init := 0xd7274; pa_locale_ctor := 0xfbd4c; pa_locale_dtor := 0xfbe24;
pa_reader_ctor := 0xabbb0; pa_src_ctor := 0xabf38; pa_nullis_ctor := 0xac0cc; pa_vec_alloc := 0xacd48; pa_splitbuf_dtor := 0xacc10;
pa_syscat := 0xd63f0; pa_reset := 0xace2c; pa_parse := 0xad088; pa_rtv := 0xae168; pa_read_value := 0xae618; pa_get_length := 0xb160c;
pa_read_key := 0xaff54; pa_begin_array := 0xb209c; pa_begin_object := 0xb2904; pa_end_array := 0xae43c; pa_end_object := 0xb02a4;
pa_peek := 0xaf8ec; pa_ignore := 0xafaf4; pa_src_read := 0xb065c; pa_fill_buffer := 0xb0e58; pa_read_span := 0xb1c08; pa_srd_read := 0xb31b4;
pa_validate := 0xb11c8; pa_is_base10 := 0xb1f28; pa_make_ec := 0xafa18; pa_str_resize := 0xd3170; pa_str_append := 0xd2bf4;
pa_xsgetn := 0xd76e4; pa_uflow := 0xd77f8; pa_underflow := 0xd79b4; pa_ios_clear := 0xd719c;
pa_src_dtor := 0xaab7c; pa_istream_dtor := 0xd792c; pa_ios_dtor := 0xd7640; pa_iosbase_dtor := 0xd7094;
pa_reader_read := 0xa8738; pa_vec_dtor := 0xaade4;
pa_opnew := 0x12d21c; pa_opdel := 0xd0890; pa_opdel_sized := 0xd088c;
pa_memcpy := 0x1267e4; pa_memmove := 0x77604; pa_memset := 0x126be8;
pa_guard_acquire := 0xb3f84; pa_guard_release := 0xb3fd4; pa_cxa_atexit := 0x11557c;
pa_vp_visitor := 0x12e760; pa_vp_parser := 0x12e938;
pa_vp_iss := 0x132010; pa_vp_strbuf := 0x131f20; pa_vp_iss_ios := 0x132038;
pa_vp_nullis := 0x12e9b0; pa_vp_nullbuf := 0x12ea80; pa_vp_nullis_ios := 0x12e9d8; pa_vp_opts := 0x12e8b8;
pa_errcat_guard := 0x66f0c0; pa_errcat_obj := 0x138ad8; pa_errcat_dtor := 0xd2008; pa_dso := 0x1361b0;
pa_syscat_guard := 0x66f2f0; pa_syscat_obj := 0x138b10;
pa_glocale := 0x66f4c8; pa_classic_imp := 0x66f900;
pa_loc_foot := [(0x66f2f2, 0x66fa30); (0x670158, 0x6701b0)];
pa_atexit := 0x690b10; pa_atexit_call := 0x115708; pa_exit_guard := 0xa78a4;
pa_need_locks := 0x690d53; pa_locale_lock := 0x690e30; pa_canary := 0x690b00;
pa_frame := 1024; pa_off_opts := 928; pa_off_ec := 992; pa_off_p := 464; pa_off_v := 432; pa_off_is := 96; pa_off_s := 32;
pa_rw_lo := 0x136000; pa_gp := 0x10800; pa_tp := 0x670ac0
|}.
Record pm_asan_addrs : Type := PAA {
paa_annotate : Z;
paa_ann_new : Z;
paa_ann_delete : Z;
paa_ann_shrink : Z;
paa_ann_helper : Z;
paa_ann_increase : Z;
paa_esp_mi : Z;
paa_esp_miu : Z;
paa_esp_msu : Z;
paa_esp_ms : Z;
paa_swap_out : Z;
paa_set_shadow_f5 : Z;
paa_wrap_memset : Z;
paa_cxa_atexit_icpt : Z;
paa_at_cxa_atexit : Z;
paa_atexit_f0 : Z;
paa_atexit_a0 : Z;
paa_vec_clear : Z; paa_pop_back : Z; paa_eb_mi : Z; paa_eb_miu : Z; paa_eb_msu : Z; paa_eb_ms : Z; paa_src_eof : Z
}.
Definition AADDR_A : pm_asan_addrs := {|
paa_annotate := 0x7b124; paa_ann_new := 0xabbbc; paa_ann_delete := 0xaa6d8; paa_ann_shrink := 0xaa778; paa_ann_helper := 0xabef8; paa_ann_increase := 0;
paa_esp_mi := 0xab610; paa_esp_miu := 0xacda8; paa_esp_msu := 0xb1920; paa_esp_ms := 0xb1cc4; paa_swap_out := 0xabc64;
paa_set_shadow_f5 := 0x7afb4; paa_wrap_memset := 0x77330; paa_cxa_atexit_icpt := 0x6d0c0; paa_at_cxa_atexit := 0x6d144; paa_atexit_f0 := 0x1138d0; paa_atexit_a0 := 0x96c0c;
paa_vec_clear := 0; paa_pop_back := 0; paa_eb_mi := 0; paa_eb_miu := 0; paa_eb_msu := 0; paa_eb_ms := 0; paa_src_eof := 0
|}.
Definition AADDR_B : pm_asan_addrs := {|
paa_annotate := 0x7b3f4; paa_ann_new := 0xac888; paa_ann_delete := 0xab054; paa_ann_shrink := 0xab10c; paa_ann_helper := 0xacd74; paa_ann_increase := 0xac6ec;
paa_esp_mi := 0xac4ac; paa_esp_miu := 0xadef8; paa_esp_msu := 0xb3780; paa_esp_ms := 0xb3b60; paa_swap_out := 0xac9f8;
paa_set_shadow_f5 := 0x7b284; paa_wrap_memset := 0x77600; paa_cxa_atexit_icpt := 0x6d390; paa_at_cxa_atexit := 0x6d414; paa_atexit_f0 := 0x115708; paa_atexit_a0 := 0x96edc;
paa_vec_clear := 0xaaf04; paa_pop_back := 0xb1130; paa_eb_mi := 0xac324; paa_eb_miu := 0xadd40; paa_eb_msu := 0xb35d4; paa_eb_ms := 0xb39e4; paa_src_eof := 0xb34ec
|}.
