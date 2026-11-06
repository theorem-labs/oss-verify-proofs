(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.
Module PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ADDR_A : pm_addrs := {|
  pa_harness := 0xa7340; pa_str_ctor := 0xa7d5c; pa_iss_ctor := 0xa7eb4; pa_strbuf_ctor := 0xaa9b4; pa_init_buf_ptrs := 0xaab6c;
  pa_str_copy := 0xd0d98; pa_ios_init := 0xd5130; pa_locale_ctor := 0xf9c08; pa_locale_dtor := 0xf9ce0;
  pa_reader_ctor := 0xaaeb0; pa_src_ctor := 0xab17c; pa_nullis_ctor := 0xab66c; pa_vec_alloc := 0xabbb0; pa_splitbuf_dtor := 0xabac4;
  pa_syscat := 0xd42ac; pa_reset := 0xabc78; pa_parse := 0xabe60; pa_rtv := 0xace58; pa_read_value := 0xad2d0; pa_get_length := 0xafb20;
  pa_read_key := 0xae960; pa_begin_array := 0xb0558; pa_begin_object := 0xb0bb8; pa_end_array := 0xad118; pa_end_object := 0xaeca4;
  pa_peek := 0xae544; pa_ignore := 0xae744; pa_src_read := 0xaf028; pa_fill_buffer := 0xaf4e4; pa_read_span := 0xb011c; pa_srd_read := 0xb1258;
  pa_validate := 0xaf77c; pa_is_base10 := 0xb0410; pa_make_ec := 0xae668; pa_str_resize := 0xd102c; pa_str_append := 0xd0ab0;
  pa_xsgetn := 0xd55a0; pa_uflow := 0xd56b4; pa_underflow := 0xd5870; pa_ios_clear := 0xd5058;
  pa_src_dtor := 0xaa040; pa_istream_dtor := 0xd57e8; pa_ios_dtor := 0xd54fc; pa_iosbase_dtor := 0xd4f50;
  pa_reader_read := 0; pa_vec_dtor := 0xaa2a8;
  pa_opnew := 0x12b0d8; pa_opdel := 0xce74c; pa_opdel_sized := 0xce748;
  pa_memcpy := 0x1246ac; pa_memmove := 0x771ec; pa_memset := 0x124ab0;
  pa_guard_acquire := 0xb1e40; pa_guard_release := 0xb1e90; pa_cxa_atexit := 0x113444;
  pa_vp_visitor := 0x12c630; pa_vp_parser := 0x12c808;
  pa_vp_iss := 0x12ff98; pa_vp_strbuf := 0x12fea8; pa_vp_iss_ios := 0x12ffc0;
  pa_vp_nullis := 0x12c880; pa_vp_nullbuf := 0x12c950; pa_vp_nullis_ios := 0x12c8a8; pa_vp_opts := 0x12c788;
  pa_errcat_guard := 0x66d000; pa_errcat_obj := 0x136a48; pa_errcat_dtor := 0xcfec4; pa_dso := 0x134128;
  pa_syscat_guard := 0x66d230; pa_syscat_obj := 0x136a80;
  pa_glocale := 0x66d408; pa_classic_imp := 0x66d840;
  pa_loc_foot := [(0x66d232, 0x66d970); (0x66e098, 0x66e0f0)];
  pa_atexit := 0x66ead0; pa_need_locks := 0x66ed13; pa_locale_lock := 0x66edf0; pa_canary := 0x66eac0;
  pa_frame := 1024; pa_off_opts := 928; pa_off_ec := 992; pa_off_p := 464; pa_off_v := 432; pa_off_is := 96; pa_off_s := 32;
  pa_rw_lo := 0x134000; pa_gp := 0x10800; pa_tp := 0x66ea38
|}.

Definition ADDR_B : pm_addrs := {|
  pa_harness := 0xa7618; pa_str_ctor := 0xa8028; pa_iss_ctor := 0xa8190; pa_strbuf_ctor := 0xab35c; pa_init_buf_ptrs := 0xab524;
  pa_str_copy := 0xd2bd8; pa_ios_init := 0xd6f70; pa_locale_ctor := 0xfba48; pa_locale_dtor := 0xfbb20;
  pa_reader_ctor := 0xab8ac; pa_src_ctor := 0xabc34; pa_nullis_ctor := 0xabdc8; pa_vec_alloc := 0xaca44; pa_splitbuf_dtor := 0xac90c;
  pa_syscat := 0xd60ec; pa_reset := 0xacb28; pa_parse := 0xacd84; pa_rtv := 0xade64; pa_read_value := 0xae314; pa_get_length := 0xb1308;
  pa_read_key := 0xafc50; pa_begin_array := 0xb1d98; pa_begin_object := 0xb2600; pa_end_array := 0xae138; pa_end_object := 0xaffa0;
  pa_peek := 0xaf5e8; pa_ignore := 0xaf7f0; pa_src_read := 0xb0358; pa_fill_buffer := 0xb0b54; pa_read_span := 0xb1904; pa_srd_read := 0xb2eb0;
  pa_validate := 0xb0ec4; pa_is_base10 := 0xb1c24; pa_make_ec := 0xaf714; pa_str_resize := 0xd2e6c; pa_str_append := 0xd28f0;
  pa_xsgetn := 0xd73e0; pa_uflow := 0xd74f4; pa_underflow := 0xd76b0; pa_ios_clear := 0xd6e98;
  pa_src_dtor := 0xaa878; pa_istream_dtor := 0xd7628; pa_ios_dtor := 0xd733c; pa_iosbase_dtor := 0xd6d90;
  pa_reader_read := 0xa8434; pa_vec_dtor := 0xaaae0;
  pa_opnew := 0x12cf18; pa_opdel := 0xd058c; pa_opdel_sized := 0xd0588;
  pa_memcpy := 0x1264ec; pa_memmove := 0x774c4; pa_memset := 0x1268f0;
  pa_guard_acquire := 0xb3c80; pa_guard_release := 0xb3cd0; pa_cxa_atexit := 0x115284;
  pa_vp_visitor := 0x12e460; pa_vp_parser := 0x12e638;
  pa_vp_iss := 0x131d10; pa_vp_strbuf := 0x131c20; pa_vp_iss_ios := 0x131d38;
  pa_vp_nullis := 0x12e6b0; pa_vp_nullbuf := 0x12e780; pa_vp_nullis_ios := 0x12e6d8; pa_vp_opts := 0x12e5b8;
  pa_errcat_guard := 0x66ed40; pa_errcat_obj := 0x1387b4; pa_errcat_dtor := 0xd1d04; pa_dso := 0x135ea0;
  pa_syscat_guard := 0x66ef70; pa_syscat_obj := 0x1387ec;
  pa_glocale := 0x66f148; pa_classic_imp := 0x66f580;
  pa_loc_foot := [(0x66ef72, 0x66f6b0); (0x66fdd8, 0x66fe30)];
  pa_atexit := 0x670810; pa_need_locks := 0x670a53; pa_locale_lock := 0x670b30; pa_canary := 0x670800;
  pa_frame := 1024; pa_off_opts := 928; pa_off_ec := 992; pa_off_p := 464; pa_off_v := 432; pa_off_is := 96; pa_off_s := 32;
  pa_rw_lo := 0x135000; pa_gp := 0x10800; pa_tp := 0x670778
|}.

(* [comment removed for export] *)
Record pm_asan_addrs : Type := PAA {
  paa_annotate : Z;        (* [comment removed for export] *)
  paa_ann_new : Z;         (* [comment removed for export] *)
  paa_ann_delete : Z;      (* [comment removed for export] *)
  paa_ann_shrink : Z;      (* [comment removed for export] *)
  paa_ann_helper : Z;      (* [comment removed for export] *)
  paa_ann_increase : Z;    (* [comment removed for export] *)
  paa_esp_mi : Z;          (* [comment removed for export] *)
  paa_esp_miu : Z;         (* [comment removed for export] *)
  paa_esp_msu : Z;         (* [comment removed for export] *)
  paa_esp_ms : Z;          (* [comment removed for export] *)
  paa_swap_out : Z;        (* [comment removed for export] *)
  paa_set_shadow_f5 : Z;   (* [comment removed for export] *)
  paa_wrap_memset : Z;     (* [comment removed for export] *)
  paa_cxa_atexit_icpt : Z; (* [comment removed for export] *)
  paa_at_cxa_atexit : Z;   (* [comment removed for export] *)
  paa_atexit_f0 : Z;       (* [comment removed for export] *)
  paa_atexit_a0 : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  paa_vec_clear : Z; paa_pop_back : Z; paa_eb_mi : Z; paa_eb_miu : Z; paa_eb_msu : Z; paa_eb_ms : Z; paa_src_eof : Z
}.

Definition AADDR_A : pm_asan_addrs := {|
  paa_annotate := 0x7afdc; paa_ann_new := 0xab8b0; paa_ann_delete := 0xaa3cc; paa_ann_shrink := 0xaa46c; paa_ann_helper := 0xabbec; paa_ann_increase := 0;
  paa_esp_mi := 0xab304; paa_esp_miu := 0xaca9c; paa_esp_msu := 0xb1614; paa_esp_ms := 0xb19b8; paa_swap_out := 0xab958;
  paa_set_shadow_f5 := 0x7ae6c; paa_wrap_memset := 0x771e8; paa_cxa_atexit_icpt := 0x6cf78; paa_at_cxa_atexit := 0x6cffc; paa_atexit_f0 := 0x1135d0; paa_atexit_a0 := 0x96988;
  paa_vec_clear := 0; paa_pop_back := 0; paa_eb_mi := 0; paa_eb_miu := 0; paa_eb_msu := 0; paa_eb_ms := 0; paa_src_eof := 0
|}.

Definition AADDR_B : pm_asan_addrs := {|
  paa_annotate := 0x7b2b4; paa_ann_new := 0xac584; paa_ann_delete := 0xaad50; paa_ann_shrink := 0xaae08; paa_ann_helper := 0xaca70; paa_ann_increase := 0xac3e8;
  paa_esp_mi := 0xac1a8; paa_esp_miu := 0xadbf4; paa_esp_msu := 0xb347c; paa_esp_ms := 0xb385c; paa_swap_out := 0xac6f4;
  paa_set_shadow_f5 := 0x7b144; paa_wrap_memset := 0x774c0; paa_cxa_atexit_icpt := 0x6d250; paa_at_cxa_atexit := 0x6d2d4; paa_atexit_f0 := 0x115410; paa_atexit_a0 := 0x96c60;
  paa_vec_clear := 0xaac00; paa_pop_back := 0xb0e2c; paa_eb_mi := 0xac020; paa_eb_miu := 0xada3c; paa_eb_msu := 0xb32d0; paa_eb_ms := 0xb36e0; paa_src_eof := 0xb31e8
|}.

End PmLayoutA.
Module PnLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout.
(* [comment removed for export] *)
Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ADDR_A : pm_addrs := {|
  pa_harness := 0xaeecc;   (* [comment removed for export] *)
  pa_str_ctor := 0xafab8;   (* [comment removed for export] *)
  pa_iss_ctor := 0xafc10;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0xc15f4;   (* [comment removed for export] *)
  pa_init_buf_ptrs := 0xc17ac;   (* [comment removed for export] *)
  pa_str_copy := 0xf4a74;   (* [comment removed for export] *)
  pa_ios_init := 0xf97e0;   (* [comment removed for export] *)
  pa_locale_ctor := 0x11e2b8;   (* [comment removed for export] *)
  pa_locale_dtor := 0x11e390;   (* [comment removed for export] *)
  pa_reader_ctor := 0xafeac;   (* [comment removed for export] *)
  pa_src_ctor := 0xceff0;   (* [comment removed for export] *)
  pa_nullis_ctor := 0xcf4b4;   (* [comment removed for export] *)
  pa_vec_alloc := 0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0;   (* [comment removed for export] *)
  pa_syscat := 0xf8930;   (* [comment removed for export] *)
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
  pa_src_read := 0xd2ab0;   (* [comment removed for export] *)
  pa_fill_buffer := 0xd4b30;   (* [comment removed for export] *)
  pa_read_span := 0;   (* [comment removed for export] *)
  pa_srd_read := 0;   (* [comment removed for export] *)
  pa_validate := 0xd3560;   (* [comment removed for export] *)
  pa_is_base10 := 0;   (* [comment removed for export] *)
  pa_make_ec := 0xc5ed8;   (* [comment removed for export] *)
  pa_str_resize := 0xf4e18;   (* [comment removed for export] *)
  pa_str_append := 0xf478c;   (* [comment removed for export] *)
  pa_xsgetn := 0xf9c50;   (* [comment removed for export] *)
  pa_uflow := 0xf9d64;   (* [comment removed for export] *)
  pa_underflow := 0xf9f20;   (* [comment removed for export] *)
  pa_ios_clear := 0xf9708;   (* [comment removed for export] *)
  pa_src_dtor := 0xc0b10;   (* [comment removed for export] *)
  pa_istream_dtor := 0xf9e98;   (* [comment removed for export] *)
  pa_ios_dtor := 0xf9bac;   (* [comment removed for export] *)
  pa_iosbase_dtor := 0xf9600;   (* [comment removed for export] *)
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0;   (* [comment removed for export] *)
  pa_opnew := 0x14f7a0;   (* [comment removed for export] *)
  pa_opdel := 0xf1fc0;   (* [comment removed for export] *)
  pa_opdel_sized := 0xf1fbc;   (* [comment removed for export] *)
  pa_memcpy := 0x148d68;   (* [comment removed for export] *)
  pa_memmove := 0x7ebb4;   (* [comment removed for export] *)
  pa_memset := 0x14916c;   (* [comment removed for export] *)
  pa_guard_acquire := 0xd56a0;   (* [comment removed for export] *)
  pa_guard_release := 0xd56f0;   (* [comment removed for export] *)
  pa_cxa_atexit := 0x137ae8;   (* [comment removed for export] *)
  pa_vp_visitor := 0x151408;   (* [comment removed for export] *)
  pa_vp_parser := 0x150fe8;   (* [comment removed for export] *)
  pa_vp_iss := 0x154a08;   (* [comment removed for export] *)
  pa_vp_strbuf := 0x154918;   (* [comment removed for export] *)
  pa_vp_iss_ios := 0x154a30;   (* [comment removed for export] *)
  pa_vp_nullis := 0x151060;   (* [comment removed for export] *)
  pa_vp_nullbuf := 0x151370;   (* [comment removed for export] *)
  pa_vp_nullis_ios := 0x151088;   (* [comment removed for export] *)
  pa_vp_opts := 0x150d08;   (* [comment removed for export] *)
  pa_errcat_guard := 0x692100;   (* [comment removed for export] *)
  pa_errcat_obj := 0x15b4d0;   (* [comment removed for export] *)
  pa_errcat_dtor := 0xf3738;   (* [comment removed for export] *)
  pa_dso := 0x158ba8;   (* [comment removed for export] *)
  pa_syscat_guard := 0x692330;   (* [comment removed for export] *)
  pa_syscat_obj := 0x15b508;   (* [comment removed for export] *)
  pa_glocale := 0x692508;   (* [comment removed for export] *)
  pa_classic_imp := 0x692940;   (* [comment removed for export] *)
  pa_loc_foot := [(0x692332, 0x692a70); (0x693198, 0x6931f0)];   (* [comment removed for export] *)
  pa_atexit := 0x6b3b50;   (* [comment removed for export] *)
  pa_need_locks := 0x6b3d93;   (* [comment removed for export] *)
  pa_locale_lock := 0x6b3e70;   (* [comment removed for export] *)
  pa_canary := 0x6b3b40;   (* [comment removed for export] *)
  pa_frame := 1280;   (* [comment removed for export] *)
  pa_off_opts := 1168;   (* [comment removed for export] *)
  pa_off_ec := 1232;   (* [comment removed for export] *)
  pa_off_p := 592;   (* [comment removed for export] *)
  pa_off_v := 496;   (* [comment removed for export] *)
  pa_off_is := 96;   (* [comment removed for export] *)
  pa_off_s := 32;   (* [comment removed for export] *)
  pa_rw_lo := 0x158000;   (* [comment removed for export] *)
  pa_gp := 0x10800;   (* [comment removed for export] *)
  pa_tp := 0x693b00   (* [comment removed for export] *)
|}.

Definition AADDR_A : pm_asan_addrs := {|
  paa_annotate := 0x829a4;   (* [comment removed for export] *)
  paa_ann_new := 0;   (* [comment removed for export] *)
  paa_ann_delete := 0xc0ea8;   (* [comment removed for export] *)
  paa_ann_shrink := 0;   (* [comment removed for export] *)
  paa_ann_helper := 0;   (* [comment removed for export] *)
  paa_ann_increase := 0;   (* [comment removed for export] *)
  paa_esp_mi := 0;   (* [comment removed for export] *)
  paa_esp_miu := 0;   (* [comment removed for export] *)
  paa_esp_msu := 0;   (* [comment removed for export] *)
  paa_esp_ms := 0;   (* [comment removed for export] *)
  paa_swap_out := 0;   (* [comment removed for export] *)
  paa_set_shadow_f5 := 0x82834;   (* [comment removed for export] *)
  paa_wrap_memset := 0x7ebb0;   (* [comment removed for export] *)
  paa_cxa_atexit_icpt := 0x74940;   (* [comment removed for export] *)
  paa_at_cxa_atexit := 0x749c4;   (* [comment removed for export] *)
  paa_atexit_f0 := 0x137c74;   (* [comment removed for export] *)
  paa_atexit_a0 := 0x9e48c;   (* [comment removed for export] *)
  paa_vec_clear := 0;   (* [comment removed for export] *)
  paa_pop_back := 0;   (* [comment removed for export] *)
  paa_eb_mi := 0;   (* [comment removed for export] *)
  paa_eb_miu := 0;   (* [comment removed for export] *)
  paa_eb_msu := 0;   (* [comment removed for export] *)
  paa_eb_ms := 0;   (* [comment removed for export] *)
  paa_src_eof := 0   (* [comment removed for export] *)
|}.

Definition NADDR_A : PNL.pn_addrs := {|
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
  PNL.pn_read_span_v := 0xd3324;   (* [comment removed for export] *)
  PNL.pn_srd_read_v := 0xd50ec;   (* [comment removed for export] *)
  PNL.pn_vu8_resize := 0xd53d4;   (* [comment removed for export] *)
  PNL.pn_vu8_append := 0xd5470;   (* [comment removed for export] *)
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
  PNL.pn_str_push_back := 0xf4640;   (* [comment removed for export] *)
  PNL.pn_str_cstr := 0xb8d9c;   (* [comment removed for export] *)
  PNL.pn_str_dtor := 0xf3cd0;   (* [comment removed for export] *)
  PNL.pn_strlen := 0x149650;   (* [comment removed for export] *)
  PNL.pn_vbs_tag := 0xcfb6c;   (* [comment removed for export] *)
  PNL.pn_vbs_ext := 0xc5e74;   (* [comment removed for export] *)
  PNL.pn_strlen_icpt := 0x6a378;   (* [comment removed for export] *)
  PNL.pn_wrap_strlen := 0x6a294;   (* [comment removed for export] *)
  PNL.pn_wrap_cxa_atexit := 0x6a374;   (* [comment removed for export] *)
  PNL.pn_inf_guard := 0;   (* [comment removed for export] *)
  PNL.pn_inf_obj := 0;   (* [comment removed for export] *)
  PNL.pn_inf_lit := 0;   (* [comment removed for export] *)
  PNL.pn_nan_guard := 0;   (* [comment removed for export] *)
  PNL.pn_nan_obj := 0;   (* [comment removed for export] *)
  PNL.pn_nan_lit := 0;   (* [comment removed for export] *)
  PNL.pn_str_dtor_slot := 0x157b28;   (* [comment removed for export] *)
  PNL.pn_drv_call := 0x137c74;   (* [comment removed for export] *)
  PNL.pn_drv_guard := 0xaee54   (* [comment removed for export] *)
|}.

Definition ADDR_B : pm_addrs := {|
  pa_harness := 0xadd24;   (* [comment removed for export] *)
  pa_str_ctor := 0xb019c;   (* [comment removed for export] *)
  pa_iss_ctor := 0xc5d9c;   (* [comment removed for export] *)
  pa_strbuf_ctor := 0xd11b0;   (* [comment removed for export] *)
  pa_init_buf_ptrs := 0xd1378;   (* [comment removed for export] *)
  pa_str_copy := 0xf9dd4;   (* [comment removed for export] *)
  pa_ios_init := 0xfe16c;   (* [comment removed for export] *)
  pa_locale_ctor := 0x122c44;   (* [comment removed for export] *)
  pa_locale_dtor := 0x122d1c;   (* [comment removed for export] *)
  pa_reader_ctor := 0xc4514;   (* [comment removed for export] *)
  pa_src_ctor := 0xd1cf4;   (* [comment removed for export] *)
  pa_nullis_ctor := 0xd1e88;   (* [comment removed for export] *)
  pa_vec_alloc := 0;   (* [comment removed for export] *)
  pa_splitbuf_dtor := 0;   (* [comment removed for export] *)
  pa_syscat := 0xfd2e8;   (* [comment removed for export] *)
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
  pa_src_read := 0xd4f7c;   (* [comment removed for export] *)
  pa_fill_buffer := 0xccb18;   (* [comment removed for export] *)
  pa_read_span := 0;   (* [comment removed for export] *)
  pa_srd_read := 0;   (* [comment removed for export] *)
  pa_validate := 0xca644;   (* [comment removed for export] *)
  pa_is_base10 := 0;   (* [comment removed for export] *)
  pa_make_ec := 0xd4ea0;   (* [comment removed for export] *)
  pa_str_resize := 0xfa068;   (* [comment removed for export] *)
  pa_str_append := 0xf9aec;   (* [comment removed for export] *)
  pa_xsgetn := 0xfe5dc;   (* [comment removed for export] *)
  pa_uflow := 0xfe6f0;   (* [comment removed for export] *)
  pa_underflow := 0xfe8ac;   (* [comment removed for export] *)
  pa_ios_clear := 0xfe094;   (* [comment removed for export] *)
  pa_src_dtor := 0xd0458;   (* [comment removed for export] *)
  pa_istream_dtor := 0xfe824;   (* [comment removed for export] *)
  pa_ios_dtor := 0xfe538;   (* [comment removed for export] *)
  pa_iosbase_dtor := 0xfdf8c;   (* [comment removed for export] *)
  pa_reader_read := 0;   (* [comment removed for export] *)
  pa_vec_dtor := 0xd06c0;   (* [comment removed for export] *)
  pa_opnew := 0x1543a4;   (* [comment removed for export] *)
  pa_opdel := 0xf6b58;   (* [comment removed for export] *)
  pa_opdel_sized := 0xf6b54;   (* [comment removed for export] *)
  pa_memcpy := 0x14d794;   (* [comment removed for export] *)
  pa_memmove := 0x7f284;   (* [comment removed for export] *)
  pa_memset := 0x14db98;   (* [comment removed for export] *)
  pa_guard_acquire := 0xda02c;   (* [comment removed for export] *)
  pa_guard_release := 0xda07c;   (* [comment removed for export] *)
  pa_cxa_atexit := 0x13c474;   (* [comment removed for export] *)
  pa_vp_visitor := 0x1558e8;   (* [comment removed for export] *)
  pa_vp_parser := 0x155d10;   (* [comment removed for export] *)
  pa_vp_iss := 0x1593a8;   (* [comment removed for export] *)
  pa_vp_strbuf := 0x1592b8;   (* [comment removed for export] *)
  pa_vp_iss_ios := 0x159370;   (* [comment removed for export] *)
  pa_vp_nullis := 0x155d88;   (* [comment removed for export] *)
  pa_vp_nullbuf := 0x155e58;   (* [comment removed for export] *)
  pa_vp_nullis_ios := 0x155db0;   (* [comment removed for export] *)
  pa_vp_opts := 0x155a40;   (* [comment removed for export] *)
  pa_errcat_guard := 0x6b6d00;   (* [comment removed for export] *)
  pa_errcat_obj := 0x160050;   (* [comment removed for export] *)
  pa_errcat_dtor := 0xf8b94;   (* [comment removed for export] *)
  pa_dso := 0x15d728;   (* [comment removed for export] *)
  pa_syscat_guard := 0x6b6f30;   (* [comment removed for export] *)
  pa_syscat_obj := 0x160088;   (* [comment removed for export] *)
  pa_glocale := 0x6b7108;   (* [comment removed for export] *)
  pa_classic_imp := 0x6b7540;   (* [comment removed for export] *)
  pa_loc_foot := [(0x6b6f32, 0x6b7670); (0x6b7d98, 0x6b7df0)];   (* [comment removed for export] *)
  pa_atexit := 0x6b87d0;   (* [comment removed for export] *)
  pa_need_locks := 0x6b8a13;   (* [comment removed for export] *)
  pa_locale_lock := 0x6b8af0;   (* [comment removed for export] *)
  pa_canary := 0x6b87c0;   (* [comment removed for export] *)
  pa_frame := 1152;   (* [comment removed for export] *)
  pa_off_opts := 1040;   (* [comment removed for export] *)
  pa_off_ec := 1104;   (* [comment removed for export] *)
  pa_off_p := 464;   (* [comment removed for export] *)
  pa_off_v := 432;   (* [comment removed for export] *)
  pa_off_is := 96;   (* [comment removed for export] *)
  pa_off_s := 32;   (* [comment removed for export] *)
  pa_rw_lo := 0x154000;   (* [comment removed for export] *)
  pa_gp := 0x10800;   (* [comment removed for export] *)
  pa_tp := 0x6b8738   (* [comment removed for export] *)
|}.

Definition AADDR_B : pm_asan_addrs := {|
  paa_annotate := 0x83074;   (* [comment removed for export] *)
  paa_ann_new := 0;   (* [comment removed for export] *)
  paa_ann_delete := 0;   (* [comment removed for export] *)
  paa_ann_shrink := 0xd0a00;   (* [comment removed for export] *)
  paa_ann_helper := 0;   (* [comment removed for export] *)
  paa_ann_increase := 0;   (* [comment removed for export] *)
  paa_esp_mi := 0;   (* [comment removed for export] *)
  paa_esp_miu := 0;   (* [comment removed for export] *)
  paa_esp_msu := 0;   (* [comment removed for export] *)
  paa_esp_ms := 0;   (* [comment removed for export] *)
  paa_swap_out := 0;   (* [comment removed for export] *)
  paa_set_shadow_f5 := 0x82f04;   (* [comment removed for export] *)
  paa_wrap_memset := 0x7f280;   (* [comment removed for export] *)
  paa_cxa_atexit_icpt := 0x75010;   (* [comment removed for export] *)
  paa_at_cxa_atexit := 0x75094;   (* [comment removed for export] *)
  paa_atexit_f0 := 0x13c600;   (* [comment removed for export] *)
  paa_atexit_a0 := 0x9eb5c;   (* [comment removed for export] *)
  paa_vec_clear := 0xd07e0;   (* [comment removed for export] *)
  paa_pop_back := 0;   (* [comment removed for export] *)
  paa_eb_mi := 0;   (* [comment removed for export] *)
  paa_eb_miu := 0;   (* [comment removed for export] *)
  paa_eb_msu := 0;   (* [comment removed for export] *)
  paa_eb_ms := 0;   (* [comment removed for export] *)
  paa_src_eof := 0xcd2c0   (* [comment removed for export] *)
|}.

Definition NADDR_B : PNL.pn_addrs := {|
  PNL.pn_reader_ctor := 0;   (* [comment removed for export] *)
  PNL.pn_reader_dtor := 0;   (* [comment removed for export] *)
  PNL.pn_reader_read := 0xcfb50;   (* [comment removed for export] *)
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
  PNL.pn_read_span_v := 0xca41c;   (* [comment removed for export] *)
  PNL.pn_srd_read_v := 0xcbf80;   (* [comment removed for export] *)
  PNL.pn_vu8_resize := 0xcc060;   (* [comment removed for export] *)
  PNL.pn_vu8_append := 0xd56ac;   (* [comment removed for export] *)
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
  PNL.pn_str_push_back := 0xf99a0;   (* [comment removed for export] *)
  PNL.pn_str_cstr := 0xba3d4;   (* [comment removed for export] *)
  PNL.pn_str_dtor := 0xf912c;   (* [comment removed for export] *)
  PNL.pn_strlen := 0x14e07c;   (* [comment removed for export] *)
  PNL.pn_vbs_tag := 0xc4af4;   (* [comment removed for export] *)
  PNL.pn_vbs_ext := 0xc4afc;   (* [comment removed for export] *)
  PNL.pn_strlen_icpt := 0x6aa48;   (* [comment removed for export] *)
  PNL.pn_wrap_strlen := 0x6a964;   (* [comment removed for export] *)
  PNL.pn_wrap_cxa_atexit := 0x6aa44;   (* [comment removed for export] *)
  PNL.pn_inf_guard := 0;   (* [comment removed for export] *)
  PNL.pn_inf_obj := 0;   (* [comment removed for export] *)
  PNL.pn_inf_lit := 0;   (* [comment removed for export] *)
  PNL.pn_nan_guard := 0;   (* [comment removed for export] *)
  PNL.pn_nan_obj := 0;   (* [comment removed for export] *)
  PNL.pn_nan_lit := 0;   (* [comment removed for export] *)
  PNL.pn_str_dtor_slot := 0x15c6a8;   (* [comment removed for export] *)
  PNL.pn_drv_call := 0x13c600;   (* [comment removed for export] *)
  PNL.pn_drv_guard := 0xadcac   (* [comment removed for export] *)
|}.


End PnLayoutA.
From Stdlib Require ZArith.
Module NemLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition NEADDR_A : ne_addrs := {|
  ne_vt                 := 0x151130;   (* [comment removed for export] *)
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
  ne_begin_arr_len      := 0xc1b2c;   (* [comment removed for export] *)
  ne_end_arr            := 0xc1cb4;   (* [comment removed for export] *)
  ne_uint64             := 0xc2158;   (* [comment removed for export] *)
  ne_int64              := 0xc23e4;   (* [comment removed for export] *)
  ne_double             := 0xc27a4;   (* [comment removed for export] *)
  ne_flush              := 0xc28c4;   (* [comment removed for export] *)
  ne_begin_obj_len      := 0xc28ec;   (* [comment removed for export] *)
  ne_end_obj            := 0xc2a70;   (* [comment removed for export] *)
  ne_key                := 0xc2f38;   (* [comment removed for export] *)
  ne_null               := 0xc2f60;   (* [comment removed for export] *)
  ne_bool               := 0xc3024;   (* [comment removed for export] *)
  ne_string             := 0xc30e8;   (* [comment removed for export] *)
  ne_bstr_tag           := 0xc3c7c;   (* [comment removed for export] *)
  ne_bstr_raw           := 0xc3ee0;   (* [comment removed for export] *)
  ne_push_back          := 0xc6a1c;   (* [comment removed for export] *)
  ne_evec_alloc         := 0xc5fb4;   (* [comment removed for export] *)
  ne_evec_sbdtor        := 0;
  ne_ntb_u16            := 0xc62d8;   (* [comment removed for export] *)
  ne_ntb_u32            := 0xc636c;   (* [comment removed for export] *)
  ne_ntb_u64            := 0xc7134;   (* [comment removed for export] *)
  ne_ntb_i8             := 0;   (* [comment removed for export] *)
  ne_ntb_i16            := 0xc7220;   (* [comment removed for export] *)
  ne_ntb_i32            := 0xc72b8;   (* [comment removed for export] *)
  ne_ntb_i64            := 0xc736c;   (* [comment removed for export] *)
  ne_ntb_f32            := 0xc7458;   (* [comment removed for export] *)
  ne_ntb_f64            := 0xc7510;   (* [comment removed for export] *)
  ne_write_timestamp    := 0xc6fb0;   (* [comment removed for export] *)
  ne_write_string_value := 0xc8b50;   (* [comment removed for export] *)
  ne_validate_enc       := 0xcd538;   (* [comment removed for export] *)
  ne_to_bigint          := 0xc7600;   (* [comment removed for export] *)
  ne_to_bigint_d        := 0xc8e20;   (* [comment removed for export] *)
  ne_to_bigint_h        := 0;   (* [comment removed for export] *)
  ne_ts_helper          := 0xc76f0;   (* [comment removed for export] *)
  ne_divide             := 0xc799c;   (* [comment removed for export] *)
  ne_make_ec            := 0xc5ed8;   (* [comment removed for export] *)
  ne_off_sink           := 432;
  ne_spare              := 0
|}.

End NemLayoutA.
Module PnLayoutQA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition QADDR_A : pq_addrs := {|
  qa_vp_adaptor := 0x150d88;   (* [comment removed for export] *)
  qa_off_a := 400;   (* [comment removed for export] *)
  qa_off_vref := 496;   (* [comment removed for export] *)
  qa_parser_ctor := 0xceb7c;   (* [comment removed for export] *)
  qa_adaptor_ctor := 0xcee24;   (* [comment removed for export] *)
  qa_reader_dtor := 0xaff54;   (* [comment removed for export] *)
  qa_reset := 0xcfb7c;   (* [comment removed for export] *)
  qa_parse := 0xcfdb4;   (* [comment removed for export] *)
  qa_read_item := 0xd051c;   (* [comment removed for export] *)
  qa_begin_array := 0xd3148;   (* [comment removed for export] *)
  qa_begin_object := 0xd2f6c;   (* [comment removed for export] *)
  qa_get_size := 0xd3904;   (* [comment removed for export] *)
  qa_ps_alloc := 0xcfa28;   (* [comment removed for export] *)
  qa_ps_sbdtor := 0xcf920;   (* [comment removed for export] *)
  qa_read_span_v := 0xd3324;   (* [comment removed for export] *)
  qa_srd_read_v := 0xd50ec;   (* [comment removed for export] *)
  qa_vu8_resize := 0xd53d4;   (* [comment removed for export] *)
  qa_vu8_append := 0xd5470;   (* [comment removed for export] *)
  qa_v_begin_array := 0xb06b8;   (* [comment removed for export] *)
  qa_v_end_array := 0xb090c;   (* [comment removed for export] *)
  qa_v_uint64 := 0xb1320;   (* [comment removed for export] *)
  qa_v_int64 := 0xb1b44;   (* [comment removed for export] *)
  qa_v_double := 0xb2368;   (* [comment removed for export] *)
  qa_v_flush := 0xb2c00;   (* [comment removed for export] *)
  qa_v_begin_object := 0xb2e40;   (* [comment removed for export] *)
  qa_v_end_object := 0xb309c;   (* [comment removed for export] *)
  qa_v_null := 0xb3cf4;   (* [comment removed for export] *)
  qa_v_bool := 0xb456c;   (* [comment removed for export] *)
  qa_v_string := 0xb4e30;   (* [comment removed for export] *)
  qa_v_bstr_tag := 0xb52d0;   (* [comment removed for export] *)
  qa_v_bstr_raw := 0xb5c20;   (* [comment removed for export] *)
  qa_js_alloc := 0xb8c88;   (* [comment removed for export] *)
  qa_js_sbdtor := 0xb8ac8;   (* [comment removed for export] *)
  qa_from_u64 := 0xb8fb0;   (* [comment removed for export] *)
  qa_from_i64 := 0xba148;   (* [comment removed for export] *)
  qa_str_insert := 0xb95f0;   (* [comment removed for export] *)
  qa_str_append := 0xbe330;   (* [comment removed for export] *)
  qa_b64url := 0xbebe4;   (* [comment removed for export] *)
  qa_b64disp := 0xbeac0;   (* [comment removed for export] *)
  qa_push_back := 0xf4640;   (* [comment removed for export] *)
  qa_write_double := 0xba7f8;   (* [comment removed for export] *)
  qa_localeconv := 0;   (* [comment removed for export] *)
  qa_ts_list := [0xcce0c; 0xc99fc; 0xd3d10; 0xd4448; 0xcaed8; 0xd4678];   (* [comment removed for export] *)
  qa_drv_call := 0x137c74;   (* [comment removed for export] *)
  qa_drv_guard := 0xaee54   (* [comment removed for export] *)
|}.

(* [comment removed for export] *)
Definition FCM : list Z := [0; 1; 2; 3; 4; 5].
(* [comment removed for export] *)
Definition QCLS_A : list (Z * Z * Z) :=
  [(0xceb7c, -1, 80)   (* [comment removed for export] *);
   (0xcee24, -1, 80)   (* [comment removed for export] *);
   (0xaff54, -1, 32)   (* [comment removed for export] *);
   (0xcfb7c, -1, 48)   (* [comment removed for export] *);
   (0xcfdb4, 1, 224)   (* [comment removed for export] *);
   (0xd051c, 4, 160)   (* [comment removed for export] *);
   (0xd3148, -1, 80)   (* [comment removed for export] *);
   (0xd2f6c, -1, 80)   (* [comment removed for export] *);
   (0xd3904, 1, 96)   (* [comment removed for export] *);
   (0xcfa28, -1, 16)   (* [comment removed for export] *);
   (0xcf920, -1, 16)   (* [comment removed for export] *);
   (0xd3324, -1, 80)   (* [comment removed for export] *);
   (0xd50ec, -1, 160)   (* [comment removed for export] *);
   (0xd53d4, -1, 16)   (* [comment removed for export] *);
   (0xd5470, -1, 96)   (* [comment removed for export] *);
   (0xb06b8, -1, 80)   (* [comment removed for export] *);
   (0xb090c, 2, 160)   (* [comment removed for export] *);
   (0xb1320, 0, 160)   (* [comment removed for export] *);
   (0xb1b44, 0, 160)   (* [comment removed for export] *);
   (0xb2368, 0, 160)   (* [comment removed for export] *);
   (0xb2c00, -1, 16)   (* [comment removed for export] *);
   (0xb2e40, -1, 80)   (* [comment removed for export] *);
   (0xb309c, 2, 160)   (* [comment removed for export] *);
   (0xb3cf4, 0, 128)   (* [comment removed for export] *);
   (0xb456c, 0, 160)   (* [comment removed for export] *);
   (0xb4e30, -1, 64)   (* [comment removed for export] *);
   (0xb52d0, 1, 160)   (* [comment removed for export] *);
   (0xb5c20, 1, 160)   (* [comment removed for export] *);
   (0xb8c88, -1, 16)   (* [comment removed for export] *);
   (0xb8ac8, -1, 16)   (* [comment removed for export] *);
   (0xb8fb0, 3, 128)   (* [comment removed for export] *);
   (0xba148, 3, 128)   (* [comment removed for export] *);
   (0xb95f0, 1, 128)   (* [comment removed for export] *);
   (0xbe330, 1, 128)   (* [comment removed for export] *);
   (0xbebe4, 0, 160)   (* [comment removed for export] *);
   (0xbeac0, -1, 80)   (* [comment removed for export] *);
   (0xf4640, -1, 64)   (* [comment removed for export] *);
   (0xba7f8, 4, 96)   (* [comment removed for export] *);
   (0x137c74, -1, 32)   (* [comment removed for export] *);
   (0xaee54, -1, 16)   (* [comment removed for export] *)].

End PnLayoutQA.
From Stdlib Require ZArith List Lia Bool.
Module PnAEmbKitQ.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PQAEKQ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma d24 x : (24 * x) / 8 = 3 * x.
Proof. Lia.lia. Qed.
Lemma d24b x : (24 * x + 24) / 8 = 3 * x + 3.
Proof. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PQAEKQ.

End PnAEmbKitQ.
