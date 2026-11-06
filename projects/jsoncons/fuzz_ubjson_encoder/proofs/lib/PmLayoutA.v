(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ADDR_A : pm_addrs := {|
  pa_harness := 0xa72f0; pa_str_ctor := 0xa7d0c; pa_iss_ctor := 0xa7e64; pa_strbuf_ctor := 0xaa964; pa_init_buf_ptrs := 0xaab1c;
  pa_str_copy := 0xd0d48; pa_ios_init := 0xd50e0; pa_locale_ctor := 0xf9bb8; pa_locale_dtor := 0xf9c90;
  pa_reader_ctor := 0xaae60; pa_src_ctor := 0xab12c; pa_nullis_ctor := 0xab61c; pa_vec_alloc := 0xabb60; pa_splitbuf_dtor := 0xaba74;
  pa_syscat := 0xd425c; pa_reset := 0xabc28; pa_parse := 0xabe10; pa_rtv := 0xace08; pa_read_value := 0xad280; pa_get_length := 0xafad0;
  pa_read_key := 0xae910; pa_begin_array := 0xb0508; pa_begin_object := 0xb0b68; pa_end_array := 0xad0c8; pa_end_object := 0xaec54;
  pa_peek := 0xae4f4; pa_ignore := 0xae6f4; pa_src_read := 0xaefd8; pa_fill_buffer := 0xaf494; pa_read_span := 0xb00cc; pa_srd_read := 0xb1208;
  pa_validate := 0xaf72c; pa_is_base10 := 0xb03c0; pa_make_ec := 0xae618; pa_str_resize := 0xd0fdc; pa_str_append := 0xd0a60;
  pa_xsgetn := 0xd5550; pa_uflow := 0xd5664; pa_underflow := 0xd5820; pa_ios_clear := 0xd5008;
  pa_src_dtor := 0xa9ff0; pa_istream_dtor := 0xd5798; pa_ios_dtor := 0xd54ac; pa_iosbase_dtor := 0xd4f00;
  pa_reader_read := 0; pa_vec_dtor := 0xaa258;
  pa_opnew := 0x12b088; pa_opdel := 0xce6fc; pa_opdel_sized := 0xce6f8;
  pa_memcpy := 0x12465c; pa_memmove := 0x7719c; pa_memset := 0x124a60;
  pa_guard_acquire := 0xb1df0; pa_guard_release := 0xb1e40; pa_cxa_atexit := 0x1133f4;
  pa_vp_visitor := 0x12c5e0; pa_vp_parser := 0x12c7b8;
  pa_vp_iss := 0x12ff48; pa_vp_strbuf := 0x12fe58; pa_vp_iss_ios := 0x12ff70;
  pa_vp_nullis := 0x12c830; pa_vp_nullbuf := 0x12c900; pa_vp_nullis_ios := 0x12c858; pa_vp_opts := 0x12c738;
  pa_errcat_guard := 0x66d000; pa_errcat_obj := 0x1369f8; pa_errcat_dtor := 0xcfe74; pa_dso := 0x1340d8;
  pa_syscat_guard := 0x66d230; pa_syscat_obj := 0x136a30;
  pa_glocale := 0x66d408; pa_classic_imp := 0x66d840;
  pa_loc_foot := [(0x66d232, 0x66d970); (0x66e098, 0x66e0f0)];
  pa_atexit := 0x66ead0; pa_need_locks := 0x66ed13; pa_locale_lock := 0x66edf0; pa_canary := 0x66eac0;
  pa_frame := 1024; pa_off_opts := 928; pa_off_ec := 992; pa_off_p := 464; pa_off_v := 432; pa_off_is := 96; pa_off_s := 32;
  pa_rw_lo := 0x134000; pa_gp := 0x10800; pa_tp := 0x66ea38
|}.

Definition ADDR_B : pm_addrs := {|
  pa_harness := 0xa75c8; pa_str_ctor := 0xa7fd8; pa_iss_ctor := 0xa8140; pa_strbuf_ctor := 0xab30c; pa_init_buf_ptrs := 0xab4d4;
  pa_str_copy := 0xd2b88; pa_ios_init := 0xd6f20; pa_locale_ctor := 0xfb9f8; pa_locale_dtor := 0xfbad0;
  pa_reader_ctor := 0xab85c; pa_src_ctor := 0xabbe4; pa_nullis_ctor := 0xabd78; pa_vec_alloc := 0xac9f4; pa_splitbuf_dtor := 0xac8bc;
  pa_syscat := 0xd609c; pa_reset := 0xacad8; pa_parse := 0xacd34; pa_rtv := 0xade14; pa_read_value := 0xae2c4; pa_get_length := 0xb12b8;
  pa_read_key := 0xafc00; pa_begin_array := 0xb1d48; pa_begin_object := 0xb25b0; pa_end_array := 0xae0e8; pa_end_object := 0xaff50;
  pa_peek := 0xaf598; pa_ignore := 0xaf7a0; pa_src_read := 0xb0308; pa_fill_buffer := 0xb0b04; pa_read_span := 0xb18b4; pa_srd_read := 0xb2e60;
  pa_validate := 0xb0e74; pa_is_base10 := 0xb1bd4; pa_make_ec := 0xaf6c4; pa_str_resize := 0xd2e1c; pa_str_append := 0xd28a0;
  pa_xsgetn := 0xd7390; pa_uflow := 0xd74a4; pa_underflow := 0xd7660; pa_ios_clear := 0xd6e48;
  pa_src_dtor := 0xaa828; pa_istream_dtor := 0xd75d8; pa_ios_dtor := 0xd72ec; pa_iosbase_dtor := 0xd6d40;
  pa_reader_read := 0xa83e4; pa_vec_dtor := 0xaaa90;
  pa_opnew := 0x12cec8; pa_opdel := 0xd053c; pa_opdel_sized := 0xd0538;
  pa_memcpy := 0x12649c; pa_memmove := 0x77474; pa_memset := 0x1268a0;
  pa_guard_acquire := 0xb3c30; pa_guard_release := 0xb3c80; pa_cxa_atexit := 0x115234;
  pa_vp_visitor := 0x12e410; pa_vp_parser := 0x12e5e8;
  pa_vp_iss := 0x131cc0; pa_vp_strbuf := 0x131bd0; pa_vp_iss_ios := 0x131ce8;
  pa_vp_nullis := 0x12e660; pa_vp_nullbuf := 0x12e730; pa_vp_nullis_ios := 0x12e688; pa_vp_opts := 0x12e568;
  pa_errcat_guard := 0x66ed40; pa_errcat_obj := 0x138770; pa_errcat_dtor := 0xd1cb4; pa_dso := 0x135e50;
  pa_syscat_guard := 0x66ef70; pa_syscat_obj := 0x1387a8;
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
  paa_annotate := 0x7af8c; paa_ann_new := 0xab860; paa_ann_delete := 0xaa37c; paa_ann_shrink := 0xaa41c; paa_ann_helper := 0xabb9c; paa_ann_increase := 0;
  paa_esp_mi := 0xab2b4; paa_esp_miu := 0xaca4c; paa_esp_msu := 0xb15c4; paa_esp_ms := 0xb1968; paa_swap_out := 0xab908;
  paa_set_shadow_f5 := 0x7ae1c; paa_wrap_memset := 0x77198; paa_cxa_atexit_icpt := 0x6cf28; paa_at_cxa_atexit := 0x6cfac; paa_atexit_f0 := 0x113580; paa_atexit_a0 := 0x96938;
  paa_vec_clear := 0; paa_pop_back := 0; paa_eb_mi := 0; paa_eb_miu := 0; paa_eb_msu := 0; paa_eb_ms := 0; paa_src_eof := 0
|}.

Definition AADDR_B : pm_asan_addrs := {|
  paa_annotate := 0x7b264; paa_ann_new := 0xac534; paa_ann_delete := 0xaad00; paa_ann_shrink := 0xaadb8; paa_ann_helper := 0xaca20; paa_ann_increase := 0xac398;
  paa_esp_mi := 0xac158; paa_esp_miu := 0xadba4; paa_esp_msu := 0xb342c; paa_esp_ms := 0xb380c; paa_swap_out := 0xac6a4;
  paa_set_shadow_f5 := 0x7b0f4; paa_wrap_memset := 0x77470; paa_cxa_atexit_icpt := 0x6d200; paa_at_cxa_atexit := 0x6d284; paa_atexit_f0 := 0x1153c0; paa_atexit_a0 := 0x96c10;
  paa_vec_clear := 0xaabb0; paa_pop_back := 0xb0ddc; paa_eb_mi := 0xabfd0; paa_eb_miu := 0xad9ec; paa_eb_msu := 0xb3280; paa_eb_ms := 0xb3690; paa_src_eof := 0xb3198
|}.
