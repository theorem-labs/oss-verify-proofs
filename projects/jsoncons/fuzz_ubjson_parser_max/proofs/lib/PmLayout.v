(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Record pm_addrs : Type := PA {
pa_harness : Z;
pa_str_ctor : Z;
pa_iss_ctor : Z;
pa_strbuf_ctor : Z;
pa_init_buf_ptrs : Z;
pa_str_copy : Z;
pa_ios_init : Z;
pa_locale_ctor : Z;
pa_locale_dtor : Z;
pa_reader_ctor : Z;
pa_src_ctor : Z;
pa_nullis_ctor : Z;
pa_vec_alloc : Z;
pa_splitbuf_dtor : Z;
pa_syscat : Z;
pa_reset : Z;
pa_parse : Z;
pa_rtv : Z;
pa_read_value : Z;
pa_get_length : Z;
pa_read_key : Z;
pa_begin_array : Z;
pa_begin_object : Z;
pa_end_array : Z;
pa_end_object : Z;
pa_peek : Z;
pa_ignore : Z;
pa_src_read : Z;
pa_fill_buffer : Z;
pa_read_span : Z;
pa_srd_read : Z;
pa_validate : Z;
pa_is_base10 : Z;
pa_make_ec : Z;
pa_str_resize : Z;
pa_str_append : Z;
pa_xsgetn : Z;
pa_uflow : Z;
pa_underflow : Z;
pa_ios_clear : Z;
pa_src_dtor : Z;
pa_istream_dtor : Z;
pa_ios_dtor : Z;
pa_iosbase_dtor : Z;
pa_reader_read : Z;
pa_vec_dtor : Z;
pa_opnew : Z;
pa_opdel : Z;
pa_opdel_sized : Z;
pa_memcpy : Z; pa_memmove : Z; pa_memset : Z;
pa_guard_acquire : Z; pa_guard_release : Z;
pa_cxa_atexit : Z;
pa_vp_visitor : Z;
pa_vp_parser : Z;
pa_vp_iss : Z;
pa_vp_strbuf : Z;
pa_vp_iss_ios : Z;
pa_vp_nullis : Z;
pa_vp_nullbuf : Z;
pa_vp_nullis_ios : Z;
pa_vp_opts : Z;
pa_errcat_guard : Z;
pa_errcat_obj : Z;
pa_errcat_dtor : Z;
pa_dso : Z;
pa_syscat_guard : Z;
pa_syscat_obj : Z;
pa_glocale : Z;
pa_classic_imp : Z;
pa_loc_foot : list (Z * Z);
pa_atexit : Z;
pa_atexit_call : Z;
pa_exit_guard : Z;
pa_need_locks : Z;
pa_locale_lock : Z;
pa_canary : Z;
pa_frame : Z;
pa_off_opts : Z;
pa_off_ec : Z;
pa_off_p : Z;
pa_off_v : Z;
pa_off_is : Z;
pa_off_s : Z;
pa_rw_lo : Z;
pa_gp : Z;
pa_tp : Z
}.
Definition pm_foot (A : pm_addrs) : list (Z * Z) :=
[(pa_errcat_guard A, pa_errcat_guard A + 2); (pa_syscat_guard A, pa_syscat_guard A + 2)]
++ pa_loc_foot A ++ [(pa_atexit A, pa_atexit A + 544)].
Definition pm_initc (A : pm_addrs) : list (Z * Z) :=
[(pa_need_locks A, pa_need_locks A + 1); (pa_locale_lock A, pa_locale_lock A + 4)].
