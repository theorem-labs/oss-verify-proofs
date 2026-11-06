(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record pm_addrs : Type := PA {
  (* [comment removed for export] *)
  pa_harness : Z;          (* [comment removed for export] *)
  pa_str_ctor : Z;         (* [comment removed for export] *)
  pa_iss_ctor : Z;         (* [comment removed for export] *)
  pa_strbuf_ctor : Z;      (* [comment removed for export] *)
  pa_init_buf_ptrs : Z;    (* [comment removed for export] *)
  pa_str_copy : Z;         (* [comment removed for export] *)
  pa_ios_init : Z;         (* [comment removed for export] *)
  pa_locale_ctor : Z;      (* [comment removed for export] *)
  pa_locale_dtor : Z;      (* [comment removed for export] *)
  pa_reader_ctor : Z;      (* [comment removed for export] *)
  pa_src_ctor : Z;         (* [comment removed for export] *)
  pa_nullis_ctor : Z;      (* [comment removed for export] *)
  pa_vec_alloc : Z;        (* [comment removed for export] *)
  pa_splitbuf_dtor : Z;    (* [comment removed for export] *)
  pa_syscat : Z;           (* [comment removed for export] *)
  pa_reset : Z;            (* [comment removed for export] *)
  pa_parse : Z;            (* [comment removed for export] *)
  pa_rtv : Z;              (* [comment removed for export] *)
  pa_read_value : Z;
  pa_get_length : Z;
  pa_read_key : Z;
  pa_begin_array : Z;
  pa_begin_object : Z;
  pa_end_array : Z;
  pa_end_object : Z;
  pa_peek : Z;             (* [comment removed for export] *)
  pa_ignore : Z;           (* [comment removed for export] *)
  pa_src_read : Z;         (* [comment removed for export] *)
  pa_fill_buffer : Z;      (* [comment removed for export] *)
  pa_read_span : Z;        (* [comment removed for export] *)
  pa_srd_read : Z;         (* [comment removed for export] *)
  pa_validate : Z;         (* [comment removed for export] *)
  pa_is_base10 : Z;
  pa_make_ec : Z;          (* [comment removed for export] *)
  pa_str_resize : Z;       (* [comment removed for export] *)
  pa_str_append : Z;       (* [comment removed for export] *)
  pa_xsgetn : Z;           (* [comment removed for export] *)
  pa_uflow : Z;            (* [comment removed for export] *)
  pa_underflow : Z;        (* [comment removed for export] *)
  pa_ios_clear : Z;        (* [comment removed for export] *)
  pa_src_dtor : Z;         (* [comment removed for export] *)
  pa_istream_dtor : Z;     (* [comment removed for export] *)
  pa_ios_dtor : Z;         (* [comment removed for export] *)
  pa_iosbase_dtor : Z;     (* [comment removed for export] *)
  pa_reader_read : Z;      (* [comment removed for export] *)
  pa_vec_dtor : Z;         (* [comment removed for export] *)
  pa_opnew : Z;            (* [comment removed for export] *)
  pa_opdel : Z;            (* [comment removed for export] *)
  pa_opdel_sized : Z;      (* [comment removed for export] *)
  pa_memcpy : Z; pa_memmove : Z; pa_memset : Z;
  pa_guard_acquire : Z; pa_guard_release : Z;   (* [comment removed for export] *)
  pa_cxa_atexit : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_vp_visitor : Z;       (* [comment removed for export] *)
  pa_vp_parser : Z;        (* [comment removed for export] *)
  pa_vp_iss : Z;           (* [comment removed for export] *)
  pa_vp_strbuf : Z;        (* [comment removed for export] *)
  pa_vp_iss_ios : Z;       (* [comment removed for export] *)
  pa_vp_nullis : Z;        (* [comment removed for export] *)
  pa_vp_nullbuf : Z;       (* [comment removed for export] *)
  pa_vp_nullis_ios : Z;    (* [comment removed for export] *)
  pa_vp_opts : Z;          (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_errcat_guard : Z;     (* [comment removed for export] *)
  pa_errcat_obj : Z;       (* [comment removed for export] *)
  pa_errcat_dtor : Z;      (* [comment removed for export] *)
  pa_dso : Z;              (* [comment removed for export] *)
  pa_syscat_guard : Z;     (* [comment removed for export] *)
  pa_syscat_obj : Z;       (* [comment removed for export] *)
  pa_glocale : Z;          (* [comment removed for export] *)
  pa_classic_imp : Z;      (* [comment removed for export] *)
  pa_loc_foot : list (Z * Z);  (* [comment removed for export] *)
  pa_atexit : Z;           (* [comment removed for export] *)
  pa_need_locks : Z;       (* [comment removed for export] *)
  pa_locale_lock : Z;      (* [comment removed for export] *)
  pa_canary : Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_frame : Z;            (* [comment removed for export] *)
  pa_off_opts : Z;         (* [comment removed for export] *)
  pa_off_ec : Z;           (* [comment removed for export] *)
  pa_off_p : Z;            (* [comment removed for export] *)
  pa_off_v : Z;            (* [comment removed for export] *)
  pa_off_is : Z;           (* [comment removed for export] *)
  pa_off_s : Z;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  pa_rw_lo : Z;            (* [comment removed for export] *)
  pa_gp : Z;
  pa_tp : Z
}.

(* [comment removed for export] *)
Definition pm_foot (A : pm_addrs) : list (Z * Z) :=
  [(pa_errcat_guard A, pa_errcat_guard A + 2); (pa_syscat_guard A, pa_syscat_guard A + 2)]
  ++ pa_loc_foot A ++ [(pa_atexit A, pa_atexit A + 544)].
(* [comment removed for export] *)
Definition pm_initc (A : pm_addrs) : list (Z * Z) :=
  [(pa_need_locks A, pa_need_locks A + 1); (pa_locale_lock A, pa_locale_lock A + 4)].
