(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNL.
Record pn_addrs : Type := PNA {
  pn_reader_ctor : Z;   (* [comment removed for export] *)
  pn_reader_dtor : Z;   (* [comment removed for export] *)
  pn_reader_read : Z;   (* [comment removed for export] *)
  pn_reset : Z;   (* [comment removed for export] *)
  pn_parse : Z;   (* [comment removed for export] *)
  pn_begin_document : Z;
  pn_end_document : Z;
  pn_begin_array : Z;
  pn_end_array : Z;
  pn_read_e_name : Z;
  pn_read_cstring : Z;   (* [comment removed for export] *)
  pn_read_string : Z;
  pn_read_value : Z;   (* [comment removed for export] *)
  pn_read_span_v : Z;   (* [comment removed for export] *)
  pn_srd_read_v : Z;   (* [comment removed for export] *)
  pn_vu8_resize : Z;
  pn_vu8_append : Z;   (* [comment removed for export] *)
  pn_vu8_dtor : Z;   (* [comment removed for export] *)
  pn_vu8_recommend : Z;   (* [comment removed for export] *)
  pn_sbu8_ctor : Z;   (* [comment removed for export] *)
  pn_sbu8_construct : Z;   (* [comment removed for export] *)
  pn_vu8_swap_out : Z;   (* [comment removed for export] *)
  pn_sbu8_dtor : Z;   (* [comment removed for export] *)
  pn_vec_alloc : Z;   (* [comment removed for export] *)
  pn_splitbuf_dtor : Z;
  pn_vec_dtor : Z;   (* [comment removed for export] *)
  pn_esp_mii : Z;   (* [comment removed for export] *)
  pn_esp_mis : Z;   (* [comment removed for export] *)
  pn_sb_ctor : Z;   (* [comment removed for export] *)
  pn_swap_out : Z;   (* [comment removed for export] *)
  pn_dec128 : Z;
  pn_from_int : Z;
  pn_hex_pairs : Z;   (* [comment removed for export] *)
  pn_str_push_back : Z;   (* [comment removed for export] *)
  pn_str_cstr : Z;   (* [comment removed for export] *)
  pn_str_dtor : Z;   (* [comment removed for export] *)
  pn_strlen : Z;   (* [comment removed for export] *)
  pn_vbs_tag : Z;   (* [comment removed for export] *)
  pn_vbs_ext : Z;
  pn_strlen_icpt : Z;   (* [comment removed for export] *)
  pn_wrap_strlen : Z;   (* [comment removed for export] *)
  pn_wrap_cxa_atexit : Z;   (* [comment removed for export] *)
  pn_inf_guard : Z;   (* [comment removed for export] *)
  pn_inf_obj : Z;   (* [comment removed for export] *)
  pn_inf_lit : Z;   (* [comment removed for export] *)
  pn_nan_guard : Z;   (* [comment removed for export] *)
  pn_nan_obj : Z;
  pn_nan_lit : Z;
  pn_str_dtor_slot : Z;   (* [comment removed for export] *)
  pn_drv_call : Z;   (* [comment removed for export] *)
  pn_drv_guard : Z   (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition pn_d128_foot (N : pn_addrs) : list (Z * Z) :=
  [(pn_inf_guard N, pn_inf_guard N + 8); (pn_inf_obj N, pn_inf_obj N + 24); (pn_nan_guard N, pn_nan_guard N + 8); (pn_nan_obj N, pn_nan_obj N + 24)].
End PNL.
