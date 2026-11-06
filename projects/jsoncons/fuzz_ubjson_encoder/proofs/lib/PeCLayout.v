(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Record pe_addrs : Type := PEA {
  (* [comment removed for export] *)
  pe_vt : Z;                 (* [comment removed for export] *)
  pe_off_begin_obj : Z;      (* [comment removed for export] *)
  pe_off_begin_obj_len : Z;
  pe_off_end_obj : Z;
  pe_off_begin_arr : Z;
  pe_off_begin_arr_len : Z;
  pe_off_end_arr : Z;
  pe_off_key : Z;
  pe_off_null : Z;
  pe_off_bool : Z;
  pe_off_string : Z;
  pe_off_uint64 : Z;
  pe_off_int64 : Z;
  pe_off_double : Z;
  pe_off_flush : Z;
  pe_begin_obj : Z;          (* [comment removed for export] *)
  pe_begin_obj_len : Z;      (* [comment removed for export] *)
  pe_end_obj : Z;
  pe_begin_arr : Z;
  pe_begin_arr_len : Z;      (* [comment removed for export] *)
  pe_end_arr : Z;
  pe_key : Z;
  pe_null : Z;
  pe_bool : Z;
  pe_string : Z;
  pe_uint64 : Z;
  pe_int64 : Z;
  pe_double : Z;
  pe_flush : Z;              (* [comment removed for export] *)
  (* [comment removed for export] *)
  pe_put_length : Z;         (* [comment removed for export] *)
  pe_push_back : Z;          (* [comment removed for export] *)
  pe_evec_alloc : Z;         (* [comment removed for export] *)
  pe_evec_sbdtor : Z;        (* [comment removed for export] *)
  pe_validate_enc : Z;       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pe_off_sink : Z;           (* [comment removed for export] *)
  pe_frame : Z;              (* [comment removed for export] *)
  (* [comment removed for export] *)
  pe_drv_call : Z;           (* [comment removed for export] *)
  pe_drv_guard : Z           (* [comment removed for export] *)
}.
