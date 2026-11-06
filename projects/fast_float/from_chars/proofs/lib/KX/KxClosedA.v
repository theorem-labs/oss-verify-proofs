(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_small_mul_stmt A_parse_mantissa_stmt
  A_negative_digit_comp_d_stmt A_dcf_d_stmt A_dcf_f_stmt A_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_D1_closed A_dcf_d A_dcf_f A_parse_mantissa A_small_mul
  A_negative_digit_comp_d A_negative_digit_comp_f A_smalloc4 A_rt_tls A_rt_m2s A_set_shadow A_musl_memset.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxLMe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_long_mul_closed : long_mul_stmt := KxLMe.long_mul_fx.
Definition A_set_shadow_f5_closed : set_shadow_f5_stmt := A_set_shadow.set_shadow_f5_spec A_musl_memset.memset_spec.
Definition A_smalloc4_closed : smalloc4_stmt := A_smalloc4.smalloc4_spec A_rt_tls.tls_chain_spec A_rt_m2s.m2s_spec.
Definition A_asan_memset_closed : asan_memset_stmt := A_D1_closed.A_asan_memset_closed.
Definition A_parse_mantissa_closed : parse_mantissa_stmt := A_parse_mantissa.parse_mantissa_spec A_small_mul.small_mul_spec.
Definition A_pos_dc_d_closed := A_D1_closed.A_pos_dc_d_closed A_long_mul_closed.
Definition A_pos_dc_f_closed := A_D1_closed.A_pos_dc_f_closed A_long_mul_closed.
Definition A_neg_dc_d_closed :=
  A_negative_digit_comp_d.negative_digit_comp_d_spec A_smalloc4_closed A_asan_memset_closed
    (A_D1_closed.A_pow5_closed A_long_mul_closed) A_D1_closed.A_shl_closed A_set_shadow_f5_closed.
Definition A_neg_dc_f_closed :=
  A_negative_digit_comp_f.negative_digit_comp_f_spec A_smalloc4_closed A_asan_memset_closed
    (A_D1_closed.A_pow5_closed A_long_mul_closed) A_D1_closed.A_shl_closed A_set_shadow_f5_closed.
Definition A_dcf_d_closed : dcf_d_stmt :=
  A_dcf_d.dcf_d_spec A_asan_memset_closed A_parse_mantissa_closed A_pos_dc_d_closed A_neg_dc_d_closed.
Definition A_dcf_f_closed : dcf_f_stmt :=
  A_dcf_f.dcf_f_spec A_asan_memset_closed A_parse_mantissa_closed A_pos_dc_f_closed A_neg_dc_f_closed.
