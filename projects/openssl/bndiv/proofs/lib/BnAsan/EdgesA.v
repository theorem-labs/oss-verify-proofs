(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import UnwindA.
Open Scope Z_scope.

(* [comment removed for export] *)
Class BnEdges {UK : UnwindKit} : Prop := mkBnEdges {
  R_BN_bin2bn_1f32b0 : uk_ctx 2050412 [2045476]   (* [comment removed for export] *);
  R_BN_bin2bn_1f32d8 : uk_ctx 2050412 [2045516]   (* [comment removed for export] *);
  R_ERR_clear_error_1f32fc : uk_ctx 2067576 [2045552]   (* [comment removed for export] *);
  R_BN_div_1f3358 : uk_ctx 2421772 [2045644]   (* [comment removed for export] *);
  R_BN_mul_1f3410 : uk_ctx 2407100 [2045828]   (* [comment removed for export] *);
  R_BN_add_1f3424 : uk_ctx 2424292 [2045848]   (* [comment removed for export] *);
  E_bn_free_d_1f3b14 : uk_tail 2047480 2062540   (* [comment removed for export] *);
  E_bn_free_d_1f3b80 : uk_tail 2047480 2062212   (* [comment removed for export] *);
  E_bn_expand2_1f3e68 : uk_call 2048312 2048476 2102212   (* [comment removed for export] *);
  E_bn_expand2_1f3edc : uk_call 2048312 2048592 2047480   (* [comment removed for export] *);
  E_BN_copy_1f4178 : uk_call 2049076 2049260 2048312   (* [comment removed for export] *);
  E_bn_wexpand_1f4334 : uk_tail 2049632 2048312   (* [comment removed for export] *);
  E_BN_bin2bn_1f4620 : uk_tail 2050412 2050452   (* [comment removed for export] *);
  E_bin2bn_1f46b4 : uk_call 2050452 2050600 2061116   (* [comment removed for export] *);
  E_bin2bn_1f4850 : uk_call 2050452 2051012 2048312   (* [comment removed for export] *);
  E_CRYPTO_malloc_1f6f74 : uk_leaf 2060912 2061032   (* [comment removed for export] *);
  E_CRYPTO_zalloc_1f6fe8 : uk_call 2061116 2061148 2060912   (* [comment removed for export] *);
  E_CRYPTO_free_1f7454 : uk_leaf_tail 2062212   (* [comment removed for export] *);
  E_CRYPTO_clear_free_1f7608 : uk_leaf_tail 2062540   (* [comment removed for export] *);
  E_ERR_clear_error_1f8a90 : uk_call 2067576 2067972 2062212   (* [comment removed for export] *);
  E_ERR_clear_error_1f8ac0 : uk_call 2067576 2068020 2062212   (* [comment removed for export] *);
  E_CRYPTO_malloc_array_201050 : uk_tail 2102064 2060912   (* [comment removed for export] *);
  E_CRYPTO_calloc_2010e4 : uk_tail 2102212 2061116   (* [comment removed for export] *);
  E_bn_lshift_fixed_top_226528 : uk_call 2254876 2255004 2049632   (* [comment removed for export] *);
  E_bn_rshift_fixed_top_2268e4 : uk_call 2255832 2255960 2049632   (* [comment removed for export] *);
  E_BN_CTX_start_249b7c : uk_call 2399644 2399984 2102064   (* [comment removed for export] *);
  E_BN_CTX_start_249bd0 : uk_call 2399644 2400068 2062212   (* [comment removed for export] *);
  E_BN_CTX_get_24a0b4 : uk_call 2401032 2401320 2060912   (* [comment removed for export] *);
  E_BN_mul_24b768 : uk_call 2407100 2407132 2407172   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b828 : uk_call 2407172 2407324 2399644   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b83c : uk_call 2407172 2407344 2401032   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b85c : uk_call 2407172 2407376 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b90c : uk_call 2407172 2407552 2401032   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b940 : uk_call 2407172 2407604 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b950 : uk_call 2407172 2407620 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b9c8 : uk_call 2407172 2407740 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24ba44 : uk_call 2407172 2407864 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24ba54 : uk_call 2407172 2407880 2049632   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24bb30 : uk_call 2407172 2408100 2049076   (* [comment removed for export] *);
  E_BN_div_24f1b0 : uk_call 2421772 2422052 2422156   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f27c : uk_call 2422156 2422256 2399644   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f288 : uk_call 2422156 2422268 2401032   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f294 : uk_call 2422156 2422280 2401032   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2a0 : uk_call 2422156 2422292 2401032   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2ac : uk_call 2422156 2422304 2401032   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2bc : uk_call 2422156 2422320 2049076   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f3bc : uk_call 2422156 2422576 2254876   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f418 : uk_call 2422156 2422668 2049632   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f4e8 : uk_call 2422156 2422876 2049632   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f580 : uk_call 2422156 2423028 2049632   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f8b0 : uk_call 2422156 2423844 2255832   (* [comment removed for export] *);
  E_BN_add_24fb00 : uk_call 2424292 2424436 2424712   (* [comment removed for export] *);
  E_BN_add_24fb30 : uk_call 2424292 2424484 2425440   (* [comment removed for export] *);
  E_BN_uadd_24fcdc : uk_call 2424712 2424912 2049632   (* [comment removed for export] *);
  E_BN_usub_24ff74 : uk_call 2425440 2425576 2049632   (* [comment removed for export] *)
}.
