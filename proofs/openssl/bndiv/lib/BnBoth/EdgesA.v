(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UnwindA.
Open Scope Z_scope.

(* [comment removed for export] *)
Class BnEdges {UK : UnwindKit} : Prop := mkBnEdges {
  R_BN_bin2bn_1f32b0 : uk_ctx 2030252 [2024852]   (* [comment removed for export] *);
  R_BN_bin2bn_1f32d8 : uk_ctx 2030252 [2024912]   (* [comment removed for export] *);
  R_ERR_clear_error_1f32fc : uk_ctx 2048852 [2024948]   (* [comment removed for export] *);
  R_BN_div_1f3358 : uk_ctx 2434228 [2025040]   (* [comment removed for export] *);
  R_BN_mul_1f3410 : uk_ctx 2417908 [2025224]   (* [comment removed for export] *);
  R_BN_add_1f3424 : uk_ctx 2437472 [2025244]   (* [comment removed for export] *);
  E_bn_free_d_1f3b14 : uk_tail 2027080 2043028   (* [comment removed for export] *);
  E_bn_free_d_1f3b80 : uk_tail 2027080 2042688   (* [comment removed for export] *);
  E_bn_expand2_1f3e68 : uk_call 2027968 2028144 2084472   (* [comment removed for export] *);
  E_bn_expand2_1f3edc : uk_call 2027968 2028284 2027080   (* [comment removed for export] *);
  E_BN_copy_1f4178 : uk_call 2028800 2028996 2027968   (* [comment removed for export] *);
  E_bn_wexpand_1f4334 : uk_tail 2029388 2027968   (* [comment removed for export] *);
  E_BN_bin2bn_1f4620 : uk_tail 2030252 2030292   (* [comment removed for export] *);
  E_bin2bn_1f46b4 : uk_call 2030292 2030404 2027708   (* [comment removed for export] *);
  E_bin2bn_1f4850 : uk_call 2030292 2030792 2027968   (* [comment removed for export] *);
  E_CRYPTO_malloc_1f6f74 : uk_leaf 2041372 2041492   (* [comment removed for export] *);
  E_CRYPTO_zalloc_1f6fe8 : uk_call 2041576 2041608 2041372   (* [comment removed for export] *);
  E_CRYPTO_free_1f7454 : uk_leaf_tail 2042688   (* [comment removed for export] *);
  E_CRYPTO_clear_free_1f7608 : uk_leaf_tail 2043028   (* [comment removed for export] *);
  E_ERR_clear_error_1f8a90 : uk_call 2048852 2048936 2046760   (* [comment removed for export] *);
  E_ERR_clear_error_1f8ac0 : uk_call 2048852 2048936 2046760   (* [comment removed for export] *);
  E_CRYPTO_malloc_array_201050 : uk_tail 2084324 2041372   (* [comment removed for export] *);
  E_CRYPTO_calloc_2010e4 : uk_tail 2084472 2041576   (* [comment removed for export] *);
  E_bn_lshift_fixed_top_226528 : uk_call 2247620 2247780 2029388   (* [comment removed for export] *);
  E_bn_rshift_fixed_top_2268e4 : uk_call 2248864 2249012 2029388   (* [comment removed for export] *);
  E_BN_CTX_start_249b7c : uk_call 2408120 2408476 2084324   (* [comment removed for export] *);
  E_BN_CTX_start_249bd0 : uk_call 2408120 2408572 2042688   (* [comment removed for export] *);
  E_BN_CTX_get_24a0b4 : uk_call 2409672 2409984 2041372   (* [comment removed for export] *);
  E_BN_mul_24b768 : uk_call 2417908 2417940 2417980   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b828 : uk_call 2417980 2418168 2408120   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b83c : uk_call 2417980 2418188 2409672   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b85c : uk_call 2417980 2418232 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b90c : uk_call 2417980 2418444 2409672   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b940 : uk_call 2417980 2418484 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b950 : uk_call 2417980 2418500 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24b9c8 : uk_call 2417980 2418636 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24ba44 : uk_call 2417980 2418772 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24ba54 : uk_call 2417980 2418788 2029388   (* [comment removed for export] *);
  E_bn_mul_fixed_top_24bb30 : uk_call 2417980 2419032 2028800   (* [comment removed for export] *);
  E_BN_div_24f1b0 : uk_call 2434228 2434568 2434676   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f27c : uk_call 2434676 2434776 2408120   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f288 : uk_call 2434676 2434788 2409672   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f294 : uk_call 2434676 2434800 2409672   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2a0 : uk_call 2434676 2434812 2409672   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2ac : uk_call 2434676 2434824 2409672   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f2bc : uk_call 2434676 2434844 2028800   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f3bc : uk_call 2434676 2435176 2247620   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f418 : uk_call 2434676 2435292 2029388   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f4e8 : uk_call 2434676 2435780 2029388   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f580 : uk_call 2434676 2436012 2029388   (* [comment removed for export] *);
  E_bn_div_fixed_top_24f8b0 : uk_call 2434676 2437028 2248864   (* [comment removed for export] *);
  E_BN_add_24fb00 : uk_call 2437472 2437640 2437940   (* [comment removed for export] *);
  E_BN_add_24fb30 : uk_call 2437472 2437692 2438900   (* [comment removed for export] *);
  E_BN_uadd_24fcdc : uk_call 2437940 2438180 2029388   (* [comment removed for export] *);
  E_BN_usub_24ff74 : uk_call 2438900 2439068 2029388   (* [comment removed for export] *);
  E_BN_new_222654 : uk_call 2027708 2027760 2041576;
  E_err_clear_1f8720 : uk_call 2046760 2047020 2042688;
  E_err_clear_1f8824 : uk_call 2046760 2047280 2042688;
  E_err_clear_1f8864 : uk_call 2046760 2047344 2042688
}.
