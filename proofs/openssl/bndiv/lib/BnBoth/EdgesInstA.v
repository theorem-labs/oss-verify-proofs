(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface RT_unwind_kit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UnwindA EdgesA.
Open Scope Z_scope.

#[export] Instance UK_A : UnwindKit :=
  mkUK site_ctx (fun f r g => call_edgeb f r g = true) (fun f g => tail_edgeb f g = true) (fun f r => leaf_edgeb f r = true) (fun f => leaf_tailb f = true)
       site_ctx_call site_ctx_tail site_ctx_leaf site_ctx_leaf_tail.

Lemma I_R_BN_bin2bn_1f32b0 : site_ctx 2030252 [2024852].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_bin2bn_1f32d8 : site_ctx 2030252 [2024912].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_ERR_clear_error_1f32fc : site_ctx 2048852 [2024948].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_div_1f3358 : site_ctx 2434228 [2025040].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_mul_1f3410 : site_ctx 2417908 [2025224].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_add_1f3424 : site_ctx 2437472 [2025244].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_E_bn_free_d_1f3b14 : tail_edgeb 2027080 2043028 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_free_d_1f3b80 : tail_edgeb 2027080 2042688 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_expand2_1f3e68 : call_edgeb 2027968 2028144 2084472 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_expand2_1f3edc : call_edgeb 2027968 2028284 2027080 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_copy_1f4178 : call_edgeb 2028800 2028996 2027968 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_wexpand_1f4334 : tail_edgeb 2029388 2027968 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_bin2bn_1f4620 : tail_edgeb 2030252 2030292 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bin2bn_1f46b4 : call_edgeb 2030292 2030404 2027708 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bin2bn_1f4850 : call_edgeb 2030292 2030792 2027968 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_malloc_1f6f74 : leaf_edgeb 2041372 2041492 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_zalloc_1f6fe8 : call_edgeb 2041576 2041608 2041372 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_free_1f7454 : leaf_tailb 2042688 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_clear_free_1f7608 : leaf_tailb 2043028 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_ERR_clear_error_1f8a90 : call_edgeb 2048852 2048936 2046760 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_ERR_clear_error_1f8ac0 : call_edgeb 2048852 2048936 2046760 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_malloc_array_201050 : tail_edgeb 2084324 2041372 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_calloc_2010e4 : tail_edgeb 2084472 2041576 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_lshift_fixed_top_226528 : call_edgeb 2247620 2247780 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_rshift_fixed_top_2268e4 : call_edgeb 2248864 2249012 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_start_249b7c : call_edgeb 2408120 2408476 2084324 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_start_249bd0 : call_edgeb 2408120 2408572 2042688 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_get_24a0b4 : call_edgeb 2409672 2409984 2041372 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_mul_24b768 : call_edgeb 2417908 2417940 2417980 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b828 : call_edgeb 2417980 2418168 2408120 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b83c : call_edgeb 2417980 2418188 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b85c : call_edgeb 2417980 2418232 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b90c : call_edgeb 2417980 2418444 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b940 : call_edgeb 2417980 2418484 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b950 : call_edgeb 2417980 2418500 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b9c8 : call_edgeb 2417980 2418636 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24ba44 : call_edgeb 2417980 2418772 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24ba54 : call_edgeb 2417980 2418788 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24bb30 : call_edgeb 2417980 2419032 2028800 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_div_24f1b0 : call_edgeb 2434228 2434568 2434676 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f27c : call_edgeb 2434676 2434776 2408120 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f288 : call_edgeb 2434676 2434788 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f294 : call_edgeb 2434676 2434800 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2a0 : call_edgeb 2434676 2434812 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2ac : call_edgeb 2434676 2434824 2409672 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2bc : call_edgeb 2434676 2434844 2028800 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f3bc : call_edgeb 2434676 2435176 2247620 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f418 : call_edgeb 2434676 2435292 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f4e8 : call_edgeb 2434676 2435780 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f580 : call_edgeb 2434676 2436012 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f8b0 : call_edgeb 2434676 2437028 2248864 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_add_24fb00 : call_edgeb 2437472 2437640 2437940 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_add_24fb30 : call_edgeb 2437472 2437692 2438900 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_uadd_24fcdc : call_edgeb 2437940 2438180 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_usub_24ff74 : call_edgeb 2438900 2439068 2029388 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_new_222654 : call_edgeb 2027708 2027760 2041576 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_err_clear_1f8720 : call_edgeb 2046760 2047020 2042688 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_err_clear_1f8824 : call_edgeb 2046760 2047280 2042688 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_err_clear_1f8864 : call_edgeb 2046760 2047344 2042688 = true.
Proof. vm_compute. reflexivity. Qed.

#[export] Instance BE_A : @BnEdges UK_A.
Proof. constructor.
  - exact I_R_BN_bin2bn_1f32b0.
  - exact I_R_BN_bin2bn_1f32d8.
  - exact I_R_ERR_clear_error_1f32fc.
  - exact I_R_BN_div_1f3358.
  - exact I_R_BN_mul_1f3410.
  - exact I_R_BN_add_1f3424.
  - exact I_E_bn_free_d_1f3b14.
  - exact I_E_bn_free_d_1f3b80.
  - exact I_E_bn_expand2_1f3e68.
  - exact I_E_bn_expand2_1f3edc.
  - exact I_E_BN_copy_1f4178.
  - exact I_E_bn_wexpand_1f4334.
  - exact I_E_BN_bin2bn_1f4620.
  - exact I_E_bin2bn_1f46b4.
  - exact I_E_bin2bn_1f4850.
  - exact I_E_CRYPTO_malloc_1f6f74.
  - exact I_E_CRYPTO_zalloc_1f6fe8.
  - exact I_E_CRYPTO_free_1f7454.
  - exact I_E_CRYPTO_clear_free_1f7608.
  - exact I_E_ERR_clear_error_1f8a90.
  - exact I_E_ERR_clear_error_1f8ac0.
  - exact I_E_CRYPTO_malloc_array_201050.
  - exact I_E_CRYPTO_calloc_2010e4.
  - exact I_E_bn_lshift_fixed_top_226528.
  - exact I_E_bn_rshift_fixed_top_2268e4.
  - exact I_E_BN_CTX_start_249b7c.
  - exact I_E_BN_CTX_start_249bd0.
  - exact I_E_BN_CTX_get_24a0b4.
  - exact I_E_BN_mul_24b768.
  - exact I_E_bn_mul_fixed_top_24b828.
  - exact I_E_bn_mul_fixed_top_24b83c.
  - exact I_E_bn_mul_fixed_top_24b85c.
  - exact I_E_bn_mul_fixed_top_24b90c.
  - exact I_E_bn_mul_fixed_top_24b940.
  - exact I_E_bn_mul_fixed_top_24b950.
  - exact I_E_bn_mul_fixed_top_24b9c8.
  - exact I_E_bn_mul_fixed_top_24ba44.
  - exact I_E_bn_mul_fixed_top_24ba54.
  - exact I_E_bn_mul_fixed_top_24bb30.
  - exact I_E_BN_div_24f1b0.
  - exact I_E_bn_div_fixed_top_24f27c.
  - exact I_E_bn_div_fixed_top_24f288.
  - exact I_E_bn_div_fixed_top_24f294.
  - exact I_E_bn_div_fixed_top_24f2a0.
  - exact I_E_bn_div_fixed_top_24f2ac.
  - exact I_E_bn_div_fixed_top_24f2bc.
  - exact I_E_bn_div_fixed_top_24f3bc.
  - exact I_E_bn_div_fixed_top_24f418.
  - exact I_E_bn_div_fixed_top_24f4e8.
  - exact I_E_bn_div_fixed_top_24f580.
  - exact I_E_bn_div_fixed_top_24f8b0.
  - exact I_E_BN_add_24fb00.
  - exact I_E_BN_add_24fb30.
  - exact I_E_BN_uadd_24fcdc.
  - exact I_E_BN_usub_24ff74.
  - exact I_E_BN_new_222654.
  - exact I_E_err_clear_1f8720.
  - exact I_E_err_clear_1f8824.
  - exact I_E_err_clear_1f8864.
Qed.
