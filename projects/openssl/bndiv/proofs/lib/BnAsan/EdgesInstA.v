(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Import ListNotations.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import RT_iface RT_unwind_kit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import UnwindA EdgesA.
Open Scope Z_scope.

#[export] Instance UK_A : UnwindKit :=
  mkUK site_ctx (fun f r g => call_edgeb f r g = true) (fun f g => tail_edgeb f g = true) (fun f r => leaf_edgeb f r = true) (fun f => leaf_tailb f = true)
       site_ctx_call site_ctx_tail site_ctx_leaf site_ctx_leaf_tail.

Lemma I_R_BN_bin2bn_1f32b0 : site_ctx 2050412 [2045476].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_bin2bn_1f32d8 : site_ctx 2050412 [2045516].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_ERR_clear_error_1f32fc : site_ctx 2067576 [2045552].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_div_1f3358 : site_ctx 2421772 [2045644].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_mul_1f3410 : site_ctx 2407100 [2045828].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_R_BN_add_1f3424 : site_ctx 2424292 [2045848].
Proof. apply site_ctx_root. vm_compute. reflexivity. Qed.
Lemma I_E_bn_free_d_1f3b14 : tail_edgeb 2047480 2062540 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_free_d_1f3b80 : tail_edgeb 2047480 2062212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_expand2_1f3e68 : call_edgeb 2048312 2048476 2102212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_expand2_1f3edc : call_edgeb 2048312 2048592 2047480 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_copy_1f4178 : call_edgeb 2049076 2049260 2048312 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_wexpand_1f4334 : tail_edgeb 2049632 2048312 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_bin2bn_1f4620 : tail_edgeb 2050412 2050452 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bin2bn_1f46b4 : call_edgeb 2050452 2050600 2061116 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bin2bn_1f4850 : call_edgeb 2050452 2051012 2048312 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_malloc_1f6f74 : leaf_edgeb 2060912 2061032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_zalloc_1f6fe8 : call_edgeb 2061116 2061148 2060912 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_free_1f7454 : leaf_tailb 2062212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_clear_free_1f7608 : leaf_tailb 2062540 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_ERR_clear_error_1f8a90 : call_edgeb 2067576 2067972 2062212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_ERR_clear_error_1f8ac0 : call_edgeb 2067576 2068020 2062212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_malloc_array_201050 : tail_edgeb 2102064 2060912 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_CRYPTO_calloc_2010e4 : tail_edgeb 2102212 2061116 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_lshift_fixed_top_226528 : call_edgeb 2254876 2255004 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_rshift_fixed_top_2268e4 : call_edgeb 2255832 2255960 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_start_249b7c : call_edgeb 2399644 2399984 2102064 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_start_249bd0 : call_edgeb 2399644 2400068 2062212 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_CTX_get_24a0b4 : call_edgeb 2401032 2401320 2060912 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_mul_24b768 : call_edgeb 2407100 2407132 2407172 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b828 : call_edgeb 2407172 2407324 2399644 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b83c : call_edgeb 2407172 2407344 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b85c : call_edgeb 2407172 2407376 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b90c : call_edgeb 2407172 2407552 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b940 : call_edgeb 2407172 2407604 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b950 : call_edgeb 2407172 2407620 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24b9c8 : call_edgeb 2407172 2407740 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24ba44 : call_edgeb 2407172 2407864 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24ba54 : call_edgeb 2407172 2407880 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_mul_fixed_top_24bb30 : call_edgeb 2407172 2408100 2049076 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_div_24f1b0 : call_edgeb 2421772 2422052 2422156 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f27c : call_edgeb 2422156 2422256 2399644 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f288 : call_edgeb 2422156 2422268 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f294 : call_edgeb 2422156 2422280 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2a0 : call_edgeb 2422156 2422292 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2ac : call_edgeb 2422156 2422304 2401032 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f2bc : call_edgeb 2422156 2422320 2049076 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f3bc : call_edgeb 2422156 2422576 2254876 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f418 : call_edgeb 2422156 2422668 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f4e8 : call_edgeb 2422156 2422876 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f580 : call_edgeb 2422156 2423028 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_bn_div_fixed_top_24f8b0 : call_edgeb 2422156 2423844 2255832 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_add_24fb00 : call_edgeb 2424292 2424436 2424712 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_add_24fb30 : call_edgeb 2424292 2424484 2425440 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_uadd_24fcdc : call_edgeb 2424712 2424912 2049632 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma I_E_BN_usub_24ff74 : call_edgeb 2425440 2425576 2049632 = true.
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
Qed.
