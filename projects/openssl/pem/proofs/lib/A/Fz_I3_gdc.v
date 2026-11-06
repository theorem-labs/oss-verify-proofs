(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_master1 Fz_I3_dctki Fz_G_context_init_w Fz_G_context_init Fz_G_default_context_do_init_ossl Fz_I3_gdcw Fz_I2_rcx Fz_I2_snm Fz_I2_namemap Fz_I2_htnew Fz_I2_ppisn Fz_G_kit2 Fz_M_zalloc Fz_M_locknew Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Th_mutex_init Fz_M_strdup Fz_W5_icb Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_OPENSSL_sk_new_null Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Th_cond Fz_M_aligned Fz_M_aligned_array Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_nmw Fz_I2_pdefns Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_I2_ppisn Fz_G_kit3 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition GDC_COST : Z := 1 + 1 + mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1 + mcost 16 + 1 + RCX_COST + mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1 + mcost 16 + 1 + mcost 104 + mcost 128 + mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1 + mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1 + mcost 80 + mcost 56 + 1 + mcost 56 + 1 + mcost 48 + 1 + mcost 104 + mcost 128 + mcost 104 + mcost 128 + mcost 56 + mcost 56 + NM_COST + mcost 104 + mcost 128 + mcost 16 + mcost 56 + mcost 16 + 1 + mcost 16 + mcost 8 + mcost 32 + mcost 40 + mcost 48 + mcost 88 + PPI_COST + mcost 56.
Lemma GDC_COST_nonneg : 0 <= GDC_COST.
Proof.
  unfold GDC_COST. pose proof RCX_COST_nonneg. pose proof NM_COST_nonneg. pose proof PPI_COST_nonneg.
  repeat match goal with |- context [mcost ?n] => lazymatch goal with _ : 0 <= mcost n |- _ => fail | _ => pose proof (wg_mcost_nonneg n) end end. lia.
Qed.

Section Gdc.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_DCDI : default_context_do_init_ossl_stmt RT.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)].
Hypothesis GO_dckey : GOBJ 0xb9f720 4.

Definition GDC_SITES : list (Z * Z) := [(SITE_default_context_do_init_ossl_1, e_default_context_do_init_ossl); (SITE_context_init_1, e_context_init); (SITE_context_init_2, e_context_init); (SITE_context_init_3, e_context_init); (SITE_context_init_4, e_context_init); (SITE_context_init_5, e_context_init); (SITE_context_init_6, e_context_init); (SITE_context_init_7, e_context_init); (SITE_context_init_8, e_context_init); (SITE_context_init_9, e_context_init); (SITE_context_init_10, e_context_init); (SITE_context_init_11, e_context_init); (SITE_context_init_12, e_context_init); (SITE_context_init_13, e_context_init); (SITE_context_init_14, e_context_init); (SITE_context_init_15, e_context_init); (SITE_context_init_16, e_context_init); (SITE_context_init_17, e_context_init); (SITE_context_init_18, e_context_init); (SITE_context_init_19, e_context_init); (SITE_context_init_20, e_context_init); (SITE_context_init_21, e_context_init); (SITE_context_init_22, e_context_init); (SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ossl_do_ex_data_init_1, e_ossl_do_ex_data_init); (SITE_ossl_do_ex_data_init_2, e_ossl_do_ex_data_init); (SITE_ossl_method_store_new_1, e_ossl_method_store_new); (SITE_ossl_method_store_new_2, e_ossl_method_store_new); (SITE_ossl_method_store_new_3, e_ossl_method_store_new); (SITE_ossl_method_store_new_4, e_ossl_method_store_new); (SITE_ossl_method_store_new_5, e_ossl_method_store_new); (SITE_ossl_method_store_new_6, e_ossl_method_store_new); (SITE_ossl_prov_conf_ctx_new_1, e_ossl_prov_conf_ctx_new); (SITE_ossl_prov_conf_ctx_new_2, e_ossl_prov_conf_ctx_new); (SITE_rcx_zalloc, e_rand_ctx_new); (SITE_rcx_strdup, e_rand_ctx_new); (SITE_rcx_locknew, e_rand_ctx_new); (SITE_sd_malloc, e_CRYPTO_strdup); (SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_4, e_ossl_decoder_cache_new); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new); (SITE_ossl_provider_store_new_1, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_3, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_4, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_5, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_8, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_9, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_10, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new); (SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_1, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_2, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_3, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_4, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_5, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_6, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_7, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_8, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_9, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_10, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_11, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_12, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_13, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_14, e_ossl_property_string_data_new); (SITE_snm_nm, e_stored_namemap_new); (SITE_nm_zalloc, e_namemap_new); (SITE_nm_locknew, e_namemap_new); (SITE_nm_htnew, e_namemap_new); (SITE_nm_sknew, e_namemap_new); (SITE_ht_zalloc1, e_ht_new); (SITE_ht_locknew, e_ht_new); (SITE_ht_zalloc2, e_ht_new); (SITE_ht_anl, e_ht_new); (SITE_ht_rcu, e_ht_new); (SITE_anl_aaa, e_anl); (SITE_aa_memalign, e_CRYPTO_aligned_alloc); (SITE_rcu_zalloc, e_rcu_lock_new); (SITE_rcu_calloc, e_rcu_lock_new); (SITE_pdefns_lhn, e_pdefns); (SITE_ossl_prov_drbg_nonce_ctx_new_1, e_ossl_prov_drbg_nonce_ctx_new); (SITE_ossl_prov_drbg_nonce_ctx_new_2, e_ossl_prov_drbg_nonce_ctx_new); (SITE_ossl_threads_ctx_new_1, e_ossl_threads_ctx_new); (SITE_ossl_threads_ctx_new_2, e_ossl_threads_ctx_new); (SITE_ossl_threads_ctx_new_3, e_ossl_threads_ctx_new); (SITE_ossl_crypto_mutex_new_1, e_ossl_crypto_mutex_new); (SITE_ossl_crypto_condvar_new_1, e_ossl_crypto_condvar_new); (0x20ab30, 0x20aacc); (0x20ab5c, 0x20aacc); (0x20ab74, 0x20aacc); (0x20c10c, 0x20c090); (0x20c1a0, 0x20c090); (0x20c1f4, 0x20c090); (0x20c208, 0x20c090); (0x20c284, 0x20c090); (0x20c29c, 0x20c090); (0x20c2e8, 0x20c090); (0x20c2f4, 0x20c090); (0x20c30c, 0x20c090); (0x20c328, 0x20c090); (0x20c490, 0x20c090); (0x20c4a8, 0x20c090); (0x20c4b0, 0x20c090); (0x20c220, 0x20c090); (0x1f6040, 0x1f6028); (0x201018, 0x200fc8); (0x2009a8, 0x200920); (0x1f6098, 0x1f6080); (0x1f606c, 0x1f6054); (0x1fbf98, 0x1fbf20); (0x1fab44, 0x1faa5c); (0x1fa6e0, 0x1fa5e0); (0x1fc00c, 0x1fbfec); (0x1fc024, 0x1fbfec); (0x200494, 0x2003c8); (0x2006e0, 0x2003c8); (0x1fa808, 0x1fa5e0); (0x1fc3b8, 0x1fc320); (SITE_ossl_load_builtin_compressions_1, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_2, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_3, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_4, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_5, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_6, e_ossl_load_builtin_compressions)].
Definition GDC_CALLS : list (Z * Z) := (ONCE_RET_INIT, e_default_context_do_init_ossl) :: [(SITE_default_context_do_init_ossl_1, e_context_init); (SITE_context_init_1, e_lock_new); (SITE_context_init_2, e_ossl_do_ex_data_init); (SITE_context_init_3, e_ossl_method_store_new); (SITE_context_init_4, e_ossl_prov_conf_ctx_new); (SITE_context_init_5, e_rand_ctx_new); (SITE_context_init_6, e_ossl_method_store_new); (SITE_context_init_7, e_ossl_decoder_cache_new); (SITE_context_init_8, e_ossl_method_store_new); (SITE_context_init_9, e_ossl_method_store_new); (SITE_context_init_10, e_ossl_provider_store_new); (SITE_context_init_11, e_ossl_property_string_data_new); (SITE_context_init_12, e_stored_namemap_new); (SITE_context_init_13, e_pdefns); (SITE_context_init_14, e_ossl_ctx_global_properties_new); (SITE_context_init_14, e_CRYPTO_zalloc); (SITE_context_init_15, e_ossl_bio_core_globals_new); (SITE_context_init_15, e_CRYPTO_zalloc); (SITE_context_init_16, e_ossl_prov_drbg_nonce_ctx_new); (SITE_context_init_17, e_ossl_self_test_set_callback_new); (SITE_context_init_17, e_CRYPTO_zalloc); (SITE_context_init_18, e_ossl_indicator_set_callback_new); (SITE_context_init_18, e_CRYPTO_zalloc); (SITE_context_init_19, e_ossl_threads_ctx_new); (SITE_context_init_20, e_ossl_child_prov_ctx_new); (SITE_context_init_20, e_CRYPTO_zalloc); (SITE_context_init_21, e_property_parse_init); (SITE_context_init_22, e_ossl_load_builtin_compressions); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ossl_do_ex_data_init_1, e_ossl_lib_ctx_get_ex_data_global); (SITE_ossl_do_ex_data_init_2, e_lock_new); (SITE_ossl_method_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_2, e_CRYPTO_calloc); (SITE_ossl_method_store_new_2, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_3, e_ossl_sa_new); (SITE_ossl_method_store_new_3, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_4, e_lock_new); (SITE_ossl_method_store_new_5, e_lock_new); (SITE_ossl_method_store_new_6, e_lock_new); (SITE_ossl_prov_conf_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_prov_conf_ctx_new_2, e_lock_new); (SITE_rcx_zalloc, e_CRYPTO_zalloc); (SITE_rcx_strdup, e_CRYPTO_strdup); (SITE_rcx_locknew, e_lock_new); (SITE_sd_malloc, e_CRYPTO_malloc); (SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc); (SITE_ossl_decoder_cache_new_2, e_lock_new); (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new); (SITE_ossl_decoder_cache_new_4, e_OPENSSL_LH_set_thunks); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc); (SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new); (SITE_ossl_provider_store_new_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_4, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_6, e_lock_new); (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_provider_store_new_8, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_10, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_11, e_lock_new); (SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc); (SITE_ossl_property_string_data_new_2, e_lock_new); (SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_4, e_OPENSSL_LH_set_thunks); (SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_6, e_OPENSSL_LH_set_thunks); (SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_8, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_property_string_data_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_property_string_data_new_10, e_OPENSSL_sk_set_thunks); (SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_12, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_property_string_data_new_13, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_property_string_data_new_14, e_OPENSSL_sk_set_thunks); (SITE_snm_nm, e_namemap_new); (SITE_nm_zalloc, e_CRYPTO_zalloc); (SITE_nm_locknew, e_lock_new); (SITE_nm_htnew, e_ht_new); (SITE_nm_sknew, e_OPENSSL_sk_new_null); (SITE_ht_zalloc1, e_CRYPTO_zalloc); (SITE_ht_locknew, e_lock_new); (SITE_ht_zalloc2, e_CRYPTO_zalloc); (SITE_ht_anl, e_anl); (SITE_ht_rcu, e_rcu_lock_new); (SITE_anl_aaa, e_CRYPTO_aligned_alloc_array); (SITE_anl_aaa, e_CRYPTO_aligned_alloc); (SITE_aa_memalign, e_posix_memalign); (SITE_rcu_zalloc, e_CRYPTO_zalloc); (SITE_rcu_calloc, e_CRYPTO_calloc); (SITE_rcu_calloc, e_CRYPTO_zalloc); (SITE_pdefns_lhn, e_OPENSSL_LH_new); (SITE_ossl_prov_drbg_nonce_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_prov_drbg_nonce_ctx_new_2, e_lock_new); (SITE_ossl_threads_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_threads_ctx_new_2, e_ossl_crypto_mutex_new); (SITE_ossl_threads_ctx_new_3, e_ossl_crypto_condvar_new); (SITE_ossl_crypto_mutex_new_1, e_CRYPTO_zalloc); (SITE_ossl_crypto_condvar_new_1, e_CRYPTO_zalloc); (0x20ab30, 0x20c068); (0x20ab5c, 0x20c6fc); (0x20ab74, 0x20c6fc); (0x20ab30, 0x20c090); (0x20c10c, 0x1a63bc); (0x20c1a0, 0x1f77d0); (0x20c1f4, 0x1f6028); (0x20c208, 0x200fc8); (0x20c284, 0x1f6080); (0x20c29c, 0x1f6054); (0x20c2e8, 0x200fc8); (0x20c2f4, 0x1ac568); (0x20c30c, 0x1fbf20); (0x20c328, 0x1c1920); (0x20c490, 0x1fb7f4); (0x20c4a8, 0x2003c8); (0x20c4b0, 0x201498); (0x20c220, 0x1f6080); (0x1f6040, 0x529908); (0x201018, 0x200920); (0x2009a8, 0x20c77c); (0x2009a8, 0x20bf48); (0x2009a8, 0x2000a0); (0x1f6098, 0x529df4); (0x1f606c, 0x529908); (0x1fbf98, 0x1c2fe4); (0x20c490, 0x1faa5c); (0x1fab44, 0x1fa5e0); (0x1fa6e0, 0x201580); (0x1fa6e0, 0x1fbfec); (0x1fc00c, 0x1fbf20); (0x1fc024, 0x1c1dbc); (0x200494, 0x200920); (0x2006e0, 0x1fbf20); (0x1fa808, 0x2016f0); (0x1fa808, 0x1fc320); (0x1fc3b8, 0x1c2fec); (0x20ab5c, 0x20c090); (0x20ab74, 0x20c090); (SITE_ossl_load_builtin_compressions_1, e_COMP_zlib); (SITE_ossl_load_builtin_compressions_2, e_OPENSSL_sk_new); (SITE_ossl_load_builtin_compressions_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_load_builtin_compressions_4, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_load_builtin_compressions_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_load_builtin_compressions_6, e_COMP_get_type)].
(* [comment removed for export] *)
Definition GDC_W (j : Z) : list (Z * Z) :=
  [(0xb9f560, 0xb9f561); (0xb9f580, 0xb9f590); (0xb9f628, 0xb9f6c0);
   (0xb9f720, 0xb9f720 + 4); (0xb9f740, 0xb9f740 + 4); (0xb9f760, 0xb9f760 + 4); (0xb9f780, 0xb9f780 + 4);
   (0xb9f7a0, 0xb9f7a4); (G_ALLOW_CUST, G_ALLOW_CUST + 1);
   (TP_A + -96, TP_A + -88); (KEYS + 8 * j, KEYS + 8 * j + 8); (NEXT_KEY, NEXT_KEY + 12)].
(* [comment removed for export] *)
Definition dc_blocks_ok (Σ Σ' : rts RT) (lk : Z) : Prop :=
  exists news : list (Z * Z), rt_live RT Σ' = news ++ rt_live RT Σ /\ Z.of_nat (length news) = 124
    /\ Forall (fun e => 0 < fst e /\ fst e mod 16 = 0 /\ fst e + snd e < USTACK_TOP /\ 0 < snd e) news /\ In (lk, 40) news.

Definition gdc_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (nk j : Z) (sh kold w r oldcb : word) (g1 : byte)
         (g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17
          g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od : word),
    tp = Z_to_bv 64 TP_A ->
    fdfs_only PMc -> mat_stable PMc ->
    ART RT Σ m -> mem_inv asegs m -> cl_env m lb canary ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 1232 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_gdc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ) GDC_SITES GDC_CALLS ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
    Z.of_nat (length (rt_live RT Σ)) + 124 <= LIVE_MAX ->
    Forall (fun blk : Z * Z => 0 < snd blk) (rt_live RT Σ) ->
    GDC_COST <= rt_credit RT Σ ->
    rw_cells asegs m 0xb9f740 [C4 z64] -> rw_cells asegs m 0xb9f780 [C4 z64] ->
    rw_cells asegs m 0xb9f720 [C4 kold] -> rw_cells asegs m 0xb9f760 [C4 r] ->
    rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 0 <= nk < 128 ->
    rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
    rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
    (j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0) ->
    0 < j -> ro_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] ->
    rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
    rw_cells asegs m 0xb9f560 [C1 g1] -> rw_cells asegs m 0xb9f7a0 [C4 g2] ->
    rw_cells asegs m 0xb9f580 [C8 g1_g2] -> rw_cells asegs m 0xb9f588 [C8 g1_g2_g2] ->
    rw_cells asegs m 0xb9f628 [C8 g1_g3] -> rw_cells asegs m 0xb9f630 [C8 g1_g4] -> rw_cells asegs m 0xb9f638 [C8 g1_g5] ->
    rw_cells asegs m 0xb9f640 [C8 g1_g6] -> rw_cells asegs m 0xb9f648 [C8 g1_g7] -> rw_cells asegs m 0xb9f650 [C8 g1_g8] ->
    rw_cells asegs m 0xb9f658 [C8 g1_g9] -> rw_cells asegs m 0xb9f660 [C8 g1_g10] -> rw_cells asegs m 0xb9f668 [C8 g1_g11] ->
    rw_cells asegs m 0xb9f670 [C8 g1_g12] -> rw_cells asegs m 0xb9f678 [C8 g1_g13] -> rw_cells asegs m 0xb9f680 [C8 g1_g14] ->
    rw_cells asegs m 0xb9f688 [C8 g1_g15] -> rw_cells asegs m 0xb9f690 [C8 g1_g16] -> rw_cells asegs m 0xb9f698 [C8 g1_g17] ->
    rw_cells asegs m 0xb9f6a0 [C8 g1_g18] -> rw_cells asegs m 0xb9f6a8 [C8 g1_g19] -> rw_cells asegs m 0xb9f6b0 [C8 g1_g20] ->
    rw_cells asegs m 0xb9f6b8 [C8 g1_g21] ->
    rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 0xb9f2a0 [C8 g1_g5_od] ->
    rw_cells asegs m 0xb9f2c0 [C4 (Z_to_bv 64 2)] -> rw_cells asegs m 0xb9f2e0 [C4 (Z_to_bv 64 1)] ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                           F fc e_gdc m)))
      (fun c => exists (Σ' : rts RT) (lk xd : Z),
         ASTA RT Σ' PMc
           (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0xb9f580) m' ms
              /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' 0xb9f560 [C1 (Z_to_bv 8 1)]
              /\ rw_cells asegs m' 0xb9f580 [C8 (Z_to_bv 64 lk)]
              /\ rw_cells asegs m' 0xb9f588 [C8 (Z_to_bv 64 xd)]
              /\ rw_cells asegs m' lk (mutex_cells z64 z64)
              /\ rw_cells asegs m' xd (mutex_cells z64 z64)
              /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)]
              /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)]
              /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
              /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)]
              /\ rw_cells asegs m' 0xb9f7a0 [C4 (Z_to_bv 64 1)]
              /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
              /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
              /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)]
              /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh])
           c
         /\ dc_blocks_ok Σ Σ' lk /\ dc_blocks_ok Σ Σ' xd /\ xd mod 16 = 0
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ - GDC_COST /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem gdc_cps : gdc_stmt.
Proof.
  unfold gdc_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo outer lb canary nk j sh kold w r oldcb g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10
    g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
    ThreadPtr PmFds PmStable RtAt0 InvAt0 EnvAt0 Callable Headroom CallerCtx CallerChain Graph FramesFree LiveFree
    LiveSized Budget KeyOnceIdle CtxOnceIdle KeyWord KeyOnceRet NextKeyAt NkRange KeyLockFree SlotJFree SlotNkWord
    SlotPick KeyAboveZero TsdSlotEmpty CleanupHead InitedAt CtxRetAt CtxLockAt CtxNextAt
    Ctx03 Ctx04 Ctx05 Ctx06 Ctx07 Ctx08 Ctx09 Ctx10 Ctx11 Ctx12 Ctx13 Ctx14 Ctx15 Ctx16 Ctx17 Ctx18 Ctx19 Ctx20 Ctx21
    RandFlagAt RandOdAt RandTwoAt RandOneAt
    Tgt cfg0 Begin Finish.
  clear CallerCtx CallerChain.
  destruct Callable as (StackAt0 & LoWindow & LoRoom & SpTop & SpAligned).
  pose proof (af_sp0_win RT AF Σ m RtAt0) as Sp0High.
  unfold RT_STACK in Headroom.
  assert (LoHigh : 0x10007fff8000 <= lo) by (unfold STACK_WIN in LoWindow; lia).
  assert (SpCap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in SpTop; lia).
  assert (JRange : 0 <= j < 128) by (destruct SlotPick as [(-> & _) | (-> & _)]; lia).
  destruct (af_client_consts RT AF Σ m RtAt0) as (_ & _ & _ & _ & Pristine0).
  pose proof (cl_env_ssp m lb canary Pristine0 EnvAt0) as Guard0.
  pose proof (wg_rw_ro _ _ _ (TSD Σ m RtAt0)) as TsdHome0.
  pose proof (gdc_w0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo nk j sh kold w r oldcb canary ThreadPtr StackAt0 LoHigh ltac:(lia) SpCap Pristine0
                KeyOnceIdle CtxOnceIdle KeyWord KeyOnceRet TsdHome0 NextKeyAt NkRange KeyLockFree SlotJFree SlotNkWord
                SlotPick Guard0 CleanupHead InvAt0) as ToOnce.
  cl_lift ToOnce Begin cfg1 AtOnce.
  destruct (ASTA_unpack RT Σ _ _ cfg1 AtOnce) as (st1 & ReachedOnce & AtDcdi). clear AtOnce.
  destruct ReachedOnce as (t0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & junk & m1 & -> & Wrote1 & Grow1 & InvAt1
    & GdcFrame1 & OnceLink1 & OnceRet1 & OnceFrame1 & CleanupAt1 & CtxOnceBusy1 & KeyOnceDone1 & KeyIdx1 & KeyRet1
    & NextKey1 & KeyLock1 & SlotJ1 & Guard1 & StackAt1).
  pose (KeyFp := [(0xb9f720, 0xb9f720 + 4); (0xb9f740, 0xb9f740 + 4); (0xb9f760, 0xb9f760 + 4); (0xb9f780, 0xb9f780 + 4);
                  (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)]).
  assert (Wrote1' : munch (KeyFp ++ [(bv_unsigned sp - 272, bv_unsigned sp)]) m m1).
  { intros x Away. apply Wrote1. unfold KeyFp in Away. cbn [outside app] in Away |- *. tauto. }
  assert (KeyFpStatic : forall x, ~ outside KeyFp x -> client_static x).
  { intros x Hit. apply client_static_intro. unfold KeyFp in Hit. cbn [outside] in Hit. lia. }
  assert (RtAt1 : ART RT Σ m1).
  { refine (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 272 KeyFp RtAt0 _ _ Wrote1' KeyFpStatic Grow1);
      unfold USTACK_TOP in *; lia. }
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 272 KeyFp RtAt0 ltac:(lia) ltac:(lia) Wrote1') as Kept1.
  assert (EnvAt1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary EnvAt0 Wrote1); cl_fp_lia).
  assert (TsdSlot1 : ro_cells asegs m1 (TSD_MAIN + 8 * j) [C8 z64]).
  { apply (wg_keep_static_ro _ _ _ _ m m1 _ _ TsdSlotEmpty Kept1). intros x Span. cbn [cells_size csize Nat.add] in Span.
    split; [apply client_static_intro; lia | unfold KeyFp; cbn [outside]; repeat split; lia]. }
  assert (SpLit1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) = bv_unsigned sp + -16 + -128)
    by (apply unsigned_lit; lia).
  assert (CallOk1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) lo).
  { unfold call_ok. rewrite SpLit1. refine (conj StackAt1 (conj LoWindow _)). unfold RT_STACK, USTACK_TOP in *. lia. }
  assert (Depth1 : lo + RT_STACK + 1088 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16 + -128)))
    by (rewrite SpLit1; unfold RT_STACK; lia).
  assert (OnceCtx : cg_ctx (rt_cg RT Σ) e_default_context_do_init_ossl (bv_unsigned (Z_to_bv 64 ONCE_RET_INIT) :: [])).
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia).
    cbn [cg_ctx cg_linked]. split; [| exact I].
    apply (proj2 Graph). unfold GDC_CALLS. left. reflexivity. }
  assert (FreshChain : uw_chain m1 (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) (Z_to_bv 64 0xb9f780) []).
  { cbn [uw_chain]. unfold fp_invalid. left. rewrite SpLit1, (unsigned_lit 0xb9f780) by lia. lia. }
  assert (CostSplit : GDC_COST = 46 + NM_COST + PPI_COST).
  { unfold GDC_COST, RCX_COST.
    repeat match goal with |- context [mcost ?n] => replace (mcost n) with 0 by reflexivity end.
    lia. }
  pose proof C_DCDI as Dcdi. unfold default_context_do_init_ossl_stmt in Dcdi.
  refine (Dcdi Σ PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 (bv_unsigned sp + -16 + -128)) gp tp t0' t1 t2
            (Z_to_bv 64 0xb9f780) (Z_to_bv 64 e_dcdi) a0' a1' a2' a3' a4' a5' a6' a7'
            (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m1 lo [] lb canary g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14
            g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
            PmFds PmStable ThreadPtr RtAt1 InvAt1 EnvAt1 CallOk1 Depth1 OnceCtx FreshChain _ FramesFree LiveFree LiveSized _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            Tgt cfg1 AtDcdi _).
  3-29: (eapply (wg_keep_static_nw _ _ _ _ m m1); [eassumption | exact Kept1 |];
         intros x Span; cbn [cells_size csize Nat.add] in Span; split;
         [apply client_static_intro; lia | unfold KeyFp; cbn [outside]; repeat split; lia]).
  - apply (cg_has_weaken _ _ _ _ _ Graph); vm_compute; reflexivity.
  - rewrite <- CostSplit. exact Budget.
  - intros cfg2 Back.
    destruct Back as (Σ1 & lk1 & xd2 & Back).
    repeat match type of Back with ex _ => destruct Back as (? & Back) end.
    destruct Back as (AtBack & Blocks & FramesSame & Sp0Same & CreditSpent & CgSame).
    destruct Blocks as (NEW & NewIs & LiveNow & NewCount & LockIn & NewShape).
    destruct (ASTA_unpack RT Σ1 _ _ cfg2 AtBack) as (st2 & Returned & AtRet). clear AtBack.
    destruct Returned as (m2 & j4 & j16 & j19 & RetShape & After2 & Kept2 & EnvAt2 & Inited2 & CtxRet2 & CtxLock2 & CtxGlobal2
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LockObj2 & GlobalObj2 & _).
    destruct RetShape as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite SpLit1 in After2, Kept2.
    destruct After2 as (RtAt2 & InvAt2 & StackAt2).
    rewrite (ret_pc_even ONCE_RET_INIT) in AtRet by (unfold ONCE_RET_INIT; lia).
    assert (Stack2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]
                     /\ rw_cells asegs m2 (bv_unsigned sp + -16 + -16) [C8 sp; C8 (Z_to_bv 64 SITE_gdc_once2)]
                     /\ rw_cells asegs m2 (bv_unsigned sp + -16 + -32) [CB 8 junk; C8 (Z_to_bv 64 RUN_ONCE_RET)]
                     /\ rw_cells asegs m2 (bv_unsigned sp + -16 + -128)
                          (once_full_cells 0xb9f780 oldcb canary s6 s5 s4 s3 s2 s1 (Z_to_bv 64 (bv_unsigned sp + -16)))).
    { refine (conj _ (conj _ (conj _ _))).
      all: eapply rw_cells_agree_nw; [eassumption |].
      all: apply (agree_of_pres_fp _ _ _ _ m1 m2 _ Kept2); intros here Span;
           cbn [cells_size csize Nat.add once_full_cells] in Span; split;
           [apply acl_stack; unfold USTACK_TOP in *; lia | cbn [outside]; unfold G_ALLOW_CUST; repeat split; lia]. }
    destruct Stack2 as (GdcFrame2 & OnceLink2 & OnceRet2 & OnceFrame2).
    assert (Static2 : rw_cells asegs m2 (TP_A + -96) [C8 (Z_to_bv 64 (bv_unsigned sp + -16 + -128))]
                      /\ rw_cells asegs m2 0xb9f780 [C4 (Z_to_bv 64 1)]
                      /\ rw_cells asegs m2 0xb9f740 [C4 (Z_to_bv 64 2)]
                      /\ rw_cells asegs m2 0xb9f720 [C4 (Z_to_bv 64 j)]
                      /\ rw_cells asegs m2 0xb9f760 [C4 (Z_to_bv 64 1)]
                      /\ rw_cells asegs m2 NEXT_KEY [C4 (Z_to_bv 64 j)]
                      /\ rw_cells asegs m2 KEY_LOCK [C4 z64; C4 z64; C4 sh]
                      /\ rw_cells asegs m2 (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]).
    { refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
      all: eapply (wg_keep_static_nw _ _ _ _ m1 m2); [eassumption | exact Kept2 |].
      all: intros here Span; cbn [cells_size csize Nat.add] in Span; split;
           [apply client_static_intro; lia | cbn [outside]; unfold G_ALLOW_CUST; repeat split; lia]. }
    destruct Static2 as (CleanupAt2 & CtxOnceBusy2 & KeyOnceDone2 & KeyIdx2 & KeyRet2 & NextKey2 & KeyLock2 & SlotJ2).
    assert (TsdSlot2 : ro_cells asegs m2 (TSD_MAIN + 8 * j) [C8 z64]).
    { apply (wg_keep_static_ro _ _ _ _ m1 m2 _ _ TsdSlot1 Kept2). intros here Span. cbn [cells_size csize Nat.add] in Span.
      split; [apply client_static_intro; lia | cbn [outside]; unfold G_ALLOW_CUST; repeat split; lia]. }
    destruct (af_client_consts RT AF Σ1 m2 RtAt2) as (_ & ShadowBase2 & _ & _ & Pristine2).
    pose proof (cl_env_ssp m2 _ canary Pristine2 EnvAt2) as Guard2.
    pose proof (wg_rw_ro _ _ _ (TSD Σ1 m2 RtAt2)) as TsdHome2.
    assert (KeyShadow2 : ro_cells asegs m2 (0xb9f720 / 8 + 2147450880) [C1 (Z_to_bv 8 4)])
      by exact (afp_gsh_byte RT GOBJ AFP Σ1 m2 0xb9f720 4 0xb9f720 RtAt2 GO_dckey ltac:(lia) ltac:(lia) eq_refl).
    pose proof (gdc_w1 sp gp tp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F1 fc1 m2
                  lo j 4 sh oldcb canary junk ThreadPtr JRange (or_intror eq_refl) StackAt2 LoHigh ltac:(lia) SpCap Pristine2
                  ShadowBase2 GdcFrame2 OnceLink2 OnceRet2 OnceFrame2 CleanupAt2 CtxOnceBusy2 CtxRet2 (wg_rw_ro _ _ _ KeyIdx2)
                  KeyShadow2 TsdHome2 TsdSlot2 Inited2 Guard2 InvAt2) as ToExit.
    cl_lift ToExit AtRet cfg3 AtExit.
    assert (LockLive : In (lk1, 40) (rt_live RT Σ1)) by (rewrite LiveNow; apply in_or_app; left; exact LockIn).
    assert (GlobalIn : In (xd2, 40) NEW) by (rewrite NewIs; repeat (first [left; reflexivity | right])).
    assert (GlobalLive : In (xd2, 40) (rt_live RT Σ1)) by (rewrite LiveNow; apply in_or_app; left; exact GlobalIn).
    pose proof (af_live_range RT AF Σ1 m2 lk1 40 RtAt2 LockLive) as LockSpan.
    pose proof (af_live_range RT AF Σ1 m2 xd2 40 RtAt2 GlobalLive) as GlobalSpan.
    rewrite Sp0Same in LockSpan, GlobalSpan. unfold SEGTOP_A in LockSpan, GlobalSpan.
    destruct (proj1 (Forall_forall _ _) NewShape _ GlobalIn) as (_ & XdAligned & _). cbn [fst] in XdAligned.
    apply Finish. exists Σ1, lk1, xd2.
    refine (conj _ (conj _ (conj _ (conj XdAligned (conj FramesSame (conj Sp0Same (conj _ CgSame))))))).
    + apply (ASTA_conseq RT Σ1 PMc _ _ cfg3 AtExit). intros st3 Exited.
      destruct Exited as (v1 & v2 & v3 & v4 & m3 & -> & Wrote3 & Grow3 & InvAt3 & CtxOnceDone3 & CleanupBack3 & Guard3 & StackAt3).
      exists m3.
      pose (ExitFp := [(0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)]).
      assert (Wrote3' : munch (ExitFp ++ [(bv_unsigned sp - 176, bv_unsigned sp)]) m2 m3).
      { intros here Away. apply Wrote3. unfold ExitFp in Away. cbn [outside app] in Away |- *. tauto. }
      assert (ExitFpStatic : forall x, ~ outside ExitFp x -> client_static x).
      { intros here Hit. apply client_static_intro. unfold ExitFp in Hit. cbn [outside] in Hit. lia. }
      assert (RtAt3 : ART RT Σ1 m3).
      { refine (cl_seg_ART RT AF Σ1 m2 m3 (bv_unsigned sp) 176 ExitFp RtAt2 _ _ Wrote3' ExitFpStatic Grow3);
          rewrite ?Sp0Same; unfold USTACK_TOP in *; lia. }
      pose proof (cl_seg_pres RT AF Σ1 m2 m3 (bv_unsigned sp) 176 ExitFp RtAt2 ltac:(rewrite Sp0Same; lia) ltac:(lia) Wrote3')
        as Kept3.
      assert (PresAll : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m3).
      { apply (pres_fp_trans _ _ _ _ m m2 m3); [apply (pres_fp_trans _ _ _ _ m m1 m2) |].
        - apply (pres_fp_sub _ _ _ _ _ _ _ _ m m1 Kept1). intros here Acl Away. split; [exact Acl |].
          unfold GDC_W in Away. unfold KeyFp. cbn [outside] in Away |- *. tauto.
        - apply (pres_fp_sub _ _ _ _ _ _ _ _ m1 m2 Kept2). intros here Acl Away. split.
          + apply (aclient_mono _ _ _ _ _ _ _ Acl); [tauto | tauto | lia].
          + unfold GDC_W in Away. cbn [outside] in Away |- *. tauto.
        - apply (pres_fp_sub _ _ _ _ _ _ _ _ m2 m3 Kept3). intros here Acl Away. split.
          + rewrite FramesSame. apply (aclient_mono _ _ _ _ _ _ _ Acl); [| tauto | lia].
            intros blk Was. rewrite LiveNow. apply in_or_app. right. exact Was.
          + unfold GDC_W in Away. unfold ExitFp. cbn [outside] in Away |- *. tauto. }
      assert (EnvAt3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary EnvAt2 Wrote3); cl_fp_lia).
      refine (conj _ (conj (conj RtAt3 (conj InvAt3 StackAt3)) (conj PresAll (conj EnvAt3 _)))).
      { exists u0, v1, u2, v2, v3, v4, b4, b5, b6, b7, u3, u4, u5, u6, F1, fc1. reflexivity. }
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))).
      all: first
        [ assumption
        | eapply (wg_keep_seg_nw _ m2 m3); [eassumption | exact Wrote3 |];
          intros here Span; cbn [cells_size csize Nat.add mutex_cells] in Span; cbn [outside]; unfold STACK_WIN in *;
          repeat split; lia ].
    + exists NEW. refine (conj LiveNow (conj _ (conj NewShape LockIn))). rewrite NewCount. reflexivity.
    + exists NEW. refine (conj LiveNow (conj _ (conj NewShape GlobalIn))). rewrite NewCount. reflexivity.
    + rewrite CreditSpent, CostSplit. reflexivity.
Qed.
End Gdc.
