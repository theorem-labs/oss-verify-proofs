(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_master1 Fz_I3_dctki Fz_G_context_init_w Fz_G_context_init Fz_G_default_context_do_init_ossl Fz_I3_gdcw Fz_I2_rcx Fz_I2_snm Fz_I2_namemap Fz_I2_htnew Fz_I2_ppisn Fz_G_kit2 Fz_M_zalloc Fz_M_locknew Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Th_mutex_init Fz_M_strdup Fz_W5_icb Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_OPENSSL_sk_new_null Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Th_cond Fz_M_aligned Fz_M_aligned_array Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_nmw Fz_I2_pdefns Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_I2_ppisn Fz_G_kit3 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions.
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
  [(0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8);
   (TP_A + -96, TP_A + -88)] ++ [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (0xb9f588, 0xb9f590); (0xb9f580, 0xb9f588); (0xb9f630, 0xb9f638); (0xb9f668, 0xb9f670); (0xb9f658, 0xb9f660); (0xb9f680, 0xb9f688); (0xb9f688, 0xb9f690); (0xb9f690, 0xb9f698); (0xb9f698, 0xb9f6a0); (0xb9f638, 0xb9f640); (0xb9f628, 0xb9f630); (0xb9f640, 0xb9f648); (0xb9f648, 0xb9f650); (0xb9f650, 0xb9f658); (0xb9f670, 0xb9f678); (0xb9f660, 0xb9f668); (0xb9f6a0, 0xb9f6a8); (0xb9f6a8, 0xb9f6b0); (0xb9f6b0, 0xb9f6b8); (0xb9f678, 0xb9f680); (0xb9f6b8, 0xb9f6c0); (0xb9f560, 0xb9f561); (0xb9f7a0, 0xb9f7a4)].
(* [comment removed for export] *)
Definition dc_blocks_ok (Σ Σ' : rts RT) (lk : Z) : Prop :=
  exists news : list (Z * Z), rt_live RT Σ' = news ++ rt_live RT Σ /\ Z.of_nat (length news) = 124
    /\ Forall (fun e => 0 < fst e /\ fst e mod 16 = 0 /\ fst e + snd e < USTACK_TOP /\ 0 < snd e) news /\ In (lk, 40) news.

Definition gdc_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (nk j : Z) (sh kold w r oldcb : word) (g1 : byte) (g2 : word) (g1_g2 : word) (g1_g3 : word) (g1_g4 : word) (g1_g5 : word) (g1_g6 : word) (g1_g7 : word) (g1_g8 : word) (g1_g9 : word) (g1_g10 : word) (g1_g11 : word) (g1_g12 : word) (g1_g13 : word) (g1_g14 : word) (g1_g15 : word) (g1_g16 : word) (g1_g17 : word) (g1_g18 : word) (g1_g19 : word) (g1_g20 : word) (g1_g21 : word) (g1_g2_g2 : word) (g1_g5_od : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x570 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_gdc (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) GDC_SITES GDC_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 124 <= LIVE_MAX -> GDC_COST <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m 0xb9f740 [C4 z64] -> rw_cells asegs m 0xb9f780 [C4 z64] -> rw_cells asegs m 0xb9f720 [C4 kold] -> rw_cells asegs m 0xb9f760 [C4 r] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 1 <= nk < 127 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] -> rw_cells asegs m 0xb9f5f0 [C8 z64] ->
  rw_cells asegs m 0xb9f560 [C1 g1] ->
  rw_cells asegs m 0xb9f7a0 [C4 g2] ->
  rw_cells asegs m 0xb9f580 [C8 g1_g2] ->
  rw_cells asegs m 0xb9f628 [C8 g1_g3] ->
  rw_cells asegs m 0xb9f630 [C8 g1_g4] ->
  rw_cells asegs m 0xb9f638 [C8 g1_g5] ->
  rw_cells asegs m 0xb9f640 [C8 g1_g6] ->
  rw_cells asegs m 0xb9f648 [C8 g1_g7] ->
  rw_cells asegs m 0xb9f650 [C8 g1_g8] ->
  rw_cells asegs m 0xb9f658 [C8 g1_g9] ->
  rw_cells asegs m 0xb9f660 [C8 g1_g10] ->
  rw_cells asegs m 0xb9f668 [C8 g1_g11] ->
  rw_cells asegs m 0xb9f670 [C8 g1_g12] ->
  rw_cells asegs m 0xb9f678 [C8 g1_g13] ->
  rw_cells asegs m 0xb9f680 [C8 g1_g14] ->
  rw_cells asegs m 0xb9f688 [C8 g1_g15] ->
  rw_cells asegs m 0xb9f690 [C8 g1_g16] ->
  rw_cells asegs m 0xb9f698 [C8 g1_g17] ->
  rw_cells asegs m 0xb9f6a0 [C8 g1_g18] ->
  rw_cells asegs m 0xb9f6a8 [C8 g1_g19] ->
  rw_cells asegs m 0xb9f6b0 [C8 g1_g20] ->
  rw_cells asegs m 0xb9f6b8 [C8 g1_g21] ->
  rw_cells asegs m 0xb9f588 [C8 g1_g2_g2] ->
  rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xb9f2a0 [C8 g1_g5_od] ->
  rw_cells asegs m 0xb9f2c0 [C4 (Z_to_bv 64 2)] ->
  rw_cells asegs m 0xb9f2e0 [C4 (Z_to_bv 64 1)] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_gdc m)))
    (fun c => exists (Σ' : rts RT) (lk : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0xb9f580) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
           /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 z64] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' 0xb9f5f0 [C8 z64]
           /\ In (lk, 40) (rt_live RT Σ') /\ rw_cells asegs m' 0xb9f588 [C8 (Z_to_bv 64 lk)] /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' 0xb9f7a0 [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' 0xb9f560 [C1 (Z_to_bv 8 1)]
           /\ rw_cells asegs m' 0xb9f200 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' 0xb9f2c0 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' 0xb9f2e0 [C4 (Z_to_bv 64 1)]) c
       /\ dc_blocks_ok Σ Σ' lk /\ 1 <= j < 128 /\ lk mod 16 = 0
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - GDC_COST /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem gdc_cps : gdc_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary nk j sh kold w r oldcb g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr POS0 ENV O1 O2 KC RC NK HNK KL KJ PROBE CASE TSDJ CBC IP12 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19 X20 X21 X22 X23 X24 X25 X26.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 304 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp2 := usp + -16 + -128).
  assert (EU2 : bv_unsigned (Z_to_bv 64 usp2) = usp2) by (apply unsigned_lit; unfold usp2, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  assert (HJ : 1 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [lia | rewrite Z.mod_small by lia; lia]).
  pose proof (TSD Σ m ART0) as TC0.
  (* [comment removed for export] *)
  pose proof (gdc_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo nk j sh kold w r oldcb canary
                eq_refl ST ltac:(lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(lia) UT O1 O2 KC RC (wg_rw_ro _ _ _ TC0) NK ltac:(lia) KL KJ PROBE CASE
                (cl_env_ssp m lb canary UT ENV) CBC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (x0 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & junk & m1 & -> & MU1 & WM1 & MI1 & FR1 & REC1 & RR1 & OFC1 & CBP1 & O2_1 & O1_1 & KC1 & RC1 & NK1 & KL1 & KJ1 & SSP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, REC1, RR1, OFC1, CBP1, ST1, Hc1'. fold usp2 in OFC1, CBP1, ST1, Hc1'.
  assert (MU1' : munch ([(0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] ++ [(usp - 304, usp)]) m m1) by (eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside app]; intros; lia).
  assert (CSW : forall x, ~ outside [(0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] x -> client_static x).
  { intros x Hx. apply client_static_intro. clear - Hx HJ. cbn [outside] in Hx. lia. }
  pose proof (cl_seg_ART RT AF Σ m m1 usp 304 _ ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1' CSW WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 304 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) MU1') as PR1.
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> 0xb6c780 <= a -> (a + Z.of_nat (cells_size cs) <= 0xb9f720 \/ (0xb9f724 <= a /\ a + Z.of_nat (cells_size cs) <= 0xb9f740) \/ (0xb9f784 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e00) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5780)) -> rw_cells asegs m1 a cs).
  { intros a cs H R0 R. apply (wg_keep_seg _ m m1 _ _ H MU1 WM1). intros x Hx. cbn [app outside]. clear - Hx R0 R HJ NUM HSTK. unfold RT_STACK in *. lia. }
  pose proof (STAT1 _ _ X0 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X0_1.
  pose proof (STAT1 _ _ X1 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X1_1.
  pose proof (STAT1 _ _ X2 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X2_1.
  pose proof (STAT1 _ _ X3 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X3_1.
  pose proof (STAT1 _ _ X4 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X4_1.
  pose proof (STAT1 _ _ X5 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X5_1.
  pose proof (STAT1 _ _ X6 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X6_1.
  pose proof (STAT1 _ _ X7 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X7_1.
  pose proof (STAT1 _ _ X8 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X8_1.
  pose proof (STAT1 _ _ X9 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X9_1.
  pose proof (STAT1 _ _ X10 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X10_1.
  pose proof (STAT1 _ _ X11 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X11_1.
  pose proof (STAT1 _ _ X12 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X12_1.
  pose proof (STAT1 _ _ X13 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X13_1.
  pose proof (STAT1 _ _ X14 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X14_1.
  pose proof (STAT1 _ _ X15 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X15_1.
  pose proof (STAT1 _ _ X16 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X16_1.
  pose proof (STAT1 _ _ X17 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X17_1.
  pose proof (STAT1 _ _ X18 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X18_1.
  pose proof (STAT1 _ _ X19 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X19_1.
  pose proof (STAT1 _ _ X20 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X20_1.
  pose proof (STAT1 _ _ X21 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X21_1.
  pose proof (STAT1 _ _ X22 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X22_1.
  pose proof (STAT1 _ _ X23 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X23_1.
  pose proof (STAT1 _ _ X24 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X24_1.
  pose proof (STAT1 _ _ X25 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X25_1.
  pose proof (STAT1 _ _ X26 ltac:(clear; lia) ltac:(cbn; clear; lia)) as X26_1.
  pose proof (STAT1 _ _ TSDJ ltac:(clear - HJ; lia) ltac:(cbn; clear - HJ; lia)) as TSDJ1. pose proof (STAT1 _ _ IP12 ltac:(clear; lia) ltac:(cbn; clear; lia)) as IP12_1.
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(first [solve [clear - NUM HSTK HJ; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia])) as ENV1.
  (* [comment removed for export] *)
  apply (C_DCDI Σ PMc (Z_to_bv 64 ONCE_RET_INIT) (Z_to_bv 64 usp2) gp (Z_to_bv 64 TP_A) x0 t1 t2 (Z_to_bv 64 0xb9f780) (Z_to_bv 64 e_dcdi) y0 y1 y2 y3 y4 y5 y6 y7
           (Z_to_bv 64 0) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 2) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo [] lb canary g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
           FDO MST eq_refl ART1 MI1).
  { unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [exact LOW|]. split; [clear - HSTK; unfold usp2, RT_STACK in *; lia|]. split; [clear - NUM; unfold usp2, USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA. unfold usp2. Z.div_mod_to_equations. lia. }
  { rewrite EU2. clear - HSTK. unfold usp2, RT_STACK in *. lia. }
  { rewrite (unsigned_lit ONCE_RET_INIT) by (unfold ONCE_RET_INIT; lia). split; [| exact I]. apply (proj2 CGH). left. reflexivity. }
  { cbn [uw_chain fp_invalid]. left. rewrite (unsigned_lit 0xb9f780), EU2 by lia. clear - HSTK NUM. unfold usp2, RT_STACK in *. lia. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. }
  { exact Hlen. }
  { unfold GDC_COST in Hcr. exact Hcr. }
  { exact POS0. }
  { exact ENV1. }
  { exact X0_1. }
  { exact X1_1. }
  { exact X2_1. }
  { exact X3_1. }
  { exact X4_1. }
  { exact X5_1. }
  { exact X6_1. }
  { exact X7_1. }
  { exact X8_1. }
  { exact X9_1. }
  { exact X10_1. }
  { exact X11_1. }
  { exact X12_1. }
  { exact X13_1. }
  { exact X14_1. }
  { exact X15_1. }
  { exact X16_1. }
  { exact X17_1. }
  { exact X18_1. }
  { exact X19_1. }
  { exact X20_1. }
  { exact X21_1. }
  { exact X22_1. }
  { exact X23_1. }
  { exact X24_1. }
  { exact X25_1. }
  { exact X26_1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q18 & q19 & q20 & q21 & q22 & q23 & q24 & q25 & q26 & q27 & q28 & q29 & q30 & q31 & q32 & q33 & q34 & q35 & q36 & q37 & q38 & q39 & q40 & q41 & q42 & q43 & q44 & q45 & q46 & q47 & q48 & q49 & q50 & q51 & q52 & q53 & q54 & q55 & q56 & q57 & q58 & q59 & q60 & q61 & q62 & q63 & q64 & q65 & q66 & q67 & q68 & q69 & q70 & q71 & q72 & q73 & q74 & q75 & q76 & q77 & q78 & q79 & q80 & q81 & q82 & q83 & q84 & q85 & q86 & q87 & q88 & q89 & q90 & q91 & q92 & q93 & q94 & q95 & q96 & q97 & q98 & q99 & q100 & q101 & q102 & q103 & q104 & q105 & q106 & q107 & q108 & q109 & q110 & q111 & q112 & q113 & q114 & q115 & q116 & q117 & q118 & q119 & q120 & q121 & q122 & q123 & q124 & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0_q1 & P16_q1 & PU_q1 & P0_q2 & P16_q2 & PU_q2 & P0_q3 & P16_q3 & PU_q3 & P0_q4 & P16_q4 & PU_q4 & P0_q5 & P16_q5 & PU_q5 & P0_q6 & P16_q6 & PU_q6 & P0_q7 & P16_q7 & PU_q7 & P0_q8 & P16_q8 & PU_q8 & P0_q9 & P16_q9 & PU_q9 & P0_q10 & P16_q10 & PU_q10 & P0_q11 & P16_q11 & PU_q11 & P0_q12 & P16_q12 & PU_q12 & P0_q13 & P16_q13 & PU_q13 & P0_q14 & P16_q14 & PU_q14 & P0_q15 & P16_q15 & PU_q15 & P0_q16 & P16_q16 & PU_q16 & P0_q17 & P16_q17 & PU_q17 & P0_q18 & P16_q18 & PU_q18 & P0_q19 & P16_q19 & PU_q19 & P0_q20 & P16_q20 & PU_q20 & P0_q21 & P16_q21 & PU_q21 & P0_q22 & P16_q22 & PU_q22 & P0_q23 & P16_q23 & PU_q23 & P0_q24 & P16_q24 & PU_q24 & P0_q25 & P16_q25 & PU_q25 & P0_q26 & P16_q26 & PU_q26 & P0_q27 & P16_q27 & PU_q27 & P0_q28 & P16_q28 & PU_q28 & P0_q29 & P16_q29 & PU_q29 & P0_q30 & P16_q30 & PU_q30 & P0_q31 & P16_q31 & PU_q31 & P0_q32 & P16_q32 & PU_q32 & P0_q33 & P16_q33 & PU_q33 & P0_q34 & P16_q34 & PU_q34 & P0_q35 & P16_q35 & PU_q35 & P0_q36 & P16_q36 & PU_q36 & P0_q37 & P16_q37 & PU_q37 & P0_q38 & P16_q38 & PU_q38 & P0_q39 & P16_q39 & PU_q39 & P0_q40 & P16_q40 & PU_q40 & P0_q41 & P16_q41 & PU_q41 & P0_q42 & P16_q42 & PU_q42 & P0_q43 & P16_q43 & PU_q43 & P0_q44 & P16_q44 & PU_q44 & P0_q45 & P16_q45 & PU_q45 & P0_q46 & P16_q46 & PU_q46 & P0_q47 & P16_q47 & PU_q47 & P0_q48 & P16_q48 & PU_q48 & P0_q49 & P16_q49 & PU_q49 & P0_q50 & P16_q50 & PU_q50 & P0_q51 & P16_q51 & PU_q51 & P0_q52 & P16_q52 & PU_q52 & P0_q53 & P16_q53 & PU_q53 & P0_q54 & P16_q54 & PU_q54 & P0_q55 & P16_q55 & PU_q55 & P0_q56 & P16_q56 & PU_q56 & P0_q57 & P16_q57 & PU_q57 & P0_q58 & P16_q58 & PU_q58 & P0_q59 & P16_q59 & PU_q59 & P0_q60 & P16_q60 & PU_q60 & P0_q61 & P16_q61 & PU_q61 & P0_q62 & P16_q62 & PU_q62 & P0_q63 & P16_q63 & PU_q63 & P0_q64 & P16_q64 & PU_q64 & P0_q65 & P16_q65 & PU_q65 & P0_q66 & P16_q66 & PU_q66 & P0_q67 & P16_q67 & PU_q67 & P0_q68 & P16_q68 & PU_q68 & P0_q69 & P16_q69 & PU_q69 & P0_q70 & P16_q70 & PU_q70 & P0_q71 & P16_q71 & PU_q71 & P0_q72 & P16_q72 & PU_q72 & P0_q73 & P16_q73 & PU_q73 & P0_q74 & P16_q74 & PU_q74 & P0_q75 & P16_q75 & PU_q75 & P0_q76 & P16_q76 & PU_q76 & P0_q77 & P16_q77 & PU_q77 & P0_q78 & P16_q78 & PU_q78 & P0_q79 & P16_q79 & PU_q79 & P0_q80 & P16_q80 & PU_q80 & P0_q81 & P16_q81 & PU_q81 & P0_q82 & P16_q82 & PU_q82 & P0_q83 & P16_q83 & PU_q83 & P0_q84 & P16_q84 & PU_q84 & P0_q85 & P16_q85 & PU_q85 & P0_q86 & P16_q86 & PU_q86 & P0_q87 & P16_q87 & PU_q87 & P0_q88 & P16_q88 & PU_q88 & P0_q89 & P16_q89 & PU_q89 & P0_q90 & P16_q90 & PU_q90 & P0_q91 & P16_q91 & PU_q91 & P0_q92 & P16_q92 & PU_q92 & P0_q93 & P16_q93 & PU_q93 & P0_q94 & P16_q94 & PU_q94 & P0_q95 & P16_q95 & PU_q95 & P0_q96 & P16_q96 & PU_q96 & P0_q97 & P16_q97 & PU_q97 & P0_q98 & P16_q98 & PU_q98 & P0_q99 & P16_q99 & PU_q99 & P0_q100 & P16_q100 & PU_q100 & P0_q101 & P16_q101 & PU_q101 & P0_q102 & P16_q102 & PU_q102 & P0_q103 & P16_q103 & PU_q103 & P0_q104 & P16_q104 & PU_q104 & P0_q105 & P16_q105 & PU_q105 & P0_q106 & P16_q106 & PU_q106 & P0_q107 & P16_q107 & PU_q107 & P0_q108 & P16_q108 & PU_q108 & P0_q109 & P16_q109 & PU_q109 & P0_q110 & P16_q110 & PU_q110 & P0_q111 & P16_q111 & PU_q111 & P0_q112 & P16_q112 & PU_q112 & P0_q113 & P16_q113 & PU_q113 & P0_q114 & P16_q114 & PU_q114 & P0_q115 & P16_q115 & PU_q115 & P0_q116 & P16_q116 & PU_q116 & P0_q117 & P16_q117 & PU_q117 & P0_q118 & P16_q118 & PU_q118 & P0_q119 & P16_q119 & PU_q119 & P0_q120 & P16_q120 & PU_q120 & P0_q121 & P16_q121 & PU_q121 & P0_q122 & P16_q122 & PU_q122 & P0_q123 & P16_q123 & PU_q123 & P0_q124 & P16_q124 & PU_q124 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & WRlk & ACClk & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & MX2 & D26 & D27 & D28 & D29) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even ONCE_RET_INIT) in Hc2' by (unfold ONCE_RET_INIT; lia).
  (* [comment removed for export] *)
  assert (STK2 : forall a cs, rw_cells asegs m1 a cs -> usp2 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree_nw asegs m1 m2 _ _ H). intros x Hx. apply PRES2; [left; clear - H1 H2 Hx; lia|]. cbn [app outside]. unfold G_ALLOW_CUST. clear - H1 Hx NUM HSTK. unfold usp2, RT_STACK in *. repeat (split; [lia|]). exact I. }
  assert (STA2 : forall a cs, rw_cells asegs m1 a cs -> 0xb9f700 <= a -> a + Z.of_nat (cells_size cs) <= 0xbc57d0 -> (a + Z.of_nat (cells_size cs) <= 0xb9f7a0 \/ (0xb9f7c1 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc41b8 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc5298) \/ 0xbc52a0 <= a) -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree_nw asegs m1 m2 _ _ H). intros x Hx. apply PRES2; [right; left; apply client_static_intro; clear - H1 H2 H3 Hx; lia|]. cbn [app outside]. unfold G_ALLOW_CUST. clear - H1 H2 H3 Hx. repeat (split; [lia|]). exact I. }
  pose proof (STK2 _ _ FR1 ltac:(clear; unfold usp2; lia) ltac:(cbn; clear - NUM; unfold USTACK_TOP in *; lia)) as FR2.
  pose proof (STK2 _ _ REC1 ltac:(clear; unfold usp2; lia) ltac:(cbn; clear - NUM; unfold USTACK_TOP in *; lia)) as REC2.
  pose proof (STK2 _ _ RR1 ltac:(clear; unfold usp2; lia) ltac:(cbn; clear - NUM; unfold USTACK_TOP in *; lia)) as RR2.
  pose proof (STK2 _ _ OFC1 ltac:(clear; unfold usp2; lia) ltac:(unfold once_full_cells; cbn; clear - NUM; unfold usp2, USTACK_TOP in *; lia)) as OFC2.
  pose proof (STA2 _ _ CBP1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as CBP2.
  pose proof (STA2 _ _ O2_1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as O2_2.
  pose proof (STA2 _ _ O1_1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as O1_2.
  pose proof (STA2 _ _ KC1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as KC2.
  pose proof (STA2 _ _ RC1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as RC2.
  pose proof (STA2 _ _ NK1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as NK2.
  pose proof (STA2 _ _ KL1 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as KL2.
  pose proof (STA2 _ _ KJ1 ltac:(clear - HJ; lia) ltac:(cbn; clear - HJ; lia) ltac:(cbn; clear - HJ; lia)) as KJ2.
  pose proof (STA2 _ _ TSDJ1 ltac:(clear - HJ; lia) ltac:(cbn; clear - HJ; lia) ltac:(cbn; clear - HJ; lia)) as TSDJ2.
  assert (IP12_2 : rw_cells asegs m2 0xb9f5f0 [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ IP12_1). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES2; [right; left; apply client_static_intro; clear - Hx; lia|]. cbn [app outside]. unfold G_ALLOW_CUST. clear - Hx. repeat (split; [lia|]). exact I. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2). unfold g_shadow_memory_dynamic_address in SHC2.
  pose proof (cl_env_ssp m2 _ canary UT2 ENV2) as SSP2.
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 0xb9f720 4 0xb9f720 ART2 GO_dckey ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity)) as KSH2.
  pose proof (TSD Σ1 m2 ART2) as TC2.
  (* [comment removed for export] *)
  pose proof (gdc_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F2 fc2 m2 lo j _ sh oldcb canary junk
                eq_refl ltac:(clear - HJ; lia) ltac:(right; reflexivity) ST2 ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) UT2 SHC2 FR2 REC2 RR2 OFC2 CBP2 O2_2 D2
                (wg_rw_ro _ _ _ KC2) KSH2 (wg_rw_ro _ _ _ TC2) (wg_rw_ro _ _ _ TSDJ2) D3 SSP2 MI2) as W1.
  fold usp in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (t1' & a1' & a2' & a3' & m3 & -> & MU3 & WM3 & MI3 & O2_3 & CBP3 & SSP3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3'.
  (* [comment removed for export] *)
  assert (INlk : In (q2, 40) (rt_live RT Σ1)) by (rewrite LV1; do 122 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 q2 40 ART2 INlk) as (_ & LKLO & _). rewrite SP1 in LKLO. pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 q2 40 ART2 INlk ltac:(clear; lia)) as LKH.
  assert (MU3' : munch ([(0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] ++ [(usp - 304, usp)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 304 [(0xb9f780, 0xb9f780 + 4); (TP_A + -96, TP_A + -88)] ART2 ltac:(rewrite SP1; clear - NUM; lia) ltac:(clear - NUM; lia) MU3'); [| exact WM3].
    intros x Hx. left. apply client_static_intro. cbn [outside] in Hx. clear - Hx. lia. }
  assert (STA3 : forall a cs, rw_cells asegs m2 a cs -> 0x10000 <= a -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> (a + Z.of_nat (cells_size cs) <= 0xb9f780 \/ (0xb9f784 <= a /\ a + Z.of_nat (cells_size cs) <= TP_A + -96) \/ TP_A + -88 <= a) -> rw_cells asegs m3 a cs).
  { intros a cs H H1 H2 H3. apply (rw_cells_agree_nw asegs m2 m3 _ _ H). intros x Hx. apply MU3. cbn [app outside]. clear - H1 H2 H3 Hx NUM HSTK. unfold RT_STACK in *. lia. }
  apply Hk. exists Σ1, q2.
  split; [| split; [| split; [exact HJ | split; [exact P16_q2 | split; [exact FRS1 | split; [exact SP1 | split; [unfold GDC_COST; exact CR1 | exact CG1]]]]]]].
  2: { exists [(q124, 56); (q123, 24); (q122, 18); (q121, 24); (q120, 32); (q119, 19); (q118, 24); (q117, 25); (q116, 24); (q115, 48); (q114, 21); (q113, 24); (q112, 22); (q111, 24); (q110, 20); (q109, 24); (q108, 23); (q107, 24); (q106, 24); (q105, 88); (q104, 48); (q103, 40); (q102, 32); (q101, 8); (q100, 16); (q99, 40); (q98, 16); (q97, 56); (q96, 16); (q95, 128); (q94, 104); (q93, 56); (q92, 16); (q91, 264); (q90, 32768); (q89, 24); (q88, 40); (q87, 96); (q86, 40); (q85, 40); (q84, 56); (q83, 56); (q82, 128); (q81, 104); (q80, 128); (q79, 104); (q78, 40); (q77, 48); (q76, 40); (q75, 56); (q74, 40); (q73, 56); (q72, 80); (q71, 40); (q70, 40); (q69, 40); (q68, 32); (q67, 40); (q66, 40); (q65, 32); (q64, 40); (q63, 40); (q62, 32); (q61, 40); (q60, 40); (q59, 32); (q58, 384); (q57, 24); (q56, 40); (q55, 40); (q54, 40); (q53, 32); (q52, 40); (q51, 40); (q50, 32); (q49, 40); (q48, 40); (q47, 32); (q46, 40); (q45, 40); (q44, 32); (q43, 384); (q42, 24); (q41, 128); (q40, 104); (q39, 40); (q38, 16); (q37, 40); (q36, 40); (q35, 40); (q34, 32); (q33, 40); (q32, 40); (q31, 32); (q30, 40); (q29, 40); (q28, 32); (q27, 40); (q26, 40); (q25, 32); (q24, 384); (q23, 24); (q22, 40); (q21, 5); (q20, 88); (q19, 40); (q18, 16); (q17, 40); (q16, 40); (q15, 40); (q14, 32); (q13, 40); (q12, 40); (q11, 32); (q10, 40); (q9, 40); (q8, 32); (q7, 40); (q6, 40); (q5, 32); (q4, 384); (q3, 24); (q2, 40); (q1, 40)]. split; [rewrite LV1; reflexivity|]. split; [reflexivity|].
       split; [repeat (apply Forall_cons; [cbn [fst snd]; split; [assumption | split; [assumption | split; [assumption | clear; lia]]] |]); apply Forall_nil|]. do 122 right. left. reflexivity. }
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, t1', u2, a1', a2', a3', b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | exact ST3]]|].
  split.
  { intros a Ha Ho.
    assert (HoD : outside [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (0xb9f588, 0xb9f590); (0xb9f580, 0xb9f588); (0xb9f630, 0xb9f638); (0xb9f668, 0xb9f670); (0xb9f658, 0xb9f660); (0xb9f680, 0xb9f688); (0xb9f688, 0xb9f690); (0xb9f690, 0xb9f698); (0xb9f698, 0xb9f6a0); (0xb9f638, 0xb9f640); (0xb9f628, 0xb9f630); (0xb9f640, 0xb9f648); (0xb9f648, 0xb9f650); (0xb9f650, 0xb9f658); (0xb9f670, 0xb9f678); (0xb9f660, 0xb9f668); (0xb9f6a0, 0xb9f6a8); (0xb9f6a8, 0xb9f6b0); (0xb9f6b0, 0xb9f6b8); (0xb9f678, 0xb9f680); (0xb9f6b8, 0xb9f6c0); (0xb9f560, 0xb9f561); (0xb9f7a0, 0xb9f7a4)] (bv_unsigned a)) by (clear - Ho; unfold GDC_W in Ho; cbn [outside app] in Ho |- *; tauto).
    assert (Ho0 : outside [(0xb9f740, 0xb9f740 + 4); (0xb9f780, 0xb9f780 + 4); (0xb9f720, 0xb9f720 + 4); (0xb9f760, 0xb9f760 + 4); (NEXT_KEY, NEXT_KEY + 12); (KEYS + 8 * j, KEYS + 8 * j + 8); (TP_A + -96, TP_A + -88)] (bv_unsigned a)) by (clear - Ho; unfold GDC_W in Ho; cbn [outside app] in Ho |- *; tauto).
    pose proof (cl_split RT AF Σ m usp 304 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as SPL.
    rewrite (MU3 a ltac:(clear - Ho0 SPL; cbn [outside] in Ho0 |- *; lia)).
    assert (A2 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp2 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; unfold usp2; lia]).
    rewrite (PRES2 a A2 HoD).
    exact (PR1 a Ha Ho0). }
  split; [exact (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(first [solve [clear - NUM HSTK; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia]))|].
  split; [exact (STA3 _ _ O1_2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact O2_3|].
  split; [exact (STA3 _ _ KC2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ RC2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|].
  split; [exact (STA3 _ _ NK2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ KL2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ KJ2 ltac:(clear - HJ; lia) ltac:(cbn; clear - HJ; lia) ltac:(cbn; clear - HJ; lia))|].
  split; [exact (STA3 _ _ TSDJ2 ltac:(clear - HJ; lia) ltac:(cbn; clear - HJ; lia) ltac:(cbn; clear - HJ; lia))|]. split; [exact CBP3|]. split; [exact (STA3 _ _ IP12_2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|].
  split; [exact INlk|]. split; [exact (STA3 _ _ D24 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|].
  split.
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ MX2). intros x Hx. unfold mutex_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply MU3. cbn [app outside]. clear - Hx LKLO LKH LOW HSTK. unfold RT_STACK in *. lia. }
  split; [exact (STA3 _ _ D2 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D3 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|].
  split; [exact (STA3 _ _ D26 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D28 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) | exact (STA3 _ _ D29 ltac:(clear; lia) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia))].
Qed.
End Gdc.
