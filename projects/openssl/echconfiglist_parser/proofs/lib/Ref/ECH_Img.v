(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_LLVMFuzzerTestOneInput : Z := 0xdddb0.   (* [comment removed for export] *)
Definition P_FuzzerTestOneInput : Z := 0xdddbc.       (* [comment removed for export] *)
Definition P_parse_one : Z := 0xdde84.                (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_CRYPTO_strndup : Z := 0xddfdc.           (* [comment removed for export] *)
Definition P_CRYPTO_memdup : Z := 0xde0cc.            (* [comment removed for export] *)
Definition P_CRYPTO_malloc : Z := 0xde954.            (* [comment removed for export] *)
Definition P_CRYPTO_zalloc : Z := 0xdea24.            (* [comment removed for export] *)
Definition P_CRYPTO_realloc : Z := 0xdebd4.           (* [comment removed for export] *)
Definition P_CRYPTO_free : Z := 0xdecec.              (* [comment removed for export] *)
Definition P_CRYPTO_malloc_array : Z := 0xe3cb8.      (* [comment removed for export] *)
Definition P_CRYPTO_calloc : Z := 0xe3d4c.            (* [comment removed for export] *)
Definition P_CRYPTO_realloc_array : Z := 0xe3e90.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_ERR_new : Z := 0xdeef0.                  (* [comment removed for export] *)
Definition P_ERR_set_debug : Z := 0xdf000.            (* [comment removed for export] *)
Definition P_ERR_set_error : Z := 0xdf154.            (* [comment removed for export] *)
Definition P_ERR_vset_error : Z := 0xdf194.           (* [comment removed for export] *)
Definition P_ERR_clear_error : Z := 0xdf7f8.          (* [comment removed for export] *)
Definition P_ossl_err_get_state_int : Z := 0xdf8e4.   (* [comment removed for export] *)
Definition P_OSSL_ERR_STATE_new : Z := 0x26beb4.      (* [comment removed for export] *)
Definition P_ossl_init_thread_start : Z := 0xe29fc.   (* [comment removed for export] *)
Definition P_init_thread_push_handlers : Z := 0xe2ab4. (* [comment removed for export] *)
Definition P_OPENSSL_init_crypto : Z := 0xea7e4.
(* [comment removed for export] *)
Definition P_CRYPTO_THREAD_read_lock : Z := 0xe1188.
Definition P_CRYPTO_THREAD_write_lock : Z := 0xe11b4.
Definition P_CRYPTO_THREAD_unlock : Z := 0xe11e0.
Definition P_CRYPTO_THREAD_run_once : Z := 0xe1258.
Definition P_CRYPTO_THREAD_init_local : Z := 0xe1284.
Definition P_CRYPTO_THREAD_get_local : Z := 0xe12b0.
Definition P_CRYPTO_THREAD_set_local : Z := 0xe12d8.
Definition P_CRYPTO_THREAD_get_local_ex : Z := 0xe156c.
Definition P_CRYPTO_THREAD_set_local_ex : Z := 0xe1674.
Definition P_ossl_sa_new : Z := 0x10cbf8.
Definition P_ossl_sa_get : Z := 0x10ce4c.
Definition P_ossl_sa_set : Z := 0x10cee8.
(* [comment removed for export] *)
Definition P_get_default_context : Z := 0xe1ff8.
Definition P_ossl_lib_ctx_get_ex_data_global : Z := 0xe2210.   (* [comment removed for export] *)
Definition P_ossl_lib_ctx_get_concrete : Z := 0xe18c0.
Definition P_get_and_lock : Z := 0xe5368.
Definition P_ossl_crypto_new_ex_data_ex : Z := 0xe5650.
Definition P_CRYPTO_new_ex_data : Z := 0xe586c.
Definition P_CRYPTO_free_ex_data : Z := 0xe5be4.
(* [comment removed for export] *)
Definition P_OPENSSL_sk_new_null : Z := 0xe2fdc.
Definition P_OPENSSL_sk_new : Z := 0xe30d0.
Definition P_sk_reserve : Z := 0xe3120.
Definition P_OPENSSL_sk_free : Z := 0xe3320.
Definition P_OPENSSL_sk_set_thunks : Z := 0xe3380.
Definition P_OPENSSL_sk_set_cmp_thunks : Z := 0xe33a8.
Definition P_OPENSSL_sk_set_copy_thunks : Z := 0xe33d0.
Definition P_OPENSSL_sk_insert : Z := 0xe33f8.
Definition P_OPENSSL_sk_push : Z := 0xe3970.
Definition P_OPENSSL_sk_pop_free : Z := 0xe3a0c.
Definition P_OPENSSL_sk_num : Z := 0xe3acc.
Definition P_OPENSSL_sk_value : Z := 0xe3afc.
(* [comment removed for export] *)
Definition P_BIO_new_ex : Z := 0xff4b8.
Definition P_BIO_new : Z := 0xff5cc.
Definition P_BIO_free : Z := 0xff5f4.
Definition P_BIO_free_int : Z := 0xff61c.
Definition P_BIO_set_data : Z := 0xff724.
Definition P_BIO_get_data : Z := 0xff748.
Definition P_BIO_set_init : Z := 0xff76c.
Definition P_BIO_clear_flags : Z := 0xff7e8.
Definition P_BIO_test_flags : Z := 0xff818.
Definition P_BIO_set_flags : Z := 0xff840.
Definition P_BIO_ctrl : Z := 0xff86c.
Definition P_BIO_read : Z := 0xff9d8.
Definition P_bio_read_intern : Z := 0xffa44.
Definition P_BIO_read_ex : Z := 0xffc28.
Definition P_BIO_eof : Z := 0x100330.
Definition P_BIO_push : Z := 0x100540.
Definition P_BIO_next : Z := 0x10061c.
Definition P_BIO_free_all : Z := 0x100644.
Definition P_BIO_copy_next_retry : Z := 0x100694.
Definition P_bread_conv : Z := 0x1008c0.
Definition P_BUF_MEM_new : Z := 0x108f88.
Definition P_BUF_MEM_free : Z := 0x109000.
Definition P_BIO_f_base64 : Z := 0x26d7b4.
(* [comment removed for export] *)
Definition P_BIO_new_mem_buf : Z := 0x1d55a8.
Definition P_mem_read : Z := 0x1d57bc.
Definition P_mem_ctrl : Z := 0x1d5a00.
Definition P_mem_new : Z := 0x1d5c70.              (* [comment removed for export] *)
Definition P_mem_init : Z := 0x1d5ddc.
Definition P_mem_write : Z := 0x1d5678.            (* [comment removed for export] *)
Definition P_mem_puts : Z := 0x1d58ac.             (* [comment removed for export] *)
Definition P_mem_gets : Z := 0x1d591c.             (* [comment removed for export] *)
Definition P_bwrite_conv : Z := 0x100830.          (* [comment removed for export] *)
Definition P_mem_free : Z := 0x1d5c94.
Definition P_mem_buf_free : Z := 0x1d5d70.
(* [comment removed for export] *)
Definition P_EVP_ENCODE_CTX_new : Z := 0x1da6ac.
Definition P_EVP_ENCODE_CTX_free : Z := 0x1da6dc.
Definition P_EVP_DecodeInit : Z := 0x1da9a0.
Definition P_EVP_DecodeUpdate : Z := 0x1da9cc.
Definition P_evp_decodeblock_int : Z := 0x1dac24.
Definition P_EVP_DecodeFinal : Z := 0x1dae9c.
(* [comment removed for export] *)
Definition P_b64_read : Z := 0x26db2c.
Definition P_b64_ctrl : Z := 0x26e0e4.
Definition P_b64_new : Z := 0x26e388.
Definition P_b64_free : Z := 0x26e450.
Definition P_b64_write : Z := 0x26d7dc.            (* [comment removed for export] *)
Definition P_b64_puts : Z := 0x26e074.             (* [comment removed for export] *)
Definition P_b64_callback_ctrl : Z := 0x26e510.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_PACKET_memdup : Z := 0x26d278.
Definition P_PACKET_strndup : Z := 0x26d330.
(* [comment removed for export] *)
Definition P_ossl_HPKE_KEM_INFO_find_id : Z := 0x1bf2a0.
Definition P_ossl_HPKE_KDF_INFO_find_id : Z := 0x1bf32c.
Definition P_ossl_HPKE_AEAD_INFO_find_id : Z := 0x1bf3a0.
Definition P_OSSL_HPKE_suite_check : Z := 0x26d780.
Definition P_hpke_suite_check : Z := 0x26d6c8.         (* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_ossl_ctype_check : Z := 0xe950c.
Definition P_EVP_PKEY_free : Z := 0x191cb4.
Definition P_X509_VERIFY_PARAM_new : Z := 0x1e14d0.
Definition P_X509_VERIFY_PARAM_free : Z := 0x1e1518.
Definition P_X509_VERIFY_PARAM_add1_host : Z := 0x1e1608.
Definition P_validate_string_name : Z := 0x1e16d8.
Definition P_validate_hostname_part : Z := 0x1e1754.
Definition P_buffer_free : Z := 0x1e1a38.
Definition P_ASN1_OBJECT_free : Z := 0xf3e88.        (* [comment removed for export] *)
Definition P_buffer_cmp : Z := 0x1e1b1c.             (* [comment removed for export] *)
Definition P_sk_X509_BUFFER_cmp_thunk : Z := 0x1e1ac8.
Definition P_sk_X509_BUFFER_copy_thunk : Z := 0x1e1af4.
Definition P_add_string_to_buffer_stack : Z := 0x1e18a4.   (* [comment removed for export] *)
Definition P_sk_X509_BUFFER_freefunc_thunk : Z := 0x1e1aa0.
(* [comment removed for export] *)
Definition P_ossl_echext_free : Z := 0x26c044.
Definition P_ossl_echstore_entry_free : Z := 0x26c0ac.
Definition P_OSSL_ECHSTORE_new : Z := 0x26c17c.
Definition P_OSSL_ECHSTORE_free : Z := 0x26c224.
Definition P_sk_OSSL_ECHEXT_freefunc_thunk : Z := 0x26d0f8.
Definition P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk : Z := 0x26d120.
(* [comment removed for export] *)
Definition P_ech_final_config_checks : Z := 0x26c2b0.
Definition P_OSSL_ECHSTORE_read_echconfiglist : Z := 0x26c54c.
Definition P_ech_read_priv_echconfiglist : Z := 0x26c574.
Definition P_ech_decode_echconfig_exts : Z := 0x26d3b4.
(* [comment removed for export] *)
Definition P_errno_location : Z := 0x26ede4.
Definition P_syscall_ret : Z := 0x26f1dc.
Definition P_free : Z := 0x26f3a8.
Definition P_malloc : Z := 0x26f4e8.
Definition P_realloc : Z := 0x271098.
Definition P_memchr : Z := 0x2797c0.
Definition P_memcpy : Z := 0x2798bc.
Definition P_memset : Z := 0x279e3c.
Definition P_strcpy : Z := 0x27a088.
Definition P_stpcpy : Z := 0x27a0b0.
Definition P_strlen : Z := 0x27a320.
Definition P_strrchr : Z := 0x27a58c.
Definition P_strspn : Z := 0x27a5f8.
Definition P_pthread_getspecific : Z := 0x27c668.   (* [comment removed for export] *)
Definition P_pthread_key_create : Z := 0x27c7d4.
Definition P_nodtor : Z := 0x27c8a8.
Definition P_init_thread_destructor : Z := 0xe24ec.   (* [comment removed for export] *)
Definition P_err_delete_thread_state : Z := 0xe1810. (* [comment removed for export] *)
Definition P_pthread_mutex_lock : Z := 0x27cb38.
Definition P_pthread_mutex_unlock : Z := 0x27d024.
Definition P_pthread_once_full : Z := 0x27d220.
Definition P_pthread_once : Z := 0x27d3d8.
Definition P_pthread_rwlock_unlock : Z := 0x27d590.
Definition P_pthread_rwlock_wrlock : Z := 0x27d634.
Definition P_pthread_setspecific : Z := 0x27d7b4.
Definition P_clock_gettime : Z := 0x27d940.
Definition P_cgt_init : Z := 0x27d9f8.
Definition P_vdsosym : Z := 0x27da80.
Definition P_time : Z := 0x27de80.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_malloc_impl : Z := 0x2dc188.      (* [comment removed for export] *)
Definition A_realloc_impl : Z := 0x2dc190.
Definition A_free_impl : Z := 0x2dc198.
Definition A_destructor_key : Z := 0x2dc1a8.  (* [comment removed for export] *)
Definition A_vdso_func : Z := 0x2dc8a0.       (* [comment removed for export] *)
Definition A_mem_inited : Z := 0x2ec930.      (* [comment removed for export] *)
Definition A_err_string_once : Z := 0x2ec938. (* [comment removed for export] *)
Definition A_err_string_lock : Z := 0x2ec940. (* [comment removed for export] *)
Definition A_master_once_ret : Z := 0x2ec950. (* [comment removed for export] *)
Definition A_master_once : Z := 0x2ec954.     (* [comment removed for export] *)
Definition A_master_key : Z := 0x2ec958.      (* [comment removed for export] *)
Definition A_defctx_inited : Z := 0x2ec960.   (* [comment removed for export] *)
Definition A_defctx_tlkey : Z := 0x2ec964.    (* [comment removed for export] *)
Definition A_defctx_tlkey_once : Z := 0x2ec968. (* [comment removed for export] *)
Definition A_defctx_once : Z := 0x2ec970.     (* [comment removed for export] *)
Definition A_defctx : Z := 0x2ec978.          (* [comment removed for export] *)
Definition A_defctx_exlock : Z := 0x2ec980.   (* [comment removed for export] *)
Definition A_defctx_exmeth_bio : Z := 0x2ec9e8. (* [comment removed for export] *)
Definition A_tevent_once : Z := 0x2ecac0.     (* [comment removed for export] *)
Definition A_base_inited : Z := 0x2ecb38.     (* [comment removed for export] *)
Definition A_global_cleanup : Z := 0x2ecb3c.  (* [comment removed for export] *)
Definition A_stopped : Z := 0x2ecb40.         (* [comment removed for export] *)
Definition A_in_init_config_key : Z := 0x2ecb54. (* [comment removed for export] *)
Definition A_base_once : Z := 0x2ecb58.       (* [comment removed for export] *)
Definition A_load_strings_once : Z := 0x2ecb60. (* [comment removed for export] *)
Definition A_optsdone_lock : Z := 0x2ecb88.   (* [comment removed for export] *)
Definition A_optsdone : Z := 0x2ecb98.        (* [comment removed for export] *)
Definition A_td_tsd_used : Z := 0x2ef3e2.     (* [comment removed for export] *)
Definition A_td_cancelbuf : Z := 0x2ef418.    (* [comment removed for export] *)
Definition A_td_tsd : Z := 0x2ef420.          (* [comment removed for export] *)
Definition A_keys : Z := 0x3103a0.            (* [comment removed for export] *)
Definition A_next_key : Z := 0x3107a0.        (* [comment removed for export] *)
Definition A_key_lock : Z := 0x3107a8.        (* [comment removed for export] *)
Definition A_tsd_main : Z := 0x3107e0.        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_got_CRYPTO_malloc : Z := 0x2dad30.   (* [comment removed for export] *)
Definition A_got_ossl_echext_free : Z := 0x2dab78. (* [comment removed for export] *)
Definition A_got_ASN1_OBJECT_free : Z := 0x2dabb8.   (* [comment removed for export] *)
Definition A_got_evp_pkey : Z := 0x2dae18.
Definition A_mem_buf_method : Z := 0x2ae180.     (* [comment removed for export] *)
Definition A_b64_method : Z := 0x2daa98.         (* [comment removed for export] *)
Definition A_hpke_kem_tab : Z := 0x2ad830.        (* [comment removed for export] *)
Definition A_hpke_kdf_tab : Z := 0x2ad998.        (* [comment removed for export] *)
Definition A_hpke_aead_tab : Z := 0x2ad9e0.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIBX0 : list (Z * Z) :=
  [ (0x2dc188, 0x2dc1b0); (0x2dc8a0, 0x2dc8a8); (0x2ec930, 0x2ecba0); (0x2ef3e2, 0x2ef3e3);
    (0x2ef418, 0x2ef428); (0x3103a0, 0x3107b8); (0x3107e0, 0x310be0) ].
Definition LIBX : list (Z * Z) := LIBX0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_FUZZ_ENTRY : Z := P_LLVMFuzzerTestOneInput.
Definition P_FUZZ_RA : Z := 0xddc98.           (* [comment removed for export] *)
Definition P_FUZZ_EMPTY : Z := 0x2ec910.       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x311000.     (* [comment removed for export] *)
Definition RELRO_LO : Z := 0x27efc0.   (* [comment removed for export] *)
Definition RELRO_HI : Z := 0x2db160.   (* [comment removed for export] *)
Definition DATA_LO : Z := 0x2dc160.    (* [comment removed for export] *)
Definition BSS_HI : Z := 0x310be8.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_CRYPTO_malloc : Z := 48.
Definition FR_CRYPTO_zalloc : Z := 32.
Definition FR_CRYPTO_realloc : Z := 48.
Definition FR_CRYPTO_free : Z := 0.          (* [comment removed for export] *)
Definition FR_CRYPTO_memdup : Z := 32.
Definition FR_CRYPTO_strndup : Z := 48.
Definition FR_CRYPTO_array : Z := 32.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_pthread_mutex_unlock : Z := 96.
Definition FR_CRYPTO_THREAD_read_lock : Z := 16.   (* [comment removed for export] *)
Definition FR_CRYPTO_THREAD_get_local_ex : Z := 48.
Definition FR_ossl_sa_get : Z := 16.
Definition FR_OPENSSL_init_crypto : Z := 80.
(* [comment removed for export] *)
Definition FR_ossl_err_get_state_int : Z := 48.
Definition FR_ERR_new : Z := 32.
Definition FR_ERR_set_debug : Z := 64.
Definition FR_ERR_set_error : Z := 80.
Definition FR_ERR_vset_error : Z := 80.
Definition FR_ERR_clear_error : Z := 64.
(* [comment removed for export] *)
Definition FR_ossl_HPKE_KEM_INFO_find_id : Z := 32.
Definition FR_ossl_HPKE_KDF_INFO_find_id : Z := 16.
Definition FR_ossl_HPKE_AEAD_INFO_find_id : Z := 16.
Definition FR_OSSL_HPKE_suite_check : Z := 16.     (* [comment removed for export] *)
Definition FR_hpke_suite_check : Z := 64.
(* [comment removed for export] *)
Definition FR_get_default_context : Z := 32.
Definition FR_ossl_lib_ctx_get_ex_data_global : Z := 16.   (* [comment removed for export] *)
Definition FR_get_and_lock : Z := 32.
Definition FR_ossl_crypto_new_ex_data_ex : Z := 176.
Definition FR_CRYPTO_new_ex_data : Z := 16.                (* [comment removed for export] *)
Definition FR_CRYPTO_free_ex_data : Z := 256.
(* [comment removed for export] *)
Definition FR_BIO_new_ex : Z := 48.
Definition FR_BIO_new : Z := 16.                  (* [comment removed for export] *)
Definition FR_BIO_free : Z := 32.
Definition FR_BIO_free_int : Z := 32.
Definition FR_BIO_set_data : Z := 16.             (* [comment removed for export] *)
Definition FR_BIO_ctrl : Z := 48.
Definition FR_BIO_read : Z := 32.
Definition FR_bio_read_intern : Z := 80.
Definition FR_BIO_eof : Z := 16.
Definition FR_BIO_push : Z := 32.
Definition FR_BIO_free_all : Z := 32.
Definition FR_bread_conv : Z := 32.
Definition FR_BUF_MEM_new : Z := 32.
Definition FR_BUF_MEM_free : Z := 32.
Definition FR_BIO_new_mem_buf : Z := 32.
Definition FR_mem_read : Z := 64.
Definition FR_mem_ctrl : Z := 64.
Definition FR_mem_new : Z := 16.                  (* [comment removed for export] *)
Definition FR_mem_init : Z := 48.
Definition FR_mem_free : Z := 32.
Definition FR_mem_buf_free : Z := 32.
(* [comment removed for export] *)
Definition FR_ossl_echext_free : Z := 32.           (* [comment removed for export] *)
Definition FR_ossl_echstore_entry_free : Z := 32.   (* [comment removed for export] *)
Definition FR_OSSL_ECHSTORE_new : Z := 48.
Definition FR_OSSL_ECHSTORE_free : Z := 32.         (* [comment removed for export] *)
Definition FR_sk_freefunc_thunk : Z := 16.          (* [comment removed for export] *)
Definition FR_EVP_PKEY_free : Z := 32.
(* [comment removed for export] *)
Definition FR_X509_VERIFY_PARAM_new : Z := 16.
Definition FR_X509_VERIFY_PARAM_free : Z := 48.     (* [comment removed for export] *)
Definition FR_X509_VERIFY_PARAM_add1_host : Z := 48.
Definition FR_validate_string_name : Z := 32.
Definition FR_validate_hostname_part : Z := 96.
Definition FR_ossl_ctype_check : Z := 16.
Definition FR_buffer_free : Z := 32.                (* [comment removed for export] *)
Definition A_ctype_char_map : Z := 0x3aad4.          (* [comment removed for export] *)
Definition FR_add_string_to_buffer_stack : Z := 48.
(* [comment removed for export] *)
Definition A_data_ascii2bin : Z := 0x60608.         (* [comment removed for export] *)
Definition FR_EVP_ENCODE_CTX_new : Z := 16.         (* [comment removed for export] *)
Definition FR_EVP_ENCODE_CTX_free : Z := 16.        (* [comment removed for export] *)
Definition FR_EVP_DecodeInit : Z := 16.
Definition FR_EVP_DecodeUpdate : Z := 112.
Definition FR_evp_decodeblock_int : Z := 16.
Definition FR_EVP_DecodeFinal : Z := 48.
Definition FR_b64_read : Z := 192.
Definition FR_b64_ctrl : Z := 80.
Definition FR_b64_new : Z := 48.
Definition FR_b64_free : Z := 48.                   (* [comment removed for export] *)
Definition FR_BIO_copy_next_retry : Z := 16.
(* [comment removed for export] *)
Definition FR_ech_read_priv_echconfiglist : Z := 2352.   (* [comment removed for export] *)
Definition FR_OSSL_ECHSTORE_read_echconfiglist : Z := 16.   (* [comment removed for export] *)
Definition FR_ech_final_config_checks : Z := 80.
Definition FR_ech_decode_echconfig_exts : Z := 144.
Definition FR_FuzzerTestOneInput : Z := 32.
Definition FR_parse_one : Z := 32.
