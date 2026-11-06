(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_env
  Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_env Fz_G_OPENSSL_cpuid_setup Fz_I3_ibase Fz_W5_icb Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_T_sa_set Fz_T_slx Fz_I3_shelve Fz_G_OPENSSL_LH_new Fz_I1_first Fz_M_realloc Fz_M_realloc_array Fz_I1_insert Fz_I1_load Fz_I1_efirst Fz_I1_getitem Fz_I1_reason Fz_I1_errload Fz_I1_const Fz_I1_crypto Fz_I3_loadstr Fz_I3_full Fz_M_free Fz_G_OSSL_ERR_STATE_new Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_create_global_tevent_register_ossl Fz_T_its Fz_I3_icfast Fz_I3_egsi Fz_I3_eclear Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Fz_M_strdup Fz_I2_rcx Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Fz_M_aligned Fz_M_aligned_array Fz_I2_anl Fz_T_rcu Fz_I2_htnew Fz_I2_namemap Fz_I2_snm Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_K_pstrf Fz_K_pstr Fz_K_pstrg Fz_I2_ppi2 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions Fz_G_context_init Fz_G_default_context_do_init_ossl Fz_I3_gdc Fz_I3_fxi Fz_K_pstrs Fz_I2_ppisn Fz_I2_ppi2a Fz_I2_ppisn
  Fz_lib0 Fz_libA Fz_I3_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xba3ef0)%Z (only parsing).
Notation TSD_MAIN := (0xbc5298)%Z (only parsing).
Notation MK_KEY := (0xb9f520)%Z (only parsing).
Notation DTOR_KEY := (0x5a9f20)%Z (only parsing).

(* [comment removed for export] *)
Definition INITA_GOBJS : list (Z * Z) :=
  [(G_IC_OPTSDONE, 8); (MK_KEY, 4); (DTOR_KEY, 8); (0xb9f580, 328); (0xb9f720, 4);
   (STR_FIPS, 5); (PPI_TAB, 48); (A_PROVIDER, 9); (A_VERSION, 8); (A_FIPS, 5);
   (A_OUTPUT, 7); (A_INPUT, 6); (A_STRUCTURE, 10); (A_YES, 4); (A_NO, 3)].
Definition INITA_GCOVER : list (Z * Z) :=
  [(0xf88e0, 16); (0x52ec60, 704); (0x52efc0, 640); (0x59b500, 368);
   (0x59b6c0, 1312); (0x59bd20, 512); (0x59bfa0, 2016); (0x59c960, 64);
   (0x59c9c0, 560); (0x59cc80, 272); (0x59cde0, 768); (0x59d1a0, 1888);
   (0x59dac0, 448); (0x59dce0, 512); (0x59df60, 176); (0x59e040, 1232);
   (0x59e640, 768); (0x59ea00, 624); (0x59ed00, 1184); (0x59f2c0, 368);
   (0x59f480, 736); (0x59f800, 272); (0x59f960, 640); (0x59fc80, 528);
   (0x59ff20, 416); (0x5a0120, 224); (0x5a0220, 1648); (0x5a0a20, 496);
   (0x5a0c80, 1712); (0x5a14e0, 288); (0x5a1640, 160); (0x5a1700, 80);
   (0x5a1780, 240); (0x5a18a0, 416); (0x5a1aa0, 192); (0x5a1b80, 2576)].

Section InitA.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis CR : cli_rt RT GOBJ.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells asegs m 0xba3e98 [C8 (Z_to_bv 64 0xbc5298)].   (* [comment removed for export] *)
Hypothesis ERRNO_ACC : forall Σ m, ART RT Σ m -> acc asegs m 0xba3e48 8.                          (* [comment removed for export] *)
Hypothesis HGO : Forall (fun p => GOBJ (fst p) (snd p)) INITA_GOBJS.
Hypothesis HGC : Forall (fun p => exists b sz, GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) INITA_GCOVER.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis HCG : cg_sub FI_SITES FI_CALLS FZ_SITES FZ_CALLS.

Theorem fuzz_init_closed : fuzz_init_cps RT LIB0_A LIB_A FZ_SITES FZ_CALLS.
Proof.
  assert (facts := cr_af CR).
  assert (facts_pem := cr_afp CR).
  assert (contracts := cr_rc CR).
  assert (contracts_pem := cr_rcp CR).
  assert (c_malloc := rc_malloc RT contracts).
  assert (c_free0 := rc_free_null RT contracts).
  assert (c_stk0 := rc_stack_malloc_0 RT contracts).
  assert (c_stk1 := rc_stack_malloc_1 RT contracts).
  assert (c_memset := rc_asan_memset RT contracts).
  assert (c_memcpy := rc_asan_memcpy RT contracts).
  assert (c_strlen := rc_strlen RT contracts).
  assert (c_realloc := rcp_realloc RT contracts_pem).
  assert (c_memalign := rcp_memalign RT contracts_pem).
  assert (tsd_cell : forall Σ m, ART RT Σ m -> rw_cells asegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)])
    by exact TSD.
  assert (obj_of : forall a n, In (a, n) INITA_GOBJS -> GOBJ a n)
    by (intros a n listed; exact (proj1 (Forall_forall _ _) HGO (a, n) listed)).
  assert (cover_of : forall x n, In (x, n) INITA_GCOVER -> exists b sz, GOBJ b sz /\ b <= x /\ x + n <= b + sz)
    by (intros x n listed; exact (proj1 (Forall_forall _ _) HGC (x, n) listed)).
  assert (GOBJ G_IC_OPTSDONE 8 /\ GOBJ MK_KEY 4 /\ GOBJ DTOR_KEY 8 /\ GOBJ 0xb9f580 328 /\ GOBJ 0xb9f720 4 /\
          GOBJ STR_FIPS 5 /\ GOBJ PPI_TAB 48 /\ GOBJ A_PROVIDER 9 /\ GOBJ A_VERSION 8 /\ GOBJ A_FIPS 5 /\
          GOBJ A_OUTPUT 7 /\ GOBJ A_INPUT 6 /\ GOBJ A_STRUCTURE 10 /\ GOBJ A_YES 4 /\ GOBJ A_NO 3)
    as (obj_optsdone & obj_master_key & obj_dtor_key & obj_ctx & obj_ctx_tls & obj_rand_fips & obj_ppi_tab &
        obj_provider & obj_version & obj_fips & obj_output & obj_input & obj_structure & obj_yes & obj_no).
  { repeat split; apply obj_of; cbv [INITA_GOBJS In]; repeat first [left; reflexivity | right]. }
  (* allocators *)
  assert (run_malloc := crypto_malloc_cps RT facts c_malloc).
  assert (run_malloc_env := crypto_malloc_env RT facts run_malloc).
  assert (run_zalloc := crypto_zalloc_cps RT facts run_malloc c_memset).
  assert (run_zalloc_env := crypto_zalloc_env RT facts run_zalloc).
  assert (run_calloc := CRYPTO_calloc_cps RT facts run_zalloc_env).
  assert (run_realloc_env := crypto_realloc_cps RT facts c_realloc).
  assert (run_realloc_arr := crypto_realloc_array_cps RT facts run_realloc_env).
  assert (run_aligned_env := crypto_aligned_alloc_cps RT facts GOBJ facts_pem c_stk0 c_memalign).
  assert (run_aligned_arr := crypto_aligned_alloc_array_cps RT facts run_aligned_env).
  assert (run_free_null := crypto_free_null_cps RT facts c_free0).
  assert (run_strdup := crypto_strdup_cps RT GOBJ facts facts_pem c_strlen run_malloc_env c_memcpy).
  (* locks, stacks, hash tables, sparse arrays *)
  assert (run_lock := crypto_lock_new_cps RT facts GOBJ facts_pem c_stk0 run_zalloc).
  assert (run_lock_env := crypto_lock_new_env RT facts run_lock).
  assert (run_sk_null := OPENSSL_sk_new_null_cps RT GOBJ facts facts_pem run_zalloc_env).
  assert (run_sk_new := OPENSSL_sk_new_cps RT GOBJ facts facts_pem run_zalloc_env).
  assert (run_sk_cmp := OPENSSL_sk_set_cmp_thunks_cps RT GOBJ facts facts_pem).
  assert (run_sk_copy := OPENSSL_sk_set_copy_thunks_cps RT GOBJ facts facts_pem).
  assert (run_sk_thunks := OPENSSL_sk_set_thunks_cps RT GOBJ facts facts_pem).
  assert (run_lh_new := OPENSSL_LH_new_cps RT GOBJ facts facts_pem run_zalloc_env run_calloc).
  assert (run_lh_keep := OPENSSL_LH_set_thunks_keep_cps RT GOBJ facts facts_pem).
  assert (run_sa_new := ossl_sa_new_cps RT facts run_zalloc_env).
  assert (run_sa_set := sa_set_fresh_cps RT GOBJ facts facts_pem run_calloc).
  assert (run_rcu := rcu_lock_new_cps RT GOBJ facts facts_pem c_stk1 c_memset run_zalloc_env run_calloc).
  assert (run_anl := anl_cps RT GOBJ facts facts_pem c_memset run_aligned_arr).
  assert (run_ht := ht_new_cps RT GOBJ facts facts_pem c_memcpy run_zalloc_env run_lock_env run_anl run_rcu).
  (* OPENSSL_init_crypto base, thread-local error state, ERR_clear_error *)
  assert (run_cpuid := OPENSSL_cpuid_setup_cps RT facts).
  assert (run_base := init_crypto_base_cps RT facts GOBJ facts_pem c_stk0 obj_optsdone).
  assert (run_fast := init_crypto_fast_cps RT facts GOBJ facts_pem c_stk0 obj_optsdone).
  assert (run_ibase := ibase_cps RT GOBJ facts facts_pem run_lock_env run_cpuid tsd_cell).
  assert (run_tevent := create_global_tevent_register_ossl_cps RT GOBJ facts facts_pem
                          run_zalloc_env run_sk_null run_sk_cmp run_sk_copy run_sk_thunks run_lock_env).
  assert (run_its := its_first_cps RT GOBJ facts facts_pem run_zalloc_env run_malloc_env run_calloc run_tevent
                       obj_dtor_key tsd_cell).
  assert (run_err_state := OSSL_ERR_STATE_new_cps RT facts run_zalloc_env).
  assert (run_egsi := egsi_first_cps RT GOBJ facts facts_pem run_base run_err_state run_its run_fast
                        obj_master_key tsd_cell).
  assert (run_eclear := eclear_first_cps RT GOBJ facts facts_pem run_free_null run_egsi).
  (* error string tables *)
  assert (run_igi := igi_cps RT GOBJ facts facts_pem).
  assert (run_ers := ers_cps RT GOBJ facts facts_pem c_stk0 run_igi).
  assert (run_lh_insert := lh_insert_cps RT GOBJ facts facts_pem run_malloc_env run_realloc_arr c_memset).
  assert (run_load_strs := err_load_strings_cps RT GOBJ facts facts_pem run_lh_insert).
  assert (run_steady := err_strings_steady_cps RT GOBJ facts facts_pem run_load_strs).
  assert (run_err_const := err_const_cps RT GOBJ facts facts_pem run_load_strs run_steady).
  assert (run_esi := do_esi_cps RT GOBJ facts facts_pem run_base run_lock_env run_lh_new).
  assert (run_efirst := efirst_cps RT GOBJ facts facts_pem run_esi run_load_strs).
  assert (run_strs : crypto_strs_stmt RT GOBJ).
  { apply (crypto_strs_cps RT GOBJ facts facts_pem run_efirst run_ers run_err_const);
      apply cover_of; cbv [INITA_GCOVER In]; repeat first [left; reflexivity | right]. }
  (* the string loading path of OPENSSL_init_crypto *)
  assert (run_slx := slx_first_cps RT GOBJ facts facts_pem run_calloc run_sa_new run_sa_set obj_master_key tsd_cell).
  assert (run_shelve := shelve_first_cps RT GOBJ facts facts_pem run_base run_slx obj_master_key ERRNO_ACC tsd_cell).
  assert (run_loadstr := loadstr_cps RT GOBJ facts facts_pem c_stk0 run_shelve run_strs obj_master_key tsd_cell).
  assert (run_full := init_crypto_full_cps RT GOBJ facts facts_pem c_stk0 run_ibase run_loadstr obj_optsdone).
  (* the default library context *)
  assert (run_exdata_global := ossl_lib_ctx_get_ex_data_global_cps RT facts).
  assert (run_exdata := ossl_do_ex_data_init_cps RT GOBJ facts facts_pem obj_ctx run_exdata_global run_lock_env).
  assert (run_method_store := ossl_method_store_new_cps RT GOBJ facts facts_pem
                                run_zalloc_env run_calloc run_sa_new run_lock_env).
  assert (run_prov_conf := ossl_prov_conf_ctx_new_cps RT GOBJ facts facts_pem run_zalloc_env run_lock_env).
  assert (run_rand := rand_ctx_new_cps RT GOBJ facts facts_pem run_zalloc_env run_base run_strdup run_lock_env
                        obj_rand_fips).
  assert (run_decoder := ossl_decoder_cache_new_cps RT GOBJ facts facts_pem
                           run_malloc_env run_lock_env run_lh_new run_lh_keep).
  assert (run_prov_store := ossl_provider_store_new_cps RT GOBJ facts facts_pem
                              run_zalloc_env run_sk_new run_sk_cmp run_sk_copy run_sk_thunks run_lock_env run_sk_null).
  assert (run_propstr := ossl_property_string_data_new_cps RT GOBJ facts facts_pem
                           run_zalloc_env run_lock_env run_lh_new run_lh_keep
                           run_sk_null run_sk_cmp run_sk_copy run_sk_thunks).
  assert (run_namemap := namemap_new_cps RT GOBJ facts facts_pem c_stk1 c_memset run_zalloc_env run_lock_env run_ht
                           run_sk_null run_sk_cmp run_sk_copy run_sk_thunks).
  assert (run_stored_nm := stored_namemap_new_cps RT GOBJ facts facts_pem run_namemap).
  assert (run_defns := ossl_property_defns_new_cps RT GOBJ facts facts_pem run_lh_new).
  assert (run_glob_props := ossl_ctx_global_properties_new_cps RT facts run_zalloc_env).
  assert (run_bio := ossl_bio_core_globals_new_cps RT facts run_zalloc_env).
  assert (run_nonce := ossl_prov_drbg_nonce_ctx_new_cps RT GOBJ facts facts_pem run_zalloc_env run_lock_env).
  assert (run_selftest := ossl_self_test_set_callback_new_cps RT facts run_zalloc_env).
  assert (run_indicator := ossl_indicator_set_callback_new_cps RT facts run_zalloc_env).
  assert (run_mutex := ossl_crypto_mutex_new_cps RT GOBJ facts facts_pem run_zalloc_env).
  assert (run_condvar := ossl_crypto_condvar_new_cps RT GOBJ facts facts_pem run_zalloc_env).
  assert (run_threads := ossl_threads_ctx_new_cps RT GOBJ facts facts_pem run_zalloc_env run_mutex run_condvar).
  assert (run_child := ossl_child_prov_ctx_new_cps RT facts run_zalloc_env).
  assert (run_pstr_first := pstr_first_cps RT GOBJ facts facts_pem c_stk0 c_strlen c_memcpy run_malloc_env run_calloc
                              obj_ctx).
  assert (run_pstr_room := pstr_room_cps RT GOBJ facts facts_pem c_stk0 c_strlen c_memcpy run_malloc_env obj_ctx).
  assert (run_pstr_grow := pstr_grow_cps RT GOBJ facts facts_pem c_stk0 c_strlen c_memcpy run_malloc_env obj_ctx
                             run_realloc_arr).
  assert (run_parse_init := ossl_property_parse_init_cps RT GOBJ facts facts_pem obj_ppi_tab
                              obj_provider obj_version obj_fips obj_output obj_input obj_structure obj_yes obj_no
                              run_pstr_first run_pstr_room run_pstr_grow).
  assert (run_zlib := COMP_zlib_cps RT facts).
  assert (run_comp_type := COMP_get_type_cps RT facts).
  assert (run_comp := ossl_load_builtin_compressions_cps RT GOBJ facts facts_pem
                        run_zlib run_sk_new run_sk_cmp run_sk_copy run_sk_thunks run_comp_type).
  assert (run_ctx_init := context_init_cps RT GOBJ facts facts_pem obj_ctx run_lock_env
                            run_exdata run_method_store run_prov_conf run_rand run_decoder run_prov_store run_propstr
                            run_stored_nm run_defns run_glob_props run_bio run_nonce run_selftest run_indicator
                            run_threads run_child run_parse_init run_comp).
  assert (run_dcdi := default_context_do_init_ossl_cps RT GOBJ facts facts_pem run_ctx_init).
  assert (run_gdc := gdc_cps RT GOBJ facts facts_pem run_dcdi tsd_cell obj_ctx_tls).
  assert (run_fxi := fxi_cps RT GOBJ facts facts_pem run_gdc obj_ctx).
  exact (fuzz_init_A RT GOBJ facts facts_pem run_full run_eclear run_fxi FZ_SITES FZ_CALLS HCG).
Qed.
End InitA.
