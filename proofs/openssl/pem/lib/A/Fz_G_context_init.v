(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_M_zalloc Th_mutex Fz_M_locknew Fz_env Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Th_mutex_init Fz_M_strdup Fz_W5_icb Fz_I2_rcx Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_OPENSSL_sk_new_null Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Th_cond Fz_M_aligned Fz_M_aligned_array Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_I2_nmw Fz_I2_namemap Fz_I2_snm Fz_I2_pdefns Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_I2_ppisn Fz_G_kit3 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_G_context_init_w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tslia ::= wp_tslia.
(* [comment removed for export] *)
Local Ltac wp_out Ho SPL unf := cbn [app outside]; unf;
  repeat (split; [ first [ wp_na
                         | (clear - Ho SPL; first [ tauto | lia ])
                         | match goal with H : wp_box (aclient _ _ _ _) |- _ => unfold wp_box in H; lia end
                         | (repeat match goal with H : wp_box _ |- _ => unfold wp_box in H end; lia) ] |]); exact I.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Section context_init_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_bd1e00 : GOBJ 12187008 328.          (* [comment removed for export] *)
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.
Hypothesis C_ossl_do_ex_data_init : ossl_do_ex_data_init_stmt RT.
Hypothesis C_ossl_method_store_new : ossl_method_store_new_stmt RT.
Hypothesis C_ossl_prov_conf_ctx_new : ossl_prov_conf_ctx_new_stmt RT.
Hypothesis C_ossl_rand_ctx_new : rand_ctx_new_stmt RT.
Hypothesis C_ossl_decoder_cache_new : ossl_decoder_cache_new_stmt RT.
Hypothesis C_ossl_provider_store_new : ossl_provider_store_new_stmt RT.
Hypothesis C_ossl_property_string_data_new : ossl_property_string_data_new_stmt RT.
Hypothesis C_ossl_stored_namemap_new : stored_namemap_new_stmt RT.
Hypothesis C_ossl_property_defns_new : ossl_property_defns_new_stmt RT.
Hypothesis C_ossl_ctx_global_properties_new : ossl_ctx_global_properties_new_stmt RT.
Hypothesis C_ossl_bio_core_globals_new : ossl_bio_core_globals_new_stmt RT.
Hypothesis C_ossl_prov_drbg_nonce_ctx_new : ossl_prov_drbg_nonce_ctx_new_stmt RT.
Hypothesis C_ossl_self_test_set_callback_new : ossl_self_test_set_callback_new_stmt RT.
Hypothesis C_ossl_indicator_set_callback_new : ossl_indicator_set_callback_new_stmt RT.
Hypothesis C_ossl_threads_ctx_new : ossl_threads_ctx_new_stmt RT.
Hypothesis C_ossl_child_prov_ctx_new : ossl_child_prov_ctx_new_stmt RT.
Hypothesis C_ossl_property_parse_init : ossl_property_parse_init_stmt RT.
Hypothesis C_ossl_load_builtin_compressions : ossl_load_builtin_compressions_stmt RT.

Definition context_init_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g2_g2 g5_od : word),
    fdfs_only PMc -> mat_stable PMc ->
    a0 = Z_to_bv 64 12187008 -> tp = Z_to_bv 64 12205808 ->
    ART RT Σ m -> mem_inv asegs m -> cl_env m lb canary ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 1072 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_context_init (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ)
      ([(SITE_context_init_1, e_context_init); (SITE_context_init_2, e_context_init); (SITE_context_init_3, e_context_init);
        (SITE_context_init_4, e_context_init); (SITE_context_init_5, e_context_init); (SITE_context_init_6, e_context_init);
        (SITE_context_init_7, e_context_init); (SITE_context_init_8, e_context_init); (SITE_context_init_9, e_context_init);
        (SITE_context_init_10, e_context_init); (SITE_context_init_11, e_context_init); (SITE_context_init_12, e_context_init);
        (SITE_context_init_13, e_context_init); (SITE_context_init_14, e_context_init); (SITE_context_init_15, e_context_init);
        (SITE_context_init_16, e_context_init); (SITE_context_init_17, e_context_init); (SITE_context_init_18, e_context_init);
        (SITE_context_init_19, e_context_init); (SITE_context_init_20, e_context_init); (SITE_context_init_21, e_context_init);
        (SITE_context_init_22, e_context_init);
        (SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc);
        (SITE_ossl_do_ex_data_init_1, e_ossl_do_ex_data_init); (SITE_ossl_do_ex_data_init_2, e_ossl_do_ex_data_init);
        (SITE_ossl_method_store_new_1, e_ossl_method_store_new); (SITE_ossl_method_store_new_2, e_ossl_method_store_new);
        (SITE_ossl_method_store_new_3, e_ossl_method_store_new); (SITE_ossl_method_store_new_4, e_ossl_method_store_new);
        (SITE_ossl_method_store_new_5, e_ossl_method_store_new); (SITE_ossl_method_store_new_6, e_ossl_method_store_new);
        (SITE_ossl_prov_conf_ctx_new_1, e_ossl_prov_conf_ctx_new); (SITE_ossl_prov_conf_ctx_new_2, e_ossl_prov_conf_ctx_new);
        (SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new);
        (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_4, e_ossl_decoder_cache_new);
        (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new);
        (SITE_ossl_provider_store_new_1, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new);
        (SITE_ossl_provider_store_new_3, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_4, e_ossl_provider_store_new);
        (SITE_ossl_provider_store_new_5, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new);
        (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_8, e_ossl_provider_store_new);
        (SITE_ossl_provider_store_new_9, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_10, e_ossl_provider_store_new);
        (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new);
        (SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null);
        (SITE_ossl_property_string_data_new_1, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_2, e_ossl_property_string_data_new);
        (SITE_ossl_property_string_data_new_3, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_5, e_ossl_property_string_data_new);
        (SITE_ossl_property_string_data_new_7, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_11, e_ossl_property_string_data_new);
        (SITE_ossl_prov_drbg_nonce_ctx_new_1, e_ossl_prov_drbg_nonce_ctx_new); (SITE_ossl_prov_drbg_nonce_ctx_new_2, e_ossl_prov_drbg_nonce_ctx_new);
        (SITE_ossl_threads_ctx_new_1, e_ossl_threads_ctx_new); (SITE_ossl_threads_ctx_new_2, e_ossl_threads_ctx_new);
        (SITE_ossl_threads_ctx_new_3, e_ossl_threads_ctx_new);
        (SITE_ossl_crypto_mutex_new_1, e_ossl_crypto_mutex_new); (SITE_ossl_crypto_condvar_new_1, e_ossl_crypto_condvar_new);
        (SITE_ossl_load_builtin_compressions_1, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_2, e_ossl_load_builtin_compressions);
        (SITE_ossl_load_builtin_compressions_3, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_4, e_ossl_load_builtin_compressions);
        (SITE_ossl_load_builtin_compressions_5, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_6, e_ossl_load_builtin_compressions)]
       ++ RCX_SITES ++ SNM_SITES ++ PDEFNS_SITES ++ PPI_SITES)
      ([(SITE_context_init_1, e_lock_new); (SITE_context_init_2, e_ossl_do_ex_data_init); (SITE_context_init_3, e_ossl_method_store_new);
        (SITE_context_init_4, e_ossl_prov_conf_ctx_new); (SITE_context_init_5, e_rand_ctx_new); (SITE_context_init_6, e_ossl_method_store_new);
        (SITE_context_init_7, e_ossl_decoder_cache_new); (SITE_context_init_8, e_ossl_method_store_new); (SITE_context_init_9, e_ossl_method_store_new);
        (SITE_context_init_10, e_ossl_provider_store_new); (SITE_context_init_11, e_ossl_property_string_data_new);
        (SITE_context_init_12, e_stored_namemap_new); (SITE_context_init_13, e_pdefns);
        (SITE_context_init_14, e_ossl_ctx_global_properties_new); (SITE_context_init_14, e_CRYPTO_zalloc);
        (SITE_context_init_15, e_ossl_bio_core_globals_new); (SITE_context_init_15, e_CRYPTO_zalloc);
        (SITE_context_init_16, e_ossl_prov_drbg_nonce_ctx_new);
        (SITE_context_init_17, e_ossl_self_test_set_callback_new); (SITE_context_init_17, e_CRYPTO_zalloc);
        (SITE_context_init_18, e_ossl_indicator_set_callback_new); (SITE_context_init_18, e_CRYPTO_zalloc);
        (SITE_context_init_19, e_ossl_threads_ctx_new);
        (SITE_context_init_20, e_ossl_child_prov_ctx_new); (SITE_context_init_20, e_CRYPTO_zalloc);
        (SITE_context_init_21, e_property_parse_init); (SITE_context_init_22, e_ossl_load_builtin_compressions);
        (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc);
        (SITE_ossl_do_ex_data_init_1, e_ossl_lib_ctx_get_ex_data_global); (SITE_ossl_do_ex_data_init_2, e_lock_new);
        (SITE_ossl_method_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_2, e_CRYPTO_calloc);
        (SITE_ossl_method_store_new_2, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_3, e_ossl_sa_new);
        (SITE_ossl_method_store_new_3, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_4, e_lock_new);
        (SITE_ossl_method_store_new_5, e_lock_new); (SITE_ossl_method_store_new_6, e_lock_new);
        (SITE_ossl_prov_conf_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_prov_conf_ctx_new_2, e_lock_new);
        (SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc); (SITE_ossl_decoder_cache_new_2, e_lock_new);
        (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new); (SITE_ossl_decoder_cache_new_4, e_OPENSSL_LH_set_thunks);
        (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc);
        (SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new);
        (SITE_ossl_provider_store_new_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_4, e_OPENSSL_sk_set_copy_thunks);
        (SITE_ossl_provider_store_new_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_6, e_lock_new);
        (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_provider_store_new_8, e_OPENSSL_sk_set_cmp_thunks);
        (SITE_ossl_provider_store_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_10, e_OPENSSL_sk_set_thunks);
        (SITE_ossl_provider_store_new_11, e_lock_new);
        (SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc);
        (SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc); (SITE_ossl_property_string_data_new_2, e_lock_new);
        (SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new);
        (SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null);
        (SITE_ossl_prov_drbg_nonce_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_prov_drbg_nonce_ctx_new_2, e_lock_new);
        (SITE_ossl_threads_ctx_new_1, e_CRYPTO_zalloc); (SITE_ossl_threads_ctx_new_2, e_ossl_crypto_mutex_new);
        (SITE_ossl_threads_ctx_new_3, e_ossl_crypto_condvar_new);
        (SITE_ossl_crypto_mutex_new_1, e_CRYPTO_zalloc); (SITE_ossl_crypto_condvar_new_1, e_CRYPTO_zalloc);
        (SITE_ossl_load_builtin_compressions_1, e_COMP_zlib); (SITE_ossl_load_builtin_compressions_2, e_OPENSSL_sk_new);
        (SITE_ossl_load_builtin_compressions_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_load_builtin_compressions_4, e_OPENSSL_sk_set_copy_thunks);
        (SITE_ossl_load_builtin_compressions_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_load_builtin_compressions_6, e_COMP_get_type)]
       ++ RCX_CALLS ++ SNM_CALLS ++ PDEFNS_CALLS ++ PPI_CALLS) ->
    (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat ->
    Z.of_nat (length (rt_live RT Σ)) + 124 <= LIVE_MAX ->
    Forall (fun blk : Z * Z => 0 < snd blk) (rt_live RT Σ) ->
    46 + NM_COST + PPI_COST <= rt_credit RT Σ ->
    rw_cells asegs m 12187008 [C8 g2] -> rw_cells asegs m 12187176 [C8 g3] -> rw_cells asegs m 12187184 [C8 g4] ->
    rw_cells asegs m 12187192 [C8 g5] -> rw_cells asegs m 12187200 [C8 g6] -> rw_cells asegs m 12187208 [C8 g7] ->
    rw_cells asegs m 12187216 [C8 g8] -> rw_cells asegs m 12187224 [C8 g9] -> rw_cells asegs m 12187232 [C8 g10] ->
    rw_cells asegs m 12187240 [C8 g11] -> rw_cells asegs m 12187248 [C8 g12] -> rw_cells asegs m 12187256 [C8 g13] ->
    rw_cells asegs m 12187264 [C8 g14] -> rw_cells asegs m 12187272 [C8 g15] -> rw_cells asegs m 12187280 [C8 g16] ->
    rw_cells asegs m 12187288 [C8 g17] -> rw_cells asegs m 12187296 [C8 g18] -> rw_cells asegs m 12187304 [C8 g19] ->
    rw_cells asegs m 12187312 [C8 g20] -> rw_cells asegs m 12187320 [C8 g21] ->
    rw_cells asegs m 12187016 [C8 g2_g2] ->
    rw_cells asegs m 12186112 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 12186272 [C8 g5_od] ->
    rw_cells asegs m 12186304 [C4 (Z_to_bv 64 2)] -> rw_cells asegs m 12186336 [C4 (Z_to_bv 64 1)] ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                           F fc e_context_init m)))
      (fun c => exists (Σ' : rts RT)
         (lk1 xd2 : Z)
         (ms3 sh3 sa3a la3a lb3a sa3b la3b lb3b sa3c la3c lb3c sa3d la3d lb3d big3 : Z)
         (cf4 ck4 : Z)
         (rx5 rq5 rl5 : Z)
         (ms6 sh6 sa6a la6a lb6a sa6b la6b lb6b sa6c la6c lb6c sa6d la6d lb6d big6 : Z)
         (dc7 dl7 dq7 dr7 : Z)
         (ms8 sh8 sa8a la8a lb8a sa8b la8b lb8b sa8c la8c lb8c sa8d la8d lb8d big8 : Z)
         (ms9 sh9 sa9a la9a lb9a sa9b la9b lb9b sa9c la9c lb9c sa9d la9d lb9d big9 : Z)
         (pv10 pp10 pd10 pc10 pk10 : Z)
         (ps11 pk11 pla11 pba11 plb11 pbb11 pqa11 pqb11 : Z)
         (nm12 nk12 nh12 nhl12 nmd12 nnb12 nrl12 nrq12 nsk12 : Z)
         (pd13 pb13 : Z)
         (gp14 : Z)
         (bc15 : Z)
         (dn16 dk16 : Z)
         (st17 : Z)
         (ic18 : Z)
         (th19 tm19 tc19 : Z)
         (ch20 : Z)
         (pi8 pi9 pi10 pi11 pi12 pi13 pi14 pi15 pi16 pi17 pi18 pi19 pi20 pi21 pi22 pi23 pi24 pi25 : Z)
         (cp22 : Z),
         ASTA RT Σ' PMc
           (fun ms => exists (m' : mem) (j4 j16 j19 : list byte),
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
              /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
              /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
                   [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (12187008, 12187024); (12187176, 12187328)] m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 lk1)]
              /\ rw_cells asegs m' 12187016 [C8 (Z_to_bv 64 xd2)]
              /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 ps11)]
              /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 ms3)]
              /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 pv10)]
              /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 nm12)]
              /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 pd13)]
              /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 gp14)]
              /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 rx5)]
              /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 dn16)]
              /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 cf4)]
              /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 bc15)]
              /\ rw_cells asegs m' 12187256 [C8 (Z_to_bv 64 ch20)]
              /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 ms6)]
              /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 dc7)]
              /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 ms8)]
              /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 ms9)]
              /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 st17)]
              /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 ic18)]
              /\ rw_cells asegs m' 12187312 [C8 (Z_to_bv 64 th19)]
              /\ rw_cells asegs m' 12187320 [C8 (Z_to_bv 64 cp22)]
              /\ rw_cells asegs m' lk1 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\ rw_cells asegs m' xd2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' ms3 [C8 (Z_to_bv 64 12187008); C8 (Z_to_bv 64 sh3); C8 (Z_to_bv 64 big3)]
              /\ rw_cells asegs m' sh3 [C8 (Z_to_bv 64 sa3a); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la3a); C8 (Z_to_bv 64 lb3a); C8 (Z_to_bv 64 sa3b); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la3b); C8 (Z_to_bv 64 lb3b); C8 (Z_to_bv 64 sa3c); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la3c); C8 (Z_to_bv 64 lb3c); C8 (Z_to_bv 64 sa3d); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la3d); C8 (Z_to_bv 64 lb3d)]
              /\ Forall (fun q => rw_cells asegs m' q [CB 32 (repeat (Z_to_bv 8 0) 32)]) [sa3a; sa3b; sa3c; sa3d]
              /\ Forall (fun q => rw_cells asegs m' q (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) [la3a; lb3a; la3b; lb3b; la3c; lb3c; la3d; lb3d; big3]
              /\ rw_cells asegs m' cf4 [C8 (Z_to_bv 64 ck4); CB 8 j4]
              /\ rw_cells asegs m' ck4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' rx5 (rcx_cells rl5 rq5)
              /\ rw_cells asegs m' rq5 [C1 (Z_to_bv 8 102); C1 (Z_to_bv 8 105); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 0)]
              /\ rw_cells asegs m' rl5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' ms6 [C8 (Z_to_bv 64 12187008); C8 (Z_to_bv 64 sh6); C8 (Z_to_bv 64 big6)]
              /\ rw_cells asegs m' sh6 [C8 (Z_to_bv 64 sa6a); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la6a); C8 (Z_to_bv 64 lb6a); C8 (Z_to_bv 64 sa6b); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la6b); C8 (Z_to_bv 64 lb6b); C8 (Z_to_bv 64 sa6c); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la6c); C8 (Z_to_bv 64 lb6c); C8 (Z_to_bv 64 sa6d); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la6d); C8 (Z_to_bv 64 lb6d)]
              /\ Forall (fun q => rw_cells asegs m' q [CB 32 (repeat (Z_to_bv 8 0) 32)]) [sa6a; sa6b; sa6c; sa6d]
              /\ Forall (fun q => rw_cells asegs m' q (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) [la6a; lb6a; la6b; lb6b; la6c; lb6c; la6d; lb6d; big6]
              /\ rw_cells asegs m' dc7 [C8 (Z_to_bv 64 dl7); C8 (Z_to_bv 64 dq7)]
              /\ rw_cells asegs m' dl7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' dq7 [C8 (Z_to_bv 64 dr7); C8 (Z_to_bv 64 0x315864); C8 (Z_to_bv 64 0x3156e0); C8 (Z_to_bv 64 0x31707c); C8 (Z_to_bv 64 0x31709c); C8 (Z_to_bv 64 0x3170bc); C8 (Z_to_bv 64 0x3170dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]
              /\ rw_cells asegs m' dr7 [CB 128 (repeat (Z_to_bv 8 0) 128)]
              /\ rw_cells asegs m' ms8 [C8 (Z_to_bv 64 12187008); C8 (Z_to_bv 64 sh8); C8 (Z_to_bv 64 big8)]
              /\ rw_cells asegs m' sh8 [C8 (Z_to_bv 64 sa8a); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la8a); C8 (Z_to_bv 64 lb8a); C8 (Z_to_bv 64 sa8b); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la8b); C8 (Z_to_bv 64 lb8b); C8 (Z_to_bv 64 sa8c); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la8c); C8 (Z_to_bv 64 lb8c); C8 (Z_to_bv 64 sa8d); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la8d); C8 (Z_to_bv 64 lb8d)]
              /\ Forall (fun q => rw_cells asegs m' q [CB 32 (repeat (Z_to_bv 8 0) 32)]) [sa8a; sa8b; sa8c; sa8d]
              /\ Forall (fun q => rw_cells asegs m' q (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) [la8a; lb8a; la8b; lb8b; la8c; lb8c; la8d; lb8d; big8]
              /\ rw_cells asegs m' ms9 [C8 (Z_to_bv 64 12187008); C8 (Z_to_bv 64 sh9); C8 (Z_to_bv 64 big9)]
              /\ rw_cells asegs m' sh9 [C8 (Z_to_bv 64 sa9a); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la9a); C8 (Z_to_bv 64 lb9a); C8 (Z_to_bv 64 sa9b); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la9b); C8 (Z_to_bv 64 lb9b); C8 (Z_to_bv 64 sa9c); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la9c); C8 (Z_to_bv 64 lb9c); C8 (Z_to_bv 64 sa9d); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 la9d); C8 (Z_to_bv 64 lb9d)]
              /\ Forall (fun q => rw_cells asegs m' q [CB 32 (repeat (Z_to_bv 8 0) 32)]) [sa9a; sa9b; sa9c; sa9d]
              /\ Forall (fun q => rw_cells asegs m' q (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) [la9a; lb9a; la9b; lb9b; la9c; lb9c; la9d; lb9d; big9]
              /\ rw_cells asegs m' pv10 [C8 (Z_to_bv 64 12187008); C8 (Z_to_bv 64 pp10); C8 (Z_to_bv 64 pc10); C8 (Z_to_bv 64 pd10); C8 (Z_to_bv 64 pk10); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]
              /\ rw_cells asegs m' pp10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]
              /\ rw_cells asegs m' pd10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' pc10 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x214568); C8 (Z_to_bv 64 0x2144ec); C8 (Z_to_bv 64 0x214594)]
              /\ rw_cells asegs m' pk10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' nm12 (snm_cells nh12 nk12 nsk12)
              /\ rw_cells asegs m' nk12 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' nh12 (ht_tab4 (Z_to_bv 64 12187008) nrl12 nhl12 nmd12)
              /\ rw_cells asegs m' nhl12 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' nmd12 [C8 (Z_to_bv 64 nnb12); C8 (Z_to_bv 64 nnb12); C8 (Z_to_bv 64 511)]
              /\ rw_cells asegs m' nnb12 [CB (Z.to_nat NB_BYTES) (repeat (Z_to_bv 8 0) (Z.to_nat NB_BYTES))]
              /\ rw_cells asegs m' nrl12 (rcu_head (Z_to_bv 64 12187008) nrq12)
              /\ rw_cells asegs m' (nrl12 + 48) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' (nrl12 + 88) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' (nrl12 + 128) cond_cells
              /\ rw_cells asegs m' (nrl12 + 176) (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' (nrl12 + 216) cond_cells
              /\ rw_cells asegs m' nrq12 [CB 16 (repeat (Z_to_bv 8 0) 16)]
              /\ rw_cells asegs m' nsk12 nm_sk_cells
              /\ rw_cells asegs m' pd13 (pdefns_cells pb13)
              /\ rw_cells asegs m' pb13 [CB 128 (repeat (Z_to_bv 8 0) 128)]
              /\ rw_cells asegs m' gp14 [CB 16 (repeat (Z_to_bv 8 0) 16)]
              /\ rw_cells asegs m' bc15 [CB 56 (repeat (Z_to_bv 8 0) 56)]
              /\ rw_cells asegs m' dn16 [C8 (Z_to_bv 64 dk16); CB 8 j16]
              /\ rw_cells asegs m' dk16 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
              /\ rw_cells asegs m' st17 [CB 16 (repeat (Z_to_bv 8 0) 16)]
              /\ rw_cells asegs m' ic18 [CB 8 (repeat (Z_to_bv 8 0) 8)]
              /\ rw_cells asegs m' th19 [CB 16 j19; C8 (Z_to_bv 64 tm19); C8 (Z_to_bv 64 tc19)]
              /\ rw_cells asegs m' tm19 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
              /\ rw_cells asegs m' tc19 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
              /\ rw_cells asegs m' ch20 [CB 88 (repeat (Z_to_bv 8 0) 88)]
              /\ rw_cells asegs m' cp22 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 5312040); C8 (Z_to_bv 64 5312000)])
           c
         /\ (exists NEW : list (Z * Z),
               NEW = [(cp22, 56); (pi25, 24); (pi24, 18); (pi23, 24); (pi22, 32); (pi21, 19); (pi20, 24); (pi19, 25);
                      (pi18, 24); (pi17, 48); (pi16, 21); (pi15, 24); (pi14, 22); (pi13, 24); (pi12, 20); (pi11, 24);
                      (pi10, 23); (pi9, 24); (pi8, 24); (ch20, 88); (tc19, 48); (tm19, 40); (th19, 32); (ic18, 8);
                      (st17, 16); (dk16, 40); (dn16, 16); (bc15, 56); (gp14, 16); (pb13, 128); (pd13, 104); (nsk12, 56);
                      (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40);
                      (pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104); (pba11, 128); (pla11, 104); (pk11, 40); (ps11, 48);
                      (pk10, 40); (pc10, 56); (pd10, 40); (pp10, 56); (pv10, 80); (big9, 40); (lb9d, 40); (la9d, 40);
                      (sa9d, 32); (lb9c, 40); (la9c, 40); (sa9c, 32); (lb9b, 40); (la9b, 40); (sa9b, 32); (lb9a, 40);
                      (la9a, 40); (sa9a, 32); (sh9, 384); (ms9, 24); (big8, 40); (lb8d, 40); (la8d, 40); (sa8d, 32);
                      (lb8c, 40); (la8c, 40); (sa8c, 32); (lb8b, 40); (la8b, 40); (sa8b, 32); (lb8a, 40); (la8a, 40);
                      (sa8a, 32); (sh8, 384); (ms8, 24); (dr7, 128); (dq7, 104); (dl7, 40); (dc7, 16); (big6, 40);
                      (lb6d, 40); (la6d, 40); (sa6d, 32); (lb6c, 40); (la6c, 40); (sa6c, 32); (lb6b, 40); (la6b, 40);
                      (sa6b, 32); (lb6a, 40); (la6a, 40); (sa6a, 32); (sh6, 384); (ms6, 24); (rl5, 40); (rq5, 5);
                      (rx5, 88); (ck4, 40); (cf4, 16); (big3, 40); (lb3d, 40); (la3d, 40); (sa3d, 32); (lb3c, 40);
                      (la3c, 40); (sa3c, 32); (lb3b, 40); (la3b, 40); (sa3b, 32); (lb3a, 40); (la3a, 40); (sa3a, 32);
                      (sh3, 384); (ms3, 24); (xd2, 40); (lk1, 40)]
               /\ rt_live RT Σ' = NEW ++ rt_live RT Σ
               /\ length NEW = 124%nat
               /\ In (lk1, 40) NEW
               /\ Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP /\ 0 < snd blk) NEW)
         /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
         /\ rt_credit RT Σ' = rt_credit RT Σ - (46 + NM_COST + PPI_COST)
         /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem context_init_cps : context_init_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo outer lb canary g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 g2_g2 g5_od
    OnlyFds Stable ArgCtx TpVal Rt0 Inv0 Cl0 Ok0 Deep0 Chain0 FpChain0 Edges FrmCap LiveCap LivePos Budget
    FLock FPsd FEvp FProvSt FNmap FDefns FGprops FDrbg FNonce FConf FBio FChild FDecSt FDecCa FEncSt FLdrSt
    FSelfT FIndic FThr FComp ExGlob RndFlag RndOd RndTwo RndOne TS cfg0 Entry Cont.
  subst a0.
  pose proof NM_COST_nonneg as NmPos. pose proof PPI_COST_nonneg as PpiPos.
  assert (Mcost0 : forall n, n <= 64512 -> mcost n = 0).
  { intros n Small. unfold mcost. rewrite (proj2 (Z.leb_le n 64512) Small). reflexivity. }
  pose proof (af_sp0_win RT AF Σ m Rt0) as Sp0Floor.
  destruct Ok0 as (Stack0 & LoInWin & LoRtGap & SpRoom16 & SpAlign16).
  assert (LoHeap : 0x10007fff8000 <= lo) by (unfold STACK_WIN in LoInWin; lia).
  assert (SpBelow47 : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in SpRoom16; lia).
  assert (Room0 : lo + 65536 + 1072 <= bv_unsigned sp) by (unfold RT_STACK in Deep0; exact Deep0).
  assert (FrameLit : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48)
    by (apply unsigned_lit; lia).
  assert (CtxAccOf : forall (Σx : rts RT) (mx : mem), ART RT Σx mx -> acc asegs mx 12187008 328).
  { intros Σx mx RtX.
    exact (afp_acc_global RT GOBJ AFP Σx mx 12187008 328 12187008 328 RtX GO_bd1e00 (Z.le_refl _) (Z.le_refl _)). }
  assert (ShadowOf : forall (Σx : rts RT) (mx : mem) (a : Z), ART RT Σx mx -> 2148974256 <= a <= 2148974296 ->
                       ro_cells asegs mx a [C1 (Z_to_bv 8 0)]).
  { intros Σx mx a RtX Span.
    pose proof (afp_gsh_byte RT GOBJ AFP Σx mx 12187008 328 (12187008 + (a - 2148974256) * 8) RtX GO_bd1e00
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Byte.
    rewrite (proj2 (Z.ltb_ge _ 8)) in Byte by lia.
    replace ((12187008 + (a - 2148974256) * 8) / 8 + 2147450880) with a in Byte by lia.
    exact Byte. }
  assert (ConstsOf : forall (Σx : rts RT) (mx : mem), ART RT Σx mx ->
                       ro_cells asegs mx 6736696 [C8 (Z_to_bv 64 2147450880)] /\ img_untouched mx).
  { intros Σx mx RtX.
    destruct (af_client_consts RT AF Σx mx RtX) as (_ & ShBase & _ & _ & Clean).
    split; [exact ShBase | exact Clean]. }
  destruct (ConstsOf Σ m Rt0) as (ShBase0 & Clean0).
  pose proof (context_init_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F fc m lo) as Seg0.
  repeat match type of Seg0 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ m Rt0) | (apply (ShadowOf Σ m); [exact Rt0 | clear - Rt0; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg0 ok); clear ok
         end.
  cl_lift Seg0 Entry cfg1 At1.
  destruct (ASTA_unpack RT Σ _ _ cfg1 At1) as (st1 & Post0 & At1s). clear At1.
  (* the frame of context_init and the ctx object survive the first segment untouched outside the frame *)
  clear FLock FPsd FEvp FProvSt FNmap FDefns FGprops FDrbg FNonce FConf FBio FChild FDecSt FDecCa FEncSt FLdrSt
    FSelfT FIndic FThr FComp.
  destruct Post0 as (j1 & m1 & -> & Munch1 & Mono1 & Inv1 & Frame1
                     & FComp & FThr & FIndic & FSelfT & FLdrSt & FEncSt & FDecCa & FDecSt & FChild & FBio
                     & FConf & FNonce & FDrbg & FGprops & FDefns & FNmap & FProvSt & FEvp & FPsd & FLock
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack1).
  repeat match goal with
         | Cell : rw_cells asegs m ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m m1 X cs Cell Munch1
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add] in Iny; clear - Iny LoHeap Room0; cbn [outside]; split; [lia | exact I]))
               as Moved;
             clear Cell; rename Moved into Cell
         end.
  assert (Rt1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 48 [] Rt0); [clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch1 | | exact Mono1].
    intros x Inside. exfalso. apply Inside. exact I. }
  assert (Cl1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary Cl0 Munch1); cl_fp_lia).
  assert (Above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { intros w Hi. cbv beta in Hi. apply Munch1. cbn [outside]. clear - Hi. split; [lia | exact I]. }
  set (Wctx := [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (12187008, 12187024); (12187176, 12187328)]).
  assert (PresGrow : forall (Σx : rts RT) (spx : Z) (Wx : list (Z * Z)) (mx my : mem),
                       (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> rt_frames RT Σx = rt_frames RT Σ ->
                       spx <= bv_unsigned sp -> (forall x, outside Wctx x -> outside Wx x) ->
                       rt_pres_fp (rt_live RT Σx) (rt_frames RT Σx) spx Wx mx my ->
                       rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx mx my).
  { intros Σx spx Wx mx my LiveSub FramesX SpLe Narrow PresX.
    apply (pres_fp_sub _ _ _ _ _ _ _ _ mx my PresX).
    intros x Acl Out. split; [|exact (Narrow x Out)].
    apply (aclient_mono _ _ _ _ _ _ _ Acl); [exact LiveSub | rewrite FramesX; intros e Ein; exact Ein | exact SpLe]. }
  assert (Kept1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m1).
  { apply (PresGrow Σ (bv_unsigned sp) []); [intros e Ein; exact Ein | reflexivity | clear - FrameLit; lia | intros; exact I |].
    exact (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 48 [] Rt0 ltac:(clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch1). }
  clear Munch1 Rt0 Inv0 Cl0 Stack0 Clean0 ShBase0 Entry.
  (* call 1: CRYPTO_THREAD_lock_new *)
  assert (CallOkBelow : forall (Σx : rts RT) (mx : mem), stk asegs mx lo (bv_unsigned sp + -48) -> rt_sp0 RT Σx = rt_sp0 RT Σ ->
                     call_ok RT Σx mx (Z_to_bv 64 (bv_unsigned sp + -48)) lo).
  { intros Σx mx StackX BaseX. unfold call_ok. rewrite FrameLit, BaseX.
    split; [exact StackX|]. split; [exact LoInWin|]. split; [unfold RT_STACK; lia|].
    split; [unfold USTACK_TOP in *; lia | lia]. }
  assert (SavedOf : forall (mx : mem) (jx : list byte),
                      rw_cells asegs mx (bv_unsigned sp + -48) [CB 8 jx; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
                      rw_cells asegs mx (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { intros mx jx Fr.
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -48 + Z.of_nat (cells_size [CB 8 jx; C8 s3; C8 s2; C8 s1]))
      by (cbn [cells_size csize Nat.add]; lia).
    exact (rw_cells_skip mx _ [CB 8 jx; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] Fr). }
  assert (Lit1 : bv_unsigned (Z_to_bv 64 SITE_context_init_1) = SITE_context_init_1)
    by (apply unsigned_lit; unfold SITE_context_init_1; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_lock_new SITE_context_init_1 m m1 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_1, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_1, e_lock_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above1 (SavedOf m1 j1 Frame1) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain1 & FpChain1).
  apply (C_lock_new Σ PMc (Z_to_bv 64 SITE_context_init_1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp
           (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 6736696) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880)
           s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary).
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve [ assumption
                 | apply CallOkBelow; [exact Stack1 | reflexivity]
                 | rewrite FrameLit; unfold RT_STACK; lia
                 | rewrite Lit1; exact Chain1
                 | apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
                 | unfold LIVE_MAX in *; lia
                 | lia ] end).
  intros cfg2 (Σ1 & lk1 & At2 & LvAfter1 & FrAfter1 & BaseAfter1 & CrAfter1 & LockPos & LockAlign & LockBelow & GrAfter1).
  destruct (ASTA_unpack RT Σ1 _ _ cfg2 At2) as (st2 & (m2 & Ret1 & After1 & Pres1 & Cl2 & LkWr1 & LkAcc1) & At2s).
  clear At2.
  destruct Ret1 as (r0 & r1 & r2 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & r3 & r4 & r5 & r6 & F1 & fc1 & ->).
  rewrite FrameLit in After1, Pres1. destruct After1 as (Rt2 & Inv2 & Mono2 & Stack2).
  rewrite (ret_pc_even SITE_context_init_1) in At2s by (unfold SITE_context_init_1; clear - Room0; lia).
  clear At1s.
  (* the lock object: where it lives, and that it lies in the heap below the stack *)
  rename LkWr1 into lk1Obj. clear LkAcc1.
  assert (lk1Live : In (lk1, 40) (rt_live RT Σ1)) by (rewrite LvAfter1; left; reflexivity).
  assert (lk1Heap : 17594333495296 <= lk1 /\ lk1 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ1 m2 lk1 40 Rt2 lk1Live ltac:(clear - Rt2; lia)) |].
    pose proof (af_live_range RT AF Σ1 m2 lk1 40 Rt2 lk1Live) as Span.
    rewrite BaseAfter1 in Span. clear - Span LoInWin; lia. }
  (* the lock call wrote nothing of ours: carry the frame and the static cells to m2 *)
  repeat match goal with
         | Cell : rw_cells asegs m1 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : rw_cells asegs m2 X cs);
             [ apply (rw_cells_agree_nw asegs m1 m2 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add] in Rw; apply Pres1;
               [ first [ apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ]
             | clear Cell; rename Moved into Cell ]
         end.
  assert (Above2 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m2).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres1 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I])).
    exact (Above1 w Hi). }
  assert (Kept2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m2).
  { apply (pres_fp_trans _ _ _ _ m m1 m2 Kept1).
    apply (PresGrow Σ (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m1 m2); [intros e Ein; exact Ein | reflexivity | clear - FrameLit; lia | | exact Pres1].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept1 Above1 Pres1 Mono1 Inv1 Rt1 Cl1 Stack1 Chain1 FpChain1.
  (* second segment: store the lock, call ossl_do_ex_data_init *)
  destruct (ConstsOf Σ1 m2 Rt2) as (ShBase2 & Clean2).
  assert (LockWord : 0 <= lk1 < 2 ^ 64) by (unfold USTACK_TOP in LockBelow; lia).
  assert (LockNz : bv_eqb (Z_to_bv 64 lk1) (Z_to_bv 64 0) = false) by solve_cond_u.
  pose proof (context_init_s1_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_1)
                r0 r1 r2 x1 x2 x3 x4 x5 x6 x7 r3 r4 r5 r6 lk1 j1
                g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F1 fc1 m2 lo) as Seg1.
  repeat match type of Seg1 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ1 m2 Rt2) | (apply (ShadowOf Σ1 m2); [exact Rt2 | clear - Rt2; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg1 ok); clear ok
         end.
  cl_lift Seg1 At2s cfg3 At3.
  destruct (ASTA_unpack RT Σ1 _ _ cfg3 At3) as (st3 & Post1 & At3s). clear At3 At2s.
  clear FLock FPsd FEvp FProvSt FNmap FDefns FGprops FDrbg FNonce FConf FBio FChild FDecSt FDecCa FEncSt FLdrSt
    FSelfT FIndic FThr FComp Frame1.
  destruct Post1 as (m3 & -> & Munch3 & Mono3 & Inv3 & FLock & Frame3
                     & FComp & FThr & FIndic & FSelfT & FLdrSt & FEncSt & FDecCa & FDecSt & FChild & FBio
                     & FConf & FNonce & FDrbg & FGprops & FDefns & FNmap & FProvSt & FEvp & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack3).
  repeat match goal with
         | Cell : rw_cells asegs m2 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m2 m3 X cs Cell Munch3
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells] in Iny;
                                 first [ clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                       | let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end ]))
               as Moved;
             clear Cell; rename Moved into Cell
         end.
  assert (Rt3 : ART RT Σ1 m3).
  { apply (cl_seg_ART RT AF Σ1 m2 m3 (bv_unsigned sp) 48 [(12187008, 12187016)] Rt2);
      [rewrite BaseAfter1; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch3 | | exact Mono3].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary Cl2 Munch3); cl_fp_lia).
  assert (Above3 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m3).
  { intros w Hi. cbv beta in Hi. rewrite Munch3 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I). exact (Above2 w Hi). }
  assert (Kept3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m3).
  { apply (pres_fp_trans _ _ _ _ m m2 m3 Kept2).
    apply (PresGrow Σ1 (bv_unsigned sp) [(12187008, 12187016)] m2 m3);
      [rewrite LvAfter1; intros e Ein; right; exact Ein | exact FrAfter1 | clear - FrameLit; lia | | ].
    - intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. unfold G_ALLOW_CUST in Out. clear - Out. split; [lia | exact I].
    - exact (cl_seg_pres RT AF Σ1 m2 m3 (bv_unsigned sp) 48 [(12187008, 12187016)] Rt2 ltac:(rewrite BaseAfter1; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch3). }
  clear Kept2 Above2 Munch3 Mono2 Inv2 Rt2 Cl2 Stack2 ShBase2 Clean2.
  assert (Lit2 : bv_unsigned (Z_to_bv 64 SITE_context_init_2) = SITE_context_init_2)
    by (apply unsigned_lit; unfold SITE_context_init_2; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_do_ex_data_init SITE_context_init_2 m m3 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_2, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_2, e_ossl_do_ex_data_init) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above3 (SavedOf m3 j1 Frame3) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain2 & FpChain2).
  apply (C_ossl_do_ex_data_init Σ1 PMc (Z_to_bv 64 SITE_context_init_2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp
           r0 r1 r2 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 0) x2 x3 x4 x5 x6 x7
           (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 r3 r4 r5 r6 F1 fc1 m3 lo
           (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary g2_g2).
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve [ assumption | reflexivity
                 | apply CallOkBelow; [exact Stack3 | exact BaseAfter1]
                 | rewrite FrameLit; unfold RT_STACK; lia
                 | rewrite GrAfter1, Lit2; exact Chain2
                 | rewrite GrAfter1; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
                 | rewrite FrAfter1; lia
                 | rewrite LvAfter1; cbn [length]; unfold LIVE_MAX in *; lia
                 | rewrite CrAfter1; lia ] end).
  intros cfg4 (Σ2 & q1 & At4 & LvAfter2 & FrAfter2 & BaseAfter2 & CrAfter2 & ExPos & ExAlign & ExBelow & GrAfter2).
  destruct (ASTA_unpack RT Σ2 _ _ cfg4 At4) as (st4 & (m4 & Ret2 & After2 & Pres2 & Cl4 & ExWr & ExAcc & ExNew & ExMutex) & At4s).
  clear At4 At3s.
  destruct Ret2 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & ->).
  rewrite FrameLit in After2, Pres2. destruct After2 as (Rt4 & Inv4 & Mono4 & Stack4).
  rewrite (ret_pc_even SITE_context_init_2) in At4s by (unfold SITE_context_init_2; clear - Room0; lia).
  rewrite (proj2 (Z.ltb_lt 0 q1) ExPos) in At4s. cbn [Z.b2z] in At4s.
  clear ExGlob. rename ExNew into ExGlob.
  repeat match goal with
         | Cell : rw_cells asegs m3 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : rw_cells asegs m4 X cs);
             [ apply (rw_cells_agree_nw asegs m3 m4 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells] in Rw; apply Pres2;
               [ first [ apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia
                       | match goal with
                         | Mem : In (X, ?n) (rt_live RT Σ1) |- _ => apply (acl_live _ _ _ X n); [exact Mem | clear - Rw; lia]
                         end ]
               | first [ clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                       | match goal with
                         | Hp : 17594333495296 <= X /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end ] ]
             | clear Cell; rename Moved into Cell ]
         end.
  assert (Above4 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m4).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres2 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above3 w Hi). }
  assert (Kept4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m4).
  { apply (pres_fp_trans _ _ _ _ m m3 m4 Kept3).
    apply (PresGrow Σ1 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1); (12187016, 12187024)] m3 m4);
      [rewrite LvAfter1; intros e Ein; right; exact Ein | exact FrAfter1 | clear - FrameLit; lia | | exact Pres2].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. unfold G_ALLOW_CUST in *. clear - Out. repeat split; try exact I; lia. }
  clear Kept3 Above3 Pres2 Mono3 Inv3 Rt3 Cl3 Stack3 Chain2 FpChain2.
  (* the ex-data lock object, and the lock object again, now in the ledger of Σ2 *)
  rename ExMutex into q1Obj. clear ExWr ExAcc.
  assert (Moved : In (lk1, 40) (rt_live RT Σ2)) by (rewrite LvAfter2; right; exact lk1Live).
  clear lk1Live. rename Moved into lk1Live.
  assert (q1Live : In (q1, 40) (rt_live RT Σ2)) by (rewrite LvAfter2; left; reflexivity).
  assert (q1Heap : 17594333495296 <= q1 /\ q1 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ2 m4 q1 40 Rt4 q1Live ltac:(clear - Rt4; lia)) |].
    pose proof (af_live_range RT AF Σ2 m4 q1 40 Rt4 q1Live) as Span.
    rewrite BaseAfter2, BaseAfter1 in Span. clear - Span LoInWin; lia. }
  (* third segment: check the ex_data result, then call ossl_method_store_new *)
  destruct (ConstsOf Σ2 m4 Rt4) as (ShBase4 & Clean4).
  pose proof (context_init_s2_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_2)
                y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 lk1 1 j1
                g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F2 fc2 m4 lo) as Seg2.
  repeat match type of Seg2 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ2 m4 Rt4) | (apply (ShadowOf Σ2 m4); [exact Rt4 | clear - Rt4; lia])
                        | reflexivity | (vm_compute; reflexivity) | clear - Room0; lia ];
             specialize (Seg2 ok); clear ok
         end.
  cl_lift Seg2 At4s cfg5 At5.
  destruct (ASTA_unpack RT Σ2 _ _ cfg5 At5) as (st5 & Post2 & At5s). clear At5 At4s.
  clear FLock FPsd FEvp FProvSt FNmap FDefns FGprops FDrbg FNonce FConf FBio FChild FDecSt FDecCa FEncSt FLdrSt
    FSelfT FIndic FThr FComp Frame3.
  destruct Post2 as (m5 & -> & Munch5 & Mono5 & Inv5 & FLock & Frame5
                     & FComp & FThr & FIndic & FSelfT & FLdrSt & FEncSt & FDecCa & FDecSt & FChild & FBio
                     & FConf & FNonce & FDrbg & FGprops & FDefns & FNmap & FProvSt & FEvp & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack5).
  repeat match goal with
         | Cell : rw_cells asegs m4 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m4 m5 X cs Cell Munch5
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells] in Iny;
                                 first [ clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                       | let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end ]))
               as Moved;
             clear Cell; rename Moved into Cell
         end.
  assert (Rt5 : ART RT Σ2 m5).
  { apply (cl_seg_ART RT AF Σ2 m4 m5 (bv_unsigned sp) 48 [] Rt4);
      [rewrite BaseAfter2, BaseAfter1; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch5 | | exact Mono5].
    intros x Inside. exfalso. apply Inside. exact I. }
  assert (Cl5 : cl_env m5 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m4 m5 _ canary Cl4 Munch5); cl_fp_lia).
  assert (Above5 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m5).
  { intros w Hi. cbv beta in Hi. rewrite Munch5 by (clear - Hi; cbn [outside]; split; [lia | exact I]). exact (Above4 w Hi). }
  assert (Kept5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m5).
  { apply (pres_fp_trans _ _ _ _ m m4 m5 Kept4).
    apply (PresGrow Σ2 (bv_unsigned sp) [] m4 m5);
      [rewrite LvAfter2, LvAfter1; intros e Ein; right; right; exact Ein | rewrite FrAfter2; exact FrAfter1 | clear - FrameLit; lia | intros; exact I | ].
    exact (cl_seg_pres RT AF Σ2 m4 m5 (bv_unsigned sp) 48 [] Rt4 ltac:(rewrite BaseAfter2, BaseAfter1; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch5). }
  clear Kept4 Above4 Munch5 Mono4 Inv4 Rt4 Cl4 Stack4 ShBase4 Clean4 LockNz Lit1 Lit2.
  (* the runtime ledger after call 2, relative to the entry state *)
  assert (Lv2 : rt_live RT Σ2 = [(q1, 40); (lk1, 40)] ++ rt_live RT Σ) by (rewrite LvAfter2, LvAfter1; reflexivity).
  remember [(q1, 40); (lk1, 40)] as New2 eqn:New2Is in Lv2.
  assert (NewLen2 : Z.of_nat (length New2) = 2) by (rewrite New2Is; reflexivity).
  assert (NewPos2 : Forall (fun blk => 0 < snd blk) New2).
  { rewrite New2Is. repeat first [ apply Forall_cons; [cbn [snd]; lia | ] | apply Forall_nil ]. }
  assert (Fr2 : rt_frames RT Σ2 = rt_frames RT Σ) by (rewrite FrAfter2; exact FrAfter1).
  assert (Base2 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite BaseAfter2; exact BaseAfter1).
  assert (Gr2 : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite GrAfter2; exact GrAfter1).
  assert (Cr2 : rt_credit RT Σ2 = rt_credit RT Σ - 2) by (rewrite CrAfter2, CrAfter1; lia).
  assert (NewBnd2 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New2).
  { rewrite New2Is. constructor; [cbn [fst snd]; split; [|split]; assumption |].
    constructor; [cbn [fst snd]; split; [|split]; assumption | constructor]. }
  clear LvAfter1 LvAfter2 FrAfter1 FrAfter2 BaseAfter1 BaseAfter2 GrAfter1 GrAfter2 CrAfter1 CrAfter2.
  clear LockPos LockAlign LockBelow ExPos ExAlign ExBelow SpAlign16.
  (* call 3: ossl_method_store_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_method_store_new SITE_context_init_3 m m5 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_3, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_3, e_ossl_method_store_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above5 (SavedOf m5 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain3 & FpChain3).
  match type of At5s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_method_store_new Σ2 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr2, unsigned_lit by (unfold SITE_context_init_3; clear - Room0; lia); exact Chain3
             | rewrite Gr2, unsigned_lit by (unfold SITE_context_init_3; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr2; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr2; clear - FrmCap; lia
             | rewrite Lv2, length_app, Nat2Z.inj_add, NewLen2; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr2; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg6 (Σ3 & ms3 & sh3 & sa3a & la3a & lb3a & sa3b & la3b & lb3b & sa3c & la3c & lb3c & sa3d & la3d & lb3d & big3 & At6 & LvPost3 & FrPost3 & BasePost3 & CrPost3 & Bnd3 & GrPost3).
  destruct (proj1 (Forall_forall _ _) Bnd3 (ms3, 24) ltac:(wp_in_lit)) as (V3Pos & V3Al & V3Top).
  cbn [fst snd] in V3Pos, V3Al, V3Top. clear V3Al.
  destruct (ASTA_unpack RT Σ3 _ _ cfg6 At6) as (st6 & (m6 & Ret3 & After3 & Pres3 & Cl6 & Obj3) & At6s).
  clear At6 At5s.
  destruct Ret3 as (r30 & r31 & r32 & x31 & x32 & x33 & x34 & x35 & x36 & x37 & r33 & r34 & r35 & r36 & F3 & fc3 & ->).
  rewrite FrameLit in After3, Pres3. destruct After3 as (Rt6 & Inv6 & Mono6 & Stack6).
  rewrite (ret_pc_even SITE_context_init_3) in At6s by (unfold SITE_context_init_3; clear - Room0; lia).
  destruct Obj3 as (ms3Obj & _ & sh3Obj & _ & SaAll3 & LkAll3).
  destruct (proj1 (Forall_forall _ _) SaAll3 sa3a ltac:(wp_in_lit)) as (sa3aObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll3 sa3b ltac:(wp_in_lit)) as (sa3bObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll3 sa3c ltac:(wp_in_lit)) as (sa3cObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll3 sa3d ltac:(wp_in_lit)) as (sa3dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 la3a ltac:(wp_in_lit)) as (la3aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 lb3a ltac:(wp_in_lit)) as (lb3aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 la3b ltac:(wp_in_lit)) as (la3bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 lb3b ltac:(wp_in_lit)) as (lb3bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 la3c ltac:(wp_in_lit)) as (la3cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 lb3c ltac:(wp_in_lit)) as (lb3cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 la3d ltac:(wp_in_lit)) as (la3dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 lb3d ltac:(wp_in_lit)) as (lb3dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll3 big3 ltac:(wp_in_lit)) as (big3Obj & _).
  clear SaAll3 LkAll3.
  repeat match goal with
         | Cell : rw_cells asegs m5 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m6 X cs);
             [ apply (rw_cells_agree_nw asegs m5 m6 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres3;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ2) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above6 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m6).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres3 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above5 w Hi). }
  assert (Kept6 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m6).
  { apply (pres_fp_trans _ _ _ _ m m5 m6 Kept5).
    apply (PresGrow Σ2 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m5 m6);
      [rewrite Lv2; intros e Ein; apply in_or_app; right; exact Ein | exact Fr2 | clear - FrameLit; lia | | exact Pres3].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept5 Above5 Pres3 Mono6 Inv5 Rt5 Cl5 Stack5 Chain3 FpChain3.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ2) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ3)) by (rewrite LvPost3; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (big3Live : In (big3, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (big3Heap : 17594333495296 <= big3 /\ big3 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 big3 40 Rt6 big3Live ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 big3 40 Rt6 big3Live) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (lb3dLive : In (lb3d, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (lb3dHeap : 17594333495296 <= lb3d /\ lb3d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 lb3d 40 Rt6 lb3dLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 lb3d 40 Rt6 lb3dLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (la3dLive : In (la3d, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (la3dHeap : 17594333495296 <= la3d /\ la3d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 la3d 40 Rt6 la3dLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 la3d 40 Rt6 la3dLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (sa3dLive : In (sa3d, 32) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (sa3dHeap : 17594333495296 <= sa3d /\ sa3d + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 sa3d 32 Rt6 sa3dLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 sa3d 32 Rt6 sa3dLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (lb3cLive : In (lb3c, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (lb3cHeap : 17594333495296 <= lb3c /\ lb3c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 lb3c 40 Rt6 lb3cLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 lb3c 40 Rt6 lb3cLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (la3cLive : In (la3c, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (la3cHeap : 17594333495296 <= la3c /\ la3c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 la3c 40 Rt6 la3cLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 la3c 40 Rt6 la3cLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (sa3cLive : In (sa3c, 32) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (sa3cHeap : 17594333495296 <= sa3c /\ sa3c + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 sa3c 32 Rt6 sa3cLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 sa3c 32 Rt6 sa3cLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (lb3bLive : In (lb3b, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (lb3bHeap : 17594333495296 <= lb3b /\ lb3b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 lb3b 40 Rt6 lb3bLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 lb3b 40 Rt6 lb3bLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (la3bLive : In (la3b, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (la3bHeap : 17594333495296 <= la3b /\ la3b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 la3b 40 Rt6 la3bLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 la3b 40 Rt6 la3bLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (sa3bLive : In (sa3b, 32) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (sa3bHeap : 17594333495296 <= sa3b /\ sa3b + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 sa3b 32 Rt6 sa3bLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 sa3b 32 Rt6 sa3bLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (lb3aLive : In (lb3a, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (lb3aHeap : 17594333495296 <= lb3a /\ lb3a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 lb3a 40 Rt6 lb3aLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 lb3a 40 Rt6 lb3aLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (la3aLive : In (la3a, 40) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (la3aHeap : 17594333495296 <= la3a /\ la3a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 la3a 40 Rt6 la3aLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 la3a 40 Rt6 la3aLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (sa3aLive : In (sa3a, 32) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (sa3aHeap : 17594333495296 <= sa3a /\ sa3a + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 sa3a 32 Rt6 sa3aLive ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 sa3a 32 Rt6 sa3aLive) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (sh3Live : In (sh3, 384) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (sh3Heap : 17594333495296 <= sh3 /\ sh3 + 384 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 sh3 384 Rt6 sh3Live ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 sh3 384 Rt6 sh3Live) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  assert (ms3Live : In (ms3, 24) (rt_live RT Σ3)) by (rewrite LvPost3; apply in_or_app; left; wp_in_lit).
  assert (ms3Heap : 17594333495296 <= ms3 /\ ms3 + 24 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ3 m6 ms3 24 Rt6 ms3Live ltac:(clear - Rt6; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ3 m6 ms3 24 Rt6 ms3Live) as Span.
    rewrite BasePost3, Base2 in Span. clear - Span LoInWin; lia. }
  rewrite Lv2 in LvPost3. rewrite ?app_assoc, ?app_comm_cons in LvPost3.
  match type of LvPost3 with _ = ?L ++ rt_live RT Σ => remember L as New3 eqn:New3Is in LvPost3 end.
  rename LvPost3 into Lv3.
  assert (NewLen3 : Z.of_nat (length New3) = 17)
    by (rewrite New3Is; rewrite ?length_app; cbn [length]; clear - NewLen2; lia).
  assert (NewPos3 : Forall (fun blk => 0 < snd blk) New3).
  { rewrite New3Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos2; lia | ] | apply Forall_nil | exact NewPos2 ]. }
  assert (NewBnd3 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New3).
  { rewrite New3Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(big3, 40); (lb3d, 40); (la3d, 40); (sa3d, 32); (lb3c, 40); (la3c, 40); (sa3c, 32); (lb3b, 40); (la3b, 40); (sa3b, 32); (lb3a, 40); (la3a, 40); (sa3a, 32); (sh3, 384); (ms3, 24)] ++ New2)). apply Forall_app. split; [exact Bnd3 | exact NewBnd2]. }
  assert (Fr3 : rt_frames RT Σ3 = rt_frames RT Σ) by (rewrite FrPost3; exact Fr2).
  assert (Base3 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite BasePost3; exact Base2).
  assert (Gr3 : rt_cg RT Σ3 = rt_cg RT Σ) by (rewrite GrPost3; exact Gr2).
  assert (Cr3 : rt_credit RT Σ3 = rt_credit RT Σ - 11)
    by (rewrite CrPost3, Cr2; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost3 BasePost3 GrPost3 CrPost3 Lv2 NewLen2 NewPos2 NewBnd2 Bnd3 Fr2 Base2 Gr2 Cr2.
  assert (V3Word : 0 <= ms3 < 2 ^ 64) by (unfold USTACK_TOP in V3Top; clear - V3Pos V3Top; lia).
  assert (V3Nz : bv_eqb (Z_to_bv 64 ms3) (Z_to_bv 64 0) = false) by (clear - V3Word V3Pos; solve_cond_u).
  destruct (ConstsOf Σ3 m6 Rt6) as (ShBase6 & Clean6).
  pose proof (context_init_s3_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_3)
                r30 r31 r32 x31 x32 x33 x34 x35 x36 x37 r33 r34 r35 r36 lk1 ms3 j1
                g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F3 fc3 m6 lo) as Seg3.
  repeat match type of Seg3 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ3 m6 Rt6) | (apply (ShadowOf Σ3 m6); [exact Rt6 | clear - Rt6; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg3 ok); clear ok
         end.
  cl_lift Seg3 At6s cfg7 At7.
  destruct (ASTA_unpack RT Σ3 _ _ cfg7 At7) as (st7 & Post3 & At7s). clear At7 At6s.
  repeat match goal with
         | Old : rw_cells asegs m6 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post3 as (m7 & -> & Munch7 & Mono7 & Inv7
                     & FEvp & FLock & Frame7 & FComp & FThr & FIndic & FSelfT
                     & FLdrSt & FEncSt & FDecCa & FDecSt & FChild & FBio & FConf
                     & FNonce & FDrbg & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack7).
  repeat match goal with
         | Cell : rw_cells asegs m6 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m6 m7 X cs Cell Munch7
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt7 : ART RT Σ3 m7).
  { apply (cl_seg_ART RT AF Σ3 m6 m7 (bv_unsigned sp) 48 [(12187184, 12187192)] Rt6);
      [rewrite Base3; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch7 | | exact Mono7].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl7 : cl_env m7 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m6 m7 _ canary Cl6 Munch7); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above7 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m7).
  { intros w Hi. cbv beta in Hi. rewrite Munch7 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above6 w Hi). }
  assert (Kept7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m7).
  { apply (pres_fp_trans _ _ _ _ m m6 m7 Kept6).
    apply (PresGrow Σ3 (bv_unsigned sp) [(12187184, 12187192)] m6 m7);
      [rewrite Lv3; intros e Ein; apply in_or_app; right; exact Ein | exact Fr3 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ3 m6 m7 (bv_unsigned sp) 48 [(12187184, 12187192)] Rt6
             ltac:(rewrite Base3; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch7). }
  clear Kept6 Above6 Munch7 Mono7 Inv6 Rt6 Cl6 Stack6 ShBase6 Clean6.
  clear V3Pos V3Top V3Nz.
  (* call 4: ossl_prov_conf_ctx_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_prov_conf_ctx_new SITE_context_init_4 m m7 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_4, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_4, e_ossl_prov_conf_ctx_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above7 (SavedOf m7 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain4 & FpChain4).
  match type of At7s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_prov_conf_ctx_new Σ3 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr3, unsigned_lit by (unfold SITE_context_init_4; clear - Room0; lia); exact Chain4
             | rewrite Gr3, unsigned_lit by (unfold SITE_context_init_4; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr3; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr3; clear - FrmCap; lia
             | rewrite Lv3, length_app, Nat2Z.inj_add, NewLen3; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr3; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg8 (Σ4 & cf4 & ck4 & At8 & LvPost4 & FrPost4 & BasePost4 & CrPost4 & V4Pos & V4Al & V4Top & ck4Pos & ck4Al & ck4Top & GrPost4).
  destruct (ASTA_unpack RT Σ4 _ _ cfg8 At8) as (st8 & (jc4 & m8 & Ret4 & After4 & Pres4 & Cl8 & Obj4) & At8s).
  clear At8 At7s.
  destruct Ret4 as (r40 & r41 & r42 & x41 & x42 & x43 & x44 & x45 & x46 & x47 & r43 & r44 & r45 & r46 & F4 & fc4 & ->).
  rewrite FrameLit in After4, Pres4. destruct After4 as (Rt8 & Inv8 & Mono8 & Stack8).
  rewrite (ret_pc_even SITE_context_init_4) in At8s by (unfold SITE_context_init_4; clear - Room0; lia).
  destruct Obj4 as (_ & _ & _ & _ & cf4Obj & ck4Obj).
  repeat match goal with
         | Cell : rw_cells asegs m7 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m8 X cs);
             [ apply (rw_cells_agree_nw asegs m7 m8 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres4;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ3) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above8 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m8).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres4 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above7 w Hi). }
  assert (Kept8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m8).
  { apply (pres_fp_trans _ _ _ _ m m7 m8 Kept7).
    apply (PresGrow Σ3 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m7 m8);
      [rewrite Lv3; intros e Ein; apply in_or_app; right; exact Ein | exact Fr3 | clear - FrameLit; lia | | exact Pres4].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept7 Above7 Pres4 Mono8 Inv7 Rt7 Cl7 Stack7 Chain4 FpChain4.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ3) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ4)) by (rewrite LvPost4; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (ck4Live : In (ck4, 40) (rt_live RT Σ4)) by (rewrite LvPost4; wp_in_lit).
  assert (ck4Heap : 17594333495296 <= ck4 /\ ck4 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ4 m8 ck4 40 Rt8 ck4Live ltac:(clear - Rt8; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ4 m8 ck4 40 Rt8 ck4Live) as Span.
    rewrite BasePost4, Base3 in Span. clear - Span LoInWin; lia. }
  assert (cf4Live : In (cf4, 16) (rt_live RT Σ4)) by (rewrite LvPost4; wp_in_lit).
  assert (cf4Heap : 17594333495296 <= cf4 /\ cf4 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ4 m8 cf4 16 Rt8 cf4Live ltac:(clear - Rt8; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ4 m8 cf4 16 Rt8 cf4Live) as Span.
    rewrite BasePost4, Base3 in Span. clear - Span LoInWin; lia. }
  assert (Bnd4 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(ck4, 40); (cf4, 16)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V4Al ck4Pos ck4Al ck4Top.
  rewrite Lv3 in LvPost4. rewrite ?app_assoc, ?app_comm_cons in LvPost4.
  match type of LvPost4 with _ = ?L ++ rt_live RT Σ => remember L as New4 eqn:New4Is in LvPost4 end.
  rename LvPost4 into Lv4.
  assert (NewLen4 : Z.of_nat (length New4) = 19)
    by (rewrite New4Is; rewrite ?length_app; cbn [length]; clear - NewLen3; lia).
  assert (NewPos4 : Forall (fun blk => 0 < snd blk) New4).
  { rewrite New4Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos3; lia | ] | apply Forall_nil | exact NewPos3 ]. }
  assert (NewBnd4 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New4).
  { rewrite New4Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(ck4, 40); (cf4, 16)] ++ New3)). apply Forall_app. split; [exact Bnd4 | exact NewBnd3]. }
  assert (Fr4 : rt_frames RT Σ4 = rt_frames RT Σ) by (rewrite FrPost4; exact Fr3).
  assert (Base4 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (rewrite BasePost4; exact Base3).
  assert (Gr4 : rt_cg RT Σ4 = rt_cg RT Σ) by (rewrite GrPost4; exact Gr3).
  assert (Cr4 : rt_credit RT Σ4 = rt_credit RT Σ - 12)
    by (rewrite CrPost4, Cr3; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost4 BasePost4 GrPost4 CrPost4 Lv3 NewLen3 NewPos3 NewBnd3 Bnd4 Fr3 Base3 Gr3 Cr3.
  assert (V4Word : 0 <= cf4 < 2 ^ 64) by (unfold USTACK_TOP in V4Top; clear - V4Pos V4Top; lia).
  assert (V4Nz : bv_eqb (Z_to_bv 64 cf4) (Z_to_bv 64 0) = false) by (clear - V4Word V4Pos; solve_cond_u).
  destruct (ConstsOf Σ4 m8 Rt8) as (ShBase8 & Clean8).
  pose proof (context_init_s4_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_4)
                r40 r41 r42 x41 x42 x43 x44 x45 x46 x47 r43 r44 r45 r46 lk1 ms3 cf4 j1
                g3 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F4 fc4 m8 lo) as Seg4.
  repeat match type of Seg4 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ4 m8 Rt8) | (apply (ShadowOf Σ4 m8); [exact Rt8 | clear - Rt8; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg4 ok); clear ok
         end.
  cl_lift Seg4 At8s cfg9 At9.
  destruct (ASTA_unpack RT Σ4 _ _ cfg9 At9) as (st9 & Post4 & At9s). clear At9 At8s.
  repeat match goal with
         | Old : rw_cells asegs m8 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post4 as (m9 & -> & Munch9 & Mono9 & Inv9
                     & FConf & FEvp & FLock & Frame9 & FComp & FThr & FIndic
                     & FSelfT & FLdrSt & FEncSt & FDecCa & FDecSt & FChild & FBio
                     & FNonce & FDrbg & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack9).
  repeat match goal with
         | Cell : rw_cells asegs m8 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m8 m9 X cs Cell Munch9
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt9 : ART RT Σ4 m9).
  { apply (cl_seg_ART RT AF Σ4 m8 m9 (bv_unsigned sp) 48 [(12187240, 12187248)] Rt8);
      [rewrite Base4; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch9 | | exact Mono9].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl9 : cl_env m9 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m8 m9 _ canary Cl8 Munch9); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above9 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m9).
  { intros w Hi. cbv beta in Hi. rewrite Munch9 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above8 w Hi). }
  assert (Kept9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m9).
  { apply (pres_fp_trans _ _ _ _ m m8 m9 Kept8).
    apply (PresGrow Σ4 (bv_unsigned sp) [(12187240, 12187248)] m8 m9);
      [rewrite Lv4; intros e Ein; apply in_or_app; right; exact Ein | exact Fr4 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ4 m8 m9 (bv_unsigned sp) 48 [(12187240, 12187248)] Rt8
             ltac:(rewrite Base4; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch9). }
  clear Kept8 Above8 Munch9 Mono9 Inv8 Rt8 Cl8 Stack8 ShBase8 Clean8.
  clear V4Pos V4Top V4Nz.
  (* call 5: rand_ctx_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_rand_ctx_new SITE_context_init_5 m m9 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_5, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_5, e_rand_ctx_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above9 (SavedOf m9 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain5 & FpChain5).
  match type of At9s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_rand_ctx_new Σ4 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m9 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary g5_od)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr4, unsigned_lit by (unfold SITE_context_init_5; clear - Room0; lia); exact Chain5
             | rewrite Gr4, unsigned_lit by (unfold SITE_context_init_5; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr4; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr4; clear - FrmCap; lia
             | rewrite Lv4, length_app, Nat2Z.inj_add, NewLen4; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr4; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg10 (Σ5 & rx5 & rq5 & rl5 & At10 & LvPost5 & FrPost5 & BasePost5 & CrPost5 & V5Pos & V5Al & V5Top & rq5Pos & rq5Al & rq5Top & rl5Pos & rl5Al & rl5Top & GrPost5).
  destruct (ASTA_unpack RT Σ5 _ _ cfg10 At10) as (st10 & (m10 & Ret5 & After5 & Pres5 & Cl10 & Obj5) & At10s).
  clear At10 At9s.
  destruct Ret5 as (r50 & r51 & r52 & x51 & x52 & x53 & x54 & x55 & x56 & x57 & r53 & r54 & r55 & r56 & F5 & fc5 & ->).
  rewrite FrameLit in After5, Pres5. destruct After5 as (Rt10 & Inv10 & Mono10 & Stack10).
  rewrite (ret_pc_even SITE_context_init_5) in At10s by (unfold SITE_context_init_5; clear - Room0; lia).
  destruct Obj5 as (_ & _ & rx5Obj & rq5Obj & rl5Obj & _ & _ & _ & _).
  repeat match goal with
         | Cell : rw_cells asegs m9 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m10 X cs);
             [ apply (rw_cells_agree_nw asegs m9 m10 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres5;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ4) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above10 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m10).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres5 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above9 w Hi). }
  assert (Kept10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m10).
  { apply (pres_fp_trans _ _ _ _ m m9 m10 Kept9).
    apply (PresGrow Σ4 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m9 m10);
      [rewrite Lv4; intros e Ein; apply in_or_app; right; exact Ein | exact Fr4 | clear - FrameLit; lia | | exact Pres5].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept9 Above9 Pres5 Mono10 Inv9 Rt9 Cl9 Stack9 Chain5 FpChain5.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ4) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ5)) by (rewrite LvPost5; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (rl5Live : In (rl5, 40) (rt_live RT Σ5)) by (rewrite LvPost5; wp_in_lit).
  assert (rl5Heap : 17594333495296 <= rl5 /\ rl5 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ5 m10 rl5 40 Rt10 rl5Live ltac:(clear - Rt10; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ5 m10 rl5 40 Rt10 rl5Live) as Span.
    rewrite BasePost5, Base4 in Span. clear - Span LoInWin; lia. }
  assert (rq5Live : In (rq5, 5) (rt_live RT Σ5)) by (rewrite LvPost5; wp_in_lit).
  assert (rq5Heap : 17594333495296 <= rq5 /\ rq5 + 5 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ5 m10 rq5 5 Rt10 rq5Live ltac:(clear - Rt10; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ5 m10 rq5 5 Rt10 rq5Live) as Span.
    rewrite BasePost5, Base4 in Span. clear - Span LoInWin; lia. }
  assert (rx5Live : In (rx5, 88) (rt_live RT Σ5)) by (rewrite LvPost5; wp_in_lit).
  assert (rx5Heap : 17594333495296 <= rx5 /\ rx5 + 88 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ5 m10 rx5 88 Rt10 rx5Live ltac:(clear - Rt10; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ5 m10 rx5 88 Rt10 rx5Live) as Span.
    rewrite BasePost5, Base4 in Span. clear - Span LoInWin; lia. }
  assert (Bnd5 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(rl5, 40); (rq5, 5); (rx5, 88)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V5Al rq5Pos rq5Al rq5Top rl5Pos rl5Al rl5Top.
  rewrite Lv4 in LvPost5. rewrite ?app_assoc, ?app_comm_cons in LvPost5.
  match type of LvPost5 with _ = ?L ++ rt_live RT Σ => remember L as New5 eqn:New5Is in LvPost5 end.
  rename LvPost5 into Lv5.
  assert (NewLen5 : Z.of_nat (length New5) = 22)
    by (rewrite New5Is; rewrite ?length_app; cbn [length]; clear - NewLen4; lia).
  assert (NewPos5 : Forall (fun blk => 0 < snd blk) New5).
  { rewrite New5Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos4; lia | ] | apply Forall_nil | exact NewPos4 ]. }
  assert (NewBnd5 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New5).
  { rewrite New5Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(rl5, 40); (rq5, 5); (rx5, 88)] ++ New4)). apply Forall_app. split; [exact Bnd5 | exact NewBnd4]. }
  assert (Fr5 : rt_frames RT Σ5 = rt_frames RT Σ) by (rewrite FrPost5; exact Fr4).
  assert (Base5 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite BasePost5; exact Base4).
  assert (Gr5 : rt_cg RT Σ5 = rt_cg RT Σ) by (rewrite GrPost5; exact Gr4).
  assert (Cr5 : rt_credit RT Σ5 = rt_credit RT Σ - 14)
    by (rewrite CrPost5, Cr4; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost5 BasePost5 GrPost5 CrPost5 Lv4 NewLen4 NewPos4 NewBnd4 Bnd5 Fr4 Base4 Gr4 Cr4.
  assert (V5Word : 0 <= rx5 < 2 ^ 64) by (unfold USTACK_TOP in V5Top; clear - V5Pos V5Top; lia).
  assert (V5Nz : bv_eqb (Z_to_bv 64 rx5) (Z_to_bv 64 0) = false) by (clear - V5Word V5Pos; solve_cond_u).
  destruct (ConstsOf Σ5 m10 Rt10) as (ShBase10 & Clean10).
  pose proof (context_init_s5_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_5)
                r50 r51 r52 x51 x52 x53 x54 x55 x56 x57 r53 r54 r55 r56 lk1 ms3 cf4 rx5 j1
                g3 g5 g6 g7 g8 g9 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F5 fc5 m10 lo) as Seg5.
  repeat match type of Seg5 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ5 m10 Rt10) | (apply (ShadowOf Σ5 m10); [exact Rt10 | clear - Rt10; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg5 ok); clear ok
         end.
  cl_lift Seg5 At10s cfg11 At11.
  destruct (ASTA_unpack RT Σ5 _ _ cfg11 At11) as (st11 & Post5 & At11s). clear At11 At10s.
  repeat match goal with
         | Old : rw_cells asegs m10 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post5 as (m11 & -> & Munch11 & Mono11 & Inv11
                     & FDrbg & FConf & FEvp & FLock & Frame11 & FComp & FThr
                     & FIndic & FSelfT & FLdrSt & FEncSt & FDecCa & FDecSt & FChild
                     & FBio & FNonce & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack11).
  repeat match goal with
         | Cell : rw_cells asegs m10 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m10 m11 X cs Cell Munch11
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt11 : ART RT Σ5 m11).
  { apply (cl_seg_ART RT AF Σ5 m10 m11 (bv_unsigned sp) 48 [(12187224, 12187232)] Rt10);
      [rewrite Base5; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch11 | | exact Mono11].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl11 : cl_env m11 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m10 m11 _ canary Cl10 Munch11); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above11 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m11).
  { intros w Hi. cbv beta in Hi. rewrite Munch11 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above10 w Hi). }
  assert (Kept11 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m11).
  { apply (pres_fp_trans _ _ _ _ m m10 m11 Kept10).
    apply (PresGrow Σ5 (bv_unsigned sp) [(12187224, 12187232)] m10 m11);
      [rewrite Lv5; intros e Ein; apply in_or_app; right; exact Ein | exact Fr5 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ5 m10 m11 (bv_unsigned sp) 48 [(12187224, 12187232)] Rt10
             ltac:(rewrite Base5; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch11). }
  clear Kept10 Above10 Munch11 Mono11 Inv10 Rt10 Cl10 Stack10 ShBase10 Clean10.
  clear V5Pos V5Top V5Nz.
  (* call 6: ossl_method_store_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_method_store_new SITE_context_init_6 m m11 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_6, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_6, e_ossl_method_store_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above11 (SavedOf m11 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain6 & FpChain6).
  match type of At11s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_method_store_new Σ5 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m11 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr5, unsigned_lit by (unfold SITE_context_init_6; clear - Room0; lia); exact Chain6
             | rewrite Gr5, unsigned_lit by (unfold SITE_context_init_6; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr5; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr5; clear - FrmCap; lia
             | rewrite Lv5, length_app, Nat2Z.inj_add, NewLen5; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr5; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg12 (Σ6 & ms6 & sh6 & sa6a & la6a & lb6a & sa6b & la6b & lb6b & sa6c & la6c & lb6c & sa6d & la6d & lb6d & big6 & At12 & LvPost6 & FrPost6 & BasePost6 & CrPost6 & Bnd6 & GrPost6).
  destruct (proj1 (Forall_forall _ _) Bnd6 (ms6, 24) ltac:(wp_in_lit)) as (V6Pos & V6Al & V6Top).
  cbn [fst snd] in V6Pos, V6Al, V6Top. clear V6Al.
  destruct (ASTA_unpack RT Σ6 _ _ cfg12 At12) as (st12 & (m12 & Ret6 & After6 & Pres6 & Cl12 & Obj6) & At12s).
  clear At12 At11s.
  destruct Ret6 as (r60 & r61 & r62 & x61 & x62 & x63 & x64 & x65 & x66 & x67 & r63 & r64 & r65 & r66 & F6 & fc6 & ->).
  rewrite FrameLit in After6, Pres6. destruct After6 as (Rt12 & Inv12 & Mono12 & Stack12).
  rewrite (ret_pc_even SITE_context_init_6) in At12s by (unfold SITE_context_init_6; clear - Room0; lia).
  destruct Obj6 as (ms6Obj & _ & sh6Obj & _ & SaAll6 & LkAll6).
  destruct (proj1 (Forall_forall _ _) SaAll6 sa6a ltac:(wp_in_lit)) as (sa6aObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll6 sa6b ltac:(wp_in_lit)) as (sa6bObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll6 sa6c ltac:(wp_in_lit)) as (sa6cObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll6 sa6d ltac:(wp_in_lit)) as (sa6dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 la6a ltac:(wp_in_lit)) as (la6aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 lb6a ltac:(wp_in_lit)) as (lb6aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 la6b ltac:(wp_in_lit)) as (la6bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 lb6b ltac:(wp_in_lit)) as (lb6bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 la6c ltac:(wp_in_lit)) as (la6cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 lb6c ltac:(wp_in_lit)) as (lb6cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 la6d ltac:(wp_in_lit)) as (la6dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 lb6d ltac:(wp_in_lit)) as (lb6dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll6 big6 ltac:(wp_in_lit)) as (big6Obj & _).
  clear SaAll6 LkAll6.
  repeat match goal with
         | Cell : rw_cells asegs m11 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m12 X cs);
             [ apply (rw_cells_agree_nw asegs m11 m12 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres6;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ5) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above12 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m12).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres6 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above11 w Hi). }
  assert (Kept12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m12).
  { apply (pres_fp_trans _ _ _ _ m m11 m12 Kept11).
    apply (PresGrow Σ5 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m11 m12);
      [rewrite Lv5; intros e Ein; apply in_or_app; right; exact Ein | exact Fr5 | clear - FrameLit; lia | | exact Pres6].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept11 Above11 Pres6 Mono12 Inv11 Rt11 Cl11 Stack11 Chain6 FpChain6.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ5) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ6)) by (rewrite LvPost6; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (big6Live : In (big6, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (big6Heap : 17594333495296 <= big6 /\ big6 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 big6 40 Rt12 big6Live ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 big6 40 Rt12 big6Live) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (lb6dLive : In (lb6d, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (lb6dHeap : 17594333495296 <= lb6d /\ lb6d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 lb6d 40 Rt12 lb6dLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 lb6d 40 Rt12 lb6dLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (la6dLive : In (la6d, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (la6dHeap : 17594333495296 <= la6d /\ la6d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 la6d 40 Rt12 la6dLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 la6d 40 Rt12 la6dLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (sa6dLive : In (sa6d, 32) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (sa6dHeap : 17594333495296 <= sa6d /\ sa6d + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 sa6d 32 Rt12 sa6dLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 sa6d 32 Rt12 sa6dLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (lb6cLive : In (lb6c, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (lb6cHeap : 17594333495296 <= lb6c /\ lb6c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 lb6c 40 Rt12 lb6cLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 lb6c 40 Rt12 lb6cLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (la6cLive : In (la6c, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (la6cHeap : 17594333495296 <= la6c /\ la6c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 la6c 40 Rt12 la6cLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 la6c 40 Rt12 la6cLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (sa6cLive : In (sa6c, 32) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (sa6cHeap : 17594333495296 <= sa6c /\ sa6c + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 sa6c 32 Rt12 sa6cLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 sa6c 32 Rt12 sa6cLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (lb6bLive : In (lb6b, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (lb6bHeap : 17594333495296 <= lb6b /\ lb6b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 lb6b 40 Rt12 lb6bLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 lb6b 40 Rt12 lb6bLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (la6bLive : In (la6b, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (la6bHeap : 17594333495296 <= la6b /\ la6b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 la6b 40 Rt12 la6bLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 la6b 40 Rt12 la6bLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (sa6bLive : In (sa6b, 32) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (sa6bHeap : 17594333495296 <= sa6b /\ sa6b + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 sa6b 32 Rt12 sa6bLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 sa6b 32 Rt12 sa6bLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (lb6aLive : In (lb6a, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (lb6aHeap : 17594333495296 <= lb6a /\ lb6a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 lb6a 40 Rt12 lb6aLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 lb6a 40 Rt12 lb6aLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (la6aLive : In (la6a, 40) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (la6aHeap : 17594333495296 <= la6a /\ la6a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 la6a 40 Rt12 la6aLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 la6a 40 Rt12 la6aLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (sa6aLive : In (sa6a, 32) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (sa6aHeap : 17594333495296 <= sa6a /\ sa6a + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 sa6a 32 Rt12 sa6aLive ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 sa6a 32 Rt12 sa6aLive) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (sh6Live : In (sh6, 384) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (sh6Heap : 17594333495296 <= sh6 /\ sh6 + 384 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 sh6 384 Rt12 sh6Live ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 sh6 384 Rt12 sh6Live) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  assert (ms6Live : In (ms6, 24) (rt_live RT Σ6)) by (rewrite LvPost6; apply in_or_app; left; wp_in_lit).
  assert (ms6Heap : 17594333495296 <= ms6 /\ ms6 + 24 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ6 m12 ms6 24 Rt12 ms6Live ltac:(clear - Rt12; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ6 m12 ms6 24 Rt12 ms6Live) as Span.
    rewrite BasePost6, Base5 in Span. clear - Span LoInWin; lia. }
  rewrite Lv5 in LvPost6. rewrite ?app_assoc, ?app_comm_cons in LvPost6.
  match type of LvPost6 with _ = ?L ++ rt_live RT Σ => remember L as New6 eqn:New6Is in LvPost6 end.
  rename LvPost6 into Lv6.
  assert (NewLen6 : Z.of_nat (length New6) = 37)
    by (rewrite New6Is; rewrite ?length_app; cbn [length]; clear - NewLen5; lia).
  assert (NewPos6 : Forall (fun blk => 0 < snd blk) New6).
  { rewrite New6Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos5; lia | ] | apply Forall_nil | exact NewPos5 ]. }
  assert (NewBnd6 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New6).
  { rewrite New6Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(big6, 40); (lb6d, 40); (la6d, 40); (sa6d, 32); (lb6c, 40); (la6c, 40); (sa6c, 32); (lb6b, 40); (la6b, 40); (sa6b, 32); (lb6a, 40); (la6a, 40); (sa6a, 32); (sh6, 384); (ms6, 24)] ++ New5)). apply Forall_app. split; [exact Bnd6 | exact NewBnd5]. }
  assert (Fr6 : rt_frames RT Σ6 = rt_frames RT Σ) by (rewrite FrPost6; exact Fr5).
  assert (Base6 : rt_sp0 RT Σ6 = rt_sp0 RT Σ) by (rewrite BasePost6; exact Base5).
  assert (Gr6 : rt_cg RT Σ6 = rt_cg RT Σ) by (rewrite GrPost6; exact Gr5).
  assert (Cr6 : rt_credit RT Σ6 = rt_credit RT Σ - 23)
    by (rewrite CrPost6, Cr5; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost6 BasePost6 GrPost6 CrPost6 Lv5 NewLen5 NewPos5 NewBnd5 Bnd6 Fr5 Base5 Gr5 Cr5.
  assert (V6Word : 0 <= ms6 < 2 ^ 64) by (unfold USTACK_TOP in V6Top; clear - V6Pos V6Top; lia).
  assert (V6Nz : bv_eqb (Z_to_bv 64 ms6) (Z_to_bv 64 0) = false) by (clear - V6Word V6Pos; solve_cond_u).
  destruct (ConstsOf Σ6 m12 Rt12) as (ShBase12 & Clean12).
  pose proof (context_init_s6_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_6)
                r60 r61 r62 x61 x62 x63 x64 x65 x66 x67 r63 r64 r65 r66 lk1 ms3 cf4 rx5 ms6 j1
                g3 g5 g6 g7 g8 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F6 fc6 m12 lo) as Seg6.
  repeat match type of Seg6 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ6 m12 Rt12) | (apply (ShadowOf Σ6 m12); [exact Rt12 | clear - Rt12; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg6 ok); clear ok
         end.
  cl_lift Seg6 At12s cfg13 At13.
  destruct (ASTA_unpack RT Σ6 _ _ cfg13 At13) as (st13 & Post6 & At13s). clear At13 At12s.
  repeat match goal with
         | Old : rw_cells asegs m12 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post6 as (m13 & -> & Munch13 & Mono13 & Inv13
                     & FDecSt & FDrbg & FConf & FEvp & FLock & Frame13 & FComp
                     & FThr & FIndic & FSelfT & FLdrSt & FEncSt & FDecCa & FChild
                     & FBio & FNonce & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack13).
  repeat match goal with
         | Cell : rw_cells asegs m12 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m12 m13 X cs Cell Munch13
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt13 : ART RT Σ6 m13).
  { apply (cl_seg_ART RT AF Σ6 m12 m13 (bv_unsigned sp) 48 [(12187264, 12187272)] Rt12);
      [rewrite Base6; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch13 | | exact Mono13].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl13 : cl_env m13 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m12 m13 _ canary Cl12 Munch13); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above13 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m13).
  { intros w Hi. cbv beta in Hi. rewrite Munch13 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above12 w Hi). }
  assert (Kept13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m13).
  { apply (pres_fp_trans _ _ _ _ m m12 m13 Kept12).
    apply (PresGrow Σ6 (bv_unsigned sp) [(12187264, 12187272)] m12 m13);
      [rewrite Lv6; intros e Ein; apply in_or_app; right; exact Ein | exact Fr6 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ6 m12 m13 (bv_unsigned sp) 48 [(12187264, 12187272)] Rt12
             ltac:(rewrite Base6; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch13). }
  clear Kept12 Above12 Munch13 Mono13 Inv12 Rt12 Cl12 Stack12 ShBase12 Clean12.
  clear V6Pos V6Top V6Nz.
  (* call 7: ossl_decoder_cache_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_decoder_cache_new SITE_context_init_7 m m13 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_7, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_7, e_ossl_decoder_cache_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above13 (SavedOf m13 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain7 & FpChain7).
  match type of At13s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_decoder_cache_new Σ6 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m13 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr6, unsigned_lit by (unfold SITE_context_init_7; clear - Room0; lia); exact Chain7
             | rewrite Gr6, unsigned_lit by (unfold SITE_context_init_7; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr6; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr6; clear - FrmCap; lia
             | rewrite Lv6, length_app, Nat2Z.inj_add, NewLen6; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr6; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg14 (Σ7 & dc7 & dl7 & dq7 & dr7 & At14 & LvPost7 & FrPost7 & BasePost7 & CrPost7 & V7Pos & V7Al & V7Top & dl7Pos & dl7Al & dl7Top & dq7Pos & dq7Al & dq7Top & dr7Pos & dr7Al & dr7Top & GrPost7).
  destruct (ASTA_unpack RT Σ7 _ _ cfg14 At14) as (st14 & (m14 & Ret7 & After7 & Pres7 & Cl14 & Obj7) & At14s).
  clear At14 At13s.
  destruct Ret7 as (r70 & r71 & r72 & x71 & x72 & x73 & x74 & x75 & x76 & x77 & r73 & r74 & r75 & r76 & F7 & fc7 & ->).
  rewrite FrameLit in After7, Pres7. destruct After7 as (Rt14 & Inv14 & Mono14 & Stack14).
  rewrite (ret_pc_even SITE_context_init_7) in At14s by (unfold SITE_context_init_7; clear - Room0; lia).
  destruct Obj7 as (dc7Obj & _ & dl7Obj & _ & dq7Obj & _ & dr7Obj & _).
  repeat match goal with
         | Cell : rw_cells asegs m13 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m14 X cs);
             [ apply (rw_cells_agree_nw asegs m13 m14 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres7;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ6) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above14 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m14).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres7 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above13 w Hi). }
  assert (Kept14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m14).
  { apply (pres_fp_trans _ _ _ _ m m13 m14 Kept13).
    apply (PresGrow Σ6 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m13 m14);
      [rewrite Lv6; intros e Ein; apply in_or_app; right; exact Ein | exact Fr6 | clear - FrameLit; lia | | exact Pres7].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept13 Above13 Pres7 Mono14 Inv13 Rt13 Cl13 Stack13 Chain7 FpChain7.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ6) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ7)) by (rewrite LvPost7; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (dr7Live : In (dr7, 128) (rt_live RT Σ7)) by (rewrite LvPost7; wp_in_lit).
  assert (dr7Heap : 17594333495296 <= dr7 /\ dr7 + 128 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ7 m14 dr7 128 Rt14 dr7Live ltac:(clear - Rt14; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ7 m14 dr7 128 Rt14 dr7Live) as Span.
    rewrite BasePost7, Base6 in Span. clear - Span LoInWin; lia. }
  assert (dq7Live : In (dq7, 104) (rt_live RT Σ7)) by (rewrite LvPost7; wp_in_lit).
  assert (dq7Heap : 17594333495296 <= dq7 /\ dq7 + 104 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ7 m14 dq7 104 Rt14 dq7Live ltac:(clear - Rt14; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ7 m14 dq7 104 Rt14 dq7Live) as Span.
    rewrite BasePost7, Base6 in Span. clear - Span LoInWin; lia. }
  assert (dl7Live : In (dl7, 40) (rt_live RT Σ7)) by (rewrite LvPost7; wp_in_lit).
  assert (dl7Heap : 17594333495296 <= dl7 /\ dl7 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ7 m14 dl7 40 Rt14 dl7Live ltac:(clear - Rt14; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ7 m14 dl7 40 Rt14 dl7Live) as Span.
    rewrite BasePost7, Base6 in Span. clear - Span LoInWin; lia. }
  assert (dc7Live : In (dc7, 16) (rt_live RT Σ7)) by (rewrite LvPost7; wp_in_lit).
  assert (dc7Heap : 17594333495296 <= dc7 /\ dc7 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ7 m14 dc7 16 Rt14 dc7Live ltac:(clear - Rt14; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ7 m14 dc7 16 Rt14 dc7Live) as Span.
    rewrite BasePost7, Base6 in Span. clear - Span LoInWin; lia. }
  assert (Bnd7 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(dr7, 128); (dq7, 104); (dl7, 40); (dc7, 16)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V7Al dl7Pos dl7Al dl7Top dq7Pos dq7Al dq7Top dr7Pos dr7Al dr7Top.
  rewrite Lv6 in LvPost7. rewrite ?app_assoc, ?app_comm_cons in LvPost7.
  match type of LvPost7 with _ = ?L ++ rt_live RT Σ => remember L as New7 eqn:New7Is in LvPost7 end.
  rename LvPost7 into Lv7.
  assert (NewLen7 : Z.of_nat (length New7) = 41)
    by (rewrite New7Is; rewrite ?length_app; cbn [length]; clear - NewLen6; lia).
  assert (NewPos7 : Forall (fun blk => 0 < snd blk) New7).
  { rewrite New7Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos6; lia | ] | apply Forall_nil | exact NewPos6 ]. }
  assert (NewBnd7 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New7).
  { rewrite New7Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(dr7, 128); (dq7, 104); (dl7, 40); (dc7, 16)] ++ New6)). apply Forall_app. split; [exact Bnd7 | exact NewBnd6]. }
  assert (Fr7 : rt_frames RT Σ7 = rt_frames RT Σ) by (rewrite FrPost7; exact Fr6).
  assert (Base7 : rt_sp0 RT Σ7 = rt_sp0 RT Σ) by (rewrite BasePost7; exact Base6).
  assert (Gr7 : rt_cg RT Σ7 = rt_cg RT Σ) by (rewrite GrPost7; exact Gr6).
  assert (Cr7 : rt_credit RT Σ7 = rt_credit RT Σ - 24)
    by (rewrite CrPost7, Cr6; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost7 BasePost7 GrPost7 CrPost7 Lv6 NewLen6 NewPos6 NewBnd6 Bnd7 Fr6 Base6 Gr6 Cr6.
  assert (V7Word : 0 <= dc7 < 2 ^ 64) by (unfold USTACK_TOP in V7Top; clear - V7Pos V7Top; lia).
  assert (V7Nz : bv_eqb (Z_to_bv 64 dc7) (Z_to_bv 64 0) = false) by (clear - V7Word V7Pos; solve_cond_u).
  destruct (ConstsOf Σ7 m14 Rt14) as (ShBase14 & Clean14).
  pose proof (context_init_s7_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_7)
                r70 r71 r72 x71 x72 x73 x74 x75 x76 x77 r73 r74 r75 r76 lk1 ms3 cf4 rx5 ms6 dc7 j1
                g3 g5 g6 g7 g8 g10 g12 g13 g15 g16 g17 g18 g19 g20 g21 F7 fc7 m14 lo) as Seg7.
  repeat match type of Seg7 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ7 m14 Rt14) | (apply (ShadowOf Σ7 m14); [exact Rt14 | clear - Rt14; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg7 ok); clear ok
         end.
  cl_lift Seg7 At14s cfg15 At15.
  destruct (ASTA_unpack RT Σ7 _ _ cfg15 At15) as (st15 & Post7 & At15s). clear At15 At14s.
  repeat match goal with
         | Old : rw_cells asegs m14 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post7 as (m15 & -> & Munch15 & Mono15 & Inv15
                     & FDecCa & FDecSt & FDrbg & FConf & FEvp & FLock & Frame15
                     & FComp & FThr & FIndic & FSelfT & FLdrSt & FEncSt & FChild
                     & FBio & FNonce & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack15).
  repeat match goal with
         | Cell : rw_cells asegs m14 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m14 m15 X cs Cell Munch15
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt15 : ART RT Σ7 m15).
  { apply (cl_seg_ART RT AF Σ7 m14 m15 (bv_unsigned sp) 48 [(12187272, 12187280)] Rt14);
      [rewrite Base7; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch15 | | exact Mono15].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl15 : cl_env m15 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m14 m15 _ canary Cl14 Munch15); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above15 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m15).
  { intros w Hi. cbv beta in Hi. rewrite Munch15 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above14 w Hi). }
  assert (Kept15 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m15).
  { apply (pres_fp_trans _ _ _ _ m m14 m15 Kept14).
    apply (PresGrow Σ7 (bv_unsigned sp) [(12187272, 12187280)] m14 m15);
      [rewrite Lv7; intros e Ein; apply in_or_app; right; exact Ein | exact Fr7 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ7 m14 m15 (bv_unsigned sp) 48 [(12187272, 12187280)] Rt14
             ltac:(rewrite Base7; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch15). }
  clear Kept14 Above14 Munch15 Mono15 Inv14 Rt14 Cl14 Stack14 ShBase14 Clean14.
  clear V7Pos V7Top V7Nz.
  (* call 8: ossl_method_store_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_method_store_new SITE_context_init_8 m m15 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_8, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_8, e_ossl_method_store_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above15 (SavedOf m15 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain8 & FpChain8).
  match type of At15s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_method_store_new Σ7 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m15 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr7, unsigned_lit by (unfold SITE_context_init_8; clear - Room0; lia); exact Chain8
             | rewrite Gr7, unsigned_lit by (unfold SITE_context_init_8; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr7; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr7; clear - FrmCap; lia
             | rewrite Lv7, length_app, Nat2Z.inj_add, NewLen7; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr7; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg16 (Σ8 & ms8 & sh8 & sa8a & la8a & lb8a & sa8b & la8b & lb8b & sa8c & la8c & lb8c & sa8d & la8d & lb8d & big8 & At16 & LvPost8 & FrPost8 & BasePost8 & CrPost8 & Bnd8 & GrPost8).
  destruct (proj1 (Forall_forall _ _) Bnd8 (ms8, 24) ltac:(wp_in_lit)) as (V8Pos & V8Al & V8Top).
  cbn [fst snd] in V8Pos, V8Al, V8Top. clear V8Al.
  destruct (ASTA_unpack RT Σ8 _ _ cfg16 At16) as (st16 & (m16 & Ret8 & After8 & Pres8 & Cl16 & Obj8) & At16s).
  clear At16 At15s.
  destruct Ret8 as (r80 & r81 & r82 & x81 & x82 & x83 & x84 & x85 & x86 & x87 & r83 & r84 & r85 & r86 & F8 & fc8 & ->).
  rewrite FrameLit in After8, Pres8. destruct After8 as (Rt16 & Inv16 & Mono16 & Stack16).
  rewrite (ret_pc_even SITE_context_init_8) in At16s by (unfold SITE_context_init_8; clear - Room0; lia).
  destruct Obj8 as (ms8Obj & _ & sh8Obj & _ & SaAll8 & LkAll8).
  destruct (proj1 (Forall_forall _ _) SaAll8 sa8a ltac:(wp_in_lit)) as (sa8aObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll8 sa8b ltac:(wp_in_lit)) as (sa8bObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll8 sa8c ltac:(wp_in_lit)) as (sa8cObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll8 sa8d ltac:(wp_in_lit)) as (sa8dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 la8a ltac:(wp_in_lit)) as (la8aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 lb8a ltac:(wp_in_lit)) as (lb8aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 la8b ltac:(wp_in_lit)) as (la8bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 lb8b ltac:(wp_in_lit)) as (lb8bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 la8c ltac:(wp_in_lit)) as (la8cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 lb8c ltac:(wp_in_lit)) as (lb8cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 la8d ltac:(wp_in_lit)) as (la8dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 lb8d ltac:(wp_in_lit)) as (lb8dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll8 big8 ltac:(wp_in_lit)) as (big8Obj & _).
  clear SaAll8 LkAll8.
  repeat match goal with
         | Cell : rw_cells asegs m15 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m16 X cs);
             [ apply (rw_cells_agree_nw asegs m15 m16 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres8;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ7) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above16 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m16).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres8 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above15 w Hi). }
  assert (Kept16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m16).
  { apply (pres_fp_trans _ _ _ _ m m15 m16 Kept15).
    apply (PresGrow Σ7 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m15 m16);
      [rewrite Lv7; intros e Ein; apply in_or_app; right; exact Ein | exact Fr7 | clear - FrameLit; lia | | exact Pres8].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept15 Above15 Pres8 Mono16 Inv15 Rt15 Cl15 Stack15 Chain8 FpChain8.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ7) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ8)) by (rewrite LvPost8; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (big8Live : In (big8, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (big8Heap : 17594333495296 <= big8 /\ big8 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 big8 40 Rt16 big8Live ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 big8 40 Rt16 big8Live) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (lb8dLive : In (lb8d, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (lb8dHeap : 17594333495296 <= lb8d /\ lb8d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 lb8d 40 Rt16 lb8dLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 lb8d 40 Rt16 lb8dLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (la8dLive : In (la8d, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (la8dHeap : 17594333495296 <= la8d /\ la8d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 la8d 40 Rt16 la8dLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 la8d 40 Rt16 la8dLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (sa8dLive : In (sa8d, 32) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (sa8dHeap : 17594333495296 <= sa8d /\ sa8d + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 sa8d 32 Rt16 sa8dLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 sa8d 32 Rt16 sa8dLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (lb8cLive : In (lb8c, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (lb8cHeap : 17594333495296 <= lb8c /\ lb8c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 lb8c 40 Rt16 lb8cLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 lb8c 40 Rt16 lb8cLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (la8cLive : In (la8c, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (la8cHeap : 17594333495296 <= la8c /\ la8c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 la8c 40 Rt16 la8cLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 la8c 40 Rt16 la8cLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (sa8cLive : In (sa8c, 32) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (sa8cHeap : 17594333495296 <= sa8c /\ sa8c + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 sa8c 32 Rt16 sa8cLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 sa8c 32 Rt16 sa8cLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (lb8bLive : In (lb8b, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (lb8bHeap : 17594333495296 <= lb8b /\ lb8b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 lb8b 40 Rt16 lb8bLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 lb8b 40 Rt16 lb8bLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (la8bLive : In (la8b, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (la8bHeap : 17594333495296 <= la8b /\ la8b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 la8b 40 Rt16 la8bLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 la8b 40 Rt16 la8bLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (sa8bLive : In (sa8b, 32) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (sa8bHeap : 17594333495296 <= sa8b /\ sa8b + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 sa8b 32 Rt16 sa8bLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 sa8b 32 Rt16 sa8bLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (lb8aLive : In (lb8a, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (lb8aHeap : 17594333495296 <= lb8a /\ lb8a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 lb8a 40 Rt16 lb8aLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 lb8a 40 Rt16 lb8aLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (la8aLive : In (la8a, 40) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (la8aHeap : 17594333495296 <= la8a /\ la8a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 la8a 40 Rt16 la8aLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 la8a 40 Rt16 la8aLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (sa8aLive : In (sa8a, 32) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (sa8aHeap : 17594333495296 <= sa8a /\ sa8a + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 sa8a 32 Rt16 sa8aLive ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 sa8a 32 Rt16 sa8aLive) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (sh8Live : In (sh8, 384) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (sh8Heap : 17594333495296 <= sh8 /\ sh8 + 384 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 sh8 384 Rt16 sh8Live ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 sh8 384 Rt16 sh8Live) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  assert (ms8Live : In (ms8, 24) (rt_live RT Σ8)) by (rewrite LvPost8; apply in_or_app; left; wp_in_lit).
  assert (ms8Heap : 17594333495296 <= ms8 /\ ms8 + 24 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ8 m16 ms8 24 Rt16 ms8Live ltac:(clear - Rt16; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ8 m16 ms8 24 Rt16 ms8Live) as Span.
    rewrite BasePost8, Base7 in Span. clear - Span LoInWin; lia. }
  rewrite Lv7 in LvPost8. rewrite ?app_assoc, ?app_comm_cons in LvPost8.
  match type of LvPost8 with _ = ?L ++ rt_live RT Σ => remember L as New8 eqn:New8Is in LvPost8 end.
  rename LvPost8 into Lv8.
  assert (NewLen8 : Z.of_nat (length New8) = 56)
    by (rewrite New8Is; rewrite ?length_app; cbn [length]; clear - NewLen7; lia).
  assert (NewPos8 : Forall (fun blk => 0 < snd blk) New8).
  { rewrite New8Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos7; lia | ] | apply Forall_nil | exact NewPos7 ]. }
  assert (NewBnd8 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New8).
  { rewrite New8Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(big8, 40); (lb8d, 40); (la8d, 40); (sa8d, 32); (lb8c, 40); (la8c, 40); (sa8c, 32); (lb8b, 40); (la8b, 40); (sa8b, 32); (lb8a, 40); (la8a, 40); (sa8a, 32); (sh8, 384); (ms8, 24)] ++ New7)). apply Forall_app. split; [exact Bnd8 | exact NewBnd7]. }
  assert (Fr8 : rt_frames RT Σ8 = rt_frames RT Σ) by (rewrite FrPost8; exact Fr7).
  assert (Base8 : rt_sp0 RT Σ8 = rt_sp0 RT Σ) by (rewrite BasePost8; exact Base7).
  assert (Gr8 : rt_cg RT Σ8 = rt_cg RT Σ) by (rewrite GrPost8; exact Gr7).
  assert (Cr8 : rt_credit RT Σ8 = rt_credit RT Σ - 33)
    by (rewrite CrPost8, Cr7; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost8 BasePost8 GrPost8 CrPost8 Lv7 NewLen7 NewPos7 NewBnd7 Bnd8 Fr7 Base7 Gr7 Cr7.
  assert (V8Word : 0 <= ms8 < 2 ^ 64) by (unfold USTACK_TOP in V8Top; clear - V8Pos V8Top; lia).
  assert (V8Nz : bv_eqb (Z_to_bv 64 ms8) (Z_to_bv 64 0) = false) by (clear - V8Word V8Pos; solve_cond_u).
  destruct (ConstsOf Σ8 m16 Rt16) as (ShBase16 & Clean16).
  pose proof (context_init_s8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_8)
                r80 r81 r82 x81 x82 x83 x84 x85 x86 x87 r83 r84 r85 r86 lk1 ms3 cf4 rx5 ms6 dc7 ms8 j1
                g3 g5 g6 g7 g8 g10 g12 g13 g16 g17 g18 g19 g20 g21 F8 fc8 m16 lo) as Seg8.
  repeat match type of Seg8 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ8 m16 Rt16) | (apply (ShadowOf Σ8 m16); [exact Rt16 | clear - Rt16; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg8 ok); clear ok
         end.
  cl_lift Seg8 At16s cfg17 At17.
  destruct (ASTA_unpack RT Σ8 _ _ cfg17 At17) as (st17 & Post8 & At17s). clear At17 At16s.
  repeat match goal with
         | Old : rw_cells asegs m16 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post8 as (m17 & -> & Munch17 & Mono17 & Inv17
                     & FEncSt & FDecCa & FDecSt & FDrbg & FConf & FEvp & FLock
                     & Frame17 & FComp & FThr & FIndic & FSelfT & FLdrSt & FChild
                     & FBio & FNonce & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack17).
  repeat match goal with
         | Cell : rw_cells asegs m16 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m16 m17 X cs Cell Munch17
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt17 : ART RT Σ8 m17).
  { apply (cl_seg_ART RT AF Σ8 m16 m17 (bv_unsigned sp) 48 [(12187280, 12187288)] Rt16);
      [rewrite Base8; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch17 | | exact Mono17].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl17 : cl_env m17 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m16 m17 _ canary Cl16 Munch17); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above17 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m17).
  { intros w Hi. cbv beta in Hi. rewrite Munch17 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above16 w Hi). }
  assert (Kept17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m17).
  { apply (pres_fp_trans _ _ _ _ m m16 m17 Kept16).
    apply (PresGrow Σ8 (bv_unsigned sp) [(12187280, 12187288)] m16 m17);
      [rewrite Lv8; intros e Ein; apply in_or_app; right; exact Ein | exact Fr8 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ8 m16 m17 (bv_unsigned sp) 48 [(12187280, 12187288)] Rt16
             ltac:(rewrite Base8; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch17). }
  clear Kept16 Above16 Munch17 Mono17 Inv16 Rt16 Cl16 Stack16 ShBase16 Clean16.
  clear V8Pos V8Top V8Nz.
  (* call 9: ossl_method_store_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_method_store_new SITE_context_init_9 m m17 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_9, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_9, e_ossl_method_store_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above17 (SavedOf m17 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain9 & FpChain9).
  match type of At17s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_method_store_new Σ8 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m17 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr8, unsigned_lit by (unfold SITE_context_init_9; clear - Room0; lia); exact Chain9
             | rewrite Gr8, unsigned_lit by (unfold SITE_context_init_9; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr8; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr8; clear - FrmCap; lia
             | rewrite Lv8, length_app, Nat2Z.inj_add, NewLen8; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr8; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg18 (Σ9 & ms9 & sh9 & sa9a & la9a & lb9a & sa9b & la9b & lb9b & sa9c & la9c & lb9c & sa9d & la9d & lb9d & big9 & At18 & LvPost9 & FrPost9 & BasePost9 & CrPost9 & Bnd9 & GrPost9).
  destruct (proj1 (Forall_forall _ _) Bnd9 (ms9, 24) ltac:(wp_in_lit)) as (V9Pos & V9Al & V9Top).
  cbn [fst snd] in V9Pos, V9Al, V9Top. clear V9Al.
  destruct (ASTA_unpack RT Σ9 _ _ cfg18 At18) as (st18 & (m18 & Ret9 & After9 & Pres9 & Cl18 & Obj9) & At18s).
  clear At18 At17s.
  destruct Ret9 as (r90 & r91 & r92 & x91 & x92 & x93 & x94 & x95 & x96 & x97 & r93 & r94 & r95 & r96 & F9 & fc9 & ->).
  rewrite FrameLit in After9, Pres9. destruct After9 as (Rt18 & Inv18 & Mono18 & Stack18).
  rewrite (ret_pc_even SITE_context_init_9) in At18s by (unfold SITE_context_init_9; clear - Room0; lia).
  destruct Obj9 as (ms9Obj & _ & sh9Obj & _ & SaAll9 & LkAll9).
  destruct (proj1 (Forall_forall _ _) SaAll9 sa9a ltac:(wp_in_lit)) as (sa9aObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll9 sa9b ltac:(wp_in_lit)) as (sa9bObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll9 sa9c ltac:(wp_in_lit)) as (sa9cObj & _).
  destruct (proj1 (Forall_forall _ _) SaAll9 sa9d ltac:(wp_in_lit)) as (sa9dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 la9a ltac:(wp_in_lit)) as (la9aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 lb9a ltac:(wp_in_lit)) as (lb9aObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 la9b ltac:(wp_in_lit)) as (la9bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 lb9b ltac:(wp_in_lit)) as (lb9bObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 la9c ltac:(wp_in_lit)) as (la9cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 lb9c ltac:(wp_in_lit)) as (lb9cObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 la9d ltac:(wp_in_lit)) as (la9dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 lb9d ltac:(wp_in_lit)) as (lb9dObj & _).
  destruct (proj1 (Forall_forall _ _) LkAll9 big9 ltac:(wp_in_lit)) as (big9Obj & _).
  clear SaAll9 LkAll9.
  repeat match goal with
         | Cell : rw_cells asegs m17 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m18 X cs);
             [ apply (rw_cells_agree_nw asegs m17 m18 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres9;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ8) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above18 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m18).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres9 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above17 w Hi). }
  assert (Kept18 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m18).
  { apply (pres_fp_trans _ _ _ _ m m17 m18 Kept17).
    apply (PresGrow Σ8 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m17 m18);
      [rewrite Lv8; intros e Ein; apply in_or_app; right; exact Ein | exact Fr8 | clear - FrameLit; lia | | exact Pres9].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept17 Above17 Pres9 Mono18 Inv17 Rt17 Cl17 Stack17 Chain9 FpChain9.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ8) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ9)) by (rewrite LvPost9; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (big9Live : In (big9, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (big9Heap : 17594333495296 <= big9 /\ big9 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 big9 40 Rt18 big9Live ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 big9 40 Rt18 big9Live) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (lb9dLive : In (lb9d, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (lb9dHeap : 17594333495296 <= lb9d /\ lb9d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 lb9d 40 Rt18 lb9dLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 lb9d 40 Rt18 lb9dLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (la9dLive : In (la9d, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (la9dHeap : 17594333495296 <= la9d /\ la9d + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 la9d 40 Rt18 la9dLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 la9d 40 Rt18 la9dLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (sa9dLive : In (sa9d, 32) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (sa9dHeap : 17594333495296 <= sa9d /\ sa9d + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 sa9d 32 Rt18 sa9dLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 sa9d 32 Rt18 sa9dLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (lb9cLive : In (lb9c, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (lb9cHeap : 17594333495296 <= lb9c /\ lb9c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 lb9c 40 Rt18 lb9cLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 lb9c 40 Rt18 lb9cLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (la9cLive : In (la9c, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (la9cHeap : 17594333495296 <= la9c /\ la9c + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 la9c 40 Rt18 la9cLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 la9c 40 Rt18 la9cLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (sa9cLive : In (sa9c, 32) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (sa9cHeap : 17594333495296 <= sa9c /\ sa9c + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 sa9c 32 Rt18 sa9cLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 sa9c 32 Rt18 sa9cLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (lb9bLive : In (lb9b, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (lb9bHeap : 17594333495296 <= lb9b /\ lb9b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 lb9b 40 Rt18 lb9bLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 lb9b 40 Rt18 lb9bLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (la9bLive : In (la9b, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (la9bHeap : 17594333495296 <= la9b /\ la9b + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 la9b 40 Rt18 la9bLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 la9b 40 Rt18 la9bLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (sa9bLive : In (sa9b, 32) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (sa9bHeap : 17594333495296 <= sa9b /\ sa9b + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 sa9b 32 Rt18 sa9bLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 sa9b 32 Rt18 sa9bLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (lb9aLive : In (lb9a, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (lb9aHeap : 17594333495296 <= lb9a /\ lb9a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 lb9a 40 Rt18 lb9aLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 lb9a 40 Rt18 lb9aLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (la9aLive : In (la9a, 40) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (la9aHeap : 17594333495296 <= la9a /\ la9a + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 la9a 40 Rt18 la9aLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 la9a 40 Rt18 la9aLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (sa9aLive : In (sa9a, 32) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (sa9aHeap : 17594333495296 <= sa9a /\ sa9a + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 sa9a 32 Rt18 sa9aLive ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 sa9a 32 Rt18 sa9aLive) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (sh9Live : In (sh9, 384) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (sh9Heap : 17594333495296 <= sh9 /\ sh9 + 384 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 sh9 384 Rt18 sh9Live ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 sh9 384 Rt18 sh9Live) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  assert (ms9Live : In (ms9, 24) (rt_live RT Σ9)) by (rewrite LvPost9; apply in_or_app; left; wp_in_lit).
  assert (ms9Heap : 17594333495296 <= ms9 /\ ms9 + 24 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ9 m18 ms9 24 Rt18 ms9Live ltac:(clear - Rt18; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ9 m18 ms9 24 Rt18 ms9Live) as Span.
    rewrite BasePost9, Base8 in Span. clear - Span LoInWin; lia. }
  rewrite Lv8 in LvPost9. rewrite ?app_assoc, ?app_comm_cons in LvPost9.
  match type of LvPost9 with _ = ?L ++ rt_live RT Σ => remember L as New9 eqn:New9Is in LvPost9 end.
  rename LvPost9 into Lv9.
  assert (NewLen9 : Z.of_nat (length New9) = 71)
    by (rewrite New9Is; rewrite ?length_app; cbn [length]; clear - NewLen8; lia).
  assert (NewPos9 : Forall (fun blk => 0 < snd blk) New9).
  { rewrite New9Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos8; lia | ] | apply Forall_nil | exact NewPos8 ]. }
  assert (NewBnd9 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New9).
  { rewrite New9Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(big9, 40); (lb9d, 40); (la9d, 40); (sa9d, 32); (lb9c, 40); (la9c, 40); (sa9c, 32); (lb9b, 40); (la9b, 40); (sa9b, 32); (lb9a, 40); (la9a, 40); (sa9a, 32); (sh9, 384); (ms9, 24)] ++ New8)). apply Forall_app. split; [exact Bnd9 | exact NewBnd8]. }
  assert (Fr9 : rt_frames RT Σ9 = rt_frames RT Σ) by (rewrite FrPost9; exact Fr8).
  assert (Base9 : rt_sp0 RT Σ9 = rt_sp0 RT Σ) by (rewrite BasePost9; exact Base8).
  assert (Gr9 : rt_cg RT Σ9 = rt_cg RT Σ) by (rewrite GrPost9; exact Gr8).
  assert (Cr9 : rt_credit RT Σ9 = rt_credit RT Σ - 42)
    by (rewrite CrPost9, Cr8; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost9 BasePost9 GrPost9 CrPost9 Lv8 NewLen8 NewPos8 NewBnd8 Bnd9 Fr8 Base8 Gr8 Cr8.
  assert (V9Word : 0 <= ms9 < 2 ^ 64) by (unfold USTACK_TOP in V9Top; clear - V9Pos V9Top; lia).
  assert (V9Nz : bv_eqb (Z_to_bv 64 ms9) (Z_to_bv 64 0) = false) by (clear - V9Word V9Pos; solve_cond_u).
  destruct (ConstsOf Σ9 m18 Rt18) as (ShBase18 & Clean18).
  pose proof (context_init_s9_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_9)
                r90 r91 r92 x91 x92 x93 x94 x95 x96 x97 r93 r94 r95 r96 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 j1
                g3 g5 g6 g7 g8 g10 g12 g13 g17 g18 g19 g20 g21 F9 fc9 m18 lo) as Seg9.
  repeat match type of Seg9 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ9 m18 Rt18) | (apply (ShadowOf Σ9 m18); [exact Rt18 | clear - Rt18; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg9 ok); clear ok
         end.
  cl_lift Seg9 At18s cfg19 At19.
  destruct (ASTA_unpack RT Σ9 _ _ cfg19 At19) as (st19 & Post9 & At19s). clear At19 At18s.
  repeat match goal with
         | Old : rw_cells asegs m18 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post9 as (m19 & -> & Munch19 & Mono19 & Inv19
                     & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg & FConf & FEvp
                     & FLock & Frame19 & FComp & FThr & FIndic & FSelfT & FChild
                     & FBio & FNonce & FGprops & FDefns & FNmap & FProvSt & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack19).
  repeat match goal with
         | Cell : rw_cells asegs m18 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m18 m19 X cs Cell Munch19
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt19 : ART RT Σ9 m19).
  { apply (cl_seg_ART RT AF Σ9 m18 m19 (bv_unsigned sp) 48 [(12187288, 12187296)] Rt18);
      [rewrite Base9; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch19 | | exact Mono19].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl19 : cl_env m19 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m18 m19 _ canary Cl18 Munch19); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above19 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m19).
  { intros w Hi. cbv beta in Hi. rewrite Munch19 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above18 w Hi). }
  assert (Kept19 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m19).
  { apply (pres_fp_trans _ _ _ _ m m18 m19 Kept18).
    apply (PresGrow Σ9 (bv_unsigned sp) [(12187288, 12187296)] m18 m19);
      [rewrite Lv9; intros e Ein; apply in_or_app; right; exact Ein | exact Fr9 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ9 m18 m19 (bv_unsigned sp) 48 [(12187288, 12187296)] Rt18
             ltac:(rewrite Base9; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch19). }
  clear Kept18 Above18 Munch19 Mono19 Inv18 Rt18 Cl18 Stack18 ShBase18 Clean18.
  clear V9Pos V9Top V9Nz.
  (* call 10: ossl_provider_store_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_provider_store_new SITE_context_init_10 m m19 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_10, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_10, e_ossl_provider_store_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above19 (SavedOf m19 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain10 & FpChain10).
  match type of At19s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_provider_store_new Σ9 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m19 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr9, unsigned_lit by (unfold SITE_context_init_10; clear - Room0; lia); exact Chain10
             | rewrite Gr9, unsigned_lit by (unfold SITE_context_init_10; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr9; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr9; clear - FrmCap; lia
             | rewrite Lv9, length_app, Nat2Z.inj_add, NewLen9; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr9; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg20 (Σ10 & pv10 & pp10 & pd10 & pc10 & pk10 & At20 & LvPost10 & FrPost10 & BasePost10 & CrPost10 & V10Pos & V10Al & V10Top & pp10Al & pd10Al & pc10Al & pk10Al & GrPost10).
  destruct (ASTA_unpack RT Σ10 _ _ cfg20 At20) as (st20 & (m20 & Ret10 & After10 & Pres10 & Cl20 & Obj10) & At20s).
  clear At20 At19s.
  destruct Ret10 as (r100 & r101 & r102 & x101 & x102 & x103 & x104 & x105 & x106 & x107 & r103 & r104 & r105 & r106 & F10 & fc10 & ->).
  rewrite FrameLit in After10, Pres10. destruct After10 as (Rt20 & Inv20 & Mono20 & Stack20).
  rewrite (ret_pc_even SITE_context_init_10) in At20s by (unfold SITE_context_init_10; clear - Room0; lia).
  destruct Obj10 as (_ & _ & pv10Obj & pp10Obj & pd10Obj & pc10Obj & pk10Obj).
  repeat match goal with
         | Cell : rw_cells asegs m19 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m20 X cs);
             [ apply (rw_cells_agree_nw asegs m19 m20 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres10;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ9) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above20 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m20).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres10 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above19 w Hi). }
  assert (Kept20 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m20).
  { apply (pres_fp_trans _ _ _ _ m m19 m20 Kept19).
    apply (PresGrow Σ9 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m19 m20);
      [rewrite Lv9; intros e Ein; apply in_or_app; right; exact Ein | exact Fr9 | clear - FrameLit; lia | | exact Pres10].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept19 Above19 Pres10 Mono20 Inv19 Rt19 Cl19 Stack19 Chain10 FpChain10.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ9) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ10)) by (rewrite LvPost10; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (pk10Live : In (pk10, 40) (rt_live RT Σ10)) by (rewrite LvPost10; wp_in_lit).
  assert (pk10Heap : 17594333495296 <= pk10 /\ pk10 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ10 m20 pk10 40 Rt20 pk10Live ltac:(clear - Rt20; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ10 m20 pk10 40 Rt20 pk10Live) as Span.
    rewrite BasePost10, Base9 in Span. clear - Span LoInWin; lia. }
  assert (pc10Live : In (pc10, 56) (rt_live RT Σ10)) by (rewrite LvPost10; wp_in_lit).
  assert (pc10Heap : 17594333495296 <= pc10 /\ pc10 + 56 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ10 m20 pc10 56 Rt20 pc10Live ltac:(clear - Rt20; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ10 m20 pc10 56 Rt20 pc10Live) as Span.
    rewrite BasePost10, Base9 in Span. clear - Span LoInWin; lia. }
  assert (pd10Live : In (pd10, 40) (rt_live RT Σ10)) by (rewrite LvPost10; wp_in_lit).
  assert (pd10Heap : 17594333495296 <= pd10 /\ pd10 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ10 m20 pd10 40 Rt20 pd10Live ltac:(clear - Rt20; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ10 m20 pd10 40 Rt20 pd10Live) as Span.
    rewrite BasePost10, Base9 in Span. clear - Span LoInWin; lia. }
  assert (pp10Live : In (pp10, 56) (rt_live RT Σ10)) by (rewrite LvPost10; wp_in_lit).
  assert (pp10Heap : 17594333495296 <= pp10 /\ pp10 + 56 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ10 m20 pp10 56 Rt20 pp10Live ltac:(clear - Rt20; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ10 m20 pp10 56 Rt20 pp10Live) as Span.
    rewrite BasePost10, Base9 in Span. clear - Span LoInWin; lia. }
  assert (pv10Live : In (pv10, 80) (rt_live RT Σ10)) by (rewrite LvPost10; wp_in_lit).
  assert (pv10Heap : 17594333495296 <= pv10 /\ pv10 + 80 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ10 m20 pv10 80 Rt20 pv10Live ltac:(clear - Rt20; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ10 m20 pv10 80 Rt20 pv10Live) as Span.
    rewrite BasePost10, Base9 in Span. clear - Span LoInWin; lia. }
  assert (Bnd10 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(pk10, 40); (pc10, 56); (pd10, 40); (pp10, 56); (pv10, 80)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V10Al pp10Al pd10Al pc10Al pk10Al.
  rewrite Lv9 in LvPost10. rewrite ?app_assoc, ?app_comm_cons in LvPost10.
  match type of LvPost10 with _ = ?L ++ rt_live RT Σ => remember L as New10 eqn:New10Is in LvPost10 end.
  rename LvPost10 into Lv10.
  assert (NewLen10 : Z.of_nat (length New10) = 76)
    by (rewrite New10Is; rewrite ?length_app; cbn [length]; clear - NewLen9; lia).
  assert (NewPos10 : Forall (fun blk => 0 < snd blk) New10).
  { rewrite New10Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos9; lia | ] | apply Forall_nil | exact NewPos9 ]. }
  assert (NewBnd10 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New10).
  { rewrite New10Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(pk10, 40); (pc10, 56); (pd10, 40); (pp10, 56); (pv10, 80)] ++ New9)). apply Forall_app. split; [exact Bnd10 | exact NewBnd9]. }
  assert (Fr10 : rt_frames RT Σ10 = rt_frames RT Σ) by (rewrite FrPost10; exact Fr9).
  assert (Base10 : rt_sp0 RT Σ10 = rt_sp0 RT Σ) by (rewrite BasePost10; exact Base9).
  assert (Gr10 : rt_cg RT Σ10 = rt_cg RT Σ) by (rewrite GrPost10; exact Gr9).
  assert (Cr10 : rt_credit RT Σ10 = rt_credit RT Σ - 44)
    by (rewrite CrPost10, Cr9; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost10 BasePost10 GrPost10 CrPost10 Lv9 NewLen9 NewPos9 NewBnd9 Bnd10 Fr9 Base9 Gr9 Cr9.
  assert (V10Word : 0 <= pv10 < 2 ^ 64) by (unfold USTACK_TOP in V10Top; clear - V10Pos V10Top; lia).
  assert (V10Nz : bv_eqb (Z_to_bv 64 pv10) (Z_to_bv 64 0) = false) by (clear - V10Word V10Pos; solve_cond_u).
  destruct (ConstsOf Σ10 m20 Rt20) as (ShBase20 & Clean20).
  pose proof (context_init_s10_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_10)
                r100 r101 r102 x101 x102 x103 x104 x105 x106 x107 r103 r104 r105 r106 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 j1
                g3 g5 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F10 fc10 m20 lo) as Seg10.
  repeat match type of Seg10 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ10 m20 Rt20) | (apply (ShadowOf Σ10 m20); [exact Rt20 | clear - Rt20; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg10 ok); clear ok
         end.
  cl_lift Seg10 At20s cfg21 At21.
  destruct (ASTA_unpack RT Σ10 _ _ cfg21 At21) as (st21 & Post10 & At21s). clear At21 At20s.
  repeat match goal with
         | Old : rw_cells asegs m20 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post10 as (m21 & -> & Munch21 & Mono21 & Inv21
                     & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg & FConf
                     & FEvp & FLock & Frame21 & FComp & FThr & FIndic & FSelfT
                     & FChild & FBio & FNonce & FGprops & FDefns & FNmap & FPsd
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack21).
  repeat match goal with
         | Cell : rw_cells asegs m20 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m20 m21 X cs Cell Munch21
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt21 : ART RT Σ10 m21).
  { apply (cl_seg_ART RT AF Σ10 m20 m21 (bv_unsigned sp) 48 [(12187192, 12187200)] Rt20);
      [rewrite Base10; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch21 | | exact Mono21].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl21 : cl_env m21 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m20 m21 _ canary Cl20 Munch21); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above21 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m21).
  { intros w Hi. cbv beta in Hi. rewrite Munch21 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above20 w Hi). }
  assert (Kept21 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m21).
  { apply (pres_fp_trans _ _ _ _ m m20 m21 Kept20).
    apply (PresGrow Σ10 (bv_unsigned sp) [(12187192, 12187200)] m20 m21);
      [rewrite Lv10; intros e Ein; apply in_or_app; right; exact Ein | exact Fr10 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ10 m20 m21 (bv_unsigned sp) 48 [(12187192, 12187200)] Rt20
             ltac:(rewrite Base10; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch21). }
  clear Kept20 Above20 Munch21 Mono21 Inv20 Rt20 Cl20 Stack20 ShBase20 Clean20.
  clear V10Pos V10Top V10Nz.
  (* call 11: ossl_property_string_data_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_property_string_data_new SITE_context_init_11 m m21 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_11, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_11, e_ossl_property_string_data_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above21 (SavedOf m21 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain11 & FpChain11).
  match type of At21s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_property_string_data_new Σ10 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m21 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr10, unsigned_lit by (unfold SITE_context_init_11; clear - Room0; lia); exact Chain11
             | rewrite Gr10, unsigned_lit by (unfold SITE_context_init_11; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr10; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr10; clear - FrmCap; lia
             | rewrite Lv10, length_app, Nat2Z.inj_add, NewLen10; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr10; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg22 (Σ11 & ps11 & pk11 & pla11 & pba11 & plb11 & pbb11 & pqa11 & pqb11 & At22 & LvPost11 & FrPost11 & BasePost11 & CrPost11 & V11Pos & V11Al & V11Top & PkPos & PkAl & PkTop & PlaPos & PlaAl & PlaTop & PbaPos & PbaAl & PbaTop & PlbPos & PlbAl & PlbTop & PbbPos & PbbAl & PbbTop & PqaPos & PqaAl & PqaTop & PqbPos & PqbAl & PqbTop & GrPost11).
  destruct (ASTA_unpack RT Σ11 _ _ cfg22 At22) as (st22 & (m22 & Ret11 & After11 & Pres11 & Cl22 & Obj11) & At22s).
  clear At22 At21s.
  destruct Ret11 as (r110 & r111 & r112 & x111 & x112 & x113 & x114 & x115 & x116 & x117 & r113 & r114 & r115 & r116 & F11 & fc11 & ->).
  rewrite FrameLit in After11, Pres11. destruct After11 as (Rt22 & Inv22 & Mono22 & Stack22).
  rewrite (ret_pc_even SITE_context_init_11) in At22s by (unfold SITE_context_init_11; clear - Room0; lia).
  repeat match goal with
         | Cell : rw_cells asegs m21 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m22 X cs);
             [ apply (rw_cells_agree_nw asegs m21 m22 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres11;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ10) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above22 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m22).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres11 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above21 w Hi). }
  assert (Kept22 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m22).
  { apply (pres_fp_trans _ _ _ _ m m21 m22 Kept21).
    apply (PresGrow Σ10 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m21 m22);
      [rewrite Lv10; intros e Ein; apply in_or_app; right; exact Ein | exact Fr10 | clear - FrameLit; lia | | exact Pres11].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept21 Above21 Pres11 Mono22 Inv21 Rt21 Cl21 Stack21 Chain11 FpChain11.
  repeat match goal with
         | Mem : In (?X, ?n) (rt_live RT Σ10) |- _ =>
             lazymatch goal with
             | _ : forall w, X <= w < X + n -> outside _ w |- _ => fail
             | Hp : 17594333495296 <= X /\ _ |- _ =>
                 let Ap := fresh X "Apart" in
                 assert (Ap : forall w, X <= w < X + n -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w);
                 [ intros w InX;
                   pose proof (acl_live (rt_live RT Σ10) (rt_frames RT Σ10) (bv_unsigned sp) X n w Mem InX) as Acl;
                   cbn [outside]; unfold G_ALLOW_CUST;
                   repeat (split; [ first [ clear - InX Hp; lia
                                          | apply (wg_newchunk_apart RT AF Σ10 Σ11 m22 [(pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104); (pba11, 128); (pla11, 104); (pk11, 40); (ps11, 48)] _ _ (bv_unsigned sp) w Rt22 LvPost11);
                                            [ wp_in_lit | exact FrPost11 | exact BasePost11
                                            | rewrite Base10; clear - LoInWin Room0; lia | clear - InX; lia | exact Acl ] ] |]);
                   exact I
                 | ]
             end
         end.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ10) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ11)) by (rewrite LvPost11; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (Bnd11 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104); (pba11, 128); (pla11, 104); (pk11, 40); (ps11, 48)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  rewrite Lv10 in LvPost11. rewrite ?app_assoc, ?app_comm_cons in LvPost11.
  match type of LvPost11 with _ = ?L ++ rt_live RT Σ => remember L as New11 eqn:New11Is in LvPost11 end.
  rename LvPost11 into Lv11.
  assert (NewLen11 : Z.of_nat (length New11) = 84)
    by (rewrite New11Is; rewrite ?length_app; cbn [length]; clear - NewLen10; lia).
  assert (NewPos11 : Forall (fun blk => 0 < snd blk) New11).
  { rewrite New11Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos10; lia | ] | apply Forall_nil | exact NewPos10 ]. }
  assert (NewBnd11 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New11).
  { rewrite New11Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104); (pba11, 128); (pla11, 104); (pk11, 40); (ps11, 48)] ++ New10)). apply Forall_app. split; [exact Bnd11 | exact NewBnd10]. }
  assert (Fr11 : rt_frames RT Σ11 = rt_frames RT Σ) by (rewrite FrPost11; exact Fr10).
  assert (Base11 : rt_sp0 RT Σ11 = rt_sp0 RT Σ) by (rewrite BasePost11; exact Base10).
  assert (Gr11 : rt_cg RT Σ11 = rt_cg RT Σ) by (rewrite GrPost11; exact Gr10).
  assert (Cr11 : rt_credit RT Σ11 = rt_credit RT Σ - 45)
    by (rewrite CrPost11, Cr10; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost11 BasePost11 GrPost11 CrPost11 Lv10 NewLen10 NewPos10 NewBnd10 Bnd11 Fr10 Base10 Gr10 Cr10.
  (* what ossl_property_parse_init will need of these objects: where they are, and that they are apart *)
  destruct Obj11 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PsObj & PkObj & PlaObj & PbaObj & PlbObj & PbbObj & PqaObj & PqbObj).
  assert (Sub11_11 : incl New11 (rt_live RT Σ11)) by (intros e Ein; rewrite Lv11; apply in_or_app; left; exact Ein).
  assert (PsIn : In (ps11, 48) New11) by (rewrite New11Is; wp_in_lit).
  assert (PsHi : 17594333495296 <= ps11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 ps11 48 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PsIn) ltac:(clear - Rt22; lia)).
  assert (PsLow : ps11 + 48 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 ps11 48 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PsIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PkIn : In (pk11, 40) New11) by (rewrite New11Is; wp_in_lit).
  assert (PkHi : 17594333495296 <= pk11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pk11 40 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PkIn) ltac:(clear - Rt22; lia)).
  assert (PkLow : pk11 + 40 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pk11 40 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PkIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PlaIn : In (pla11, 104) New11) by (rewrite New11Is; wp_in_lit).
  assert (PlaHi : 17594333495296 <= pla11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pla11 104 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PlaIn) ltac:(clear - Rt22; lia)).
  assert (PlaLow : pla11 + 104 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pla11 104 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PlaIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PbaIn : In (pba11, 128) New11) by (rewrite New11Is; wp_in_lit).
  assert (PbaHi : 17594333495296 <= pba11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pba11 128 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PbaIn) ltac:(clear - Rt22; lia)).
  assert (PbaLow : pba11 + 128 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pba11 128 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PbaIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PlbIn : In (plb11, 104) New11) by (rewrite New11Is; wp_in_lit).
  assert (PlbHi : 17594333495296 <= plb11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 plb11 104 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PlbIn) ltac:(clear - Rt22; lia)).
  assert (PlbLow : plb11 + 104 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 plb11 104 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PlbIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PbbIn : In (pbb11, 128) New11) by (rewrite New11Is; wp_in_lit).
  assert (PbbHi : 17594333495296 <= pbb11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pbb11 128 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PbbIn) ltac:(clear - Rt22; lia)).
  assert (PbbLow : pbb11 + 128 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pbb11 128 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PbbIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PqaIn : In (pqa11, 56) New11) by (rewrite New11Is; wp_in_lit).
  assert (PqaHi : 17594333495296 <= pqa11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pqa11 56 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PqaIn) ltac:(clear - Rt22; lia)).
  assert (PqaLow : pqa11 + 56 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pqa11 56 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PqaIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PqbIn : In (pqb11, 56) New11) by (rewrite New11Is; wp_in_lit).
  assert (PqbHi : 17594333495296 <= pqb11)
    by exact (afp_live_hi RT GOBJ AFP Σ11 m22 pqb11 56 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PqbIn) ltac:(clear - Rt22; lia)).
  assert (PqbLow : pqb11 + 56 <= lo).
  { pose proof (af_live_range RT AF Σ11 m22 pqb11 56 Rt22 ltac:(rewrite Lv11; apply in_or_app; left; exact PqbIn)) as Span.
    rewrite Base11 in Span. clear - Span LoInWin; lia. }
  assert (PlDiff : pla11 <> plb11).
  { destruct (wg_live_apart RT AF Σ11 m22 [(pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104); (pba11, 128)] pla11 104
                ((pk11, 40) :: (ps11, 48) :: New10 ++ rt_live RT Σ) plb11 104 Rt22
                ltac:(rewrite Lv11, New11Is; reflexivity) ltac:(apply in_or_app; left; wp_in_lit)) as [Gap | Gap]; clear - Gap; lia. }
  assert (PbDiff : pba11 <> pbb11).
  { destruct (wg_live_apart RT AF Σ11 m22 [(pqb11, 56); (pqa11, 56); (pbb11, 128); (plb11, 104)] pba11 128
                ((pla11, 104) :: (pk11, 40) :: (ps11, 48) :: New10 ++ rt_live RT Σ) pbb11 128 Rt22
                ltac:(rewrite Lv11, New11Is; reflexivity) ltac:(apply in_or_app; left; wp_in_lit)) as [Gap | Gap]; clear - Gap; lia. }
  assert (PqDiff : pqa11 <> pqb11).
  { destruct (wg_live_apart RT AF Σ11 m22 [(pqb11, 56)] pqa11 56
                ((pbb11, 128) :: (plb11, 104) :: (pba11, 128) :: (pla11, 104) :: (pk11, 40) :: (ps11, 48) :: New10 ++ rt_live RT Σ) pqb11 56 Rt22
                ltac:(rewrite Lv11, New11Is; reflexivity) ltac:(apply in_or_app; left; wp_in_lit)) as [Gap | Gap]; clear - Gap; lia. }
  assert (PsdApart : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a ->
                       forall p n, In (p, n) New11 -> ~ (p <= a < p + n)).
  { intros a Acl p n Pin.
    pose proof (proj1 (Forall_forall _ _) NewPos11 (p, n) Pin) as Npos. cbn [snd] in Npos.
    exact (wg_newchunk_apart RT AF Σ Σ11 m22 New11 p n (bv_unsigned sp) a Rt22 Lv11 Pin Fr11 Base11
             ltac:(clear - LoInWin Room0; lia) ltac:(clear - Npos; lia) Acl). }
  assert (PsdAl : Forall (fun q => q mod 16 = 0) [ps11; pk11; pla11; pba11; plb11; pbb11; pqa11; pqb11]) by (repeat constructor; assumption).
  clear V11Al PkPos PkAl PkTop PlaPos PlaAl PlaTop PbaPos PbaAl PbaTop PlbPos PlbAl PlbTop PbbPos PbbAl PbbTop PqaPos PqaAl PqaTop PqbPos PqbAl PqbTop.
  assert (V11Word : 0 <= ps11 < 2 ^ 64) by (unfold USTACK_TOP in V11Top; clear - V11Pos V11Top; lia).
  assert (V11Nz : bv_eqb (Z_to_bv 64 ps11) (Z_to_bv 64 0) = false) by (clear - V11Word V11Pos; solve_cond_u).
  destruct (ConstsOf Σ11 m22 Rt22) as (ShBase22 & Clean22).
  pose proof (context_init_s11_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_11)
                r110 r111 r112 x111 x112 x113 x114 x115 x116 x117 r113 r114 r115 r116 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 j1
                g3 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F11 fc11 m22 lo) as Seg11.
  repeat match type of Seg11 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ11 m22 Rt22) | (apply (ShadowOf Σ11 m22); [exact Rt22 | clear - Rt22; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg11 ok); clear ok
         end.
  cl_lift Seg11 At22s cfg23 At23.
  destruct (ASTA_unpack RT Σ11 _ _ cfg23 At23) as (st23 & Post11 & At23s). clear At23 At22s.
  repeat match goal with
         | Old : rw_cells asegs m22 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post11 as (m23 & -> & Munch23 & Mono23 & Inv23
                     & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg
                     & FConf & FEvp & FLock & Frame23 & FComp & FThr & FIndic
                     & FSelfT & FChild & FBio & FNonce & FGprops & FDefns & FNmap
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack23).
  repeat match goal with
         | Cell : rw_cells asegs m22 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m22 m23 X cs Cell Munch23
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt23 : ART RT Σ11 m23).
  { apply (cl_seg_ART RT AF Σ11 m22 m23 (bv_unsigned sp) 48 [(12187176, 12187184)] Rt22);
      [rewrite Base11; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch23 | | exact Mono23].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl23 : cl_env m23 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m22 m23 _ canary Cl22 Munch23); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above23 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m23).
  { intros w Hi. cbv beta in Hi. rewrite Munch23 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above22 w Hi). }
  assert (Kept23 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m23).
  { apply (pres_fp_trans _ _ _ _ m m22 m23 Kept22).
    apply (PresGrow Σ11 (bv_unsigned sp) [(12187176, 12187184)] m22 m23);
      [rewrite Lv11; intros e Ein; apply in_or_app; right; exact Ein | exact Fr11 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ11 m22 m23 (bv_unsigned sp) 48 [(12187176, 12187184)] Rt22
             ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch23). }
  clear Kept22 Above22 Munch23 Mono23 Inv22 Rt22 Cl22 Stack22 ShBase22 Clean22.
  clear V11Pos V11Top V11Nz.
  (* call 12: stored_namemap_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_stored_namemap_new SITE_context_init_12 m m23 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_12, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_12, e_stored_namemap_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above23 (SavedOf m23 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain12 & FpChain12).
  match type of At23s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_stored_namemap_new Σ11 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m23 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr11, unsigned_lit by (unfold SITE_context_init_12; clear - Room0; lia); exact Chain12
             | rewrite Gr11, unsigned_lit by (unfold SITE_context_init_12; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr11; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr11; clear - FrmCap; lia
             | rewrite Lv11, length_app, Nat2Z.inj_add, NewLen11; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr11; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg24 (Σ12 & nm12 & nk12 & nh12 & nhl12 & nmd12 & nnb12 & nrl12 & nrq12 & nsk12 & At24 & LvPost12 & FrPost12 & BasePost12 & CrPost12 & V12Pos & V12Al & V12Top & nk12Pos & nk12Al & nk12Top & nh12Pos & nh12Al & nh12Top & nhl12Pos & nhl12Al & nhl12Top & nmd12Pos & nmd12Al & nmd12Top & nnb12Pos & nnb12Al & nnb12Top & nrl12Pos & nrl12Al & nrl12Top & nrq12Pos & nrq12Al & nrq12Top & nsk12Pos & nsk12Al & nsk12Top & GrPost12).
  destruct (ASTA_unpack RT Σ12 _ _ cfg24 At24) as (st24 & (m24 & Ret12 & After12 & Pres12 & Cl24 & Obj12) & At24s).
  clear At24 At23s.
  destruct Ret12 as (r120 & r121 & r122 & x121 & x122 & x123 & x124 & x125 & x126 & x127 & r123 & r124 & r125 & r126 & F12 & fc12 & ->).
  rewrite FrameLit in After12, Pres12. destruct After12 as (Rt24 & Inv24 & Mono24 & Stack24).
  rewrite (ret_pc_even SITE_context_init_12) in At24s by (unfold SITE_context_init_12; clear - Room0; lia).
  destruct Obj12 as (nm12Obj & _ & nk12Obj & _ & nh12Obj & _ & nhl12Obj & _ & nmd12Obj & _ & nnb12Obj & _ & nrl12Obj & nrl12At48 & nrl12At88 & nrl12At128 & nrl12At176 & nrl12At216 & _ & nrq12Obj & _ & nsk12Obj & _).
  repeat match goal with
         | Cell : rw_cells asegs m23 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m24 X cs);
             [ apply (rw_cells_agree_nw asegs m23 m24 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres12;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ11) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_11; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above24 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m24).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres12 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above23 w Hi). }
  assert (Kept24 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m24).
  { apply (pres_fp_trans _ _ _ _ m m23 m24 Kept23).
    apply (PresGrow Σ11 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m23 m24);
      [rewrite Lv11; intros e Ein; apply in_or_app; right; exact Ein | exact Fr11 | clear - FrameLit; lia | | exact Pres12].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept23 Above23 Pres12 Mono24 Inv23 Rt23 Cl23 Stack23 Chain12 FpChain12.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ11) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ12)) by (rewrite LvPost12; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (nsk12Live : In (nsk12, 56) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nsk12Heap : 17594333495296 <= nsk12 /\ nsk12 + 56 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nsk12 56 Rt24 nsk12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nsk12 56 Rt24 nsk12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nrq12Live : In (nrq12, 16) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nrq12Heap : 17594333495296 <= nrq12 /\ nrq12 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nrq12 16 Rt24 nrq12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nrq12 16 Rt24 nrq12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nrl12Live : In (nrl12, 264) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nrl12Heap : 17594333495296 <= nrl12 /\ nrl12 + 264 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nrl12 264 Rt24 nrl12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nrl12 264 Rt24 nrl12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nnb12Live : In (nnb12, NB_BYTES) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nnb12Heap : 17594333495296 <= nnb12 /\ nnb12 + NB_BYTES <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nnb12 NB_BYTES Rt24 nnb12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nnb12 NB_BYTES Rt24 nnb12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nmd12Live : In (nmd12, 24) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nmd12Heap : 17594333495296 <= nmd12 /\ nmd12 + 24 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nmd12 24 Rt24 nmd12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nmd12 24 Rt24 nmd12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nhl12Live : In (nhl12, 40) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nhl12Heap : 17594333495296 <= nhl12 /\ nhl12 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nhl12 40 Rt24 nhl12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nhl12 40 Rt24 nhl12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nh12Live : In (nh12, 96) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nh12Heap : 17594333495296 <= nh12 /\ nh12 + 96 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nh12 96 Rt24 nh12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nh12 96 Rt24 nh12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nk12Live : In (nk12, 40) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nk12Heap : 17594333495296 <= nk12 /\ nk12 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nk12 40 Rt24 nk12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nk12 40 Rt24 nk12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nm12Live : In (nm12, 40) (rt_live RT Σ12)) by (rewrite LvPost12; wp_in_lit).
  assert (nm12Heap : 17594333495296 <= nm12 /\ nm12 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ12 m24 nm12 40 Rt24 nm12Live ltac:(clear - Rt24; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ12 m24 nm12 40 Rt24 nm12Live) as Span.
    rewrite BasePost12, Base11 in Span. clear - Span LoInWin; lia. }
  assert (nsk12Apart : forall w, nsk12 <= w < nsk12 + 56 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nsk12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nsk12 56 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nrq12Apart : forall w, nrq12 <= w < nrq12 + 16 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nrq12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nrq12 16 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nrl12Apart : forall w, nrl12 <= w < nrl12 + 264 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nrl12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nrl12 264 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nnb12Apart : forall w, nnb12 <= w < nnb12 + NB_BYTES -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nnb12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nnb12 NB_BYTES (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nmd12Apart : forall w, nmd12 <= w < nmd12 + 24 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nmd12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nmd12 24 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nhl12Apart : forall w, nhl12 <= w < nhl12 + 40 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nhl12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nhl12 40 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nh12Apart : forall w, nh12 <= w < nh12 + 96 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nh12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nh12 96 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nk12Apart : forall w, nk12 <= w < nk12 + 40 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nk12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nk12 40 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (nm12Apart : forall w, nm12 <= w < nm12 + 40 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX nm12Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] nm12 40 (bv_unsigned sp) w Rt24 LvPost12
                                        ltac:(wp_in_lit) FrPost12 BasePost12
                                        ltac:(rewrite Base11; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_11; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd12 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V12Al nk12Pos nk12Al nk12Top nh12Pos nh12Al nh12Top nhl12Pos nhl12Al nhl12Top nmd12Pos nmd12Al nmd12Top nnb12Pos nnb12Al nnb12Top nrl12Pos nrl12Al nrl12Top nrq12Pos nrq12Al nrq12Top nsk12Pos nsk12Al nsk12Top.
  assert (Sub11_12 : incl New11 (rt_live RT Σ12)) by (intros e Ein; rewrite LvPost12; repeat first [apply in_or_app; right | right]; exact (Sub11_11 e Ein)).
  rewrite Lv11 in LvPost12. rewrite ?app_assoc, ?app_comm_cons in LvPost12.
  match type of LvPost12 with _ = ?L ++ rt_live RT Σ => remember L as New12 eqn:New12Is in LvPost12 end.
  rename LvPost12 into Lv12.
  assert (NewLen12 : Z.of_nat (length New12) = 93)
    by (rewrite New12Is; rewrite ?length_app; cbn [length]; clear - NewLen11; lia).
  assert (NewPos12 : Forall (fun blk => 0 < snd blk) New12).
  { rewrite New12Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos11; lia | ] | apply Forall_nil | exact NewPos11 ]. }
  assert (NewBnd12 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New12).
  { rewrite New12Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(nsk12, 56); (nrq12, 16); (nrl12, 264); (nnb12, NB_BYTES); (nmd12, 24); (nhl12, 40); (nh12, 96); (nk12, 40); (nm12, 40)] ++ New11)). apply Forall_app. split; [exact Bnd12 | exact NewBnd11]. }
  assert (Fr12 : rt_frames RT Σ12 = rt_frames RT Σ) by (rewrite FrPost12; exact Fr11).
  assert (Base12 : rt_sp0 RT Σ12 = rt_sp0 RT Σ) by (rewrite BasePost12; exact Base11).
  assert (Gr12 : rt_cg RT Σ12 = rt_cg RT Σ) by (rewrite GrPost12; exact Gr11).
  assert (Cr12 : rt_credit RT Σ12 = rt_credit RT Σ - (45 + NM_COST))
    by (rewrite CrPost12, Cr11; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost12 BasePost12 GrPost12 CrPost12 Lv11 NewLen11 NewPos11 NewBnd11 Bnd12 Fr11 Base11 Gr11 Cr11.
  assert (V12Word : 0 <= nm12 < 2 ^ 64) by (unfold USTACK_TOP in V12Top; clear - V12Pos V12Top; lia).
  assert (V12Nz : bv_eqb (Z_to_bv 64 nm12) (Z_to_bv 64 0) = false) by (clear - V12Word V12Pos; solve_cond_u).
  destruct (ConstsOf Σ12 m24 Rt24) as (ShBase24 & Clean24).
  pose proof (context_init_s12_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_12)
                r120 r121 r122 x121 x122 x123 x124 x125 x126 x127 r123 r124 r125 r126 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 j1
                g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F12 fc12 m24 lo) as Seg12.
  repeat match type of Seg12 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ12 m24 Rt24) | (apply (ShadowOf Σ12 m24); [exact Rt24 | clear - Rt24; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg12 ok); clear ok
         end.
  cl_lift Seg12 At24s cfg25 At25.
  destruct (ASTA_unpack RT Σ12 _ _ cfg25 At25) as (st25 & Post12 & At25s). clear At25 At24s.
  repeat match goal with
         | Old : rw_cells asegs m24 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post12 as (m25 & -> & Munch25 & Mono25 & Inv25
                     & FNmap & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt
                     & FDrbg & FConf & FEvp & FLock & Frame25 & FComp & FThr
                     & FIndic & FSelfT & FChild & FBio & FNonce & FGprops & FDefns
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack25).
  repeat match goal with
         | Cell : rw_cells asegs m24 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m24 m25 X cs Cell Munch25
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt25 : ART RT Σ12 m25).
  { apply (cl_seg_ART RT AF Σ12 m24 m25 (bv_unsigned sp) 48 [(12187200, 12187208)] Rt24);
      [rewrite Base12; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch25 | | exact Mono25].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl25 : cl_env m25 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m24 m25 _ canary Cl24 Munch25); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above25 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m25).
  { intros w Hi. cbv beta in Hi. rewrite Munch25 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above24 w Hi). }
  assert (Kept25 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m25).
  { apply (pres_fp_trans _ _ _ _ m m24 m25 Kept24).
    apply (PresGrow Σ12 (bv_unsigned sp) [(12187200, 12187208)] m24 m25);
      [rewrite Lv12; intros e Ein; apply in_or_app; right; exact Ein | exact Fr12 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ12 m24 m25 (bv_unsigned sp) 48 [(12187200, 12187208)] Rt24
             ltac:(rewrite Base12; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch25). }
  clear Kept24 Above24 Munch25 Mono25 Inv24 Rt24 Cl24 Stack24 ShBase24 Clean24.
  clear V12Pos V12Top V12Nz.
  (* call 13: ossl_property_defns_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_pdefns SITE_context_init_13 m m25 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_13, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_13, e_pdefns) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above25 (SavedOf m25 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain13 & FpChain13).
  match type of At25s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_property_defns_new Σ12 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m25 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr12, unsigned_lit by (unfold SITE_context_init_13; clear - Room0; lia); exact Chain13
             | rewrite Gr12, unsigned_lit by (unfold SITE_context_init_13; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr12; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr12; clear - FrmCap; lia
             | rewrite Lv12, length_app, Nat2Z.inj_add, NewLen12; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr12; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg26 (Σ13 & pd13 & pb13 & At26 & LvPost13 & FrPost13 & BasePost13 & CrPost13 & V13Pos & V13Al & V13Top & pb13Pos & pb13Al & pb13Top & GrPost13).
  destruct (ASTA_unpack RT Σ13 _ _ cfg26 At26) as (st26 & (m26 & Ret13 & After13 & Pres13 & Cl26 & Obj13) & At26s).
  clear At26 At25s.
  destruct Ret13 as (r130 & r131 & r132 & x131 & x132 & x133 & x134 & x135 & x136 & x137 & r133 & r134 & r135 & r136 & F13 & fc13 & ->).
  rewrite FrameLit in After13, Pres13. destruct After13 as (Rt26 & Inv26 & Mono26 & Stack26).
  rewrite (ret_pc_even SITE_context_init_13) in At26s by (unfold SITE_context_init_13; clear - Room0; lia).
  destruct Obj13 as (_ & _ & _ & _ & pd13Obj & pb13Obj).
  repeat match goal with
         | Cell : rw_cells asegs m25 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m26 X cs);
             [ apply (rw_cells_agree_nw asegs m25 m26 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres13;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ12) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_12; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above26 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m26).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres13 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above25 w Hi). }
  assert (Kept26 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m26).
  { apply (pres_fp_trans _ _ _ _ m m25 m26 Kept25).
    apply (PresGrow Σ12 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m25 m26);
      [rewrite Lv12; intros e Ein; apply in_or_app; right; exact Ein | exact Fr12 | clear - FrameLit; lia | | exact Pres13].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept25 Above25 Pres13 Mono26 Inv25 Rt25 Cl25 Stack25 Chain13 FpChain13.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ12) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ13)) by (rewrite LvPost13; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (pb13Live : In (pb13, 128) (rt_live RT Σ13)) by (rewrite LvPost13; wp_in_lit).
  assert (pb13Heap : 17594333495296 <= pb13 /\ pb13 + 128 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ13 m26 pb13 128 Rt26 pb13Live ltac:(clear - Rt26; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ13 m26 pb13 128 Rt26 pb13Live) as Span.
    rewrite BasePost13, Base12 in Span. clear - Span LoInWin; lia. }
  assert (pd13Live : In (pd13, 104) (rt_live RT Σ13)) by (rewrite LvPost13; wp_in_lit).
  assert (pd13Heap : 17594333495296 <= pd13 /\ pd13 + 104 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ13 m26 pd13 104 Rt26 pd13Live ltac:(clear - Rt26; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ13 m26 pd13 104 Rt26 pd13Live) as Span.
    rewrite BasePost13, Base12 in Span. clear - Span LoInWin; lia. }
  assert (pb13Apart : forall w, pb13 <= w < pb13 + 128 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX pb13Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ12 Σ13 m26 [(pb13, 128); (pd13, 104)] pb13 128 (bv_unsigned sp) w Rt26 LvPost13
                                        ltac:(wp_in_lit) FrPost13 BasePost13
                                        ltac:(rewrite Base12; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_12; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (pd13Apart : forall w, pd13 <= w < pd13 + 104 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX pd13Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ12 Σ13 m26 [(pb13, 128); (pd13, 104)] pd13 104 (bv_unsigned sp) w Rt26 LvPost13
                                        ltac:(wp_in_lit) FrPost13 BasePost13
                                        ltac:(rewrite Base12; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_12; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd13 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(pb13, 128); (pd13, 104)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V13Al pb13Pos pb13Al pb13Top.
  assert (Sub11_13 : incl New11 (rt_live RT Σ13)) by (intros e Ein; rewrite LvPost13; repeat first [apply in_or_app; right | right]; exact (Sub11_12 e Ein)).
  rewrite Lv12 in LvPost13. rewrite ?app_assoc, ?app_comm_cons in LvPost13.
  match type of LvPost13 with _ = ?L ++ rt_live RT Σ => remember L as New13 eqn:New13Is in LvPost13 end.
  rename LvPost13 into Lv13.
  assert (NewLen13 : Z.of_nat (length New13) = 95)
    by (rewrite New13Is; rewrite ?length_app; cbn [length]; clear - NewLen12; lia).
  assert (NewPos13 : Forall (fun blk => 0 < snd blk) New13).
  { rewrite New13Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos12; lia | ] | apply Forall_nil | exact NewPos12 ]. }
  assert (NewBnd13 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New13).
  { rewrite New13Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(pb13, 128); (pd13, 104)] ++ New12)). apply Forall_app. split; [exact Bnd13 | exact NewBnd12]. }
  assert (Fr13 : rt_frames RT Σ13 = rt_frames RT Σ) by (rewrite FrPost13; exact Fr12).
  assert (Base13 : rt_sp0 RT Σ13 = rt_sp0 RT Σ) by (rewrite BasePost13; exact Base12).
  assert (Gr13 : rt_cg RT Σ13 = rt_cg RT Σ) by (rewrite GrPost13; exact Gr12).
  assert (Cr13 : rt_credit RT Σ13 = rt_credit RT Σ - (45 + NM_COST))
    by (rewrite CrPost13, Cr12; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost13 BasePost13 GrPost13 CrPost13 Lv12 NewLen12 NewPos12 NewBnd12 Bnd13 Fr12 Base12 Gr12 Cr12 Sub11_12.
  assert (V13Word : 0 <= pd13 < 2 ^ 64) by (unfold USTACK_TOP in V13Top; clear - V13Pos V13Top; lia).
  assert (V13Nz : bv_eqb (Z_to_bv 64 pd13) (Z_to_bv 64 0) = false) by (clear - V13Word V13Pos; solve_cond_u).
  destruct (ConstsOf Σ13 m26 Rt26) as (ShBase26 & Clean26).
  pose proof (context_init_s13_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_13)
                r130 r131 r132 x131 x132 x133 x134 x135 x136 x137 r133 r134 r135 r136 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 j1
                g7 g8 g10 g12 g13 g18 g19 g20 g21 F13 fc13 m26 lo) as Seg13.
  repeat match type of Seg13 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ13 m26 Rt26) | (apply (ShadowOf Σ13 m26); [exact Rt26 | clear - Rt26; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg13 ok); clear ok
         end.
  cl_lift Seg13 At26s cfg27 At27.
  destruct (ASTA_unpack RT Σ13 _ _ cfg27 At27) as (st27 & Post13 & At27s). clear At27 At26s.
  repeat match goal with
         | Old : rw_cells asegs m26 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post13 as (m27 & -> & Munch27 & Mono27 & Inv27
                     & FDefns & FNmap & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa
                     & FDecSt & FDrbg & FConf & FEvp & FLock & Frame27 & FComp
                     & FThr & FIndic & FSelfT & FChild & FBio & FNonce & FGprops
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack27).
  repeat match goal with
         | Cell : rw_cells asegs m26 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m26 m27 X cs Cell Munch27
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt27 : ART RT Σ13 m27).
  { apply (cl_seg_ART RT AF Σ13 m26 m27 (bv_unsigned sp) 48 [(12187208, 12187216)] Rt26);
      [rewrite Base13; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch27 | | exact Mono27].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl27 : cl_env m27 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m26 m27 _ canary Cl26 Munch27); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above27 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m27).
  { intros w Hi. cbv beta in Hi. rewrite Munch27 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above26 w Hi). }
  assert (Kept27 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m27).
  { apply (pres_fp_trans _ _ _ _ m m26 m27 Kept26).
    apply (PresGrow Σ13 (bv_unsigned sp) [(12187208, 12187216)] m26 m27);
      [rewrite Lv13; intros e Ein; apply in_or_app; right; exact Ein | exact Fr13 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ13 m26 m27 (bv_unsigned sp) 48 [(12187208, 12187216)] Rt26
             ltac:(rewrite Base13; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch27). }
  clear Kept26 Above26 Munch27 Mono27 Inv26 Rt26 Cl26 Stack26 ShBase26 Clean26.
  clear V13Pos V13Top V13Nz.
  (* call 14: ossl_ctx_global_properties_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_ctx_global_properties_new SITE_context_init_14 m m27 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_14, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_14, e_ossl_ctx_global_properties_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above27 (SavedOf m27 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain14 & FpChain14).
  match type of At27s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_ctx_global_properties_new Σ13 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m27 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr13, unsigned_lit by (unfold SITE_context_init_14; clear - Room0; lia); exact Chain14
             | rewrite Gr13, unsigned_lit by (unfold SITE_context_init_14; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr13; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr13; clear - FrmCap; lia
             | rewrite Lv13, length_app, Nat2Z.inj_add, NewLen13; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr13; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg28 (Σ14 & gp14 & At28 & LvPost14 & FrPost14 & BasePost14 & CrPost14 & V14Pos & V14Al & V14Top & GrPost14).
  destruct (ASTA_unpack RT Σ14 _ _ cfg28 At28) as (st28 & (m28 & Ret14 & After14 & Pres14 & Cl28 & Obj14) & At28s).
  clear At28 At27s.
  destruct Ret14 as (r140 & r141 & r142 & x141 & x142 & x143 & x144 & x145 & x146 & x147 & r143 & r144 & r145 & r146 & F14 & fc14 & ->).
  rewrite FrameLit in After14, Pres14. destruct After14 as (Rt28 & Inv28 & Mono28 & Stack28).
  rewrite (ret_pc_even SITE_context_init_14) in At28s by (unfold SITE_context_init_14; clear - Room0; lia).
  destruct Obj14 as (ZWr14 & _ & ZBytes14).
  assert (gp14Obj : rw_cells asegs m28 gp14 [CB 16 (repeat (Z_to_bv 8 0) 16)]) by exact (rw_CB_of_bytes _ _ _ ZBytes14 ZWr14).
  clear ZWr14 ZBytes14.
  repeat match goal with
         | Cell : rw_cells asegs m27 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m28 X cs);
             [ apply (rw_cells_agree_nw asegs m27 m28 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres14;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ13) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_13; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above28 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m28).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres14 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above27 w Hi). }
  assert (Kept28 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m28).
  { apply (pres_fp_trans _ _ _ _ m m27 m28 Kept27).
    apply (PresGrow Σ13 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m27 m28);
      [rewrite Lv13; intros e Ein; apply in_or_app; right; exact Ein | exact Fr13 | clear - FrameLit; lia | | exact Pres14].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept27 Above27 Pres14 Mono28 Inv27 Rt27 Cl27 Stack27 Chain14 FpChain14.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ13) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ14)) by (rewrite LvPost14; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (gp14Live : In (gp14, 16) (rt_live RT Σ14)) by (rewrite LvPost14; wp_in_lit).
  assert (gp14Heap : 17594333495296 <= gp14 /\ gp14 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ14 m28 gp14 16 Rt28 gp14Live ltac:(clear - Rt28; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ14 m28 gp14 16 Rt28 gp14Live) as Span.
    rewrite BasePost14, Base13 in Span. clear - Span LoInWin; lia. }
  assert (gp14Apart : forall w, gp14 <= w < gp14 + 16 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX gp14Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ13 Σ14 m28 [(gp14, 16)] gp14 16 (bv_unsigned sp) w Rt28 LvPost14
                                        ltac:(wp_in_lit) FrPost14 BasePost14
                                        ltac:(rewrite Base13; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_13; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd14 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(gp14, 16)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V14Al.
  assert (Sub11_14 : incl New11 (rt_live RT Σ14)) by (intros e Ein; rewrite LvPost14; repeat first [apply in_or_app; right | right]; exact (Sub11_13 e Ein)).
  rewrite Lv13 in LvPost14. rewrite ?app_assoc, ?app_comm_cons in LvPost14.
  match type of LvPost14 with _ = ?L ++ rt_live RT Σ => remember L as New14 eqn:New14Is in LvPost14 end.
  rename LvPost14 into Lv14.
  assert (NewLen14 : Z.of_nat (length New14) = 96)
    by (rewrite New14Is; rewrite ?length_app; cbn [length]; clear - NewLen13; lia).
  assert (NewPos14 : Forall (fun blk => 0 < snd blk) New14).
  { rewrite New14Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos13; lia | ] | apply Forall_nil | exact NewPos13 ]. }
  assert (NewBnd14 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New14).
  { rewrite New14Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(gp14, 16)] ++ New13)). apply Forall_app. split; [exact Bnd14 | exact NewBnd13]. }
  assert (Fr14 : rt_frames RT Σ14 = rt_frames RT Σ) by (rewrite FrPost14; exact Fr13).
  assert (Base14 : rt_sp0 RT Σ14 = rt_sp0 RT Σ) by (rewrite BasePost14; exact Base13).
  assert (Gr14 : rt_cg RT Σ14 = rt_cg RT Σ) by (rewrite GrPost14; exact Gr13).
  assert (Cr14 : rt_credit RT Σ14 = rt_credit RT Σ - (45 + NM_COST))
    by (rewrite CrPost14, Cr13; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost14 BasePost14 GrPost14 CrPost14 Lv13 NewLen13 NewPos13 NewBnd13 Bnd14 Fr13 Base13 Gr13 Cr13 Sub11_13.
  assert (V14Word : 0 <= gp14 < 2 ^ 64) by (unfold USTACK_TOP in V14Top; clear - V14Pos V14Top; lia).
  assert (V14Nz : bv_eqb (Z_to_bv 64 gp14) (Z_to_bv 64 0) = false) by (clear - V14Word V14Pos; solve_cond_u).
  destruct (ConstsOf Σ14 m28 Rt28) as (ShBase28 & Clean28).
  pose proof (context_init_s14_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_14)
                r140 r141 r142 x141 x142 x143 x144 x145 x146 x147 r143 r144 r145 r146 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 j1
                g8 g10 g12 g13 g18 g19 g20 g21 F14 fc14 m28 lo) as Seg14.
  repeat match type of Seg14 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ14 m28 Rt28) | (apply (ShadowOf Σ14 m28); [exact Rt28 | clear - Rt28; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg14 ok); clear ok
         end.
  cl_lift Seg14 At28s cfg29 At29.
  destruct (ASTA_unpack RT Σ14 _ _ cfg29 At29) as (st29 & Post14 & At29s). clear At29 At28s.
  repeat match goal with
         | Old : rw_cells asegs m28 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post14 as (m29 & -> & Munch29 & Mono29 & Inv29
                     & FGprops & FDefns & FNmap & FPsd & FProvSt & FLdrSt & FEncSt
                     & FDecCa & FDecSt & FDrbg & FConf & FEvp & FLock & Frame29
                     & FComp & FThr & FIndic & FSelfT & FChild & FBio & FNonce
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack29).
  repeat match goal with
         | Cell : rw_cells asegs m28 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m28 m29 X cs Cell Munch29
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt29 : ART RT Σ14 m29).
  { apply (cl_seg_ART RT AF Σ14 m28 m29 (bv_unsigned sp) 48 [(12187216, 12187224)] Rt28);
      [rewrite Base14; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch29 | | exact Mono29].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl29 : cl_env m29 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m28 m29 _ canary Cl28 Munch29); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above29 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m29).
  { intros w Hi. cbv beta in Hi. rewrite Munch29 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above28 w Hi). }
  assert (Kept29 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m29).
  { apply (pres_fp_trans _ _ _ _ m m28 m29 Kept28).
    apply (PresGrow Σ14 (bv_unsigned sp) [(12187216, 12187224)] m28 m29);
      [rewrite Lv14; intros e Ein; apply in_or_app; right; exact Ein | exact Fr14 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ14 m28 m29 (bv_unsigned sp) 48 [(12187216, 12187224)] Rt28
             ltac:(rewrite Base14; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch29). }
  clear Kept28 Above28 Munch29 Mono29 Inv28 Rt28 Cl28 Stack28 ShBase28 Clean28.
  clear V14Pos V14Top V14Nz.
  (* call 15: ossl_bio_core_globals_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_bio_core_globals_new SITE_context_init_15 m m29 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_15, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_15, e_ossl_bio_core_globals_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above29 (SavedOf m29 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain15 & FpChain15).
  match type of At29s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_bio_core_globals_new Σ14 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m29 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr14, unsigned_lit by (unfold SITE_context_init_15; clear - Room0; lia); exact Chain15
             | rewrite Gr14, unsigned_lit by (unfold SITE_context_init_15; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr14; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr14; clear - FrmCap; lia
             | rewrite Lv14, length_app, Nat2Z.inj_add, NewLen14; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr14; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg30 (Σ15 & bc15 & At30 & LvPost15 & FrPost15 & BasePost15 & CrPost15 & V15Pos & V15Al & V15Top & GrPost15).
  destruct (ASTA_unpack RT Σ15 _ _ cfg30 At30) as (st30 & (m30 & Ret15 & After15 & Pres15 & Cl30 & Obj15) & At30s).
  clear At30 At29s.
  destruct Ret15 as (r150 & r151 & r152 & x151 & x152 & x153 & x154 & x155 & x156 & x157 & r153 & r154 & r155 & r156 & F15 & fc15 & ->).
  rewrite FrameLit in After15, Pres15. destruct After15 as (Rt30 & Inv30 & Mono30 & Stack30).
  rewrite (ret_pc_even SITE_context_init_15) in At30s by (unfold SITE_context_init_15; clear - Room0; lia).
  destruct Obj15 as (ZWr15 & _ & ZBytes15).
  assert (bc15Obj : rw_cells asegs m30 bc15 [CB 56 (repeat (Z_to_bv 8 0) 56)]) by exact (rw_CB_of_bytes _ _ _ ZBytes15 ZWr15).
  clear ZWr15 ZBytes15.
  repeat match goal with
         | Cell : rw_cells asegs m29 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m30 X cs);
             [ apply (rw_cells_agree_nw asegs m29 m30 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres15;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ14) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_14; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above30 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m30).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres15 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above29 w Hi). }
  assert (Kept30 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m30).
  { apply (pres_fp_trans _ _ _ _ m m29 m30 Kept29).
    apply (PresGrow Σ14 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m29 m30);
      [rewrite Lv14; intros e Ein; apply in_or_app; right; exact Ein | exact Fr14 | clear - FrameLit; lia | | exact Pres15].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept29 Above29 Pres15 Mono30 Inv29 Rt29 Cl29 Stack29 Chain15 FpChain15.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ14) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ15)) by (rewrite LvPost15; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (bc15Live : In (bc15, 56) (rt_live RT Σ15)) by (rewrite LvPost15; wp_in_lit).
  assert (bc15Heap : 17594333495296 <= bc15 /\ bc15 + 56 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ15 m30 bc15 56 Rt30 bc15Live ltac:(clear - Rt30; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ15 m30 bc15 56 Rt30 bc15Live) as Span.
    rewrite BasePost15, Base14 in Span. clear - Span LoInWin; lia. }
  assert (bc15Apart : forall w, bc15 <= w < bc15 + 56 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX bc15Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ14 Σ15 m30 [(bc15, 56)] bc15 56 (bv_unsigned sp) w Rt30 LvPost15
                                        ltac:(wp_in_lit) FrPost15 BasePost15
                                        ltac:(rewrite Base14; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_14; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd15 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(bc15, 56)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V15Al.
  assert (Sub11_15 : incl New11 (rt_live RT Σ15)) by (intros e Ein; rewrite LvPost15; repeat first [apply in_or_app; right | right]; exact (Sub11_14 e Ein)).
  rewrite Lv14 in LvPost15. rewrite ?app_assoc, ?app_comm_cons in LvPost15.
  match type of LvPost15 with _ = ?L ++ rt_live RT Σ => remember L as New15 eqn:New15Is in LvPost15 end.
  rename LvPost15 into Lv15.
  assert (NewLen15 : Z.of_nat (length New15) = 97)
    by (rewrite New15Is; rewrite ?length_app; cbn [length]; clear - NewLen14; lia).
  assert (NewPos15 : Forall (fun blk => 0 < snd blk) New15).
  { rewrite New15Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos14; lia | ] | apply Forall_nil | exact NewPos14 ]. }
  assert (NewBnd15 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New15).
  { rewrite New15Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(bc15, 56)] ++ New14)). apply Forall_app. split; [exact Bnd15 | exact NewBnd14]. }
  assert (Fr15 : rt_frames RT Σ15 = rt_frames RT Σ) by (rewrite FrPost15; exact Fr14).
  assert (Base15 : rt_sp0 RT Σ15 = rt_sp0 RT Σ) by (rewrite BasePost15; exact Base14).
  assert (Gr15 : rt_cg RT Σ15 = rt_cg RT Σ) by (rewrite GrPost15; exact Gr14).
  assert (Cr15 : rt_credit RT Σ15 = rt_credit RT Σ - (45 + NM_COST))
    by (rewrite CrPost15, Cr14; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost15 BasePost15 GrPost15 CrPost15 Lv14 NewLen14 NewPos14 NewBnd14 Bnd15 Fr14 Base14 Gr14 Cr14 Sub11_14.
  assert (V15Word : 0 <= bc15 < 2 ^ 64) by (unfold USTACK_TOP in V15Top; clear - V15Pos V15Top; lia).
  assert (V15Nz : bv_eqb (Z_to_bv 64 bc15) (Z_to_bv 64 0) = false) by (clear - V15Word V15Pos; solve_cond_u).
  destruct (ConstsOf Σ15 m30 Rt30) as (ShBase30 & Clean30).
  pose proof (context_init_s15_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_15)
                r150 r151 r152 x151 x152 x153 x154 x155 x156 x157 r153 r154 r155 r156 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 j1
                g10 g12 g13 g18 g19 g20 g21 F15 fc15 m30 lo) as Seg15.
  repeat match type of Seg15 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ15 m30 Rt30) | (apply (ShadowOf Σ15 m30); [exact Rt30 | clear - Rt30; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg15 ok); clear ok
         end.
  cl_lift Seg15 At30s cfg31 At31.
  destruct (ASTA_unpack RT Σ15 _ _ cfg31 At31) as (st31 & Post15 & At31s). clear At31 At30s.
  repeat match goal with
         | Old : rw_cells asegs m30 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post15 as (m31 & -> & Munch31 & Mono31 & Inv31
                     & FBio & FGprops & FDefns & FNmap & FPsd & FProvSt & FLdrSt
                     & FEncSt & FDecCa & FDecSt & FDrbg & FConf & FEvp & FLock
                     & Frame31 & FComp & FThr & FIndic & FSelfT & FChild & FNonce
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack31).
  repeat match goal with
         | Cell : rw_cells asegs m30 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m30 m31 X cs Cell Munch31
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt31 : ART RT Σ15 m31).
  { apply (cl_seg_ART RT AF Σ15 m30 m31 (bv_unsigned sp) 48 [(12187248, 12187256)] Rt30);
      [rewrite Base15; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch31 | | exact Mono31].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl31 : cl_env m31 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m30 m31 _ canary Cl30 Munch31); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above31 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m31).
  { intros w Hi. cbv beta in Hi. rewrite Munch31 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above30 w Hi). }
  assert (Kept31 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m31).
  { apply (pres_fp_trans _ _ _ _ m m30 m31 Kept30).
    apply (PresGrow Σ15 (bv_unsigned sp) [(12187248, 12187256)] m30 m31);
      [rewrite Lv15; intros e Ein; apply in_or_app; right; exact Ein | exact Fr15 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ15 m30 m31 (bv_unsigned sp) 48 [(12187248, 12187256)] Rt30
             ltac:(rewrite Base15; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch31). }
  clear Kept30 Above30 Munch31 Mono31 Inv30 Rt30 Cl30 Stack30 ShBase30 Clean30.
  clear V15Pos V15Top V15Nz.
  (* call 16: ossl_prov_drbg_nonce_ctx_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_prov_drbg_nonce_ctx_new SITE_context_init_16 m m31 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_16, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_16, e_ossl_prov_drbg_nonce_ctx_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above31 (SavedOf m31 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain16 & FpChain16).
  match type of At31s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_prov_drbg_nonce_ctx_new Σ15 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m31 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr15, unsigned_lit by (unfold SITE_context_init_16; clear - Room0; lia); exact Chain16
             | rewrite Gr15, unsigned_lit by (unfold SITE_context_init_16; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr15; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr15; clear - FrmCap; lia
             | rewrite Lv15, length_app, Nat2Z.inj_add, NewLen15; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr15; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg32 (Σ16 & dn16 & dk16 & At32 & LvPost16 & FrPost16 & BasePost16 & CrPost16 & V16Pos & V16Al & V16Top & dk16Pos & dk16Al & dk16Top & GrPost16).
  destruct (ASTA_unpack RT Σ16 _ _ cfg32 At32) as (st32 & (jc16 & m32 & Ret16 & After16 & Pres16 & Cl32 & Obj16) & At32s).
  clear At32 At31s.
  destruct Ret16 as (r160 & r161 & r162 & x161 & x162 & x163 & x164 & x165 & x166 & x167 & r163 & r164 & r165 & r166 & F16 & fc16 & ->).
  rewrite FrameLit in After16, Pres16. destruct After16 as (Rt32 & Inv32 & Mono32 & Stack32).
  rewrite (ret_pc_even SITE_context_init_16) in At32s by (unfold SITE_context_init_16; clear - Room0; lia).
  destruct Obj16 as (_ & _ & _ & _ & dn16Obj & dk16Obj).
  repeat match goal with
         | Cell : rw_cells asegs m31 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m32 X cs);
             [ apply (rw_cells_agree_nw asegs m31 m32 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres16;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ15) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_15; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above32 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m32).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres16 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above31 w Hi). }
  assert (Kept32 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m32).
  { apply (pres_fp_trans _ _ _ _ m m31 m32 Kept31).
    apply (PresGrow Σ15 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m31 m32);
      [rewrite Lv15; intros e Ein; apply in_or_app; right; exact Ein | exact Fr15 | clear - FrameLit; lia | | exact Pres16].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept31 Above31 Pres16 Mono32 Inv31 Rt31 Cl31 Stack31 Chain16 FpChain16.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ15) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ16)) by (rewrite LvPost16; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (dk16Live : In (dk16, 40) (rt_live RT Σ16)) by (rewrite LvPost16; wp_in_lit).
  assert (dk16Heap : 17594333495296 <= dk16 /\ dk16 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ16 m32 dk16 40 Rt32 dk16Live ltac:(clear - Rt32; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ16 m32 dk16 40 Rt32 dk16Live) as Span.
    rewrite BasePost16, Base15 in Span. clear - Span LoInWin; lia. }
  assert (dn16Live : In (dn16, 16) (rt_live RT Σ16)) by (rewrite LvPost16; wp_in_lit).
  assert (dn16Heap : 17594333495296 <= dn16 /\ dn16 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ16 m32 dn16 16 Rt32 dn16Live ltac:(clear - Rt32; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ16 m32 dn16 16 Rt32 dn16Live) as Span.
    rewrite BasePost16, Base15 in Span. clear - Span LoInWin; lia. }
  assert (dk16Apart : forall w, dk16 <= w < dk16 + 40 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX dk16Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ15 Σ16 m32 [(dk16, 40); (dn16, 16)] dk16 40 (bv_unsigned sp) w Rt32 LvPost16
                                        ltac:(wp_in_lit) FrPost16 BasePost16
                                        ltac:(rewrite Base15; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_15; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (dn16Apart : forall w, dn16 <= w < dn16 + 16 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX dn16Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ15 Σ16 m32 [(dk16, 40); (dn16, 16)] dn16 16 (bv_unsigned sp) w Rt32 LvPost16
                                        ltac:(wp_in_lit) FrPost16 BasePost16
                                        ltac:(rewrite Base15; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_15; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd16 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(dk16, 40); (dn16, 16)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V16Al dk16Pos dk16Al dk16Top.
  assert (Sub11_16 : incl New11 (rt_live RT Σ16)) by (intros e Ein; rewrite LvPost16; repeat first [apply in_or_app; right | right]; exact (Sub11_15 e Ein)).
  rewrite Lv15 in LvPost16. rewrite ?app_assoc, ?app_comm_cons in LvPost16.
  match type of LvPost16 with _ = ?L ++ rt_live RT Σ => remember L as New16 eqn:New16Is in LvPost16 end.
  rename LvPost16 into Lv16.
  assert (NewLen16 : Z.of_nat (length New16) = 99)
    by (rewrite New16Is; rewrite ?length_app; cbn [length]; clear - NewLen15; lia).
  assert (NewPos16 : Forall (fun blk => 0 < snd blk) New16).
  { rewrite New16Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos15; lia | ] | apply Forall_nil | exact NewPos15 ]. }
  assert (NewBnd16 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New16).
  { rewrite New16Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(dk16, 40); (dn16, 16)] ++ New15)). apply Forall_app. split; [exact Bnd16 | exact NewBnd15]. }
  assert (Fr16 : rt_frames RT Σ16 = rt_frames RT Σ) by (rewrite FrPost16; exact Fr15).
  assert (Base16 : rt_sp0 RT Σ16 = rt_sp0 RT Σ) by (rewrite BasePost16; exact Base15).
  assert (Gr16 : rt_cg RT Σ16 = rt_cg RT Σ) by (rewrite GrPost16; exact Gr15).
  assert (Cr16 : rt_credit RT Σ16 = rt_credit RT Σ - (46 + NM_COST))
    by (rewrite CrPost16, Cr15; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost16 BasePost16 GrPost16 CrPost16 Lv15 NewLen15 NewPos15 NewBnd15 Bnd16 Fr15 Base15 Gr15 Cr15 Sub11_15.
  assert (V16Word : 0 <= dn16 < 2 ^ 64) by (unfold USTACK_TOP in V16Top; clear - V16Pos V16Top; lia).
  assert (V16Nz : bv_eqb (Z_to_bv 64 dn16) (Z_to_bv 64 0) = false) by (clear - V16Word V16Pos; solve_cond_u).
  destruct (ConstsOf Σ16 m32 Rt32) as (ShBase32 & Clean32).
  pose proof (context_init_s16_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_16)
                r160 r161 r162 x161 x162 x163 x164 x165 x166 x167 r163 r164 r165 r166 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 j1
                g10 g13 g18 g19 g20 g21 F16 fc16 m32 lo) as Seg16.
  repeat match type of Seg16 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ16 m32 Rt32) | (apply (ShadowOf Σ16 m32); [exact Rt32 | clear - Rt32; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg16 ok); clear ok
         end.
  cl_lift Seg16 At32s cfg33 At33.
  destruct (ASTA_unpack RT Σ16 _ _ cfg33 At33) as (st33 & Post16 & At33s). clear At33 At32s.
  repeat match goal with
         | Old : rw_cells asegs m32 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post16 as (m33 & -> & Munch33 & Mono33 & Inv33
                     & FNonce & FBio & FGprops & FDefns & FNmap & FPsd & FProvSt
                     & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg & FConf & FEvp
                     & FLock & Frame33 & FComp & FThr & FIndic & FSelfT & FChild
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack33).
  repeat match goal with
         | Cell : rw_cells asegs m32 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m32 m33 X cs Cell Munch33
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt33 : ART RT Σ16 m33).
  { apply (cl_seg_ART RT AF Σ16 m32 m33 (bv_unsigned sp) 48 [(12187232, 12187240)] Rt32);
      [rewrite Base16; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch33 | | exact Mono33].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl33 : cl_env m33 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m32 m33 _ canary Cl32 Munch33); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above33 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m33).
  { intros w Hi. cbv beta in Hi. rewrite Munch33 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above32 w Hi). }
  assert (Kept33 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m33).
  { apply (pres_fp_trans _ _ _ _ m m32 m33 Kept32).
    apply (PresGrow Σ16 (bv_unsigned sp) [(12187232, 12187240)] m32 m33);
      [rewrite Lv16; intros e Ein; apply in_or_app; right; exact Ein | exact Fr16 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ16 m32 m33 (bv_unsigned sp) 48 [(12187232, 12187240)] Rt32
             ltac:(rewrite Base16; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch33). }
  clear Kept32 Above32 Munch33 Mono33 Inv32 Rt32 Cl32 Stack32 ShBase32 Clean32.
  clear V16Pos V16Top V16Nz.
  (* call 17: ossl_self_test_set_callback_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_self_test_set_callback_new SITE_context_init_17 m m33 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_17, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_17, e_ossl_self_test_set_callback_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above33 (SavedOf m33 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain17 & FpChain17).
  match type of At33s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_self_test_set_callback_new Σ16 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m33 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr16, unsigned_lit by (unfold SITE_context_init_17; clear - Room0; lia); exact Chain17
             | rewrite Gr16, unsigned_lit by (unfold SITE_context_init_17; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr16; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr16; clear - FrmCap; lia
             | rewrite Lv16, length_app, Nat2Z.inj_add, NewLen16; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr16; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg34 (Σ17 & st17 & At34 & LvPost17 & FrPost17 & BasePost17 & CrPost17 & V17Pos & V17Al & V17Top & GrPost17).
  destruct (ASTA_unpack RT Σ17 _ _ cfg34 At34) as (st34 & (m34 & Ret17 & After17 & Pres17 & Cl34 & Obj17) & At34s).
  clear At34 At33s.
  destruct Ret17 as (r170 & r171 & r172 & x171 & x172 & x173 & x174 & x175 & x176 & x177 & r173 & r174 & r175 & r176 & F17 & fc17 & ->).
  rewrite FrameLit in After17, Pres17. destruct After17 as (Rt34 & Inv34 & Mono34 & Stack34).
  rewrite (ret_pc_even SITE_context_init_17) in At34s by (unfold SITE_context_init_17; clear - Room0; lia).
  destruct Obj17 as (ZWr17 & _ & ZBytes17).
  assert (st17Obj : rw_cells asegs m34 st17 [CB 16 (repeat (Z_to_bv 8 0) 16)]) by exact (rw_CB_of_bytes _ _ _ ZBytes17 ZWr17).
  clear ZWr17 ZBytes17.
  repeat match goal with
         | Cell : rw_cells asegs m33 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m34 X cs);
             [ apply (rw_cells_agree_nw asegs m33 m34 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres17;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ16) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_16; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above34 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m34).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres17 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above33 w Hi). }
  assert (Kept34 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m34).
  { apply (pres_fp_trans _ _ _ _ m m33 m34 Kept33).
    apply (PresGrow Σ16 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m33 m34);
      [rewrite Lv16; intros e Ein; apply in_or_app; right; exact Ein | exact Fr16 | clear - FrameLit; lia | | exact Pres17].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept33 Above33 Pres17 Mono34 Inv33 Rt33 Cl33 Stack33 Chain17 FpChain17.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ16) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ17)) by (rewrite LvPost17; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (st17Live : In (st17, 16) (rt_live RT Σ17)) by (rewrite LvPost17; wp_in_lit).
  assert (st17Heap : 17594333495296 <= st17 /\ st17 + 16 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ17 m34 st17 16 Rt34 st17Live ltac:(clear - Rt34; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ17 m34 st17 16 Rt34 st17Live) as Span.
    rewrite BasePost17, Base16 in Span. clear - Span LoInWin; lia. }
  assert (st17Apart : forall w, st17 <= w < st17 + 16 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX st17Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ16 Σ17 m34 [(st17, 16)] st17 16 (bv_unsigned sp) w Rt34 LvPost17
                                        ltac:(wp_in_lit) FrPost17 BasePost17
                                        ltac:(rewrite Base16; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_16; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd17 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(st17, 16)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V17Al.
  assert (Sub11_17 : incl New11 (rt_live RT Σ17)) by (intros e Ein; rewrite LvPost17; repeat first [apply in_or_app; right | right]; exact (Sub11_16 e Ein)).
  rewrite Lv16 in LvPost17. rewrite ?app_assoc, ?app_comm_cons in LvPost17.
  match type of LvPost17 with _ = ?L ++ rt_live RT Σ => remember L as New17 eqn:New17Is in LvPost17 end.
  rename LvPost17 into Lv17.
  assert (NewLen17 : Z.of_nat (length New17) = 100)
    by (rewrite New17Is; rewrite ?length_app; cbn [length]; clear - NewLen16; lia).
  assert (NewPos17 : Forall (fun blk => 0 < snd blk) New17).
  { rewrite New17Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos16; lia | ] | apply Forall_nil | exact NewPos16 ]. }
  assert (NewBnd17 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New17).
  { rewrite New17Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(st17, 16)] ++ New16)). apply Forall_app. split; [exact Bnd17 | exact NewBnd16]. }
  assert (Fr17 : rt_frames RT Σ17 = rt_frames RT Σ) by (rewrite FrPost17; exact Fr16).
  assert (Base17 : rt_sp0 RT Σ17 = rt_sp0 RT Σ) by (rewrite BasePost17; exact Base16).
  assert (Gr17 : rt_cg RT Σ17 = rt_cg RT Σ) by (rewrite GrPost17; exact Gr16).
  assert (Cr17 : rt_credit RT Σ17 = rt_credit RT Σ - (46 + NM_COST))
    by (rewrite CrPost17, Cr16; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost17 BasePost17 GrPost17 CrPost17 Lv16 NewLen16 NewPos16 NewBnd16 Bnd17 Fr16 Base16 Gr16 Cr16 Sub11_16.
  assert (V17Word : 0 <= st17 < 2 ^ 64) by (unfold USTACK_TOP in V17Top; clear - V17Pos V17Top; lia).
  assert (V17Nz : bv_eqb (Z_to_bv 64 st17) (Z_to_bv 64 0) = false) by (clear - V17Word V17Pos; solve_cond_u).
  destruct (ConstsOf Σ17 m34 Rt34) as (ShBase34 & Clean34).
  pose proof (context_init_s17_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_17)
                r170 r171 r172 x171 x172 x173 x174 x175 x176 x177 r173 r174 r175 r176 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 j1
                g13 g18 g19 g20 g21 F17 fc17 m34 lo) as Seg17.
  repeat match type of Seg17 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ17 m34 Rt34) | (apply (ShadowOf Σ17 m34); [exact Rt34 | clear - Rt34; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg17 ok); clear ok
         end.
  cl_lift Seg17 At34s cfg35 At35.
  destruct (ASTA_unpack RT Σ17 _ _ cfg35 At35) as (st35 & Post17 & At35s). clear At35 At34s.
  repeat match goal with
         | Old : rw_cells asegs m34 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post17 as (m35 & -> & Munch35 & Mono35 & Inv35
                     & FSelfT & FNonce & FBio & FGprops & FDefns & FNmap & FPsd
                     & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg & FConf
                     & FEvp & FLock & Frame35 & FComp & FThr & FIndic & FChild
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack35).
  repeat match goal with
         | Cell : rw_cells asegs m34 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m34 m35 X cs Cell Munch35
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt35 : ART RT Σ17 m35).
  { apply (cl_seg_ART RT AF Σ17 m34 m35 (bv_unsigned sp) 48 [(12187296, 12187304)] Rt34);
      [rewrite Base17; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch35 | | exact Mono35].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl35 : cl_env m35 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m34 m35 _ canary Cl34 Munch35); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above35 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m35).
  { intros w Hi. cbv beta in Hi. rewrite Munch35 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above34 w Hi). }
  assert (Kept35 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m35).
  { apply (pres_fp_trans _ _ _ _ m m34 m35 Kept34).
    apply (PresGrow Σ17 (bv_unsigned sp) [(12187296, 12187304)] m34 m35);
      [rewrite Lv17; intros e Ein; apply in_or_app; right; exact Ein | exact Fr17 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ17 m34 m35 (bv_unsigned sp) 48 [(12187296, 12187304)] Rt34
             ltac:(rewrite Base17; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch35). }
  clear Kept34 Above34 Munch35 Mono35 Inv34 Rt34 Cl34 Stack34 ShBase34 Clean34.
  clear V17Pos V17Top V17Nz.
  (* call 18: ossl_indicator_set_callback_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_indicator_set_callback_new SITE_context_init_18 m m35 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_18, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_18, e_ossl_indicator_set_callback_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above35 (SavedOf m35 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain18 & FpChain18).
  match type of At35s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_indicator_set_callback_new Σ17 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m35 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr17, unsigned_lit by (unfold SITE_context_init_18; clear - Room0; lia); exact Chain18
             | rewrite Gr17, unsigned_lit by (unfold SITE_context_init_18; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr17; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr17; clear - FrmCap; lia
             | rewrite Lv17, length_app, Nat2Z.inj_add, NewLen17; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr17; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg36 (Σ18 & ic18 & At36 & LvPost18 & FrPost18 & BasePost18 & CrPost18 & V18Pos & V18Al & V18Top & GrPost18).
  destruct (ASTA_unpack RT Σ18 _ _ cfg36 At36) as (st36 & (m36 & Ret18 & After18 & Pres18 & Cl36 & Obj18) & At36s).
  clear At36 At35s.
  destruct Ret18 as (r180 & r181 & r182 & x181 & x182 & x183 & x184 & x185 & x186 & x187 & r183 & r184 & r185 & r186 & F18 & fc18 & ->).
  rewrite FrameLit in After18, Pres18. destruct After18 as (Rt36 & Inv36 & Mono36 & Stack36).
  rewrite (ret_pc_even SITE_context_init_18) in At36s by (unfold SITE_context_init_18; clear - Room0; lia).
  destruct Obj18 as (ZWr18 & _ & ZBytes18).
  assert (ic18Obj : rw_cells asegs m36 ic18 [CB 8 (repeat (Z_to_bv 8 0) 8)]) by exact (rw_CB_of_bytes _ _ _ ZBytes18 ZWr18).
  clear ZWr18 ZBytes18.
  repeat match goal with
         | Cell : rw_cells asegs m35 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m36 X cs);
             [ apply (rw_cells_agree_nw asegs m35 m36 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres18;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ17) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_17; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above36 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m36).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres18 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above35 w Hi). }
  assert (Kept36 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m36).
  { apply (pres_fp_trans _ _ _ _ m m35 m36 Kept35).
    apply (PresGrow Σ17 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m35 m36);
      [rewrite Lv17; intros e Ein; apply in_or_app; right; exact Ein | exact Fr17 | clear - FrameLit; lia | | exact Pres18].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept35 Above35 Pres18 Mono36 Inv35 Rt35 Cl35 Stack35 Chain18 FpChain18.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ17) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ18)) by (rewrite LvPost18; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (ic18Live : In (ic18, 8) (rt_live RT Σ18)) by (rewrite LvPost18; wp_in_lit).
  assert (ic18Heap : 17594333495296 <= ic18 /\ ic18 + 8 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ18 m36 ic18 8 Rt36 ic18Live ltac:(clear - Rt36; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ18 m36 ic18 8 Rt36 ic18Live) as Span.
    rewrite BasePost18, Base17 in Span. clear - Span LoInWin; lia. }
  assert (ic18Apart : forall w, ic18 <= w < ic18 + 8 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX ic18Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ17 Σ18 m36 [(ic18, 8)] ic18 8 (bv_unsigned sp) w Rt36 LvPost18
                                        ltac:(wp_in_lit) FrPost18 BasePost18
                                        ltac:(rewrite Base17; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_17; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd18 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(ic18, 8)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V18Al.
  assert (Sub11_18 : incl New11 (rt_live RT Σ18)) by (intros e Ein; rewrite LvPost18; repeat first [apply in_or_app; right | right]; exact (Sub11_17 e Ein)).
  rewrite Lv17 in LvPost18. rewrite ?app_assoc, ?app_comm_cons in LvPost18.
  match type of LvPost18 with _ = ?L ++ rt_live RT Σ => remember L as New18 eqn:New18Is in LvPost18 end.
  rename LvPost18 into Lv18.
  assert (NewLen18 : Z.of_nat (length New18) = 101)
    by (rewrite New18Is; rewrite ?length_app; cbn [length]; clear - NewLen17; lia).
  assert (NewPos18 : Forall (fun blk => 0 < snd blk) New18).
  { rewrite New18Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos17; lia | ] | apply Forall_nil | exact NewPos17 ]. }
  assert (NewBnd18 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New18).
  { rewrite New18Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(ic18, 8)] ++ New17)). apply Forall_app. split; [exact Bnd18 | exact NewBnd17]. }
  assert (Fr18 : rt_frames RT Σ18 = rt_frames RT Σ) by (rewrite FrPost18; exact Fr17).
  assert (Base18 : rt_sp0 RT Σ18 = rt_sp0 RT Σ) by (rewrite BasePost18; exact Base17).
  assert (Gr18 : rt_cg RT Σ18 = rt_cg RT Σ) by (rewrite GrPost18; exact Gr17).
  assert (Cr18 : rt_credit RT Σ18 = rt_credit RT Σ - (46 + NM_COST))
    by (rewrite CrPost18, Cr17; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost18 BasePost18 GrPost18 CrPost18 Lv17 NewLen17 NewPos17 NewBnd17 Bnd18 Fr17 Base17 Gr17 Cr17 Sub11_17.
  assert (V18Word : 0 <= ic18 < 2 ^ 64) by (unfold USTACK_TOP in V18Top; clear - V18Pos V18Top; lia).
  assert (V18Nz : bv_eqb (Z_to_bv 64 ic18) (Z_to_bv 64 0) = false) by (clear - V18Word V18Pos; solve_cond_u).
  destruct (ConstsOf Σ18 m36 Rt36) as (ShBase36 & Clean36).
  pose proof (context_init_s18_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_18)
                r180 r181 r182 x181 x182 x183 x184 x185 x186 x187 r183 r184 r185 r186 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 ic18 j1
                g13 g19 g20 g21 F18 fc18 m36 lo) as Seg18.
  repeat match type of Seg18 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ18 m36 Rt36) | (apply (ShadowOf Σ18 m36); [exact Rt36 | clear - Rt36; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg18 ok); clear ok
         end.
  cl_lift Seg18 At36s cfg37 At37.
  destruct (ASTA_unpack RT Σ18 _ _ cfg37 At37) as (st37 & Post18 & At37s). clear At37 At36s.
  repeat match goal with
         | Old : rw_cells asegs m36 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post18 as (m37 & -> & Munch37 & Mono37 & Inv37
                     & FIndic & FSelfT & FNonce & FBio & FGprops & FDefns & FNmap
                     & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt & FDrbg
                     & FConf & FEvp & FLock & Frame37 & FComp & FThr & FChild
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack37).
  repeat match goal with
         | Cell : rw_cells asegs m36 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m36 m37 X cs Cell Munch37
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt37 : ART RT Σ18 m37).
  { apply (cl_seg_ART RT AF Σ18 m36 m37 (bv_unsigned sp) 48 [(12187304, 12187312)] Rt36);
      [rewrite Base18; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch37 | | exact Mono37].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl37 : cl_env m37 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m36 m37 _ canary Cl36 Munch37); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above37 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m37).
  { intros w Hi. cbv beta in Hi. rewrite Munch37 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above36 w Hi). }
  assert (Kept37 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m37).
  { apply (pres_fp_trans _ _ _ _ m m36 m37 Kept36).
    apply (PresGrow Σ18 (bv_unsigned sp) [(12187304, 12187312)] m36 m37);
      [rewrite Lv18; intros e Ein; apply in_or_app; right; exact Ein | exact Fr18 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ18 m36 m37 (bv_unsigned sp) 48 [(12187304, 12187312)] Rt36
             ltac:(rewrite Base18; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch37). }
  clear Kept36 Above36 Munch37 Mono37 Inv36 Rt36 Cl36 Stack36 ShBase36 Clean36.
  clear V18Pos V18Top V18Nz.
  (* call 19: ossl_threads_ctx_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_threads_ctx_new SITE_context_init_19 m m37 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_19, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_19, e_ossl_threads_ctx_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above37 (SavedOf m37 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain19 & FpChain19).
  match type of At37s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_threads_ctx_new Σ18 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m37 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr18, unsigned_lit by (unfold SITE_context_init_19; clear - Room0; lia); exact Chain19
             | rewrite Gr18, unsigned_lit by (unfold SITE_context_init_19; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr18; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr18; clear - FrmCap; lia
             | rewrite Lv18, length_app, Nat2Z.inj_add, NewLen18; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr18; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg38 (Σ19 & th19 & tm19 & tc19 & At38 & LvPost19 & FrPost19 & BasePost19 & CrPost19 & V19Pos & V19Al & V19Top & tm19Pos & tm19Al & tm19Top & tc19Pos & tc19Al & tc19Top & GrPost19).
  destruct (ASTA_unpack RT Σ19 _ _ cfg38 At38) as (st38 & (jc19 & m38 & Ret19 & After19 & Pres19 & Cl38 & Obj19) & At38s).
  clear At38 At37s.
  destruct Ret19 as (r190 & r191 & r192 & x191 & x192 & x193 & x194 & x195 & x196 & x197 & r193 & r194 & r195 & r196 & F19 & fc19 & ->).
  rewrite FrameLit in After19, Pres19. destruct After19 as (Rt38 & Inv38 & Mono38 & Stack38).
  rewrite (ret_pc_even SITE_context_init_19) in At38s by (unfold SITE_context_init_19; clear - Room0; lia).
  destruct Obj19 as (_ & _ & _ & _ & _ & _ & th19Obj & tm19Obj & tc19Obj).
  repeat match goal with
         | Cell : rw_cells asegs m37 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m38 X cs);
             [ apply (rw_cells_agree_nw asegs m37 m38 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres19;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ18) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_18; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above38 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m38).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres19 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above37 w Hi). }
  assert (Kept38 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m38).
  { apply (pres_fp_trans _ _ _ _ m m37 m38 Kept37).
    apply (PresGrow Σ18 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m37 m38);
      [rewrite Lv18; intros e Ein; apply in_or_app; right; exact Ein | exact Fr18 | clear - FrameLit; lia | | exact Pres19].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept37 Above37 Pres19 Mono38 Inv37 Rt37 Cl37 Stack37 Chain19 FpChain19.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ18) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ19)) by (rewrite LvPost19; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (tc19Live : In (tc19, 48) (rt_live RT Σ19)) by (rewrite LvPost19; wp_in_lit).
  assert (tc19Heap : 17594333495296 <= tc19 /\ tc19 + 48 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ19 m38 tc19 48 Rt38 tc19Live ltac:(clear - Rt38; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ19 m38 tc19 48 Rt38 tc19Live) as Span.
    rewrite BasePost19, Base18 in Span. clear - Span LoInWin; lia. }
  assert (tm19Live : In (tm19, 40) (rt_live RT Σ19)) by (rewrite LvPost19; wp_in_lit).
  assert (tm19Heap : 17594333495296 <= tm19 /\ tm19 + 40 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ19 m38 tm19 40 Rt38 tm19Live ltac:(clear - Rt38; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ19 m38 tm19 40 Rt38 tm19Live) as Span.
    rewrite BasePost19, Base18 in Span. clear - Span LoInWin; lia. }
  assert (th19Live : In (th19, 32) (rt_live RT Σ19)) by (rewrite LvPost19; wp_in_lit).
  assert (th19Heap : 17594333495296 <= th19 /\ th19 + 32 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ19 m38 th19 32 Rt38 th19Live ltac:(clear - Rt38; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ19 m38 th19 32 Rt38 th19Live) as Span.
    rewrite BasePost19, Base18 in Span. clear - Span LoInWin; lia. }
  assert (tc19Apart : forall w, tc19 <= w < tc19 + 48 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX tc19Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ18 Σ19 m38 [(tc19, 48); (tm19, 40); (th19, 32)] tc19 48 (bv_unsigned sp) w Rt38 LvPost19
                                        ltac:(wp_in_lit) FrPost19 BasePost19
                                        ltac:(rewrite Base18; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_18; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (tm19Apart : forall w, tm19 <= w < tm19 + 40 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX tm19Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ18 Σ19 m38 [(tc19, 48); (tm19, 40); (th19, 32)] tm19 40 (bv_unsigned sp) w Rt38 LvPost19
                                        ltac:(wp_in_lit) FrPost19 BasePost19
                                        ltac:(rewrite Base18; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_18; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (th19Apart : forall w, th19 <= w < th19 + 32 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX th19Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ18 Σ19 m38 [(tc19, 48); (tm19, 40); (th19, 32)] th19 32 (bv_unsigned sp) w Rt38 LvPost19
                                        ltac:(wp_in_lit) FrPost19 BasePost19
                                        ltac:(rewrite Base18; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_18; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd19 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(tc19, 48); (tm19, 40); (th19, 32)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V19Al tm19Pos tm19Al tm19Top tc19Pos tc19Al tc19Top.
  assert (Sub11_19 : incl New11 (rt_live RT Σ19)) by (intros e Ein; rewrite LvPost19; repeat first [apply in_or_app; right | right]; exact (Sub11_18 e Ein)).
  rewrite Lv18 in LvPost19. rewrite ?app_assoc, ?app_comm_cons in LvPost19.
  match type of LvPost19 with _ = ?L ++ rt_live RT Σ => remember L as New19 eqn:New19Is in LvPost19 end.
  rename LvPost19 into Lv19.
  assert (NewLen19 : Z.of_nat (length New19) = 104)
    by (rewrite New19Is; rewrite ?length_app; cbn [length]; clear - NewLen18; lia).
  assert (NewPos19 : Forall (fun blk => 0 < snd blk) New19).
  { rewrite New19Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos18; lia | ] | apply Forall_nil | exact NewPos18 ]. }
  assert (NewBnd19 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New19).
  { rewrite New19Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(tc19, 48); (tm19, 40); (th19, 32)] ++ New18)). apply Forall_app. split; [exact Bnd19 | exact NewBnd18]. }
  assert (Fr19 : rt_frames RT Σ19 = rt_frames RT Σ) by (rewrite FrPost19; exact Fr18).
  assert (Base19 : rt_sp0 RT Σ19 = rt_sp0 RT Σ) by (rewrite BasePost19; exact Base18).
  assert (Gr19 : rt_cg RT Σ19 = rt_cg RT Σ) by (rewrite GrPost19; exact Gr18).
  assert (Cr19 : rt_credit RT Σ19 = rt_credit RT Σ - (46 + NM_COST))
    by (rewrite CrPost19, Cr18; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost19 BasePost19 GrPost19 CrPost19 Lv18 NewLen18 NewPos18 NewBnd18 Bnd19 Fr18 Base18 Gr18 Cr18 Sub11_18.
  assert (V19Word : 0 <= th19 < 2 ^ 64) by (unfold USTACK_TOP in V19Top; clear - V19Pos V19Top; lia).
  assert (V19Nz : bv_eqb (Z_to_bv 64 th19) (Z_to_bv 64 0) = false) by (clear - V19Word V19Pos; solve_cond_u).
  destruct (ConstsOf Σ19 m38 Rt38) as (ShBase38 & Clean38).
  pose proof (context_init_s19_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_19)
                r190 r191 r192 x191 x192 x193 x194 x195 x196 x197 r193 r194 r195 r196 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 ic18 th19 j1
                g13 g20 g21 F19 fc19 m38 lo) as Seg19.
  repeat match type of Seg19 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ19 m38 Rt38) | (apply (ShadowOf Σ19 m38); [exact Rt38 | clear - Rt38; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg19 ok); clear ok
         end.
  cl_lift Seg19 At38s cfg39 At39.
  destruct (ASTA_unpack RT Σ19 _ _ cfg39 At39) as (st39 & Post19 & At39s). clear At39 At38s.
  repeat match goal with
         | Old : rw_cells asegs m38 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post19 as (m39 & -> & Munch39 & Mono39 & Inv39
                     & FThr & FIndic & FSelfT & FNonce & FBio & FGprops & FDefns
                     & FNmap & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa & FDecSt
                     & FDrbg & FConf & FEvp & FLock & Frame39 & FComp & FChild
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack39).
  repeat match goal with
         | Cell : rw_cells asegs m38 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m38 m39 X cs Cell Munch39
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt39 : ART RT Σ19 m39).
  { apply (cl_seg_ART RT AF Σ19 m38 m39 (bv_unsigned sp) 48 [(12187312, 12187320)] Rt38);
      [rewrite Base19; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch39 | | exact Mono39].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl39 : cl_env m39 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m38 m39 _ canary Cl38 Munch39); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above39 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m39).
  { intros w Hi. cbv beta in Hi. rewrite Munch39 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above38 w Hi). }
  assert (Kept39 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m39).
  { apply (pres_fp_trans _ _ _ _ m m38 m39 Kept38).
    apply (PresGrow Σ19 (bv_unsigned sp) [(12187312, 12187320)] m38 m39);
      [rewrite Lv19; intros e Ein; apply in_or_app; right; exact Ein | exact Fr19 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ19 m38 m39 (bv_unsigned sp) 48 [(12187312, 12187320)] Rt38
             ltac:(rewrite Base19; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch39). }
  clear Kept38 Above38 Munch39 Mono39 Inv38 Rt38 Cl38 Stack38 ShBase38 Clean38.
  clear V19Pos V19Top V19Nz.
  (* call 20: ossl_child_prov_ctx_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_child_prov_ctx_new SITE_context_init_20 m m39 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_20, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_20, e_ossl_child_prov_ctx_new) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above39 (SavedOf m39 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain20 & FpChain20).
  match type of At39s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_child_prov_ctx_new Σ19 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m39 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr19, unsigned_lit by (unfold SITE_context_init_20; clear - Room0; lia); exact Chain20
             | rewrite Gr19, unsigned_lit by (unfold SITE_context_init_20; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr19; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr19; clear - FrmCap; lia
             | rewrite Lv19, length_app, Nat2Z.inj_add, NewLen19; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr19; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg40 (Σ20 & ch20 & At40 & LvPost20 & FrPost20 & BasePost20 & CrPost20 & V20Pos & V20Al & V20Top & GrPost20).
  destruct (ASTA_unpack RT Σ20 _ _ cfg40 At40) as (st40 & (m40 & Ret20 & After20 & Pres20 & Cl40 & Obj20) & At40s).
  clear At40 At39s.
  destruct Ret20 as (r200 & r201 & r202 & x201 & x202 & x203 & x204 & x205 & x206 & x207 & r203 & r204 & r205 & r206 & F20 & fc20 & ->).
  rewrite FrameLit in After20, Pres20. destruct After20 as (Rt40 & Inv40 & Mono40 & Stack40).
  rewrite (ret_pc_even SITE_context_init_20) in At40s by (unfold SITE_context_init_20; clear - Room0; lia).
  destruct Obj20 as (ZWr20 & _ & ZBytes20).
  assert (ch20Obj : rw_cells asegs m40 ch20 [CB 88 (repeat (Z_to_bv 8 0) 88)]) by exact (rw_CB_of_bytes _ _ _ ZBytes20 ZWr20).
  clear ZWr20 ZBytes20.
  repeat match goal with
         | Cell : rw_cells asegs m39 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m40 X cs);
             [ apply (rw_cells_agree_nw asegs m39 m40 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres20;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ19) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_19; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above40 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m40).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres20 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above39 w Hi). }
  assert (Kept40 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m40).
  { apply (pres_fp_trans _ _ _ _ m m39 m40 Kept39).
    apply (PresGrow Σ19 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m39 m40);
      [rewrite Lv19; intros e Ein; apply in_or_app; right; exact Ein | exact Fr19 | clear - FrameLit; lia | | exact Pres20].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept39 Above39 Pres20 Mono40 Inv39 Rt39 Cl39 Stack39 Chain20 FpChain20.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ19) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ20)) by (rewrite LvPost20; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (ch20Live : In (ch20, 88) (rt_live RT Σ20)) by (rewrite LvPost20; wp_in_lit).
  assert (ch20Heap : 17594333495296 <= ch20 /\ ch20 + 88 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ20 m40 ch20 88 Rt40 ch20Live ltac:(clear - Rt40; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ20 m40 ch20 88 Rt40 ch20Live) as Span.
    rewrite BasePost20, Base19 in Span. clear - Span LoInWin; lia. }
  assert (ch20Apart : forall w, ch20 <= w < ch20 + 88 -> outside [(ps11, ps11 + 48); (pk11, pk11 + 40); (pla11, pla11 + 104); (pba11, pba11 + 128); (plb11, plb11 + 104); (pbb11, pbb11 + 128); (pqa11, pqa11 + 56); (pqb11, pqb11 + 56); (G_ALLOW_CUST, G_ALLOW_CUST + 1)] w).
  { intros w InX. cbn [outside]. unfold G_ALLOW_CUST.
    repeat (split; [ first [ clear - InX ch20Heap; lia
                           | intros InP; match type of InP with ?P <= _ < _ + ?S =>
                               apply (wg_newchunk_apart RT AF Σ19 Σ20 m40 [(ch20, 88)] ch20 88 (bv_unsigned sp) w Rt40 LvPost20
                                        ltac:(wp_in_lit) FrPost20 BasePost20
                                        ltac:(rewrite Base19; clear - LoInWin Room0; lia) ltac:(clear - InX; try unfold NB_BYTES; lia));
                               [ apply (acl_live _ _ _ P S w); [apply Sub11_19; assumption | exact InP] | exact InX ] end ] |]).
    exact I. }
  assert (Bnd20 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(ch20, 88)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V20Al.
  assert (Sub11_20 : incl New11 (rt_live RT Σ20)) by (intros e Ein; rewrite LvPost20; repeat first [apply in_or_app; right | right]; exact (Sub11_19 e Ein)).
  rewrite Lv19 in LvPost20. rewrite ?app_assoc, ?app_comm_cons in LvPost20.
  match type of LvPost20 with _ = ?L ++ rt_live RT Σ => remember L as New20 eqn:New20Is in LvPost20 end.
  rename LvPost20 into Lv20.
  assert (NewLen20 : Z.of_nat (length New20) = 105)
    by (rewrite New20Is; rewrite ?length_app; cbn [length]; clear - NewLen19; lia).
  assert (NewPos20 : Forall (fun blk => 0 < snd blk) New20).
  { rewrite New20Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos19; lia | ] | apply Forall_nil | exact NewPos19 ]. }
  assert (NewBnd20 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New20).
  { rewrite New20Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(ch20, 88)] ++ New19)). apply Forall_app. split; [exact Bnd20 | exact NewBnd19]. }
  assert (Fr20 : rt_frames RT Σ20 = rt_frames RT Σ) by (rewrite FrPost20; exact Fr19).
  assert (Base20 : rt_sp0 RT Σ20 = rt_sp0 RT Σ) by (rewrite BasePost20; exact Base19).
  assert (Gr20 : rt_cg RT Σ20 = rt_cg RT Σ) by (rewrite GrPost20; exact Gr19).
  assert (Cr20 : rt_credit RT Σ20 = rt_credit RT Σ - (46 + NM_COST))
    by (rewrite CrPost20, Cr19; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost20 BasePost20 GrPost20 CrPost20 Lv19 NewLen19 NewPos19 NewBnd19 Bnd20 Fr19 Base19 Gr19 Cr19 Sub11_19.
  assert (V20Word : 0 <= ch20 < 2 ^ 64) by (unfold USTACK_TOP in V20Top; clear - V20Pos V20Top; lia).
  assert (V20Nz : bv_eqb (Z_to_bv 64 ch20) (Z_to_bv 64 0) = false) by (clear - V20Word V20Pos; solve_cond_u).
  destruct (ConstsOf Σ20 m40 Rt40) as (ShBase40 & Clean40).
  pose proof (context_init_s20_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_20)
                r200 r201 r202 x201 x202 x203 x204 x205 x206 x207 r203 r204 r205 r206 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 ic18 th19 ch20 j1
                g13 g21 F20 fc20 m40 lo) as Seg20.
  repeat match type of Seg20 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ20 m40 Rt40) | (apply (ShadowOf Σ20 m40); [exact Rt40 | clear - Rt40; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg20 ok); clear ok
         end.
  cl_lift Seg20 At40s cfg41 At41.
  destruct (ASTA_unpack RT Σ20 _ _ cfg41 At41) as (st41 & Post20 & At41s). clear At41 At40s.
  repeat match goal with
         | Old : rw_cells asegs m40 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post20 as (m41 & -> & Munch41 & Mono41 & Inv41
                     & FChild & FThr & FIndic & FSelfT & FNonce & FBio & FGprops
                     & FDefns & FNmap & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa
                     & FDecSt & FDrbg & FConf & FEvp & FLock & Frame41 & FComp
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack41).
  repeat match goal with
         | Cell : rw_cells asegs m40 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m40 m41 X cs Cell Munch41
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt41 : ART RT Σ20 m41).
  { apply (cl_seg_ART RT AF Σ20 m40 m41 (bv_unsigned sp) 48 [(12187256, 12187264)] Rt40);
      [rewrite Base20; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch41 | | exact Mono41].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl41 : cl_env m41 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m40 m41 _ canary Cl40 Munch41); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above41 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m41).
  { intros w Hi. cbv beta in Hi. rewrite Munch41 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above40 w Hi). }
  assert (Kept41 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m41).
  { apply (pres_fp_trans _ _ _ _ m m40 m41 Kept40).
    apply (PresGrow Σ20 (bv_unsigned sp) [(12187256, 12187264)] m40 m41);
      [rewrite Lv20; intros e Ein; apply in_or_app; right; exact Ein | exact Fr20 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ20 m40 m41 (bv_unsigned sp) 48 [(12187256, 12187264)] Rt40
             ltac:(rewrite Base20; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch41). }
  clear Kept40 Above40 Munch41 Mono41 Inv40 Rt40 Cl40 Stack40 ShBase40 Clean40.
  clear V20Pos V20Top V20Nz.
  (* call 21: ossl_property_parse_init *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_property_parse_init SITE_context_init_21 m m41 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_21, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_21, e_property_parse_init) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above41 (SavedOf m41 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain21 & FpChain21).
  match type of At41s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_property_parse_init Σ20 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m41 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary ps11 pk11 pla11 pba11 plb11 pbb11 pqa11 pqb11)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr20, unsigned_lit by (unfold SITE_context_init_21; clear - Room0; lia); exact Chain21
             | rewrite Gr20, unsigned_lit by (unfold SITE_context_init_21; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr20; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr20; clear - FrmCap; lia
             | rewrite Lv20, length_app, Nat2Z.inj_add, NewLen20; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr20; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia
             | rewrite Lv20; apply Forall_app; split; assumption
             | apply (proj1 (Forall_forall _ _) PsdAl); wp_in_lit
             | apply Sub11_20; assumption ] end).
  intros cfg42 (Σ21 & pi8 & pi9 & pi10 & pi11 & pi12 & pi13 & pi14 & pi15 & pi16 & pi17 & pi18 & pi19 & pi20 & pi21 & pi22 & pi23 & pi24 & pi25 & At42 & LvPost21 & FrPost21 & BasePost21 & CrPost21 & pi8Pos & pi8Al & pi8Top & pi9Pos & pi9Al & pi9Top & pi10Pos & pi10Al & pi10Top & pi11Pos & pi11Al & pi11Top & pi12Pos & pi12Al & pi12Top & pi13Pos & pi13Al & pi13Top & pi14Pos & pi14Al & pi14Top & pi15Pos & pi15Al & pi15Top & pi16Pos & pi16Al & pi16Top & pi17Pos & pi17Al & pi17Top & pi18Pos & pi18Al & pi18Top & pi19Pos & pi19Al & pi19Top & pi20Pos & pi20Al & pi20Top & pi21Pos & pi21Al & pi21Top & pi22Pos & pi22Al & pi22Top & pi23Pos & pi23Al & pi23Top & pi24Pos & pi24Al & pi24Top & pi25Pos & pi25Al & pi25Top & GrPost21).
  destruct (ASTA_unpack RT Σ21 _ _ cfg42 At42) as (st42 & (m42 & Ret21 & After21 & Pres21 & Cl42) & At42s).
  clear At42 At41s.
  destruct Ret21 as (r210 & r211 & r212 & x211 & x212 & x213 & x214 & x215 & x216 & x217 & r213 & r214 & r215 & r216 & F21 & fc21 & ->).
  rewrite FrameLit in After21, Pres21. destruct After21 as (Rt42 & Inv42 & Stack42).
  rewrite (ret_pc_even SITE_context_init_21) in At42s by (unfold SITE_context_init_21; clear - Room0; lia).
  repeat match goal with
         | Cell : rw_cells asegs m41 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m42 X cs);
             [ apply (rw_cells_agree_nw asegs m41 m42 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres21;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ20) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_20; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Ap : forall w, b <= w < _ -> outside _ w |- _ => apply Ap; clear - Rw; lia
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above42 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m42).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres21 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above41 w Hi). }
  assert (Kept42 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m42).
  { apply (pres_fp_trans _ _ _ _ m m41 m42 Kept41).
    apply (pres_fp_sub _ _ _ _ _ _ _ _ m41 m42 Pres21).
    intros x Acl Out. split.
    - apply (aclient_mono _ _ _ _ _ _ _ Acl);
        [rewrite Lv20; intros e Ein; apply in_or_app; right; exact Ein | rewrite Fr20; intros e Ein; exact Ein | clear - FrameLit; lia].
    - pose proof (PsdApart x Acl) as Apart. unfold Wctx in Out. cbn [outside] in Out |- *.
      repeat (split; [first [ solve [apply Apart; assumption] | clear - Out; tauto ] |]). exact I. }
  clear Kept41 Above41 Pres21 Inv41 Rt41 Cl41 Stack41 Chain21 FpChain21.
  repeat match goal with Old : rw_cells asegs m41 _ _ |- _ => clear Old end.
  repeat match goal with Ap : forall w : Z, _ -> outside _ w |- _ => clear Ap end.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ20) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ21)) by (rewrite LvPost21; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (Bnd21 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(pi25, 24); (pi24, 18); (pi23, 24); (pi22, 32); (pi21, 19); (pi20, 24); (pi19, 25); (pi18, 24); (pi17, 48); (pi16, 21); (pi15, 24); (pi14, 22); (pi13, 24); (pi12, 20); (pi11, 24); (pi10, 23); (pi9, 24); (pi8, 24)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear pi8Pos pi8Al pi8Top pi9Pos pi9Al pi9Top pi10Pos pi10Al pi10Top pi11Pos pi11Al pi11Top pi12Pos pi12Al pi12Top pi13Pos pi13Al pi13Top pi14Pos pi14Al pi14Top pi15Pos pi15Al pi15Top pi16Pos pi16Al pi16Top pi17Pos pi17Al pi17Top pi18Pos pi18Al pi18Top pi19Pos pi19Al pi19Top pi20Pos pi20Al pi20Top pi21Pos pi21Al pi21Top pi22Pos pi22Al pi22Top pi23Pos pi23Al pi23Top pi24Pos pi24Al pi24Top pi25Pos pi25Al pi25Top.
  assert (Sub11_21 : incl New11 (rt_live RT Σ21)) by (intros e Ein; rewrite LvPost21; repeat first [apply in_or_app; right | right]; exact (Sub11_20 e Ein)).
  rewrite Lv20 in LvPost21. rewrite ?app_assoc, ?app_comm_cons in LvPost21.
  match type of LvPost21 with _ = ?L ++ rt_live RT Σ => remember L as New21 eqn:New21Is in LvPost21 end.
  rename LvPost21 into Lv21.
  assert (NewLen21 : Z.of_nat (length New21) = 123)
    by (rewrite New21Is; rewrite ?length_app; cbn [length]; clear - NewLen20; lia).
  assert (NewPos21 : Forall (fun blk => 0 < snd blk) New21).
  { rewrite New21Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos20; lia | ] | apply Forall_nil | exact NewPos20 ]. }
  assert (NewBnd21 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New21).
  { rewrite New21Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(pi25, 24); (pi24, 18); (pi23, 24); (pi22, 32); (pi21, 19); (pi20, 24); (pi19, 25); (pi18, 24); (pi17, 48); (pi16, 21); (pi15, 24); (pi14, 22); (pi13, 24); (pi12, 20); (pi11, 24); (pi10, 23); (pi9, 24); (pi8, 24)] ++ New20)). apply Forall_app. split; [exact Bnd21 | exact NewBnd20]. }
  assert (Fr21 : rt_frames RT Σ21 = rt_frames RT Σ) by (rewrite FrPost21; exact Fr20).
  assert (Base21 : rt_sp0 RT Σ21 = rt_sp0 RT Σ) by (rewrite BasePost21; exact Base20).
  assert (Gr21 : rt_cg RT Σ21 = rt_cg RT Σ) by (rewrite GrPost21; exact Gr20).
  assert (Cr21 : rt_credit RT Σ21 = rt_credit RT Σ - (46 + NM_COST + PPI_COST))
    by (rewrite CrPost21, Cr20; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost21 BasePost21 GrPost21 CrPost21 Lv20 NewLen20 NewPos20 NewBnd20 Bnd21 Fr20 Base20 Gr20 Cr20 Sub11_20.
  destruct (ConstsOf Σ21 m42 Rt42) as (ShBase42 & Clean42).
  pose proof (context_init_s21_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_21)
                r210 r211 r212 x211 x212 x213 x214 x215 x216 x217 r213 r214 r215 r216 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 ic18 th19 ch20 j1
                g21 F21 fc21 m42 lo) as Seg21.
  repeat match type of Seg21 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ21 m42 Rt42) | (apply (ShadowOf Σ21 m42); [exact Rt42 | clear - Rt42; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg21 ok); clear ok
         end.
  cl_lift Seg21 At42s cfg43 At43.
  destruct (ASTA_unpack RT Σ21 _ _ cfg43 At43) as (st43 & Post21 & At43s). clear At43 At42s.
  repeat match goal with
         | Old : rw_cells asegs m42 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post21 as (m43 & -> & Munch43 & Mono43 & Inv43
                     & FChild & FThr & FIndic & FSelfT & FNonce & FBio & FGprops
                     & FDefns & FNmap & FPsd & FProvSt & FLdrSt & FEncSt & FDecCa
                     & FDecSt & FDrbg & FConf & FEvp & FLock & Frame43 & FComp
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack43).
  repeat match goal with
         | Cell : rw_cells asegs m42 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m42 m43 X cs Cell Munch43
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt43 : ART RT Σ21 m43).
  { apply (cl_seg_ART RT AF Σ21 m42 m43 (bv_unsigned sp) 48 [] Rt42);
      [rewrite Base21; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch43 | | exact Mono43].
    intros x Inside. exfalso. apply Inside. exact I. }
  assert (Cl43 : cl_env m43 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m42 m43 _ canary Cl42 Munch43); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Above43 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m43).
  { intros w Hi. cbv beta in Hi. rewrite Munch43 by (clear - Hi LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I).
    exact (Above42 w Hi). }
  assert (Kept43 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m43).
  { apply (pres_fp_trans _ _ _ _ m m42 m43 Kept42).
    apply (PresGrow Σ21 (bv_unsigned sp) [] m42 m43);
      [rewrite Lv21; intros e Ein; apply in_or_app; right; exact Ein | exact Fr21 | clear - FrameLit; lia | intros; exact I | ].
    exact (cl_seg_pres RT AF Σ21 m42 m43 (bv_unsigned sp) 48 [] Rt42
             ltac:(rewrite Base21; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch43). }
  clear Kept42 Above42 Munch43 Mono43 Inv42 Rt42 Cl42 Stack42 ShBase42 Clean42.
  (* call 22: ossl_load_builtin_compressions *)
  destruct (cl_chain_call (rt_cg RT Σ) e_context_init e_ossl_load_builtin_compressions SITE_context_init_22 m m43 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -48)) outer Chain0
              (proj1 Edges (SITE_context_init_22, e_context_init) ltac:(apply in_or_app; left; wp_in_lit))
              (proj2 Edges (SITE_context_init_22, e_ossl_load_builtin_compressions) ltac:(apply in_or_app; left; wp_in_lit))
              FpChain0 Above43 (SavedOf m43 j1 ltac:(assumption)) ltac:(rewrite FrameLit; clear - FrameLit; lia) SpRoom16) as (Chain22 & FpChain22).
  match type of At43s with
  | ASTA _ _ _ (eq (MS (mkR ?xra ?xsp ?xgp ?xtp ?xt0 ?xt1 ?xt2 ?xs0 ?xs1 ?xa0 ?xa1 ?xa2 ?xa3 ?xa4 ?xa5 ?xa6 ?xa7
                         ?xs2 ?xs3 ?xs4 ?xs5 ?xs6 ?xs7 ?xs8 ?xs9 ?xs10 ?xs11 ?xt3 ?xt4 ?xt5 ?xt6) ?xF _ ?xfc _ _ _)) _ =>
      apply (C_ossl_load_builtin_compressions Σ21 PMc xra xsp xgp xtp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m43 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary)
  end.
  all: try (lazymatch goal with |- forall _ : config, _ => fail | _ => solve
             [ assumption | reflexivity | apply CallOkBelow; assumption
             | rewrite FrameLit; unfold RT_STACK; clear - Room0; lia
             | rewrite Gr21, unsigned_lit by (unfold SITE_context_init_22; clear - Room0; lia); exact Chain22
             | rewrite Gr21, unsigned_lit by (unfold SITE_context_init_22; clear - Room0; lia); apply (proj2 Edges);
               apply in_or_app; left; wp_in_lit
             | rewrite Gr21; apply (cg_has_weaken _ _ _ _ _ Edges); vm_compute; reflexivity
             | rewrite Fr21; clear - FrmCap; lia
             | rewrite Lv21, length_app, Nat2Z.inj_add, NewLen21; clear - LiveCap; unfold LIVE_MAX in *; lia
             | rewrite Cr21; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity);
               clear - Budget NmPos PpiPos; lia
             | rewrite unsigned_lit by (clear - Room0; lia); clear - Room0; lia ] end).
  intros cfg44 (Σ22 & cp22 & At44 & LvPost22 & FrPost22 & BasePost22 & CrPost22 & V22Pos & V22Al & V22Top & GrPost22).
  destruct (ASTA_unpack RT Σ22 _ _ cfg44 At44) as (st44 & (m44 & Ret22 & After22 & Pres22 & Cl44 & Obj22) & At44s).
  clear At44 At43s.
  destruct Ret22 as (r220 & r221 & r222 & x221 & x222 & x223 & x224 & x225 & x226 & x227 & r223 & r224 & r225 & r226 & F22 & fc22 & ->).
  rewrite FrameLit in After22, Pres22. destruct After22 as (Rt44 & Inv44 & Mono44 & Stack44).
  rewrite (ret_pc_even SITE_context_init_22) in At44s by (unfold SITE_context_init_22; clear - Room0; lia).
  destruct Obj22 as (_ & _ & cp22Obj).
  repeat match goal with
         | Cell : rw_cells asegs m43 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             let b := lazymatch X with ?b + _ => b | _ => X end in
             assert (Moved : rw_cells asegs m44 X cs);
             [ apply (rw_cells_agree_nw asegs m43 m44 X cs Cell); intros w Rw; cbv beta in Rw;
               cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Rw; apply Pres22;
               [ first [ match goal with
                         | Mem : In (b, ?n) (rt_live RT Σ21) |- _ =>
                             apply (acl_live _ _ _ b n); [exact Mem | clear - Rw; lia]
                         end
                       | match goal with
                         | Mem : In (X, ?n) New11 |- _ =>
                             apply (acl_live _ _ _ X n); [apply Sub11_21; exact Mem | clear - Rw; lia]
                         end
                       | apply acl_static, client_static_intro; clear - Rw; lia
                       | apply acl_stack; clear - Rw SpRoom16; lia ]
               | first [ match goal with
                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                             clear - Rw Hp; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I
                         end
                       | clear - Rw LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I ] ]
             | clear Cell ]
         end.
  assert (Above44 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m44).
  { intros w Hi. cbv beta in Hi.
    rewrite (Pres22 w ltac:(apply acl_stack; clear - Hi; lia)
                     ltac:(clear - Hi LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; unfold G_ALLOW_CUST; repeat (split; [lia|]); exact I)).
    exact (Above43 w Hi). }
  assert (Kept44 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m44).
  { apply (pres_fp_trans _ _ _ _ m m43 m44 Kept43).
    apply (PresGrow Σ21 (bv_unsigned sp + -48) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m43 m44);
      [rewrite Lv21; intros e Ein; apply in_or_app; right; exact Ein | exact Fr21 | clear - FrameLit; lia | | exact Pres22].
    intros x Out. unfold Wctx in Out. cbn [outside] in Out |- *. clear - Out. tauto. }
  clear Kept43 Above43 Pres22 Mono44 Inv43 Rt43 Cl43 Stack43 Chain22 FpChain22.
  repeat match goal with
         | Mem : In ?e (rt_live RT Σ21) |- _ =>
             let Moved := fresh "Moved" in
             assert (Moved : In e (rt_live RT Σ22)) by (rewrite LvPost22; repeat first [apply in_or_app; right | right]; exact Mem);
             clear Mem
         end.
  assert (cp22Live : In (cp22, 56) (rt_live RT Σ22)) by (rewrite LvPost22; wp_in_lit).
  assert (cp22Heap : 17594333495296 <= cp22 /\ cp22 + 56 <= lo).
  { split; [exact (afp_live_hi RT GOBJ AFP Σ22 m44 cp22 56 Rt44 cp22Live ltac:(clear - Rt44; try unfold NB_BYTES; lia)) |].
    pose proof (af_live_range RT AF Σ22 m44 cp22 56 Rt44 cp22Live) as Span.
    rewrite BasePost22, Base21 in Span. clear - Span LoInWin; lia. }
  assert (Bnd22 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) [(cp22, 56)]).
  { repeat (apply Forall_cons; [cbn [fst snd]; refine (conj _ (conj _ _)) |]); try apply Forall_nil.
    all: first [ assumption
               | match goal with
                 | Hp : 17594333495296 <= ?x /\ _ |- 0 < ?x => clear - Hp; lia
                 | Hp : 17594333495296 <= ?x /\ _ |- ?x + _ < USTACK_TOP => clear - Hp LoHeap Room0 SpRoom16; lia
                 | Ha : ?x mod 64 = 0 |- ?x mod 16 = 0 => clear - Ha; lia
                 end ]. }
  clear V22Al.
  assert (Sub11_22 : incl New11 (rt_live RT Σ22)) by (intros e Ein; rewrite LvPost22; repeat first [apply in_or_app; right | right]; exact (Sub11_21 e Ein)).
  rewrite Lv21 in LvPost22. rewrite ?app_assoc, ?app_comm_cons in LvPost22.
  match type of LvPost22 with _ = ?L ++ rt_live RT Σ => remember L as New22 eqn:New22Is in LvPost22 end.
  rename LvPost22 into Lv22.
  assert (NewLen22 : Z.of_nat (length New22) = 124)
    by (rewrite New22Is; rewrite ?length_app; cbn [length]; clear - NewLen21; lia).
  assert (NewPos22 : Forall (fun blk => 0 < snd blk) New22).
  { rewrite New22Is.
    repeat first [ apply Forall_cons; [cbn [snd]; try unfold NB_BYTES; clear - NewPos21; lia | ] | apply Forall_nil | exact NewPos21 ]. }
  assert (NewBnd22 : Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) New22).
  { rewrite New22Is. change (Forall (fun blk : Z * Z => 0 < fst blk /\ fst blk mod 16 = 0 /\ fst blk + snd blk < USTACK_TOP) ([(cp22, 56)] ++ New21)). apply Forall_app. split; [exact Bnd22 | exact NewBnd21]. }
  assert (Fr22 : rt_frames RT Σ22 = rt_frames RT Σ) by (rewrite FrPost22; exact Fr21).
  assert (Base22 : rt_sp0 RT Σ22 = rt_sp0 RT Σ) by (rewrite BasePost22; exact Base21).
  assert (Gr22 : rt_cg RT Σ22 = rt_cg RT Σ) by (rewrite GrPost22; exact Gr21).
  assert (Cr22 : rt_credit RT Σ22 = rt_credit RT Σ - (46 + NM_COST + PPI_COST))
    by (rewrite CrPost22, Cr21; try unfold RCX_COST; rewrite ?Mcost0 by (apply Z.leb_le; reflexivity); clear - Mcost0; lia).
  clear FrPost22 BasePost22 GrPost22 CrPost22 Lv21 NewLen21 NewPos21 NewBnd21 Bnd22 Fr21 Base21 Gr21 Cr21 Sub11_21.
  assert (V22Word : 0 <= cp22 < 2 ^ 64) by (unfold USTACK_TOP in V22Top; clear - V22Pos V22Top; lia).
  destruct (ConstsOf Σ22 m44 Rt44) as (ShBase44 & Clean44).
  pose proof (context_init_s22_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_context_init_22)
                r220 r221 r222 x221 x222 x223 x224 x225 x226 x227 r223 r224 r225 r226 lk1 ms3 cf4 rx5 ms6 dc7 ms8 ms9 pv10 ps11 nm12 pd13 gp14 bc15 dn16 st17 ic18 th19 ch20 cp22 j1
                g21 F22 fc22 m44 lo) as Seg22.
  repeat match type of Seg22 with
         | ?Need -> _ =>
             let ok := fresh "ok" in
             assert (ok : Need)
               by first [ assumption | exact (CtxAccOf Σ22 m44 Rt44) | (apply (ShadowOf Σ22 m44); [exact Rt44 | clear - Rt44; lia])
                        | reflexivity | clear - Room0; lia ];
             specialize (Seg22 ok); clear ok
         end.
  cl_lift Seg22 At44s cfg45 At45.
  destruct (ASTA_unpack RT Σ22 _ _ cfg45 At45) as (st45 & Post22 & At45s). clear At45 At44s.
  repeat match goal with
         | Old : rw_cells asegs m44 ?A _ |- _ =>
             lazymatch A with
             | bv_unsigned sp + -48 => clear Old
             | 12187008 => clear Old
             | 12187176 => clear Old
             | 12187184 => clear Old
             | 12187192 => clear Old
             | 12187200 => clear Old
             | 12187208 => clear Old
             | 12187216 => clear Old
             | 12187224 => clear Old
             | 12187232 => clear Old
             | 12187240 => clear Old
             | 12187248 => clear Old
             | 12187256 => clear Old
             | 12187264 => clear Old
             | 12187272 => clear Old
             | 12187280 => clear Old
             | 12187288 => clear Old
             | 12187296 => clear Old
             | 12187304 => clear Old
             | 12187312 => clear Old
             | 12187320 => clear Old
             end
         end.
  destruct Post22 as (m45 & -> & Munch45 & Mono45 & Inv45
                     & FComp & FChild & FThr & FIndic & FSelfT & FNonce & FBio
                     & FGprops & FDefns & FNmap & FPsd & FProvSt & FLdrSt & FEncSt
                     & FDecCa & FDecSt & FDrbg & FConf & FEvp & FLock
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Stack45).
  repeat match goal with
         | Cell : rw_cells asegs m44 ?X ?cs |- _ =>
             let Moved := fresh "Moved" in
             pose proof (wg_keep_seg_nw _ m44 m45 X cs Cell Munch45
                           ltac:(intros y Iny; cbn [cells_size csize Nat.add mutex_cells cond_cells rcu_head ht_tab4 nm_sk_cells snm_cells rcx_cells pdefns_cells] in Iny;
                                 first [ let b := lazymatch X with ?b + _ => b | _ => X end in
                                         match goal with
                                         | Hp : 17594333495296 <= b /\ _ |- _ =>
                                             clear - Iny Hp LoHeap Room0; cbn [outside]; repeat (split; [lia|]); exact I
                                         end
                                       | clear - Iny LoHeap Room0 PsHi PsLow PkHi PkLow PlaHi PlaLow PbaHi PbaLow PlbHi PlbLow PbbHi PbbLow PqaHi PqaLow PqbHi PqbLow; cbn [outside]; repeat (split; [lia|]); exact I ]))
               as Moved;
             clear Cell
         end.
  assert (Rt45 : ART RT Σ22 m45).
  { apply (cl_seg_ART RT AF Σ22 m44 m45 (bv_unsigned sp) 48 [(12187320, 12187328)] Rt44);
      [rewrite Base22; clear - LoInWin Room0; lia | clear - SpRoom16; lia | exact Munch45 | | exact Mono45].
    intros x Inside. cbn [outside] in Inside. apply client_static_intro. clear - Inside. lia. }
  assert (Cl45 : cl_env m45 (Z_to_bv 8 1) canary)
    by (apply (cl_env_seg _ m44 m45 _ canary Cl44 Munch45); first [solve [clear - LoHeap Room0 SpRoom16; cl_fp_lia] | cl_fp_lia]).
  assert (Kept45 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) Wctx m m45).
  { apply (pres_fp_trans _ _ _ _ m m44 m45 Kept44).
    apply (PresGrow Σ22 (bv_unsigned sp) [(12187320, 12187328)] m44 m45);
      [rewrite Lv22; intros e Ein; apply in_or_app; right; exact Ein | exact Fr22 | clear - FrameLit; lia | intros x Out; unfold Wctx in Out; cbn [outside] in Out |- *; unfold G_ALLOW_CUST in Out; clear - Out; split; [lia | exact I] | ].
    exact (cl_seg_pres RT AF Σ22 m44 m45 (bv_unsigned sp) 48 [(12187320, 12187328)] Rt44
             ltac:(rewrite Base22; clear - LoInWin Room0; lia) ltac:(clear - FrameLit; lia) Munch45). }
  clear Kept44 Munch45 Mono45 Inv44 Rt44 Cl44 Stack44 ShBase44 Clean44.
  clear V22Pos V22Top.
  (* the return: the caller's registers, 1 in a0, the frame released *)
  apply Cont.
  exists Σ22, lk1, q1, ms3, sh3, sa3a, la3a, lb3a, sa3b, la3b, lb3b, sa3c, la3c, lb3c, sa3d, la3d,
         lb3d, big3, cf4, ck4, rx5, rq5, rl5, ms6, sh6, sa6a, la6a, lb6a, sa6b, la6b, lb6b, sa6c,
         la6c, lb6c, sa6d, la6d, lb6d, big6, dc7, dl7, dq7, dr7, ms8, sh8, sa8a, la8a, lb8a, sa8b,
         la8b, lb8b, sa8c, la8c, lb8c, sa8d, la8d, lb8d, big8, ms9, sh9, sa9a, la9a, lb9a, sa9b, la9b,
         lb9b, sa9c, la9c, lb9c, sa9d, la9d, lb9d, big9, pv10, pp10, pd10, pc10, pk10, ps11, pk11, pla11,
         pba11, plb11, pbb11, pqa11, pqb11, nm12, nk12, nh12, nhl12, nmd12, nnb12, nrl12, nrq12, nsk12, pd13, pb13,
         gp14, bc15, dn16, dk16, st17, ic18, th19, tm19, tc19, ch20, pi8, pi9, pi10, pi11, pi12, pi13,
         pi14, pi15, pi16, pi17, pi18, pi19, pi20, pi21, pi22, pi23, pi24, pi25, cp22.
  split.
  { apply (ASTA_conseq RT Σ22 PMc _ _ cfg45 At45s).
    intros ms <-. exists m45, jc4, jc16, jc19.
    split; [do 16 eexists; reflexivity |].
    split; [unfold rt_after_f; split; [exact Rt45 | split; [exact Inv45 | exact Stack45]] |].
    split; [exact Kept45 |]. split; [exact Cl45 |].
    repeat match goal with |- _ /\ _ => split end;
      first [ assumption | (repeat (apply Forall_cons; [assumption |]); apply Forall_nil) ]. }
  split.
  { exists New22.
    split; [rewrite New22Is, New21Is, New20Is, New19Is, New18Is, New17Is, New16Is, New15Is, New14Is, New13Is, New12Is, New11Is, New10Is, New9Is, New8Is, New7Is, New6Is, New5Is, New4Is, New3Is, New2Is; reflexivity |].
    split; [exact Lv22 |].
    split; [clear - NewLen22; lia |].
    split; [rewrite New22Is, New21Is, New20Is, New19Is, New18Is, New17Is, New16Is, New15Is, New14Is, New13Is, New12Is, New11Is, New10Is, New9Is, New8Is, New7Is, New6Is, New5Is, New4Is, New3Is, New2Is; cbn [app]; wp_in_lit |].
    apply Forall_forall. intros blk Bin.
    destruct (proj1 (Forall_forall _ _) NewBnd22 blk Bin) as (BlkPos & BlkAl & BlkTop).
    pose proof (proj1 (Forall_forall _ _) NewPos22 blk Bin) as BlkSize.
    exact (conj BlkPos (conj BlkAl (conj BlkTop BlkSize))). }
  split; [exact Fr22 |]. split; [exact Base22 |]. split; [exact Cr22 | exact Gr22].
Qed.
End context_init_cps.
