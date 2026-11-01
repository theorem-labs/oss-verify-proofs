(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_M_zalloc Th_mutex Fz_M_locknew Fz_env Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Th_mutex_init Fz_M_strdup Fz_W5_icb Fz_I2_rcx Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_OPENSSL_sk_new_null Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Th_cond Fz_M_aligned Fz_M_aligned_array Fz_G_ossl_lib_ctx_get_concrete Fz_T_rcuw Fz_T_rcu Fz_I2_anl Fz_I2_htw Fz_I2_htnew Fz_I2_nmw Fz_I2_namemap Fz_I2_snm Fz_I2_pdefns Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_I2_ppisn Fz_G_kit3 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions Fz_G_context_init_w Fz_G_context_init.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
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

Definition e_default_context_do_init_ossl : Z := 0x1f767c.
Definition SITE_default_context_do_init_ossl_1 : Z := 0x1f7698.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition default_context_do_init_ossl_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (g1 : byte) (g2 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun st => exists m1 : mem,
    st = MS (mkR (Z_to_bv 64 SITE_default_context_do_init_ossl_1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 12187008)
               a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_context_init) fc None m1 (seg_rom asegs)
    /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells asegs m1 12186976 [C1 g1]
    /\ rw_cells asegs m1 12187552 [C4 g2]
    /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1
    /\ wmono asegs m m1.

Lemma default_context_do_init_ossl_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (g1 : byte) (g2 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 0xb9f560 [C1 g1] ->
  rw_cells asegs m 0xb9f7a0 [C4 g2] ->
  mem_inv asegs m ->
  evt asegs (default_context_do_init_ossl_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g1 g2 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f767c) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g1 g2 F fc m lo
    Stack FrameFits LoAboveShadow SpCap CellInit CellRet MemOk.
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as Footprint.
  pose proof (wmono_refl asegs m) as Writable.
  destruct (stk_carve asegs m lo (bv_unsigned sp) 16 Stack ltac:(lia)) as [StackBelow [junk Slot]].
  replace (bv_unsigned sp - Z.of_nat 16) with (bv_unsigned sp + -16) in StackBelow, Slot by lia.
  clear Stack.
  do 7 zstep.
  apply evt_done.
  eexists; split; [reflexivity|].
  exact (conj MemOk (conj StackBelow (conj Slot (conj CellInit (conj CellRet (conj Footprint Writable)))))).
Qed.

(* [comment removed for export] *)
Definition default_context_do_init_ossl_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word)
    (g1 : byte) (g2 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun st => exists m2 : mem,
    st = MS (mkR ra sp gp tp u0_1 u1_1 u2_1 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 12187304) b2_1 b3_1 b4_1 b5_1 b6_1 b7_1
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (ret_pc ra) fc1 None m2 (seg_rom asegs)
    /\ mem_inv asegs m2
    /\ stk asegs m2 lo (bv_unsigned sp)
    /\ rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells asegs m2 12186976 [C1 (Z_to_bv 8 1)]
    /\ rw_cells asegs m2 12187552 [C4 (Z_to_bv 64 1)]
    /\ munch [(12186976, 12186977); (12187552, 12187556)] m m2
    /\ wmono asegs m m2.

Lemma default_context_do_init_ossl_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (g1 : byte) (g2 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -16) -> lo <= (bv_unsigned sp + -16) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells asegs m 12187552 [C4 g2] ->
  rw_cells asegs m 12186976 [C1 g1] ->
  mem_inv asegs m ->
  evt asegs (default_context_do_init_ossl_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g1 g2 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x1f7698) fc1 None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 g1 g2 F1 fc1 m lo
    StackBelow FrameFits LoAboveShadow SpCap Slot CellRet CellInit MemOk.
  pose proof (stk_release asegs m lo _ _ StackBelow Slot FrameFits) as StackAll.
  change (Z.of_nat (cells_size [C8 s0; C8 ra])) with 16 in StackAll.
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in StackAll by lia.
  clear StackBelow.
  pose proof (munch_refl [(12186976, 12186977); (12187552, 12187556)] m) as Footprint.
  pose proof (wmono_refl asegs m) as Writable.
  zstep. wg_F.
  do 2 zstep. zstore.
  zstep. zstore.
  do 4 zstep.
  apply evt_done.
  exists m1.
  exact (conj eq_refl (conj MemOk (conj StackAll (conj Slot (conj CellInit (conj CellRet (conj Footprint Writable))))))).
Qed.

Section default_context_do_init_ossl_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_context_init : context_init_stmt RT.

Definition default_context_do_init_ossl_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word)
         (g1 : byte)
         (g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17
          g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od : word),
    fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 12205808 ->
    ART RT Σ m -> mem_inv asegs m -> cl_env m lb canary ->
    call_ok RT Σ m sp lo -> lo + RT_STACK + 1088 <= bv_unsigned sp ->
    cg_ctx (rt_cg RT Σ) e_default_context_do_init_ossl (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
    cg_has (rt_cg RT Σ)
      ((SITE_default_context_do_init_ossl_1, e_default_context_do_init_ossl) ::
       [(SITE_context_init_1, e_context_init); (SITE_context_init_2, e_context_init); (SITE_context_init_3, e_context_init);
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
      ((SITE_default_context_do_init_ossl_1, e_context_init) ::
       [(SITE_context_init_1, e_lock_new); (SITE_context_init_2, e_ossl_do_ex_data_init); (SITE_context_init_3, e_ossl_method_store_new);
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
    rw_cells asegs m 12186976 [C1 g1] -> rw_cells asegs m 12187552 [C4 g2] ->
    rw_cells asegs m 12187008 [C8 g1_g2] -> rw_cells asegs m 12187176 [C8 g1_g3] -> rw_cells asegs m 12187184 [C8 g1_g4] ->
    rw_cells asegs m 12187192 [C8 g1_g5] -> rw_cells asegs m 12187200 [C8 g1_g6] -> rw_cells asegs m 12187208 [C8 g1_g7] ->
    rw_cells asegs m 12187216 [C8 g1_g8] -> rw_cells asegs m 12187224 [C8 g1_g9] -> rw_cells asegs m 12187232 [C8 g1_g10] ->
    rw_cells asegs m 12187240 [C8 g1_g11] -> rw_cells asegs m 12187248 [C8 g1_g12] -> rw_cells asegs m 12187256 [C8 g1_g13] ->
    rw_cells asegs m 12187264 [C8 g1_g14] -> rw_cells asegs m 12187272 [C8 g1_g15] -> rw_cells asegs m 12187280 [C8 g1_g16] ->
    rw_cells asegs m 12187288 [C8 g1_g17] -> rw_cells asegs m 12187296 [C8 g1_g18] -> rw_cells asegs m 12187304 [C8 g1_g19] ->
    rw_cells asegs m 12187312 [C8 g1_g20] -> rw_cells asegs m 12187320 [C8 g1_g21] ->
    rw_cells asegs m 12187016 [C8 g1_g2_g2] ->
    rw_cells asegs m 12186112 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m 12186272 [C8 g1_g5_od] ->
    rw_cells asegs m 12186304 [C4 (Z_to_bv 64 2)] -> rw_cells asegs m 12186336 [C4 (Z_to_bv 64 1)] ->
    cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                           F fc e_default_context_do_init_ossl m)))
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
                   [(12186976, 12186977); (12187008, 12187024); (12187176, 12187328); (12187552, 12187556);
                    (G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
              /\ cl_env m' (Z_to_bv 8 1) canary
              /\ rw_cells asegs m' 12186976 [C1 (Z_to_bv 8 1)]
              /\ rw_cells asegs m' 12187552 [C4 (Z_to_bv 64 1)]
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

Theorem default_context_do_init_ossl_cps : default_context_do_init_ossl_stmt.
Proof using AF AFP C_context_init.
  unfold default_context_do_init_ossl_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo outer lb canary g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14
    g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
    FdsOnly PMStable TpLit Art0 MemOk0 Env0 CallOk0 StackRoom CgCtx0 Unwind0 Graph FrameRoom LiveRoom LiveNonEmpty Credit
    CInit CRet Gl02 Gl03 Gl04 Gl05 Gl06 Gl07 Gl08 Gl09 Gl10 Gl11 Gl12 Gl13 Gl14 Gl15 Gl16 Gl17 Gl18 Gl19 Gl20 Gl21
    GlCtx GlZero GlOd GlTwo GlOne
    Tr cfg0 AtEntry Finish.
  pose proof (af_sp0_win RT AF Σ m Art0) as WinFloor.
  destruct CallOk0 as (Stack0 & LoInWin & LoGap & SpTop & SpAligned).
  assert (LoAboveShadow : 0x10007fff8000 <= lo) by (unfold STACK_WIN in LoInWin; lia).
  assert (SpCap : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in SpTop; lia).
  unfold RT_STACK in StackRoom.
  pose proof (default_context_do_init_ossl_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                s10 s11 t3 t4 t5 t6 g1 g2 F fc m lo Stack0 ltac:(lia) LoAboveShadow SpCap CInit CRet MemOk0) as Prologue.
  cl_lift Prologue AtEntry cfg1 AtCall.
  destruct (ASTA_unpack RT Σ _ _ cfg1 AtCall) as (stCall & AtCallPost & AtCallSt). clear AtCall.
  destruct AtCallPost as (m1 & -> & MemOk1 & Stack1 & Frame1 & CInit1 & CRet1 & Scratch1 & Grow1).
  assert (FrameLit : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  assert (SiteLit : bv_unsigned (Z_to_bv 64 SITE_default_context_do_init_ossl_1) = SITE_default_context_do_init_ossl_1)
    by (apply unsigned_lit; unfold SITE_default_context_do_init_ossl_1; lia).
  assert (Art1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 16 [] Art0); [lia | lia | exact Scratch1 | | exact Grow1].
    intros x NotOut. exfalso. exact (NotOut I). }
  assert (Env1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary Env0 Scratch1); cl_fp_lia).
  clear CInit CRet.
  repeat match goal with
         | Old : rw_cells asegs m ?X ?cs |- _ =>
             let New := fresh "Now" in
             assert (New : rw_cells asegs m1 X cs)
               by (apply (wg_keep_seg_nw _ m m1 X cs Old Scratch1); intros x Span; cbn [cells_size csize Nat.add] in Span;
                   cbn [outside]; split; [lia | exact I]);
             clear Old; rename New into Old
         end.
  assert (Above1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1)
    by (apply (agree_of_munch _ m m1 _ Scratch1); intros x Span; cbn [outside]; split; [lia | exact I]).
  destruct (cl_chain_call (rt_cg RT Σ) e_default_context_do_init_ossl e_context_init SITE_default_context_do_init_ossl_1
              m m1 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -16)) outer CgCtx0
              (proj1 Graph _ (or_introl eq_refl)) (proj2 Graph _ (or_introl eq_refl)) Unwind0 Above1 Frame1
              ltac:(rewrite FrameLit; lia) SpTop) as (CgCtx1 & Unwind1).
  rewrite <- SiteLit in CgCtx1.
  assert (CallOk1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -16)) lo).
  { unfold call_ok. rewrite FrameLit. unfold USTACK_TOP, RT_STACK in *.
    refine (conj Stack1 (conj LoInWin (conj _ (conj _ _)))); lia. }
  assert (Deep1 : lo + RT_STACK + 1072 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)))
    by (rewrite FrameLit; unfold RT_STACK; lia).
  refine (C_context_init Σ PMc (Z_to_bv 64 SITE_default_context_do_init_ossl_1) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp
            s1 (Z_to_bv 64 12187008) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo
            (bv_unsigned ra :: outer) lb canary g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13
            g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
            FdsOnly PMStable eq_refl TpLit Art1 MemOk1 Env1 CallOk1 Deep1 CgCtx1 Unwind1
            (cg_has_sub _ _ _ _ _ Graph (incl_tl _ (incl_refl _)) (incl_tl _ (incl_refl _)))
            FrameRoom LiveRoom LiveNonEmpty Credit
            Gl02 Gl03 Gl04 Gl05 Gl06 Gl07 Gl08 Gl09 Gl10 Gl11 Gl12 Gl13 Gl14 Gl15 Gl16 Gl17 Gl18 Gl19 Gl20 Gl21
            GlCtx GlZero GlOd GlTwo GlOne Tr cfg1 AtCallSt _).
  intros cfg2 (Σ1 & lk1 & xd2
                & ms3 & sh3 & sa3a & la3a & lb3a & sa3b & la3b & lb3b & sa3c & la3c & lb3c & sa3d & la3d & lb3d & big3
                & cf4 & ck4 & rx5 & rq5 & rl5
                & ms6 & sh6 & sa6a & la6a & lb6a & sa6b & la6b & lb6b & sa6c & la6c & lb6c & sa6d & la6d & lb6d & big6
                & dc7 & dl7 & dq7 & dr7
                & ms8 & sh8 & sa8a & la8a & lb8a & sa8b & la8b & lb8b & sa8c & la8c & lb8c & sa8d & la8d & lb8d & big8
                & ms9 & sh9 & sa9a & la9a & lb9a & sa9b & la9b & lb9b & sa9c & la9c & lb9c & sa9d & la9d & lb9d & big9
                & pv10 & pp10 & pd10 & pc10 & pk10 & ps11 & pk11 & pla11 & pba11 & plb11 & pbb11 & pqa11 & pqb11
                & nm12 & nk12 & nh12 & nhl12 & nmd12 & nnb12 & nrl12 & nrq12 & nsk12 & pd13 & pb13 & gp14 & bc15
                & dn16 & dk16 & st17 & ic18 & th19 & tm19 & tc19 & ch20
                & pi8 & pi9 & pi10 & pi11 & pi12 & pi13 & pi14 & pi15 & pi16 & pi17 & pi18 & pi19 & pi20 & pi21 & pi22
                & pi23 & pi24 & pi25 & cp22
                & AtRet & NewBlocks & SameFrames & SameSp0 & CreditUsed & SameCg).
  destruct (ASTA_unpack RT Σ1 _ _ cfg2 AtRet) as (stRet & RetPost & AtRetSt). clear AtRet.
  destruct RetPost as (m2 & j4 & j16 & j19 & RetShape & After2 & Pres2 & Env2 & Objects).
  destruct RetShape as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
  rewrite FrameLit in After2, Pres2.
  destruct After2 as (Art2 & MemOk2 & Stack2).
  rewrite (ret_pc_even SITE_default_context_do_init_ossl_1) in AtRetSt by (unfold SITE_default_context_do_init_ossl_1; lia).
  assert (MineStatic : forall x, 12186976 <= x < 12186977 \/ 12187552 <= x < 12187556 -> client_static x).
  { intros x Span. split.
    - exists 0xb9f190, 0xbc57d0. unfold CLIENT_STATIC. split; [cbn [In]; right; right; left; reflexivity | lia].
    - intros (lo' & hi' & Listed & Within). unfold RT_STATIC in Listed. cbn [In] in Listed.
      repeat (destruct Listed as [Hit | Listed]; [injection Hit as <- <-; lia |]). exact Listed. }
  assert (Frame2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ Frame1). intros w Span. cbn [cells_size csize Nat.add] in Span.
    apply Pres2; [left; unfold USTACK_TOP in *; lia |].
    cbn [outside]. unfold G_ALLOW_CUST. refine (conj _ (conj _ (conj _ I))); lia. }
  assert (CInit2 : rw_cells asegs m2 12186976 [C1 g1]).
  { apply (wg_keep_static_nw _ _ _ _ m1 m2 _ _ CInit1 Pres2). intros x Span. cbn [cells_size csize Nat.add] in Span.
    split; [apply MineStatic; lia |]. cbn [outside]. unfold G_ALLOW_CUST. refine (conj _ (conj _ (conj _ I))); lia. }
  assert (CRet2 : rw_cells asegs m2 12187552 [C4 g2]).
  { apply (wg_keep_static_nw _ _ _ _ m1 m2 _ _ CRet1 Pres2). intros x Span. cbn [cells_size csize Nat.add] in Span.
    split; [apply MineStatic; lia |]. cbn [outside]. unfold G_ALLOW_CUST. refine (conj _ (conj _ (conj _ I))); lia. }
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 16 [] Art0 ltac:(lia) ltac:(lia) Scratch1) as PresFrame.
  pose proof (default_context_do_init_ossl_s1_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_default_context_do_init_ossl_1) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 g1 g2 F1 fc1 m2 lo
                Stack2 ltac:(lia) LoAboveShadow SpCap Frame2 CRet2 CInit2 MemOk2) as Epilogue.
  cl_lift Epilogue AtRetSt cfg3 AtDone.
  clear Frame2 CInit2 CRet2.
  pose proof NewBlocks as (NEW & NewList & LiveNow & _). subst NEW.
  assert (BlockSide : forall q n, In (q, n) (rt_live RT Σ1) -> SEGTOP_A <= q \/ q + n <= 65536).
  { intros q n Listed. destruct (af_live_range RT AF Σ1 m2 q n Art2 Listed) as (_ & _ & [Low | High]);
      [right; exact Low | left; exact High]. }
  apply Finish.
  exists Σ1, lk1, xd2,
    ms3, sh3, sa3a, la3a, lb3a, sa3b, la3b, lb3b, sa3c, la3c, lb3c, sa3d, la3d, lb3d, big3,
    cf4, ck4, rx5, rq5, rl5,
    ms6, sh6, sa6a, la6a, lb6a, sa6b, la6b, lb6b, sa6c, la6c, lb6c, sa6d, la6d, lb6d, big6,
    dc7, dl7, dq7, dr7,
    ms8, sh8, sa8a, la8a, lb8a, sa8b, la8b, lb8b, sa8c, la8c, lb8c, sa8d, la8d, lb8d, big8,
    ms9, sh9, sa9a, la9a, lb9a, sa9b, la9b, lb9b, sa9c, la9c, lb9c, sa9d, la9d, lb9d, big9,
    pv10, pp10, pd10, pc10, pk10, ps11, pk11, pla11, pba11, plb11, pbb11, pqa11, pqb11,
    nm12, nk12, nh12, nhl12, nmd12, nnb12, nrl12, nrq12, nsk12, pd13, pb13, gp14, bc15,
    dn16, dk16, st17, ic18, th19, tm19, tc19, ch20,
    pi8, pi9, pi10, pi11, pi12, pi13, pi14, pi15, pi16, pi17, pi18, pi19, pi20, pi21, pi22,
    pi23, pi24, pi25, cp22.
  refine (conj _ (conj NewBlocks (conj SameFrames (conj SameSp0 (conj CreditUsed SameCg))))).
  apply (ASTA_conseq RT Σ1 PMc _ _ cfg3 AtDone). intros ms Done.
  destruct Done as (m3 & FinalState & MemOk3 & Stack3 & _ & CInit3 & CRet3 & Scratch3 & Grow3).
  assert (RetFinal : ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m3 ms)
    by (exists u0, u1, u2, (Z_to_bv 64 12187304), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F1, fc1; exact FinalState).
  assert (After3 : rt_after_f RT Σ1 (bv_unsigned sp) lo m m3).
  { refine (conj _ (conj MemOk3 Stack3)).
    apply (af_frame RT AF Σ1 m2 m3 (bv_unsigned sp) Art2); [rewrite SameSp0; lia | | exact Grow3].
    intros a NotClient. apply Scratch3. cbn [outside].
    refine (conj _ (conj _ I)); intros Hit; apply NotClient; right; left; apply MineStatic; lia. }
  assert (Pres3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
                    [(12186976, 12186977); (12187008, 12187024); (12187176, 12187328); (12187552, 12187556);
                     (G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
  { apply (pres_fp_trans _ _ _ _ m m2 m3).
    - apply (pres_fp_trans _ _ _ _ m m1 m2).
      + apply (pres_fp_sub _ _ _ _ _ _ _ [] m m1 PresFrame). intros x Acl _. exact (conj Acl I).
      + apply (pres_fp_sub _ _ _ _ _ _ _ _ m1 m2 Pres2). intros x Acl Out. split.
        * apply (aclient_mono _ _ _ _ _ _ _ Acl); [intros e Ein; exact Ein | intros e Ein; exact Ein | lia].
        * cbn [outside] in Out |- *. destruct Out as (_ & OutA & OutB & _ & OutC & _). exact (conj OutC (conj OutA (conj OutB I))).
    - apply (pres_fp_of_munch _ _ _ _ _ m2 m3 Scratch3). intros x _ Out.
      cbn [outside] in Out |- *. destruct Out as (OutLo & _ & _ & OutHi & _). exact (conj OutLo (conj OutHi I)). }
  assert (Env3 : cl_env m3 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m2 m3 _ canary Env2 Scratch3); cl_fp_lia).
  (* every object fact of context_init's post lies in a static ctx cell or in a block of rt_live; none meets the two stored cells *)
  repeat match type of Objects with _ /\ _ => let Piece := fresh "Obj" in destruct Objects as [Piece Objects] end.
  repeat match goal with
         | Group : Forall _ (_ :: _) |- _ =>
             let Piece := fresh "Obj" in apply Forall_cons_iff in Group; destruct Group as [Piece Group]; cbv beta in Piece
         end.
  repeat match goal with Group : Forall _ [] |- _ => clear Group end.
  lazymatch type of LiveNow with
  | _ = ?blocks ++ _ =>
      assert (SideAll : Forall (fun blk : Z * Z => SEGTOP_A <= fst blk \/ fst blk + snd blk <= 65536) blocks)
        by (apply Forall_forall; intros [q n] InNew; apply BlockSide; rewrite LiveNow; apply in_or_app; left; exact InNew)
  end.
  repeat match type of SideAll with
         | Forall _ (_ :: _) =>
             let One := fresh "Side" in apply Forall_cons_iff in SideAll; destruct SideAll as [One SideAll]; cbn [fst snd] in One
         end.
  clear SideAll.
  repeat match goal with
         | Cell : rw_cells asegs m2 ?X ?cs |- _ =>
             let width := eval lazy in (Z.of_nat (cells_size cs)) in
             let Clear := fresh "Clear" in
             lazymatch X with
             | Zpos _ =>
                 assert (Clear : forall x, X <= x < X + Z.of_nat (cells_size cs) ->
                                   outside [(12186976, 12186977); (12187552, 12187556)] x)
                   by (intros x Span; change (Z.of_nat (cells_size cs)) with width in Span; clear - Span;
                       cbn [outside]; refine (conj _ (conj _ I)); lia)
             | _ =>
                 let base := lazymatch X with ?q + _ => q | _ => X end in
                 lazymatch goal with
                 | Side : SEGTOP_A <= base \/ _ |- _ =>
                     assert (Clear : forall x, X <= x < X + Z.of_nat (cells_size cs) ->
                                       outside [(12186976, 12186977); (12187552, 12187556)] x)
                       by (intros x Span; change (Z.of_nat (cells_size cs)) with width in Span; clear - Side Span;
                           unfold SEGTOP_A, NB_BYTES in *; cbn [outside]; refine (conj _ (conj _ I)); lia)
                 end
             end;
             let Moved := fresh "Kept" in
             pose proof (wg_keep_seg_nw _ m2 m3 X cs Cell Scratch3 Clear) as Moved;
             clear Cell Clear
         end.
  exists m3, j4, j16, j19.
  refine (conj RetFinal (conj After3 (conj Pres3 (conj Env3 (conj CInit3 (conj CRet3 _)))))).
  repeat match goal with |- _ /\ _ => split end.
  all: first [ assumption | repeat (apply Forall_cons; [assumption |]); apply Forall_nil ].
Qed.
End default_context_do_init_ossl_cps.
