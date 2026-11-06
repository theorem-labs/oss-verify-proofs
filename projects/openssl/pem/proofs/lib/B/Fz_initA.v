(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout PLayout RT_iface RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_env
  Fz_M_malloc Fz_M_zalloc Fz_M_locknew Fz_env Fz_G_OPENSSL_cpuid_setup Fz_I3_ibase Fz_W5_icb Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Fz_T_sa_set Fz_T_slx Fz_I3_shelve Fz_G_OPENSSL_LH_new Fz_I1_first Fz_M_realloc Fz_M_realloc_array Fz_I1_insert Fz_I1_load Fz_I1_efirst Fz_I1_getitem Fz_I1_reason Fz_I1_errload Fz_I1_const Fz_I1_crypto Fz_I3_loadstr Fz_I3_full Fz_M_free Fz_W5_eclr Fz_G_OSSL_ERR_STATE_new Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_create_global_tevent_register_ossl Fz_T_its Fz_I3_icfast Fz_I3_egsi Fz_I3_eclear Fz_G_ossl_lib_ctx_get_ex_data_global Fz_G_ossl_do_ex_data_init Fz_G_ossl_method_store_new Fz_G_ossl_prov_conf_ctx_new Fz_M_strdup Fz_I2_rcx Fz_I2_lhst Fz_G_ossl_decoder_cache_new Fz_G_OPENSSL_sk_new Fz_G_ossl_provider_store_new Fz_G_ossl_property_string_data_new Fz_M_aligned Fz_M_aligned_array Fz_I2_anl Fz_T_rcu Fz_I2_htnew Fz_I2_namemap Fz_I2_snm Fz_I2_pdefnsd Fz_G_ossl_ctx_global_properties_new Fz_G_ossl_bio_core_globals_new Fz_G_ossl_prov_drbg_nonce_ctx_new Fz_G_ossl_self_test_set_callback_new Fz_G_ossl_indicator_set_callback_new Fz_G_ossl_crypto_mutex_new Fz_G_ossl_crypto_condvar_new Fz_G_ossl_threads_ctx_new Fz_G_ossl_child_prov_ctx_new Fz_K_pstrf Fz_K_pstr Fz_K_pstrg Fz_I2_ppi2 Fz_G_COMP_zlib Fz_G_COMP_get_type Fz_G_ossl_load_builtin_compressions Fz_G_context_init Fz_G_default_context_do_init_ossl Fz_I3_gdc Fz_I3_fxi Fz_K_pstrs Fz_I2_ppisn Fz_I2_ppi2a Fz_I2_ppisn
  Fz_lib0 Fz_libA Fz_I3_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation TP_A := (0xbd66f0)%Z (only parsing).
Notation TSD_MAIN := (0xbf7a98)%Z (only parsing).
Notation MK_KEY := (0xbd1d20)%Z (only parsing).
Notation DTOR_KEY := (0x5e21a0)%Z (only parsing).

(* [comment removed for export] *)
Definition INITA_GOBJS : list (Z * Z) :=
  [(G_IC_OPTSDONE, 8); (MK_KEY, 4); (DTOR_KEY, 8); (12393856, 328); (STR_FIPS, 5); (PPI_TAB, 48); (A_PROVIDER, 9); (A_VERSION, 8); (A_FIPS, 5); (A_OUTPUT, 7); (A_INPUT, 6); (A_STRUCTURE, 10); (A_YES, 4); (A_NO, 3); (PPI_CTX, 328); (0xbd1f20, 4); (0xbd1d80, 328)].
Definition INITA_GCOVER : list (Z * Z) :=
  [(0x567360, 16 * (43 + 1));
   (0x5676c0, 16 * (39 + 1));
   (0x5d3780, 16 * (22 + 1));
   (0x5d3940, 16 * (81 + 1));
   (0x5d3fa0, 16 * (31 + 1));
   (0x5d4220, 16 * (125 + 1));
   (0xf1c20, 16 * (0 + 1));
   (0x5d4be0, 16 * (3 + 1));
   (0x5d4c40, 16 * (34 + 1));
   (0x5d4f00, 16 * (16 + 1));
   (0x5d5060, 16 * (47 + 1));
   (0x5d5420, 16 * (117 + 1));
   (0x5d5d40, 16 * (27 + 1));
   (0x5d5f60, 16 * (31 + 1));
   (0x5d61e0, 16 * (10 + 1));
   (0x5d62c0, 16 * (76 + 1));
   (0x5d68c0, 16 * (47 + 1));
   (0x5d6c80, 16 * (38 + 1));
   (0x5d6f80, 16 * (73 + 1));
   (0x5d7540, 16 * (22 + 1));
   (0x5d7700, 16 * (45 + 1));
   (0x5d7a80, 16 * (16 + 1));
   (0x5d7be0, 16 * (39 + 1));
   (0x5d7f00, 16 * (32 + 1));
   (0x5d81a0, 16 * (25 + 1));
   (0x5d83a0, 16 * (13 + 1));
   (0x5d84a0, 16 * (102 + 1));
   (0x5d8ca0, 16 * (30 + 1));
   (0x5d8f00, 16 * (106 + 1));
   (0x5d9760, 16 * (17 + 1));
   (0x5d98c0, 16 * (9 + 1));
   (0x5d9980, 16 * (4 + 1));
   (0x5d9a00, 16 * (14 + 1));
   (0x5d9b20, 16 * (25 + 1));
   (0x5d9d20, 16 * (11 + 1));
   (0x5d9e00, 16 * (160 + 1))].

Section InitA.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis CR : cli_rt RT GOBJ.
Hypothesis TSD : forall Σ m, ART RT Σ m -> rw_cells bsegs m 0xbd6698 [C8 (Z_to_bv 64 0xbf7a98)].   (* [comment removed for export] *)
Hypothesis ERRNO_ACC : forall Σ m, ART RT Σ m -> acc bsegs m 0xbd6648 8.                          (* [comment removed for export] *)
Hypothesis HGO : Forall (fun p => GOBJ (fst p) (snd p)) INITA_GOBJS.
Hypothesis HGC : Forall (fun p => exists b sz, GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) INITA_GCOVER.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis HCG : cg_sub FI_SITES FI_CALLS FZ_SITES FZ_CALLS.

Theorem fuzz_init_closed : fuzz_init_cps RT LIB0_A LIB_A FZ_SITES FZ_CALLS.
Proof using CR TSD ERRNO_ACC HGO HGC HCG.
  pose proof (cr_af CR) as AF. pose proof (cr_afp CR) as AFP. pose proof (cr_rc CR) as RC. pose proof (cr_rcp CR) as RCP.
  pose proof (rc_malloc RT RC) as R1. pose proof (rc_free RT RC) as R2. pose proof (rc_free_null RT RC) as R3. pose proof (rc_memcpy RT RC) as R4. pose proof (rc_asan_memcpy RT RC) as R5.
  pose proof (rc_memset RT RC) as R6. pose proof (rc_asan_memset RT RC) as R7. pose proof (rc_memchr RT RC) as R8. pose proof (rc_strlen RT RC) as R9. pose proof (rc_strnlen RT RC) as R10.
  pose proof (rc_strncmp RT RC) as R11. pose proof (rc_stack_malloc_0 RT RC) as R12. pose proof (rc_stack_malloc_1 RT RC) as R13. pose proof (rc_stack_malloc_2 RT RC) as R14.
  pose proof (rcp_realloc RT RCP) as R15. pose proof (rcp_memalign RT RCP) as R16. pose proof (rcp_memcmp RT RCP) as R17. pose proof (rcp_strcpy RT RCP) as R18. pose proof (rcp_asan_memmove RT RCP) as R19.
  assert (TSD1 : forall Σ m, ART RT Σ m -> rw_cells bsegs m (TP_A + -88) [C8 (Z_to_bv 64 TSD_MAIN)]) by exact TSD.
  assert (GO1 : GOBJ G_IC_OPTSDONE 8) by exact (proj1 (Forall_forall _ _) HGO (G_IC_OPTSDONE, 8) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO2 : GOBJ MK_KEY 4) by exact (proj1 (Forall_forall _ _) HGO (MK_KEY, 4) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO3 : GOBJ DTOR_KEY 8) by exact (proj1 (Forall_forall _ _) HGO (DTOR_KEY, 8) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO4 : GOBJ 12393856 328) by exact (proj1 (Forall_forall _ _) HGO (12393856, 328) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO5 : GOBJ STR_FIPS 5) by exact (proj1 (Forall_forall _ _) HGO (STR_FIPS, 5) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO6 : GOBJ PPI_TAB 48) by exact (proj1 (Forall_forall _ _) HGO (PPI_TAB, 48) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO7 : GOBJ A_PROVIDER 9) by exact (proj1 (Forall_forall _ _) HGO (A_PROVIDER, 9) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO8 : GOBJ A_VERSION 8) by exact (proj1 (Forall_forall _ _) HGO (A_VERSION, 8) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO9 : GOBJ A_FIPS 5) by exact (proj1 (Forall_forall _ _) HGO (A_FIPS, 5) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO10 : GOBJ A_OUTPUT 7) by exact (proj1 (Forall_forall _ _) HGO (A_OUTPUT, 7) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO11 : GOBJ A_INPUT 6) by exact (proj1 (Forall_forall _ _) HGO (A_INPUT, 6) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO12 : GOBJ A_STRUCTURE 10) by exact (proj1 (Forall_forall _ _) HGO (A_STRUCTURE, 10) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO13 : GOBJ A_YES 4) by exact (proj1 (Forall_forall _ _) HGO (A_YES, 4) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO14 : GOBJ A_NO 3) by exact (proj1 (Forall_forall _ _) HGO (A_NO, 3) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO15 : GOBJ PPI_CTX 328) by exact (proj1 (Forall_forall _ _) HGO (PPI_CTX, 328) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO16 : GOBJ 0xbd1f20 4) by exact (proj1 (Forall_forall _ _) HGO (0xbd1f20, 4) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GO17 : GOBJ 0xbd1d80 328) by exact (proj1 (Forall_forall _ _) HGO (0xbd1d80, 328) ltac:(clear; unfold INITA_GOBJS; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC1 : exists b sz, GOBJ b sz /\ b <= 0x567360 /\ 0x567360 + 16 * (43 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x567360, 16 * (43 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC2 : exists b sz, GOBJ b sz /\ b <= 0x5676c0 /\ 0x5676c0 + 16 * (39 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5676c0, 16 * (39 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC3 : exists b sz, GOBJ b sz /\ b <= 0x5d3780 /\ 0x5d3780 + 16 * (22 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d3780, 16 * (22 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC4 : exists b sz, GOBJ b sz /\ b <= 0x5d3940 /\ 0x5d3940 + 16 * (81 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d3940, 16 * (81 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC5 : exists b sz, GOBJ b sz /\ b <= 0x5d3fa0 /\ 0x5d3fa0 + 16 * (31 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d3fa0, 16 * (31 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC6 : exists b sz, GOBJ b sz /\ b <= 0x5d4220 /\ 0x5d4220 + 16 * (125 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d4220, 16 * (125 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC7 : exists b sz, GOBJ b sz /\ b <= 0xf1c20 /\ 0xf1c20 + 16 * (0 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0xf1c20, 16 * (0 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC8 : exists b sz, GOBJ b sz /\ b <= 0x5d4be0 /\ 0x5d4be0 + 16 * (3 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d4be0, 16 * (3 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC9 : exists b sz, GOBJ b sz /\ b <= 0x5d4c40 /\ 0x5d4c40 + 16 * (34 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d4c40, 16 * (34 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC10 : exists b sz, GOBJ b sz /\ b <= 0x5d4f00 /\ 0x5d4f00 + 16 * (16 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d4f00, 16 * (16 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC11 : exists b sz, GOBJ b sz /\ b <= 0x5d5060 /\ 0x5d5060 + 16 * (47 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d5060, 16 * (47 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC12 : exists b sz, GOBJ b sz /\ b <= 0x5d5420 /\ 0x5d5420 + 16 * (117 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d5420, 16 * (117 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC13 : exists b sz, GOBJ b sz /\ b <= 0x5d5d40 /\ 0x5d5d40 + 16 * (27 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d5d40, 16 * (27 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC14 : exists b sz, GOBJ b sz /\ b <= 0x5d5f60 /\ 0x5d5f60 + 16 * (31 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d5f60, 16 * (31 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC15 : exists b sz, GOBJ b sz /\ b <= 0x5d61e0 /\ 0x5d61e0 + 16 * (10 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d61e0, 16 * (10 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC16 : exists b sz, GOBJ b sz /\ b <= 0x5d62c0 /\ 0x5d62c0 + 16 * (76 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d62c0, 16 * (76 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC17 : exists b sz, GOBJ b sz /\ b <= 0x5d68c0 /\ 0x5d68c0 + 16 * (47 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d68c0, 16 * (47 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC18 : exists b sz, GOBJ b sz /\ b <= 0x5d6c80 /\ 0x5d6c80 + 16 * (38 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d6c80, 16 * (38 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC19 : exists b sz, GOBJ b sz /\ b <= 0x5d6f80 /\ 0x5d6f80 + 16 * (73 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d6f80, 16 * (73 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC20 : exists b sz, GOBJ b sz /\ b <= 0x5d7540 /\ 0x5d7540 + 16 * (22 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d7540, 16 * (22 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC21 : exists b sz, GOBJ b sz /\ b <= 0x5d7700 /\ 0x5d7700 + 16 * (45 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d7700, 16 * (45 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC22 : exists b sz, GOBJ b sz /\ b <= 0x5d7a80 /\ 0x5d7a80 + 16 * (16 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d7a80, 16 * (16 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC23 : exists b sz, GOBJ b sz /\ b <= 0x5d7be0 /\ 0x5d7be0 + 16 * (39 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d7be0, 16 * (39 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC24 : exists b sz, GOBJ b sz /\ b <= 0x5d7f00 /\ 0x5d7f00 + 16 * (32 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d7f00, 16 * (32 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC25 : exists b sz, GOBJ b sz /\ b <= 0x5d81a0 /\ 0x5d81a0 + 16 * (25 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d81a0, 16 * (25 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC26 : exists b sz, GOBJ b sz /\ b <= 0x5d83a0 /\ 0x5d83a0 + 16 * (13 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d83a0, 16 * (13 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC27 : exists b sz, GOBJ b sz /\ b <= 0x5d84a0 /\ 0x5d84a0 + 16 * (102 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d84a0, 16 * (102 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC28 : exists b sz, GOBJ b sz /\ b <= 0x5d8ca0 /\ 0x5d8ca0 + 16 * (30 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d8ca0, 16 * (30 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC29 : exists b sz, GOBJ b sz /\ b <= 0x5d8f00 /\ 0x5d8f00 + 16 * (106 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d8f00, 16 * (106 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC30 : exists b sz, GOBJ b sz /\ b <= 0x5d9760 /\ 0x5d9760 + 16 * (17 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9760, 16 * (17 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC31 : exists b sz, GOBJ b sz /\ b <= 0x5d98c0 /\ 0x5d98c0 + 16 * (9 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d98c0, 16 * (9 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC32 : exists b sz, GOBJ b sz /\ b <= 0x5d9980 /\ 0x5d9980 + 16 * (4 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9980, 16 * (4 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC33 : exists b sz, GOBJ b sz /\ b <= 0x5d9a00 /\ 0x5d9a00 + 16 * (14 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9a00, 16 * (14 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC34 : exists b sz, GOBJ b sz /\ b <= 0x5d9b20 /\ 0x5d9b20 + 16 * (25 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9b20, 16 * (25 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC35 : exists b sz, GOBJ b sz /\ b <= 0x5d9d20 /\ 0x5d9d20 + 16 * (11 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9d20, 16 * (11 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (GC36 : exists b sz, GOBJ b sz /\ b <= 0x5d9e00 /\ 0x5d9e00 + 16 * (160 + 1) <= b + sz) by exact (proj1 (Forall_forall _ _) HGC (0x5d9e00, 16 * (160 + 1)) ltac:(clear; unfold INITA_GCOVER; cbn [In]; repeat (first [left; reflexivity | right]))).
  assert (c1 : crypto_malloc_stmt RT) by (eapply Fz_M_malloc.crypto_malloc_cps; eassumption).
  assert (c2 : crypto_zalloc_stmt RT) by (eapply Fz_M_zalloc.crypto_zalloc_cps; eassumption).
  assert (c3 : crypto_lock_new_stmt RT) by (eapply Fz_M_locknew.crypto_lock_new_cps; eassumption).
  assert (c4 : crypto_lock_new_env_stmt RT) by (eapply Fz_env.crypto_lock_new_env; eassumption).
  assert (c5 : OPENSSL_cpuid_setup_stmt RT) by (eapply Fz_G_OPENSSL_cpuid_setup.OPENSSL_cpuid_setup_cps; eassumption).
  assert (c6 : ibase_stmt RT) by (eapply Fz_I3_ibase.ibase_cps; eassumption).
  assert (c7 : init_crypto_base_stmt RT) by (eapply Fz_W5_icb.init_crypto_base_cps; eassumption).
  assert (c8 : crypto_zalloc_env_stmt RT) by (eapply Fz_env.crypto_zalloc_env; eassumption).
  assert (c9 : CRYPTO_calloc_stmt RT) by (eapply Fz_G_CRYPTO_calloc.CRYPTO_calloc_cps; eassumption).
  assert (c10 : ossl_sa_new_stmt RT) by (eapply Fz_G_ossl_sa_new.ossl_sa_new_cps; eassumption).
  assert (c11 : sa_set_fresh_stmt RT) by (eapply Fz_T_sa_set.sa_set_fresh_cps; eassumption).
  assert (c12 : slx_first_stmt RT) by (eapply Fz_T_slx.slx_first_cps; eassumption).
  assert (c13 : shelve_first_stmt RT) by (eapply Fz_I3_shelve.shelve_first_cps; eassumption).
  assert (c14 : OPENSSL_LH_new_stmt RT) by (eapply Fz_G_OPENSSL_LH_new.OPENSSL_LH_new_cps; eassumption).
  assert (c15 : do_esi_stmt RT GOBJ) by (eapply Fz_I1_first.do_esi_cps; eassumption).
  assert (c16 : crypto_malloc_env_stmt RT) by (eapply Fz_env.crypto_malloc_env; eassumption).
  assert (c17 : crypto_realloc_env_stmt RT) by (eapply Fz_M_realloc.crypto_realloc_cps; eassumption).
  assert (c18 : crypto_realloc_array_env_stmt RT) by (eapply Fz_M_realloc_array.crypto_realloc_array_cps; eassumption).
  assert (c19 : lh_insert_stmt RT GOBJ) by (eapply Fz_I1_insert.lh_insert_cps; eassumption).
  assert (c20 : err_load_strings_stmt RT GOBJ) by (eapply Fz_I1_load.err_load_strings_cps; eassumption).
  assert (c21 : efirst_stmt RT GOBJ) by (eapply Fz_I1_efirst.efirst_cps; eassumption).
  assert (c22 : igi_stmt RT GOBJ) by (eapply Fz_I1_getitem.igi_cps; eassumption).
  assert (c23 : ers_stmt RT GOBJ) by (eapply Fz_I1_reason.ers_cps; eassumption).
  assert (c24 : err_strings_steady_stmt RT GOBJ) by (eapply Fz_I1_errload.err_strings_steady_cps; eassumption).
  assert (c25 : err_const_stmt RT GOBJ) by (eapply Fz_I1_const.err_const_cps; eassumption).
  assert (c26 : crypto_strs_stmt RT GOBJ) by (eapply Fz_I1_crypto.crypto_strs_cps; eassumption).
  assert (c27 : loadstr_stmt RT GOBJ) by (eapply Fz_I3_loadstr.loadstr_cps; eassumption).
  assert (c28 : init_crypto_full_stmt RT GOBJ) by (eapply Fz_I3_full.init_crypto_full_cps; eassumption).
  assert (c29 : crypto_free_null_env_stmt RT) by (eapply Fz_M_free.crypto_free_null_cps; eassumption).
  assert (c30 : crypto_free_env_stmt RT) by (eapply Fz_M_free.crypto_free_cps; eassumption).
  assert (c31 : err_clear_stmt RT) by (eapply Fz_W5_eclr.err_clear_cps; eassumption).
  assert (c32 : OSSL_ERR_STATE_new_stmt RT) by (eapply Fz_G_OSSL_ERR_STATE_new.OSSL_ERR_STATE_new_cps; eassumption).
  assert (c33 : OPENSSL_sk_new_null_stmt RT) by (eapply Fz_G_OPENSSL_sk_new_null.OPENSSL_sk_new_null_cps; eassumption).
  assert (c34 : OPENSSL_sk_set_cmp_thunks_stmt RT) by (eapply Fz_G_OPENSSL_sk_set_cmp_thunks.OPENSSL_sk_set_cmp_thunks_cps; eassumption).
  assert (c35 : OPENSSL_sk_set_copy_thunks_stmt RT) by (eapply Fz_G_OPENSSL_sk_set_copy_thunks.OPENSSL_sk_set_copy_thunks_cps; eassumption).
  assert (c36 : OPENSSL_sk_set_thunks_stmt RT) by (eapply Fz_G_OPENSSL_sk_set_thunks.OPENSSL_sk_set_thunks_cps; eassumption).
  assert (c37 : create_global_tevent_register_ossl_stmt RT) by (eapply Fz_G_create_global_tevent_register_ossl.create_global_tevent_register_ossl_cps; eassumption).
  assert (c38 : its_first_stmt RT) by (eapply Fz_T_its.its_first_cps; eassumption).
  assert (c39 : init_crypto_fast_stmt RT) by (eapply Fz_I3_icfast.init_crypto_fast_cps; eassumption).
  assert (c40 : egsi_first_stmt RT) by (eapply Fz_I3_egsi.egsi_first_cps; eassumption).
  assert (c41 : eclear_first_stmt RT) by (eapply Fz_I3_eclear.eclear_first_cps; eassumption).
  assert (c42 : ossl_lib_ctx_get_ex_data_global_stmt RT) by (eapply Fz_G_ossl_lib_ctx_get_ex_data_global.ossl_lib_ctx_get_ex_data_global_cps; eassumption).
  assert (c43 : ossl_do_ex_data_init_stmt RT) by (eapply Fz_G_ossl_do_ex_data_init.ossl_do_ex_data_init_cps; eassumption).
  assert (c44 : ossl_method_store_new_stmt RT) by (eapply Fz_G_ossl_method_store_new.ossl_method_store_new_cps; eassumption).
  assert (c45 : ossl_prov_conf_ctx_new_stmt RT) by (eapply Fz_G_ossl_prov_conf_ctx_new.ossl_prov_conf_ctx_new_cps; eassumption).
  assert (c46 : crypto_strdup_env_stmt RT GOBJ) by (eapply Fz_M_strdup.crypto_strdup_cps; eassumption).
  assert (c47 : rand_ctx_new_stmt RT) by (eapply Fz_I2_rcx.rand_ctx_new_cps; eassumption).
  assert (c48 : OPENSSL_LH_set_thunks_keep_stmt RT) by (eapply Fz_I2_lhst.OPENSSL_LH_set_thunks_keep_cps; eassumption).
  assert (c49 : ossl_decoder_cache_new_stmt RT) by (eapply Fz_G_ossl_decoder_cache_new.ossl_decoder_cache_new_cps; eassumption).
  assert (c50 : OPENSSL_sk_new_stmt RT) by (eapply Fz_G_OPENSSL_sk_new.OPENSSL_sk_new_cps; eassumption).
  assert (c51 : ossl_provider_store_new_stmt RT) by (eapply Fz_G_ossl_provider_store_new.ossl_provider_store_new_cps; eassumption).
  assert (c52 : ossl_property_string_data_new_stmt RT) by (eapply Fz_G_ossl_property_string_data_new.ossl_property_string_data_new_cps; eassumption).
  assert (c53 : crypto_aligned_alloc_env_stmt RT) by (eapply Fz_M_aligned.crypto_aligned_alloc_cps; eassumption).
  assert (c54 : crypto_aligned_alloc_array_env_stmt RT) by (eapply Fz_M_aligned_array.crypto_aligned_alloc_array_cps; eassumption).
  assert (c55 : anl_stmt RT) by (eapply Fz_I2_anl.anl_cps; eassumption).
  assert (c56 : rcu_lock_new_stmt RT) by (eapply Fz_T_rcu.rcu_lock_new_cps; eassumption).
  assert (c57 : ht_new_stmt RT) by (eapply Fz_I2_htnew.ht_new_cps; eassumption).
  assert (c58 : namemap_new_stmt RT) by (eapply Fz_I2_namemap.namemap_new_cps; eassumption).
  assert (c59 : stored_namemap_new_stmt RT) by (eapply Fz_I2_snm.stored_namemap_new_cps; eassumption).
  assert (c60 : ossl_property_defns_new_stmt RT) by (eapply Fz_I2_pdefnsd.ossl_property_defns_new_cps; eassumption).
  assert (c61 : ossl_ctx_global_properties_new_stmt RT) by (eapply Fz_G_ossl_ctx_global_properties_new.ossl_ctx_global_properties_new_cps; eassumption).
  assert (c62 : ossl_bio_core_globals_new_stmt RT) by (eapply Fz_G_ossl_bio_core_globals_new.ossl_bio_core_globals_new_cps; eassumption).
  assert (c63 : ossl_prov_drbg_nonce_ctx_new_stmt RT) by (eapply Fz_G_ossl_prov_drbg_nonce_ctx_new.ossl_prov_drbg_nonce_ctx_new_cps; eassumption).
  assert (c64 : ossl_self_test_set_callback_new_stmt RT) by (eapply Fz_G_ossl_self_test_set_callback_new.ossl_self_test_set_callback_new_cps; eassumption).
  assert (c65 : ossl_indicator_set_callback_new_stmt RT) by (eapply Fz_G_ossl_indicator_set_callback_new.ossl_indicator_set_callback_new_cps; eassumption).
  assert (c66 : ossl_crypto_mutex_new_stmt RT) by (eapply Fz_G_ossl_crypto_mutex_new.ossl_crypto_mutex_new_cps; eassumption).
  assert (c67 : ossl_crypto_condvar_new_stmt RT) by (eapply Fz_G_ossl_crypto_condvar_new.ossl_crypto_condvar_new_cps; eassumption).
  assert (c68 : ossl_threads_ctx_new_stmt RT) by (eapply Fz_G_ossl_threads_ctx_new.ossl_threads_ctx_new_cps; eassumption).
  assert (c69 : ossl_child_prov_ctx_new_stmt RT) by (eapply Fz_G_ossl_child_prov_ctx_new.ossl_child_prov_ctx_new_cps; eassumption).
  assert (c70 : pstr_first_stmt RT GOBJ) by (eapply Fz_K_pstrf.pstr_first_cps; eassumption).
  assert (c71 : pstr_room_stmt RT GOBJ) by (eapply Fz_K_pstr.pstr_room_cps; eassumption).
  assert (c72 : pstr_grow_stmt RT GOBJ) by (eapply Fz_K_pstrg.pstr_grow_cps; eassumption).
  assert (c73 : ossl_property_parse_init_stmt RT) by (eapply Fz_I2_ppi2.ossl_property_parse_init_cps; eassumption).
  assert (c74 : COMP_zlib_stmt RT) by (eapply Fz_G_COMP_zlib.COMP_zlib_cps; eassumption).
  assert (c75 : COMP_get_type_stmt RT) by (eapply Fz_G_COMP_get_type.COMP_get_type_cps; eassumption).
  assert (c76 : ossl_load_builtin_compressions_stmt RT) by (eapply Fz_G_ossl_load_builtin_compressions.ossl_load_builtin_compressions_cps; eassumption).
  assert (c77 : context_init_stmt RT) by (eapply Fz_G_context_init.context_init_cps; eassumption).
  assert (c78 : default_context_do_init_ossl_stmt RT) by (eapply Fz_G_default_context_do_init_ossl.default_context_do_init_ossl_cps; eassumption).
  assert (c79 : gdc_stmt RT) by (eapply Fz_I3_gdc.gdc_cps; eassumption).
  assert (c80 : fxi_stmt RT) by (eapply Fz_I3_fxi.fxi_cps; eassumption).
  eapply (fuzz_init_A RT GOBJ); eassumption.
Qed.
End InitA.
