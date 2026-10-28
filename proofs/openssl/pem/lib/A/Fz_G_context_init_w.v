(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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

Definition e_context_init : Z := 0x1f6f4c.
Definition SITE_context_init_1 : Z := 0x1f6f7c.     (* [comment removed for export] *)
Definition SITE_context_init_2 : Z := 0x1f6f9c.     (* [comment removed for export] *)
Definition SITE_context_init_3 : Z := 0x1f6fa8.     (* [comment removed for export] *)
Definition SITE_context_init_4 : Z := 0x1f6fcc.     (* [comment removed for export] *)
Definition SITE_context_init_5 : Z := 0x1f6ff0.     (* [comment removed for export] *)
Definition SITE_context_init_6 : Z := 0x1f7014.     (* [comment removed for export] *)
Definition SITE_context_init_7 : Z := 0x1f703c.     (* [comment removed for export] *)
Definition SITE_context_init_8 : Z := 0x1f7060.     (* [comment removed for export] *)
Definition SITE_context_init_9 : Z := 0x1f7084.     (* [comment removed for export] *)
Definition SITE_context_init_10 : Z := 0x1f70a8.     (* [comment removed for export] *)
Definition SITE_context_init_11 : Z := 0x1f70cc.     (* [comment removed for export] *)
Definition SITE_context_init_12 : Z := 0x1f70f0.     (* [comment removed for export] *)
Definition SITE_context_init_13 : Z := 0x1f7114.     (* [comment removed for export] *)
Definition SITE_context_init_14 : Z := 0x1f7138.     (* [comment removed for export] *)
Definition SITE_context_init_15 : Z := 0x1f7160.     (* [comment removed for export] *)
Definition SITE_context_init_16 : Z := 0x1f7188.     (* [comment removed for export] *)
Definition SITE_context_init_17 : Z := 0x1f71ac.     (* [comment removed for export] *)
Definition SITE_context_init_18 : Z := 0x1f71d4.     (* [comment removed for export] *)
Definition SITE_context_init_19 : Z := 0x1f71fc.     (* [comment removed for export] *)
Definition SITE_context_init_20 : Z := 0x1f7220.     (* [comment removed for export] *)
Definition SITE_context_init_21 : Z := 0x1f7244.     (* [comment removed for export] *)
Definition SITE_context_init_22 : Z := 0x1f7250.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition context_init_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j1 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060156) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 6736696) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2055740) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187240 [C8 g11]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187224 [C8 g9]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187184 [C8 g4]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ rw_cells asegs m' 12187008 [C8 g2]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m 0xb9f580 [C8 g2] ->
  rw_cells asegs m 0xb9f628 [C8 g3] ->
  rw_cells asegs m 0xb9f630 [C8 g4] ->
  rw_cells asegs m 0xb9f638 [C8 g5] ->
  rw_cells asegs m 0xb9f640 [C8 g6] ->
  rw_cells asegs m 0xb9f648 [C8 g7] ->
  rw_cells asegs m 0xb9f650 [C8 g8] ->
  rw_cells asegs m 0xb9f658 [C8 g9] ->
  rw_cells asegs m 0xb9f660 [C8 g10] ->
  rw_cells asegs m 0xb9f668 [C8 g11] ->
  rw_cells asegs m 0xb9f670 [C8 g12] ->
  rw_cells asegs m 0xb9f678 [C8 g13] ->
  rw_cells asegs m 0xb9f680 [C8 g14] ->
  rw_cells asegs m 0xb9f688 [C8 g15] ->
  rw_cells asegs m 0xb9f690 [C8 g16] ->
  rw_cells asegs m 0xb9f698 [C8 g17] ->
  rw_cells asegs m 0xb9f6a0 [C8 g18] ->
  rw_cells asegs m 0xb9f6a8 [C8 g19] ->
  rw_cells asegs m 0xb9f6b0 [C8 g20] ->
  rw_cells asegs m 0xb9f6b8 [C8 g21] ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (context_init_s0_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 12187008) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f6f4c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep.
  do 5 zstore.
  do 6 zstep.
  unfold context_init_s0_post. apply evt_done. do 2 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (j1 : list byte) (g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060188) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 0) b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2064540) fc1 None m' (seg_rom asegs)
    /\ munch [(0xb9f580, 0xb9f588); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187240 [C8 g11]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187224 [C8 g9]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187184 [C8 g4]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (j1 : list byte) (g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187240 [C8 g11] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187224 [C8 g9] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187184 [C8 g4] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  rw_cells asegs m 12187008 [C8 g2] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v1) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 j1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x1f6f7c) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G11 G10 G9 G8 G7 G6 G5 G4 G3 G2 G1 Hv1 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR1_4 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f580, 0xb9f588); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR1_4.
  do 2 zstep.
  unfold context_init_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j1 : list byte) (g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060200) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2115364) fc2 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187240 [C8 g11]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187224 [C8 g9]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187184 [C8 g4]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j1 : list byte) (g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187240 [C8 g11] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187224 [C8 g9] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187184 [C8 g4] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j1 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x1f6f9c) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G2 FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G11 G10 G9 G8 G7 G6 G5 G4 G3 G1 Hv1 Hv2 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR2_1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_raw BR2_1.
  do 2 zstep.
  unfold context_init_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v3 : Z) (j1 : list byte) (g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060236) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187184) (Z_to_bv 64 0) b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2153804) fc3 None m' (seg_rom asegs)
    /\ munch [(0xb9f630, 0xb9f638); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187240 [C8 g11]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187224 [C8 g9]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s3_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v3 : Z) (j1 : list byte) (g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187240 [C8 g11] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187224 [C8 g9] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187184 [C8 g4] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v3) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v3 j1 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x1f6fa8) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G2 FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G11 G10 G9 G8 G7 G6 G5 G4 G3 G1 Hv1 Hv3 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR3_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f630, 0xb9f638); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR3_2.
  do 2 zstep.
  unfold context_init_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v3 v4 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060272) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187240) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 2439280) fc4 None m' (seg_rom asegs)
    /\ munch [(0xb9f668, 0xb9f670); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187224 [C8 g9]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s4_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v3 v4 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187240 [C8 g11] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187224 [C8 g9] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v3 v4 j1 g3 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x1f6fcc) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G4 G2 FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G11 G10 G9 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR4_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f668, 0xb9f670); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR4_2.
  do 2 zstep.
  unfold context_init_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v3 v4 v5 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g9 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060308) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187224) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 2115364) fc5 None m' (seg_rom asegs)
    /\ munch [(0xb9f658, 0xb9f660); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187264 [C8 g14]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s5_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v3 v4 v5 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g9 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187224 [C8 g9] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v5) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v3 v4 v5 j1 g3 g5 g6 g7 g8 g9 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x1f6ff0) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G11 G4 G2 FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G10 G9 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR5_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f658, 0xb9f660); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR5_2.
  do 2 zstep.
  unfold context_init_s5_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v3 v4 v5 v6 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060348) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187264) (Z_to_bv 64 0) b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 3233184) fc6 None m' (seg_rom asegs)
    /\ munch [(0xb9f680, 0xb9f688); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187272 [C8 g15]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s6_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v3 v4 v5 v6 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 : word) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187264 [C8 g14] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v3 v4 v5 v6 j1 g3 g5 g6 g7 g8 g10 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x1f7014) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G9 G11 G4 G2 FR G21 G20 G19 G18 G17 G16 G15 G14 G13 G12 G10 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR6_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f680, 0xb9f688); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR6_2.
  do 2 zstep.
  unfold context_init_s6_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v3 v4 v5 v6 v7 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g15 g16 g17 g18 g19 g20 g21 : word) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060384) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187272) (Z_to_bv 64 0) b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
            F7 (Z_to_bv 64 2115364) fc7 None m' (seg_rom asegs)
    /\ munch [(0xb9f688, 0xb9f690); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187280 [C8 g16]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s7_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v3 v4 v5 v6 v7 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g15 g16 g17 g18 g19 g20 g21 : word) (F7 : bvmap 5 word) (fc7 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187272 [C8 g15] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v7) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v3 v4 v5 v6 v7 j1 g3 g5 g6 g7 g8 g10 g12 g13 g15 g16 g17 g18 g19 g20 g21 F7 fc7 lo m)
    (MS (mkR ra7 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v7) b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
        F7 (Z_to_bv 64 0x1f703c) fc7 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G17 G16 G15 G13 G12 G10 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR7_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f688, 0xb9f690); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR7_2.
  do 2 zstep.
  unfold context_init_s7_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s8_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v3 v4 v5 v6 v7 v8 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g16 g17 g18 g19 g20 g21 : word) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060420) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187280) (Z_to_bv 64 0) b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
            F8 (Z_to_bv 64 2115364) fc8 None m' (seg_rom asegs)
    /\ munch [(0xb9f690, 0xb9f698); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187288 [C8 g17]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s8_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v3 v4 v5 v6 v7 v8 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g16 g17 g18 g19 g20 g21 : word) (F8 : bvmap 5 word) (fc8 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187280 [C8 g16] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v8) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v3 v4 v5 v6 v7 v8 j1 g3 g5 g6 g7 g8 g10 g12 g13 g16 g17 g18 g19 g20 g21 F8 fc8 lo m)
    (MS (mkR ra8 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v8) b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
        F8 (Z_to_bv 64 0x1f7060) fc8 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G17 G16 G13 G12 G10 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR8_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f690, 0xb9f698); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR8_2.
  do 2 zstep.
  unfold context_init_s8_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s9_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v3 v4 v5 v6 v7 v8 v9 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g17 g18 g19 g20 g21 : word) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060456) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187288) (Z_to_bv 64 0) b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
            F9 (Z_to_bv 64 2160100) fc9 None m' (seg_rom asegs)
    /\ munch [(0xb9f698, 0xb9f6a0); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187192 [C8 g5]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s9_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v3 v4 v5 v6 v7 v8 v9 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g17 g18 g19 g20 g21 : word) (F9 : bvmap 5 word) (fc9 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187288 [C8 g17] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v9) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s9_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v3 v4 v5 v6 v7 v8 v9 j1 g3 g5 g6 g7 g8 g10 g12 g13 g17 g18 g19 g20 g21 F9 fc9 lo m)
    (MS (mkR ra9 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v9) b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
        F9 (Z_to_bv 64 0x1f7084) fc9 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G17 G13 G12 G10 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR9_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f698, 0xb9f6a0); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR9_2.
  do 2 zstep.
  unfold context_init_s9_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s10_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060492) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187192) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 2145524) fc10 None m' (seg_rom asegs)
    /\ munch [(0xb9f638, 0xb9f640); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ rw_cells asegs m' 12187176 [C8 g3]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s10_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (j1 : list byte) (g3 g5 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F10 : bvmap 5 word) (fc10 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187192 [C8 g5] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v10) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s10_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v3 v4 v5 v6 v7 v8 v9 v10 j1 g3 g5 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F10 fc10 lo m)
    (MS (mkR ra10 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v10) b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
        F10 (Z_to_bv 64 0x1f70a8) fc10 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G8 G7 G6 G5 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR10_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f638, 0xb9f640); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR10_2.
  do 2 zstep.
  unfold context_init_s10_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s11_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (j1 : list byte) (g3 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060528) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187176) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (Z_to_bv 64 2195816) fc11 None m' (seg_rom asegs)
    /\ munch [(0xb9f628, 0xb9f630); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ rw_cells asegs m' 12187200 [C8 g6]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s11_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (j1 : list byte) (g3 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F11 : bvmap 5 word) (fc11 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  rw_cells asegs m 12187176 [C8 g3] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v11) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s11_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 j1 g3 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F11 fc11 lo m)
    (MS (mkR ra11 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v11) b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
        F11 (Z_to_bv 64 0x1f70cc) fc11 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G8 G7 G6 G3 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR11_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f628, 0xb9f630); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR11_2.
  do 2 zstep.
  unfold context_init_s11_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s12_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (j1 : list byte) (g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F12 : bvmap 5 word) (fc12 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060564) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187200) (Z_to_bv 64 0) b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
            F12 (Z_to_bv 64 2151080) fc12 None m' (seg_rom asegs)
    /\ munch [(0xb9f640, 0xb9f648); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ rw_cells asegs m' 12187208 [C8 g7]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s12_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (j1 : list byte) (g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F12 : bvmap 5 word) (fc12 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  rw_cells asegs m 12187200 [C8 g6] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v12) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s12_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 j1 g6 g7 g8 g10 g12 g13 g18 g19 g20 g21 F12 fc12 lo m)
    (MS (mkR ra12 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v12) b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
        F12 (Z_to_bv 64 0x1f70f0) fc12 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G8 G7 G6 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR12_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f640, 0xb9f648); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR12_2.
  do 2 zstep.
  unfold context_init_s12_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s13_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (j1 : list byte) (g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F13 : bvmap 5 word) (fc13 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060600) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187208) (Z_to_bv 64 0) b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
            F13 (Z_to_bv 64 2115012) fc13 None m' (seg_rom asegs)
    /\ munch [(0xb9f648, 0xb9f650); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ rw_cells asegs m' 12187216 [C8 g8]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s13_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (j1 : list byte) (g7 g8 g10 g12 g13 g18 g19 g20 g21 : word) (F13 : bvmap 5 word) (fc13 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  rw_cells asegs m 12187208 [C8 g7] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v13) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s13_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 j1 g7 g8 g10 g12 g13 g18 g19 g20 g21 F13 fc13 lo m)
    (MS (mkR ra13 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v13) b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
        F13 (Z_to_bv 64 0x1f7114) fc13 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G8 G7 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR13_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f648, 0xb9f650); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR13_2.
  do 2 zstep.
  unfold context_init_s13_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s14_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (j1 : list byte) (g8 g10 g12 g13 g18 g19 g20 g21 : word) (F14 : bvmap 5 word) (fc14 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060640) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187216) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
            F14 (Z_to_bv 64 5310392) fc14 None m' (seg_rom asegs)
    /\ munch [(0xb9f650, 0xb9f658); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187248 [C8 g12]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s14_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (j1 : list byte) (g8 g10 g12 g13 g18 g19 g20 g21 : word) (F14 : bvmap 5 word) (fc14 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  rw_cells asegs m 12187216 [C8 g8] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v14) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s14_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 j1 g8 g10 g12 g13 g18 g19 g20 g21 F14 fc14 lo m)
    (MS (mkR ra14 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v14) b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
        F14 (Z_to_bv 64 0x1f7138) fc14 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G8 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR14_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f650, 0xb9f658); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR14_2.
  do 2 zstep.
  unfold context_init_s14_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s15_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (j1 : list byte) (g10 g12 g13 g18 g19 g20 g21 : word) (F15 : bvmap 5 word) (fc15 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060680) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_15 u1_15 u2_15 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187248) (Z_to_bv 64 0) b3_15 b4_15 b5_15 b6_15 b7_15 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
            F15 (Z_to_bv 64 4306280) fc15 None m' (seg_rom asegs)
    /\ munch [(0xb9f670, 0xb9f678); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ rw_cells asegs m' 12187232 [C8 g10]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s15_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (j1 : list byte) (g10 g12 g13 g18 g19 g20 g21 : word) (F15 : bvmap 5 word) (fc15 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187248 [C8 g12] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v15) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s15_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 j1 g10 g12 g13 g18 g19 g20 g21 F15 fc15 lo m)
    (MS (mkR ra15 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_15 u1_15 u2_15 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v15) b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
        F15 (Z_to_bv 64 0x1f7160) fc15 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G12 G10 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR15_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f670, 0xb9f678); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR15_2.
  do 2 zstep.
  unfold context_init_s15_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra16 u0_16 u1_16 u2_16 b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 u3_16 u4_16 u5_16 u6_16 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Z) (j1 : list byte) (g10 g13 g18 g19 g20 g21 : word) (F16 : bvmap 5 word) (fc16 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060716) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_16 u1_16 u2_16 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187232) (Z_to_bv 64 0) b3_16 b4_16 b5_16 b6_16 b7_16 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_16 u4_16 u5_16 u6_16)
            F16 (Z_to_bv 64 2965112) fc16 None m' (seg_rom asegs)
    /\ munch [(0xb9f660, 0xb9f668); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187296 [C8 g18]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s16_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra16 u0_16 u1_16 u2_16 b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 u3_16 u4_16 u5_16 u6_16 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 : Z) (j1 : list byte) (g10 g13 g18 g19 g20 g21 : word) (F16 : bvmap 5 word) (fc16 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  rw_cells asegs m 12187232 [C8 g10] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v16) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra16 u0_16 u1_16 u2_16 b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 u3_16 u4_16 u5_16 u6_16 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 j1 g10 g13 g18 g19 g20 g21 F16 fc16 lo m)
    (MS (mkR ra16 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_16 u1_16 u2_16 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v16) b1_16 b2_16 b3_16 b4_16 b5_16 b6_16 b7_16 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_16 u4_16 u5_16 u6_16)
        F16 (Z_to_bv 64 0x1f7188) fc16 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G10 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR16_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f660, 0xb9f668); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR16_2.
  do 2 zstep.
  unfold context_init_s16_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s17_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra17 u0_17 u1_17 u2_17 b1_17 b2_17 b3_17 b4_17 b5_17 b6_17 b7_17 u3_17 u4_17 u5_17 u6_17 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : Z) (j1 : list byte) (g13 g18 g19 g20 g21 : word) (F17 : bvmap 5 word) (fc17 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060756) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_17 u1_17 u2_17 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187296) (Z_to_bv 64 0) b3_17 b4_17 b5_17 b6_17 b7_17 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_17 u4_17 u5_17 u6_17)
            F17 (Z_to_bv 64 5308624) fc17 None m' (seg_rom asegs)
    /\ munch [(0xb9f6a0, 0xb9f6a8); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187304 [C8 g19]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s17_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra17 u0_17 u1_17 u2_17 b1_17 b2_17 b3_17 b4_17 b5_17 b6_17 b7_17 u3_17 u4_17 u5_17 u6_17 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : Z) (j1 : list byte) (g13 g18 g19 g20 g21 : word) (F17 : bvmap 5 word) (fc17 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187296 [C8 g18] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v17) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s17_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra17 u0_17 u1_17 u2_17 b1_17 b2_17 b3_17 b4_17 b5_17 b6_17 b7_17 u3_17 u4_17 u5_17 u6_17 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 j1 g13 g18 g19 g20 g21 F17 fc17 lo m)
    (MS (mkR ra17 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_17 u1_17 u2_17 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v17) b1_17 b2_17 b3_17 b4_17 b5_17 b6_17 b7_17 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_17 u4_17 u5_17 u6_17)
        F17 (Z_to_bv 64 0x1f71ac) fc17 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G18 G13 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR17_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f6a0, 0xb9f6a8); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR17_2.
  do 2 zstep.
  unfold context_init_s17_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s18_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra18 u0_18 u1_18 u2_18 b1_18 b2_18 b3_18 b4_18 b5_18 b6_18 b7_18 u3_18 u4_18 u5_18 u6_18 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : Z) (j1 : list byte) (g13 g19 g20 g21 : word) (F18 : bvmap 5 word) (fc18 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060796) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_18 u1_18 u2_18 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187304) (Z_to_bv 64 0) b3_18 b4_18 b5_18 b6_18 b7_18 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_18 u4_18 u5_18 u6_18)
            F18 (Z_to_bv 64 4351556) fc18 None m' (seg_rom asegs)
    /\ munch [(0xb9f6a8, 0xb9f6b0); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 v18)]
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187312 [C8 g20]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s18_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra18 u0_18 u1_18 u2_18 b1_18 b2_18 b3_18 b4_18 b5_18 b6_18 b7_18 u3_18 u4_18 u5_18 u6_18 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 : Z) (j1 : list byte) (g13 g19 g20 g21 : word) (F18 : bvmap 5 word) (fc18 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187296 [C8 (Z_to_bv 64 v17)] ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187304 [C8 g19] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  0 <= v18 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v18) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s18_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra18 u0_18 u1_18 u2_18 b1_18 b2_18 b3_18 b4_18 b5_18 b6_18 b7_18 u3_18 u4_18 u5_18 u6_18 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 j1 g13 g19 g20 g21 F18 fc18 lo m)
    (MS (mkR ra18 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_18 u1_18 u2_18 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v18) b1_18 b2_18 b3_18 b4_18 b5_18 b6_18 b7_18 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_18 u4_18 u5_18 u6_18)
        F18 (Z_to_bv 64 0x1f71d4) fc18 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G18 G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G19 G13 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hv18 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR18_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f6a8, 0xb9f6b0); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR18_2.
  do 2 zstep.
  unfold context_init_s18_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s19_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra19 u0_19 u1_19 u2_19 b1_19 b2_19 b3_19 b4_19 b5_19 b6_19 b7_19 u3_19 u4_19 u5_19 u6_19 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : Z) (j1 : list byte) (g13 g20 g21 : word) (F19 : bvmap 5 word) (fc19 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060832) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_19 u1_19 u2_19 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187312) (Z_to_bv 64 0) b3_19 b4_19 b5_19 b6_19 b7_19 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_19 u4_19 u5_19 u6_19)
            F19 (Z_to_bv 64 2184068) fc19 None m' (seg_rom asegs)
    /\ munch [(0xb9f6b0, 0xb9f6b8); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187312 [C8 (Z_to_bv 64 v19)]
    /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 v18)]
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ rw_cells asegs m' 12187256 [C8 g13]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s19_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra19 u0_19 u1_19 u2_19 b1_19 b2_19 b3_19 b4_19 b5_19 b6_19 b7_19 u3_19 u4_19 u5_19 u6_19 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : Z) (j1 : list byte) (g13 g20 g21 : word) (F19 : bvmap 5 word) (fc19 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187304 [C8 (Z_to_bv 64 v18)] ->
  rw_cells asegs m 12187296 [C8 (Z_to_bv 64 v17)] ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187312 [C8 g20] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  0 <= v18 < 2 ^ 64 ->
  0 <= v19 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v19) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s19_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra19 u0_19 u1_19 u2_19 b1_19 b2_19 b3_19 b4_19 b5_19 b6_19 b7_19 u3_19 u4_19 u5_19 u6_19 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 j1 g13 g20 g21 F19 fc19 lo m)
    (MS (mkR ra19 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_19 u1_19 u2_19 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v19) b1_19 b2_19 b3_19 b4_19 b5_19 b6_19 b7_19 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_19 u4_19 u5_19 u6_19)
        F19 (Z_to_bv 64 0x1f71fc) fc19 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G19 G18 G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G20 G13 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hv18 Hv19 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR19_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f6b0, 0xb9f6b8); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR19_2.
  do 2 zstep.
  unfold context_init_s19_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s20_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra20 u0_20 u1_20 u2_20 b1_20 b2_20 b3_20 b4_20 b5_20 b6_20 b7_20 u3_20 u4_20 u5_20 u6_20 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : Z) (j1 : list byte) (g13 g21 : word) (F20 : bvmap 5 word) (fc20 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060868) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_20 u1_20 u2_20 sp (Z_to_bv 64 12187008) (Z_to_bv 64 12187008) (Z_to_bv 64 12187256) (Z_to_bv 64 0) b3_20 b4_20 b5_20 b6_20 b7_20 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_20 u4_20 u5_20 u6_20)
            F20 (Z_to_bv 64 2140876) fc20 None m' (seg_rom asegs)
    /\ munch [(0xb9f678, 0xb9f680); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187256 [C8 (Z_to_bv 64 v20)]
    /\ rw_cells asegs m' 12187312 [C8 (Z_to_bv 64 v19)]
    /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 v18)]
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s20_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra20 u0_20 u1_20 u2_20 b1_20 b2_20 b3_20 b4_20 b5_20 b6_20 b7_20 u3_20 u4_20 u5_20 u6_20 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : Z) (j1 : list byte) (g13 g21 : word) (F20 : bvmap 5 word) (fc20 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187312 [C8 (Z_to_bv 64 v19)] ->
  rw_cells asegs m 12187304 [C8 (Z_to_bv 64 v18)] ->
  rw_cells asegs m 12187296 [C8 (Z_to_bv 64 v17)] ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  rw_cells asegs m 12187256 [C8 g13] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  0 <= v18 < 2 ^ 64 ->
  0 <= v19 < 2 ^ 64 ->
  0 <= v20 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  (bv_eqb (Z_to_bv 64 v20) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (context_init_s20_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra20 u0_20 u1_20 u2_20 b1_20 b2_20 b3_20 b4_20 b5_20 b6_20 b7_20 u3_20 u4_20 u5_20 u6_20 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 j1 g13 g21 F20 fc20 lo m)
    (MS (mkR ra20 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_20 u1_20 u2_20 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v20) b1_20 b2_20 b3_20 b4_20 b5_20 b6_20 b7_20 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_20 u4_20 u5_20 u6_20)
        F20 (Z_to_bv 64 0x1f7220) fc20 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G20 G19 G18 G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G13 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hv18 Hv19 Hv20 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 BR20_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f678, 0xb9f680); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR20_2.
  do 2 zstep.
  unfold context_init_s20_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s21_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra21 u0_21 u1_21 u2_21 b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 u3_21 u4_21 u5_21 u6_21 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : Z) (j1 : list byte) (g21 : word) (F21 : bvmap 5 word) (fc21 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2060880) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_21 u1_21 u2_21 sp (Z_to_bv 64 12187008) (Z_to_bv 64 1) b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_21 u4_21 u5_21 u6_21)
            F21 (Z_to_bv 64 5311392) fc21 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187256 [C8 (Z_to_bv 64 v20)]
    /\ rw_cells asegs m' 12187312 [C8 (Z_to_bv 64 v19)]
    /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 v18)]
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 12187320 [C8 g21]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma context_init_s21_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra21 u0_21 u1_21 u2_21 b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 u3_21 u4_21 u5_21 u6_21 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : Z) (j1 : list byte) (g21 : word) (F21 : bvmap 5 word) (fc21 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187256 [C8 (Z_to_bv 64 v20)] ->
  rw_cells asegs m 12187312 [C8 (Z_to_bv 64 v19)] ->
  rw_cells asegs m 12187304 [C8 (Z_to_bv 64 v18)] ->
  rw_cells asegs m 12187296 [C8 (Z_to_bv 64 v17)] ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  0 <= v18 < 2 ^ 64 ->
  0 <= v19 < 2 ^ 64 ->
  0 <= v20 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (context_init_s21_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra21 u0_21 u1_21 u2_21 b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 u3_21 u4_21 u5_21 u6_21 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 j1 g21 F21 fc21 lo m)
    (MS (mkR ra21 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_21 u1_21 u2_21 sp (Z_to_bv 64 12187008) (Z_to_bv 64 1) b1_21 b2_21 b3_21 b4_21 b5_21 b6_21 b7_21 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_21 u4_21 u5_21 u6_21)
        F21 (Z_to_bv 64 0x1f7244) fc21 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G13 G20 G19 G18 G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hv18 Hv19 Hv20 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  zstep.
  unfold context_init_s21_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition context_init_s22_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra22 u0_22 u1_22 u2_22 b1_22 b2_22 b3_22 b4_22 b5_22 b6_22 b7_22 u3_22 u4_22 u5_22 u6_22 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v22 : Z) (j1 : list byte) (g21 : word) (F22 : bvmap 5 word) (fc22 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_22 u1_22 u2_22 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 12187320) (Z_to_bv 64 0) b3_22 b4_22 b5_22 b6_22 b7_22 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_22 u4_22 u5_22 u6_22)
            F22 (ret_pc ra) fc22 None m' (seg_rom asegs)
    /\ munch [(0xb9f6b8, 0xb9f6c0); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' 12187320 [C8 (Z_to_bv 64 v22)]
    /\ rw_cells asegs m' 12187256 [C8 (Z_to_bv 64 v20)]
    /\ rw_cells asegs m' 12187312 [C8 (Z_to_bv 64 v19)]
    /\ rw_cells asegs m' 12187304 [C8 (Z_to_bv 64 v18)]
    /\ rw_cells asegs m' 12187296 [C8 (Z_to_bv 64 v17)]
    /\ rw_cells asegs m' 12187232 [C8 (Z_to_bv 64 v16)]
    /\ rw_cells asegs m' 12187248 [C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' 12187216 [C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' 12187208 [C8 (Z_to_bv 64 v13)]
    /\ rw_cells asegs m' 12187200 [C8 (Z_to_bv 64 v12)]
    /\ rw_cells asegs m' 12187176 [C8 (Z_to_bv 64 v11)]
    /\ rw_cells asegs m' 12187192 [C8 (Z_to_bv 64 v10)]
    /\ rw_cells asegs m' 12187288 [C8 (Z_to_bv 64 v9)]
    /\ rw_cells asegs m' 12187280 [C8 (Z_to_bv 64 v8)]
    /\ rw_cells asegs m' 12187272 [C8 (Z_to_bv 64 v7)]
    /\ rw_cells asegs m' 12187264 [C8 (Z_to_bv 64 v6)]
    /\ rw_cells asegs m' 12187224 [C8 (Z_to_bv 64 v5)]
    /\ rw_cells asegs m' 12187240 [C8 (Z_to_bv 64 v4)]
    /\ rw_cells asegs m' 12187184 [C8 (Z_to_bv 64 v3)]
    /\ rw_cells asegs m' 12187008 [C8 (Z_to_bv 64 v1)]
    /\ ro_cells asegs m' 2148974295 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974287 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974294 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974293 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974292 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974284 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974286 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974282 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974281 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974280 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974277 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974279 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974291 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974290 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974289 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974288 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974283 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974285 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974278 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 2148974256 [C1 (Z_to_bv 8 0)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma context_init_s22_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra22 u0_22 u1_22 u2_22 b1_22 b2_22 b3_22 b4_22 b5_22 b6_22 b7_22 u3_22 u4_22 u5_22 u6_22 : word) (v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v22 : Z) (j1 : list byte) (g21 : word) (F22 : bvmap 5 word) (fc22 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m 12187256 [C8 (Z_to_bv 64 v20)] ->
  rw_cells asegs m 12187312 [C8 (Z_to_bv 64 v19)] ->
  rw_cells asegs m 12187304 [C8 (Z_to_bv 64 v18)] ->
  rw_cells asegs m 12187296 [C8 (Z_to_bv 64 v17)] ->
  rw_cells asegs m 12187232 [C8 (Z_to_bv 64 v16)] ->
  rw_cells asegs m 12187248 [C8 (Z_to_bv 64 v15)] ->
  rw_cells asegs m 12187216 [C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m 12187208 [C8 (Z_to_bv 64 v13)] ->
  rw_cells asegs m 12187200 [C8 (Z_to_bv 64 v12)] ->
  rw_cells asegs m 12187176 [C8 (Z_to_bv 64 v11)] ->
  rw_cells asegs m 12187192 [C8 (Z_to_bv 64 v10)] ->
  rw_cells asegs m 12187288 [C8 (Z_to_bv 64 v9)] ->
  rw_cells asegs m 12187280 [C8 (Z_to_bv 64 v8)] ->
  rw_cells asegs m 12187272 [C8 (Z_to_bv 64 v7)] ->
  rw_cells asegs m 12187264 [C8 (Z_to_bv 64 v6)] ->
  rw_cells asegs m 12187224 [C8 (Z_to_bv 64 v5)] ->
  rw_cells asegs m 12187240 [C8 (Z_to_bv 64 v4)] ->
  rw_cells asegs m 12187184 [C8 (Z_to_bv 64 v3)] ->
  rw_cells asegs m 12187008 [C8 (Z_to_bv 64 v1)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m 12187320 [C8 g21] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  0 <= v15 < 2 ^ 64 ->
  0 <= v16 < 2 ^ 64 ->
  0 <= v17 < 2 ^ 64 ->
  0 <= v18 < 2 ^ 64 ->
  0 <= v19 < 2 ^ 64 ->
  0 <= v20 < 2 ^ 64 ->
  0 <= v22 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m 12187008 328 ->
  12187008 mod 8 = 0 ->
  ro_cells asegs m 2148974256 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974278 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974285 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974283 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974288 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974289 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974290 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974291 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974279 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974277 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974280 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974281 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974282 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974286 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974284 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974292 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974293 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974294 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974287 [C1 (Z_to_bv 8 0)] ->
  ro_cells asegs m 2148974295 [C1 (Z_to_bv 8 0)] ->
  mem_inv asegs m ->
  evt asegs (context_init_s22_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra22 u0_22 u1_22 u2_22 b1_22 b2_22 b3_22 b4_22 b5_22 b6_22 b7_22 u3_22 u4_22 u5_22 u6_22 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v22 j1 g21 F22 fc22 lo m)
    (MS (mkR ra22 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_22 u1_22 u2_22 sp (Z_to_bv 64 12187008) (Z_to_bv 64 v22) b1_22 b2_22 b3_22 b4_22 b5_22 b6_22 b7_22 (Z_to_bv 64 2148974256) (Z_to_bv 64 2147450880) s4 s5 s6 s7 s8 s9 s10 s11 u3_22 u4_22 u5_22 u6_22)
        F22 (Z_to_bv 64 0x1f7250) fc22 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP G13 G20 G19 G18 G10 G12 G8 G7 G6 G3 G5 G17 G16 G15 G14 G9 G11 G4 G2 FR G21 G1 Hv1 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 Hv16 Hv17 Hv18 Hv19 Hv20 Hv22 UT GACCbd1e00 GPALbd1e00 GSH801723c0 GSH801723d6 GSH801723dd GSH801723db GSH801723e0 GSH801723e1 GSH801723e2 GSH801723e3 GSH801723d7 GSH801723d5 GSH801723d8 GSH801723d9 GSH801723da GSH801723de GSH801723dc GSH801723e4 GSH801723e5 GSH801723e6 GSH801723df GSH801723e7 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(0xb9f6b8, 0xb9f6c0); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 9 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold context_init_s22_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.
