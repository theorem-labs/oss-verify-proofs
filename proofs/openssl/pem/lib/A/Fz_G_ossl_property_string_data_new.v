(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Th_mutex Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks.
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

Definition e_ossl_property_string_data_new : Z := 0x20bcf4.
Definition SITE_ossl_property_string_data_new_1 : Z := 0x20bd48.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_2 : Z := 0x20bd54.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_3 : Z := 0x20bd80.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_4 : Z := 0x20bda4.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_5 : Z := 0x20bdd0.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_6 : Z := 0x20bdf4.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_7 : Z := 0x20be10.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_8 : Z := 0x20be1c.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_9 : Z := 0x20be28.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_10 : Z := 0x20be34.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_11 : Z := 0x20be50.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_12 : Z := 0x20be5c.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_13 : Z := 0x20be68.     (* [comment removed for export] *)
Definition SITE_ossl_property_string_data_new_14 : Z := 0x20be74.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j1 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145608) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 48) (Z_to_bv 64 309632) (Z_to_bv 64 98) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2080748) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20bcf4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 96%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep.
  do 11 zstore.
  do 9 zstep.
  unfold ossl_property_string_data_new_s0_post. apply evt_done. do 2 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145620) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2055740) fc1 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 48 (repeat (Z_to_bv 8 0) 48)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 j1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x20bd48) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 UT HBr1 ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  do 2 zstep.
  unfold ossl_property_string_data_new_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145664) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 2146120) (Z_to_bv 64 2146188) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2096816) fc2 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 48 (repeat (Z_to_bv 8 0) 48)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0))) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j1 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x20bd54) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR2_1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstep.
  zstore.
  do 5 zstep.
  unfold ossl_property_string_data_new_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145700) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 2148220) (Z_to_bv 64 2148252) (Z_to_bv 64 2148284) (Z_to_bv 64 2148316) b5_3 b6_3 b7_3 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2096640) fc3 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s3_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j1 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x20bd80) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv3 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 9 zstep.
  unfold ossl_property_string_data_new_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145744) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 2146120) (Z_to_bv 64 2146188) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 2096816) fc4 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s4_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v4 j1 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x20bda4) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 5 zstep.
  unfold ossl_property_string_data_new_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v4 v5 : Z) (j1 : list byte) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145780) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 2148220) (Z_to_bv 64 2148252) (Z_to_bv 64 2148284) (Z_to_bv 64 2148316) b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 2096640) fc5 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s5_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v4 v5 : Z) (j1 : list byte) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); CB 32 (repeat (Z_to_bv 8 0) 32)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v4 v5 j1 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x20bdd0) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv5 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 9 zstep.
  unfold ossl_property_string_data_new_s5_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v4 v6 : Z) (j1 : list byte) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145808) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 2073476) fc6 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s6_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v4 v6 : Z) (j1 : list byte) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); CB 32 (repeat (Z_to_bv 8 0) 32)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v4 v6 j1 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x20bdf4) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep.
  unfold ossl_property_string_data_new_s6_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v4 v6 v7 : Z) (j1 : list byte) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145820) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2146284) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
            F7 (Z_to_bv 64 2075068) fc7 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s7_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v4 v6 v7 : Z) (j1 : list byte) (F7 : bvmap 5 word) (fc7 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v4 v6 v7 j1 F7 fc7 lo m)
    (MS (mkR ra7 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
        F7 (Z_to_bv 64 0x20be10) fc7 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv7 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s7_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s8_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v2 v4 v6 v8 : Z) (j1 : list byte) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145832) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) (Z_to_bv 64 2146328) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
            F8 (Z_to_bv 64 2075148) fc8 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s8_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v2 v4 v6 v8 : Z) (j1 : list byte) (F8 : bvmap 5 word) (fc8 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v4 v6 v8 j1 F8 fc8 lo m)
    (MS (mkR ra8 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
        F8 (Z_to_bv 64 0x20be1c) fc8 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv8 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s8_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s9_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v2 v4 v6 v9 : Z) (j1 : list byte) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145844) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) (Z_to_bv 64 2146368) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
            F9 (Z_to_bv 64 2074988) fc9 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s9_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v2 v4 v6 v9 : Z) (j1 : list byte) (F9 : bvmap 5 word) (fc9 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s9_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v4 v6 v9 j1 F9 fc9 lo m)
    (MS (mkR ra9 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
        F9 (Z_to_bv 64 0x20be28) fc9 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv9 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s9_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s10_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v2 v4 v6 v10 : Z) (j1 : list byte) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145872) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 0) b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 2073476) fc10 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s10_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v2 v4 v6 v10 : Z) (j1 : list byte) (F10 : bvmap 5 word) (fc10 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s10_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v4 v6 v10 j1 F10 fc10 lo m)
    (MS (mkR ra10 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
        F10 (Z_to_bv 64 0x20be34) fc10 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv10 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep.
  unfold ossl_property_string_data_new_s10_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s11_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v2 v4 v6 v10 v11 : Z) (j1 : list byte) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145884) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 2146284) b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (Z_to_bv 64 2075068) fc11 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s11_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v2 v4 v6 v10 v11 : Z) (j1 : list byte) (F11 : bvmap 5 word) (fc11 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s11_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v4 v6 v10 v11 j1 F11 fc11 lo m)
    (MS (mkR ra11 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_11 u4_11 u5_11 u6_11)
        F11 (Z_to_bv 64 0x20be50) fc11 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv10 Hv11 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s11_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s12_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v2 v4 v6 v10 v12 : Z) (j1 : list byte) (F12 : bvmap 5 word) (fc12 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145896) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) (Z_to_bv 64 2146328) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_12 u4_12 u5_12 u6_12)
            F12 (Z_to_bv 64 2075148) fc12 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s12_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v2 v4 v6 v10 v12 : Z) (j1 : list byte) (F12 : bvmap 5 word) (fc12 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v12 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s12_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v2 v4 v6 v10 v12 j1 F12 fc12 lo m)
    (MS (mkR ra12 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_12 u4_12 u5_12 u6_12)
        F12 (Z_to_bv 64 0x20be5c) fc12 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv10 Hv12 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s12_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s13_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v2 v4 v6 v10 v13 : Z) (j1 : list byte) (F13 : bvmap 5 word) (fc13 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2145908) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) (Z_to_bv 64 2146368) b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_13 u4_13 u5_13 u6_13)
            F13 (Z_to_bv 64 2074988) fc13 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ossl_property_string_data_new_s13_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v2 v4 v6 v10 v13 : Z) (j1 : list byte) (F13 : bvmap 5 word) (fc13 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v13 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s13_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v2 v4 v6 v10 v13 j1 F13 fc13 lo m)
    (MS (mkR ra13 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_13 u4_13 u5_13 u6_13)
        F13 (Z_to_bv 64 0x20be68) fc13 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv10 Hv13 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_property_string_data_new_s13_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s14_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v2 v4 v6 v10 v14 : Z) (j1 : list byte) (F14 : bvmap 5 word) (fc14 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_14 u1_14 u2_14 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
            F14 (ret_pc ra) fc14 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v14)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_property_string_data_new_s14_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v2 v4 v6 v10 v14 : Z) (j1 : list byte) (F14 : bvmap 5 word) (fc14 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -96) -> lo <= (bv_unsigned sp + -96) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v14 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 48 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 48 <= 2 ^ 47 ->
  v1 + 48 <= lo ->
  (bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0)) = false ->
  (bv_eqb (Z_to_bv 64 v10) (Z_to_bv 64 0)) = false ->
  (bv_eqb (Z_to_bv 64 v14) (Z_to_bv 64 0)) = false ->
  (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0)) = false ->
  (negb (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0))) = true ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s14_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v2 v4 v6 v10 v14 j1 F14 fc14 lo m)
    (MS (mkR ra14 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1) (Z_to_bv 64 v14) b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_14 u4_14 u5_14 u6_14)
        F14 (Z_to_bv 64 0x20be74) fc14 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 Hv6 Hv10 Hv14 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR14_3 BR14_5 BR14_6 BR14_8 BR14_10 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR14_3.
  zstep.
  zstep. wg_F.
  zstep.
  zstep. wg_raw BR14_5.
  zstep. wg_raw BR14_6.
  zstep.
  zstep. wg_F.
  zstep.
  zstep. wg_raw BR14_8.
  zstep.
  zstep. wg_F.
  zstep.
  zstep. wg_raw BR14_10.
  do 14 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_property_string_data_new_s14_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_property_string_data_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_zalloc : crypto_zalloc_env_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.
Hypothesis C_OPENSSL_LH_new : OPENSSL_LH_new_stmt RT.
Hypothesis C_OPENSSL_LH_set_thunks : OPENSSL_LH_set_thunks_keep_stmt RT.
Hypothesis C_OPENSSL_sk_new_null : OPENSSL_sk_new_null_stmt RT.
Hypothesis C_OPENSSL_sk_set_cmp_thunks : OPENSSL_sk_set_cmp_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_copy_thunks : OPENSSL_sk_set_copy_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_thunks : OPENSSL_sk_set_thunks_stmt RT.

Definition ossl_property_string_data_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x260 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_property_string_data_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_property_string_data_new_1, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_2, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_3, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_4, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_5, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_6, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_7, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_8, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_9, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_10, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_11, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_12, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_13, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_14, e_ossl_property_string_data_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null)]
                      [(SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc); (SITE_ossl_property_string_data_new_2, e_lock_new); (SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_4, e_OPENSSL_LH_set_thunks); (SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_6, e_OPENSSL_LH_set_thunks); (SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_8, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_property_string_data_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_property_string_data_new_10, e_OPENSSL_sk_set_thunks); (SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_12, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_property_string_data_new_13, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_property_string_data_new_14, e_OPENSSL_sk_set_thunks); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 8 <= LIVE_MAX -> mcost 48 + 1 + mcost 104 + mcost 128 + mcost 104 + mcost 128 + mcost 56 + mcost 56 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_property_string_data_new m)))
    (fun c => exists (Σ' : rts RT) (q1 q2 q3 q4 q5 q6 q7 q8 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 48
           /\ acc asegs m' q1 48
           /\ wr_at asegs m' q2 40
           /\ acc asegs m' q2 40
           /\ wr_at asegs m' q3 104
           /\ acc asegs m' q3 104
           /\ wr_at asegs m' q4 128
           /\ acc asegs m' q4 128
           /\ wr_at asegs m' q5 104
           /\ acc asegs m' q5 104
           /\ wr_at asegs m' q6 128
           /\ acc asegs m' q6 128
           /\ wr_at asegs m' q7 56
           /\ acc asegs m' q7 56
           /\ wr_at asegs m' q8 56
           /\ acc asegs m' q8 56
           /\ rw_cells asegs m' q1 [C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 q7); C8 (Z_to_bv 64 q8)]
           /\ rw_cells asegs m' q2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q4 [CB 128 (repeat (Z_to_bv 8 0) 128)]
           /\ rw_cells asegs m' q3 [C8 (Z_to_bv 64 q4); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]
           /\ rw_cells asegs m' q6 [CB 128 (repeat (Z_to_bv 8 0) 128)]
           /\ rw_cells asegs m' q5 [C8 (Z_to_bv 64 q6); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]
           /\ rw_cells asegs m' q7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]
           /\ rw_cells asegs m' q8 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) c
       /\ rt_live RT Σ' = (q8, 56) :: (q7, 56) :: (q6, 128) :: (q5, 104) :: (q4, 128) :: (q3, 104) :: (q2, 40) :: (q1, 48) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 48 + 1 + mcost 104 + mcost 128 + mcost 104 + mcost 128 + mcost 56 + mcost 56) /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 48 < USTACK_TOP /\ 0 < q2 /\ q2 mod 16 = 0 /\ q2 + 40 < USTACK_TOP /\ 0 < q3 /\ q3 mod 16 = 0 /\ q3 + 104 < USTACK_TOP /\ 0 < q4 /\ q4 mod 16 = 0 /\ q4 + 128 < USTACK_TOP /\ 0 < q5 /\ q5 mod 16 = 0 /\ q5 + 104 < USTACK_TOP /\ 0 < q6 /\ q6 mod 16 = 0 /\ q6 + 128 < USTACK_TOP /\ 0 < q7 /\ q7 mod 16 = 0 /\ q7 + 56 < USTACK_TOP /\ 0 < q8 /\ q8 mod 16 = 0 /\ q8 + 56 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_property_string_data_new_cps : ossl_property_string_data_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 96 /\ 0x10007fff8000 < usp - 96 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-96) EU1.
  assert (WHLO : lo <= usp - 96) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (wg_mcost_nonneg 104) as MC_104.
  pose proof (wg_mcost_nonneg 128) as MC_128.
  pose proof (wg_mcost_nonneg 48) as MC_48.
  pose proof (wg_mcost_nonneg 56) as MC_56.
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST WHLO WHIMG WHTOP UT SHC MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j1 & m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1', H1_0.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV1.
  clear H1_1 ENV.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_CRYPTO_zalloc SITE_ossl_property_string_data_new_1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTX
              (proj1 CGH (SITE_ossl_property_string_data_new_1, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc) ltac:(wp_in_lit)) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H1_0))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CRYPTO_zalloc Σ PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_1) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 48) (Z_to_bv 64 309632) (Z_to_bv 64 98) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 48 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { clear - EU1 ST1 LOW SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_1) by (unfold SITE_ossl_property_string_data_new_1; clear; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { clear - Hlen; lia. }
  { clear - Hcr MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV2 & FRS2 & SP2 & CR2 & P0_v1 & P16_v1 & PU_v1 & CG2).
  wp_box1 PU_v1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & G1_ENVp & G1_WR & G1_ACC & G1_ZER) & Hc2'). clear Hc2.
  destruct RS2 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & F1 & fc1 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_property_string_data_new_1) in Hc2' by (unfold SITE_ossl_property_string_data_new_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; exact (AGc2 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AGu2) as UWF2.
  cl_keep H1_0 AGc2 WM2 KF1.
  clear H1_0 AGc2 CTXc1 UWCc1.
  pose proof SP2 as SPc2. pose proof CG2 as CGc2.
  assert (LOW2 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SPc2; exact LOW).
  assert (LEN2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (rewrite LV2; clear; cbn [length]; lia).
  assert (LENc2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (clear - LEN2; lia). wp_box1 CR2.
  assert (Hfr2 : (length (rt_frames RT Σ1) < FRAMES_MAX)%nat) by (rewrite FRS2; exact Hfr).
  assert (CTXb2 : cg_ctx (rt_cg RT Σ1) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc2; exact CTX).
  assert (CGH2 : cg_has (rt_cg RT Σ1) _ _) by (rewrite CGc2; exact CGH).
  assert (INP_v1_2 : In (v1, 48) (rt_live RT Σ1)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 v1 48 ART2 INP_v1_2) as (_ & PHI_v1 & _). rewrite SPc2 in PHI_v1.
  pose proof (afp_live_mem RT GOBJ AFP Σ1 m2 v1 48 ART2 INP_v1_2 ltac:(clear; lia)) as (_ & PT_v1).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 48 ART2 INP_v1_2 ltac:(clear; lia)) as PHH_v1.
  pose proof (wg_mod16_8 _ P16_v1) as PAL_v1. assert (PR64_v1 : 0 <= v1 < 2 ^ 64) by (first [clear - PHH_v1 PT_v1; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v1 : v1 + 48 <= lo) by (first [clear - PHI_v1 LOW2; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v1. wp_box1 PAL_v1. wp_box1 PR64_v1.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ1 m2 v1 48 ART2 INP_v1_2) as (WR_v1_3 & ACC_v1_3).
  pose proof (wp_cells_congr asegs m2 v1 [CB (Z.to_nat 48) (repeat (Z_to_bv 8 0) (Z.to_nat 48))] [CB 48 (repeat (Z_to_bv 8 0) 48)] ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m2 v1 48 G1_ZER WR_v1_3 ltac:(lia))) as HB_v1_3.
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 j1 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 SHC2 PR64_v1 UT2 HB_v1_3 ACC_v1_3 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & H3_2 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_1.
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 96 [] ART2 ltac:(rewrite SPc2; clear - NUM; lia) ltac:(clear - NUM; lia) MU3); [|exact WM3].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary G1_ENVp MU3 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV3.
  clear KF1 H3_2 G1_ENVp.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ossl_property_string_data_new e_lock_new SITE_ossl_property_string_data_new_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTXb2
              (proj1 CGH2 (SITE_ossl_property_string_data_new_2, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH2 (SITE_ossl_property_string_data_new_2, e_lock_new) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H3_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_lock_new Σ1 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_2) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART3 MI3).
  { clear - EU1 ST3 LOW2 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST3 LOW2 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_2) by (unfold SITE_ossl_property_string_data_new_2; clear; lia). exact CTXc3. }
  { exact UWCc3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH2); vm_compute; reflexivity. }
  { first [exact Hfr2 | clear - Hfr2; lia]. }
  { clear - Hlen LENc2; lia. }
  { clear - Hcr CR2 MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_MX & G2_ACC) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_property_string_data_new_2) in Hc4' by (unfold SITE_ossl_property_string_data_new_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; cbv beta in Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  assert (KF2 : rw_cells asegs m4 v1 [CB 48 (repeat (Z_to_bv 8 0) 48)]) by (apply (wg_keep_live _ _ _ _ m3 m4 v1 48 _ _ H3_0 PRES4 WM4 INP_v1_2); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H3_1 AGc4 WM4 KF3.
  clear H3_0 H3_1 AGc4 CTXc3 UWCc3.
  assert (SPc4 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP4; exact SPc2).
  assert (CGc4 : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite CG4; exact CGc2).
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ1)) + 1) by (rewrite LV4; clear; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 2) by (clear - LEN4 LENc2; lia). clear LENc2. wp_box1 LEN2. wp_box1 CR4.
  assert (Hfr4 : (length (rt_frames RT Σ2) < FRAMES_MAX)%nat) by (rewrite FRS4; exact Hfr2).
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v1_4 : In (v1, 48) (rt_live RT Σ2)) by (rewrite LV4; do 1 right; exact INP_v1_2).
  assert (INP_v2_4 : In (v2, 40) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 40 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(clear; lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(clear; lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (first [clear - PHH_v2 PT_v2; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v2 : v2 + 40 <= lo) by (first [clear - PHI_v2 LOW4; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (af_acc_live RT AF Σ2 m4 v1 48 ART4 INP_v1_4) as (WR_v1_5 & ACC_v1_5).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j1 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF2 KF3 SHC4 PR64_v1 PR64_v2 UT4 ACC_v1_5 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & H5_2 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5', H5_1.
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 96 [(v1, v1 + 48)] ART4 ltac:(rewrite SPc4; clear - NUM; lia) ltac:(clear - NUM; lia) MU5); [|exact WM5].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 48; split; [exact INP_v1_4 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF4 : rw_cells asegs m5 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 48 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m4 m5 _ _ G2_MX MU5 WM5); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia])) as ENV5.
  clear KF2 KF3 G2_MX H5_2 G2_ENVp.
  assert (AGs5 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AGs5) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ2) e_ossl_property_string_data_new e_OPENSSL_LH_new SITE_ossl_property_string_data_new_3 m5 m5 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTXb4
              (proj1 CGH4 (SITE_ossl_property_string_data_new_3, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH4 (SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new) ltac:(wp_in_lit)) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H5_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_new Σ2 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_3) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 2146120) (Z_to_bv 64 2146188) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2
           F2 fc2 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART5 MI5).
  { clear - EU1 ST5 LOW4 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_3) by (unfold SITE_ossl_property_string_data_new_3; clear; lia). exact CTXc5. }
  { exact UWCc5. }
  { apply (cg_has_weaken _ _ _ _ _ CGH4); vm_compute; reflexivity. }
  { clear - Hlen LENc4; lia. }
  { clear - Hcr CR2 CR4 MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV5. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & v3 & w3_2 & Hc6 & LV6 & FRS6 & SP6 & CR6 & P0_v3 & P16_v3 & PU_v3 & P0_w3_2 & P16_w3_2 & PU_w3_2 & CG6).
  wp_box1 PU_v3. wp_box1 PU_w3_2.
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & G3_ENVp & G3_WR_v1 & G3_ACC_v1 & G3_WR_v2 & G3_ACC_v2 & G3_CL0 & G3_CL2) & Hc6'). clear Hc6.
  destruct RS6 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & F3 & fc3 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ossl_property_string_data_new_3) in Hc6' by (unfold SITE_ossl_property_string_data_new_3; clear; first [reflexivity | lia]).
  assert (AGc6 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu6 : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6) by (intros a Ha; cbv beta in Ha; exact (AGc6 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AGu6) as UWF6.
  assert (KF5 : rw_cells asegs m6 v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]) by (apply (wg_keep_live _ _ _ _ m5 m6 v1 48 _ _ H5_0 PRES6 WM6 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H5_1 AGc6 WM6 KF6.
  assert (KF7 : rw_cells asegs m6 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m5 m6 v2 40 _ _ KF4 PRES6 WM6 INP_v2_4); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H5_0 H5_1 KF4 AGc6 CTXc5 UWCc5.
  assert (SPc6 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite SP6; exact SPc4).
  assert (CGc6 : rt_cg RT Σ3 = rt_cg RT Σ) by (rewrite CG6; exact CGc4).
  assert (LOW6 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SPc6; exact LOW).
  assert (LEN6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ2)) + 2) by (rewrite LV6; clear; cbn [length]; lia).
  assert (LENc6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ)) + 4) by (clear - LEN6 LENc4; lia). clear LENc4. wp_box1 LEN4. wp_box1 CR6.
  assert (Hfr6 : (length (rt_frames RT Σ3) < FRAMES_MAX)%nat) by (rewrite FRS6; exact Hfr4).
  assert (CTXb6 : cg_ctx (rt_cg RT Σ3) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc6; exact CTX).
  assert (CGH6 : cg_has (rt_cg RT Σ3) _ _) by (rewrite CGc6; exact CGH).
  assert (INP_v1_6 : In (v1, 48) (rt_live RT Σ3)) by (rewrite LV6; do 2 right; exact INP_v1_4).
  assert (INP_v2_6 : In (v2, 40) (rt_live RT Σ3)) by (rewrite LV6; do 2 right; exact INP_v2_4).
  assert (INP_v3_6 : In (v3, 104) (rt_live RT Σ3)) by (rewrite LV6; do 1 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ3 m6 v3 104 ART6 INP_v3_6) as (_ & PHI_v3 & _). rewrite SPc6 in PHI_v3.
  pose proof (afp_live_mem RT GOBJ AFP Σ3 m6 v3 104 ART6 INP_v3_6 ltac:(clear; lia)) as (_ & PT_v3).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 v3 104 ART6 INP_v3_6 ltac:(clear; lia)) as PHH_v3.
  pose proof (wg_mod16_8 _ P16_v3) as PAL_v3. assert (PR64_v3 : 0 <= v3 < 2 ^ 64) by (first [clear - PHH_v3 PT_v3; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v3 : v3 + 104 <= lo) by (first [clear - PHI_v3 LOW6; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v3. wp_box1 PAL_v3. wp_box1 PR64_v3.
  assert (INP_w3_2_6 : In (w3_2, 128) (rt_live RT Σ3)) by (rewrite LV6; left; reflexivity).
  pose proof (af_live_range RT AF Σ3 m6 w3_2 128 ART6 INP_w3_2_6) as (_ & PHI_w3_2 & _). rewrite SPc6 in PHI_w3_2.
  pose proof (afp_live_mem RT GOBJ AFP Σ3 m6 w3_2 128 ART6 INP_w3_2_6 ltac:(clear; lia)) as (_ & PT_w3_2).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 w3_2 128 ART6 INP_w3_2_6 ltac:(clear; lia)) as PHH_w3_2.
  pose proof (wg_mod16_8 _ P16_w3_2) as PAL_w3_2. assert (PR64_w3_2 : 0 <= w3_2 < 2 ^ 64) by (first [clear - PHH_w3_2 PT_w3_2; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_w3_2 : w3_2 + 128 <= lo) by (first [clear - PHI_w3_2 LOW6; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_w3_2. wp_box1 PAL_w3_2. wp_box1 PR64_w3_2.
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_3) u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j1 F3 fc3 m6 lo
                ST6 WHLO WHIMG WHTOP KF5 KF6 SHC6 PR64_v1 PR64_v2 PR64_v3 UT6 MI6) as W7.
  cl_lift W7 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & H7_0 & H7_1 & H7_2 & ST7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7', H7_1.
  assert (ART7 : ART RT Σ3 m7).
  { apply (wg_seg_ART RT AF Σ3 m6 m7 usp 96 [] ART6 ltac:(rewrite SPc6; clear - NUM; lia) ltac:(clear - NUM; lia) MU7); [|exact WM7].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF8 : rw_cells asegs m7 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m6 m7 _ _ KF7 MU7 WM7); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF9 : rw_cells asegs m7 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); CB 32 (repeat (Z_to_bv 8 0) 32); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL0 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF10 : rw_cells asegs m7 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL2 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m6 m7 _ canary G3_ENVp MU7 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV7.
  clear KF5 KF6 KF7 G3_CL0 G3_CL2 H7_2 G3_ENVp.
  assert (AGs7 : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7) by (intros a Ha; apply MU7; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AGs7) as UWF7.
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_set_thunks Σ3 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_4) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 2148220) (Z_to_bv 64 2148252) (Z_to_bv 64 2148284) (Z_to_bv 64 2148316) b5_3 b6_3 b7_3 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
           F3 fc3 m7 lo v3 (Z_to_bv 64 w3_2) (Z_to_bv 64 2146188) (Z_to_bv 64 2146120) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256) FDO MST eq_refl eq_refl ART7 MI7).
  { clear - EU1 ST7 LOW6 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST7 LOW6 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v3_6. }
  { exact P16_v3. }
  { exact KF9. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & G4_CL0) & Hc8'). clear Hc8.
  destruct RS8 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & F4 & fc4 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ossl_property_string_data_new_4) in Hc8' by (unfold SITE_ossl_property_string_data_new_4; clear; first [reflexivity | lia]).
  assert (AGc8 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES8; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; cbv beta in Ha; exact (AGc8 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AGu8) as UWF8.
  assert (KF11 : rw_cells asegs m8 v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_live _ _ _ _ m7 m8 v1 48 _ _ H7_0 PRES8 WM8 INP_v1_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H7_1 AGc8 WM8 KF12.
  assert (KF13 : rw_cells asegs m8 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v2 40 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_live _ _ _ _ m7 m8 v2 40 _ _ KF8 PRES8 WM8 INP_v2_6); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF15 : rw_cells asegs m8 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v3 104 ART6 LV6 ltac:(cbn [app In]; left; reflexivity)) as DJ_w3_2_v3; apply (wg_keep_live _ _ _ _ m7 m8 w3_2 128 _ _ KF10 PRES8 WM8 INP_w3_2_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v3 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H7_0 H7_1 KF8 KF9 KF10 AGc8.
  destruct (af_client_consts RT AF Σ3 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  assert (ENV8 : cl_env m8 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v3 + 24, v3 + 56)]) by cl_fp_lia. apply (cl_env_agree m7 m8 _ _ ENV7). intros a Ha. apply PRES8; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ3 m8 v1 48 ART8 INP_v1_6) as (WR_v1_9 & ACC_v1_9).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s4_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_4) u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v3 j1 F4 fc4 m8 lo
                ST8 WHLO WHIMG WHTOP KF11 KF12 SHC8 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) UT8 ACC_v1_9 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI8) as W9.
  cl_lift W9 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & H9_0 & H9_1 & H9_2 & ST9) & Hc9'). clear Hc9.
  fold usp in MU9, ST9, Hc9', H9_1.
  assert (ART9 : ART RT Σ3 m9).
  { apply (wg_seg_ART RT AF Σ3 m8 m9 usp 96 [(v1, v1 + 48)] ART8 ltac:(rewrite SPc6; clear - NUM; lia) ltac:(clear - NUM; lia) MU9); [|exact WM9].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 48; split; [exact INP_v1_6 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF16 : rw_cells asegs m9 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 48 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m8 m9 _ _ KF13 MU9 WM9); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF17 : rw_cells asegs m9 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_w3_2_v1; apply (wg_keep_seg _ m8 m9 _ _ KF15 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v1 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF18 : rw_cells asegs m9 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m8 m9 _ _ G4_CL0 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia])) as ENV9.
  clear KF11 KF12 KF13 KF15 G4_CL0 H9_2 ENV8.
  assert (AGs9 : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9) by (intros a Ha; apply MU9; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AGs9) as UWF9.
  destruct (cl_chain_call (rt_cg RT Σ3) e_ossl_property_string_data_new e_OPENSSL_LH_new SITE_ossl_property_string_data_new_5 m9 m9 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTXb6
              (proj1 CGH6 (SITE_ossl_property_string_data_new_5, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH6 (SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new) ltac:(wp_in_lit)) UWF9 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m9 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H9_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc9 & UWCc9).
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_new Σ3 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_5) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 2146120) (Z_to_bv 64 2146188) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4
           F4 fc4 m9 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART9 MI9).
  { clear - EU1 ST9 LOW6 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST9 LOW6 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_5) by (unfold SITE_ossl_property_string_data_new_5; clear; lia). exact CTXc9. }
  { exact UWCc9. }
  { apply (cg_has_weaken _ _ _ _ _ CGH6); vm_compute; reflexivity. }
  { clear - Hlen LENc6; lia. }
  { clear - Hcr CR2 CR4 CR6 MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV9. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc9'. }
  clear Hc9'. intros c10 (Σ5 & v5 & w5_2 & Hc10 & LV10 & FRS10 & SP10 & CR10 & P0_v5 & P16_v5 & PU_v5 & P0_w5_2 & P16_w5_2 & PU_w5_2 & CG10).
  wp_box1 PU_v5. wp_box1 PU_w5_2.
  destruct (ASTA_unpack RT Σ5 _ _ c10 Hc10) as (ms10 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & G5_ENVp & G5_WR_v1 & G5_ACC_v1 & G5_WR_v2 & G5_ACC_v2 & G5_CL0 & G5_CL2) & Hc10'). clear Hc10.
  destruct RS10 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & F5 & fc5 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_ossl_property_string_data_new_5) in Hc10' by (unfold SITE_ossl_property_string_data_new_5; clear; first [reflexivity | lia]).
  assert (AGc10 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES10; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu10 : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10) by (intros a Ha; cbv beta in Ha; exact (AGc10 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AGu10) as UWF10.
  assert (KF19 : rw_cells asegs m10 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m9 m10 v1 48 _ _ H9_0 PRES10 WM10 INP_v1_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H9_1 AGc10 WM10 KF20.
  assert (KF21 : rw_cells asegs m10 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m9 m10 v2 40 _ _ KF16 PRES10 WM10 INP_v2_6); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF22 : rw_cells asegs m10 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_live _ _ _ _ m9 m10 w3_2 128 _ _ KF17 PRES10 WM10 INP_w3_2_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF23 : rw_cells asegs m10 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_live _ _ _ _ m9 m10 v3 104 _ _ KF18 PRES10 WM10 INP_v3_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H9_0 H9_1 KF16 KF17 KF18 AGc10 CTXc9 UWCc9.
  assert (SPc10 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP10; exact SPc6).
  assert (CGc10 : rt_cg RT Σ5 = rt_cg RT Σ) by (rewrite CG10; exact CGc6).
  assert (LOW10 : rt_sp0 RT Σ5 - STACK_WIN <= lo) by (rewrite SPc10; exact LOW).
  assert (LEN10 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ3)) + 2) by (rewrite LV10; clear; cbn [length]; lia).
  assert (LENc10 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ)) + 6) by (clear - LEN10 LENc6; lia). clear LENc6. wp_box1 LEN6. wp_box1 CR10.
  assert (Hfr10 : (length (rt_frames RT Σ5) < FRAMES_MAX)%nat) by (rewrite FRS10; exact Hfr6).
  assert (CTXb10 : cg_ctx (rt_cg RT Σ5) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc10; exact CTX).
  assert (CGH10 : cg_has (rt_cg RT Σ5) _ _) by (rewrite CGc10; exact CGH).
  assert (INP_v1_10 : In (v1, 48) (rt_live RT Σ5)) by (rewrite LV10; do 2 right; exact INP_v1_6).
  assert (INP_v2_10 : In (v2, 40) (rt_live RT Σ5)) by (rewrite LV10; do 2 right; exact INP_v2_6).
  assert (INP_v3_10 : In (v3, 104) (rt_live RT Σ5)) by (rewrite LV10; do 2 right; exact INP_v3_6).
  assert (INP_w3_2_10 : In (w3_2, 128) (rt_live RT Σ5)) by (rewrite LV10; do 2 right; exact INP_w3_2_6).
  assert (INP_v5_10 : In (v5, 104) (rt_live RT Σ5)) by (rewrite LV10; do 1 right; left; reflexivity).
  pose proof (af_live_range RT AF Σ5 m10 v5 104 ART10 INP_v5_10) as (_ & PHI_v5 & _). rewrite SPc10 in PHI_v5.
  pose proof (afp_live_mem RT GOBJ AFP Σ5 m10 v5 104 ART10 INP_v5_10 ltac:(clear; lia)) as (_ & PT_v5).
  pose proof (afp_live_hi RT GOBJ AFP Σ5 m10 v5 104 ART10 INP_v5_10 ltac:(clear; lia)) as PHH_v5.
  pose proof (wg_mod16_8 _ P16_v5) as PAL_v5. assert (PR64_v5 : 0 <= v5 < 2 ^ 64) by (first [clear - PHH_v5 PT_v5; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v5 : v5 + 104 <= lo) by (first [clear - PHI_v5 LOW10; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v5. wp_box1 PAL_v5. wp_box1 PR64_v5.
  assert (INP_w5_2_10 : In (w5_2, 128) (rt_live RT Σ5)) by (rewrite LV10; left; reflexivity).
  pose proof (af_live_range RT AF Σ5 m10 w5_2 128 ART10 INP_w5_2_10) as (_ & PHI_w5_2 & _). rewrite SPc10 in PHI_w5_2.
  pose proof (afp_live_mem RT GOBJ AFP Σ5 m10 w5_2 128 ART10 INP_w5_2_10 ltac:(clear; lia)) as (_ & PT_w5_2).
  pose proof (afp_live_hi RT GOBJ AFP Σ5 m10 w5_2 128 ART10 INP_w5_2_10 ltac:(clear; lia)) as PHH_w5_2.
  pose proof (wg_mod16_8 _ P16_w5_2) as PAL_w5_2. assert (PR64_w5_2 : 0 <= w5_2 < 2 ^ 64) by (first [clear - PHH_w5_2 PT_w5_2; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_w5_2 : w5_2 + 128 <= lo) by (first [clear - PHI_w5_2 LOW10; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_w5_2. wp_box1 PAL_w5_2. wp_box1 PR64_w5_2.
  destruct (af_client_consts RT AF Σ5 m10 ART10) as (_ & SHC10 & _ & _ & UT10).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s5_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_5) u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v3 v5 j1 F5 fc5 m10 lo
                ST10 WHLO WHIMG WHTOP KF19 KF20 SHC10 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) PR64_v5 UT10 MI10) as W11.
  cl_lift W11 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ5 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & H11_0 & H11_1 & H11_2 & ST11) & Hc11'). clear Hc11.
  fold usp in MU11, ST11, Hc11', H11_1.
  assert (ART11 : ART RT Σ5 m11).
  { apply (wg_seg_ART RT AF Σ5 m10 m11 usp 96 [] ART10 ltac:(rewrite SPc10; clear - NUM; lia) ltac:(clear - NUM; lia) MU11); [|exact WM11].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF24 : rw_cells asegs m11 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m10 m11 _ _ KF21 MU11 WM11); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF25 : rw_cells asegs m11 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m10 m11 _ _ KF22 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF26 : rw_cells asegs m11 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m10 m11 _ _ KF23 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF27 : rw_cells asegs m11 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); CB 32 (repeat (Z_to_bv 8 0) 32); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_seg _ m10 m11 _ _ G5_CL0 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF28 : rw_cells asegs m11 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m10 m11 _ _ G5_CL2 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m10 m11 _ canary G5_ENVp MU11 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV11.
  clear KF19 KF20 KF21 KF22 KF23 G5_CL0 G5_CL2 H11_2 G5_ENVp.
  assert (AGs11 : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11) by (intros a Ha; apply MU11; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AGs11) as UWF11.
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_set_thunks Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_6) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 2148220) (Z_to_bv 64 2148252) (Z_to_bv 64 2148284) (Z_to_bv 64 2148316) b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5
           F5 fc5 m11 lo v5 (Z_to_bv 64 w5_2) (Z_to_bv 64 2146188) (Z_to_bv 64 2146120) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256) FDO MST eq_refl eq_refl ART11 MI11).
  { clear - EU1 ST11 LOW10 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST11 LOW10 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v5_10. }
  { exact P16_v5. }
  { exact KF27. }
  { exact Hc11'. }
  clear Hc11'. intros c12 Hc12.
  destruct (ASTA_unpack RT Σ5 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & G6_CL0) & Hc12'). clear Hc12.
  destruct RS12 as (u0_6 & u1_6 & u2_6 & b1_6 & b2_6 & b3_6 & b4_6 & b5_6 & b6_6 & b7_6 & u3_6 & u4_6 & u5_6 & u6_6 & F6 & fc6 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_ossl_property_string_data_new_6) in Hc12' by (unfold SITE_ossl_property_string_data_new_6; clear; first [reflexivity | lia]).
  assert (AGc12 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m11 m12).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES12; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu12 : agree_on (fun x => usp <= x < USTACK_TOP) m11 m12) by (intros a Ha; cbv beta in Ha; exact (AGc12 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m11 m12 sp s0 UWF11 AGu12) as UWF12.
  assert (KF29 : rw_cells asegs m12 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_v5_v1; apply (wg_keep_live _ _ _ _ m11 m12 v1 48 _ _ H11_0 PRES12 WM12 INP_v1_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H11_1 AGc12 WM12 KF30.
  assert (KF31 : rw_cells asegs m12 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v2 40 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v2_6)) as DJ_v5_v2; apply (wg_keep_live _ _ _ _ m11 m12 v2 40 _ _ KF24 PRES12 WM12 INP_v2_10); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF32 : rw_cells asegs m12 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) w3_2 128 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_w3_2_6)) as DJ_v5_w3_2; apply (wg_keep_live _ _ _ _ m11 m12 w3_2 128 _ _ KF25 PRES12 WM12 INP_w3_2_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF33 : rw_cells asegs m12 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v3 104 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v3_6)) as DJ_v5_v3; apply (wg_keep_live _ _ _ _ m11 m12 v3 104 _ _ KF26 PRES12 WM12 INP_v3_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF35 : rw_cells asegs m12 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [] w5_2 128 ((v5, 104) :: rt_live RT Σ3) v5 104 ART10 LV10 ltac:(cbn [app In]; left; reflexivity)) as DJ_w5_2_v5; apply (wg_keep_live _ _ _ _ m11 m12 w5_2 128 _ _ KF28 PRES12 WM12 INP_w5_2_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w5_2_v5 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H11_0 H11_1 KF24 KF25 KF26 KF27 KF28 AGc12.
  destruct (af_client_consts RT AF Σ5 m12 ART12) as (_ & SHC12 & _ & _ & UT12).
  assert (ENV12 : cl_env m12 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v5 + 24, v5 + 56)]) by cl_fp_lia. apply (cl_env_agree m11 m12 _ _ ENV11). intros a Ha. apply PRES12; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ5 m12 v1 48 ART12 INP_v1_10) as (WR_v1_13 & ACC_v1_13).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s6_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_6) u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v3 v5 j1 F6 fc6 m12 lo
                ST12 WHLO WHIMG WHTOP KF29 KF30 SHC12 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT12 ACC_v1_13 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI12) as W13.
  cl_lift W13 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ5 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13 & H13_0 & H13_1 & H13_2 & ST13) & Hc13'). clear Hc13.
  fold usp in MU13, ST13, Hc13', H13_1.
  assert (ART13 : ART RT Σ5 m13).
  { apply (wg_seg_ART RT AF Σ5 m12 m13 usp 96 [(v1, v1 + 48)] ART12 ltac:(rewrite SPc10; clear - NUM; lia) ltac:(clear - NUM; lia) MU13); [|exact WM13].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 48; split; [exact INP_v1_10 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF36 : rw_cells asegs m13 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 48 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m12 m13 _ _ KF31 MU13 WM13); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF37 : rw_cells asegs m13 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_w3_2_v1; apply (wg_keep_seg _ m12 m13 _ _ KF32 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v1 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF38 : rw_cells asegs m13 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m12 m13 _ _ KF33 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF39 : rw_cells asegs m13 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [] w5_2 128 ((v5, 104) :: rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_w5_2_v1; apply (wg_keep_seg _ m12 m13 _ _ KF35 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w5_2_v1 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF40 : rw_cells asegs m13 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_v5_v1; apply (wg_keep_seg _ m12 m13 _ _ G6_CL0 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v1 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m12 m13 _ canary ENV12 MU13 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia])) as ENV13.
  clear KF29 KF30 KF31 KF32 KF33 KF35 G6_CL0 H13_2 ENV12.
  assert (AGs13 : agree_on (fun x => usp <= x < USTACK_TOP) m12 m13) by (intros a Ha; apply MU13; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m12 m13 sp s0 UWF12 AGs13) as UWF13.
  destruct (cl_chain_call (rt_cg RT Σ5) e_ossl_property_string_data_new e_OPENSSL_sk_new_null SITE_ossl_property_string_data_new_7 m13 m13 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTXb10
              (proj1 CGH10 (SITE_ossl_property_string_data_new_7, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH10 (SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null) ltac:(wp_in_lit)) UWF13 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m13 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H13_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc13 & UWCc13).
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_new_null Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_7) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_6 u4_6 u5_6 u6_6
           F6 fc6 m13 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART13 MI13).
  { clear - EU1 ST13 LOW10 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST13 LOW10 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_7) by (unfold SITE_ossl_property_string_data_new_7; clear; lia). exact CTXc13. }
  { exact UWCc13. }
  { apply (cg_has_weaken _ _ _ _ _ CGH10); vm_compute; reflexivity. }
  { clear - Hlen LENc10; lia. }
  { clear - Hcr CR2 CR4 CR6 CR10 MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV13. }
  { exact Hc13'. }
  clear Hc13'. intros c14 (Σ7 & v7 & Hc14 & LV14 & FRS14 & SP14 & CR14 & P0_v7 & P16_v7 & PU_v7 & CG14).
  wp_box1 PU_v7.
  destruct (ASTA_unpack RT Σ7 _ _ c14 Hc14) as (ms14 & (m14 & RS14 & (ART14 & MI14 & WM14 & ST14) & PRES14 & G7_ENVp & G7_WR_v1 & G7_ACC_v1 & G7_CL0) & Hc14'). clear Hc14.
  destruct RS14 as (u0_7 & u1_7 & u2_7 & b1_7 & b2_7 & b3_7 & b4_7 & b5_7 & b6_7 & b7_7 & u3_7 & u4_7 & u5_7 & u6_7 & F7 & fc7 & ->).
  rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even SITE_ossl_property_string_data_new_7) in Hc14' by (unfold SITE_ossl_property_string_data_new_7; clear; first [reflexivity | lia]).
  assert (AGc14 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m13 m14).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES14; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu14 : agree_on (fun x => usp <= x < USTACK_TOP) m13 m14) by (intros a Ha; cbv beta in Ha; exact (AGc14 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m13 m14 sp s0 UWF13 AGu14) as UWF14.
  assert (KF41 : rw_cells asegs m14 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 24 (repeat (Z_to_bv 8 0) 24)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v1 48 _ _ H13_0 PRES14 WM14 INP_v1_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H13_1 AGc14 WM14 KF42.
  assert (KF43 : rw_cells asegs m14 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m13 m14 v2 40 _ _ KF36 PRES14 WM14 INP_v2_10); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF44 : rw_cells asegs m14 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_live _ _ _ _ m13 m14 w3_2 128 _ _ KF37 PRES14 WM14 INP_w3_2_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF45 : rw_cells asegs m14 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v3 104 _ _ KF38 PRES14 WM14 INP_v3_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF46 : rw_cells asegs m14 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_live _ _ _ _ m13 m14 w5_2 128 _ _ KF39 PRES14 WM14 INP_w5_2_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF47 : rw_cells asegs m14 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v5 104 _ _ KF40 PRES14 WM14 INP_v5_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H13_0 H13_1 KF36 KF37 KF38 KF39 KF40 AGc14 CTXc13 UWCc13.
  assert (SPc14 : rt_sp0 RT Σ7 = rt_sp0 RT Σ) by (rewrite SP14; exact SPc10).
  assert (CGc14 : rt_cg RT Σ7 = rt_cg RT Σ) by (rewrite CG14; exact CGc10).
  assert (LOW14 : rt_sp0 RT Σ7 - STACK_WIN <= lo) by (rewrite SPc14; exact LOW).
  assert (LEN14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ5)) + 1) by (rewrite LV14; clear; cbn [length]; lia).
  assert (LENc14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ)) + 7) by (clear - LEN14 LENc10; lia). clear LENc10. wp_box1 LEN10. wp_box1 CR14.
  assert (Hfr14 : (length (rt_frames RT Σ7) < FRAMES_MAX)%nat) by (rewrite FRS14; exact Hfr10).
  assert (CTXb14 : cg_ctx (rt_cg RT Σ7) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc14; exact CTX).
  assert (CGH14 : cg_has (rt_cg RT Σ7) _ _) by (rewrite CGc14; exact CGH).
  assert (INP_v1_14 : In (v1, 48) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v1_10).
  assert (INP_v2_14 : In (v2, 40) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v2_10).
  assert (INP_v3_14 : In (v3, 104) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v3_10).
  assert (INP_w3_2_14 : In (w3_2, 128) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_w3_2_10).
  assert (INP_v5_14 : In (v5, 104) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v5_10).
  assert (INP_w5_2_14 : In (w5_2, 128) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_w5_2_10).
  assert (INP_v7_14 : In (v7, 56) (rt_live RT Σ7)) by (rewrite LV14; left; reflexivity).
  pose proof (af_live_range RT AF Σ7 m14 v7 56 ART14 INP_v7_14) as (_ & PHI_v7 & _). rewrite SPc14 in PHI_v7.
  pose proof (afp_live_mem RT GOBJ AFP Σ7 m14 v7 56 ART14 INP_v7_14 ltac:(clear; lia)) as (_ & PT_v7).
  pose proof (afp_live_hi RT GOBJ AFP Σ7 m14 v7 56 ART14 INP_v7_14 ltac:(clear; lia)) as PHH_v7.
  pose proof (wg_mod16_8 _ P16_v7) as PAL_v7. assert (PR64_v7 : 0 <= v7 < 2 ^ 64) by (first [clear - PHH_v7 PT_v7; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v7 : v7 + 56 <= lo) by (first [clear - PHI_v7 LOW14; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v7. wp_box1 PAL_v7. wp_box1 PR64_v7.
  destruct (af_client_consts RT AF Σ7 m14 ART14) as (_ & SHC14 & _ & _ & UT14).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s7_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_7) u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v3 v5 v7 j1 F7 fc7 m14 lo
                ST14 WHLO WHIMG WHTOP KF41 KF42 SHC14 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) PR64_v7 UT14 MI14) as W15.
  cl_lift W15 Hc14' c15 Hc15.
  destruct (ASTA_unpack RT Σ7 _ _ c15 Hc15) as (ms15 & (m15 & -> & MU15 & WM15 & MI15 & H15_0 & H15_1 & H15_2 & ST15) & Hc15'). clear Hc15.
  fold usp in MU15, ST15, Hc15', H15_1.
  assert (ART15 : ART RT Σ7 m15).
  { apply (wg_seg_ART RT AF Σ7 m14 m15 usp 96 [] ART14 ltac:(rewrite SPc14; clear - NUM; lia) ltac:(clear - NUM; lia) MU15); [|exact WM15].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF48 : rw_cells asegs m15 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m14 m15 _ _ KF43 MU15 WM15); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF49 : rw_cells asegs m15 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m14 m15 _ _ KF44 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF50 : rw_cells asegs m15 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m14 m15 _ _ KF45 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF51 : rw_cells asegs m15 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m14 m15 _ _ KF46 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF52 : rw_cells asegs m15 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m14 m15 _ _ KF47 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF53 : rw_cells asegs m15 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m14 m15 _ _ G7_CL0 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m14 m15 _ canary G7_ENVp MU15 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV15.
  clear KF41 KF42 KF43 KF44 KF45 KF46 KF47 G7_CL0 H15_2 G7_ENVp.
  assert (AGs15 : agree_on (fun x => usp <= x < USTACK_TOP) m14 m15) by (intros a Ha; apply MU15; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m14 m15 sp s0 UWF14 AGs15) as UWF15.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_8) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2146284) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_7 u4_7 u5_7 u6_7
           F7 fc7 m15 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART15 MI15).
  { clear - EU1 ST15 LOW14 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST15 LOW14 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF53. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc15'. }
  clear Hc15'. intros c16 Hc16.
  destruct (ASTA_unpack RT Σ7 _ _ c16 Hc16) as (ms16 & (m16 & RS16 & (ART16 & MI16 & WM16 & ST16) & PRES16 & G8_CL0) & Hc16'). clear Hc16.
  destruct RS16 as (u0_8 & u1_8 & u2_8 & b1_8 & b2_8 & b3_8 & b4_8 & b5_8 & b6_8 & b7_8 & u3_8 & u4_8 & u5_8 & u6_8 & F8 & fc8 & ->).
  rewrite EU1 in ST16, PRES16. rewrite (ret_pc_even SITE_ossl_property_string_data_new_8) in Hc16' by (unfold SITE_ossl_property_string_data_new_8; clear; first [reflexivity | lia]).
  assert (AGc16 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m15 m16).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES16; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu16 : agree_on (fun x => usp <= x < USTACK_TOP) m15 m16) by (intros a Ha; cbv beta in Ha; exact (AGc16 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m15 m16 sp s0 UWF15 AGu16) as UWF16.
  assert (KF54 : rw_cells asegs m16 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 24 (repeat (Z_to_bv 8 0) 24)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v1 48 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m15 m16 v1 48 _ _ H15_0 PRES16 WM16 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H15_1 AGc16 WM16 KF55.
  assert (KF56 : rw_cells asegs m16 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v2 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m15 m16 v2 40 _ _ KF48 PRES16 WM16 INP_v2_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF57 : rw_cells asegs m16 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w3_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w3_2_10)) as DJ_v7_w3_2; apply (wg_keep_live _ _ _ _ m15 m16 w3_2 128 _ _ KF49 PRES16 WM16 INP_w3_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF58 : rw_cells asegs m16 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v3 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v3_10)) as DJ_v7_v3; apply (wg_keep_live _ _ _ _ m15 m16 v3 104 _ _ KF50 PRES16 WM16 INP_v3_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF59 : rw_cells asegs m16 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w5_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w5_2_10)) as DJ_v7_w5_2; apply (wg_keep_live _ _ _ _ m15 m16 w5_2 128 _ _ KF51 PRES16 WM16 INP_w5_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF60 : rw_cells asegs m16 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v5 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v5_10)) as DJ_v7_v5; apply (wg_keep_live _ _ _ _ m15 m16 v5 104 _ _ KF52 PRES16 WM16 INP_v5_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H15_0 H15_1 KF48 KF49 KF50 KF51 KF52 KF53 AGc16.
  destruct (af_client_consts RT AF Σ7 m16 ART16) as (_ & SHC16 & _ & _ & UT16).
  assert (ENV16 : cl_env m16 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m15 m16 _ _ ENV15). intros a Ha. apply PRES16; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s8_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_8) u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v3 v5 v7 j1 F8 fc8 m16 lo
                ST16 WHLO WHIMG WHTOP KF54 KF55 SHC16 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT16 MI16) as W17.
  cl_lift W17 Hc16' c17 Hc17.
  destruct (ASTA_unpack RT Σ7 _ _ c17 Hc17) as (ms17 & (m17 & -> & MU17 & WM17 & MI17 & H17_0 & H17_1 & H17_2 & ST17) & Hc17'). clear Hc17.
  fold usp in MU17, ST17, Hc17', H17_1.
  assert (ART17 : ART RT Σ7 m17).
  { apply (wg_seg_ART RT AF Σ7 m16 m17 usp 96 [] ART16 ltac:(rewrite SPc14; clear - NUM; lia) ltac:(clear - NUM; lia) MU17); [|exact WM17].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF62 : rw_cells asegs m17 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m16 m17 _ _ KF56 MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF63 : rw_cells asegs m17 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m16 m17 _ _ KF57 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF64 : rw_cells asegs m17 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m16 m17 _ _ KF58 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF65 : rw_cells asegs m17 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m16 m17 _ _ KF59 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF66 : rw_cells asegs m17 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m16 m17 _ _ KF60 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF67 : rw_cells asegs m17 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m16 m17 _ _ G8_CL0 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m16 m17 _ canary ENV16 MU17 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV17.
  clear KF54 KF55 KF56 KF57 KF58 KF59 KF60 G8_CL0 H17_2 ENV16.
  assert (AGs17 : agree_on (fun x => usp <= x < USTACK_TOP) m16 m17) by (intros a Ha; apply MU17; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m16 m17 sp s0 UWF16 AGs17) as UWF17.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_9) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2146328) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_8 u4_8 u5_8 u6_8
           F8 fc8 m17 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART17 MI17).
  { clear - EU1 ST17 LOW14 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST17 LOW14 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF67. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc17'. }
  clear Hc17'. intros c18 Hc18.
  destruct (ASTA_unpack RT Σ7 _ _ c18 Hc18) as (ms18 & (m18 & RS18 & (ART18 & MI18 & WM18 & ST18) & PRES18 & G9_CL0) & Hc18'). clear Hc18.
  destruct RS18 as (u0_9 & u1_9 & u2_9 & b1_9 & b2_9 & b3_9 & b4_9 & b5_9 & b6_9 & b7_9 & u3_9 & u4_9 & u5_9 & u6_9 & F9 & fc9 & ->).
  rewrite EU1 in ST18, PRES18. rewrite (ret_pc_even SITE_ossl_property_string_data_new_9) in Hc18' by (unfold SITE_ossl_property_string_data_new_9; clear; first [reflexivity | lia]).
  assert (AGc18 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m17 m18).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES18; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu18 : agree_on (fun x => usp <= x < USTACK_TOP) m17 m18) by (intros a Ha; cbv beta in Ha; exact (AGc18 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m17 m18 sp s0 UWF17 AGu18) as UWF18.
  assert (KF68 : rw_cells asegs m18 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 24 (repeat (Z_to_bv 8 0) 24)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v1 48 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m17 m18 v1 48 _ _ H17_0 PRES18 WM18 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H17_1 AGc18 WM18 KF69.
  assert (KF70 : rw_cells asegs m18 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v2 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m17 m18 v2 40 _ _ KF62 PRES18 WM18 INP_v2_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF71 : rw_cells asegs m18 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w3_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w3_2_10)) as DJ_v7_w3_2; apply (wg_keep_live _ _ _ _ m17 m18 w3_2 128 _ _ KF63 PRES18 WM18 INP_w3_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF72 : rw_cells asegs m18 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v3 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v3_10)) as DJ_v7_v3; apply (wg_keep_live _ _ _ _ m17 m18 v3 104 _ _ KF64 PRES18 WM18 INP_v3_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF73 : rw_cells asegs m18 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w5_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w5_2_10)) as DJ_v7_w5_2; apply (wg_keep_live _ _ _ _ m17 m18 w5_2 128 _ _ KF65 PRES18 WM18 INP_w5_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF74 : rw_cells asegs m18 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v5 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v5_10)) as DJ_v7_v5; apply (wg_keep_live _ _ _ _ m17 m18 v5 104 _ _ KF66 PRES18 WM18 INP_v5_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H17_0 H17_1 KF62 KF63 KF64 KF65 KF66 KF67 AGc18.
  destruct (af_client_consts RT AF Σ7 m18 ART18) as (_ & SHC18 & _ & _ & UT18).
  assert (ENV18 : cl_env m18 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m17 m18 _ _ ENV17). intros a Ha. apply PRES18; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s9_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_9) u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v3 v5 v7 j1 F9 fc9 m18 lo
                ST18 WHLO WHIMG WHTOP KF68 KF69 SHC18 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT18 MI18) as W19.
  cl_lift W19 Hc18' c19 Hc19.
  destruct (ASTA_unpack RT Σ7 _ _ c19 Hc19) as (ms19 & (m19 & -> & MU19 & WM19 & MI19 & H19_0 & H19_1 & H19_2 & ST19) & Hc19'). clear Hc19.
  fold usp in MU19, ST19, Hc19', H19_1.
  assert (ART19 : ART RT Σ7 m19).
  { apply (wg_seg_ART RT AF Σ7 m18 m19 usp 96 [] ART18 ltac:(rewrite SPc14; clear - NUM; lia) ltac:(clear - NUM; lia) MU19); [|exact WM19].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF76 : rw_cells asegs m19 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m18 m19 _ _ KF70 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF77 : rw_cells asegs m19 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m18 m19 _ _ KF71 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF78 : rw_cells asegs m19 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m18 m19 _ _ KF72 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF79 : rw_cells asegs m19 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m18 m19 _ _ KF73 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF80 : rw_cells asegs m19 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m18 m19 _ _ KF74 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF81 : rw_cells asegs m19 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_seg _ m18 m19 _ _ G9_CL0 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m18 m19 _ canary ENV18 MU19 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV19.
  clear KF68 KF69 KF70 KF71 KF72 KF73 KF74 G9_CL0 H19_2 ENV18.
  assert (AGs19 : agree_on (fun x => usp <= x < USTACK_TOP) m18 m19) by (intros a Ha; apply MU19; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m18 m19 sp s0 UWF18 AGs19) as UWF19.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_10) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2146368) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_9 u4_9 u5_9 u6_9
           F9 fc9 m19 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 0) (Z_to_bv 64 2146328) FDO MST eq_refl eq_refl ART19 MI19).
  { clear - EU1 ST19 LOW14 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST19 LOW14 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF81. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc19'. }
  clear Hc19'. intros c20 Hc20.
  destruct (ASTA_unpack RT Σ7 _ _ c20 Hc20) as (ms20 & (m20 & RS20 & (ART20 & MI20 & WM20 & ST20) & PRES20 & G10_CL0) & Hc20'). clear Hc20.
  destruct RS20 as (u0_10 & u1_10 & u2_10 & b1_10 & b2_10 & b3_10 & b4_10 & b5_10 & b6_10 & b7_10 & u3_10 & u4_10 & u5_10 & u6_10 & F10 & fc10 & ->).
  rewrite EU1 in ST20, PRES20. rewrite (ret_pc_even SITE_ossl_property_string_data_new_10) in Hc20' by (unfold SITE_ossl_property_string_data_new_10; clear; first [reflexivity | lia]).
  assert (AGc20 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m19 m20).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES20; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu20 : agree_on (fun x => usp <= x < USTACK_TOP) m19 m20) by (intros a Ha; cbv beta in Ha; exact (AGc20 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m19 m20 sp s0 UWF19 AGu20) as UWF20.
  assert (KF82 : rw_cells asegs m20 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 24 (repeat (Z_to_bv 8 0) 24)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v1 48 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m19 m20 v1 48 _ _ H19_0 PRES20 WM20 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H19_1 AGc20 WM20 KF83.
  assert (KF84 : rw_cells asegs m20 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v2 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m19 m20 v2 40 _ _ KF76 PRES20 WM20 INP_v2_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF85 : rw_cells asegs m20 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w3_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w3_2_10)) as DJ_v7_w3_2; apply (wg_keep_live _ _ _ _ m19 m20 w3_2 128 _ _ KF77 PRES20 WM20 INP_w3_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF86 : rw_cells asegs m20 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v3 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v3_10)) as DJ_v7_v3; apply (wg_keep_live _ _ _ _ m19 m20 v3 104 _ _ KF78 PRES20 WM20 INP_v3_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF87 : rw_cells asegs m20 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) w5_2 128 ART14 LV14 ltac:(cbn [app In]; exact INP_w5_2_10)) as DJ_v7_w5_2; apply (wg_keep_live _ _ _ _ m19 m20 w5_2 128 _ _ KF79 PRES20 WM20 INP_w5_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF88 : rw_cells asegs m20 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v5 104 ART14 LV14 ltac:(cbn [app In]; exact INP_v5_10)) as DJ_v7_v5; apply (wg_keep_live _ _ _ _ m19 m20 v5 104 _ _ KF80 PRES20 WM20 INP_v5_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H19_0 H19_1 KF76 KF77 KF78 KF79 KF80 KF81 AGc20.
  destruct (af_client_consts RT AF Σ7 m20 ART20) as (_ & SHC20 & _ & _ & UT20).
  assert (ENV20 : cl_env m20 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m19 m20 _ _ ENV19). intros a Ha. apply PRES20; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ7 m20 v1 48 ART20 INP_v1_14) as (WR_v1_21 & ACC_v1_21).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s10_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_10) u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v3 v5 v7 j1 F10 fc10 m20 lo
                ST20 WHLO WHIMG WHTOP KF82 KF83 SHC20 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT20 ACC_v1_21 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI20) as W21.
  cl_lift W21 Hc20' c21 Hc21.
  destruct (ASTA_unpack RT Σ7 _ _ c21 Hc21) as (ms21 & (m21 & -> & MU21 & WM21 & MI21 & H21_0 & H21_1 & H21_2 & ST21) & Hc21'). clear Hc21.
  fold usp in MU21, ST21, Hc21', H21_1.
  assert (ART21 : ART RT Σ7 m21).
  { apply (wg_seg_ART RT AF Σ7 m20 m21 usp 96 [(v1, v1 + 48)] ART20 ltac:(rewrite SPc14; clear - NUM; lia) ltac:(clear - NUM; lia) MU21); [|exact WM21].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 48; split; [exact INP_v1_14 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF90 : rw_cells asegs m21 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 48 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m20 m21 _ _ KF84 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF91 : rw_cells asegs m21 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_w3_2_v1; apply (wg_keep_seg _ m20 m21 _ _ KF85 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v1 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF92 : rw_cells asegs m21 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m20 m21 _ _ KF86 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF93 : rw_cells asegs m21 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [] w5_2 128 ((v5, 104) :: rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_w5_2_v1; apply (wg_keep_seg _ m20 m21 _ _ KF87 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w5_2_v1 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF94 : rw_cells asegs m21 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_v5_v1; apply (wg_keep_seg _ m20 m21 _ _ KF88 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v1 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF95 : rw_cells asegs m21 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v1 48 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v7_v1; apply (wg_keep_seg _ m20 m21 _ _ G10_CL0 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m20 m21 _ canary ENV20 MU21 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia])) as ENV21.
  clear KF82 KF83 KF84 KF85 KF86 KF87 KF88 G10_CL0 H21_2 ENV20.
  assert (AGs21 : agree_on (fun x => usp <= x < USTACK_TOP) m20 m21) by (intros a Ha; apply MU21; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m20 m21 sp s0 UWF20 AGs21) as UWF21.
  destruct (cl_chain_call (rt_cg RT Σ7) e_ossl_property_string_data_new e_OPENSSL_sk_new_null SITE_ossl_property_string_data_new_11 m21 m21 ra s0 sp (Z_to_bv 64 (usp + -96)) outer CTXb14
              (proj1 CGH14 (SITE_ossl_property_string_data_new_11, e_ossl_property_string_data_new) ltac:(wp_in_lit)) (proj2 CGH14 (SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null) ltac:(wp_in_lit)) UWF21 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -96 + Z.of_nat (cells_size [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m21 (usp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H21_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc21 & UWCc21).
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_new_null Σ7 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_11) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 0) b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_10 u4_10 u5_10 u6_10
           F10 fc10 m21 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART21 MI21).
  { clear - EU1 ST21 LOW14 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST21 LOW14 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_property_string_data_new_11) by (unfold SITE_ossl_property_string_data_new_11; clear; lia). exact CTXc21. }
  { exact UWCc21. }
  { apply (cg_has_weaken _ _ _ _ _ CGH14); vm_compute; reflexivity. }
  { clear - Hlen LENc14; lia. }
  { clear - Hcr CR2 CR4 CR6 CR10 CR14 MC_104 MC_128 MC_48 MC_56; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV21. }
  { exact Hc21'. }
  clear Hc21'. intros c22 (Σ11 & v11 & Hc22 & LV22 & FRS22 & SP22 & CR22 & P0_v11 & P16_v11 & PU_v11 & CG22).
  wp_box1 PU_v11.
  destruct (ASTA_unpack RT Σ11 _ _ c22 Hc22) as (ms22 & (m22 & RS22 & (ART22 & MI22 & WM22 & ST22) & PRES22 & G11_ENVp & G11_WR_v1 & G11_ACC_v1 & G11_CL0) & Hc22'). clear Hc22.
  destruct RS22 as (u0_11 & u1_11 & u2_11 & b1_11 & b2_11 & b3_11 & b4_11 & b5_11 & b6_11 & b7_11 & u3_11 & u4_11 & u5_11 & u6_11 & F11 & fc11 & ->).
  rewrite EU1 in ST22, PRES22. rewrite (ret_pc_even SITE_ossl_property_string_data_new_11) in Hc22' by (unfold SITE_ossl_property_string_data_new_11; clear; first [reflexivity | lia]).
  assert (AGc22 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m21 m22).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES22; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu22 : agree_on (fun x => usp <= x < USTACK_TOP) m21 m22) by (intros a Ha; cbv beta in Ha; exact (AGc22 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m21 m22 sp s0 UWF21 AGu22) as UWF22.
  assert (KF96 : rw_cells asegs m22 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v7); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v1 48 _ _ H21_0 PRES22 WM22 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H21_1 AGc22 WM22 KF97.
  assert (KF98 : rw_cells asegs m22 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v2 40 _ _ KF90 PRES22 WM22 INP_v2_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF99 : rw_cells asegs m22 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_live _ _ _ _ m21 m22 w3_2 128 _ _ KF91 PRES22 WM22 INP_w3_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF100 : rw_cells asegs m22 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v3 104 _ _ KF92 PRES22 WM22 INP_v3_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF101 : rw_cells asegs m22 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_live _ _ _ _ m21 m22 w5_2 128 _ _ KF93 PRES22 WM22 INP_w5_2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF102 : rw_cells asegs m22 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v5 104 _ _ KF94 PRES22 WM22 INP_v5_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF103 : rw_cells asegs m22 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v7 56 _ _ KF95 PRES22 WM22 INP_v7_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H21_0 H21_1 KF90 KF91 KF92 KF93 KF94 KF95 AGc22 CTXc21 UWCc21.
  assert (SPc22 : rt_sp0 RT Σ11 = rt_sp0 RT Σ) by (rewrite SP22; exact SPc14).
  assert (CGc22 : rt_cg RT Σ11 = rt_cg RT Σ) by (rewrite CG22; exact CGc14).
  assert (LOW22 : rt_sp0 RT Σ11 - STACK_WIN <= lo) by (rewrite SPc22; exact LOW).
  assert (LEN22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ7)) + 1) by (rewrite LV22; clear; cbn [length]; lia).
  assert (LENc22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ)) + 8) by (clear - LEN22 LENc14; lia). clear LENc14. wp_box1 LEN14. wp_box1 CR22.
  assert (Hfr22 : (length (rt_frames RT Σ11) < FRAMES_MAX)%nat) by (rewrite FRS22; exact Hfr14).
  assert (CTXb22 : cg_ctx (rt_cg RT Σ11) e_ossl_property_string_data_new (bv_unsigned ra :: outer)) by (rewrite CGc22; exact CTX).
  assert (CGH22 : cg_has (rt_cg RT Σ11) _ _) by (rewrite CGc22; exact CGH).
  assert (INP_v1_22 : In (v1, 48) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v1_14).
  assert (INP_v2_22 : In (v2, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v2_14).
  assert (INP_v3_22 : In (v3, 104) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v3_14).
  assert (INP_w3_2_22 : In (w3_2, 128) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_w3_2_14).
  assert (INP_v5_22 : In (v5, 104) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v5_14).
  assert (INP_w5_2_22 : In (w5_2, 128) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_w5_2_14).
  assert (INP_v7_22 : In (v7, 56) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v7_14).
  assert (INP_v11_22 : In (v11, 56) (rt_live RT Σ11)) by (rewrite LV22; left; reflexivity).
  pose proof (af_live_range RT AF Σ11 m22 v11 56 ART22 INP_v11_22) as (_ & PHI_v11 & _). rewrite SPc22 in PHI_v11.
  pose proof (afp_live_mem RT GOBJ AFP Σ11 m22 v11 56 ART22 INP_v11_22 ltac:(clear; lia)) as (_ & PT_v11).
  pose proof (afp_live_hi RT GOBJ AFP Σ11 m22 v11 56 ART22 INP_v11_22 ltac:(clear; lia)) as PHH_v11.
  pose proof (wg_mod16_8 _ P16_v11) as PAL_v11. assert (PR64_v11 : 0 <= v11 < 2 ^ 64) by (first [clear - PHH_v11 PT_v11; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v11 : v11 + 56 <= lo) by (first [clear - PHI_v11 LOW22; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v11. wp_box1 PAL_v11. wp_box1 PR64_v11.
  destruct (af_client_consts RT AF Σ11 m22 ART22) as (_ & SHC22 & _ & _ & UT22).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s11_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_11) u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v3 v5 v7 v11 j1 F11 fc11 m22 lo
                ST22 WHLO WHIMG WHTOP KF96 KF97 SHC22 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) PR64_v11 UT22 MI22) as W23.
  cl_lift W23 Hc22' c23 Hc23.
  destruct (ASTA_unpack RT Σ11 _ _ c23 Hc23) as (ms23 & (m23 & -> & MU23 & WM23 & MI23 & H23_0 & H23_1 & H23_2 & ST23) & Hc23'). clear Hc23.
  fold usp in MU23, ST23, Hc23', H23_1.
  assert (ART23 : ART RT Σ11 m23).
  { apply (wg_seg_ART RT AF Σ11 m22 m23 usp 96 [] ART22 ltac:(rewrite SPc22; clear - NUM; lia) ltac:(clear - NUM; lia) MU23); [|exact WM23].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF104 : rw_cells asegs m23 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m22 m23 _ _ KF98 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF105 : rw_cells asegs m23 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m22 m23 _ _ KF99 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF106 : rw_cells asegs m23 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m22 m23 _ _ KF100 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF107 : rw_cells asegs m23 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m22 m23 _ _ KF101 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF108 : rw_cells asegs m23 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m22 m23 _ _ KF102 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF109 : rw_cells asegs m23 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_seg _ m22 m23 _ _ KF103 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF110 : rw_cells asegs m23 v11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m22 m23 _ _ G11_CL0 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m22 m23 _ canary G11_ENVp MU23 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV23.
  clear KF96 KF97 KF98 KF99 KF100 KF101 KF102 KF103 G11_CL0 H23_2 G11_ENVp.
  assert (AGs23 : agree_on (fun x => usp <= x < USTACK_TOP) m22 m23) by (intros a Ha; apply MU23; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m22 m23 sp s0 UWF22 AGs23) as UWF23.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ11 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_12) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 2146284) b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_11 u4_11 u5_11 u6_11
           F11 fc11 m23 lo v11 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART23 MI23).
  { clear - EU1 ST23 LOW22 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST23 LOW22 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v11_22. }
  { exact P16_v11. }
  { exact KF110. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc23'. }
  clear Hc23'. intros c24 Hc24.
  destruct (ASTA_unpack RT Σ11 _ _ c24 Hc24) as (ms24 & (m24 & RS24 & (ART24 & MI24 & WM24 & ST24) & PRES24 & G12_CL0) & Hc24'). clear Hc24.
  destruct RS24 as (u0_12 & u1_12 & u2_12 & b1_12 & b2_12 & b3_12 & b4_12 & b5_12 & b6_12 & b7_12 & u3_12 & u4_12 & u5_12 & u6_12 & F12 & fc12 & ->).
  rewrite EU1 in ST24, PRES24. rewrite (ret_pc_even SITE_ossl_property_string_data_new_12) in Hc24' by (unfold SITE_ossl_property_string_data_new_12; clear; first [reflexivity | lia]).
  assert (AGc24 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m23 m24).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES24; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu24 : agree_on (fun x => usp <= x < USTACK_TOP) m23 m24) by (intros a Ha; cbv beta in Ha; exact (AGc24 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m23 m24 sp s0 UWF23 AGu24) as UWF24.
  assert (KF111 : rw_cells asegs m24 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v7); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v1 48 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v11_v1; apply (wg_keep_live _ _ _ _ m23 m24 v1 48 _ _ H23_0 PRES24 WM24 INP_v1_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H23_1 AGc24 WM24 KF112.
  assert (KF113 : rw_cells asegs m24 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v2 40 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v11_v2; apply (wg_keep_live _ _ _ _ m23 m24 v2 40 _ _ KF104 PRES24 WM24 INP_v2_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF114 : rw_cells asegs m24 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w3_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w3_2_14)) as DJ_v11_w3_2; apply (wg_keep_live _ _ _ _ m23 m24 w3_2 128 _ _ KF105 PRES24 WM24 INP_w3_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF115 : rw_cells asegs m24 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v3 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v3_14)) as DJ_v11_v3; apply (wg_keep_live _ _ _ _ m23 m24 v3 104 _ _ KF106 PRES24 WM24 INP_v3_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF116 : rw_cells asegs m24 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w5_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w5_2_14)) as DJ_v11_w5_2; apply (wg_keep_live _ _ _ _ m23 m24 w5_2 128 _ _ KF107 PRES24 WM24 INP_w5_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF117 : rw_cells asegs m24 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v5 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v5_14)) as DJ_v11_v5; apply (wg_keep_live _ _ _ _ m23 m24 v5 104 _ _ KF108 PRES24 WM24 INP_v5_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF118 : rw_cells asegs m24 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v7 56 ART22 LV22 ltac:(cbn [app In]; exact INP_v7_14)) as DJ_v11_v7; apply (wg_keep_live _ _ _ _ m23 m24 v7 56 _ _ KF109 PRES24 WM24 INP_v7_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v7 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H23_0 H23_1 KF104 KF105 KF106 KF107 KF108 KF109 KF110 AGc24.
  destruct (af_client_consts RT AF Σ11 m24 ART24) as (_ & SHC24 & _ & _ & UT24).
  assert (ENV24 : cl_env m24 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v11, v11 + 56)]) by cl_fp_lia. apply (cl_env_agree m23 m24 _ _ ENV23). intros a Ha. apply PRES24; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s12_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_12) u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v2 v3 v5 v7 v11 j1 F12 fc12 m24 lo
                ST24 WHLO WHIMG WHTOP KF111 KF112 SHC24 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT24 MI24) as W25.
  cl_lift W25 Hc24' c25 Hc25.
  destruct (ASTA_unpack RT Σ11 _ _ c25 Hc25) as (ms25 & (m25 & -> & MU25 & WM25 & MI25 & H25_0 & H25_1 & H25_2 & ST25) & Hc25'). clear Hc25.
  fold usp in MU25, ST25, Hc25', H25_1.
  assert (ART25 : ART RT Σ11 m25).
  { apply (wg_seg_ART RT AF Σ11 m24 m25 usp 96 [] ART24 ltac:(rewrite SPc22; clear - NUM; lia) ltac:(clear - NUM; lia) MU25); [|exact WM25].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF120 : rw_cells asegs m25 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m24 m25 _ _ KF113 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF121 : rw_cells asegs m25 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m24 m25 _ _ KF114 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF122 : rw_cells asegs m25 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m24 m25 _ _ KF115 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF123 : rw_cells asegs m25 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m24 m25 _ _ KF116 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF124 : rw_cells asegs m25 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m24 m25 _ _ KF117 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF125 : rw_cells asegs m25 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_seg _ m24 m25 _ _ KF118 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF126 : rw_cells asegs m25 v11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m24 m25 _ _ G12_CL0 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m24 m25 _ canary ENV24 MU25 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV25.
  clear KF111 KF112 KF113 KF114 KF115 KF116 KF117 KF118 G12_CL0 H25_2 ENV24.
  assert (AGs25 : agree_on (fun x => usp <= x < USTACK_TOP) m24 m25) by (intros a Ha; apply MU25; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m24 m25 sp s0 UWF24 AGs25) as UWF25.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ11 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_13) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 2146328) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_12 u4_12 u5_12 u6_12
           F12 fc12 m25 lo v11 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART25 MI25).
  { clear - EU1 ST25 LOW22 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST25 LOW22 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v11_22. }
  { exact P16_v11. }
  { exact KF126. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc25'. }
  clear Hc25'. intros c26 Hc26.
  destruct (ASTA_unpack RT Σ11 _ _ c26 Hc26) as (ms26 & (m26 & RS26 & (ART26 & MI26 & WM26 & ST26) & PRES26 & G13_CL0) & Hc26'). clear Hc26.
  destruct RS26 as (u0_13 & u1_13 & u2_13 & b1_13 & b2_13 & b3_13 & b4_13 & b5_13 & b6_13 & b7_13 & u3_13 & u4_13 & u5_13 & u6_13 & F13 & fc13 & ->).
  rewrite EU1 in ST26, PRES26. rewrite (ret_pc_even SITE_ossl_property_string_data_new_13) in Hc26' by (unfold SITE_ossl_property_string_data_new_13; clear; first [reflexivity | lia]).
  assert (AGc26 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m25 m26).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES26; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu26 : agree_on (fun x => usp <= x < USTACK_TOP) m25 m26) by (intros a Ha; cbv beta in Ha; exact (AGc26 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m25 m26 sp s0 UWF25 AGu26) as UWF26.
  assert (KF127 : rw_cells asegs m26 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v7); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v1 48 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v11_v1; apply (wg_keep_live _ _ _ _ m25 m26 v1 48 _ _ H25_0 PRES26 WM26 INP_v1_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H25_1 AGc26 WM26 KF128.
  assert (KF129 : rw_cells asegs m26 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v2 40 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v11_v2; apply (wg_keep_live _ _ _ _ m25 m26 v2 40 _ _ KF120 PRES26 WM26 INP_v2_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF130 : rw_cells asegs m26 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w3_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w3_2_14)) as DJ_v11_w3_2; apply (wg_keep_live _ _ _ _ m25 m26 w3_2 128 _ _ KF121 PRES26 WM26 INP_w3_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF131 : rw_cells asegs m26 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v3 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v3_14)) as DJ_v11_v3; apply (wg_keep_live _ _ _ _ m25 m26 v3 104 _ _ KF122 PRES26 WM26 INP_v3_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF132 : rw_cells asegs m26 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w5_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w5_2_14)) as DJ_v11_w5_2; apply (wg_keep_live _ _ _ _ m25 m26 w5_2 128 _ _ KF123 PRES26 WM26 INP_w5_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF133 : rw_cells asegs m26 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v5 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v5_14)) as DJ_v11_v5; apply (wg_keep_live _ _ _ _ m25 m26 v5 104 _ _ KF124 PRES26 WM26 INP_v5_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF134 : rw_cells asegs m26 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v7 56 ART22 LV22 ltac:(cbn [app In]; exact INP_v7_14)) as DJ_v11_v7; apply (wg_keep_live _ _ _ _ m25 m26 v7 56 _ _ KF125 PRES26 WM26 INP_v7_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v7 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H25_0 H25_1 KF120 KF121 KF122 KF123 KF124 KF125 KF126 AGc26.
  destruct (af_client_consts RT AF Σ11 m26 ART26) as (_ & SHC26 & _ & _ & UT26).
  assert (ENV26 : cl_env m26 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v11, v11 + 56)]) by cl_fp_lia. apply (cl_env_agree m25 m26 _ _ ENV25). intros a Ha. apply PRES26; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s13_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_13) u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v2 v3 v5 v7 v11 j1 F13 fc13 m26 lo
                ST26 WHLO WHIMG WHTOP KF127 KF128 SHC26 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT26 MI26) as W27.
  cl_lift W27 Hc26' c27 Hc27.
  destruct (ASTA_unpack RT Σ11 _ _ c27 Hc27) as (ms27 & (m27 & -> & MU27 & WM27 & MI27 & H27_0 & H27_1 & H27_2 & ST27) & Hc27'). clear Hc27.
  fold usp in MU27, ST27, Hc27', H27_1.
  assert (ART27 : ART RT Σ11 m27).
  { apply (wg_seg_ART RT AF Σ11 m26 m27 usp 96 [] ART26 ltac:(rewrite SPc22; clear - NUM; lia) ltac:(clear - NUM; lia) MU27); [|exact WM27].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF136 : rw_cells asegs m27 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m26 m27 _ _ KF129 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF137 : rw_cells asegs m27 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m26 m27 _ _ KF130 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF138 : rw_cells asegs m27 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m26 m27 _ _ KF131 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF139 : rw_cells asegs m27 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m26 m27 _ _ KF132 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF140 : rw_cells asegs m27 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (apply (wg_keep_seg _ m26 m27 _ _ KF133 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF141 : rw_cells asegs m27 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_seg _ m26 m27 _ _ KF134 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF142 : rw_cells asegs m27 v11 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146328)]) by (apply (wg_keep_seg _ m26 m27 _ _ G13_CL0 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m26 m27 _ canary ENV26 MU27 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV27.
  clear KF127 KF128 KF129 KF130 KF131 KF132 KF133 KF134 G13_CL0 H27_2 ENV26.
  assert (AGs27 : agree_on (fun x => usp <= x < USTACK_TOP) m26 m27) by (intros a Ha; apply MU27; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m26 m27 sp s0 UWF26 AGs27) as UWF27.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_thunks Σ11 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_14) (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 0xba3ef0) u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 2146368) b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_13 u4_13 u5_13 u6_13
           F13 fc13 m27 lo v11 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2146284) (Z_to_bv 64 0) (Z_to_bv 64 2146328) FDO MST eq_refl eq_refl ART27 MI27).
  { clear - EU1 ST27 LOW22 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST27 LOW22 SPA 6. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v11_22. }
  { exact P16_v11. }
  { exact KF142. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc27'. }
  clear Hc27'. intros c28 Hc28.
  destruct (ASTA_unpack RT Σ11 _ _ c28 Hc28) as (ms28 & (m28 & RS28 & (ART28 & MI28 & WM28 & ST28) & PRES28 & G14_CL0) & Hc28'). clear Hc28.
  destruct RS28 as (u0_14 & u1_14 & u2_14 & b1_14 & b2_14 & b3_14 & b4_14 & b5_14 & b6_14 & b7_14 & u3_14 & u4_14 & u5_14 & u6_14 & F14 & fc14 & ->).
  rewrite EU1 in ST28, PRES28. rewrite (ret_pc_even SITE_ossl_property_string_data_new_14) in Hc28' by (unfold SITE_ossl_property_string_data_new_14; clear; first [reflexivity | lia]).
  assert (AGc28 : forall a k, usp + -96 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m27 m28).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES28; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu28 : agree_on (fun x => usp <= x < USTACK_TOP) m27 m28) by (intros a Ha; cbv beta in Ha; exact (AGc28 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m27 m28 sp s0 UWF27 AGu28) as UWF28.
  assert (KF143 : rw_cells asegs m28 v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v7); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v1 48 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v11_v1; apply (wg_keep_live _ _ _ _ m27 m28 v1 48 _ _ H27_0 PRES28 WM28 INP_v1_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H27_1 AGc28 WM28 KF144.
  assert (KF145 : rw_cells asegs m28 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v2 40 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v11_v2; apply (wg_keep_live _ _ _ _ m27 m28 v2 40 _ _ KF136 PRES28 WM28 INP_v2_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF146 : rw_cells asegs m28 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w3_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w3_2_14)) as DJ_v11_w3_2; apply (wg_keep_live _ _ _ _ m27 m28 w3_2 128 _ _ KF137 PRES28 WM28 INP_w3_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w3_2 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF147 : rw_cells asegs m28 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v3 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v3_14)) as DJ_v11_v3; apply (wg_keep_live _ _ _ _ m27 m28 v3 104 _ _ KF138 PRES28 WM28 INP_v3_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v3 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF148 : rw_cells asegs m28 w5_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) w5_2 128 ART22 LV22 ltac:(cbn [app In]; exact INP_w5_2_14)) as DJ_v11_w5_2; apply (wg_keep_live _ _ _ _ m27 m28 w5_2 128 _ _ KF139 PRES28 WM28 INP_w5_2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_w5_2 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF149 : rw_cells asegs m28 v5 [C8 (Z_to_bv 64 w5_2); C8 (Z_to_bv 64 2146188); C8 (Z_to_bv 64 2146120); C8 (Z_to_bv 64 2148220); C8 (Z_to_bv 64 2148252); C8 (Z_to_bv 64 2148284); C8 (Z_to_bv 64 2148316); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v5 104 ART22 LV22 ltac:(cbn [app In]; exact INP_v5_14)) as DJ_v11_v5; apply (wg_keep_live _ _ _ _ m27 m28 v5 104 _ _ KF140 PRES28 WM28 INP_v5_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v5 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF150 : rw_cells asegs m28 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2146284); C8 (Z_to_bv 64 2146368); C8 (Z_to_bv 64 2146328)]) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v7 56 ART22 LV22 ltac:(cbn [app In]; exact INP_v7_14)) as DJ_v11_v7; apply (wg_keep_live _ _ _ _ m27 m28 v7 56 _ _ KF141 PRES28 WM28 INP_v7_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v7 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H27_0 H27_1 KF136 KF137 KF138 KF139 KF140 KF141 KF142 AGc28.
  destruct (af_client_consts RT AF Σ11 m28 ART28) as (_ & SHC28 & _ & _ & UT28).
  assert (ENV28 : cl_env m28 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v11, v11 + 56)]) by cl_fp_lia. apply (cl_env_agree m27 m28 _ _ ENV27). intros a Ha. apply PRES28; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ11 m28 v1 48 ART28 INP_v1_22) as (WR_v1_29 & ACC_v1_29).
  (* [comment removed for export] *)
  pose proof (ossl_property_string_data_new_s14_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_14) u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v2 v3 v5 v7 v11 j1 F14 fc14 m28 lo
                ST28 WHLO WHIMG WHTOP KF143 KF144 SHC28 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT28 ACC_v1_29 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI28) as W29.
  cl_lift W29 Hc28' c29 Hc29.
  apply Hk. exists Σ11, v1, v2, v3, w3_2, v5, w5_2, v7, v11.
  split; [| split; [rewrite LV22, LV14, LV10, LV6, LV4, LV2; reflexivity|]; split; [rewrite FRS22, FRS14, FRS10, FRS6, FRS4, FRS2; reflexivity|]; split; [rewrite SP22, SP14, SP10, SP6, SP4, SP2; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v1|]; split; [exact P16_v1|]; split; [exact PU_v1|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; split; [exact P0_v3|]; split; [exact P16_v3|]; split; [exact PU_v3|]; split; [exact P0_w3_2|]; split; [exact P16_w3_2|]; split; [exact PU_w3_2|]; split; [exact P0_v5|]; split; [exact P16_v5|]; split; [exact PU_v5|]; split; [exact P0_w5_2|]; split; [exact P16_w5_2|]; split; [exact PU_w5_2|]; split; [exact P0_v7|]; split; [exact P16_v7|]; split; [exact PU_v7|]; split; [exact P0_v11|]; split; [exact P16_v11|]; split; [exact PU_v11|]; rewrite CG22, CG14, CG10, CG6, CG4, CG2; reflexivity].
  apply (ASTA_conseq RT Σ11 PMc _ _ c29 Hc29). intros ms29 (m29 & -> & MU29 & WM29 & MI29 & H29_0 & H29_1 & ST29). fold usp in MU29, ST29.
  exists m29.
  split; [exists u0_14, u1_14, u2_14, (Z_to_bv 64 v7), (Z_to_bv 64 0), b3_14, b4_14, b5_14, b6_14, b7_14, u3_14, u4_14, u5_14, u6_14, F14, fc14; reflexivity|].
  assert (ART29 : ART RT Σ11 m29).
  { apply (wg_seg_ART RT AF Σ11 m28 m29 usp 96 [(v1, v1 + 48)] ART28 ltac:(rewrite SPc22; clear - NUM; lia) ltac:(clear - NUM; lia) MU29); [|exact WM29].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 48; split; [exact INP_v1_22 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART29|]; split; [exact MI29|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 (wmono_trans asegs _ _ _ WM13 (wmono_trans asegs _ _ _ WM14 (wmono_trans asegs _ _ _ WM15 (wmono_trans asegs _ _ _ WM16 (wmono_trans asegs _ _ _ WM17 (wmono_trans asegs _ _ _ WM18 (wmono_trans asegs _ _ _ WM19 (wmono_trans asegs _ _ _ WM20 (wmono_trans asegs _ _ _ WM21 (wmono_trans asegs _ _ _ WM22 (wmono_trans asegs _ _ _ WM23 (wmono_trans asegs _ _ _ WM24 (wmono_trans asegs _ _ _ WM25 (wmono_trans asegs _ _ _ WM26 (wmono_trans asegs _ _ _ WM27 (wmono_trans asegs _ _ _ WM28 WM29)))))))))))))))))))))))))))) | exact ST29]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 1 right; exact He | rewrite FRS2; intros e He; exact He | clear; lia]).
    assert (NA_v1 : ~ (v1 <= bv_unsigned a < v1 + 48)) by exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(v1, 48)] v1 48 usp _ ART2 LV2 ltac:(left; reflexivity) FRS2 SP2 ltac:(clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha).
    wp_box1 NA_v1.
    assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; rewrite LV4; do 1 right; exact He | rewrite FRS4; intros e He; exact He | clear; lia]).
    assert (NA_v2 : ~ (v2 <= bv_unsigned a < v2 + 40)) by exact (wg_newchunk_apart RT AF Σ1 Σ2 m4 [(v2, 40)] v2 40 usp _ ART4 LV4 ltac:(left; reflexivity) FRS4 SP4 ltac:(rewrite SPc2; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha1).
    wp_box1 NA_v2.
    wp_box1 Ha1.
    assert (Ha3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha2); [intros e He; rewrite LV6; do 2 right; exact He | rewrite FRS6; intros e He; exact He | clear; lia]).
    assert (NA_v3 : ~ (v3 <= bv_unsigned a < v3 + 104)) by exact (wg_newchunk_apart RT AF Σ2 Σ3 m6 [(w3_2, 128); (v3, 104)] v3 104 usp _ ART6 LV6 ltac:(do 1 right; left; reflexivity) FRS6 SP6 ltac:(rewrite SPc4; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha2).
    wp_box1 NA_v3.
    assert (NA_w3_2 : ~ (w3_2 <= bv_unsigned a < w3_2 + 128)) by exact (wg_newchunk_apart RT AF Σ2 Σ3 m6 [(w3_2, 128); (v3, 104)] w3_2 128 usp _ ART6 LV6 ltac:(left; reflexivity) FRS6 SP6 ltac:(rewrite SPc4; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha2).
    wp_box1 NA_w3_2.
    wp_box1 Ha2.
    assert (Ha4 : aclient (rt_live RT Σ5) (rt_frames RT Σ5) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha3); [intros e He; rewrite LV10; do 2 right; exact He | rewrite FRS10; intros e He; exact He | clear; lia]).
    assert (NA_v5 : ~ (v5 <= bv_unsigned a < v5 + 104)) by exact (wg_newchunk_apart RT AF Σ3 Σ5 m10 [(w5_2, 128); (v5, 104)] v5 104 usp _ ART10 LV10 ltac:(do 1 right; left; reflexivity) FRS10 SP10 ltac:(rewrite SPc6; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha3).
    wp_box1 NA_v5.
    assert (NA_w5_2 : ~ (w5_2 <= bv_unsigned a < w5_2 + 128)) by exact (wg_newchunk_apart RT AF Σ3 Σ5 m10 [(w5_2, 128); (v5, 104)] w5_2 128 usp _ ART10 LV10 ltac:(left; reflexivity) FRS10 SP10 ltac:(rewrite SPc6; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha3).
    wp_box1 NA_w5_2.
    wp_box1 Ha3.
    assert (Ha5 : aclient (rt_live RT Σ7) (rt_frames RT Σ7) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha4); [intros e He; rewrite LV14; do 1 right; exact He | rewrite FRS14; intros e He; exact He | clear; lia]).
    assert (NA_v7 : ~ (v7 <= bv_unsigned a < v7 + 56)) by exact (wg_newchunk_apart RT AF Σ5 Σ7 m14 [(v7, 56)] v7 56 usp _ ART14 LV14 ltac:(left; reflexivity) FRS14 SP14 ltac:(rewrite SPc10; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha4).
    wp_box1 NA_v7.
    wp_box1 Ha4.
    assert (Ha6 : aclient (rt_live RT Σ11) (rt_frames RT Σ11) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha5); [intros e He; rewrite LV22; do 1 right; exact He | rewrite FRS22; intros e He; exact He | clear; lia]).
    assert (NA_v11 : ~ (v11 <= bv_unsigned a < v11 + 56)) by exact (wg_newchunk_apart RT AF Σ7 Σ11 m22 [(v11, 56)] v11 56 usp _ ART22 LV22 ltac:(left; reflexivity) FRS22 SP22 ltac:(rewrite SPc14; clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha5).
    wp_box1 NA_v11.
    wp_box1 Ha5.
    wp_box1 Ha6.
    pose proof (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM HSTK; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
    rewrite (MU29 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES28 a ltac:(unfold wp_box in Ha6; destruct Ha6 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU27 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES26 a ltac:(unfold wp_box in Ha6; destruct Ha6 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU25 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES24 a ltac:(unfold wp_box in Ha6; destruct Ha6 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU23 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES22 a ltac:(unfold wp_box in Ha5; destruct Ha5 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU21 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES20 a ltac:(unfold wp_box in Ha5; destruct Ha5 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU19 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES18 a ltac:(unfold wp_box in Ha5; destruct Ha5 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU17 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES16 a ltac:(unfold wp_box in Ha5; destruct Ha5 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU15 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES14 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU13 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES12 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU11 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES10 a ltac:(unfold wp_box in Ha3; destruct Ha3 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU9 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES8 a ltac:(unfold wp_box in Ha3; destruct Ha3 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU7 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES6 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU5 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES4 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU3 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES2 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; clear - H; unfold USTACK_TOP in *; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    reflexivity. }
  pose proof (af_acc_live RT AF Σ11 m29 v1 48 ART29 INP_v1_22) as (WRE_v1 & ACCE_v1).
  pose proof (af_acc_live RT AF Σ11 m29 v2 40 ART29 INP_v2_22) as (WRE_v2 & ACCE_v2).
  pose proof (af_acc_live RT AF Σ11 m29 v3 104 ART29 INP_v3_22) as (WRE_v3 & ACCE_v3).
  pose proof (af_acc_live RT AF Σ11 m29 w3_2 128 ART29 INP_w3_2_22) as (WRE_w3_2 & ACCE_w3_2).
  pose proof (af_acc_live RT AF Σ11 m29 v5 104 ART29 INP_v5_22) as (WRE_v5 & ACCE_v5).
  pose proof (af_acc_live RT AF Σ11 m29 w5_2 128 ART29 INP_w5_2_22) as (WRE_w5_2 & ACCE_w5_2).
  pose proof (af_acc_live RT AF Σ11 m29 v7 56 ART29 INP_v7_22) as (WRE_v7 & ACCE_v7).
  pose proof (af_acc_live RT AF Σ11 m29 v11 56 ART29 INP_v11_22) as (WRE_v11 & ACCE_v11).
  split; [exact (cl_env_seg _ m28 m29 _ canary ENV28 MU29 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia]))|].
  split; [exact WRE_v1|].
  split; [exact ACCE_v1|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  split; [exact WRE_v3|].
  split; [exact ACCE_v3|].
  split; [exact WRE_w3_2|].
  split; [exact ACCE_w3_2|].
  split; [exact WRE_v5|].
  split; [exact ACCE_v5|].
  split; [exact WRE_w5_2|].
  split; [exact ACCE_w5_2|].
  split; [exact WRE_v7|].
  split; [exact ACCE_v7|].
  split; [exact WRE_v11|].
  split; [exact ACCE_v11|].
  split; [exact H29_0|].
  split; [pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 48 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m28 m29 _ _ KF145 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_w3_2_v1; apply (wg_keep_seg _ m28 m29 _ _ KF146 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v1 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 48 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m28 m29 _ _ KF147 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ5 m10 [] w5_2 128 ((v5, 104) :: rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_w5_2_v1; apply (wg_keep_seg _ m28 m29 _ _ KF148 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w5_2_v1 PHI_w5_2 PT_w5_2 PHH_w5_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ5 m10 [(w5_2, 128)] v5 104 (rt_live RT Σ3) v1 48 ART10 LV10 ltac:(cbn [app In]; do 1 right; exact INP_v1_6)) as DJ_v5_v1; apply (wg_keep_seg _ m28 m29 _ _ KF149 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v1 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ5) v1 48 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v7_v1; apply (wg_keep_seg _ m28 m29 _ _ KF150 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  pose proof (wg_live_apart RT AF Σ11 m22 [] v11 56 (rt_live RT Σ7) v1 48 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v11_v1; apply (wg_keep_seg _ m28 m29 _ _ G14_CL0 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v1 PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ].
Qed.
End ossl_property_string_data_new_cps.
