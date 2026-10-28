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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_env Fz_M_zalloc Th_mutex Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst.
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

Definition e_ossl_decoder_cache_new : Z := 0x3155a0.
Definition SITE_ossl_decoder_cache_new_1 : Z := 0x3155e0.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_2 : Z := 0x3155f0.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_3 : Z := 0x315620.     (* [comment removed for export] *)
Definition SITE_ossl_decoder_cache_new_4 : Z := 0x315648.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j1 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 3233248) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 16) (Z_to_bv 64 667872) (Z_to_bv 64 775) a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2080544) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_decoder_cache_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3155a0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep.
  do 5 zstore.
  do 9 zstep.
  unfold ossl_decoder_cache_new_s0_post. apply evt_done. do 2 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (jbr1_1 j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j2 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 3233264) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2055740) fc1 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 16 j2]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_decoder_cache_new_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (jbr1_1 j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 16 jbr1_1] ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 jbr1_1 j1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x3155e0) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 UT HBr1 ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  do 2 zstep.
  unfold ossl_decoder_cache_new_s1_post. apply evt_done. do 2 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j2 j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j3 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 3233312) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 3233504) (Z_to_bv 64 3233892) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2096816) fc2 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 16); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); CB 8 j3]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_decoder_cache_new_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (j2 j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 16 j2] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0))) = false ->
  (bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j2 j1 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x3155f0) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR2_1 BR2_3 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 16); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR2_3.
  do 5 zstep.
  unfold ossl_decoder_cache_new_s2_post. apply evt_done. do 2 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (j3 j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 3233352) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 3240060) (Z_to_bv 64 3240092) (Z_to_bv 64 3240124) (Z_to_bv 64 3240156) b5_3 b6_3 b7_3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2096640) fc3 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); CB 8 j3]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_decoder_cache_new_s3_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (j3 j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 8 j3] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j3 j1 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x315620) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv3 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 9 zstep.
  unfold ossl_decoder_cache_new_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_decoder_cache_new_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (j3 j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_4 u1_4 u2_4 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (ret_pc ra) fc4 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 16); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_decoder_cache_new_s4_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (j3 j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 (Z_to_bv 64 v2); CB 8 j3] ->
  rw_cells asegs m (bv_unsigned sp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 16 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 16 <= 2 ^ 47 ->
  v1 + 16 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0))) = true ->
  mem_inv asegs m ->
  evt asegs (ossl_decoder_cache_new_s4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v4 j3 j1 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x315648) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR4_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 16); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR4_2.
  do 8 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_decoder_cache_new_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_decoder_cache_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_malloc : crypto_malloc_env_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.
Hypothesis C_OPENSSL_LH_new : OPENSSL_LH_new_stmt RT.
Hypothesis C_OPENSSL_LH_set_thunks : OPENSSL_LH_set_thunks_keep_stmt RT.

Definition ossl_decoder_cache_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x230 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_decoder_cache_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new); (SITE_ossl_decoder_cache_new_4, e_ossl_decoder_cache_new); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new)]
                      [(SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc); (SITE_ossl_decoder_cache_new_2, e_lock_new); (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new); (SITE_ossl_decoder_cache_new_4, e_OPENSSL_LH_set_thunks); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> mcost 16 + 1 + mcost 104 + mcost 128 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_decoder_cache_new m)))
    (fun c => exists (Σ' : rts RT) (q1 q2 q3 q4 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 16
           /\ acc asegs m' q1 16
           /\ wr_at asegs m' q2 40
           /\ acc asegs m' q2 40
           /\ wr_at asegs m' q3 104
           /\ acc asegs m' q3 104
           /\ wr_at asegs m' q4 128
           /\ acc asegs m' q4 128
           /\ rw_cells asegs m' q1 [C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q3)]
           /\ rw_cells asegs m' q2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q4 [CB 128 (repeat (Z_to_bv 8 0) 128)]
           /\ rw_cells asegs m' q3 [C8 (Z_to_bv 64 q4); C8 (Z_to_bv 64 3233892); C8 (Z_to_bv 64 3233504); C8 (Z_to_bv 64 3240060); C8 (Z_to_bv 64 3240092); C8 (Z_to_bv 64 3240124); C8 (Z_to_bv 64 3240156); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]) c
       /\ rt_live RT Σ' = (q4, 128) :: (q3, 104) :: (q2, 40) :: (q1, 16) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 16 + 1 + mcost 104 + mcost 128) /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 16 < USTACK_TOP /\ 0 < q2 /\ q2 mod 16 = 0 /\ q2 + 40 < USTACK_TOP /\ 0 < q3 /\ q3 mod 16 = 0 /\ q3 + 104 < USTACK_TOP /\ 0 < q4 /\ q4 mod 16 = 0 /\ q4 + 128 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_decoder_cache_new_cps : ossl_decoder_cache_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 < usp - 48 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-48) EU1.
  assert (WHLO : lo <= usp - 48) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (wg_mcost_nonneg 104) as MC_104.
  pose proof (wg_mcost_nonneg 128) as MC_128.
  pose proof (wg_mcost_nonneg 16) as MC_16.
  (* [comment removed for export] *)
  pose proof (ossl_decoder_cache_new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST WHLO WHIMG WHTOP UT SHC MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j1 & m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1', H1_0.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV1.
  clear H1_1 ENV.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_decoder_cache_new e_CRYPTO_malloc SITE_ossl_decoder_cache_new_1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
              (proj1 CGH (SITE_ossl_decoder_cache_new_1, e_ossl_decoder_cache_new) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_decoder_cache_new_1, e_CRYPTO_malloc) ltac:(wp_in_lit)) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 j1; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H1_0))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CRYPTO_malloc Σ PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_1) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 16) (Z_to_bv 64 667872) (Z_to_bv 64 775) a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 16 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { clear - EU1 ST1 LOW SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_decoder_cache_new_1) by (unfold SITE_ossl_decoder_cache_new_1; clear; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { clear - Hlen; lia. }
  { clear - Hcr MC_104 MC_128 MC_16; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV2 & FRS2 & SP2 & CR2 & P0_v1 & P16_v1 & PU_v1 & CG2).
  wp_box1 PU_v1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & G1_ENVp & G1_WR & G1_ACC) & Hc2'). clear Hc2.
  destruct RS2 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & F1 & fc1 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_decoder_cache_new_1) in Hc2' by (unfold SITE_ossl_decoder_cache_new_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
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
  assert (CTXb2 : cg_ctx (rt_cg RT Σ1) e_ossl_decoder_cache_new (bv_unsigned ra :: outer)) by (rewrite CGc2; exact CTX).
  assert (CGH2 : cg_has (rt_cg RT Σ1) _ _) by (rewrite CGc2; exact CGH).
  assert (INP_v1_2 : In (v1, 16) (rt_live RT Σ1)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 v1 16 ART2 INP_v1_2) as (_ & PHI_v1 & _). rewrite SPc2 in PHI_v1.
  pose proof (afp_live_mem RT GOBJ AFP Σ1 m2 v1 16 ART2 INP_v1_2 ltac:(clear; lia)) as (_ & PT_v1).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 16 ART2 INP_v1_2 ltac:(clear; lia)) as PHH_v1.
  pose proof (wg_mod16_8 _ P16_v1) as PAL_v1. assert (PR64_v1 : 0 <= v1 < 2 ^ 64) by (first [clear - PHH_v1 PT_v1; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v1 : v1 + 16 <= lo) by (first [clear - PHI_v1 LOW2; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v1. wp_box1 PAL_v1. wp_box1 PR64_v1.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ1 m2 v1 16 ART2 INP_v1_2) as (WR_v1_3 & ACC_v1_3).
  destruct (wr_at_rw_CB m2 v1 16 WR_v1_3 ltac:(lia)) as (jbr1_1 & HB_v1_3). change (Z.to_nat 16) with 16%nat in HB_v1_3.
  (* [comment removed for export] *)
  pose proof (ossl_decoder_cache_new_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 jbr1_1 j1 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 SHC2 PR64_v1 UT2 HB_v1_3 ACC_v1_3 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j2 & m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & H3_2 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_1.
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 48 [] ART2 ltac:(rewrite SPc2; clear - NUM; lia) ltac:(clear - NUM; lia) MU3); [|exact WM3].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary G1_ENVp MU3 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV3.
  clear KF1 H3_2 G1_ENVp.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ossl_decoder_cache_new e_lock_new SITE_ossl_decoder_cache_new_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb2
              (proj1 CGH2 (SITE_ossl_decoder_cache_new_2, e_ossl_decoder_cache_new) ltac:(wp_in_lit)) (proj2 CGH2 (SITE_ossl_decoder_cache_new_2, e_lock_new) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 j1; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H3_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_lock_new Σ1 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_2) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 2147450880) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART3 MI3).
  { clear - EU1 ST3 LOW2 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST3 LOW2 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_decoder_cache_new_2) by (unfold SITE_ossl_decoder_cache_new_2; clear; lia). exact CTXc3. }
  { exact UWCc3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH2); vm_compute; reflexivity. }
  { first [exact Hfr2 | clear - Hfr2; lia]. }
  { clear - Hlen LENc2; lia. }
  { clear - Hcr CR2 MC_104 MC_128 MC_16; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_MX & G2_ACC) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_decoder_cache_new_2) in Hc4' by (unfold SITE_ossl_decoder_cache_new_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; cbv beta in Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  assert (KF2 : rw_cells asegs m4 v1 [CB 16 j2]) by (apply (wg_keep_live _ _ _ _ m3 m4 v1 16 _ _ H3_0 PRES4 WM4 INP_v1_2); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H3_1 AGc4 WM4 KF3.
  clear H3_0 H3_1 AGc4 CTXc3 UWCc3.
  assert (SPc4 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP4; exact SPc2).
  assert (CGc4 : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite CG4; exact CGc2).
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ1)) + 1) by (rewrite LV4; clear; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 2) by (clear - LEN4 LENc2; lia). clear LENc2. wp_box1 LEN2. wp_box1 CR4.
  assert (Hfr4 : (length (rt_frames RT Σ2) < FRAMES_MAX)%nat) by (rewrite FRS4; exact Hfr2).
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_decoder_cache_new (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v1_4 : In (v1, 16) (rt_live RT Σ2)) by (rewrite LV4; do 1 right; exact INP_v1_2).
  assert (INP_v2_4 : In (v2, 40) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 40 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(clear; lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 40 ART4 INP_v2_4 ltac:(clear; lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (first [clear - PHH_v2 PT_v2; unfold USTACK_TOP in *; lia | unfold USTACK_TOP in *; lia]).
  assert (PSTK_v2 : v2 + 40 <= lo) by (first [clear - PHI_v2 LOW4; unfold STACK_WIN in *; lia | unfold STACK_WIN in *; lia]).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (af_acc_live RT AF Σ2 m4 v1 16 ART4 INP_v1_4) as (WR_v1_5 & ACC_v1_5).
  (* [comment removed for export] *)
  pose proof (ossl_decoder_cache_new_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j2 j1 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF2 KF3 SHC4 PR64_v1 PR64_v2 UT4 ACC_v1_5 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (j3 & m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & H5_2 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5', H5_1.
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 48 [(v1, v1 + 16)] ART4 ltac:(rewrite SPc4; clear - NUM; lia) ltac:(clear - NUM; lia) MU5); [|exact WM5].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 16; split; [exact INP_v1_4 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF4 : rw_cells asegs m5 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 16 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m4 m5 _ _ G2_MX MU5 WM5); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia])) as ENV5.
  clear KF2 KF3 G2_MX H5_2 G2_ENVp.
  assert (AGs5 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AGs5) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ2) e_ossl_decoder_cache_new e_OPENSSL_LH_new SITE_ossl_decoder_cache_new_3 m5 m5 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb4
              (proj1 CGH4 (SITE_ossl_decoder_cache_new_3, e_ossl_decoder_cache_new) ltac:(wp_in_lit)) (proj2 CGH4 (SITE_ossl_decoder_cache_new_3, e_OPENSSL_LH_new) ltac:(wp_in_lit)) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [CB 8 j1; C8 s3; C8 s2; C8 s1])) by (clear; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -48) [CB 8 j1; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H5_1))
              ltac:(rewrite EU1; clear; fold usp; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_new Σ2 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_3) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 3233504) (Z_to_bv 64 3233892) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2
           F2 fc2 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART5 MI5).
  { clear - EU1 ST5 LOW4 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_decoder_cache_new_3) by (unfold SITE_ossl_decoder_cache_new_3; clear; lia). exact CTXc5. }
  { exact UWCc5. }
  { apply (cg_has_weaken _ _ _ _ _ CGH4); vm_compute; reflexivity. }
  { clear - Hlen LENc4; lia. }
  { clear - Hcr CR2 CR4 MC_104 MC_128 MC_16; (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV5. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & v3 & w3_2 & Hc6 & LV6 & FRS6 & SP6 & CR6 & P0_v3 & P16_v3 & PU_v3 & P0_w3_2 & P16_w3_2 & PU_w3_2 & CG6).
  wp_box1 PU_v3. wp_box1 PU_w3_2.
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & G3_ENVp & G3_WR_v1 & G3_ACC_v1 & G3_WR_v2 & G3_ACC_v2 & G3_CL0 & G3_CL2) & Hc6'). clear Hc6.
  destruct RS6 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & F3 & fc3 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ossl_decoder_cache_new_3) in Hc6' by (unfold SITE_ossl_decoder_cache_new_3; clear; first [reflexivity | lia]).
  assert (AGc6 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu6 : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6) by (intros a Ha; cbv beta in Ha; exact (AGc6 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AGu6) as UWF6.
  assert (KF5 : rw_cells asegs m6 v1 [C8 (Z_to_bv 64 v2); CB 8 j3]) by (apply (wg_keep_live _ _ _ _ m5 m6 v1 16 _ _ H5_0 PRES6 WM6 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H5_1 AGc6 WM6 KF6.
  assert (KF7 : rw_cells asegs m6 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m5 m6 v2 40 _ _ KF4 PRES6 WM6 INP_v2_4); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H5_0 H5_1 KF4 AGc6 CTXc5 UWCc5.
  assert (SPc6 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite SP6; exact SPc4).
  assert (CGc6 : rt_cg RT Σ3 = rt_cg RT Σ) by (rewrite CG6; exact CGc4).
  assert (LOW6 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SPc6; exact LOW).
  assert (LEN6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ2)) + 2) by (rewrite LV6; clear; cbn [length]; lia).
  assert (LENc6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ)) + 4) by (clear - LEN6 LENc4; lia). clear LENc4. wp_box1 LEN4. wp_box1 CR6.
  assert (Hfr6 : (length (rt_frames RT Σ3) < FRAMES_MAX)%nat) by (rewrite FRS6; exact Hfr4).
  assert (CTXb6 : cg_ctx (rt_cg RT Σ3) e_ossl_decoder_cache_new (bv_unsigned ra :: outer)) by (rewrite CGc6; exact CTX).
  assert (CGH6 : cg_has (rt_cg RT Σ3) _ _) by (rewrite CGc6; exact CGH).
  assert (INP_v1_6 : In (v1, 16) (rt_live RT Σ3)) by (rewrite LV6; do 2 right; exact INP_v1_4).
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
  pose proof (ossl_decoder_cache_new_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_3) u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 j3 j1 F3 fc3 m6 lo
                ST6 WHLO WHIMG WHTOP KF5 KF6 SHC6 PR64_v1 PR64_v2 PR64_v3 UT6 MI6) as W7.
  cl_lift W7 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & H7_0 & H7_1 & H7_2 & ST7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7', H7_1.
  assert (ART7 : ART RT Σ3 m7).
  { apply (wg_seg_ART RT AF Σ3 m6 m7 usp 48 [] ART6 ltac:(rewrite SPc6; clear - NUM; lia) ltac:(clear - NUM; lia) MU7); [|exact WM7].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF8 : rw_cells asegs m7 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m6 m7 _ _ KF7 MU7 WM7); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF9 : rw_cells asegs m7 v3 [C8 (Z_to_bv 64 w3_2); C8 (Z_to_bv 64 3233892); C8 (Z_to_bv 64 3233504); CB 32 (repeat (Z_to_bv 8 0) 32); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 8); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL0 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF10 : rw_cells asegs m7 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL2 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m6 m7 _ canary G3_ENVp MU7 ltac:(first [solve [clear - NUM; cl_fp_lia] | cl_fp_lia])) as ENV7.
  clear KF5 KF6 KF7 G3_CL0 G3_CL2 H7_2 G3_ENVp.
  assert (AGs7 : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7) by (intros a Ha; apply MU7; first [clear - Ha NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]).
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AGs7) as UWF7.
  (* [comment removed for export] *)
  apply (C_OPENSSL_LH_set_thunks Σ3 PMc (Z_to_bv 64 SITE_ossl_decoder_cache_new_4) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 3240060) (Z_to_bv 64 3240092) (Z_to_bv 64 3240124) (Z_to_bv 64 3240156) b5_3 b6_3 b7_3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v1 ≫ 3 + 2147450880)) s4 s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
           F3 fc3 m7 lo v3 (Z_to_bv 64 w3_2) (Z_to_bv 64 3233892) (Z_to_bv 64 3233504) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256) FDO MST eq_refl eq_refl ART7 MI7).
  { clear - EU1 ST7 LOW6 SPA HSTK NUM. fold usp in SPA. cl_call_ok EU1 ST7 LOW6 SPA 3. }
  { rewrite EU1. clear - HSTK. unfold RT_STACK in *. lia. }
  { exact INP_v3_6. }
  { exact P16_v3. }
  { exact KF9. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & G4_CL0) & Hc8'). clear Hc8.
  destruct RS8 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & F4 & fc4 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ossl_decoder_cache_new_4) in Hc8' by (unfold SITE_ossl_decoder_cache_new_4; clear; first [reflexivity | lia]).
  assert (AGc8 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES8; [left; clear - H1 H2 Hx; unfold USTACK_TOP in *; lia|]. first [clear - H1 H2 Hx NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I]. }
  assert (AGu8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; cbv beta in Ha; exact (AGc8 (bv_unsigned a) 1 ltac:(clear - Ha; cbv beta; lia) ltac:(clear - Ha; cbv beta; unfold USTACK_TOP in *; lia) a ltac:(clear - Ha; cbv beta; lia))).
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AGu8) as UWF8.
  assert (KF11 : rw_cells asegs m8 v1 [C8 (Z_to_bv 64 v2); CB 8 j3]) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 16 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_live _ _ _ _ m7 m8 v1 16 _ _ H7_0 PRES8 WM8 INP_v1_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H7_1 AGc8 WM8 KF12.
  assert (KF13 : rw_cells asegs m8 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v2 40 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_live _ _ _ _ m7 m8 v2 40 _ _ KF8 PRES8 WM8 INP_v2_6); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF15 : rw_cells asegs m8 w3_2 [CB 128 (repeat (Z_to_bv 8 0) 128)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v3 104 ART6 LV6 ltac:(cbn [app In]; left; reflexivity)) as DJ_w3_2_v3; apply (wg_keep_live _ _ _ _ m7 m8 w3_2 128 _ _ KF10 PRES8 WM8 INP_w3_2_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v3 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  clear H7_0 H7_1 KF8 KF9 KF10 AGc8.
  destruct (af_client_consts RT AF Σ3 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  assert (ENV8 : cl_env m8 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v3 + 24, v3 + 56)]) by cl_fp_lia. apply (cl_env_agree m7 m8 _ _ ENV7). intros a Ha. apply PRES8; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ3 m8 v1 16 ART8 INP_v1_6) as (WR_v1_9 & ACC_v1_9).
  (* [comment removed for export] *)
  pose proof (ossl_decoder_cache_new_s4_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_decoder_cache_new_4) u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v3 j3 j1 F4 fc4 m8 lo
                ST8 WHLO WHIMG WHTOP KF11 KF12 SHC8 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) UT8 ACC_v1_9 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI8) as W9.
  cl_lift W9 Hc8' c9 Hc9.
  apply Hk. exists Σ3, v1, v2, v3, w3_2.
  split; [| split; [rewrite LV6, LV4, LV2; reflexivity|]; split; [rewrite FRS6, FRS4, FRS2; reflexivity|]; split; [rewrite SP6, SP4, SP2; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v1|]; split; [exact P16_v1|]; split; [exact PU_v1|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; split; [exact P0_v3|]; split; [exact P16_v3|]; split; [exact PU_v3|]; split; [exact P0_w3_2|]; split; [exact P16_w3_2|]; split; [exact PU_w3_2|]; rewrite CG6, CG4, CG2; reflexivity].
  apply (ASTA_conseq RT Σ3 PMc _ _ c9 Hc9). intros ms9 (m9 & -> & MU9 & WM9 & MI9 & H9_0 & H9_1 & ST9). fold usp in MU9, ST9.
  exists m9.
  split; [exists u0_4, u1_4, u2_4, (Z_to_bv 64 (v1 + 8)), (Z_to_bv 64 0), b3_4, b4_4, b5_4, b6_4, b7_4, u3_4, u4_4, u5_4, u6_4, F4, fc4; reflexivity|].
  assert (ART9 : ART RT Σ3 m9).
  { apply (wg_seg_ART RT AF Σ3 m8 m9 usp 48 [(v1, v1 + 16)] ART8 ltac:(rewrite SPc6; clear - NUM; lia) ltac:(clear - NUM; lia) MU9); [|exact WM9].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 16; split; [exact INP_v1_6 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART9|]; split; [exact MI9|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 WM9)))))))) | exact ST9]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 1 right; exact He | rewrite FRS2; intros e He; exact He | clear; lia]).
    assert (NA_v1 : ~ (v1 <= bv_unsigned a < v1 + 16)) by exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(v1, 16)] v1 16 usp _ ART2 LV2 ltac:(left; reflexivity) FRS2 SP2 ltac:(clear - NUM; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha).
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
    wp_box1 Ha3.
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(clear - NUM HSTK; unfold RT_STACK in *; lia) ltac:(clear; lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
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
  pose proof (af_acc_live RT AF Σ3 m9 v1 16 ART9 INP_v1_6) as (WRE_v1 & ACCE_v1).
  pose proof (af_acc_live RT AF Σ3 m9 v2 40 ART9 INP_v2_6) as (WRE_v2 & ACCE_v2).
  pose proof (af_acc_live RT AF Σ3 m9 v3 104 ART9 INP_v3_6) as (WRE_v3 & ACCE_v3).
  pose proof (af_acc_live RT AF Σ3 m9 w3_2 128 ART9 INP_w3_2_6) as (WRE_w3_2 & ACCE_w3_2).
  split; [exact (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(first [solve [clear - NUM PHH_v1; cl_fp_lia] | cl_fp_lia]))|].
  split; [exact WRE_v1|].
  split; [exact ACCE_v1|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  split; [exact WRE_v3|].
  split; [exact ACCE_v3|].
  split; [exact WRE_w3_2|].
  split; [exact ACCE_w3_2|].
  split; [exact H9_0|].
  split; [pose proof (wg_live_apart RT AF Σ2 m4 [] v2 40 (rt_live RT Σ1) v1 16 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m8 m9 _ _ KF13 MU9 WM9); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  split; [pose proof (wg_live_apart RT AF Σ3 m6 [] w3_2 128 ((v3, 104) :: rt_live RT Σ2) v1 16 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_w3_2_v1; apply (wg_keep_seg _ m8 m9 _ _ KF15 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_w3_2_v1 PHI_w3_2 PT_w3_2 PHH_w3_2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]|].
  pose proof (wg_live_apart RT AF Σ3 m6 [(w3_2, 128)] v3 104 (rt_live RT Σ2) v1 16 ART6 LV6 ltac:(cbn [app In]; do 1 right; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m8 m9 _ _ G4_CL0 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ].
Qed.
End ossl_decoder_cache_new_cps.
