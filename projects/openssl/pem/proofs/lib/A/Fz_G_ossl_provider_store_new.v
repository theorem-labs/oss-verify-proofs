(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Th_mutex Fz_M_locknew Fz_G_OPENSSL_sk_new_null.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
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

Definition e_ossl_provider_store_new : Z := 0x20f5e4.
Definition SITE_ossl_provider_store_new_1 : Z := 0x20f628.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_2 : Z := 0x20f63c.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_3 : Z := 0x20f650.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_4 : Z := 0x20f660.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_5 : Z := 0x20f670.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_6 : Z := 0x20f690.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_7 : Z := 0x20f6b0.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_8 : Z := 0x20f6c4.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_9 : Z := 0x20f6d4.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_10 : Z := 0x20f6e4.     (* [comment removed for export] *)
Definition SITE_ossl_provider_store_new_11 : Z := 0x20f704.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_provider_store_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1
               (Z_to_bv 64 80) (Z_to_bv 64 0x4bfa0) (Z_to_bv 64 312) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20f5e4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI UNT SHADC MINV.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.of_N] in SPR.
  remember (bv_unsigned sp) as usp eqn:EUSP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- EUSP.
  pose proof (munch_refl [(usp + -48, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (UFP : ut_fp [(usp + -48, usp)]) by (clear - LOW LOHI SPHI; ut_fp_lia).
  assert (SFP : sh_fp [(usp + -48, usp)]) by (clear - LOW LOHI SPHI; sh_fp_lia).
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat STK.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. exists m1. rewrite unsigned_lit by lia.
  split; [reflexivity|].
  exact (conj MU (conj WM (conj MINV (conj STK (conj FR SHADC))))).
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s1_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word)
    (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 0x20f7bc) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
          F1 (Z_to_bv 64 e_OPENSSL_sk_new) fc1 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s1_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  acc asegs m v1 80 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 80 <= 2 ^ 47 ->
  v1 + 80 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s1_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x20f628) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI FRAME SHADC V1R UNT STORE ACC V1AL V1LO V1HI V1LT MINV.
  zstep. zstep. wg_F.
  zstep. zstep. zstep.
  apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s2_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word)
    (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_3) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v2) (Z_to_bv 64 0x214514) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 (Z_to_bv 64 v2) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
          F2 (Z_to_bv 64 e_OPENSSL_sk_set_cmp_thunks) fc2 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s2_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s2_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x20f63c) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R UNT MINV.
  do 5 zstep.
  apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s3_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word)
    (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v2) (Z_to_bv 64 0x214540) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 a0 (Z_to_bv 64 v2) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
          F3 (Z_to_bv 64 e_OPENSSL_sk_set_copy_thunks) fc3 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s3_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s3_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x20f650) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R V3R UNT MINV.
  zstep. zstep. zstep. zstep.
  apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s4_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word)
    (v1 v2 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_5) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v2) (Z_to_bv 64 0x2144c4) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 a0 (Z_to_bv 64 v2) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
          F4 (Z_to_bv 64 e_OPENSSL_sk_set_thunks) fc4 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s4_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s4_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v4 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x20f660) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R V4R UNT MINV.
  do 4 zstep. apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s5_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word)
    (v1 v2 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_6) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1)
               (Z_to_bv 64 v5) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 a0 (Z_to_bv 64 v2) (Z_to_bv 64 0x7fff8000)
               s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 e_lock_new) fc5 None m' (seg_rom asegs)
    /\ munch [(v1 + 8, v1 + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s5_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 80 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 80 <= 2 ^ 47 ->
  v1 + 80 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0))) = false ->
  (bv_eqb (Z_to_bv 64 v5) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s5_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v5 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x20f670) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R V5R UNT ACC V1AL V1LO V1HI V1LT ALIGN7 V5NZ MINV.
  pose proof (munch_refl [(v1 + 8, v1 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SFP : sh_fp [(v1 + 8, v1 + 16)]) by (clear - V1LO V1HI; sh_fp_lia).
  zstep. zstep. zstep. zstep.
  zstep. wg_F. zstep.
  zstep. wg_raw V5NZ. zstep.
  apply evt_done. eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MINV (conj STK (conj FRAME (conj STORE SHADC)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s6_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word)
    (v1 v2 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_7) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1)
               (Z_to_bv 64 v6) (Z_to_bv 64 (v1 + 24)) (Z_to_bv 64 0) b3_6 b4_6 b5_6 b6_6 b7_6 a0 (Z_to_bv 64 v2) (Z_to_bv 64 0x7fff8000)
               s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 e_OPENSSL_sk_new_null) fc6 None m' (seg_rom asegs)
    /\ munch [(v1 + 24, v1 + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6);
                             CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s6_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 80 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 80 <= 2 ^ 47 ->
  v1 + 80 <= lo ->
  (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s6_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v5 v6 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x20f690) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R V5R V6R UNT ACC V1AL V1LO V1HI V1LT V6NZ MINV.
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(v1 + 24, v1 + 32)] m) as MU.
  assert (SFP : sh_fp [(v1 + 24, v1 + 32)]) by (clear - V1LO V1HI; sh_fp_lia).
  do 4 zstep. zstep; wg_F.
  zstep. zstep; wg_raw V6NZ. zstep.
  apply evt_done. eexists. split; [reflexivity|].
  refine (conj MU (conj WM (conj MINV (conj STK (conj FRAME (conj _ SHADC)))))). exact STORE.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s7_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word)
    (v1 v2 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v7) (Z_to_bv 64 0x214568) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
          F7 (Z_to_bv 64 e_OPENSSL_sk_set_cmp_thunks) fc7 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s7_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s7_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v5 v6 v7 F7 fc7 lo m)
    (MS (mkR ra7 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
        F7 (Z_to_bv 64 0x20f6b0) fc7 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V2R V5R V6R V7R UNT MINV.
  do 5 zstep. apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s8_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word)
    (v1 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_9) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v7) (Z_to_bv 64 0x214594) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 a0 (Z_to_bv 64 v7) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
          F8 (Z_to_bv 64 e_OPENSSL_sk_set_copy_thunks) fc8 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s8_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s8_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v5 v6 v7 v8 F8 fc8 lo m)
    (MS (mkR ra8 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
        F8 (Z_to_bv 64 0x20f6c4) fc8 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V5R V6R V7R V8R UNT MINV.
  zstep. zstep. zstep. zstep. apply evt_done; split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s9_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word)
    (v1 v5 v6 v7 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_10) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1)
             (Z_to_bv 64 v7) (Z_to_bv 64 0x2144ec) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 a0 (Z_to_bv 64 v7) (Z_to_bv 64 0x7fff8000)
             s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
          F9 (Z_to_bv 64 e_OPENSSL_sk_set_thunks) fc9 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s9_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v5 v6 v7 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s9_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v5 v6 v7 v9 F9 fc9 lo m)
    (MS (mkR ra9 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
        F9 (Z_to_bv 64 0x20f6d4) fc9 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V5R V6R V7R V9R UNT MINV.
  do 4 zstep. apply evt_done. split; [reflexivity | exact SHADC].
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s10_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word)
    (v1 v5 v6 v7 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_provider_store_new_11) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1)
               (Z_to_bv 64 v10) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 a0 (Z_to_bv 64 v7) (Z_to_bv 64 0x7fff8000)
               s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 e_lock_new) fc10 None m' (seg_rom asegs)
    /\ munch [(v1 + 16, v1 + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v6);
                             CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s10_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v5 v6 v7 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 80 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 80 <= 2 ^ 47 ->
  v1 + 80 <= lo ->
  (bv_eqb (Z_to_bv 64 v10) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s10_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v5 v6 v7 v10 F10 fc10 lo m)
    (MS (mkR ra10 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
        F10 (Z_to_bv 64 0x20f6e4) fc10 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V5R V6R V7R V10R UNT ACC V1AL V1LO V1HI V1LT V10NZ MINV.
  assert (SFP : sh_fp [(v1 + 16, v1 + 24)]) by (clear - V1LO V1HI; sh_fp_lia).
  pose proof (munch_refl [(v1 + 16, v1 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep. wg_F.
  zstep. zstep. wg_raw V10NZ. zstep.
  apply evt_done. eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MINV (conj STK (conj FRAME (conj STORE SHADC)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s11_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word)
    (v1 v5 v6 v7 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR ra sp gp tp u0_11 u1_11 u2_11 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 1) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (ret_pc ra) fc11 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v6); C8 (Z_to_bv 64 v11);
                             CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_provider_store_new_s11_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v5 v6 v7 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  0 <= v11 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v1 80 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 80 <= 2 ^ 47 ->
  v1 + 80 <= lo ->
  (bv_eqb (Z_to_bv 64 v11) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s11_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v5 v6 v7 v10 v11 F11 fc11 lo m)
    (MS (mkR ra11 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
        F11 (Z_to_bv 64 0x20f704) fc11 None m (seg_rom asegs)).
Proof.
  intros until lo. intros STK LOW LOHI SPHI STORE FRAME SHADC V1R V5R V6R V7R V10R V11R UNT ACC V1AL V1LO V1HI V1LT V11NZ MINV.
  pose proof (munch_refl [(v1, v1 + 80)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SFP : sh_fp [(v1, v1 + 80)]) by (clear - V1LO V1HI; sh_fp_lia).
  zstep. zstep. zstep. zstep. zstep. wg_F.
  zstep. zstep. wg_raw V11NZ.
  zstep. zstep. zstep. zstep. wg_F.
  zstep.
  zstep. zstep. zstep. zstep. zstep. wg_F.
  zstep. zstep. zstore.
  do 10 zstep.
  pose proof (stk_release asegs _ lo (bv_unsigned sp + -48) _ STK FRAME LOW) as STKUP.
  cbn [cells_size csize Nat.add] in STKUP. replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in STKUP by lia.
  apply evt_done. eexists. split; [reflexivity|].
  refine (conj MU (conj WM (conj MINV (conj STKUP (conj _ SHADC))))). exact STORE.
Qed.

Section ossl_provider_store_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_zalloc : crypto_zalloc_env_stmt RT.
Hypothesis C_OPENSSL_sk_new : OPENSSL_sk_new_stmt RT.
Hypothesis C_OPENSSL_sk_set_cmp_thunks : OPENSSL_sk_set_cmp_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_copy_thunks : OPENSSL_sk_set_copy_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_thunks : OPENSSL_sk_set_thunks_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.
Hypothesis C_OPENSSL_sk_new_null : OPENSSL_sk_new_null_stmt RT.

Definition ossl_provider_store_new_stmt : Prop :=
  forall (Σ : rts RT) (PMc : Model -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 12205808 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 560 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_provider_store_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ)
    [(SITE_ossl_provider_store_new_1, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new);
     (SITE_ossl_provider_store_new_3, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_4, e_ossl_provider_store_new);
     (SITE_ossl_provider_store_new_5, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new);
     (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_8, e_ossl_provider_store_new);
     (SITE_ossl_provider_store_new_9, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_10, e_ossl_provider_store_new);
     (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new);
     (SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_ln_zalloc, e_lock_new);
     (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
    [(SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new);
     (SITE_ossl_provider_store_new_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_4, e_OPENSSL_sk_set_copy_thunks);
     (SITE_ossl_provider_store_new_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_6, e_lock_new);
     (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_provider_store_new_8, e_OPENSSL_sk_set_cmp_thunks);
     (SITE_ossl_provider_store_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_10, e_OPENSSL_sk_set_thunks);
     (SITE_ossl_provider_store_new_11, e_lock_new);
     (SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_ln_zalloc, e_CRYPTO_zalloc);
     (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 4 < LIVE_MAX ->
  2 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                         F fc e_ossl_provider_store_new m)))
    (fun c => exists (Σ' : rts RT) (st pv dl cb lk : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 st) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ wr_at asegs m' st 80 /\ acc asegs m' st 80
            /\ rw_cells asegs m' st [C8 a0; C8 (Z_to_bv 64 pv); C8 (Z_to_bv 64 cb); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 lk);
                                    CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]
            /\ rw_cells asegs m' pv [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                    C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]
            /\ rw_cells asegs m' dl (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' cb [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                    C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x214568); C8 (Z_to_bv 64 0x2144ec); C8 (Z_to_bv 64 0x214594)]
            /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)))
         c
       /\ rt_live RT Σ' = (lk, 40) :: (cb, 56) :: (dl, 40) :: (pv, 56) :: (st, 80) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 2
       /\ 0 < st /\ st mod 16 = 0 /\ st + 80 < USTACK_TOP
       /\ pv mod 16 = 0 /\ dl mod 16 = 0 /\ cb mod 16 = 0 /\ lk mod 16 = 0
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_provider_store_new_cps : ossl_provider_store_new_stmt.
Proof using AF AFP C_CRYPTO_zalloc C_OPENSSL_sk_new C_OPENSSL_sk_set_cmp_thunks C_OPENSSL_sk_set_copy_thunks C_OPENSSL_sk_set_thunks C_lock_new C_OPENSSL_sk_new_null.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDFS MSTAB ETP ART0 MINV0 CALL0 ROOM CTX0 UWC0 CGH NFRM NLIVE CRED CLE0 T c ENTRY KONT.
  subst tp.
  pose proof CALL0 as (STK0 & LOWIN & LORT & SPTOP & SPAL).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC0 & _ & _ & UT0).
  set (SP := bv_unsigned sp) in *.
  set (G1 := [(G_ALLOW_CUST, G_ALLOW_CUST + 1)]).
  assert (NUMS : rt_sp0 RT Σ - STACK_WIN <= SP + -48 /\ 0x10007fff8000 <= lo /\ SP <= 2 ^ 47 /\ lo + 65536 + 560 <= SP)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  assert (ESP48 : bv_unsigned (Z_to_bv 64 (SP + -48)) = SP + -48) by (apply unsigned_lit; lia).
  (* helper facts for the call steps below; each step uses only some of them *)
  assert (KEEPSTK : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> x < SP + -48 \/ SP <= x).
  { intros x XR. destruct (aclient_split RT AF Σ m SP x ART0 XR) as [SIDE|SIDE]; [right; exact SIDE | left; lia]. }
  assert (AGR : forall mk, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk -> agree_on (fun x => SP <= x < USTACK_TOP) m mk).
  { intros mk PRESk a ACLa. apply PRESk; [left; exact ACLa | cbn [outside G1]; split; [unfold G_ALLOW_CUST, USTACK_TOP in *; lia | exact I]]. }
  assert (CHAIN : forall mk r G, In (r, e_ossl_provider_store_new) (cg_site (rt_cg RT Σ)) -> In (r, G) (cg_call (rt_cg RT Σ)) ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk ->
            rw_cells asegs mk (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            cg_ctx (rt_cg RT Σ) G (r :: bv_unsigned ra :: outer) /\ uw_chain mk (Z_to_bv 64 (SP + -48)) sp (bv_unsigned ra :: outer)).
  { intros mk r G SITEIN CALLIN PRESk FRk.
    apply (cl_chain_call (rt_cg RT Σ) e_ossl_provider_store_new G r m mk ra s0 sp (Z_to_bv 64 (SP + -48)) outer CTX0 SITEIN CALLIN UWC0 (AGR mk PRESk)).
    - replace (SP - 16) with (SP + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn; lia).
      exact (rw_cells_skip mk (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FRk).
    - rewrite ESP48. lia.
    - exact SPTOP. }
  assert (PRESW : forall mk mk' W, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk -> munch W mk mk' ->
            (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> outside W x) -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk').
  { intros mk mk' W PRESk MUk WOUT a ACLa OUTa. rewrite (MUk a (WOUT _ ACLa)). exact (PRESk a ACLa OUTa). }
  assert (PRESC : forall (Σk : rts RT) mk mk' W, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk ->
            rt_pres_fp (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) W mk mk' ->
            (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σk)) -> rt_frames RT Σk = rt_frames RT Σ ->
            (forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> outside G1 x -> outside W x) ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m mk').
  { intros Σk mk mk' W PRESk PK INL EFR WOUT a ACLa OUTa. rewrite (PK a); [exact (PRESk a ACLa OUTa)| |exact (WOUT _ ACLa OUTa)].
    apply (aclient_mono _ _ _ _ _ _ _ ACLa INL); [rewrite EFR; tauto | lia]. }
  assert (ARTW : forall (Σk : rts RT) mk mk' W, ART RT Σk mk -> rt_sp0 RT Σk = rt_sp0 RT Σ -> munch W mk mk' -> wmono asegs mk mk' ->
            (forall x, ~ outside W x -> aclient (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) x) -> ART RT Σk mk').
  { intros Σk mk mk' W ARTk ESP0 MUk WMk WOUT. apply (af_frame RT AF Σk mk mk' (SP + -48) ARTk ltac:(lia)); [|exact WMk].
    intros a ACLa. apply MUk. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. exact (ACLa (WOUT _ O)). }
  assert (KEEPC : forall (Σk : rts RT) mk mk' W X cs, rw_cells asegs mk X cs ->
            rt_pres_fp (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) W mk mk' -> wmono asegs mk mk' ->
            (forall x, X <= x < X + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) x /\ outside W x) ->
            rw_cells asegs mk' X cs).
  { intros Σk mk mk' W X cs CELLS PK WMk XIN. apply (rw_cells_agree asegs mk mk' X cs CELLS); [|exact WMk].
    intros a ACLa. destruct (XIN _ ACLa) as [ARTk HO]. exact (PK a ARTk HO). }
  assert (KEEPG : forall (Σk : rts RT) mk mk' X cs, rw_cells asegs mk X cs ->
            rt_pres_fp (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) G1 mk mk' -> wmono asegs mk mk' -> 0x10007fff8000 <= X ->
            (forall x, X <= x < X + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) x) ->
            rw_cells asegs mk' X cs).
  { intros Σk mk mk' X cs CELLS PK WMk XLO XIN. apply (KEEPC Σk mk mk' G1 X cs CELLS PK WMk). intros x XR. split; [exact (XIN x XR)|].
    cbn [outside G1]. split; [unfold G_ALLOW_CUST; lia | exact I]. }
  assert (CLEC : forall (Σk : rts RT) mk mk' W lbk, cl_env mk lbk canary ->
            rt_pres_fp (rt_live RT Σk) (rt_frames RT Σk) (SP + -48) W mk mk' -> (forall x, cl_cell x -> outside W x) -> cl_env mk' lbk canary).
  { intros Σk mk mk' W lbk CLk PK WOUT. apply (cl_env_agree mk mk' lbk canary CLk). intros a ACLa.
    exact (PK a (acl_static _ _ _ _ (cl_cell_static _ ACLa)) (WOUT _ ACLa)). }
  assert (CALLOK : forall (Σk : rts RT) mk, rt_sp0 RT Σk = rt_sp0 RT Σ -> stk asegs mk lo (SP + -48) ->
            call_ok RT Σk mk (Z_to_bv 64 (SP + -48)) lo).
  { intros Σk mk ESP0 STKk. unfold call_ok. rewrite ESP48, ESP0.
    split; [exact STKk|]. split; [exact LOWIN|]. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    clear - SPAL. Z.div_mod_to_equations. lia. }
  (* segment 0: prologue up to CRYPTO_zalloc *)
  pose proof (ossl_provider_store_new_s0_walk ra sp gp (Z_to_bv 64 12205808) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo STK0 ltac:(lia) ltac:(lia) ltac:(lia) UT0 SHC0 MINV0) as W0.
  cl_lift W0 ENTRY c1 AS1.
  destruct (ASTA_unpack RT Σ _ _ c1 AS1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & STK1 & FR1 & SHOFF1) & E1). clear AS1.

  fold SP in MU1, STK1, FR1, E1.
  assert (PRES1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m1).
  { apply (PRESW m m1 _ (pres_fp_refl _ _ _ _ m) MU1). intros x XR. cbn [outside]. split; [|exact I]. specialize (KEEPSTK x XR). lia. }
  assert (ART1 : ART RT Σ m1).
  { apply (ARTW Σ m m1 _ ART0 eq_refl MU1 WM1). intros x XR. destruct (wg_not_outside_cons _ _ _ _ XR) as [INW|NOUT]; [|exfalso; exact (NOUT I)].
    apply acl_stack. unfold USTACK_TOP in *. lia. }
  pose proof (cl_env_seg _ m m1 lb canary CLE0 MU1 ltac:(cl_fp_lia)) as CLE1.
  destruct (CHAIN m1 SITE_ossl_provider_store_new_1 e_CRYPTO_zalloc (proj1 CGH (SITE_ossl_provider_store_new_1, e_ossl_provider_store_new) ltac:(cbn [In]; tauto))
             (proj2 CGH (SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc) ltac:(cbn [In]; tauto)) PRES1 FR1)
    as (CTX1 & UWC1).
  apply (C_CRYPTO_zalloc Σ PMc (Z_to_bv 64 SITE_ossl_provider_store_new_1) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) t0 t1 t2 sp s1
           (Z_to_bv 64 80) (Z_to_bv 64 311200) (Z_to_bv 64 312) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 80 lo (bv_unsigned ra :: outer) lb canary FDFS MSTAB eq_refl eq_refl ltac:(lia) ART1 MI1 (CALLOK Σ m1 eq_refl STK1)
           ltac:(rewrite ESP48; unfold RT_STACK in *; lia)
           ltac:(rewrite (unsigned_lit SITE_ossl_provider_store_new_1) by (unfold SITE_ossl_provider_store_new_1; lia); exact CTX1)
           UWC1 (cg_has_weaken _ _ _ [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
             [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] CGH eq_refl eq_refl) ltac:(lia) ltac:(unfold mcost; cbn; lia) CLE1 T c1 E1).
  intros c2 (Σ1 & v1 & AS2 & LV1 & FRM1 & SP01 & CR1 & V1P & V1A & V1T & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 AS2) as (ms2 & (m2 & RET2 & (ART2 & MI2 & WM2 & STK2) & PK2 & CLE2 & WR2 & ACC2 & ZERO2) & E2). clear AS2.
  destruct RET2 as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F2 & fc2 & ->).

  rewrite ESP48 in STK2, PK2.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_1) in E2 by (unfold SITE_ossl_provider_store_new_1; lia).
  assert (IN1 : In (v1, 80) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 80 ART2 IN1 ltac:(lia)) as V1HI.
  destruct (af_live_range RT AF Σ1 m2 v1 80 ART2 IN1) as (_ & V1END & _). rewrite SP01 in V1END.
  assert (V1B : 0x10007fff8000 <= v1 /\ v1 + 80 <= lo /\ v1 + 80 <= 2 ^ 47 /\ 0 <= v1 < 2 ^ 64 /\ v1 mod 8 = 0).
  { split; [exact V1HI|]. split; [lia|]. split; [unfold USTACK_TOP in *; lia|]. split; [unfold USTACK_TOP in *; lia|]. exact (wg_mod16_8 v1 V1A). }
  assert (PRES2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m2)
    by (apply (PRESC Σ m1 m2 _ PRES1 PK2 (fun e CELLS => CELLS) eq_refl); intros x _ OUTa; exact OUTa).
  assert (FR2 : rw_cells asegs m2 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ m1 m2 _ _ _ FR1 PK2 WM2). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply acl_stack; unfold USTACK_TOP in *; lia | cbn [outside]; split; [unfold G_ALLOW_CUST; lia | exact I]]. }
  assert (ST2 : rw_cells asegs m2 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (rw_cells_recast m2 v1 _ _ (wp_zero_rw_CB asegs m2 v1 80 ZERO2 WR2 ltac:(lia))); [cbn; tauto | reflexivity]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (ossl_provider_store_new_s1_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_1) x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 v1 F2 fc2 m2 lo
                STK2 ltac:(lia) ltac:(lia) ltac:(lia) FR2 SHC2 ltac:(lia) UT2 ST2 ACC2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MI2) as W1.
  cl_lift W1 E2 c3 AS3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 AS3) as (ms3 & (-> & SHOFF3) & EN3). clear AS3.
  destruct (CHAIN m2 SITE_ossl_provider_store_new_2 e_OPENSSL_sk_new (proj1 CGH (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new) ltac:(cbn [In]; tauto))
             (proj2 CGH (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new) ltac:(cbn [In]; tauto)) PRES2 FR2)
    as (CTX2 & UWC2).
  apply (C_OPENSSL_sk_new Σ1 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_2) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) x0 x1 x2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 0x20f7bc) y1 y2 y3 y4 y5 y6 y7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
           F2 fc2 m2 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDFS MSTAB eq_refl ART2 MI2 (CALLOK Σ1 m2 SP01 STK2)
           ltac:(rewrite ESP48; unfold RT_STACK in *; lia)
           ltac:(rewrite CG1, (unsigned_lit SITE_ossl_provider_store_new_2) by (unfold SITE_ossl_provider_store_new_2; lia); exact CTX2)
           UWC2
           ltac:(rewrite CG1; exact (cg_has_weaken _ _ _
                   [(SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                   [(SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] CGH eq_refl eq_refl))
           ltac:(rewrite LV1; cbn [length]; lia) ltac:(rewrite CR1; unfold mcost; cbn; lia) CLE2 T c3 EN3).
  intros c4 (Σ2 & v2 & AS4 & LV2 & FRM2 & SP02 & CR2 & V2P & V2A & V2T & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 AS4) as (ms4 & (m3 & RET4 & (ART3 & MI3 & WM3 & STK3) & PK3 & CLE3 & WR3 & ACC3 & SK3) & E4). clear AS4.
  destruct RET4 as (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & F4 & fc4 & ->).

  rewrite ESP48 in STK3, PK3.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_2) in E4 by (unfold SITE_ossl_provider_store_new_2; lia).
  assert (LV2' : rt_live RT Σ2 = [(v2, 56); (v1, 80)] ++ rt_live RT Σ) by (rewrite LV2, LV1; reflexivity).
  assert (FRM2' : rt_frames RT Σ2 = rt_frames RT Σ) by (rewrite FRM2; exact FRM1).
  assert (SP02' : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP02; exact SP01).
  assert (IN2 : In (v2, 56) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  assert (IN1' : In (v1, 80) (rt_live RT Σ2)) by (rewrite LV2; right; exact IN1).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m3 v2 56 ART3 IN2 ltac:(lia)) as V2HI.
  destruct (af_live_range RT AF Σ2 m3 v2 56 ART3 IN2) as (_ & V2END & _). rewrite SP02' in V2END.
  pose proof (af_live_disj RT AF Σ2 m3 v2 56 v1 80 [] (rt_live RT Σ1) ART3 LV2 IN1) as D21. wp_box1 D21.
  assert (PRES3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m3).
  { apply (PRESC Σ1 m2 m3 _ PRES2 PK3); [intros e INe; rewrite LV1; right; exact INe | exact FRM1 | intros x _ OUTa; exact OUTa]. }
  assert (FR3 : rw_cells asegs m3 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ1 m2 m3 _ _ _ FR2 PK3 WM3). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply acl_stack; unfold USTACK_TOP in *; lia | cbn [outside]; split; [unfold G_ALLOW_CUST; lia | exact I]]. }
  assert (ST3 : rw_cells asegs m3 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ1 m2 m3 _ _ _ ST2 PK3 WM3). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply (acl_live _ _ _ v1 80); [exact IN1 | lia] | cbn [outside]; split; [unfold G_ALLOW_CUST; lia | exact I]]. }
  destruct (af_client_consts RT AF Σ2 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  assert (CLOUT2 : forall x, cl_cell x -> outside [(v2, v2 + 56)] x).
  { intros x XR. pose proof (client_static_range x (cl_cell_static x XR)). cbn [outside]. split; [unfold SEGTOP_A in *; lia | exact I]. }
  pose proof (ossl_provider_store_new_s2_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_2) z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 v1 v2 F4 fc4 m3 lo
                STK3 ltac:(lia) ltac:(lia) ltac:(lia) ST3 FR3 SHC3 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) UT3 MI3) as W2.
  cl_lift W2 E4 c5 AS5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 AS5) as (ms5 & (-> & SHOFF5) & EN5). clear AS5.
  assert (ALN2 : negb (bv_eqb (Z_to_bv 64 (Z.land v2 7)) (Z_to_bv 64 0)) = false)
    by (rewrite (wg_land7 v2) by lia; rewrite (wg_mod16_8 v2 V2A); reflexivity).
  apply (C_OPENSSL_sk_set_cmp_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_3) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) z0 z1 z2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 0x214514) w2 w3 w4 w5 w6 w7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           z3 z4 z5 z6 F4 fc4 m3 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x20f7bc)
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDFS MSTAB eq_refl eq_refl ART3 MI3 (CALLOK Σ2 m3 SP02' STK3)
           ltac:(rewrite ESP48; lia) IN2 V2A SK3 ALN2 T c5 EN5).
  intros c6 AS6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 AS6) as (ms6 & (m4 & RET6 & (ART4 & MI4 & WM4 & STK4) & PK4 & SK4) & E6). clear AS6.
  destruct RET6 as (q0 & q1 & q2 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & F6 & fc6 & ->).

  assert (APART2 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> outside [(v2, v2 + 56)] x).
  { intros x XR. cbn [outside]. split; [|exact I].
    exact (wg_newchunk_apart RT AF Σ Σ2 m3 [(v2, 56); (v1, 80)] v2 56 SP x ART3 LV2' (or_introl eq_refl) FRM2' SP02' ltac:(lia) ltac:(lia) XR). }
  assert (OUT2 : forall x, SP + -48 <= x < SP \/ v1 <= x < v1 + 80 -> outside [(v2, v2 + 56)] x)
    by (intros x XR; unfold wp_box in D21; cbn [outside]; split; [lia | exact I]).
  assert (ACL2 : forall x, SP + -48 <= x < SP \/ v1 <= x < v1 + 80 -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (SP + -48) x).
  { intros x [XR|XR]; [apply acl_stack; unfold USTACK_TOP in *; lia | apply (acl_live _ _ _ v1 80); [exact IN1' | lia]]. }
  (* back from OPENSSL_sk_set_cmp_thunks *)
  rewrite ESP48 in STK4, PK4.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_3) in E6 by (unfold SITE_ossl_provider_store_new_3; lia).
  assert (PRES4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m4).
  { apply (PRESC Σ2 m3 m4 _ PRES3 PK4); [intros e INe; rewrite LV2'; apply in_or_app; right; exact INe | exact FRM2' | intros x XR _; exact (APART2 x XR)]. }
  assert (FR4 : rw_cells asegs m4 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ2 m3 m4 _ _ _ FR3 PK4 WM4). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  assert (ST4 : rw_cells asegs m4 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ2 m3 m4 _ _ _ ST3 PK4 WM4). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  pose proof (CLEC Σ2 m3 m4 _ _ CLE3 PK4 CLOUT2) as CLE4.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (ossl_provider_store_new_s3_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_3) q0 q1 q2 r1 r2 r3 r4 r5 r6 r7 q3 q4 q5 q6 v1 v2 v2 F6 fc6 m4 lo
                STK4 ltac:(lia) ltac:(lia) ltac:(lia) ST4 FR4 SHC4 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                UT4 MI4) as W3.
  cl_lift W3 E6 c7 AS7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 AS7) as (ms7 & (-> & SHOFF7) & EN7). clear AS7.
  apply (C_OPENSSL_sk_set_copy_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_4) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) q0 q1 q2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 0x214540) r2 r3 r4 r5 r6 r7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           q3 q4 q5 q6 F6 fc6 m4 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x20f7bc)
           (Z_to_bv 64 0x214514) (Z_to_bv 64 0) (Z_to_bv 64 0) FDFS MSTAB eq_refl eq_refl ART4 MI4 (CALLOK Σ2 m4 SP02' STK4)
           ltac:(rewrite ESP48; lia) IN2 V2A SK4 ALN2 T c7 EN7).
  intros c8 AS8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 AS8) as (ms8 & (m5 & RET8 & (ART5 & MI5 & WM5 & STK5) & PK5 & SK5) & E8). clear AS8.
  destruct RET8 as (k0 & k1 & k2 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & k3 & k4 & k5 & k6 & F8 & fc8 & ->).
  (* back from OPENSSL_sk_set_copy_thunks *)
  rewrite ESP48 in STK5, PK5.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_4) in E8 by (unfold SITE_ossl_provider_store_new_4; lia).
  assert (PRES5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m5).
  { apply (PRESC Σ2 m4 m5 _ PRES4 PK5); [intros e INe; rewrite LV2'; apply in_or_app; right; exact INe | exact FRM2' | intros x XR _; exact (APART2 x XR)]. }
  assert (FR5 : rw_cells asegs m5 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ2 m4 m5 _ _ _ FR4 PK5 WM5). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  assert (ST5 : rw_cells asegs m5 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ2 m4 m5 _ _ _ ST4 PK5 WM5). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  pose proof (CLEC Σ2 m4 m5 _ _ CLE4 PK5 CLOUT2) as CLE5.
  destruct (af_client_consts RT AF Σ2 m5 ART5) as (_ & SHC5 & _ & _ & UT5).
  pose proof (ossl_provider_store_new_s4_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_4) k0 k1 k2 j1 j2 j3 j4 j5 j6 j7 k3 k4 k5 k6 v1 v2 v2 F8 fc8 m5 lo
                STK5 ltac:(lia) ltac:(lia) ltac:(lia) ST5 FR5 SHC5 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                UT5 MI5) as W4.
  cl_lift W4 E8 c9 AS9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 AS9) as (ms9 & (-> & SHOFF9) & EN9). clear AS9.
  apply (C_OPENSSL_sk_set_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_5) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) k0 k1 k2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 0x2144c4) j2 j3 j4 j5 j6 j7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           k3 k4 k5 k6 F8 fc8 m5 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x20f7bc)
           (Z_to_bv 64 0x214514) (Z_to_bv 64 0) (Z_to_bv 64 0x214540) FDFS MSTAB eq_refl eq_refl ART5 MI5 (CALLOK Σ2 m5 SP02' STK5)
           ltac:(rewrite ESP48; lia) IN2 V2A SK5 ALN2 T c9 EN9).
  intros c10 AS10.
  destruct (ASTA_unpack RT Σ2 _ _ c10 AS10) as (ms10 & (m6 & RET10 & (ART6 & MI6 & WM6 & STK6) & PK6 & SK6) & E10). clear AS10.
  destruct RET10 as (h0 & h1 & h2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & h3 & h4 & h5 & h6 & F10 & fc10 & ->).

  (* back from OPENSSL_sk_set_thunks *)
  rewrite ESP48 in STK6, PK6.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_5) in E10 by (unfold SITE_ossl_provider_store_new_5; lia).
  assert (PRES6 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m6).
  { apply (PRESC Σ2 m5 m6 _ PRES5 PK6); [intros e INe; rewrite LV2'; apply in_or_app; right; exact INe | exact FRM2' | intros x XR _; exact (APART2 x XR)]. }
  assert (FR6 : rw_cells asegs m6 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ2 m5 m6 _ _ _ FR5 PK6 WM6). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  assert (ST6 : rw_cells asegs m6 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ2 m5 m6 _ _ _ ST5 PK6 WM6). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL2 | apply OUT2]; lia. }
  pose proof (CLEC Σ2 m5 m6 _ _ CLE5 PK6 CLOUT2) as CLE6.
  destruct (af_client_consts RT AF Σ2 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (proj2 (af_acc_live RT AF Σ2 m6 v1 80 ART6 IN1')) as ACC6.
  assert (ALN1 : negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0)) = false)
    by (rewrite (wg_land7 v1) by lia; rewrite (wg_mod16_8 v1 V1A); reflexivity).
  assert (NZ2 : bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia); apply Z.eqb_neq; lia).
  pose proof (ossl_provider_store_new_s5_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_5) h0 h1 h2 g1 g2 g3 g4 g5 g6 g7 h3 h4 h5 h6 v1 v2 v2 F10 fc10 m6 lo
                STK6 ltac:(lia) ltac:(lia) ltac:(lia) ST6 FR6 SHC6 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                UT6 ACC6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALN1 NZ2 MI6) as W5.
  cl_lift W5 E10 c11 AS11.
  destruct (ASTA_unpack RT Σ2 _ _ c11 AS11) as (ms11 & (m7 & -> & MU7 & WM7 & MI7 & STK7 & FR7 & ST7 & SHOFF11) & E11). clear AS11.
  fold SP in MU7, STK7, FR7, E11.
  assert (APART1 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> ~ (v1 <= x < v1 + 80))
    by (intros x XR; exact (wg_newchunk_apart RT AF Σ Σ2 m6 [(v2, 56); (v1, 80)] v1 80 SP x ART6 LV2' (or_intror (or_introl eq_refl)) FRM2' SP02'
                              ltac:(lia) ltac:(lia) XR)).
  assert (PRES7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m7).
  { apply (PRESW m6 m7 _ PRES6 MU7). intros x XR. pose proof (APART1 x XR). cbn [outside]. split; [lia | exact I]. }
  assert (ART7 : ART RT Σ2 m7).
  { apply (ARTW Σ2 m6 m7 _ ART6 SP02' MU7 WM7). intros x XR. destruct (wg_not_outside_cons _ _ _ _ XR) as [INW|NOUT]; [|exfalso; exact (NOUT I)].
    apply ACL2. lia. }
  pose proof (cl_env_seg _ m6 m7 _ canary CLE6 MU7 ltac:(cl_fp_lia)) as CLE7.
  assert (SKV2 : rw_cells asegs m7 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                       C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (wg_keep_seg _ m6 m7 _ _ SK6 MU7 WM7). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D21. cbn [outside]. split; [lia | exact I]. }
  destruct (CHAIN m7 SITE_ossl_provider_store_new_6 e_lock_new
              (proj1 CGH (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new) ltac:(cbn [In]; tauto))
              (proj2 CGH (SITE_ossl_provider_store_new_6, e_lock_new) ltac:(cbn [In]; tauto)) PRES7 FR7) as (CTX6 & UWC6).
  apply (C_lock_new Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_6) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) h0 h1 h2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) g3 g4 g5 g6 g7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 h3 h4 h5 h6
           F10 fc10 m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDFS MSTAB eq_refl ART7 MI7 (CALLOK Σ2 m7 SP02' STK7)
           ltac:(rewrite ESP48; unfold RT_STACK in *; lia)
           ltac:(rewrite CG2, CG1, (unsigned_lit SITE_ossl_provider_store_new_6) by (unfold SITE_ossl_provider_store_new_6; lia); exact CTX6)
           UWC6
           ltac:(rewrite CG2, CG1; exact (cg_has_weaken _ _ _
                   [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                   [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] CGH eq_refl eq_refl))
           ltac:(rewrite FRM2'; exact NFRM) ltac:(rewrite LV2'; cbn [length app]; lia) ltac:(rewrite CR2, CR1; unfold mcost; cbn; lia)
           CLE7 T c11 E11).
  intros c12 (Σ3 & v6 & AS12 & LV3 & FRM3 & SP03 & CR3 & V6P & V6A & V6T & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c12 AS12) as (ms12 & (m8 & RET12 & (ART8 & MI8 & WM8 & STK8) & PK8 & CLE8 & MX8 & ACC8) & E12). clear AS12.
  destruct RET12 as (f0 & f1 & f2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & f3 & f4 & f5 & f6 & F12 & fc12 & ->).

  (* back from CRYPTO_THREAD_lock_new (default_path_lock) *)
  rewrite ESP48 in STK8, PK8.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_6) in E12 by (unfold SITE_ossl_provider_store_new_6; lia).
  assert (LV3' : rt_live RT Σ3 = [(v6, 40); (v2, 56); (v1, 80)] ++ rt_live RT Σ) by (rewrite LV3, LV2'; reflexivity).
  assert (FRM3' : rt_frames RT Σ3 = rt_frames RT Σ) by (rewrite FRM3; exact FRM2').
  assert (SP03' : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite SP03; exact SP02').
  assert (IN6 : In (v6, 40) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  assert (IN2'' : In (v2, 56) (rt_live RT Σ3)) by (rewrite LV3; right; exact IN2).
  assert (IN1'' : In (v1, 80) (rt_live RT Σ3)) by (rewrite LV3; right; exact IN1').
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m8 v6 40 ART8 IN6 ltac:(lia)) as V6HI.
  destruct (af_live_range RT AF Σ3 m8 v6 40 ART8 IN6) as (_ & V6END & _). rewrite SP03' in V6END.
  pose proof (af_live_disj RT AF Σ3 m8 v6 40 v2 56 [] (rt_live RT Σ2) ART8 LV3 IN2) as D62. wp_box1 D62.
  pose proof (af_live_disj RT AF Σ3 m8 v6 40 v1 80 [] (rt_live RT Σ2) ART8 LV3 IN1') as D61. wp_box1 D61.
  assert (PRES8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m8).
  { apply (PRESC Σ2 m7 m8 _ PRES7 PK8); [intros e INe; rewrite LV2'; apply in_or_app; right; exact INe | exact FRM2' | intros x _ OUTa; exact OUTa]. }
  assert (FR8 : rw_cells asegs m8 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPG Σ2 m7 m8 _ _ FR7 PK8 WM8 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply acl_stack. unfold USTACK_TOP in *. lia. }
  assert (ST8 : rw_cells asegs m8 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPG Σ2 m7 m8 _ _ ST7 PK8 WM8 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v1 80); [exact IN1' | lia]. }
  assert (SKV2' : rw_cells asegs m8 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPG Σ2 m7 m8 _ _ SKV2 PK8 WM8 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v2 56); [exact IN2 | lia]. }
  destruct (af_client_consts RT AF Σ3 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  pose proof (proj2 (af_acc_live RT AF Σ3 m8 v1 80 ART8 IN1'')) as ACC1_8.
  assert (NZ6 : bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia); apply Z.eqb_neq; lia).
  pose proof (ossl_provider_store_new_s6_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_6) f0 f1 f2 d1 d2 d3 d4 d5 d6 d7 f3 f4 f5 f6 v1 v2 v2 v6 F12 fc12 m8 lo
                STK8 ltac:(lia) ltac:(lia) ltac:(lia) ST8 FR8 SHC8 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) UT8 ACC1_8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NZ6 MI8) as W6.
  cl_lift W6 E12 c13 AS13.
  destruct (ASTA_unpack RT Σ3 _ _ c13 AS13) as (ms13 & (m9 & -> & MU9 & WM9 & MI9 & STK9 & FR9 & ST9 & SHOFF13) & E13). clear AS13.
  fold SP in MU9, STK9, FR9, E13.
  assert (PRES9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m9).
  { apply (PRESW m8 m9 _ PRES8 MU9). intros x XR. pose proof (APART1 x XR). cbn [outside]. split; [lia | exact I]. }
  assert (ART9 : ART RT Σ3 m9).
  { apply (ARTW Σ3 m8 m9 _ ART8 SP03' MU9 WM9). intros x XR. destruct (wg_not_outside_cons _ _ _ _ XR) as [INW|NOUT]; [|exfalso; exact (NOUT I)].
    apply (acl_live _ _ _ v1 80); [exact IN1'' | lia]. }
  pose proof (cl_env_seg _ m8 m9 _ canary CLE8 MU9 ltac:(cl_fp_lia)) as CLE9.
  assert (SKV2_9 : rw_cells asegs m9 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (wg_keep_seg _ m8 m9 _ _ SKV2' MU9 WM9). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D21. cbn [outside]. split; [lia | exact I]. }
  assert (MX9 : rw_cells asegs m9 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m8 m9 _ _ MX8 MU9 WM9). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D61. cbn [outside]. split; [lia | exact I]. }
  destruct (CHAIN m9 SITE_ossl_provider_store_new_7 e_OPENSSL_sk_new_null
              (proj1 CGH (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new) ltac:(cbn [In]; tauto))
              (proj2 CGH (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null) ltac:(cbn [In]; tauto)) PRES9 FR9) as (CTX7 & UWC7).
  apply (C_OPENSSL_sk_new_null Σ3 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_7) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) f0 f1 f2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 (v1 + 24)) (Z_to_bv 64 0) d3 d4 d5 d6 d7 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 f3 f4 f5 f6
           F12 fc12 m9 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDFS MSTAB eq_refl ART9 MI9 (CALLOK Σ3 m9 SP03' STK9)
           ltac:(rewrite ESP48; unfold RT_STACK in *; lia)
           ltac:(rewrite CG3, CG2, CG1, (unsigned_lit SITE_ossl_provider_store_new_7) by (unfold SITE_ossl_provider_store_new_7; lia); exact CTX7)
           UWC7
           ltac:(rewrite CG3, CG2, CG1; exact (cg_has_weaken _ _ _
                   [(SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                   [(SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] CGH eq_refl eq_refl))
           ltac:(rewrite LV3'; cbn [length app]; lia) ltac:(rewrite CR3, CR2, CR1; unfold mcost; cbn; lia)
           CLE9 T c13 E13).
  intros c14 (Σ4 & v7 & AS14 & LV4 & FRM4 & SP04 & CR4 & V7P & V7A & V7T & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c14 AS14) as (ms14 & (m10 & RET14 & (ART10 & MI10 & WM10 & STK10) & PK10 & CLE10 & WR10 & ACC10 & SK10) & E14). clear AS14.
  destruct RET14 as (n0 & n1 & n2 & o1 & o2 & o3 & o4 & o5 & o6 & o7 & n3 & n4 & n5 & n6 & F14 & fc14 & ->).

  (* back from OPENSSL_sk_new_null (child_cbs) *)
  rewrite ESP48 in STK10, PK10.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_7) in E14 by (unfold SITE_ossl_provider_store_new_7; lia).
  assert (LV4' : rt_live RT Σ4 = [(v7, 56); (v6, 40); (v2, 56); (v1, 80)] ++ rt_live RT Σ) by (rewrite LV4, LV3'; reflexivity).
  assert (FRM4' : rt_frames RT Σ4 = rt_frames RT Σ) by (rewrite FRM4; exact FRM3').
  assert (SP04' : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (rewrite SP04; exact SP03').
  assert (IN7 : In (v7, 56) (rt_live RT Σ4)) by (rewrite LV4; left; reflexivity).
  assert (IN6' : In (v6, 40) (rt_live RT Σ4)) by (rewrite LV4; right; exact IN6).
  assert (IN2_4 : In (v2, 56) (rt_live RT Σ4)) by (rewrite LV4; right; exact IN2'').
  assert (IN1_4 : In (v1, 80) (rt_live RT Σ4)) by (rewrite LV4; right; exact IN1'').
  pose proof (afp_live_hi RT GOBJ AFP Σ4 m10 v7 56 ART10 IN7 ltac:(lia)) as V7HI.
  destruct (af_live_range RT AF Σ4 m10 v7 56 ART10 IN7) as (_ & V7END & _). rewrite SP04' in V7END.
  pose proof (af_live_disj RT AF Σ4 m10 v7 56 v6 40 [] (rt_live RT Σ3) ART10 LV4 IN6) as D76. wp_box1 D76.
  pose proof (af_live_disj RT AF Σ4 m10 v7 56 v2 56 [] (rt_live RT Σ3) ART10 LV4 IN2'') as D72. wp_box1 D72.
  pose proof (af_live_disj RT AF Σ4 m10 v7 56 v1 80 [] (rt_live RT Σ3) ART10 LV4 IN1'') as D71. wp_box1 D71.
  assert (APART7 : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) SP x -> outside [(v7, v7 + 56)] x).
  { intros x XR. cbn [outside]. split; [|exact I].
    exact (wg_newchunk_apart RT AF Σ Σ4 m10 [(v7, 56); (v6, 40); (v2, 56); (v1, 80)] v7 56 SP x ART10 LV4' (or_introl eq_refl) FRM4' SP04'
             ltac:(lia) ltac:(lia) XR). }
  assert (OUT7 : forall x, SP + -48 <= x < SP \/ v1 <= x < v1 + 80 \/ v2 <= x < v2 + 56 \/ v6 <= x < v6 + 40 -> outside [(v7, v7 + 56)] x)
    by (intros x XR; unfold wp_box in D76, D72, D71; cbn [outside]; split; [lia | exact I]).
  assert (ACL4 : forall x, SP + -48 <= x < SP \/ v1 <= x < v1 + 80 \/ v2 <= x < v2 + 56 \/ v6 <= x < v6 + 40 ->
                 aclient (rt_live RT Σ4) (rt_frames RT Σ4) (SP + -48) x).
  { intros x [XR|[XR|[XR|XR]]].
    - apply acl_stack. unfold USTACK_TOP in *. lia.
    - exact (acl_live _ _ _ v1 80 x IN1_4 XR).
    - exact (acl_live _ _ _ v2 56 x IN2_4 XR).
    - exact (acl_live _ _ _ v6 40 x IN6' XR). }
  assert (CLOUT7 : forall x, cl_cell x -> outside [(v7, v7 + 56)] x).
  { intros x XR. pose proof (client_static_range x (cl_cell_static x XR)). cbn [outside]. split; [unfold SEGTOP_A in *; lia | exact I]. }
  assert (PRES10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m10).
  { apply (PRESC Σ3 m9 m10 _ PRES9 PK10); [intros e INe; rewrite LV3'; apply in_or_app; right; exact INe | exact FRM3' | intros x _ OUTa; exact OUTa]. }
  assert (FR10 : rw_cells asegs m10 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPG Σ3 m9 m10 _ _ FR9 PK10 WM10 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply acl_stack. unfold USTACK_TOP in *. lia. }
  assert (ST10 : rw_cells asegs m10 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6);
                                        CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPG Σ3 m9 m10 _ _ ST9 PK10 WM10 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v1 80); [exact IN1'' | lia]. }
  assert (SKV2_10 : rw_cells asegs m10 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPG Σ3 m9 m10 _ _ SKV2_9 PK10 WM10 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v2 56); [exact IN2'' | lia]. }
  assert (MX10 : rw_cells asegs m10 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (KEEPG Σ3 m9 m10 _ _ MX9 PK10 WM10 ltac:(lia)). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v6 40); [exact IN6 | lia]. }
  destruct (af_client_consts RT AF Σ4 m10 ART10) as (_ & SHC10 & _ & _ & UT10).
  pose proof (ossl_provider_store_new_s7_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_7) n0 n1 n2 o1 o2 o3 o4 o5 o6 o7 n3 n4 n5 n6 v1 v2 v2 v6 v7 F14 fc14 m10 lo
                STK10 ltac:(lia) ltac:(lia) ltac:(lia) ST10 FR10 SHC10 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT10 MI10) as W7.
  cl_lift W7 E14 c15 AS15.
  destruct (ASTA_unpack RT Σ4 _ _ c15 AS15) as (ms15 & (-> & SHOFF15) & EN15). clear AS15.
  assert (ALN7 : negb (bv_eqb (Z_to_bv 64 (Z.land v7 7)) (Z_to_bv 64 0)) = false)
    by (rewrite (wg_land7 v7) by lia; rewrite (wg_mod16_8 v7 V7A); reflexivity).
  apply (C_OPENSSL_sk_set_cmp_thunks Σ4 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_8) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) n0 n1 n2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 0x214568) o2 o3 o4 o5 o6 o7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           n3 n4 n5 n6 F14 fc14 m10 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDFS MSTAB eq_refl eq_refl ART10 MI10 (CALLOK Σ4 m10 SP04' STK10)
           ltac:(rewrite ESP48; lia) IN7 V7A SK10 ALN7 T c15 EN15).
  intros c16 AS16.
  destruct (ASTA_unpack RT Σ4 _ _ c16 AS16) as (ms16 & (m11 & RET16 & (ART11 & MI11 & WM11 & STK11) & PK11 & SK11) & E16). clear AS16.
  destruct RET16 as (i0 & i1 & i2 & l1 & l2 & l3 & l4 & l5 & l6 & l7 & i3 & i4 & i5 & i6 & F16 & fc16 & ->).

  (* back from OPENSSL_sk_set_cmp_thunks (child_cbs) *)
  rewrite ESP48 in STK11, PK11.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_8) in E16 by (unfold SITE_ossl_provider_store_new_8; lia).
  assert (PRES11 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m11).
  { apply (PRESC Σ4 m10 m11 _ PRES10 PK11); [intros e INe; rewrite LV4'; apply in_or_app; right; exact INe | exact FRM4' | intros x XR _; exact (APART7 x XR)]. }
  assert (FR11 : rw_cells asegs m11 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ4 m10 m11 _ _ _ FR10 PK11 WM11). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (ST11 : rw_cells asegs m11 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6);
                                        CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ4 m10 m11 _ _ _ ST10 PK11 WM11). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (SKV2_11 : rw_cells asegs m11 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPC Σ4 m10 m11 _ _ _ SKV2_10 PK11 WM11). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (MX11 : rw_cells asegs m11 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (KEEPC Σ4 m10 m11 _ _ _ MX10 PK11 WM11). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  pose proof (CLEC Σ4 m10 m11 _ _ CLE10 PK11 CLOUT7) as CLE11.
  destruct (af_client_consts RT AF Σ4 m11 ART11) as (_ & SHC11 & _ & _ & UT11).
  pose proof (ossl_provider_store_new_s8_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_8) i0 i1 i2 l1 l2 l3 l4 l5 l6 l7 i3 i4 i5 i6 v1 v2 v6 v7 v7 F16 fc16 m11 lo
                STK11 ltac:(lia) ltac:(lia) ltac:(lia) ST11 FR11 SHC11 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT11 MI11) as W8.
  cl_lift W8 E16 c17 AS17.
  destruct (ASTA_unpack RT Σ4 _ _ c17 AS17) as (ms17 & (-> & SHOFF17) & EN17). clear AS17.
  apply (C_OPENSSL_sk_set_copy_thunks Σ4 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_9) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) i0 i1 i2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 0x214594) l2 l3 l4 l5 l6 l7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           i3 i4 i5 i6 F16 fc16 m11 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0x214568) (Z_to_bv 64 0) (Z_to_bv 64 0) FDFS MSTAB eq_refl eq_refl ART11 MI11 (CALLOK Σ4 m11 SP04' STK11)
           ltac:(rewrite ESP48; lia) IN7 V7A SK11 ALN7 T c17 EN17).
  intros c18 AS18.
  destruct (ASTA_unpack RT Σ4 _ _ c18 AS18) as (ms18 & (m12 & RET18 & (ART12 & MI12 & WM12 & STK12) & PK12 & SK12) & E18). clear AS18.
  destruct RET18 as (p0' & p1' & p2' & r1' & r2' & r3' & r4' & r5' & r6' & r7' & p3' & p4' & p5' & p6' & F18 & fc18 & ->).
  (* back from OPENSSL_sk_set_copy_thunks (child_cbs) *)
  rewrite ESP48 in STK12, PK12.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_9) in E18 by (unfold SITE_ossl_provider_store_new_9; lia).
  assert (PRES12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m12).
  { apply (PRESC Σ4 m11 m12 _ PRES11 PK12); [intros e INe; rewrite LV4'; apply in_or_app; right; exact INe | exact FRM4' | intros x XR _; exact (APART7 x XR)]. }
  assert (FR12 : rw_cells asegs m12 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ4 m11 m12 _ _ _ FR11 PK12 WM12). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (ST12 : rw_cells asegs m12 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6);
                                        CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ4 m11 m12 _ _ _ ST11 PK12 WM12). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (SKV2_12 : rw_cells asegs m12 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPC Σ4 m11 m12 _ _ _ SKV2_11 PK12 WM12). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (MX12 : rw_cells asegs m12 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (KEEPC Σ4 m11 m12 _ _ _ MX11 PK12 WM12). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  pose proof (CLEC Σ4 m11 m12 _ _ CLE11 PK12 CLOUT7) as CLE12.
  destruct (af_client_consts RT AF Σ4 m12 ART12) as (_ & SHC12 & _ & _ & UT12).
  pose proof (ossl_provider_store_new_s9_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_9) p0' p1' p2' r1' r2' r3' r4' r5' r6' r7' p3' p4' p5' p6' v1 v2 v6 v7 v7 F18 fc18 m12 lo
                STK12 ltac:(lia) ltac:(lia) ltac:(lia) ST12 FR12 SHC12 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT12 MI12) as W9.
  cl_lift W9 E18 c19 AS19.
  destruct (ASTA_unpack RT Σ4 _ _ c19 AS19) as (ms19 & (-> & SHOFF19) & EN19). clear AS19.
  apply (C_OPENSSL_sk_set_thunks Σ4 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_10) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) p0' p1' p2' sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 0x2144ec) r2' r3' r4' r5' r6' r7' a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           p3' p4' p5' p6' F18 fc18 m12 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 0x214568) (Z_to_bv 64 0) (Z_to_bv 64 0x214594) FDFS MSTAB eq_refl eq_refl ART12 MI12 (CALLOK Σ4 m12 SP04' STK12)
           ltac:(rewrite ESP48; lia) IN7 V7A SK12 ALN7 T c19 EN19).
  intros c20 AS20.
  destruct (ASTA_unpack RT Σ4 _ _ c20 AS20) as (ms20 & (m13 & RET20 & (ART13 & MI13 & WM13 & STK13) & PK13 & SK13) & E20). clear AS20.
  destruct RET20 as (u0 & u1 & u2 & tt1 & tt2 & tt3 & tt4 & tt5 & tt6 & tt7 & u3 & u4 & u5 & u6 & F20 & fc20 & ->).

  (* back from OPENSSL_sk_set_thunks (child_cbs) *)
  rewrite ESP48 in STK13, PK13.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_10) in E20 by (unfold SITE_ossl_provider_store_new_10; lia).
  assert (PRES13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m13).
  { apply (PRESC Σ4 m12 m13 _ PRES12 PK13); [intros e INe; rewrite LV4'; apply in_or_app; right; exact INe | exact FRM4' | intros x XR _; exact (APART7 x XR)]. }
  assert (FR13 : rw_cells asegs m13 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPC Σ4 m12 m13 _ _ _ FR12 PK13 WM13). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (ST13 : rw_cells asegs m13 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6);
                                        CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPC Σ4 m12 m13 _ _ _ ST12 PK13 WM13). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (SKV2_13 : rw_cells asegs m13 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPC Σ4 m12 m13 _ _ _ SKV2_12 PK13 WM13). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  assert (MX13 : rw_cells asegs m13 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (KEEPC Σ4 m12 m13 _ _ _ MX12 PK13 WM13). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    split; [apply ACL4 | apply OUT7]; lia. }
  pose proof (CLEC Σ4 m12 m13 _ _ CLE12 PK13 CLOUT7) as CLE13.
  destruct (af_client_consts RT AF Σ4 m13 ART13) as (_ & SHC13 & _ & _ & UT13).
  pose proof (proj2 (af_acc_live RT AF Σ4 m13 v1 80 ART13 IN1_4)) as ACC1_13.
  assert (NZ7 : bv_eqb (Z_to_bv 64 v7) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia); apply Z.eqb_neq; lia).
  pose proof (ossl_provider_store_new_s10_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_10) u0 u1 u2 tt1 tt2 tt3 tt4 tt5 tt6 tt7 u3 u4 u5 u6 v1 v2 v6 v7 v7 F20 fc20 m13 lo
                STK13 ltac:(lia) ltac:(lia) ltac:(lia) ST13 FR13 SHC13 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT13 ACC1_13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                NZ7 MI13) as W10.
  cl_lift W10 E20 c21 AS21.
  destruct (ASTA_unpack RT Σ4 _ _ c21 AS21) as (ms21 & (m14 & -> & MU14 & WM14 & MI14 & STK14 & FR14 & ST14 & SHOFF21) & E21). clear AS21.
  fold SP in MU14, STK14, FR14, E21.
  assert (PRES14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m14).
  { apply (PRESW m13 m14 _ PRES13 MU14). intros x XR. pose proof (APART1 x XR). cbn [outside]. split; [lia | exact I]. }
  assert (ART14 : ART RT Σ4 m14).
  { apply (ARTW Σ4 m13 m14 _ ART13 SP04' MU14 WM14). intros x XR. destruct (wg_not_outside_cons _ _ _ _ XR) as [INW|NOUT]; [|exfalso; exact (NOUT I)].
    apply ACL4. lia. }
  pose proof (cl_env_seg _ m13 m14 _ canary CLE13 MU14 ltac:(cl_fp_lia)) as CLE14.
  assert (SKV2_14 : rw_cells asegs m14 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (wg_keep_seg _ m13 m14 _ _ SKV2_13 MU14 WM14). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D21. cbn [outside]. split; [lia | exact I]. }
  assert (MX14 : rw_cells asegs m14 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m13 m14 _ _ MX13 MU14 WM14). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D61. cbn [outside]. split; [lia | exact I]. }
  assert (SKV7_14 : rw_cells asegs m14 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x214568); C8 (Z_to_bv 64 0x2144ec); C8 (Z_to_bv 64 0x214594)]).
  { apply (wg_keep_seg _ m13 m14 _ _ SK13 MU14 WM14). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    unfold wp_box in D71. cbn [outside]. split; [lia | exact I]. }
  destruct (CHAIN m14 SITE_ossl_provider_store_new_11 e_lock_new
              (proj1 CGH (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new) ltac:(cbn [In]; tauto))
              (proj2 CGH (SITE_ossl_provider_store_new_11, e_lock_new) ltac:(cbn [In]; tauto)) PRES14 FR14) as (CTX11 & UWC11).
  apply (C_lock_new Σ4 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_11) (Z_to_bv 64 (SP + -48)) gp (Z_to_bv 64 12205808) u0 u1 u2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) tt3 tt4 tt5 tt6 tt7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
           F20 fc20 m14 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDFS MSTAB eq_refl ART14 MI14 (CALLOK Σ4 m14 SP04' STK14)
           ltac:(rewrite ESP48; unfold RT_STACK in *; lia)
           ltac:(rewrite CG4, CG3, CG2, CG1, (unsigned_lit SITE_ossl_provider_store_new_11) by (unfold SITE_ossl_provider_store_new_11; lia); exact CTX11)
           UWC11
           ltac:(rewrite CG4, CG3, CG2, CG1; exact (cg_has_weaken _ _ _
                   [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                   [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] CGH eq_refl eq_refl))
           ltac:(rewrite FRM4'; exact NFRM) ltac:(rewrite LV4'; cbn [length app]; lia)
           ltac:(rewrite CR4, CR3, CR2, CR1; unfold mcost; cbn; lia)
           CLE14 T c21 E21).
  intros c22 (Σ5 & v11 & AS22 & LV5 & FRM5 & SP05 & CR5 & V11P & V11A & V11T & CG5).
  destruct (ASTA_unpack RT Σ5 _ _ c22 AS22) as (ms22 & (m15 & RET22 & (ART15 & MI15 & WM15 & STK15) & PK15 & CLE15 & MX15 & ACC15) & E22). clear AS22.
  destruct RET22 as (w0' & w1' & w2' & ww1 & ww2 & ww3 & ww4 & ww5 & ww6 & ww7 & w3' & w4' & w5' & w6' & F22 & fc22 & ->).

  (* back from CRYPTO_THREAD_lock_new (lock) *)
  rewrite ESP48 in STK15, PK15.
  rewrite (ret_pc_even SITE_ossl_provider_store_new_11) in E22 by (unfold SITE_ossl_provider_store_new_11; lia).
  assert (LV5' : rt_live RT Σ5 = [(v11, 40); (v7, 56); (v6, 40); (v2, 56); (v1, 80)] ++ rt_live RT Σ) by (rewrite LV5, LV4'; reflexivity).
  assert (FRM5' : rt_frames RT Σ5 = rt_frames RT Σ) by (rewrite FRM5; exact FRM4').
  assert (SP05' : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP05; exact SP04').
  assert (IN11 : In (v11, 40) (rt_live RT Σ5)) by (rewrite LV5; left; reflexivity).
  assert (IN1_5 : In (v1, 80) (rt_live RT Σ5)) by (rewrite LV5; right; exact IN1_4).
  pose proof (afp_live_hi RT GOBJ AFP Σ5 m15 v11 40 ART15 IN11 ltac:(lia)) as V11HI.
  pose proof (af_live_disj RT AF Σ5 m15 v11 40 v1 80 [] (rt_live RT Σ4) ART15 LV5 IN1_4) as D111. wp_box1 D111.
  assert (PRES15 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) SP G1 m m15).
  { apply (PRESC Σ4 m14 m15 _ PRES14 PK15); [intros e INe; rewrite LV4'; apply in_or_app; right; exact INe | exact FRM4' | intros x _ OUTa; exact OUTa]. }
  assert (FR15 : rw_cells asegs m15 (SP + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KEEPG Σ4 m14 m15 _ _ FR14 PK15 WM15 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply ACL4. lia. }
  assert (ST15 : rw_cells asegs m15 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v6);
                                        CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]).
  { apply (KEEPG Σ4 m14 m15 _ _ ST14 PK15 WM15 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply ACL4. lia. }
  assert (SKV2_15 : rw_cells asegs m15 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0x20f7bc); C8 (Z_to_bv 64 0x214514); C8 (Z_to_bv 64 0x2144c4); C8 (Z_to_bv 64 0x214540)]).
  { apply (KEEPG Σ4 m14 m15 _ _ SKV2_14 PK15 WM15 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply ACL4. lia. }
  assert (MX6_15 : rw_cells asegs m15 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (KEEPG Σ4 m14 m15 _ _ MX14 PK15 WM15 ltac:(lia)). intros x XR. cbn [mutex_cells cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply ACL4. lia. }
  assert (SKV7_15 : rw_cells asegs m15 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                                        C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x214568); C8 (Z_to_bv 64 0x2144ec); C8 (Z_to_bv 64 0x214594)]).
  { apply (KEEPG Σ4 m14 m15 _ _ SKV7_14 PK15 WM15 ltac:(lia)). intros x XR. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XR.
    apply (acl_live _ _ _ v7 56); [exact IN7 | lia]. }
  destruct (af_client_consts RT AF Σ5 m15 ART15) as (_ & SHC15 & _ & _ & UT15).
  pose proof (proj2 (af_acc_live RT AF Σ5 m15 v1 80 ART15 IN1_5)) as ACC1_15.
  assert (NZ11 : bv_eqb (Z_to_bv 64 v11) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia); apply Z.eqb_neq; lia).
  pose proof (ossl_provider_store_new_s11_walk ra sp gp (Z_to_bv 64 12205808) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                (Z_to_bv 64 SITE_ossl_provider_store_new_11) w0' w1' w2' ww1 ww2 ww3 ww4 ww5 ww6 ww7 w3' w4' w5' w6' v1 v2 v6 v7 v7 v11 F22 fc22 m15 lo
                STK15 ltac:(lia) ltac:(lia) ltac:(lia) ST15 FR15 SHC15 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT15 ACC1_15
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NZ11 MI15) as W11.
  cl_lift W11 E22 c23 AS23.
  apply KONT. exists Σ5, v1, v2, v6, v7, v11. split.
  - apply (ASTA_conseq RT Σ5 PMc _ _ c23 AS23). intros ms (m16 & EQ16 & MU16 & WM16 & MI16 & STK16 & ST16 & SHOFF23).
    fold SP in MU16, STK16. exists m16.
    assert (ART16 : ART RT Σ5 m16).
    { apply (ARTW Σ5 m15 m16 _ ART15 SP05' MU16 WM16). intros x XR. destruct (wg_not_outside_cons _ _ _ _ XR) as [INW|NOUT]; [|exfalso; exact (NOUT I)].
      exact (acl_live _ _ _ v1 80 x IN1_5 INW). }
    assert (WMALL : wmono asegs m m16).
    { refine (wmono_trans asegs m m15 m16 _ WM16). refine (wmono_trans asegs m m14 m15 _ WM15). refine (wmono_trans asegs m m13 m14 _ WM14).
      refine (wmono_trans asegs m m12 m13 _ WM13). refine (wmono_trans asegs m m11 m12 _ WM12). refine (wmono_trans asegs m m10 m11 _ WM11).
      refine (wmono_trans asegs m m9 m10 _ WM10). refine (wmono_trans asegs m m8 m9 _ WM9). refine (wmono_trans asegs m m7 m8 _ WM8).
      refine (wmono_trans asegs m m6 m7 _ WM7). refine (wmono_trans asegs m m5 m6 _ WM6). refine (wmono_trans asegs m m4 m5 _ WM5).
      refine (wmono_trans asegs m m3 m4 _ WM4). refine (wmono_trans asegs m m2 m3 _ WM3). exact (wmono_trans asegs m m1 m2 WM1 WM2). }
    assert (FAR : forall X n, (v1 + 80 <= X \/ X + n <= v1) -> forall x, X <= x < X + n -> outside [(v1, v1 + 80)] x)
      by (intros X n XIN x XR; cbn [outside]; split; [lia | exact I]).
    split; [do 16 eexists; exact EQ16|]. split; [exact (conj ART16 (conj MI16 (conj WMALL STK16)))|].
    split; [apply (PRESW m15 m16 _ PRES15 MU16); intros x XR; cbn [outside]; split; [exact (APART1 x XR) | exact I]|].
    split; [exact (cl_env_seg _ m15 m16 _ canary CLE15 MU16 ltac:(cl_fp_lia))|].
    destruct (af_acc_live RT AF Σ5 m16 v1 80 ART16 IN1_5) as (WR16 & ACC16).
    split; [exact WR16|]. split; [exact ACC16|]. split; [exact ST16|].
    split.
    { apply (wg_keep_seg _ m15 m16 _ _ SKV2_15 MU16 WM16). apply (FAR v2 56). unfold wp_box in D21. lia. }
    split.
    { apply (wg_keep_seg _ m15 m16 _ _ MX6_15 MU16 WM16). apply (FAR v6 40). unfold wp_box in D61. lia. }
    split.
    { apply (wg_keep_seg _ m15 m16 _ _ SKV7_15 MU16 WM16). apply (FAR v7 56). unfold wp_box in D71. lia. }
    { apply (wg_keep_seg _ m15 m16 _ _ MX15 MU16 WM16). apply (FAR v11 40). unfold wp_box in D111. lia. }
  - split; [rewrite LV5'; reflexivity|]. split; [exact FRM5'|]. split; [exact SP05'|].
    split; [rewrite CR5, CR4, CR3, CR2, CR1; unfold mcost; cbn; lia|].
    split; [exact V1P|]. split; [exact V1A|]. split; [exact V1T|]. split; [exact V2A|]. split; [exact V6A|]. split; [exact V7A|].
    split; [exact V11A|]. rewrite CG5, CG4, CG3, CG2, CG1. reflexivity.
Qed.
End ossl_provider_store_new_cps.
