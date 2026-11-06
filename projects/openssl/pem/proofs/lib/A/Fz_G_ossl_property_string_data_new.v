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
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_G_kit2 Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Th_mutex Fz_M_locknew Fz_G_CRYPTO_calloc Fz_G_OPENSSL_LH_new Fz_G_OPENSSL_LH_set_thunks Fz_I2_lhst Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks.
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
Definition ossl_property_string_data_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem) (j : list byte),
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1
               (Z_to_bv 64 48) (Z_to_bv 64 0x4b980) (Z_to_bv 64 98) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

Lemma ossl_property_string_data_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_property_string_data_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20bcf4) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    STK ROOM LOBASE SPHI UNT SHOFF MINV.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (UTW : ut_fp [(bv_unsigned sp + -96, bv_unsigned sp)]) by ut_fp_lia.
  th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat STK.
  do 21 zstep.
  unfold ossl_property_string_data_new_s0_post, SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc.
  apply evt_done.
  refine (ex_intro _ m0 (ex_intro _ (firstn 8 junk) (conj eq_refl (conj MU (conj WM (conj MINV (conj STK (conj FR SHOFF)))))))).
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1
  u6_1 : word)
    (v1 : Z) (j1 : list byte) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1)
                       (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
                  F1 (Z_to_bv 64 e_lock_new) fc1 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 j1 F1 fc1 m lo
    Stk Room LoMin SpMax Fr ShOff Rv1 Untouched Obj Acc1 Al1 Lo1 Hi1 Below1 Inv.
  zstep. wg_F. do 2 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s1_post, SITE_ossl_property_string_data_new_2, e_lock_new. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2
  u6_2 : word)
    (v1 v2 : Z) (j1 : list byte) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_3) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1)
               (Z_to_bv 64 0x20bf48) (Z_to_bv 64 0x20bf8c) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2
                 u6_2)
            F2 (Z_to_bv 64 e_OPENSSL_LH_new) fc2 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 j1 F2 fc2 m lo
    Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Untouched Acc1 Al1 Lo1 Hi1 Below1 Gran1 Inv.
  pose proof (munch_refl [(v1, v1 + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ShW : sh_fp [(v1, v1 + 8)]) by sh_fp_lia.
  do 4 zstep. wg_F. do 7 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s2_post, SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new.
  exists m0. cbn [skipn repeat] in Obj.
  split; [reflexivity|]. exact (conj MU (conj WM (conj Inv (conj Obj (conj Fr (conj Stk ShOff)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3
  u6_3 : word)
    (v1 v2 v3 : Z) (j1 : list byte) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3)
    (Z_to_bv 64 0x20c77c) (Z_to_bv 64 0x20c79c) (Z_to_bv 64 0x20c7bc) (Z_to_bv 64 0x20c7dc) b5_3 b6_3 b7_3 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10
    s11 u3_3 u4_3 u5_3 u6_3)
                  F3 (Z_to_bv 64 e_OPENSSL_LH_set_thunks) fc3 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv3 Untouched Inv.
  do 9 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s3_post, SITE_ossl_property_string_data_new_4, e_OPENSSL_LH_set_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4
  u6_4 : word)
    (v1 v2 v4 : Z) (j1 : list byte) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_5) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 0x20bf48)
      (Z_to_bv 64 0x20bf8c) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8
      s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 e_OPENSSL_LH_new) fc4 None m' (seg_rom asegs)
    /\ munch [(v1 + 8, v1 + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); CB 32 (repeat (Z_to_bv 8 0) 32)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Untouched Acc1 Al1 Lo1 Hi1 Below1 Inv.
  pose proof (munch_refl [(v1 + 8, v1 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ShW : sh_fp [(v1 + 8, v1 + 16)]) by sh_fp_lia.
  do 5 zstep. wg_F. do 6 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s4_post, SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new.
  exists m0. cbn [skipn repeat] in Obj.
  split; [reflexivity|]. exact (conj MU (conj WM (conj Inv (conj Obj (conj Fr (conj Stk ShOff)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5
  u6_5 : word)
    (v1 v2 v4 v5 : Z) (j1 : list byte) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_6) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5)
    (Z_to_bv 64 0x20c77c) (Z_to_bv 64 0x20c79c) (Z_to_bv 64 0x20c7bc) (Z_to_bv 64 0x20c7dc) b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64
    2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
                  F5 (Z_to_bv 64 e_OPENSSL_LH_set_thunks) fc5 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv5 Untouched Inv.
  do 9 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s5_post, SITE_ossl_property_string_data_new_6, e_OPENSSL_LH_set_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6
  u6_6 : word)
    (v1 v2 v4 v6 : Z) (j1 : list byte) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_7) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64
      0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880))
      (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 e_OPENSSL_sk_new_null) fc6 None m' (seg_rom asegs)
    /\ munch [(v1 + 16, v1 + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 24 (repeat (Z_to_bv 8 0) 24)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Untouched Acc1 Al1 Lo1 Hi1 Below1 Inv.
  pose proof (munch_refl [(v1 + 16, v1 + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ShW : sh_fp [(v1 + 16, v1 + 24)]) by sh_fp_lia.
  do 5 zstep. wg_F. do 2 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s6_post, SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null.
  exists m0. cbn [skipn repeat] in Obj.
  split; [reflexivity|]. exact (conj MU (conj WM (conj Inv (conj Obj (conj Fr (conj Stk ShOff)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7
  u6_7 : word)
    (v1 v2 v4 v6 v7 : Z) (j1 : list byte) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7)
    (Z_to_bv 64 0x20bfec) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3
    + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
                  F7 (Z_to_bv 64 e_OPENSSL_sk_set_cmp_thunks) fc7 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv7 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s7_post, SITE_ossl_property_string_data_new_8, e_OPENSSL_sk_set_cmp_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s8_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8
  u6_8 : word)
    (v1 v2 v4 v6 v8 : Z) (j1 : list byte) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_9) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8)
    (Z_to_bv 64 0x20c018) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3
    + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
                  F8 (Z_to_bv 64 e_OPENSSL_sk_set_copy_thunks) fc8 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv8 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s8_post, SITE_ossl_property_string_data_new_9, e_OPENSSL_sk_set_copy_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s9_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9
  u6_9 : word)
    (v1 v2 v4 v6 v9 : Z) (j1 : list byte) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_10) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9)
    (Z_to_bv 64 0x20c040) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3
    + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
                  F9 (Z_to_bv 64 e_OPENSSL_sk_set_thunks) fc9 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv9 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s9_post, SITE_ossl_property_string_data_new_10, e_OPENSSL_sk_set_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s10_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10
  u3_10 u4_10 u5_10 u6_10 : word)
    (v1 v2 v4 v6 v10 : Z) (j1 : list byte) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_11) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10)
      (Z_to_bv 64 0) b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64 2147450880)
      (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 e_OPENSSL_sk_new_null) fc10 None m' (seg_rom asegs)
    /\ munch [(v1 + 32, v1 + 40)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j1; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv10 Untouched Acc1 Al1 Lo1 Hi1 Below1 Inv.
  pose proof (munch_refl [(v1 + 32, v1 + 40)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ShW : sh_fp [(v1 + 32, v1 + 40)]) by sh_fp_lia.
  do 5 zstep. wg_F. do 2 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s10_post, SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null.
  exists m0. cbn [skipn repeat] in Obj.
  split; [reflexivity|]. exact (conj MU (conj WM (conj Inv (conj Obj (conj Fr (conj Stk ShOff)))))).
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s11_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11
  u3_11 u4_11 u5_11 u6_11 : word)
    (v1 v2 v4 v6 v10 v11 : Z) (j1 : list byte) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_12) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64
    v11) (Z_to_bv 64 0x20bfec) b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64
    2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_11 u4_11 u5_11
    u6_11)
                  F11 (Z_to_bv 64 e_OPENSSL_sk_set_cmp_thunks) fc11 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv10 Rv11 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s11_post, SITE_ossl_property_string_data_new_12, e_OPENSSL_sk_set_cmp_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s12_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12
  u3_12 u4_12 u5_12 u6_12 : word)
    (v1 v2 v4 v6 v10 v12 : Z) (j1 : list byte) (F12 : bvmap 5 word) (fc12 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_13) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64
    v12) (Z_to_bv 64 0x20c018) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64
    2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_12 u4_12 u5_12
    u6_12)
                  F12 (Z_to_bv 64 e_OPENSSL_sk_set_copy_thunks) fc12 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv10 Rv12 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s12_post, SITE_ossl_property_string_data_new_13, e_OPENSSL_sk_set_copy_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s13_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13
  u3_13 u4_13 u5_13 u6_13 : word)
    (v1 v2 v4 v6 v10 v13 : Z) (j1 : list byte) (F13 : bvmap 5 word) (fc13 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => ms = MS (mkR (Z_to_bv 64 SITE_ossl_property_string_data_new_14) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64
    v13) (Z_to_bv 64 0x20c040) b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64
    2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 u3_13 u4_13 u5_13
    u6_13)
                  F13 (Z_to_bv 64 e_OPENSSL_sk_set_thunks) fc13 None m (seg_rom asegs)
    /\ ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv10 Rv13 Untouched Inv.
  do 3 zstep.
  apply evt_done. unfold ossl_property_string_data_new_s13_post, SITE_ossl_property_string_data_new_14, e_OPENSSL_sk_set_thunks. split; [reflexivity | exact ShOff].
Qed.

(* [comment removed for export] *)
Definition ossl_property_string_data_new_s14_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14
  u3_14 u4_14 u5_14 u6_14 : word)
    (v1 v2 v4 v6 v10 v14 : Z) (j1 : list byte) (F14 : bvmap 5 word) (fc14 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    ms = MS (mkR ra sp gp tp u0_14 u1_14 u2_14 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
            F14 (ret_pc ra) fc14 None m' (seg_rom asegs)
    /\ munch [(v1 + 40, v1 + 48)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v6); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v14)]
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ro_cells asegs m' 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)].

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
  intros until lo. intros Stk Room LoMin SpMax Obj Fr ShOff Rv1 Rv2 Rv4 Rv6 Rv10 Rv14 Untouched Acc1 Al1 Lo1 Hi1 Below1 Nz2 Nz10 Nz14 Nz4 Nz6 Inv.
  pose proof (munch_refl [(v1 + 40, v1 + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (ShW : sh_fp [(v1 + 40, v1 + 48)]) by sh_fp_lia.
  do 5 zstep. wg_F. zstep.
  zstep. wg_raw Nz2.
  do 2 zstep. wg_F.
  do 2 zstep. wg_raw Nz10.
  zstep. wg_raw Nz14.
  do 2 zstep. wg_F.
  do 2 zstep. wg_raw Nz4.
  do 2 zstep. wg_F.
  do 2 zstep. wg_raw Nz6.
  do 14 zstep.
  th_release Fr (bv_unsigned sp).
  apply evt_done. unfold ossl_property_string_data_new_s14_post.
  exists m0. split; [reflexivity|].
  exact (conj MU (conj WM (conj Inv (conj Obj (conj Stk ShOff))))).
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
  forall (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc ->
  mat_stable PMc ->
  tp = Z_to_bv 64 12205808 ->
  ART RT Σ m ->
  mem_inv asegs m ->
  call_ok RT Σ m sp lo ->
  lo + RT_STACK + 608 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_property_string_data_new (bv_unsigned ra :: outer) ->
  uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ)
    [(SITE_ossl_property_string_data_new_1, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_2, e_ossl_property_string_data_new);
     (SITE_ossl_property_string_data_new_3, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_5, e_ossl_property_string_data_new);
     (SITE_ossl_property_string_data_new_7, e_ossl_property_string_data_new); (SITE_ossl_property_string_data_new_11, e_ossl_property_string_data_new);
     (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new);
     (SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null)]
    [(SITE_ossl_property_string_data_new_1, e_CRYPTO_zalloc); (SITE_ossl_property_string_data_new_2, e_lock_new);
     (SITE_ossl_property_string_data_new_3, e_OPENSSL_LH_new); (SITE_ossl_property_string_data_new_5, e_OPENSSL_LH_new);
     (SITE_ossl_property_string_data_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_property_string_data_new_11, e_OPENSSL_sk_new_null);
     (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc);
     (SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc);
     (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 8 <= LIVE_MAX ->
  mcost 48 + 1 + (mcost 104 + mcost 128) + (mcost 104 + mcost 128) + mcost 56 + mcost 56 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    e_ossl_property_string_data_new m)))
    (fun c => exists (Σ' : rts RT) (ps pk pl1 pb1 pl2 pb2 pq1 pq2 : Z),
       ASTA RT Σ' PMc
         (fun ms => exists m' : mem,
            ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ps) m' ms
            /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
            /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
            /\ cl_env m' (Z_to_bv 8 1) canary
            /\ wr_at asegs m' ps 48 /\ acc asegs m' ps 48 /\ wr_at asegs m' pk 40 /\ acc asegs m' pk 40
            /\ wr_at asegs m' pl1 104 /\ acc asegs m' pl1 104 /\ wr_at asegs m' pb1 128 /\ acc asegs m' pb1 128
            /\ wr_at asegs m' pl2 104 /\ acc asegs m' pl2 104 /\ wr_at asegs m' pb2 128 /\ acc asegs m' pb2 128
            /\ wr_at asegs m' pq1 56 /\ acc asegs m' pq1 56 /\ wr_at asegs m' pq2 56 /\ acc asegs m' pq2 56
            /\ rw_cells asegs m' ps [C8 (Z_to_bv 64 pk); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8);
                                     C8 (Z_to_bv 64 pq1); C8 (Z_to_bv 64 pq2)]
            /\ rw_cells asegs m' pk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
            /\ rw_cells asegs m' pl1
               [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]
            /\ rw_cells asegs m' pb1 [CB 128 (repeat (Z_to_bv 8 0) 128)]
            /\ rw_cells asegs m' pl2
               [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]
            /\ rw_cells asegs m' pb2 [CB 128 (repeat (Z_to_bv 8 0) 128)]
            /\ rw_cells asegs m' pq1
               [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]
            /\ rw_cells asegs m' pq2
               [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)])
         c
       /\ rt_live RT Σ' = (pq2, 56) :: (pq1, 56) :: (pb2, 128) :: (pl2, 104) :: (pb1, 128) :: (pl1, 104) :: (pk, 40) :: (ps, 48) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 48 + 1 + (mcost 104 + mcost 128) + (mcost 104 + mcost 128) + mcost 56 + mcost 56)
       /\ 0 < ps /\ ps mod 16 = 0 /\ ps + 48 < USTACK_TOP /\ 0 < pk /\ pk mod 16 = 0 /\ pk + 40 < USTACK_TOP
       /\ 0 < pl1 /\ pl1 mod 16 = 0 /\ pl1 + 104 < USTACK_TOP /\ 0 < pb1 /\ pb1 mod 16 = 0 /\ pb1 + 128 < USTACK_TOP
       /\ 0 < pl2 /\ pl2 mod 16 = 0 /\ pl2 + 104 < USTACK_TOP /\ 0 < pb2 /\ pb2 mod 16 = 0 /\ pb2 + 128 < USTACK_TOP
       /\ 0 < pq1 /\ pq1 mod 16 = 0 /\ pq1 + 56 < USTACK_TOP /\ 0 < pq2 /\ pq2 mod 16 = 0 /\ pq2 + 56 < USTACK_TOP
       /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_property_string_data_new_cps : ossl_property_string_data_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST TPv ART0 MI0 CALL0 Budget CTX0 UW0 CGH0 FrMax LiveMax Credit ENV0 T c HA Hk.
  destruct CALL0 as (STK0 & LOW & RTS & TOP & AL16).
  pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn [Z.of_N] in SPB.
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A, RT_STACK in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  (* CallAt serves each of the 14 calls and KeepStk each return; TopCells (before) and Fresh (after) serve the 6 calls that allocate; Consts serves each of the 15 segment walks *)
  assert (CallAt : forall (Σk : rts RT) (mk : mem), rt_sp0 RT Σk = rt_sp0 RT Σ -> stk asegs mk lo (bv_unsigned sp + -96) ->
            call_ok RT Σk mk (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { intros Σk mk SPk STKk. unfold call_ok. rewrite EU, SPk. unfold STACK_WIN, USTACK_TOP, RT_STACK.
    split; [exact STKk|]. split; [lia|]. split; [lia|]. split; [lia|]. rewrite Zplus_mod, AL16. reflexivity. }
  assert (Consts : forall (Σk : rts RT) (mk : mem), ART RT Σk mk ->
            ro_cells asegs mk 6736696 [C8 (Z_to_bv 64 2147450880)] /\ img_untouched mk).
  { intros Σk mk ARTk. destruct (af_client_consts RT AF Σk mk ARTk) as (_ & SH & _ & _ & U). exact (conj SH U). }
  assert (Fresh : forall (Σk : rts RT) (mk : mem) p n, ART RT Σk mk -> In (p, n) (rt_live RT Σk) -> rt_sp0 RT Σk = rt_sp0 RT Σ ->
            1 <= n <= 64512 -> 17594333495296 <= p /\ p + n <= 2 ^ 47 /\ p + n <= lo).
  { intros Σk mk p n ARTk INk SPk Hn. pose proof (afp_live_hi RT GOBJ AFP Σk mk p n ARTk INk ltac:(lia)) as HI.
    pose proof (afp_live_mem RT GOBJ AFP Σk mk p n ARTk INk ltac:(lia)) as (_ & TOPk).
    pose proof (af_live_range RT AF Σk mk p n ARTk INk) as (_ & SPk' & _). rewrite SPk in SPk'. unfold STACK_WIN in SPk'. lia. }
  assert (KeepStk : forall live frames usp W (ma mb : mem) X cs, rw_cells asegs ma X cs -> rt_pres_fp live frames usp W ma mb -> wmono asegs ma mb ->
            usp <= X -> X + Z.of_nat (cells_size cs) <= 2 ^ 47 -> (forall x, X <= x < X + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs mb X cs).
  { intros live frames usp W ma mb X cs CS PR WM LO HI OUT. apply (rw_cells_agree asegs ma mb X cs CS); [|exact WM].
    intros a Ha. apply PR; [left; unfold USTACK_TOP; lia | exact (OUT _ Ha)]. }
  assert (TopCells : forall (mk : mem) jk, rw_cells asegs mk (bv_unsigned sp + -96) [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
            rw_cells asegs mk (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { intros mk jk FRk.
    pose proof (rw_cells_skip mk _ [CB 8 jk; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FRk) as TOPk.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in TOPk. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + 80) by lia. exact TOPk. }
  (* segment 0: prologue up to the call of CRYPTO_zalloc *)
  pose proof (Consts Σ m ART0) as (SH0 & UT0).
  pose proof (ossl_property_string_data_new_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                STK0 ltac:(lia) ltac:(lia) ltac:(lia) UT0 SH0 MI0) as W.
  cl_lift W HA c1 H1.
  destruct (ASTA_unpack RT Σ _ _ c1 H1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & STK1 & FR1 & ShOff1) & HA1). clear H1 ShOff1.

  assert (ROOM : lo <= bv_unsigned sp + -96) by (unfold RT_STACK in *; lia).
  assert (LOMIN : 17594333495296 <= lo) by (unfold STACK_WIN in *; lia).
  assert (SPMAX : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (ArtStore : forall (Σk : rts RT) (ma mb : mem) q n W, ART RT Σk ma -> In (q, n) (rt_live RT Σk) -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> q <= x < q + n) -> ART RT Σk mb).
  { intros Σk ma mb q n W ARTa INq MU WM HW. pose proof (af_sp0_range RT AF Σk ma ARTa) as SPRk.
    apply (af_frame RT AF Σk ma mb USTACK_TOP ARTa ltac:(unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia)); [|exact WM].
    intros a Ha. apply MU. destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|].
    exfalso. apply Ha. right; right; left. exists q, n. split; [exact INq | exact (HW _ O)]. }
  assert (PresUp : forall (Σk : rts RT) (mk ma mb : mem) NEW usp W, ART RT Σk mk -> rt_live RT Σk = NEW ++ rt_live RT Σ ->
            rt_frames RT Σk = rt_frames RT Σ -> rt_sp0 RT Σk = rt_sp0 RT Σ -> usp <= bv_unsigned sp ->
            rt_pres_fp (rt_live RT Σk) (rt_frames RT Σk) usp W ma mb ->
            (forall x, ~ outside W x -> (G_ALLOW_CUST <= x < G_ALLOW_CUST + 1) \/ in_live NEW x) ->
            rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] ma mb).
  { intros Σk mk ma mb NEW usp W ARTk LVk FSk SZk Husp PRk HW a Ha Ho. apply PRk.
    - apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LVk; apply in_or_app; right; exact He | intros e He; rewrite FSk; exact He | exact Husp].
    - destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. destruct (HW _ O) as [G|(p & n & INp & Hp)].
      + cbn [outside] in Ho. destruct Ho as [Ho _]. exact (Ho G).
      + exact (wg_newchunk_apart RT AF Σ Σk mk NEW p n (bv_unsigned sp) (bv_unsigned a) ARTk LVk INp FSk SZk ltac:(unfold STACK_WIN in *; lia) ltac:(lia) Ha Hp). }
  assert (EnvKeep : forall live frames usp W (ma mb : mem) lbx, cl_env ma lbx canary -> rt_pres_fp live frames usp W ma mb ->
            (forall x, x < SEGTOP_A -> outside W x) -> cl_env mb lbx canary).
  { intros live frames usp W ma mb lbx EN PRk HW. apply (cl_env_agree ma mb lbx canary EN). intros a Ha.
    pose proof (cl_cell_static _ Ha) as CS. pose proof (client_static_range _ CS) as CR.
    apply PRk; [right; left; exact CS | apply HW; exact (proj2 CR)]. }

  assert (AgOf : forall mk : mem, rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m mk ->
            agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m mk).
  { intros mk PRk a Ha. cbv beta in Ha. apply PRk; [left; unfold USTACK_TOP in *; lia | cbn [outside]; unfold G_ALLOW_CUST; split; [lia | exact I]]. }
  assert (MC : mcost 48 = 0 /\ mcost 104 = 0 /\ mcost 128 = 0 /\ mcost 56 = 0) by (repeat split; reflexivity).

  assert (CGZ : cg_has (rt_cg RT Σ) [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                  [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ CGH0); vm_compute; reflexivity).
  assert (CGL : cg_has (rt_cg RT Σ) [(SITE_ln_zalloc, e_lock_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                  [(SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ CGH0); vm_compute; reflexivity).
  assert (CGH : cg_has (rt_cg RT Σ) [(SITE_OPENSSL_LH_new_1, e_OPENSSL_LH_new); (SITE_OPENSSL_LH_new_2, e_OPENSSL_LH_new); (SITE_cz_malloc, e_CRYPTO_zalloc);
                                     (SITE_cm_malloc, e_CRYPTO_malloc)]
                  [(SITE_OPENSSL_LH_new_1, e_CRYPTO_zalloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_calloc); (SITE_OPENSSL_LH_new_2, e_CRYPTO_zalloc);
                   (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ CGH0); vm_compute; reflexivity).
  assert (CGS : cg_has (rt_cg RT Σ) [(SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                  [(SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)])
    by (apply (cg_has_weaken _ _ _ _ _ CGH0); vm_compute; reflexivity).
  (* call 1: CRYPTO_zalloc (48 bytes) *)
  assert (ART1 : ART RT Σ m1).
  { apply (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] ART0); [unfold STACK_WIN; lia | unfold USTACK_TOP; lia | exact MU1 | intros x Hx; exfalso; exact (Hx I) | exact
    WM1]. }
  assert (PR1 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m1).
  { intros a Ha _. apply MU1. cbn [outside]. split; [| exact I].
    destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 _ ART0 ltac:(unfold STACK_WIN; lia) ltac:(lia) Ha); lia. }
  assert (ENV1 : cl_env m1 lb canary).
  { apply (cl_env_seg _ m m1 lb canary ENV0 MU1). apply cl_fp_cons; [right; left; unfold ssp_guard; lia | apply cl_fp_nil]. }
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_CRYPTO_zalloc SITE_ossl_property_string_data_new_1 m m1 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m1 PR1) (TopCells m1 j FR1) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX1 UW1].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_1) in CTX1 by (unfold SITE_ossl_property_string_data_new_1; lia).
  apply (C_CRYPTO_zalloc Σ PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1
           (Z_to_bv 64 48) (Z_to_bv 64 0x4b980) (Z_to_bv 64 98) a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
           48 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl TPv ltac:(lia) ART1 MI1 (CallAt Σ m1 eq_refl STK1) ltac:(rewrite EU; unfold RT_STACK; lia)
           CTX1 UW1 CGZ ltac:(lia) ltac:(rewrite (proj1 MC); lia)
           ENV1 T c1 HA1).
  clear HA1 CTX1 UW1.
  intros c2 (Σ1 & v1 & H2 & LV1 & FS1 & SZ1 & CR1 & P1 & Q1 & U1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 H2) as (ms2 & (m2 & (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->)
                                               & (ART2 & MI2 & WM2 & STK2) & PR2 & ENV2 & WR2 & ACC2 & BY2) & HA2). clear H2.
  rewrite EU in STK2.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_1) in HA2 by (unfold SITE_ossl_property_string_data_new_1; first [lia | reflexivity]).

  (* segment 1: test of the zalloc result and the call of CRYPTO_THREAD_lock_new *)
  rewrite EU in PR2.
  assert (IN1 : In (v1, 48) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  destruct (Fresh Σ1 m2 v1 48 ART2 IN1 SZ1 ltac:(lia)) as (LO1 & HI1 & BL1).
  pose proof (wg_mod16_8 v1 Q1) as AL1.
  assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m1 m2 _ _ FR1 PR2 WM2); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (PC2 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m2).
  { apply (pres_fp_trans _ _ _ _ m m1 m2 PR1).
    apply (PresUp Σ m1 m1 m2 [] (bv_unsigned sp + -96) _ ART1 eq_refl eq_refl eq_refl ltac:(lia) PR2).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m1 m2 WM1 WM2) as WC2.
  pose proof (wp_zero_rw_CB asegs m2 v1 48 BY2 WR2 ltac:(lia)) as OBJ2.
  clear PR1 PR2 FR1 MU1 STK1 MI1 ART1 WM1 ENV1 BY2 WR2.
  pose proof (Consts Σ1 m2 ART2) as (SH2 & UT2).
  pose proof (ossl_property_string_data_new_s1_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_1)
                u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 v1 j F2 fc2 m2 lo STK2 ROOM LOMIN SPMAX FR2 SH2 ltac:(lia) UT2 OBJ2 ACC2 AL1 LO1 HI1 BL1 MI2) as W.
  cl_lift W HA2 c3 H3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 H3) as (ms3 & (-> & ShOff_s1) & HA3). clear H3 HA2 ShOff_s1.

  (* call 2: CRYPTO_THREAD_lock_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_lock_new SITE_ossl_property_string_data_new_2 m m2 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m2 PC2) (TopCells m2 j FR2) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX2 UW2].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_2) in CTX2 by (unfold SITE_ossl_property_string_data_new_2; lia).
  rewrite <- CG1 in CTX2.
  apply (C_lock_new Σ1 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0 u1 u2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 v1) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo (bv_unsigned ra :: outer)
           (Z_to_bv 8 1) canary FDO MST TPv ART2 MI2 (CallAt Σ1 m2 SZ1 STK2) ltac:(rewrite EU; unfold RT_STACK; lia) CTX2 UW2
           ltac:(rewrite CG1; exact CGL) ltac:(rewrite FS1; exact FrMax) ltac:(rewrite LV1; cbn [length]; lia)
           ltac:(rewrite CR1; destruct MC as (M48 & M104 & M128 & M56); lia) ENV2 T c3 HA3).
  clear HA3 CTX2 UW2.
  intros c4 (Σ2 & v2 & H4 & LV2 & FS2 & SZ2 & CR2 & P2 & Q2 & U2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 H4) as (ms4 & (m3 & (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->)
                                               & (ART3 & MI3 & WM3 & STK3) & PR3 & ENV3 & LK3 & ACCK3) & HA4). clear H4.
  rewrite EU in STK3, PR3.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_2) in HA4 by (unfold SITE_ossl_property_string_data_new_2; first [lia | reflexivity]).
  rewrite LV1 in LV2. rewrite FS1 in FS2. rewrite SZ1 in SZ2. rewrite CG1 in CG2. rewrite CR1 in CR2.
  assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m2 m3 _ _ FR2 PR3 WM3); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (OBJ3 : rw_cells asegs m3 v1 [CB 48 (repeat (Z_to_bv 8 0) 48)]).
  { apply (wg_keep_live _ _ _ _ m2 m3 v1 48 v1 _ OBJ2 PR3 WM3 IN1); [lia | cbn; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (PC3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m3).
  { apply (pres_fp_trans _ _ _ _ m m2 m3 PC2).
    apply (PresUp Σ1 m2 m2 m3 [(v1, 48)] (bv_unsigned sp + -96) _ ART2 LV1 FS1 SZ1 ltac:(lia) PR3).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m2 m3 WC2 WM3) as WC3.
  clear PR3 FR2 OBJ2 STK2 MI2 ART2 PC2 WC2 ENV2 ACC2 SH2 UT2.

  (* segment 2: store of the lock and the call of OPENSSL_LH_new for the names *)
  assert (IN1b : In (v1, 48) (rt_live RT Σ2)) by (rewrite LV2; right; left; reflexivity).
  assert (INk : In (v2, 40) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  destruct (Fresh Σ2 m3 v2 40 ART3 INk SZ2 ltac:(lia)) as (LOk & HIk & BLk).
  assert (Dk1 : wp_apbox (v2 + 40 <= v1 \/ v1 + 48 <= v2)) by exact (af_live_disj RT AF Σ2 m3 v2 40 v1 48 [] _ ART3 LV2 ltac:(left; reflexivity)).
  pose proof (Consts Σ2 m3 ART3) as (SH3 & UT3).
  pose proof (proj2 (af_acc_live RT AF Σ2 m3 v1 48 ART3 IN1b)) as ACC3.
  assert (GR1 : negb (bv_eqb (Z_to_bv 64 (Z.land v1 7)) (Z_to_bv 64 0)) = false) by (rewrite wg_land7, AL1 by lia; reflexivity).
  pose proof (ossl_property_string_data_new_s2_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_2)
                w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 v1 v2 j F3 fc3 m3 lo STK3 ROOM LOMIN SPMAX OBJ3 FR3 SH3 ltac:(lia) ltac:(lia) UT3
                ACC3 AL1 LO1 HI1 BL1 GR1 MI3) as W.
  cl_lift W HA4 c5 H5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 H5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & OBJ4 & FR4 & STK4 & ShOff_s2) & HA5). clear H5 HA4 ShOff_s2.
  assert (ART4 : ART RT Σ2 m4) by (apply (ArtStore Σ2 m3 m4 v1 48 _ ART3 IN1b MU4 WM4); intros x Hx; cbn [outside] in Hx; lia).
  assert (PC4 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m4).
  { apply (pres_fp_trans _ _ _ _ m m3 m4 PC3).
    apply (PresUp Σ2 m3 m3 m4 [(v2, 40); (v1, 48)] (bv_unsigned sp) _ ART3 LV2 FS2 SZ2 ltac:(lia) (fun a _ Ho => MU4 a Ho)).
    intros x Hx. right. exists v1, 48. split; [right; left; reflexivity | cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m3 m4 WC3 WM4) as WC4.
  assert (ENV4 : cl_env m4 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m3 m4 _ canary ENV3 MU4). apply cl_fp_cons; [right; left; unfold ssp_guard; lia | apply cl_fp_nil]. }
  assert (LK4 : rw_cells asegs m4 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m3 m4 v2 _ LK3 MU4 WM4). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split;
    [clear - Hx Dk1; unfold wp_apbox in Dk1; lia | exact I]. }
  clear MU4 WM4 ART3 MI3 OBJ3 FR3 STK3 PC3 WC3 ENV3 LK3 SH3 UT3 ACC3.

  (* call 3: OPENSSL_LH_new for the property names *)
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_OPENSSL_LH_new SITE_ossl_property_string_data_new_3 m m4 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m4 PC4) (TopCells m4 j FR4) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX3 UW3].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_3) in CTX3 by (unfold SITE_ossl_property_string_data_new_3; lia).
  rewrite <- CG2 in CTX3.
  apply (C_OPENSSL_LH_new Σ2 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_3) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp w0 w1 w2 sp (Z_to_bv 64 v1)
           (Z_to_bv 64 0x20bf48) (Z_to_bv 64 0x20bf8c) d2 d3 d4 d5 d6 d7 (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m4
           lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST TPv ART4 MI4 (CallAt Σ2 m4 SZ2 STK4) ltac:(rewrite EU; unfold RT_STACK; lia) CTX3 UW3
           ltac:(rewrite CG2; exact CGH) ltac:(rewrite LV2; cbn [length]; lia) ltac:(rewrite CR2; destruct MC as (M48 & M104 & M128 & M56); lia)
           ENV4 eq_refl eq_refl T c5 HA5).
  clear HA5 CTX3 UW3.
  intros c6 (Σ3 & pl1 & pb1 & H6 & LV3 & FS3 & SZ3 & CR3 & Pl1 & Ql1 & Ul1 & Pb1 & Qb1 & Ub1 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 H6) as (ms6 & (m5 & (e0 & e1 & e2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & F5 & fc5 & ->)
                                               & (ART5 & MI5 & WM5 & STK5) & PR5 & ENV5 & _ & _ & _ & _ & L1C5 & B1C5) & HA6). clear H6.
  rewrite EU in STK5, PR5.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_3) in HA6 by (unfold SITE_ossl_property_string_data_new_3; first [lia | reflexivity]).
  rewrite LV2 in LV3. rewrite FS2 in FS3. rewrite SZ2 in SZ3. rewrite CG2 in CG3. rewrite CR2 in CR3.
  assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m4 m5 _ _ FR4 PR5 WM5); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }

  assert (OBJ5 : rw_cells asegs m5 v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]).
  { apply (wg_keep_live _ _ _ _ m4 m5 v1 48 v1 _ OBJ4 PR5 WM5 IN1b); [lia | cbn; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (LK5 : rw_cells asegs m5 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m4 m5 v2 40 v2 _ LK4 PR5 WM5 INk); [lia | cbn; lia |].
    intros x Hx. cbn [outside]. unfold G_ALLOW_CUST. split; [lia | exact I]. }
  assert (PC5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m5).
  { apply (pres_fp_trans _ _ _ _ m m4 m5 PC4).
    apply (PresUp Σ2 m4 m4 m5 [(v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART4 LV2 FS2 SZ2 ltac:(lia) PR5).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m4 m5 WC4 WM5) as WC5.
  assert (IN1c : In (v1, 48) (rt_live RT Σ3)) by (rewrite LV3; do 3 right; left; reflexivity).
  assert (INkc : In (v2, 40) (rt_live RT Σ3)) by (rewrite LV3; do 2 right; left; reflexivity).
  assert (INl1 : In (pl1, 104) (rt_live RT Σ3)) by (rewrite LV3; right; left; reflexivity).
  assert (INb1 : In (pb1, 128) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
  destruct (Fresh Σ3 m5 pl1 104 ART5 INl1 SZ3 ltac:(lia)) as (LOl1 & HIl1 & BLl1).
  destruct (Fresh Σ3 m5 pb1 128 ART5 INb1 SZ3 ltac:(lia)) as (LOb1 & HIb1 & BLb1).
  assert (Db1l1 : wp_apbox (pb1 + 128 <= pl1 \/ pl1 + 104 <= pb1)) by exact (af_live_disj RT AF Σ3 m5 pb1 128 pl1 104 [] _ ART5 LV3 ltac:(left; reflexivity)).
  assert (Db1k : wp_apbox (pb1 + 128 <= v2 \/ v2 + 40 <= pb1)) by exact (af_live_disj RT AF Σ3 m5 pb1 128 v2 40 [] _ ART5 LV3 ltac:(right; left; reflexivity)).
  assert (Db11 : wp_apbox (pb1 + 128 <= v1 \/ v1 + 48 <= pb1)) by exact (af_live_disj RT AF Σ3 m5 pb1 128 v1 48 [] _ ART5 LV3 ltac:(do 2 right; left; reflexivity)).
  assert (Dl1k : wp_apbox (pl1 + 104 <= v2 \/ v2 + 40 <= pl1)) by exact (af_live_disj RT AF Σ3 m5 pl1 104 v2 40 [(pb1, 128)] _ ART5 LV3 ltac:(right; left; reflexivity)).
  assert (Dl11 : wp_apbox (pl1 + 104 <= v1 \/ v1 + 48 <= pl1)) by exact (af_live_disj RT AF Σ3 m5 pl1 104 v1 48 [(pb1, 128)] _ ART5 LV3 ltac:(do 2 right; left;
    reflexivity)).
  clear PR5 FR4 OBJ4 LK4 STK4 MI4 ART4 PC4 WC4 ENV4 WM5.

  (* segment 3: thunk arguments for the names table *)
  pose proof (Consts Σ3 m5 ART5) as (SH5 & UT5).
  pose proof (ossl_property_string_data_new_s3_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_3)
                e0 e1 e2 f1 f2 f3 f4 f5 f6 f7 e3 e4 e5 e6 v1 v2 pl1 j F5 fc5 m5 lo STK5 ROOM LOMIN SPMAX OBJ5 FR5 SH5 ltac:(lia) ltac:(lia) ltac:(lia) UT5 MI5) as W.
  cl_lift W HA6 c7 H7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 H7) as (ms7 & (-> & ShOff_s3) & HA7). clear H7 HA6 ShOff_s3.

  (* call 4: OPENSSL_LH_set_thunks on the names table *)
  apply (C_OPENSSL_LH_set_thunks Σ3 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp e0 e1 e2 sp
           (Z_to_bv 64 v1) (Z_to_bv 64 pl1) (Z_to_bv 64 0x20c77c) (Z_to_bv 64 0x20c79c) (Z_to_bv 64 0x20c7bc) (Z_to_bv 64 0x20c7dc) f5 f6 f7
           (Z_to_bv 64 v2) s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 e3 e4 e5 e6 F5 fc5 m5 lo pl1 (Z_to_bv 64 pb1) (Z_to_bv 64 0x20bf8c)
           (Z_to_bv 64 0x20bf48) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256)
           FDO MST eq_refl TPv ART5 MI5 (CallAt Σ3 m5 SZ3 STK5) ltac:(rewrite EU; lia) INl1 Ql1 L1C5 T c7 HA7).
  clear HA7.
  intros c8 H8.
  destruct (ASTA_unpack RT Σ3 _ _ c8 H8) as (ms8 & (m6 & (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & F6 & fc6 & ->)
                                               & (ART6 & MI6 & WM6 & STK6) & PR6 & L1C6) & HA8). clear H8.
  rewrite EU in STK6, PR6.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_4) in HA8 by (unfold SITE_ossl_property_string_data_new_4; first [lia | reflexivity]).
  assert (FR6 : rw_cells asegs m6 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m5 m6 _ _ FR5 PR6 WM6); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (OBJ6 : rw_cells asegs m6 v1 [C8 (Z_to_bv 64 v2); CB 40 (repeat (Z_to_bv 8 0) 40)]).
  { apply (wg_keep_live _ _ _ _ m5 m6 v1 48 v1 _ OBJ5 PR6 WM6 IN1c); [lia | cbn; lia |]. intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat
    Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl11; unfold wp_apbox in Dl11; lia | exact I]. }
  assert (LK6 : rw_cells asegs m6 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m5 m6 v2 40 v2 _ LK5 PR6 WM6 INkc); [lia | cbn; lia |]. intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat
    Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl1k; unfold wp_apbox in Dl1k; lia | exact I]. }
  assert (B1C6 : rw_cells asegs m6 pb1 [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m5 m6 pb1 128 pb1 _ B1C5 PR6 WM6 INb1); [lia | cbn; lia |]. intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat
    Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Db1l1; unfold wp_apbox in Db1l1; lia | exact I]. }
  assert (PC6 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m6).
  { apply (pres_fp_trans _ _ _ _ m m5 m6 PC5).
    apply (PresUp Σ3 m5 m5 m6 [(pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART5 LV3 FS3 SZ3 ltac:(lia) PR6).
    intros x Hx. right. exists pl1, 104. split; [right; left; reflexivity | cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m5 m6 WC5 WM6) as WC6.
  assert (ENV6 : cl_env m6 (Z_to_bv 8 1) canary) by (apply (EnvKeep _ _ _ _ m5 m6 _ ENV5 PR6); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [lia | exact I]).
  clear PR6 WM6 FR5 OBJ5 LK5 B1C5 L1C5 STK5 MI5 ART5 PC5 WC5 ENV5 SH5 UT5.

  (* segment 4: store of the names table and the call of OPENSSL_LH_new for the values *)
  pose proof (Consts Σ3 m6 ART6) as (SH6 & UT6).
  pose proof (proj2 (af_acc_live RT AF Σ3 m6 v1 48 ART6 IN1c)) as ACC6.
  pose proof (ossl_property_string_data_new_s4_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_4)
                g0 g1 g2 h1 h2 h3 h4 h5 h6 h7 g3 g4 g5 g6 v1 v2 pl1 j F6 fc6 m6 lo STK6 ROOM LOMIN SPMAX OBJ6 FR6 SH6 ltac:(lia) ltac:(lia) ltac:(lia) UT6
                ACC6 AL1 LO1 HI1 BL1 MI6) as W.
  cl_lift W HA8 c9 H9.
  destruct (ASTA_unpack RT Σ3 _ _ c9 H9) as (ms9 & (m7 & -> & MU7 & WM7 & MI7 & OBJ7 & FR7 & STK7 & ShOff_s4) & HA9). clear H9 HA8 ShOff_s4.
  assert (ART7 : ART RT Σ3 m7) by (apply (ArtStore Σ3 m6 m7 v1 48 _ ART6 IN1c MU7 WM7); intros x Hx; cbn [outside] in Hx; lia).
  assert (PC7 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m7).
  { apply (pres_fp_trans _ _ _ _ m m6 m7 PC6).
    apply (PresUp Σ3 m6 m6 m7 [(pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp) _ ART6 LV3 FS3 SZ3 ltac:(lia) (fun a _ Ho => MU7 a Ho)).
    intros x Hx. right. exists v1, 48. split; [do 3 right; left; reflexivity | cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m6 m7 WC6 WM7) as WC7.
  assert (ENV7 : cl_env m7 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m6 m7 _ canary ENV6 MU7). apply cl_fp_cons; [right; left; unfold ssp_guard; lia | apply cl_fp_nil]. }
  assert (LK7 : rw_cells asegs m7 v2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m6 m7 v2 _ LK6 MU7 WM7). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split;
    [clear - Hx Dk1; unfold wp_apbox in Dk1; lia | exact I]. }
  assert (L1C7 : rw_cells asegs m7 pl1
                   [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_seg _ m6 m7 pl1 _ L1C6 MU7 WM7). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split;
    [clear - Hx Dl11; unfold wp_apbox in Dl11; lia | exact I]. }
  assert (B1C7 : rw_cells asegs m7 pb1 [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_seg _ m6 m7 pb1 _ B1C6 MU7 WM7). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split;
    [clear - Hx Db11; unfold wp_apbox in Db11; lia | exact I]. }
  clear MU7 WM7 ART6 MI6 OBJ6 FR6 STK6 PC6 WC6 ENV6 LK6 L1C6 B1C6 SH6 UT6 ACC6.

  (* call 5: OPENSSL_LH_new *)
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_OPENSSL_LH_new SITE_ossl_property_string_data_new_5 m m7 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m7 PC7) (TopCells m7 j FR7) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX5 UW5].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_5) in CTX5 by (unfold SITE_ossl_property_string_data_new_5; lia).
  rewrite <- CG3 in CTX5.
  apply (C_OPENSSL_LH_new Σ3 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_5) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp g0 g1 g2 sp (Z_to_bv 64 v1) (Z_to_bv 64
    0x20bf48) (Z_to_bv 64 0x20bf8c) h2 h3 h4 h5 h6 h7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9
    s10 s11 g3 g4 g5 g6 F6 fc6 m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST TPv ART7 MI7 (CallAt Σ3 m7 SZ3 STK7) ltac:(rewrite EU; unfold RT_STACK; lia) CTX5 UW5
           ltac:(rewrite CG3; exact CGH) ltac:(rewrite LV3; cbn [length]; lia) ltac:(rewrite CR3; destruct MC as (M48 & M104 & M128 & M56); lia) ENV7 eq_refl eq_refl T c9
             HA9).
  clear HA9 CTX5 UW5.
  intros c10 (Σ4 & pl2 & pb2 & H10 & LV4 & FS4 & SZ4 & CR4 & Pl2 & Ql2 & Ul2 & Pb2 & Qb2 & Ub2 & CG4).
  destruct (ASTA_unpack RT Σ4 _ _ c10 H10) as (ms10 & (m8 & (o5_0 & o5_1 & o5_2 & y5_1 & y5_2 & y5_3 & y5_4 & y5_5 & y5_6 & y5_7 & o5_3 & o5_4 & o5_5 & o5_6 & G5 & gc5 & ->)
                                               & (ART8 & MI8 & WM8 & STK8) & PR8 & ENV8 & _ & _ & _ & _ & L2C8 & B2C8) & HA10). clear H10.
  rewrite EU in STK8, PR8.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_5) in HA10 by (unfold SITE_ossl_property_string_data_new_5; first [lia | reflexivity]).
  rewrite LV3 in LV4. rewrite FS3 in FS4. rewrite SZ3 in SZ4. rewrite CG3 in CG4. rewrite CR3 in CR4.
  assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m7 m8 _ _ FR7 PR8 WM8); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx ROOM LOMIN; lia
      | exact I]. }
  assert (B1C8 : rw_cells asegs m8 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m7 m8 pb1 128 pb1 _ B1C7 PR8 WM8 INb1); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOb1; lia |
      exact I]. }
  assert (L1C8 : rw_cells asegs m8 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m7 m8 pl1 104 pl1 _ L1C7 PR8 WM8 INl1); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOl1; lia |
      exact I]. }
  assert (LK8 : rw_cells asegs m8 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m7 m8 v2 40 v2 _ LK7 PR8 WM8 INkc); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOk; lia | exact
      I]. }
  assert (OBJ8 : rw_cells asegs m8 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); CB 32 (repeat (Z_to_bv 8 0) 32)]).
  { apply (wg_keep_live _ _ _ _ m7 m8 v1 48 v1 _ OBJ7 PR8 WM8 IN1c); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LO1; lia | exact
      I]. }
  assert (PC8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m8).
  { apply (pres_fp_trans _ _ _ _ m m7 m8 PC7).
    apply (PresUp Σ3 m7 m7 m8 [(pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART7 LV3 FS3 SZ3 ltac:(lia) PR8).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m7 m8 WC7 WM8) as WC8.
  assert (Inb2_4 : In (pb2, 128) (rt_live RT Σ4)) by (rewrite LV4; left; reflexivity).
  assert (Inl2_4 : In (pl2, 104) (rt_live RT Σ4)) by (rewrite LV4; right; left; reflexivity).
  assert (Inb1_4 : In (pb1, 128) (rt_live RT Σ4)) by (rewrite LV4; do 2 right; left; reflexivity).
  assert (Inl1_4 : In (pl1, 104) (rt_live RT Σ4)) by (rewrite LV4; do 3 right; left; reflexivity).
  assert (Ink_4 : In (v2, 40) (rt_live RT Σ4)) by (rewrite LV4; do 4 right; left; reflexivity).
  assert (In1_4 : In (v1, 48) (rt_live RT Σ4)) by (rewrite LV4; do 5 right; left; reflexivity).
  destruct (Fresh Σ4 m8 pl2 104 ART8 Inl2_4 SZ4 ltac:(lia)) as (LOl2 & HIl2 & BLl2).
  destruct (Fresh Σ4 m8 pb2 128 ART8 Inb2_4 SZ4 ltac:(lia)) as (LOb2 & HIb2 & BLb2).
  assert (Db2l2 : wp_apbox (pb2 + 128 <= pl2 \/ pl2 + 104 <= pb2)) by exact (af_live_disj RT AF Σ4 m8 pb2 128 pl2 104 [] _ ART8 LV4 ltac:(left; reflexivity)).
  assert (Db2b1 : wp_apbox (pb2 + 128 <= pb1 \/ pb1 + 128 <= pb2)) by exact (af_live_disj RT AF Σ4 m8 pb2 128 pb1 128 [] _ ART8 LV4 ltac:(right; left; reflexivity)).
  assert (Db2l1 : wp_apbox (pb2 + 128 <= pl1 \/ pl1 + 104 <= pb2)) by exact (af_live_disj RT AF Σ4 m8 pb2 128 pl1 104 [] _ ART8 LV4 ltac:(do 2 right; left; reflexivity)).
  assert (Db2k : wp_apbox (pb2 + 128 <= v2 \/ v2 + 40 <= pb2)) by exact (af_live_disj RT AF Σ4 m8 pb2 128 v2 40 [] _ ART8 LV4 ltac:(do 3 right; left; reflexivity)).
  assert (Db21 : wp_apbox (pb2 + 128 <= v1 \/ v1 + 48 <= pb2)) by exact (af_live_disj RT AF Σ4 m8 pb2 128 v1 48 [] _ ART8 LV4 ltac:(do 4 right; left; reflexivity)).
  assert (Dl2b1 : wp_apbox (pl2 + 104 <= pb1 \/ pb1 + 128 <= pl2)) by exact (af_live_disj RT AF Σ4 m8 pl2 104 pb1 128 [(pb2, 128)] _ ART8 LV4 ltac:(right; left;
    reflexivity)).
  assert (Dl2l1 : wp_apbox (pl2 + 104 <= pl1 \/ pl1 + 104 <= pl2)) by exact (af_live_disj RT AF Σ4 m8 pl2 104 pl1 104 [(pb2, 128)] _ ART8 LV4 ltac:(do 2 right; left;
    reflexivity)).
  assert (Dl2k : wp_apbox (pl2 + 104 <= v2 \/ v2 + 40 <= pl2)) by exact (af_live_disj RT AF Σ4 m8 pl2 104 v2 40 [(pb2, 128)] _ ART8 LV4 ltac:(do 3 right; left;
    reflexivity)).
  assert (Dl21 : wp_apbox (pl2 + 104 <= v1 \/ v1 + 48 <= pl2)) by exact (af_live_disj RT AF Σ4 m8 pl2 104 v1 48 [(pb2, 128)] _ ART8 LV4 ltac:(do 4 right; left;
    reflexivity)).
  clear PR8 WM8 FR7 STK7 MI7 ART7 PC7 WC7 ENV7 LV3 FS3 SZ3 CR3 CG3 IN1c INkc INl1 INb1 B1C7 L1C7 LK7 OBJ7.

  (* segment 5: thunk arguments for the values table *)
  pose proof (Consts Σ4 m8 ART8) as (SH8 & UT8).
  pose proof (ossl_property_string_data_new_s5_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_5)
                o5_0 o5_1 o5_2 y5_1 y5_2 y5_3 y5_4 y5_5 y5_6 y5_7 o5_3 o5_4 o5_5 o5_6 v1 v2 pl1 pl2 j G5 gc5 m8 lo
                STK8 ROOM LOMIN SPMAX OBJ8 FR8 SH8 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear - Pl1
                  Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) UT8 MI8) as W.
  cl_lift W HA10 c11 H11.
  destruct (ASTA_unpack RT Σ4 _ _ c11 H11) as (ms11 & (-> & ShOff_s5) & HA11). clear H11 HA10 SH8 UT8 ShOff_s5.

  (* call 6: OPENSSL_LH_set_thunks *)
  apply (C_OPENSSL_LH_set_thunks Σ4 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_6) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o5_0 o5_1 o5_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pl2) (Z_to_bv 64 0x20c77c) (Z_to_bv 64 0x20c79c) (Z_to_bv 64 0x20c7bc) (Z_to_bv 64 0x20c7dc) y5_5 y5_6 y5_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) s4 s5
    (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) s8 s9 s10 s11 o5_3 o5_4 o5_5 o5_6 G5 gc5 m8 lo pl2 (Z_to_bv 64 pb2) (Z_to_bv 64 0x20bf8c) (Z_to_bv 64
    0x20bf48) (Z_to_bv 64 8) (Z_to_bv 64 16) (Z_to_bv 64 8) (Z_to_bv 64 512) (Z_to_bv 64 256)
           FDO MST eq_refl TPv ART8 MI8 (CallAt Σ4 m8 SZ4 STK8) ltac:(rewrite EU; lia) Inl2_4 Ql2 L2C8 T c11 HA11).
  clear HA11.
  intros c12 H12.
  destruct (ASTA_unpack RT Σ4 _ _ c12 H12) as (ms12 & (m9 & (o6_0 & o6_1 & o6_2 & y6_1 & y6_2 & y6_3 & y6_4 & y6_5 & y6_6 & y6_7 & o6_3 & o6_4 & o6_5 & o6_6 & G6 & gc6 & ->)
                                               & (ART9 & MI9 & WM9 & STK9) & PR9 & L2C9) & HA12). clear H12.
  rewrite EU in STK9, PR9.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_6) in HA12 by (unfold SITE_ossl_property_string_data_new_6; first [lia | reflexivity]).
  assert (FR9 : rw_cells asegs m9 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m8 m9 _ _ FR8 PR9 WM9); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLl2; lia | exact I]. }
  assert (B2C9 : rw_cells asegs m9 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m8 m9 pb2 128 pb2 _ B2C8 PR9 WM9 Inb2_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Db2l2; unfold wp_apbox in Db2l2; lia
      | exact I]. }
  assert (B1C9 : rw_cells asegs m9 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m8 m9 pb1 128 pb1 _ B1C8 PR9 WM9 Inb1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl2b1; unfold wp_apbox in Dl2b1; lia
      | exact I]. }
  assert (L1C9 : rw_cells asegs m9 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m8 m9 pl1 104 pl1 _ L1C8 PR9 WM9 Inl1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl2l1; unfold wp_apbox in Dl2l1; lia
      | exact I]. }
  assert (LK9 : rw_cells asegs m9 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m8 m9 v2 40 v2 _ LK8 PR9 WM9 Ink_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl2k; unfold wp_apbox in Dl2k; lia |
      exact I]. }
  assert (OBJ9 : rw_cells asegs m9 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); CB 32 (repeat (Z_to_bv 8 0) 32)]).
  { apply (wg_keep_live _ _ _ _ m8 m9 v1 48 v1 _ OBJ8 PR9 WM9 In1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dl21; unfold wp_apbox in Dl21; lia |
      exact I]. }
  assert (PC9 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m9).
  { apply (pres_fp_trans _ _ _ _ m m8 m9 PC8).
    apply (PresUp Σ4 m8 m8 m9 [(pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART8 LV4 FS4 SZ4 ltac:(lia) PR9).
    intros x Hx. right. exists pl2, 104. split; [right; left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m8 m9 WC8 WM9) as WC9.
  assert (ENV9 : cl_env m9 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m8 m9 _ ENV8 PR9); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOl2; lia | exact I]).
  clear PR9 WM9 FR8 STK8 MI8 ART8 PC8 WC8 ENV8 B2C8 L2C8 B1C8 L1C8 LK8 OBJ8.

  (* segment 6: store of the values table and the call of OPENSSL_sk_new_null for the name list *)
  pose proof (Consts Σ4 m9 ART9) as (SH9 & UT9).
  pose proof (proj2 (af_acc_live RT AF Σ4 m9 v1 48 ART9 In1_4)) as ACC9.
  pose proof (ossl_property_string_data_new_s6_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_6)
                o6_0 o6_1 o6_2 y6_1 y6_2 y6_3 y6_4 y6_5 y6_6 y6_7 o6_3 o6_4 o6_5 o6_6 v1 v2 pl1 pl2 j G6 gc6 m9 lo
                STK9 ROOM LOMIN SPMAX OBJ9 FR9 SH9 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear - Pl1
                  Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) UT9 ACC9 AL1 LO1 HI1 BL1 MI9) as W.
  cl_lift W HA12 c13 H13.
  destruct (ASTA_unpack RT Σ4 _ _ c13 H13) as (ms13 & (m10 & -> & MU10 & WM10 & MI10 & OBJ10 & FR10 & STK10 & ShOff_s6) & HA13).
  clear H13 HA12 ShOff_s6.
  assert (ART10 : ART RT Σ4 m10) by (apply (ArtStore Σ4 m9 m10 v1 48 _ ART9 In1_4 MU10 WM10); intros x Hx; clear - Hx; cbn [outside] in Hx; lia).
  assert (PC10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m10).
  { apply (pres_fp_trans _ _ _ _ m m9 m10 PC9).
    apply (PresUp Σ4 m9 m9 m10 [(pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp) _ ART9 LV4 FS4 SZ4 ltac:(lia) (fun a _ Ho => MU10 a
      Ho)).
    intros x Hx. right. exists v1, 48. split; [do 5 right; left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m9 m10 WC9 WM10) as WC10.
  assert (ENV10 : cl_env m10 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m9 m10 _ canary ENV9 MU10). apply cl_fp_cons; [right; left; clear - LO1; unfold ssp_guard; lia | apply cl_fp_nil]. }
  assert (B2C10 : rw_cells asegs m10 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_seg _ m9 m10 pb2 _ B2C9 MU10 WM10). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Db21; unfold wp_apbox in Db21; lia | exact I]. }
  assert (L2C10 : rw_cells asegs m10 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_seg _ m9 m10 pl2 _ L2C9 MU10 WM10). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dl21; unfold wp_apbox in Dl21; lia | exact I]. }
  assert (B1C10 : rw_cells asegs m10 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_seg _ m9 m10 pb1 _ B1C9 MU10 WM10). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Db11; unfold wp_apbox in Db11; lia | exact I]. }
  assert (L1C10 : rw_cells asegs m10 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_seg _ m9 m10 pl1 _ L1C9 MU10 WM10). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dl11; unfold wp_apbox in Dl11; lia | exact I]. }
  assert (LK10 : rw_cells asegs m10 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m9 m10 v2 _ LK9 MU10 WM10). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split;
    [clear - Hx Dk1; unfold wp_apbox in Dk1; lia | exact I]. }
  clear MU10 WM10 ART9 MI9 FR9 STK9 PC9 WC9 ENV9 SH9 UT9 ACC9 B2C9 L2C9 B1C9 L1C9 LK9 OBJ9.

  (* call 7: OPENSSL_sk_new_null *)
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_OPENSSL_sk_new_null SITE_ossl_property_string_data_new_7 m m10 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m10 PC10) (TopCells m10 j FR10) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX7 UW7].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_7) in CTX7 by (unfold SITE_ossl_property_string_data_new_7; lia).
  rewrite <- CG4 in CTX7.
  apply (C_OPENSSL_sk_new_null Σ4 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_7) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o6_0 o6_1 o6_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pl2) (Z_to_bv 64 0) y6_2 y6_3 y6_4 y6_5 y6_6 y6_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1
    + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 o6_3 o6_4 o6_5 o6_6 G6 gc6 m10 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST TPv ART10 MI10 (CallAt Σ4 m10 SZ4 STK10) ltac:(rewrite EU; unfold RT_STACK; lia) CTX7 UW7
           ltac:(rewrite CG4; exact CGS) ltac:(rewrite LV4; cbn [length]; lia) ltac:(rewrite CR4; destruct MC as (M48 & M104 & M128 & M56); lia) ENV10 T c13 HA13).
  clear HA13 CTX7 UW7.
  intros c14 (Σ5 & pq1 & H14 & LV5 & FS5 & SZ5 & CR5 & Pq1 & Qq1 & Uq1 & CG5).
  destruct (ASTA_unpack RT Σ5 _ _ c14 H14) as (ms14 & (m11 & (o7_0 & o7_1 & o7_2 & y7_1 & y7_2 & y7_3 & y7_4 & y7_5 & y7_6 & y7_7 & o7_3 & o7_4 & o7_5 & o7_6 & G7 & gc7 & ->)
                                               & (ART11 & MI11 & WM11 & STK11) & PR11 & ENV11 & _ & _ & Q1C11) & HA14). clear H14.
  rewrite EU in STK11, PR11.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_7) in HA14 by (unfold SITE_ossl_property_string_data_new_7; first [lia | reflexivity]).
  rewrite LV4 in LV5. rewrite FS4 in FS5. rewrite SZ4 in SZ5. rewrite CG4 in CG5. rewrite CR4 in CR5.
  assert (FR11 : rw_cells asegs m11 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m10 m11 _ _ FR10 PR11 WM11); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx ROOM LOMIN; lia
      | exact I]. }
  assert (B2C11 : rw_cells asegs m11 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m10 m11 pb2 128 pb2 _ B2C10 PR11 WM11 Inb2_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOb2; lia |
      exact I]. }
  assert (L2C11 : rw_cells asegs m11 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m10 m11 pl2 104 pl2 _ L2C10 PR11 WM11 Inl2_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOl2; lia |
      exact I]. }
  assert (B1C11 : rw_cells asegs m11 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m10 m11 pb1 128 pb1 _ B1C10 PR11 WM11 Inb1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOb1; lia |
      exact I]. }
  assert (L1C11 : rw_cells asegs m11 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m10 m11 pl1 104 pl1 _ L1C10 PR11 WM11 Inl1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOl1; lia |
      exact I]. }
  assert (LK11 : rw_cells asegs m11 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m10 m11 v2 40 v2 _ LK10 PR11 WM11 Ink_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOk; lia | exact
      I]. }
  assert (OBJ11 : rw_cells asegs m11 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { apply (wg_keep_live _ _ _ _ m10 m11 v1 48 v1 _ OBJ10 PR11 WM11 In1_4); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LO1; lia | exact
      I]. }
  assert (PC11 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m11).
  { apply (pres_fp_trans _ _ _ _ m m10 m11 PC10).
    apply (PresUp Σ4 m10 m10 m11 [(pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART10 LV4 FS4 SZ4 ltac:(lia) PR11).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m10 m11 WC10 WM11) as WC11.
  assert (Inq1_5 : In (pq1, 56) (rt_live RT Σ5)) by (rewrite LV5; left; reflexivity).
  assert (Inb2_5 : In (pb2, 128) (rt_live RT Σ5)) by (rewrite LV5; right; left; reflexivity).
  assert (Inl2_5 : In (pl2, 104) (rt_live RT Σ5)) by (rewrite LV5; do 2 right; left; reflexivity).
  assert (Inb1_5 : In (pb1, 128) (rt_live RT Σ5)) by (rewrite LV5; do 3 right; left; reflexivity).
  assert (Inl1_5 : In (pl1, 104) (rt_live RT Σ5)) by (rewrite LV5; do 4 right; left; reflexivity).
  assert (Ink_5 : In (v2, 40) (rt_live RT Σ5)) by (rewrite LV5; do 5 right; left; reflexivity).
  assert (In1_5 : In (v1, 48) (rt_live RT Σ5)) by (rewrite LV5; do 6 right; left; reflexivity).
  destruct (Fresh Σ5 m11 pq1 56 ART11 Inq1_5 SZ5 ltac:(lia)) as (LOq1 & HIq1 & BLq1).
  assert (Dq1b2 : wp_apbox (pq1 + 56 <= pb2 \/ pb2 + 128 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 pb2 128 [] _ ART11 LV5 ltac:(left; reflexivity)).
  assert (Dq1l2 : wp_apbox (pq1 + 56 <= pl2 \/ pl2 + 104 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 pl2 104 [] _ ART11 LV5 ltac:(right; left; reflexivity)).
  assert (Dq1b1 : wp_apbox (pq1 + 56 <= pb1 \/ pb1 + 128 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 pb1 128 [] _ ART11 LV5 ltac:(do 2 right; left; reflexivity)).
  assert (Dq1l1 : wp_apbox (pq1 + 56 <= pl1 \/ pl1 + 104 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 pl1 104 [] _ ART11 LV5 ltac:(do 3 right; left; reflexivity)).
  assert (Dq1k : wp_apbox (pq1 + 56 <= v2 \/ v2 + 40 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 v2 40 [] _ ART11 LV5 ltac:(do 4 right; left; reflexivity)).
  assert (Dq11 : wp_apbox (pq1 + 56 <= v1 \/ v1 + 48 <= pq1)) by exact (af_live_disj RT AF Σ5 m11 pq1 56 v1 48 [] _ ART11 LV5 ltac:(do 5 right; left; reflexivity)).
  assert (GRq1 : negb (bv_eqb (Z_to_bv 64 (Z.land pq1 7)) (Z_to_bv 64 0)) = false)
    by (rewrite wg_land7, (wg_mod16_8 pq1 Qq1) by lia; reflexivity).
  clear PR11 WM11 FR10 STK10 MI10 ART10 PC10 WC10 ENV10 LV4 FS4 SZ4 CR4 CG4 Inb2_4 Inl2_4 Inb1_4 Inl1_4 Ink_4 In1_4 B2C10 L2C10 B1C10 L1C10 LK10 OBJ10.

  (* segment 7: compare thunk argument for the name list *)
  pose proof (Consts Σ5 m11 ART11) as (SH11 & UT11).
  pose proof (ossl_property_string_data_new_s7_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_7)
                o7_0 o7_1 o7_2 y7_1 y7_2 y7_3 y7_4 y7_5 y7_6 y7_7 o7_3 o7_4 o7_5 o7_6 v1 v2 pl1 pl2 pq1 j G7 gc7 m11 lo
                STK11 ROOM LOMIN SPMAX OBJ11 FR11 SH11 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia) UT11
                  MI11) as W.
  cl_lift W HA14 c15 H15.
  destruct (ASTA_unpack RT Σ5 _ _ c15 H15) as (ms15 & (-> & ShOff_s7) & HA15). clear H15 HA14 SH11 UT11 ShOff_s7.

  (* call 8: OPENSSL_sk_set_cmp_thunks *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o7_0 o7_1 o7_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pq1) (Z_to_bv 64 0x20bfec) y7_2 y7_3 y7_4 y7_5 y7_6 y7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv
    64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 o7_3 o7_4 o7_5 o7_6 G7 gc7 m11 lo pq1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64
    0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
           FDO MST eq_refl TPv ART11 MI11 (CallAt Σ5 m11 SZ5 STK11) ltac:(rewrite EU; lia) Inq1_5 Qq1 Q1C11 GRq1 T c15 HA15).
  clear HA15.
  intros c16 H16.
  destruct (ASTA_unpack RT Σ5 _ _ c16 H16) as (ms16 & (m12 & (o8_0 & o8_1 & o8_2 & y8_1 & y8_2 & y8_3 & y8_4 & y8_5 & y8_6 & y8_7 & o8_3 & o8_4 & o8_5 & o8_6 & G8 & gc8 & ->)
                                               & (ART12 & MI12 & WM12 & STK12) & PR12 & Q1C12) & HA16). clear H16.
  rewrite EU in STK12, PR12.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_8) in HA16 by (unfold SITE_ossl_property_string_data_new_8; first [lia | reflexivity]).
  assert (FR12 : rw_cells asegs m12 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m11 m12 _ _ FR11 PR12 WM12); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq1; lia | exact I]. }
  assert (B2C12 : rw_cells asegs m12 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m11 m12 pb2 128 pb2 _ B2C11 PR12 WM12 Inb2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b2; unfold wp_apbox in Dq1b2; lia
      | exact I]. }
  assert (L2C12 : rw_cells asegs m12 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m11 m12 pl2 104 pl2 _ L2C11 PR12 WM12 Inl2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l2; unfold wp_apbox in Dq1l2; lia
      | exact I]. }
  assert (B1C12 : rw_cells asegs m12 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m11 m12 pb1 128 pb1 _ B1C11 PR12 WM12 Inb1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b1; unfold wp_apbox in Dq1b1; lia
      | exact I]. }
  assert (L1C12 : rw_cells asegs m12 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m11 m12 pl1 104 pl1 _ L1C11 PR12 WM12 Inl1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l1; unfold wp_apbox in Dq1l1; lia
      | exact I]. }
  assert (LK12 : rw_cells asegs m12 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m11 m12 v2 40 v2 _ LK11 PR12 WM12 Ink_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1k; unfold wp_apbox in Dq1k; lia |
      exact I]. }
  assert (OBJ12 : rw_cells asegs m12 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { apply (wg_keep_live _ _ _ _ m11 m12 v1 48 v1 _ OBJ11 PR12 WM12 In1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq11; unfold wp_apbox in Dq11; lia |
      exact I]. }
  assert (PC12 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m12).
  { apply (pres_fp_trans _ _ _ _ m m11 m12 PC11).
    apply (PresUp Σ5 m11 m11 m12 [(pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART11 LV5 FS5 SZ5 ltac:(lia)
      PR12).
    intros x Hx. right. exists pq1, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m11 m12 WC11 WM12) as WC12.
  assert (ENV12 : cl_env m12 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m11 m12 _ ENV11 PR12); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq1; lia | exact I]).
  clear PR12 WM12 FR11 STK11 MI11 ART11 PC11 WC11 ENV11 Q1C11 B2C11 L2C11 B1C11 L1C11 LK11 OBJ11.

  (* segment 8: copy thunk argument for the name list *)
  pose proof (Consts Σ5 m12 ART12) as (SH12 & UT12).
  pose proof (ossl_property_string_data_new_s8_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_8)
                o8_0 o8_1 o8_2 y8_1 y8_2 y8_3 y8_4 y8_5 y8_6 y8_7 o8_3 o8_4 o8_5 o8_6 v1 v2 pl1 pl2 pq1 j G8 gc8 m12 lo
                STK12 ROOM LOMIN SPMAX OBJ12 FR12 SH12 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia) UT12
                  MI12) as W.
  cl_lift W HA16 c17 H17.
  destruct (ASTA_unpack RT Σ5 _ _ c17 H17) as (ms17 & (-> & ShOff_s8) & HA17). clear H17 HA16 SH12 UT12 ShOff_s8.

  (* call 9: OPENSSL_sk_set_copy_thunks *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_9) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o8_0 o8_1 o8_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pq1) (Z_to_bv 64 0x20c018) y8_2 y8_3 y8_4 y8_5 y8_6 y8_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv
    64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 o8_3 o8_4 o8_5 o8_6 G8 gc8 m12 lo pq1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64
    0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0x20bfec) (Z_to_bv 64 0) (Z_to_bv 64 0)
           FDO MST eq_refl TPv ART12 MI12 (CallAt Σ5 m12 SZ5 STK12) ltac:(rewrite EU; lia) Inq1_5 Qq1 Q1C12 GRq1 T c17 HA17).
  clear HA17.
  intros c18 H18.
  destruct (ASTA_unpack RT Σ5 _ _ c18 H18) as (ms18 & (m13 & (o9_0 & o9_1 & o9_2 & y9_1 & y9_2 & y9_3 & y9_4 & y9_5 & y9_6 & y9_7 & o9_3 & o9_4 & o9_5 & o9_6 & G9 & gc9 & ->)
                                               & (ART13 & MI13 & WM13 & STK13) & PR13 & Q1C13) & HA18). clear H18.
  rewrite EU in STK13, PR13.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_9) in HA18 by (unfold SITE_ossl_property_string_data_new_9; first [lia | reflexivity]).
  assert (FR13 : rw_cells asegs m13 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m12 m13 _ _ FR12 PR13 WM13); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq1; lia | exact I]. }
  assert (B2C13 : rw_cells asegs m13 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m12 m13 pb2 128 pb2 _ B2C12 PR13 WM13 Inb2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b2; unfold wp_apbox in Dq1b2; lia
      | exact I]. }
  assert (L2C13 : rw_cells asegs m13 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m12 m13 pl2 104 pl2 _ L2C12 PR13 WM13 Inl2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l2; unfold wp_apbox in Dq1l2; lia
      | exact I]. }
  assert (B1C13 : rw_cells asegs m13 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m12 m13 pb1 128 pb1 _ B1C12 PR13 WM13 Inb1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b1; unfold wp_apbox in Dq1b1; lia
      | exact I]. }
  assert (L1C13 : rw_cells asegs m13 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m12 m13 pl1 104 pl1 _ L1C12 PR13 WM13 Inl1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l1; unfold wp_apbox in Dq1l1; lia
      | exact I]. }
  assert (LK13 : rw_cells asegs m13 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m12 m13 v2 40 v2 _ LK12 PR13 WM13 Ink_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1k; unfold wp_apbox in Dq1k; lia |
      exact I]. }
  assert (OBJ13 : rw_cells asegs m13 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { apply (wg_keep_live _ _ _ _ m12 m13 v1 48 v1 _ OBJ12 PR13 WM13 In1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq11; unfold wp_apbox in Dq11; lia |
      exact I]. }
  assert (PC13 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m13).
  { apply (pres_fp_trans _ _ _ _ m m12 m13 PC12).
    apply (PresUp Σ5 m12 m12 m13 [(pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART12 LV5 FS5 SZ5 ltac:(lia)
      PR13).
    intros x Hx. right. exists pq1, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m12 m13 WC12 WM13) as WC13.
  assert (ENV13 : cl_env m13 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m12 m13 _ ENV12 PR13); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq1; lia | exact I]).
  clear PR13 WM13 FR12 STK12 MI12 ART12 PC12 WC12 ENV12 Q1C12 B2C12 L2C12 B1C12 L1C12 LK12 OBJ12.

  (* segment 9: free thunk argument for the name list *)
  pose proof (Consts Σ5 m13 ART13) as (SH13 & UT13).
  pose proof (ossl_property_string_data_new_s9_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_9)
                o9_0 o9_1 o9_2 y9_1 y9_2 y9_3 y9_4 y9_5 y9_6 y9_7 o9_3 o9_4 o9_5 o9_6 v1 v2 pl1 pl2 pq1 j G9 gc9 m13 lo
                STK13 ROOM LOMIN SPMAX OBJ13 FR13 SH13 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia) UT13
                  MI13) as W.
  cl_lift W HA18 c19 H19.
  destruct (ASTA_unpack RT Σ5 _ _ c19 H19) as (ms19 & (-> & ShOff_s9) & HA19). clear H19 HA18 SH13 UT13 ShOff_s9.

  (* call 10: OPENSSL_sk_set_thunks *)
  apply (C_OPENSSL_sk_set_thunks Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_10) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o9_0 o9_1 o9_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pq1) (Z_to_bv 64 0x20c040) y9_2 y9_3 y9_4 y9_5 y9_6 y9_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) s5 (Z_to_bv 64 2147450880) (Z_to_bv
    64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) s9 s10 s11 o9_3 o9_4 o9_5 o9_6 G9 gc9 m13 lo pq1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64
    0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0x20bfec) (Z_to_bv 64 0) (Z_to_bv 64 0x20c018)
           FDO MST eq_refl TPv ART13 MI13 (CallAt Σ5 m13 SZ5 STK13) ltac:(rewrite EU; lia) Inq1_5 Qq1 Q1C13 GRq1 T c19 HA19).
  clear HA19.
  intros c20 H20.
  destruct (ASTA_unpack RT Σ5 _ _ c20 H20) as (ms20 & (m14 & (o10_0 & o10_1 & o10_2 & y10_1 & y10_2 & y10_3 & y10_4 & y10_5 & y10_6 & y10_7 & o10_3 & o10_4 & o10_5 &
    o10_6 & G10 & gc10 & ->)
                                               & (ART14 & MI14 & WM14 & STK14) & PR14 & Q1C14) & HA20). clear H20.
  rewrite EU in STK14, PR14.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_10) in HA20 by (unfold SITE_ossl_property_string_data_new_10; first [lia | reflexivity]).
  assert (FR14 : rw_cells asegs m14 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m13 m14 _ _ FR13 PR14 WM14); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq1; lia | exact I]. }
  assert (B2C14 : rw_cells asegs m14 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m13 m14 pb2 128 pb2 _ B2C13 PR14 WM14 Inb2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b2; unfold wp_apbox in Dq1b2; lia
      | exact I]. }
  assert (L2C14 : rw_cells asegs m14 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m13 m14 pl2 104 pl2 _ L2C13 PR14 WM14 Inl2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l2; unfold wp_apbox in Dq1l2; lia
      | exact I]. }
  assert (B1C14 : rw_cells asegs m14 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m13 m14 pb1 128 pb1 _ B1C13 PR14 WM14 Inb1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1b1; unfold wp_apbox in Dq1b1; lia
      | exact I]. }
  assert (L1C14 : rw_cells asegs m14 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m13 m14 pl1 104 pl1 _ L1C13 PR14 WM14 Inl1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1l1; unfold wp_apbox in Dq1l1; lia
      | exact I]. }
  assert (LK14 : rw_cells asegs m14 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m13 m14 v2 40 v2 _ LK13 PR14 WM14 Ink_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq1k; unfold wp_apbox in Dq1k; lia |
      exact I]. }
  assert (OBJ14 : rw_cells asegs m14 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { apply (wg_keep_live _ _ _ _ m13 m14 v1 48 v1 _ OBJ13 PR14 WM14 In1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq11; unfold wp_apbox in Dq11; lia |
      exact I]. }
  assert (PC14 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m14).
  { apply (pres_fp_trans _ _ _ _ m m13 m14 PC13).
    apply (PresUp Σ5 m13 m13 m14 [(pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART13 LV5 FS5 SZ5 ltac:(lia)
      PR14).
    intros x Hx. right. exists pq1, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m13 m14 WC13 WM14) as WC14.
  assert (ENV14 : cl_env m14 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m13 m14 _ ENV13 PR14); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq1; lia | exact I]).
  clear PR14 WM14 FR13 STK13 MI13 ART13 PC13 WC13 ENV13 Q1C13 B2C13 L2C13 B1C13 L1C13 LK13 OBJ13.

  (* segment 10: store of the name list and the call of OPENSSL_sk_new_null for the value list *)
  pose proof (Consts Σ5 m14 ART14) as (SH14 & UT14).
  pose proof (proj2 (af_acc_live RT AF Σ5 m14 v1 48 ART14 In1_5)) as ACC14.
  pose proof (ossl_property_string_data_new_s10_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_10)
                o10_0 o10_1 o10_2 y10_1 y10_2 y10_3 y10_4 y10_5 y10_6 y10_7 o10_3 o10_4 o10_5 o10_6 v1 v2 pl1 pl2 pq1 j G10 gc10 m14 lo
                STK14 ROOM LOMIN SPMAX OBJ14 FR14 SH14 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia) UT14
                  ACC14 AL1 LO1 HI1 BL1 MI14) as W.
  cl_lift W HA20 c21 H21.
  destruct (ASTA_unpack RT Σ5 _ _ c21 H21) as (ms21 & (m15 & -> & MU15 & WM15 & MI15 & OBJ15 & FR15 & STK15 & ShOff_s10) & HA21).
  clear H21 HA20 ShOff_s10.
  assert (ART15 : ART RT Σ5 m15) by (apply (ArtStore Σ5 m14 m15 v1 48 _ ART14 In1_5 MU15 WM15); intros x Hx; clear - Hx; cbn [outside] in Hx; lia).
  assert (PC15 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m15).
  { apply (pres_fp_trans _ _ _ _ m m14 m15 PC14).
    apply (PresUp Σ5 m14 m14 m15 [(pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp) _ ART14 LV5 FS5 SZ5 ltac:(lia) (fun a _
      Ho => MU15 a Ho)).
    intros x Hx. right. exists v1, 48. split; [do 6 right; left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m14 m15 WC14 WM15) as WC15.
  assert (ENV15 : cl_env m15 (Z_to_bv 8 1) canary).
  { apply (cl_env_seg _ m14 m15 _ canary ENV14 MU15). apply cl_fp_cons; [right; left; clear - LO1; unfold ssp_guard; lia | apply cl_fp_nil]. }
  assert (Q1C15 : rw_cells asegs m15 pq1
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
  { apply (wg_keep_seg _ m14 m15 pq1 _ Q1C14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dq11; unfold wp_apbox in Dq11; lia | exact I]. }
  assert (B2C15 : rw_cells asegs m15 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_seg _ m14 m15 pb2 _ B2C14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Db21; unfold wp_apbox in Db21; lia | exact I]. }
  assert (L2C15 : rw_cells asegs m15 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_seg _ m14 m15 pl2 _ L2C14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dl21; unfold wp_apbox in Dl21; lia | exact I]. }
  assert (B1C15 : rw_cells asegs m15 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_seg _ m14 m15 pb1 _ B1C14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Db11; unfold wp_apbox in Db11; lia | exact I]. }
  assert (L1C15 : rw_cells asegs m15 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_seg _ m14 m15 pl1 _ L1C14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dl11; unfold wp_apbox in Dl11; lia | exact I]. }
  assert (LK15 : rw_cells asegs m15 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_seg _ m14 m15 v2 _ LK14 MU15 WM15). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
    split; [clear - Hx Dk1; unfold wp_apbox in Dk1; lia | exact I]. }
  clear MU15 WM15 ART14 MI14 FR14 STK14 PC14 WC14 ENV14 SH14 UT14 ACC14 Q1C14 B2C14 L2C14 B1C14 L1C14 LK14 OBJ14.

  (* call 11: OPENSSL_sk_new_null *)
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_property_string_data_new e_OPENSSL_sk_new_null SITE_ossl_property_string_data_new_11 m m15 ra s0 sp
              (Z_to_bv 64 (bv_unsigned sp + -96)) outer CTX0 ltac:(apply (proj1 CGH0); cbn [In]; tauto) ltac:(apply (proj2 CGH0); cbn [In]; tauto)
              UW0 (AgOf m15 PC15) (TopCells m15 j FR15) ltac:(rewrite EU; lia) ltac:(unfold USTACK_TOP; lia)) as [CTX11 UW11].
  rewrite <- (unsigned_lit SITE_ossl_property_string_data_new_11) in CTX11 by (unfold SITE_ossl_property_string_data_new_11; lia).
  rewrite <- CG5 in CTX11.
  apply (C_OPENSSL_sk_new_null Σ5 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_11) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o10_0 o10_1 o10_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pq1) (Z_to_bv 64 0) y10_2 y10_3 y10_4 y10_5 y10_6 y10_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32)) (Z_to_bv 64
    2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 o10_3 o10_4 o10_5
    o10_6 G10 gc10 m15 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST TPv ART15 MI15 (CallAt Σ5 m15 SZ5 STK15) ltac:(rewrite EU; unfold RT_STACK; lia) CTX11 UW11
           ltac:(rewrite CG5; exact CGS) ltac:(rewrite LV5; cbn [length]; lia) ltac:(rewrite CR5; destruct MC as (M48 & M104 & M128 & M56); lia) ENV15 T c21 HA21).
  clear HA21 CTX11 UW11.
  intros c22 (Σ6 & pq2 & H22 & LV6 & FS6 & SZ6 & CR6 & Pq2 & Qq2 & Uq2 & CG6).
  destruct (ASTA_unpack RT Σ6 _ _ c22 H22) as (ms22 & (m16 & (o11_0 & o11_1 & o11_2 & y11_1 & y11_2 & y11_3 & y11_4 & y11_5 & y11_6 & y11_7 & o11_3 & o11_4 & o11_5 &
    o11_6 & G11 & gc11 & ->)
                                               & (ART16 & MI16 & WM16 & STK16) & PR16 & ENV16 & _ & _ & Q2C16) & HA22). clear H22.
  rewrite EU in STK16, PR16.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_11) in HA22 by (unfold SITE_ossl_property_string_data_new_11; first [lia | reflexivity]).
  rewrite LV5 in LV6. rewrite FS5 in FS6. rewrite SZ5 in SZ6. rewrite CG5 in CG6. rewrite CR5 in CR6.
  assert (FR16 : rw_cells asegs m16 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m15 m16 _ _ FR15 PR16 WM16); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx ROOM LOMIN; lia
      | exact I]. }
  assert (Q1C16 : rw_cells asegs m16 pq1
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 pq1 56 pq1 _ Q1C15 PR16 WM16 Inq1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOq1; lia |
      exact I]. }
  assert (B2C16 : rw_cells asegs m16 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 pb2 128 pb2 _ B2C15 PR16 WM16 Inb2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOb2; lia |
      exact I]. }
  assert (L2C16 : rw_cells asegs m16 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 pl2 104 pl2 _ L2C15 PR16 WM16 Inl2_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOl2; lia |
      exact I]. }
  assert (B1C16 : rw_cells asegs m16 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 pb1 128 pb1 _ B1C15 PR16 WM16 Inb1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOb1; lia |
      exact I]. }
  assert (L1C16 : rw_cells asegs m16 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 pl1 104 pl1 _ L1C15 PR16 WM16 Inl1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOl1; lia |
      exact I]. }
  assert (LK16 : rw_cells asegs m16 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m15 m16 v2 40 v2 _ LK15 PR16 WM16 Ink_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LOk; lia | exact
      I]. }
  assert (OBJ16 : rw_cells asegs m16 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 pq1); CB 8 (repeat (Z_to_bv 8 0) 8)]).
  { apply (wg_keep_live _ _ _ _ m15 m16 v1 48 v1 _ OBJ15 PR16 WM16 In1_5); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. unfold G_ALLOW_CUST. split; [clear - Hx LO1; lia | exact
      I]. }
  assert (PC16 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m16).
  { apply (pres_fp_trans _ _ _ _ m m15 m16 PC15).
    apply (PresUp Σ5 m15 m15 m16 [(pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART15 LV5 FS5 SZ5 ltac:(lia)
      PR16).
    intros x Hx. left. cbn [outside] in Hx. lia. }
  pose proof (wmono_trans asegs m m15 m16 WC15 WM16) as WC16.
  assert (Inq2_6 : In (pq2, 56) (rt_live RT Σ6)) by (rewrite LV6; left; reflexivity).
  assert (Inq1_6 : In (pq1, 56) (rt_live RT Σ6)) by (rewrite LV6; right; left; reflexivity).
  assert (Inb2_6 : In (pb2, 128) (rt_live RT Σ6)) by (rewrite LV6; do 2 right; left; reflexivity).
  assert (Inl2_6 : In (pl2, 104) (rt_live RT Σ6)) by (rewrite LV6; do 3 right; left; reflexivity).
  assert (Inb1_6 : In (pb1, 128) (rt_live RT Σ6)) by (rewrite LV6; do 4 right; left; reflexivity).
  assert (Inl1_6 : In (pl1, 104) (rt_live RT Σ6)) by (rewrite LV6; do 5 right; left; reflexivity).
  assert (Ink_6 : In (v2, 40) (rt_live RT Σ6)) by (rewrite LV6; do 6 right; left; reflexivity).
  assert (In1_6 : In (v1, 48) (rt_live RT Σ6)) by (rewrite LV6; do 7 right; left; reflexivity).
  destruct (Fresh Σ6 m16 pq2 56 ART16 Inq2_6 SZ6 ltac:(lia)) as (LOq2 & HIq2 & BLq2).
  assert (Dq2q1 : wp_apbox (pq2 + 56 <= pq1 \/ pq1 + 56 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 pq1 56 [] _ ART16 LV6 ltac:(left; reflexivity)).
  assert (Dq2b2 : wp_apbox (pq2 + 56 <= pb2 \/ pb2 + 128 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 pb2 128 [] _ ART16 LV6 ltac:(right; left; reflexivity)).
  assert (Dq2l2 : wp_apbox (pq2 + 56 <= pl2 \/ pl2 + 104 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 pl2 104 [] _ ART16 LV6 ltac:(do 2 right; left; reflexivity)).
  assert (Dq2b1 : wp_apbox (pq2 + 56 <= pb1 \/ pb1 + 128 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 pb1 128 [] _ ART16 LV6 ltac:(do 3 right; left; reflexivity)).
  assert (Dq2l1 : wp_apbox (pq2 + 56 <= pl1 \/ pl1 + 104 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 pl1 104 [] _ ART16 LV6 ltac:(do 4 right; left; reflexivity)).
  assert (Dq2k : wp_apbox (pq2 + 56 <= v2 \/ v2 + 40 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 v2 40 [] _ ART16 LV6 ltac:(do 5 right; left; reflexivity)).
  assert (Dq21 : wp_apbox (pq2 + 56 <= v1 \/ v1 + 48 <= pq2)) by exact (af_live_disj RT AF Σ6 m16 pq2 56 v1 48 [] _ ART16 LV6 ltac:(do 6 right; left; reflexivity)).
  assert (GRq2 : negb (bv_eqb (Z_to_bv 64 (Z.land pq2 7)) (Z_to_bv 64 0)) = false)
    by (rewrite wg_land7, (wg_mod16_8 pq2 Qq2) by lia; reflexivity).
  clear PR16 WM16 FR15 STK15 MI15 ART15 PC15 WC15 ENV15 LV5 FS5 SZ5 CR5 CG5 Inq1_5 Inb2_5 Inl2_5 Inb1_5 Inl1_5 Ink_5 In1_5 Q1C15 B2C15 L2C15 B1C15 L1C15 LK15 OBJ15.

  (* segment 11: compare thunk argument for the value list *)
  pose proof (Consts Σ6 m16 ART16) as (SH16 & UT16).
  pose proof (ossl_property_string_data_new_s11_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_11)
                o11_0 o11_1 o11_2 y11_1 y11_2 y11_3 y11_4 y11_5 y11_6 y11_7 o11_3 o11_4 o11_5 o11_6 v1 v2 pl1 pl2 pq1 pq2 j G11 gc11 m16 lo
                STK16 ROOM LOMIN SPMAX OBJ16 FR16 SH16 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia)
                  ltac:(clear - Pq2 Uq2; unfold USTACK_TOP in Uq2; lia) UT16 MI16) as W.
  cl_lift W HA22 c23 H23.
  destruct (ASTA_unpack RT Σ6 _ _ c23 H23) as (ms23 & (-> & ShOff_s11) & HA23). clear H23 HA22 SH16 UT16 ShOff_s11.

  (* call 12: OPENSSL_sk_set_cmp_thunks *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ6 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_12) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o11_0 o11_1 o11_2 sp (Z_to_bv 64
    v1) (Z_to_bv 64 pq2) (Z_to_bv 64 0x20bfec) y11_2 y11_3 y11_4 y11_5 y11_6 y11_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32))
    (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 o11_3
    o11_4 o11_5 o11_6 G11 gc11 m16 lo pq2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv
    64 0)
           FDO MST eq_refl TPv ART16 MI16 (CallAt Σ6 m16 SZ6 STK16) ltac:(rewrite EU; lia) Inq2_6 Qq2 Q2C16 GRq2 T c23 HA23).
  clear HA23.
  intros c24 H24.
  destruct (ASTA_unpack RT Σ6 _ _ c24 H24) as (ms24 & (m17 & (o12_0 & o12_1 & o12_2 & y12_1 & y12_2 & y12_3 & y12_4 & y12_5 & y12_6 & y12_7 & o12_3 & o12_4 & o12_5 &
    o12_6 & G12 & gc12 & ->)
                                               & (ART17 & MI17 & WM17 & STK17) & PR17 & Q2C17) & HA24). clear H24.
  rewrite EU in STK17, PR17.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_12) in HA24 by (unfold SITE_ossl_property_string_data_new_12; first [lia | reflexivity]).
  assert (FR17 : rw_cells asegs m17 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m16 m17 _ _ FR16 PR17 WM17); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq2; lia | exact I]. }
  assert (Q1C17 : rw_cells asegs m17 pq1
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 pq1 56 pq1 _ Q1C16 PR17 WM17 Inq1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2q1; unfold wp_apbox in Dq2q1; lia
      | exact I]. }
  assert (B2C17 : rw_cells asegs m17 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 pb2 128 pb2 _ B2C16 PR17 WM17 Inb2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b2; unfold wp_apbox in Dq2b2; lia
      | exact I]. }
  assert (L2C17 : rw_cells asegs m17 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 pl2 104 pl2 _ L2C16 PR17 WM17 Inl2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l2; unfold wp_apbox in Dq2l2; lia
      | exact I]. }
  assert (B1C17 : rw_cells asegs m17 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 pb1 128 pb1 _ B1C16 PR17 WM17 Inb1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b1; unfold wp_apbox in Dq2b1; lia
      | exact I]. }
  assert (L1C17 : rw_cells asegs m17 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 pl1 104 pl1 _ L1C16 PR17 WM17 Inl1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l1; unfold wp_apbox in Dq2l1; lia
      | exact I]. }
  assert (LK17 : rw_cells asegs m17 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m16 m17 v2 40 v2 _ LK16 PR17 WM17 Ink_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2k; unfold wp_apbox in Dq2k; lia |
      exact I]. }
  assert (OBJ17 : rw_cells asegs m17 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 pq1); CB 8 (repeat (Z_to_bv 8 0) 8)]).
  { apply (wg_keep_live _ _ _ _ m16 m17 v1 48 v1 _ OBJ16 PR17 WM17 In1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq21; unfold wp_apbox in Dq21; lia |
      exact I]. }
  assert (PC17 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m17).
  { apply (pres_fp_trans _ _ _ _ m m16 m17 PC16).
    apply (PresUp Σ6 m16 m16 m17 [(pq2, 56); (pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART16 LV6 FS6 SZ6
      ltac:(lia) PR17).
    intros x Hx. right. exists pq2, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m16 m17 WC16 WM17) as WC17.
  assert (ENV17 : cl_env m17 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m16 m17 _ ENV16 PR17); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq2; lia | exact I]).
  clear PR17 WM17 FR16 STK16 MI16 ART16 PC16 WC16 ENV16 Q2C16 Q1C16 B2C16 L2C16 B1C16 L1C16 LK16 OBJ16.

  (* segment 12: copy thunk argument for the value list *)
  pose proof (Consts Σ6 m17 ART17) as (SH17 & UT17).
  pose proof (ossl_property_string_data_new_s12_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_12)
                o12_0 o12_1 o12_2 y12_1 y12_2 y12_3 y12_4 y12_5 y12_6 y12_7 o12_3 o12_4 o12_5 o12_6 v1 v2 pl1 pl2 pq1 pq2 j G12 gc12 m17 lo
                STK17 ROOM LOMIN SPMAX OBJ17 FR17 SH17 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia)
                  ltac:(clear - Pq2 Uq2; unfold USTACK_TOP in Uq2; lia) UT17 MI17) as W.
  cl_lift W HA24 c25 H25.
  destruct (ASTA_unpack RT Σ6 _ _ c25 H25) as (ms25 & (-> & ShOff_s12) & HA25). clear H25 HA24 SH17 UT17 ShOff_s12.

  (* call 13: OPENSSL_sk_set_copy_thunks *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ6 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_13) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o12_0 o12_1 o12_2 sp (Z_to_bv 64
    v1) (Z_to_bv 64 pq2) (Z_to_bv 64 0x20c018) y12_2 y12_3 y12_4 y12_5 y12_6 y12_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32))
    (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 o12_3
    o12_4 o12_5 o12_6 G12 gc12 m17 lo pq2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0x20bfec) (Z_to_bv 64 0)
    (Z_to_bv 64 0)
           FDO MST eq_refl TPv ART17 MI17 (CallAt Σ6 m17 SZ6 STK17) ltac:(rewrite EU; lia) Inq2_6 Qq2 Q2C17 GRq2 T c25 HA25).
  clear HA25.
  intros c26 H26.
  destruct (ASTA_unpack RT Σ6 _ _ c26 H26) as (ms26 & (m18 & (o13_0 & o13_1 & o13_2 & y13_1 & y13_2 & y13_3 & y13_4 & y13_5 & y13_6 & y13_7 & o13_3 & o13_4 & o13_5 &
    o13_6 & G13 & gc13 & ->)
                                               & (ART18 & MI18 & WM18 & STK18) & PR18 & Q2C18) & HA26). clear H26.
  rewrite EU in STK18, PR18.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_13) in HA26 by (unfold SITE_ossl_property_string_data_new_13; first [lia | reflexivity]).
  assert (FR18 : rw_cells asegs m18 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m17 m18 _ _ FR17 PR18 WM18); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq2; lia | exact I]. }
  assert (Q1C18 : rw_cells asegs m18 pq1
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 pq1 56 pq1 _ Q1C17 PR18 WM18 Inq1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2q1; unfold wp_apbox in Dq2q1; lia
      | exact I]. }
  assert (B2C18 : rw_cells asegs m18 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 pb2 128 pb2 _ B2C17 PR18 WM18 Inb2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b2; unfold wp_apbox in Dq2b2; lia
      | exact I]. }
  assert (L2C18 : rw_cells asegs m18 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 pl2 104 pl2 _ L2C17 PR18 WM18 Inl2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l2; unfold wp_apbox in Dq2l2; lia
      | exact I]. }
  assert (B1C18 : rw_cells asegs m18 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 pb1 128 pb1 _ B1C17 PR18 WM18 Inb1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b1; unfold wp_apbox in Dq2b1; lia
      | exact I]. }
  assert (L1C18 : rw_cells asegs m18 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 pl1 104 pl1 _ L1C17 PR18 WM18 Inl1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l1; unfold wp_apbox in Dq2l1; lia
      | exact I]. }
  assert (LK18 : rw_cells asegs m18 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m17 m18 v2 40 v2 _ LK17 PR18 WM18 Ink_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2k; unfold wp_apbox in Dq2k; lia |
      exact I]. }
  assert (OBJ18 : rw_cells asegs m18 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 pq1); CB 8 (repeat (Z_to_bv 8 0) 8)]).
  { apply (wg_keep_live _ _ _ _ m17 m18 v1 48 v1 _ OBJ17 PR18 WM18 In1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq21; unfold wp_apbox in Dq21; lia |
      exact I]. }
  assert (PC18 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m18).
  { apply (pres_fp_trans _ _ _ _ m m17 m18 PC17).
    apply (PresUp Σ6 m17 m17 m18 [(pq2, 56); (pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART17 LV6 FS6 SZ6
      ltac:(lia) PR18).
    intros x Hx. right. exists pq2, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m17 m18 WC17 WM18) as WC18.
  assert (ENV18 : cl_env m18 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m17 m18 _ ENV17 PR18); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq2; lia | exact I]).
  clear PR18 WM18 FR17 STK17 MI17 ART17 PC17 WC17 ENV17 Q2C17 Q1C17 B2C17 L2C17 B1C17 L1C17 LK17 OBJ17.

  (* segment 13: free thunk argument for the value list *)
  pose proof (Consts Σ6 m18 ART18) as (SH18 & UT18).
  pose proof (ossl_property_string_data_new_s13_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_13)
                o13_0 o13_1 o13_2 y13_1 y13_2 y13_3 y13_4 y13_5 y13_6 y13_7 o13_3 o13_4 o13_5 o13_6 v1 v2 pl1 pl2 pq1 pq2 j G13 gc13 m18 lo
                STK18 ROOM LOMIN SPMAX OBJ18 FR18 SH18 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia)
                  ltac:(clear - Pq2 Uq2; unfold USTACK_TOP in Uq2; lia) UT18 MI18) as W.
  cl_lift W HA26 c27 H27.
  destruct (ASTA_unpack RT Σ6 _ _ c27 H27) as (ms27 & (-> & ShOff_s13) & HA27). clear H27 HA26 SH18 UT18 ShOff_s13.

  (* call 14: OPENSSL_sk_set_thunks *)
  apply (C_OPENSSL_sk_set_thunks Σ6 PMc (Z_to_bv 64 SITE_ossl_property_string_data_new_14) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp o13_0 o13_1 o13_2 sp (Z_to_bv 64 v1)
    (Z_to_bv 64 pq2) (Z_to_bv 64 0x20c040) y13_2 y13_3 y13_4 y13_5 y13_6 y13_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 (v1 + 32))
    (Z_to_bv 64 2147450880) (Z_to_bv 64 ((v1 + 8) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((v1 + 32) ≫ 3 + 2147450880)) s10 s11 o13_3
    o13_4 o13_5 o13_6 G13 gc13 m18 lo pq2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0x20bfec) (Z_to_bv 64 0)
    (Z_to_bv 64 0x20c018)
           FDO MST eq_refl TPv ART18 MI18 (CallAt Σ6 m18 SZ6 STK18) ltac:(rewrite EU; lia) Inq2_6 Qq2 Q2C18 GRq2 T c27 HA27).
  clear HA27.
  intros c28 H28.
  destruct (ASTA_unpack RT Σ6 _ _ c28 H28) as (ms28 & (m19 & (o14_0 & o14_1 & o14_2 & y14_1 & y14_2 & y14_3 & y14_4 & y14_5 & y14_6 & y14_7 & o14_3 & o14_4 & o14_5 &
    o14_6 & G14 & gc14 & ->)
                                               & (ART19 & MI19 & WM19 & STK19) & PR19 & Q2C19) & HA28). clear H28.
  rewrite EU in STK19, PR19.
  rewrite (ret_pc_even SITE_ossl_property_string_data_new_14) in HA28 by (unfold SITE_ossl_property_string_data_new_14; first [lia | reflexivity]).
  assert (FR19 : rw_cells asegs m19 (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (KeepStk _ _ _ _ m18 m19 _ _ FR18 PR19 WM19); [lia | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx ROOM BLq2; lia | exact I]. }
  assert (Q1C19 : rw_cells asegs m19 pq1
                    [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 pq1 56 pq1 _ Q1C18 PR19 WM19 Inq1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2q1; unfold wp_apbox in Dq2q1; lia
      | exact I]. }
  assert (B2C19 : rw_cells asegs m19 pb2
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 pb2 128 pb2 _ B2C18 PR19 WM19 Inb2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b2; unfold wp_apbox in Dq2b2; lia
      | exact I]. }
  assert (L2C19 : rw_cells asegs m19 pl2
                    [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 pl2 104 pl2 _ L2C18 PR19 WM19 Inl2_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l2; unfold wp_apbox in Dq2l2; lia
      | exact I]. }
  assert (B1C19 : rw_cells asegs m19 pb1
                    [CB 128 (repeat (Z_to_bv 8 0) 128)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 pb1 128 pb1 _ B1C18 PR19 WM19 Inb1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2b1; unfold wp_apbox in Dq2b1; lia
      | exact I]. }
  assert (L1C19 : rw_cells asegs m19 pl1
                    [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 pl1 104 pl1 _ L1C18 PR19 WM19 Inl1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2l1; unfold wp_apbox in Dq2l1; lia
      | exact I]. }
  assert (LK19 : rw_cells asegs m19 v2
                    (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
  { apply (wg_keep_live _ _ _ _ m18 m19 v2 40 v2 _ LK18 PR19 WM19 Ink_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq2k; unfold wp_apbox in Dq2k; lia |
      exact I]. }
  assert (OBJ19 : rw_cells asegs m19 v1
                    [C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 pl1); C8 (Z_to_bv 64 pl2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 pq1); CB 8 (repeat (Z_to_bv 8 0) 8)]).
  { apply (wg_keep_live _ _ _ _ m18 m19 v1 48 v1 _ OBJ18 PR19 WM19 In1_6); [lia | cbn; lia |].
    intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *. split; [clear - Hx Dq21; unfold wp_apbox in Dq21; lia |
      exact I]. }
  assert (PC19 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m19).
  { apply (pres_fp_trans _ _ _ _ m m18 m19 PC18).
    apply (PresUp Σ6 m18 m18 m19 [(pq2, 56); (pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp + -96) _ ART18 LV6 FS6 SZ6
      ltac:(lia) PR19).
    intros x Hx. right. exists pq2, 56. split; [left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
  pose proof (wmono_trans asegs m m18 m19 WC18 WM19) as WC19.
  assert (ENV19 : cl_env m19 (Z_to_bv 8 1) canary)
    by (apply (EnvKeep _ _ _ _ m18 m19 _ ENV18 PR19); intros x Hx; cbn [outside]; unfold SEGTOP_A in Hx; split; [clear - Hx LOq2; lia | exact I]).
  clear PR19 WM19 FR18 STK18 MI18 ART18 PC18 WC18 ENV18 Q2C18 Q1C18 B2C18 L2C18 B1C18 L1C18 LK18 OBJ18.

  (* segment 14: store of the value list, the NULL checks and the return *)
  pose proof (Consts Σ6 m19 ART19) as (SH19 & UT19).
  pose proof (proj2 (af_acc_live RT AF Σ6 m19 v1 48 ART19 In1_6)) as ACC19.
  assert (NZ : forall p, 0 < p < 2 ^ 64 -> bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0) = false).
  { intros p Hp. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
  pose proof (ossl_property_string_data_new_s14_walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_property_string_data_new_14)
                o14_0 o14_1 o14_2 y14_1 y14_2 y14_3 y14_4 y14_5 y14_6 y14_7 o14_3 o14_4 o14_5 o14_6 v1 v2 pl1 pl2 pq1 pq2 j G14 gc14 m19 lo
                STK19 ROOM LOMIN SPMAX OBJ19 FR19 SH19 ltac:(clear - P1 U1; unfold USTACK_TOP in U1; lia) ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia) ltac:(clear -
                  Pl1 Ul1; unfold USTACK_TOP in Ul1; lia) ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia) ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia)
                  ltac:(clear - Pq2 Uq2; unfold USTACK_TOP in Uq2; lia) UT19
                ACC19 AL1 LO1 HI1 BL1 (NZ v2 ltac:(clear - P2 U2; unfold USTACK_TOP in U2; lia)) (NZ pq1 ltac:(clear - Pq1 Uq1; unfold USTACK_TOP in Uq1; lia)) (NZ pq2
                  ltac:(clear - Pq2 Uq2; unfold USTACK_TOP in Uq2; lia)) (NZ pl1 ltac:(clear - Pl1 Ul1; unfold USTACK_TOP in Ul1; lia))
                ltac:(rewrite (NZ pl2 ltac:(clear - Pl2 Ul2; unfold USTACK_TOP in Ul2; lia)); reflexivity) MI19) as W.
  cl_lift W HA28 c29 H29.
  apply Hk. exists Σ6, v1, v2, pl1, pb1, pl2, pb2, pq1, pq2.
  split.
  - unfold ASTA in H29 |- *. apply (AST_conseq _ _ _ _ _ _ c29 H29); [| intros mo Hmo; exact Hmo].
    intros ms (m20 & MSEQ & MU20 & WM20 & MI20 & OBJ20 & STK20 & ShOff_s14). clear ShOff_s14.
    assert (RET : ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 v1) m20 ms).
    { rewrite MSEQ. unfold ret_st. do 16 eexists. reflexivity. }
    assert (ART20 : ART RT Σ6 m20) by (apply (ArtStore Σ6 m19 m20 v1 48 _ ART19 In1_6 MU20 WM20); intros x Hx; clear - Hx; cbn [outside] in Hx; lia).
    assert (PC20 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m20).
    { apply (pres_fp_trans _ _ _ _ m m19 m20 PC19).
      apply (PresUp Σ6 m19 m19 m20 [(pq2, 56); (pq1, 56); (pb2, 128); (pl2, 104); (pb1, 128); (pl1, 104); (v2, 40); (v1, 48)] (bv_unsigned sp) _ ART19 LV6 FS6 SZ6
        ltac:(lia) (fun a _ Ho => MU20 a Ho)).
      intros x Hx. right. exists v1, 48. split; [do 7 right; left; reflexivity | clear - Hx; cbn [outside] in Hx; lia]. }
    assert (ENV20 : cl_env m20 (Z_to_bv 8 1) canary).
    { apply (cl_env_seg _ m19 m20 _ canary ENV19 MU20). apply cl_fp_cons; [right; left; clear - LO1; unfold ssp_guard; lia | apply cl_fp_nil]. }
    assert (Q2C20 : rw_cells asegs m20 pq2
                      [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
    { apply (wg_keep_seg _ m19 m20 pq2 _ Q2C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Dq21; unfold wp_apbox in Dq21; lia | exact I]. }
    assert (Q1C20 : rw_cells asegs m20 pq1
                      [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                    C8 (Z_to_bv 64 0x20bfec); C8 (Z_to_bv 64 0x20c040); C8 (Z_to_bv 64 0x20c018)]).
    { apply (wg_keep_seg _ m19 m20 pq1 _ Q1C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Dq11; unfold wp_apbox in Dq11; lia | exact I]. }
    assert (B2C20 : rw_cells asegs m20 pb2
                      [CB 128 (repeat (Z_to_bv 8 0) 128)]).
    { apply (wg_keep_seg _ m19 m20 pb2 _ B2C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Db21; unfold wp_apbox in Db21; lia | exact I]. }
    assert (L2C20 : rw_cells asegs m20 pl2
                      [C8 (Z_to_bv 64 pb2); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
    { apply (wg_keep_seg _ m19 m20 pl2 _ L2C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Dl21; unfold wp_apbox in Dl21; lia | exact I]. }
    assert (B1C20 : rw_cells asegs m20 pb1
                      [CB 128 (repeat (Z_to_bv 8 0) 128)]).
    { apply (wg_keep_seg _ m19 m20 pb1 _ B1C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Db11; unfold wp_apbox in Db11; lia | exact I]. }
    assert (L1C20 : rw_cells asegs m20 pl1
                      [C8 (Z_to_bv 64 pb1); C8 (Z_to_bv 64 0x20bf8c); C8 (Z_to_bv 64 0x20bf48); C8 (Z_to_bv 64 0x20c77c); C8 (Z_to_bv 64 0x20c79c);
                    C8 (Z_to_bv 64 0x20c7bc); C8 (Z_to_bv 64 0x20c7dc); C4 (Z_to_bv 64 8); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8);
                    C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)]).
    { apply (wg_keep_seg _ m19 m20 pl1 _ L1C19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Dl11; unfold wp_apbox in Dl11; lia | exact I]. }
    assert (LK20 : rw_cells asegs m20 v2
                      (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { apply (wg_keep_seg _ m19 m20 v2 _ LK19 MU20 WM20). intros x Hx. cbn [outside cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ mutex_cells] in Hx |- *.
      split; [clear - Hx Dk1; unfold wp_apbox in Dk1; lia | exact I]. }
    destruct (af_acc_live RT AF Σ6 m20 v1 48 ART20 In1_6) as (Wr1 & Ac1).
    destruct (af_acc_live RT AF Σ6 m20 v2 40 ART20 Ink_6) as (Wrk & Ack).
    destruct (af_acc_live RT AF Σ6 m20 pl1 104 ART20 Inl1_6) as (Wrl1 & Acl1).
    destruct (af_acc_live RT AF Σ6 m20 pb1 128 ART20 Inb1_6) as (Wrb1 & Acb1).
    destruct (af_acc_live RT AF Σ6 m20 pl2 104 ART20 Inl2_6) as (Wrl2 & Acl2).
    destruct (af_acc_live RT AF Σ6 m20 pb2 128 ART20 Inb2_6) as (Wrb2 & Acb2).
    destruct (af_acc_live RT AF Σ6 m20 pq1 56 ART20 Inq1_6) as (Wrq1 & Acq1).
    destruct (af_acc_live RT AF Σ6 m20 pq2 56 ART20 Inq2_6) as (Wrq2 & Acq2).
    exists m20.
    refine (conj RET (conj (conj ART20 (conj MI20 (conj (wmono_trans asegs m m19 m20 WC19 WM20) STK20))) (conj PC20 (conj ENV20 _)))).
    exact (conj Wr1 (conj Ac1 (conj Wrk (conj Ack (conj Wrl1 (conj Acl1 (conj Wrb1 (conj Acb1 (conj Wrl2 (conj Acl2 (conj Wrb2 (conj Acb2 (conj Wrq1 (conj Acq1 (conj Wrq2
      (conj Acq2 (conj OBJ20 (conj LK20 (conj L1C20 (conj B1C20 (conj L2C20 (conj B2C20 (conj Q1C20 Q2C20))))))))))))))))))))))).
  - split; [exact LV6|]. split; [exact FS6|]. split; [exact SZ6|]. split; [rewrite CR6; lia|].
    unfold USTACK_TOP in *.
    exact (conj P1 (conj Q1 (conj U1 (conj P2 (conj Q2 (conj U2 (conj Pl1 (conj Ql1 (conj Ul1 (conj Pb1 (conj Qb1 (conj Ub1
             (conj Pl2 (conj Ql2 (conj Ul2 (conj Pb2 (conj Qb2 (conj Ub2 (conj Pq1 (conj Qq1 (conj Uq1 (conj Pq2 (conj Qq2 (conj Uq2 CG6)))))))))))))))))))))))).
Qed.
End ossl_property_string_data_new_cps.
