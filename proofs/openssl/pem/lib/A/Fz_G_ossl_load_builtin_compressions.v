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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_G_COMP_zlib Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_G_COMP_get_type.
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

Definition e_ossl_load_builtin_compressions : Z := 0x510ba0.
Definition SITE_ossl_load_builtin_compressions_1 : Z := 0x510bd0.     (* [comment removed for export] *)
Definition SITE_ossl_load_builtin_compressions_2 : Z := 0x510be4.     (* [comment removed for export] *)
Definition SITE_ossl_load_builtin_compressions_3 : Z := 0x510bf4.     (* [comment removed for export] *)
Definition SITE_ossl_load_builtin_compressions_4 : Z := 0x510c04.     (* [comment removed for export] *)
Definition SITE_ossl_load_builtin_compressions_5 : Z := 0x510c14.     (* [comment removed for export] *)
Definition SITE_ossl_load_builtin_compressions_6 : Z := 0x510c20.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311440) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 6736696) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 5312172) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x510ba0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep.
  do 6 zstore.
  do 5 zstep.
  unfold ossl_load_builtin_compressions_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311460) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 5311764) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2073912) fc1 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s1_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x510bd0) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.
  unfold ossl_load_builtin_compressions_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311476) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp s1 (Z_to_bv 64 v2) (Z_to_bv 64 5311956) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2075068) fc2 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s2_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp s1 (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x510be4) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 Hv2 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_load_builtin_compressions_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311492) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp s1 (Z_to_bv 64 v3) (Z_to_bv 64 5312000) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2075148) fc3 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s3_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v3 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp s1 (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x510bf4) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 Hv3 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_load_builtin_compressions_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311508) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp s1 (Z_to_bv 64 v4) (Z_to_bv 64 5312040) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 2074988) fc4 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s4_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v4 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp s1 (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x510c04) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 Hv4 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_load_builtin_compressions_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 5311520) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v5) (Z_to_bv 64 v1) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 5312240) fc5 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_load_builtin_compressions_s5_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v5 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp s1 (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x510c14) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 Hv5 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 3 zstep.
  unfold ossl_load_builtin_compressions_s5_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_load_builtin_compressions_s6_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_6 u1_6 u2_6 s0 s1 (Z_to_bv 64 v5) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (ret_pc ra) fc6 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_load_builtin_compressions_s6_walk : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= (bv_unsigned sp + -48) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0)) = true ->
  mem_inv asegs m ->
  evt asegs (ossl_load_builtin_compressions_s6_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v5 v6 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v5) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v1) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x510c20) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 Hv5 Hv6 UT BR6_1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep. wg_raw BR6_1.
  do 9 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_load_builtin_compressions_s6_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_load_builtin_compressions_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_COMP_zlib : COMP_zlib_stmt RT.
Hypothesis C_OPENSSL_sk_new : OPENSSL_sk_new_stmt RT.
Hypothesis C_OPENSSL_sk_set_cmp_thunks : OPENSSL_sk_set_cmp_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_copy_thunks : OPENSSL_sk_set_copy_thunks_stmt RT.
Hypothesis C_OPENSSL_sk_set_thunks : OPENSSL_sk_set_thunks_stmt RT.
Hypothesis C_COMP_get_type : COMP_get_type_stmt RT.

Definition ossl_load_builtin_compressions_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x150 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_load_builtin_compressions (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_load_builtin_compressions_1, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_2, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_3, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_4, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_5, e_ossl_load_builtin_compressions); (SITE_ossl_load_builtin_compressions_6, e_ossl_load_builtin_compressions); (SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)]
                      [(SITE_ossl_load_builtin_compressions_1, e_COMP_zlib); (SITE_ossl_load_builtin_compressions_2, e_OPENSSL_sk_new); (SITE_ossl_load_builtin_compressions_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_load_builtin_compressions_4, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_load_builtin_compressions_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_load_builtin_compressions_6, e_COMP_get_type); (SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost 56 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_load_builtin_compressions m)))
    (fun c => exists (Σ' : rts RT) (q1 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 56
           /\ acc asegs m' q1 56
           /\ rw_cells asegs m' q1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 5312040); C8 (Z_to_bv 64 5312000)]) c
       /\ rt_live RT Σ' = (q1, 56) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost 56 /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 56 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_load_builtin_compressions_cps : ossl_load_builtin_compressions_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 48 /\ 0x10007fff8000 < usp - 48 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-48) EU1.
  assert (WHLO : lo <= usp - 48) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (wg_mcost_nonneg 56) as MC_56.
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST WHLO WHIMG WHTOP UT SHC MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1', H1_0.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  (* [comment removed for export] *)
  apply (C_COMP_zlib Σ PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_1) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 6736696) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo FDO MST eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & Hc2'). clear Hc2.
  destruct RS2 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & F1 & fc1 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_1) in Hc2' by (unfold SITE_ossl_load_builtin_compressions_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; exact (AGc2 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AGu2) as UWF2.
  cl_keep H1_0 AGc2 WM2 KF1.
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (ENV2 : cl_env m2 lb canary).
  { assert (HFP : cl_fp []) by cl_fp_lia. apply (cl_env_agree m1 m2 _ _ ENV1). intros a Ha. apply PRES2; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 0 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 SHC2 ltac:(unfold USTACK_TOP in *; lia) UT2 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_0.
  assert (ART3 : ART RT Σ m3).
  { apply (wg_seg_ART RT AF Σ m2 m3 usp 48 [] ART2 ltac:(lia) ltac:(lia) MU3); [|exact WM3].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_load_builtin_compressions e_OPENSSL_sk_new SITE_ossl_load_builtin_compressions_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
              (proj1 CGH (SITE_ossl_load_builtin_compressions_2, e_ossl_load_builtin_compressions) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_load_builtin_compressions_2, e_OPENSSL_sk_new) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H3_0))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_new Σ PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_2) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 5311764) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 (Z_to_bv 64 0) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_load_builtin_compressions_2) by (unfold SITE_ossl_load_builtin_compressions_2; lia). exact CTXc3. }
  { exact UWCc3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_WR_v1 & G2_ACC_v1 & G2_CL0) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_2) in Hc4' by (unfold SITE_ossl_load_builtin_compressions_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  cl_keep H3_0 AGc4 WM4 KF3.
  pose proof SP4 as SPc4. pose proof CG4 as CGc4.
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (rewrite LV4; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 1) by lia. wp_box1 CR4.
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_load_builtin_compressions (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v2_4 : In (v2, 56) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 56 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 56 ART4 INP_v2_4 ltac:(lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 56 ART4 INP_v2_4 ltac:(lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v2 : v2 + 56 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 0 v2 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF3 SHC4 ltac:(unfold USTACK_TOP in *; lia) PR64_v2 UT4 MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5', H5_0.
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 48 [] ART4 ltac:(rewrite SPc4; lia) ltac:(lia) MU5); [|exact WM5].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF5 : rw_cells asegs m5 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m4 m5 _ _ G2_CL0 MU5 WM5); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AGs5 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AGs5) as UWF5.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_3) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_2 u1_2 u2_2 sp s1 (Z_to_bv 64 v2) (Z_to_bv 64 5311956) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 0) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2
           F2 fc2 m5 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5311764) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF5. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & G3_CL0) & Hc6'). clear Hc6.
  destruct RS6 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & F3 & fc3 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_3) in Hc6' by (unfold SITE_ossl_load_builtin_compressions_3; clear; first [reflexivity | lia]).
  assert (AGc6 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu6 : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6) by (intros a Ha; exact (AGc6 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AGu6) as UWF6.
  cl_keep H5_0 AGc6 WM6 KF6.
  destruct (af_client_consts RT AF Σ2 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  assert (ENV6 : cl_env m6 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m5 m6 _ _ ENV5). intros a Ha. apply PRES6; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_3) u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 0 v2 F3 fc3 m6 lo
                ST6 WHLO WHIMG WHTOP KF6 SHC6 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT6 MI6) as W7.
  cl_lift W7 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & H7_0 & H7_1 & ST7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7', H7_0.
  assert (ART7 : ART RT Σ2 m7).
  { apply (wg_seg_ART RT AF Σ2 m6 m7 usp 48 [] ART6 ltac:(rewrite SPc4; lia) ltac:(lia) MU7); [|exact WM7].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF9 : rw_cells asegs m7 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL0 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m6 m7 _ canary ENV6 MU7 ltac:(cl_fp_lia)) as ENV7.
  assert (AGs7 : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7) by (intros a Ha; apply MU7; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AGs7) as UWF7.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_4) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_3 u1_3 u2_3 sp s1 (Z_to_bv 64 v2) (Z_to_bv 64 5312000) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 0) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
           F3 fc3 m7 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5311764) (Z_to_bv 64 5311956) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART7 MI7).
  { fold usp in SPA. cl_call_ok EU1 ST7 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF9. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & G4_CL0) & Hc8'). clear Hc8.
  destruct RS8 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & F4 & fc4 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_4) in Hc8' by (unfold SITE_ossl_load_builtin_compressions_4; clear; first [reflexivity | lia]).
  assert (AGc8 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES8; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; exact (AGc8 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AGu8) as UWF8.
  cl_keep H7_0 AGc8 WM8 KF10.
  destruct (af_client_consts RT AF Σ2 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  assert (ENV8 : cl_env m8 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m7 m8 _ _ ENV7). intros a Ha. apply PRES8; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s4_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_4) u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 0 v2 F4 fc4 m8 lo
                ST8 WHLO WHIMG WHTOP KF10 SHC8 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT8 MI8) as W9.
  cl_lift W9 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & H9_0 & H9_1 & ST9) & Hc9'). clear Hc9.
  fold usp in MU9, ST9, Hc9', H9_0.
  assert (ART9 : ART RT Σ2 m9).
  { apply (wg_seg_ART RT AF Σ2 m8 m9 usp 48 [] ART8 ltac:(rewrite SPc4; lia) ltac:(lia) MU9); [|exact WM9].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF13 : rw_cells asegs m9 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 5312000)]) by (apply (wg_keep_seg _ m8 m9 _ _ G4_CL0 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(cl_fp_lia)) as ENV9.
  assert (AGs9 : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9) by (intros a Ha; apply MU9; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AGs9) as UWF9.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_5) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_4 u1_4 u2_4 sp s1 (Z_to_bv 64 v2) (Z_to_bv 64 5312040) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 0) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4
           F4 fc4 m9 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 5311764) (Z_to_bv 64 5311956) (Z_to_bv 64 0) (Z_to_bv 64 5312000) FDO MST eq_refl eq_refl ART9 MI9).
  { fold usp in SPA. cl_call_ok EU1 ST9 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF13. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc9'. }
  clear Hc9'. intros c10 Hc10.
  destruct (ASTA_unpack RT Σ2 _ _ c10 Hc10) as (ms10 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & G5_CL0) & Hc10'). clear Hc10.
  destruct RS10 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & F5 & fc5 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_5) in Hc10' by (unfold SITE_ossl_load_builtin_compressions_5; clear; first [reflexivity | lia]).
  assert (AGc10 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES10; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu10 : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10) by (intros a Ha; exact (AGc10 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AGu10) as UWF10.
  cl_keep H9_0 AGc10 WM10 KF14.
  destruct (af_client_consts RT AF Σ2 m10 ART10) as (_ & SHC10 & _ & _ & UT10).
  assert (ENV10 : cl_env m10 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m9 m10 _ _ ENV9). intros a Ha. apply PRES10; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s5_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_5) u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 0 v2 F5 fc5 m10 lo
                ST10 WHLO WHIMG WHTOP KF14 SHC10 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT10 MI10) as W11.
  cl_lift W11 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ2 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & H11_0 & H11_1 & ST11) & Hc11'). clear Hc11.
  fold usp in MU11, ST11, Hc11', H11_0.
  assert (ART11 : ART RT Σ2 m11).
  { apply (wg_seg_ART RT AF Σ2 m10 m11 usp 48 [] ART10 ltac:(rewrite SPc4; lia) ltac:(lia) MU11); [|exact WM11].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF17 : rw_cells asegs m11 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 5312040); C8 (Z_to_bv 64 5312000)]) by (apply (wg_keep_seg _ m10 m11 _ _ G5_CL0 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m10 m11 _ canary ENV10 MU11 ltac:(cl_fp_lia)) as ENV11.
  assert (AGs11 : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11) by (intros a Ha; apply MU11; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AGs11) as UWF11.
  (* [comment removed for export] *)
  apply (C_COMP_get_type Σ2 PMc (Z_to_bv 64 SITE_ossl_load_builtin_compressions_6) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_5 u1_5 u2_5 sp (Z_to_bv 64 v2) (Z_to_bv 64 0) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 0) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5
           F5 fc5 m11 lo FDO MST eq_refl ART11 MI11).
  { fold usp in SPA. cl_call_ok EU1 ST11 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc11'. }
  clear Hc11'. intros c12 Hc12.
  destruct (ASTA_unpack RT Σ2 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12) & Hc12'). clear Hc12.
  destruct RS12 as (u0_6 & u1_6 & u2_6 & b1_6 & b2_6 & b3_6 & b4_6 & b5_6 & b6_6 & b7_6 & u3_6 & u4_6 & u5_6 & u6_6 & F6 & fc6 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_ossl_load_builtin_compressions_6) in Hc12' by (unfold SITE_ossl_load_builtin_compressions_6; clear; first [reflexivity | lia]).
  assert (AGc12 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m11 m12).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES12; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu12 : agree_on (fun x => usp <= x < USTACK_TOP) m11 m12) by (intros a Ha; exact (AGc12 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m11 m12 sp s0 UWF11 AGu12) as UWF12.
  cl_keep H11_0 AGc12 WM12 KF18.
  assert (KF20 : rw_cells asegs m12 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 5311764); C8 (Z_to_bv 64 5311956); C8 (Z_to_bv 64 5312040); C8 (Z_to_bv 64 5312000)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v2 56 _ _ KF17 PRES12 WM12 INP_v2_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  destruct (af_client_consts RT AF Σ2 m12 ART12) as (_ & SHC12 & _ & _ & UT12).
  assert (ENV12 : cl_env m12 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp []) by cl_fp_lia. apply (cl_env_agree m11 m12 _ _ ENV11). intros a Ha. apply PRES12; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_load_builtin_compressions_s6_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_load_builtin_compressions_6) u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 0 v2 0 F6 fc6 m12 lo
                ST12 WHLO WHIMG WHTOP KF18 SHC12 ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(unfold USTACK_TOP in *; lia) UT12 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI12) as W13.
  cl_lift W13 Hc12' c13 Hc13.
  apply Hk. exists Σ2, v2.
  split; [| split; [rewrite LV4; reflexivity|]; split; [rewrite FRS4; reflexivity|]; split; [rewrite SP4; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; rewrite CG4; reflexivity].
  apply (ASTA_conseq RT Σ2 PMc _ _ c13 Hc13). intros ms13 (m13 & -> & MU13 & WM13 & MI13 & H13_0 & ST13). fold usp in MU13, ST13.
  exists m13.
  split; [exists u0_6, u1_6, u2_6, b1_6, b2_6, b3_6, b4_6, b5_6, b6_6, b7_6, u3_6, u4_6, u5_6, u6_6, F6, fc6; reflexivity|].
  assert (ART13 : ART RT Σ2 m13).
  { apply (wg_seg_ART RT AF Σ2 m12 m13 usp 48 [] ART12 ltac:(rewrite SPc4; lia) ltac:(lia) MU13); [|exact WM13].
    intros x Hx. exfalso; apply Hx; exact I. }
  split; [split; [exact ART13|]; split; [exact MI13|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 WM13)))))))))))) | exact ST13]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV4; do 1 right; exact He | rewrite FRS4; intros e He; exact He | lia]).
    assert (NA_v2 : ~ (v2 <= bv_unsigned a < v2 + 56)) by exact (wg_newchunk_apart RT AF Σ Σ2 m4 [(v2, 56)] v2 56 usp _ ART4 LV4 ltac:(left; reflexivity) FRS4 SP4 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha).
    wp_box1 NA_v2.
    wp_box1 Ha1.
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
    rewrite (MU13 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES12 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU11 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES10 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU9 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES8 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU7 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES6 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU5 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES4 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU3 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES2 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    reflexivity. }
  pose proof (af_acc_live RT AF Σ2 m13 v2 56 ART13 INP_v2_4) as (WRE_v2 & ACCE_v2).
  split; [exact (cl_env_seg _ m12 m13 _ canary ENV12 MU13 ltac:(cl_fp_lia))|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  apply (wg_keep_seg _ m12 m13 _ _ KF20 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I.
Qed.
End ossl_load_builtin_compressions_cps.
