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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_OPENSSL_sk_new Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Th_mutex Fz_M_locknew Fz_G_OPENSSL_sk_new_null.
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
Definition ossl_provider_store_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160168) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 80) (Z_to_bv 64 311200) (Z_to_bv 64 312) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2080748) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma ossl_provider_store_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_provider_store_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20f5e4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep.
  do 6 zstore.
  do 10 zstep.
  unfold ossl_provider_store_new_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s1_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160188) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 2160572) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2073912) fc1 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 UT HBr1 ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep.
  zstep. wg_F.
  do 3 zstep.
  unfold ossl_provider_store_new_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s2_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160208) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180372) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2075068) fc2 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 5 zstep.
  unfold ossl_provider_store_new_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s3_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160224) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180416) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2075148) fc3 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv3 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.
  unfold ossl_provider_store_new_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s4_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160240) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180292) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 2074988) fc4 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv4 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.
  unfold ossl_provider_store_new_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s5_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160272) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 2055740) fc5 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv5 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR5_1 BR5_3 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR5_3.
  zstep.
  unfold ossl_provider_store_new_s5_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s6_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160304) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 (v1 + 24)) (Z_to_bv 64 0) b3_6 b4_6 b5_6 b6_6 b7_6 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 2073476) fc6 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv5 Hv6 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR6_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR6_2.
  zstep.
  unfold ossl_provider_store_new_s6_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s7_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160324) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180456) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
            F7 (Z_to_bv 64 2075068) fc7 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 Hv5 Hv6 Hv7 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 5 zstep.
  unfold ossl_provider_store_new_s7_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s8_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160340) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180500) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
            F8 (Z_to_bv 64 2075148) fc8 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv5 Hv6 Hv7 Hv8 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.
  unfold ossl_provider_store_new_s8_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s9_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v5 v6 v7 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160356) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180332) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
            F9 (Z_to_bv 64 2074988) fc9 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv5 Hv6 Hv7 Hv9 UT MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  do 4 zstep.
  unfold ossl_provider_store_new_s9_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s10_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v5 v6 v7 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2160388) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 2055740) fc10 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv5 Hv6 Hv7 Hv10 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR10_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR10_2.
  zstep.
  unfold ossl_provider_store_new_s10_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_provider_store_new_s11_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v5 v6 v7 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_11 u1_11 u2_11 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 1) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (ret_pc ra) fc11 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v6); C8 (Z_to_bv 64 v11); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

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
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv5 Hv6 Hv7 Hv10 Hv11 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 BR11_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 80); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR11_2.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  zstep. wg_F.
  do 2 zstep.
  zstore.
  do 10 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_provider_store_new_s11_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
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
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x230 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_provider_store_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_provider_store_new_1, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_3, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_4, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_5, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_8, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_9, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_10, e_ossl_provider_store_new); (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_OPENSSL_sk_new_1, e_OPENSSL_sk_new); (SITE_ln_zalloc, e_lock_new); (SITE_OPENSSL_sk_new_null_1, e_OPENSSL_sk_new_null)]
                      [(SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new); (SITE_ossl_provider_store_new_3, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_4, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_5, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_6, e_lock_new); (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null); (SITE_ossl_provider_store_new_8, e_OPENSSL_sk_set_cmp_thunks); (SITE_ossl_provider_store_new_9, e_OPENSSL_sk_set_copy_thunks); (SITE_ossl_provider_store_new_10, e_OPENSSL_sk_set_thunks); (SITE_ossl_provider_store_new_11, e_lock_new); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_OPENSSL_sk_new_1, e_CRYPTO_zalloc); (SITE_ln_zalloc, e_CRYPTO_zalloc); (SITE_OPENSSL_sk_new_null_1, e_CRYPTO_zalloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 5 <= LIVE_MAX -> mcost 80 + mcost 56 + 1 + mcost 56 + 1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_provider_store_new m)))
    (fun c => exists (Σ' : rts RT) (q1 q2 q3 q4 q5 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 80
           /\ acc asegs m' q1 80
           /\ wr_at asegs m' q2 56
           /\ acc asegs m' q2 56
           /\ wr_at asegs m' q3 40
           /\ acc asegs m' q3 40
           /\ wr_at asegs m' q4 56
           /\ acc asegs m' q4 56
           /\ wr_at asegs m' q5 40
           /\ acc asegs m' q5 40
           /\ rw_cells asegs m' q1 [C8 a0; C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q4); C8 (Z_to_bv 64 q3); C8 (Z_to_bv 64 q5); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 1); CB 7 (repeat (Z_to_bv 8 0) 7)]
           /\ rw_cells asegs m' q2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]
           /\ rw_cells asegs m' q3 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q4 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180456); C8 (Z_to_bv 64 2180332); C8 (Z_to_bv 64 2180500)]
           /\ rw_cells asegs m' q5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q5, 40) :: (q4, 56) :: (q3, 40) :: (q2, 56) :: (q1, 80) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 80 + mcost 56 + 1 + mcost 56 + 1) /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 80 < USTACK_TOP /\ 0 < q2 /\ q2 mod 16 = 0 /\ q2 + 56 < USTACK_TOP /\ 0 < q3 /\ q3 mod 16 = 0 /\ q3 + 40 < USTACK_TOP /\ 0 < q4 /\ q4 mod 16 = 0 /\ q4 + 56 < USTACK_TOP /\ 0 < q5 /\ q5 mod 16 = 0 /\ q5 + 40 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_provider_store_new_cps : ossl_provider_store_new_stmt.
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
  pose proof (wg_mcost_nonneg 56) as MC_56.
  pose proof (wg_mcost_nonneg 80) as MC_80.
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
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
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_provider_store_new e_CRYPTO_zalloc SITE_ossl_provider_store_new_1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTX
              (proj1 CGH (SITE_ossl_provider_store_new_1, e_ossl_provider_store_new) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_provider_store_new_1, e_CRYPTO_zalloc) ltac:(wp_in_lit)) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H1_0))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CRYPTO_zalloc Σ PMc (Z_to_bv 64 SITE_ossl_provider_store_new_1) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 80) (Z_to_bv 64 311200) (Z_to_bv 64 312) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 80 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_provider_store_new_1) by (unfold SITE_ossl_provider_store_new_1; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & v1 & Hc2 & LV2 & FRS2 & SP2 & CR2 & P0_v1 & P16_v1 & PU_v1 & CG2).
  wp_box1 PU_v1.
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & G1_ENVp & G1_WR & G1_ACC & G1_ZER) & Hc2'). clear Hc2.
  destruct RS2 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & F1 & fc1 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_provider_store_new_1) in Hc2' by (unfold SITE_ossl_provider_store_new_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; exact (AGc2 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AGu2) as UWF2.
  cl_keep H1_0 AGc2 WM2 KF1.
  pose proof SP2 as SPc2. pose proof CG2 as CGc2.
  assert (LOW2 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SPc2; exact LOW).
  assert (LEN2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (rewrite LV2; cbn [length]; lia).
  assert (LENc2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by lia. wp_box1 CR2.
  assert (Hfr2 : (length (rt_frames RT Σ1) < FRAMES_MAX)%nat) by (rewrite FRS2; exact Hfr).
  assert (CTXb2 : cg_ctx (rt_cg RT Σ1) e_ossl_provider_store_new (bv_unsigned ra :: outer)) by (rewrite CGc2; exact CTX).
  assert (CGH2 : cg_has (rt_cg RT Σ1) _ _) by (rewrite CGc2; exact CGH).
  assert (INP_v1_2 : In (v1, 80) (rt_live RT Σ1)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 v1 80 ART2 INP_v1_2) as (_ & PHI_v1 & _). rewrite SPc2 in PHI_v1.
  pose proof (afp_live_mem RT GOBJ AFP Σ1 m2 v1 80 ART2 INP_v1_2 ltac:(lia)) as (_ & PT_v1).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 80 ART2 INP_v1_2 ltac:(lia)) as PHH_v1.
  pose proof (wg_mod16_8 _ P16_v1) as PAL_v1. assert (PR64_v1 : 0 <= v1 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v1 : v1 + 80 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v1. wp_box1 PAL_v1. wp_box1 PR64_v1.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ1 m2 v1 80 ART2 INP_v1_2) as (WR_v1_3 & ACC_v1_3).
  pose proof (wp_cells_congr asegs m2 v1 [CB (Z.to_nat 80) (repeat (Z_to_bv 8 0) (Z.to_nat 80))] [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)] ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m2 v1 80 G1_ZER WR_v1_3 ltac:(lia))) as HB_v1_3.
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 SHC2 PR64_v1 UT2 HB_v1_3 ACC_v1_3 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & H3_2 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_1.
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 48 [] ART2 ltac:(rewrite SPc2; lia) ltac:(lia) MU3); [|exact WM3].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary G1_ENVp MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ossl_provider_store_new e_OPENSSL_sk_new SITE_ossl_provider_store_new_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb2
              (proj1 CGH2 (SITE_ossl_provider_store_new_2, e_ossl_provider_store_new) ltac:(wp_in_lit)) (proj2 CGH2 (SITE_ossl_provider_store_new_2, e_OPENSSL_sk_new) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H3_1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_new Σ1 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_2) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 2160572) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW2 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_provider_store_new_2) by (unfold SITE_ossl_provider_store_new_2; lia). exact CTXc3. }
  { exact UWCc3. }
  { apply (cg_has_weaken _ _ _ _ _ CGH2); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_WR_v1 & G2_ACC_v1 & G2_CL0) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_provider_store_new_2) in Hc4' by (unfold SITE_ossl_provider_store_new_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  assert (KF3 : rw_cells asegs m4 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (apply (wg_keep_live _ _ _ _ m3 m4 v1 80 _ _ H3_0 PRES4 WM4 INP_v1_2); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H3_1 AGc4 WM4 KF4.
  assert (SPc4 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP4; exact SPc2).
  assert (CGc4 : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite CG4; exact CGc2).
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ1)) + 1) by (rewrite LV4; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 2) by lia. clear LENc2. wp_box1 LEN2. wp_box1 CR4.
  assert (Hfr4 : (length (rt_frames RT Σ2) < FRAMES_MAX)%nat) by (rewrite FRS4; exact Hfr2).
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_provider_store_new (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v1_4 : In (v1, 80) (rt_live RT Σ2)) by (rewrite LV4; do 1 right; exact INP_v1_2).
  assert (INP_v2_4 : In (v2, 56) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 56 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 56 ART4 INP_v2_4 ltac:(lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 56 ART4 INP_v2_4 ltac:(lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v2 : v2 + 56 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF3 KF4 SHC4 PR64_v1 PR64_v2 UT4 MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & H5_2 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5', H5_1.
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 48 [] ART4 ltac:(rewrite SPc4; lia) ltac:(lia) MU5); [|exact WM5].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF6 : rw_cells asegs m5 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m4 m5 _ _ G2_CL0 MU5 WM5); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AGs5 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AGs5) as UWF5.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_3) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180372) b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2
           F2 fc2 m5 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 2160572) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF6. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc5'. }
  clear Hc5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & G3_CL0) & Hc6'). clear Hc6.
  destruct RS6 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & F3 & fc3 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ossl_provider_store_new_3) in Hc6' by (unfold SITE_ossl_provider_store_new_3; clear; first [reflexivity | lia]).
  assert (AGc6 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu6 : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6) by (intros a Ha; exact (AGc6 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AGu6) as UWF6.
  assert (KF7 : rw_cells asegs m6 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_live _ _ _ _ m5 m6 v1 80 _ _ H5_0 PRES6 WM6 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H5_1 AGc6 WM6 KF8.
  destruct (af_client_consts RT AF Σ2 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  assert (ENV6 : cl_env m6 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m5 m6 _ _ ENV5). intros a Ha. apply PRES6; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_3) u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v2 F3 fc3 m6 lo
                ST6 WHLO WHIMG WHTOP KF7 KF8 SHC6 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) UT6 MI6) as W7.
  cl_lift W7 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & H7_0 & H7_1 & H7_2 & ST7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7', H7_1.
  assert (ART7 : ART RT Σ2 m7).
  { apply (wg_seg_ART RT AF Σ2 m6 m7 usp 48 [] ART6 ltac:(rewrite SPc4; lia) ltac:(lia) MU7); [|exact WM7].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF11 : rw_cells asegs m7 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m6 m7 _ _ G3_CL0 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m6 m7 _ canary ENV6 MU7 ltac:(cl_fp_lia)) as ENV7.
  assert (AGs7 : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7) by (intros a Ha; apply MU7; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AGs7) as UWF7.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_4) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180416) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
           F3 fc3 m7 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 2160572) (Z_to_bv 64 2180372) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART7 MI7).
  { fold usp in SPA. cl_call_ok EU1 ST7 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF11. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc7'. }
  clear Hc7'. intros c8 Hc8.
  destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & G4_CL0) & Hc8'). clear Hc8.
  destruct RS8 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & F4 & fc4 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ossl_provider_store_new_4) in Hc8' by (unfold SITE_ossl_provider_store_new_4; clear; first [reflexivity | lia]).
  assert (AGc8 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES8; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; exact (AGc8 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AGu8) as UWF8.
  assert (KF12 : rw_cells asegs m8 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_live _ _ _ _ m7 m8 v1 80 _ _ H7_0 PRES8 WM8 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H7_1 AGc8 WM8 KF13.
  destruct (af_client_consts RT AF Σ2 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  assert (ENV8 : cl_env m8 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m7 m8 _ _ ENV7). intros a Ha. apply PRES8; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s4_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_4) u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v2 F4 fc4 m8 lo
                ST8 WHLO WHIMG WHTOP KF12 KF13 SHC8 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) UT8 MI8) as W9.
  cl_lift W9 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & H9_0 & H9_1 & H9_2 & ST9) & Hc9'). clear Hc9.
  fold usp in MU9, ST9, Hc9', H9_1.
  assert (ART9 : ART RT Σ2 m9).
  { apply (wg_seg_ART RT AF Σ2 m8 m9 usp 48 [] ART8 ltac:(rewrite SPc4; lia) ltac:(lia) MU9); [|exact WM9].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF16 : rw_cells asegs m9 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_seg _ m8 m9 _ _ G4_CL0 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m8 m9 _ canary ENV8 MU9 ltac:(cl_fp_lia)) as ENV9.
  assert (AGs9 : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9) by (intros a Ha; apply MU9; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AGs9) as UWF9.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_thunks Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_5) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 2180292) b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4
           F4 fc4 m9 lo v2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 2160572) (Z_to_bv 64 2180372) (Z_to_bv 64 0) (Z_to_bv 64 2180416) FDO MST eq_refl eq_refl ART9 MI9).
  { fold usp in SPA. cl_call_ok EU1 ST9 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v2_4. }
  { exact P16_v2. }
  { exact KF16. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc9'. }
  clear Hc9'. intros c10 Hc10.
  destruct (ASTA_unpack RT Σ2 _ _ c10 Hc10) as (ms10 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & G5_CL0) & Hc10'). clear Hc10.
  destruct RS10 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & F5 & fc5 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_ossl_provider_store_new_5) in Hc10' by (unfold SITE_ossl_provider_store_new_5; clear; first [reflexivity | lia]).
  assert (AGc10 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES10; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu10 : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10) by (intros a Ha; exact (AGc10 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AGu10) as UWF10.
  assert (KF17 : rw_cells asegs m10 v1 [CB 72 (repeat (Z_to_bv 8 0) 72); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_live _ _ _ _ m9 m10 v1 80 _ _ H9_0 PRES10 WM10 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H9_1 AGc10 WM10 KF18.
  destruct (af_client_consts RT AF Σ2 m10 ART10) as (_ & SHC10 & _ & _ & UT10).
  assert (ENV10 : cl_env m10 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v2, v2 + 56)]) by cl_fp_lia. apply (cl_env_agree m9 m10 _ _ ENV9). intros a Ha. apply PRES10; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ2 m10 v1 80 ART10 INP_v1_4) as (WR_v1_11 & ACC_v1_11).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s5_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_5) u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v2 F5 fc5 m10 lo
                ST10 WHLO WHIMG WHTOP KF17 KF18 SHC10 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) UT10 ACC_v1_11 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI10) as W11.
  cl_lift W11 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ2 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & H11_0 & H11_1 & H11_2 & ST11) & Hc11'). clear Hc11.
  fold usp in MU11, ST11, Hc11', H11_1.
  assert (ART11 : ART RT Σ2 m11).
  { apply (wg_seg_ART RT AF Σ2 m10 m11 usp 48 [(v1, v1 + 80)] ART10 ltac:(rewrite SPc4; lia) ltac:(lia) MU11); [|exact WM11].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 80; split; [exact INP_v1_4 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF21 : rw_cells asegs m11 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m10 m11 _ _ G5_CL0 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m10 m11 _ canary ENV10 MU11 ltac:(cl_fp_lia)) as ENV11.
  assert (AGs11 : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11) by (intros a Ha; apply MU11; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AGs11) as UWF11.
  destruct (cl_chain_call (rt_cg RT Σ2) e_ossl_provider_store_new e_lock_new SITE_ossl_provider_store_new_6 m11 m11 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb4
              (proj1 CGH4 (SITE_ossl_provider_store_new_6, e_ossl_provider_store_new) ltac:(wp_in_lit)) (proj2 CGH4 (SITE_ossl_provider_store_new_6, e_lock_new) ltac:(wp_in_lit)) UWF11 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m11 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H11_1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc11 & UWCc11).
  (* [comment removed for export] *)
  apply (C_lock_new Σ2 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_6) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5
           F5 fc5 m11 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART11 MI11).
  { fold usp in SPA. cl_call_ok EU1 ST11 LOW4 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_provider_store_new_6) by (unfold SITE_ossl_provider_store_new_6; lia). exact CTXc11. }
  { exact UWCc11. }
  { apply (cg_has_weaken _ _ _ _ _ CGH4); vm_compute; reflexivity. }
  { exact Hfr4. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV11. }
  { exact Hc11'. }
  clear Hc11'. intros c12 (Σ6 & v6 & Hc12 & LV12 & FRS12 & SP12 & CR12 & P0_v6 & P16_v6 & PU_v6 & CG12).
  wp_box1 PU_v6.
  destruct (ASTA_unpack RT Σ6 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & G6_ENVp & G6_MX & G6_ACC) & Hc12'). clear Hc12.
  destruct RS12 as (u0_6 & u1_6 & u2_6 & b1_6 & b2_6 & b3_6 & b4_6 & b5_6 & b6_6 & b7_6 & u3_6 & u4_6 & u5_6 & u6_6 & F6 & fc6 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_ossl_provider_store_new_6) in Hc12' by (unfold SITE_ossl_provider_store_new_6; clear; first [reflexivity | lia]).
  assert (AGc12 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m11 m12).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES12; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu12 : agree_on (fun x => usp <= x < USTACK_TOP) m11 m12) by (intros a Ha; exact (AGc12 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m11 m12 sp s0 UWF11 AGu12) as UWF12.
  assert (KF22 : rw_cells asegs m12 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 56 (repeat (Z_to_bv 8 0) 56); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v1 80 _ _ H11_0 PRES12 WM12 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H11_1 AGc12 WM12 KF23.
  assert (KF25 : rw_cells asegs m12 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v2 56 _ _ KF21 PRES12 WM12 INP_v2_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc12 : rt_sp0 RT Σ6 = rt_sp0 RT Σ) by (rewrite SP12; exact SPc4).
  assert (CGc12 : rt_cg RT Σ6 = rt_cg RT Σ) by (rewrite CG12; exact CGc4).
  assert (LOW12 : rt_sp0 RT Σ6 - STACK_WIN <= lo) by (rewrite SPc12; exact LOW).
  assert (LEN12 : Z.of_nat (length (rt_live RT Σ6)) = Z.of_nat (length (rt_live RT Σ2)) + 1) by (rewrite LV12; cbn [length]; lia).
  assert (LENc12 : Z.of_nat (length (rt_live RT Σ6)) = Z.of_nat (length (rt_live RT Σ)) + 3) by lia. clear LENc4. wp_box1 LEN4. wp_box1 CR12.
  assert (Hfr12 : (length (rt_frames RT Σ6) < FRAMES_MAX)%nat) by (rewrite FRS12; exact Hfr4).
  assert (CTXb12 : cg_ctx (rt_cg RT Σ6) e_ossl_provider_store_new (bv_unsigned ra :: outer)) by (rewrite CGc12; exact CTX).
  assert (CGH12 : cg_has (rt_cg RT Σ6) _ _) by (rewrite CGc12; exact CGH).
  assert (INP_v1_12 : In (v1, 80) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v1_4).
  assert (INP_v2_12 : In (v2, 56) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v2_4).
  assert (INP_v6_12 : In (v6, 40) (rt_live RT Σ6)) by (rewrite LV12; left; reflexivity).
  pose proof (af_live_range RT AF Σ6 m12 v6 40 ART12 INP_v6_12) as (_ & PHI_v6 & _). rewrite SPc12 in PHI_v6.
  pose proof (afp_live_mem RT GOBJ AFP Σ6 m12 v6 40 ART12 INP_v6_12 ltac:(lia)) as (_ & PT_v6).
  pose proof (afp_live_hi RT GOBJ AFP Σ6 m12 v6 40 ART12 INP_v6_12 ltac:(lia)) as PHH_v6.
  pose proof (wg_mod16_8 _ P16_v6) as PAL_v6. assert (PR64_v6 : 0 <= v6 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v6 : v6 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v6. wp_box1 PAL_v6. wp_box1 PR64_v6.
  destruct (af_client_consts RT AF Σ6 m12 ART12) as (_ & SHC12 & _ & _ & UT12).
  pose proof (af_acc_live RT AF Σ6 m12 v1 80 ART12 INP_v1_12) as (WR_v1_13 & ACC_v1_13).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s6_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_6) u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v2 v6 F6 fc6 m12 lo
                ST12 WHLO WHIMG WHTOP KF22 KF23 SHC12 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 UT12 ACC_v1_13 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI12) as W13.
  cl_lift W13 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ6 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13 & H13_0 & H13_1 & H13_2 & ST13) & Hc13'). clear Hc13.
  fold usp in MU13, ST13, Hc13', H13_1.
  assert (ART13 : ART RT Σ6 m13).
  { apply (wg_seg_ART RT AF Σ6 m12 m13 usp 48 [(v1, v1 + 80)] ART12 ltac:(rewrite SPc12; lia) ltac:(lia) MU13); [|exact WM13].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 80; split; [exact INP_v1_12 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF26 : rw_cells asegs m13 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m12 m13 _ _ KF25 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF27 : rw_cells asegs m13 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 40 (rt_live RT Σ2) v1 80 ART12 LV12 ltac:(cbn [app In]; exact INP_v1_4)) as DJ_v6_v1; apply (wg_keep_seg _ m12 m13 _ _ G6_MX MU13 WM13); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v1 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m12 m13 _ canary G6_ENVp MU13 ltac:(cl_fp_lia)) as ENV13.
  assert (AGs13 : agree_on (fun x => usp <= x < USTACK_TOP) m12 m13) by (intros a Ha; apply MU13; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m12 m13 sp s0 UWF12 AGs13) as UWF13.
  destruct (cl_chain_call (rt_cg RT Σ6) e_ossl_provider_store_new e_OPENSSL_sk_new_null SITE_ossl_provider_store_new_7 m13 m13 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb12
              (proj1 CGH12 (SITE_ossl_provider_store_new_7, e_ossl_provider_store_new) ltac:(wp_in_lit)) (proj2 CGH12 (SITE_ossl_provider_store_new_7, e_OPENSSL_sk_new_null) ltac:(wp_in_lit)) UWF13 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m13 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H13_1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc13 & UWCc13).
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_new_null Σ6 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_7) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 (v1 + 24)) (Z_to_bv 64 0) b3_6 b4_6 b5_6 b6_6 b7_6 a0 (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6
           F6 fc6 m13 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART13 MI13).
  { fold usp in SPA. cl_call_ok EU1 ST13 LOW12 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_provider_store_new_7) by (unfold SITE_ossl_provider_store_new_7; lia). exact CTXc13. }
  { exact UWCc13. }
  { apply (cg_has_weaken _ _ _ _ _ CGH12); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV13. }
  { exact Hc13'. }
  clear Hc13'. intros c14 (Σ7 & v7 & Hc14 & LV14 & FRS14 & SP14 & CR14 & P0_v7 & P16_v7 & PU_v7 & CG14).
  wp_box1 PU_v7.
  destruct (ASTA_unpack RT Σ7 _ _ c14 Hc14) as (ms14 & (m14 & RS14 & (ART14 & MI14 & WM14 & ST14) & PRES14 & G7_ENVp & G7_WR_v1 & G7_ACC_v1 & G7_CL0) & Hc14'). clear Hc14.
  destruct RS14 as (u0_7 & u1_7 & u2_7 & b1_7 & b2_7 & b3_7 & b4_7 & b5_7 & b6_7 & b7_7 & u3_7 & u4_7 & u5_7 & u6_7 & F7 & fc7 & ->).
  rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even SITE_ossl_provider_store_new_7) in Hc14' by (unfold SITE_ossl_provider_store_new_7; clear; first [reflexivity | lia]).
  assert (AGc14 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m13 m14).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES14; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu14 : agree_on (fun x => usp <= x < USTACK_TOP) m13 m14) by (intros a Ha; exact (AGc14 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m13 m14 sp s0 UWF13 AGu14) as UWF14.
  assert (KF28 : rw_cells asegs m14 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v1 80 _ _ H13_0 PRES14 WM14 INP_v1_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H13_1 AGc14 WM14 KF29.
  assert (KF31 : rw_cells asegs m14 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v2 56 _ _ KF26 PRES14 WM14 INP_v2_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF32 : rw_cells asegs m14 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m13 m14 v6 40 _ _ KF27 PRES14 WM14 INP_v6_12); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc14 : rt_sp0 RT Σ7 = rt_sp0 RT Σ) by (rewrite SP14; exact SPc12).
  assert (CGc14 : rt_cg RT Σ7 = rt_cg RT Σ) by (rewrite CG14; exact CGc12).
  assert (LOW14 : rt_sp0 RT Σ7 - STACK_WIN <= lo) by (rewrite SPc14; exact LOW).
  assert (LEN14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ6)) + 1) by (rewrite LV14; cbn [length]; lia).
  assert (LENc14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ)) + 4) by lia. clear LENc12. wp_box1 LEN12. wp_box1 CR14.
  assert (Hfr14 : (length (rt_frames RT Σ7) < FRAMES_MAX)%nat) by (rewrite FRS14; exact Hfr12).
  assert (CTXb14 : cg_ctx (rt_cg RT Σ7) e_ossl_provider_store_new (bv_unsigned ra :: outer)) by (rewrite CGc14; exact CTX).
  assert (CGH14 : cg_has (rt_cg RT Σ7) _ _) by (rewrite CGc14; exact CGH).
  assert (INP_v1_14 : In (v1, 80) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v1_12).
  assert (INP_v2_14 : In (v2, 56) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v2_12).
  assert (INP_v6_14 : In (v6, 40) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v6_12).
  assert (INP_v7_14 : In (v7, 56) (rt_live RT Σ7)) by (rewrite LV14; left; reflexivity).
  pose proof (af_live_range RT AF Σ7 m14 v7 56 ART14 INP_v7_14) as (_ & PHI_v7 & _). rewrite SPc14 in PHI_v7.
  pose proof (afp_live_mem RT GOBJ AFP Σ7 m14 v7 56 ART14 INP_v7_14 ltac:(lia)) as (_ & PT_v7).
  pose proof (afp_live_hi RT GOBJ AFP Σ7 m14 v7 56 ART14 INP_v7_14 ltac:(lia)) as PHH_v7.
  pose proof (wg_mod16_8 _ P16_v7) as PAL_v7. assert (PR64_v7 : 0 <= v7 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v7 : v7 + 56 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v7. wp_box1 PAL_v7. wp_box1 PR64_v7.
  destruct (af_client_consts RT AF Σ7 m14 ART14) as (_ & SHC14 & _ & _ & UT14).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s7_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_7) u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v2 v6 v7 F7 fc7 m14 lo
                ST14 WHLO WHIMG WHTOP KF28 KF29 SHC14 PR64_v1 PR64_v2 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 PR64_v7 UT14 MI14) as W15.
  cl_lift W15 Hc14' c15 Hc15.
  destruct (ASTA_unpack RT Σ7 _ _ c15 Hc15) as (ms15 & (m15 & -> & MU15 & WM15 & MI15 & H15_0 & H15_1 & H15_2 & ST15) & Hc15'). clear Hc15.
  fold usp in MU15, ST15, Hc15', H15_1.
  assert (ART15 : ART RT Σ7 m15).
  { apply (wg_seg_ART RT AF Σ7 m14 m15 usp 48 [] ART14 ltac:(rewrite SPc14; lia) ltac:(lia) MU15); [|exact WM15].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF33 : rw_cells asegs m15 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_seg _ m14 m15 _ _ KF31 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF34 : rw_cells asegs m15 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m14 m15 _ _ KF32 MU15 WM15); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF35 : rw_cells asegs m15 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m14 m15 _ _ G7_CL0 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m14 m15 _ canary G7_ENVp MU15 ltac:(cl_fp_lia)) as ENV15.
  assert (AGs15 : agree_on (fun x => usp <= x < USTACK_TOP) m14 m15) by (intros a Ha; apply MU15; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m14 m15 sp s0 UWF14 AGs15) as UWF15.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_cmp_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_8) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180456) b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7
           F7 fc7 m15 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART15 MI15).
  { fold usp in SPA. cl_call_ok EU1 ST15 LOW14 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF35. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc15'. }
  clear Hc15'. intros c16 Hc16.
  destruct (ASTA_unpack RT Σ7 _ _ c16 Hc16) as (ms16 & (m16 & RS16 & (ART16 & MI16 & WM16 & ST16) & PRES16 & G8_CL0) & Hc16'). clear Hc16.
  destruct RS16 as (u0_8 & u1_8 & u2_8 & b1_8 & b2_8 & b3_8 & b4_8 & b5_8 & b6_8 & b7_8 & u3_8 & u4_8 & u5_8 & u6_8 & F8 & fc8 & ->).
  rewrite EU1 in ST16, PRES16. rewrite (ret_pc_even SITE_ossl_provider_store_new_8) in Hc16' by (unfold SITE_ossl_provider_store_new_8; clear; first [reflexivity | lia]).
  assert (AGc16 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m15 m16).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES16; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu16 : agree_on (fun x => usp <= x < USTACK_TOP) m15 m16) by (intros a Ha; exact (AGc16 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m15 m16 sp s0 UWF15 AGu16) as UWF16.
  assert (KF36 : rw_cells asegs m16 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v1 80 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m15 m16 v1 80 _ _ H15_0 PRES16 WM16 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H15_1 AGc16 WM16 KF37.
  assert (KF39 : rw_cells asegs m16 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v2 56 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m15 m16 v2 56 _ _ KF33 PRES16 WM16 INP_v2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF40 : rw_cells asegs m16 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v6 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v6_12)) as DJ_v7_v6; apply (wg_keep_live _ _ _ _ m15 m16 v6 40 _ _ KF34 PRES16 WM16 INP_v6_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v6 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  destruct (af_client_consts RT AF Σ7 m16 ART16) as (_ & SHC16 & _ & _ & UT16).
  assert (ENV16 : cl_env m16 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m15 m16 _ _ ENV15). intros a Ha. apply PRES16; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s8_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_8) u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v6 v7 v7 F8 fc8 m16 lo
                ST16 WHLO WHIMG WHTOP KF36 KF37 SHC16 PR64_v1 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 PR64_v7 ltac:(unfold USTACK_TOP in *; lia) UT16 MI16) as W17.
  cl_lift W17 Hc16' c17 Hc17.
  destruct (ASTA_unpack RT Σ7 _ _ c17 Hc17) as (ms17 & (m17 & -> & MU17 & WM17 & MI17 & H17_0 & H17_1 & H17_2 & ST17) & Hc17'). clear Hc17.
  fold usp in MU17, ST17, Hc17', H17_1.
  assert (ART17 : ART RT Σ7 m17).
  { apply (wg_seg_ART RT AF Σ7 m16 m17 usp 48 [] ART16 ltac:(rewrite SPc14; lia) ltac:(lia) MU17); [|exact WM17].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF42 : rw_cells asegs m17 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_seg _ m16 m17 _ _ KF39 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF43 : rw_cells asegs m17 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m16 m17 _ _ KF40 MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF44 : rw_cells asegs m17 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180456); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) by (apply (wg_keep_seg _ m16 m17 _ _ G8_CL0 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m16 m17 _ canary ENV16 MU17 ltac:(cl_fp_lia)) as ENV17.
  assert (AGs17 : agree_on (fun x => usp <= x < USTACK_TOP) m16 m17) by (intros a Ha; apply MU17; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m16 m17 sp s0 UWF16 AGs17) as UWF17.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_copy_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_9) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180500) b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8
           F8 fc8 m17 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2180456) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl ART17 MI17).
  { fold usp in SPA. cl_call_ok EU1 ST17 LOW14 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF44. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc17'. }
  clear Hc17'. intros c18 Hc18.
  destruct (ASTA_unpack RT Σ7 _ _ c18 Hc18) as (ms18 & (m18 & RS18 & (ART18 & MI18 & WM18 & ST18) & PRES18 & G9_CL0) & Hc18'). clear Hc18.
  destruct RS18 as (u0_9 & u1_9 & u2_9 & b1_9 & b2_9 & b3_9 & b4_9 & b5_9 & b6_9 & b7_9 & u3_9 & u4_9 & u5_9 & u6_9 & F9 & fc9 & ->).
  rewrite EU1 in ST18, PRES18. rewrite (ret_pc_even SITE_ossl_provider_store_new_9) in Hc18' by (unfold SITE_ossl_provider_store_new_9; clear; first [reflexivity | lia]).
  assert (AGc18 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m17 m18).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES18; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu18 : agree_on (fun x => usp <= x < USTACK_TOP) m17 m18) by (intros a Ha; exact (AGc18 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m17 m18 sp s0 UWF17 AGu18) as UWF18.
  assert (KF45 : rw_cells asegs m18 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v1 80 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m17 m18 v1 80 _ _ H17_0 PRES18 WM18 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H17_1 AGc18 WM18 KF46.
  assert (KF48 : rw_cells asegs m18 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v2 56 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m17 m18 v2 56 _ _ KF42 PRES18 WM18 INP_v2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF49 : rw_cells asegs m18 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v6 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v6_12)) as DJ_v7_v6; apply (wg_keep_live _ _ _ _ m17 m18 v6 40 _ _ KF43 PRES18 WM18 INP_v6_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v6 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  destruct (af_client_consts RT AF Σ7 m18 ART18) as (_ & SHC18 & _ & _ & UT18).
  assert (ENV18 : cl_env m18 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m17 m18 _ _ ENV17). intros a Ha. apply PRES18; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s9_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_9) u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v6 v7 v7 F9 fc9 m18 lo
                ST18 WHLO WHIMG WHTOP KF45 KF46 SHC18 PR64_v1 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 PR64_v7 ltac:(unfold USTACK_TOP in *; lia) UT18 MI18) as W19.
  cl_lift W19 Hc18' c19 Hc19.
  destruct (ASTA_unpack RT Σ7 _ _ c19 Hc19) as (ms19 & (m19 & -> & MU19 & WM19 & MI19 & H19_0 & H19_1 & H19_2 & ST19) & Hc19'). clear Hc19.
  fold usp in MU19, ST19, Hc19', H19_1.
  assert (ART19 : ART RT Σ7 m19).
  { apply (wg_seg_ART RT AF Σ7 m18 m19 usp 48 [] ART18 ltac:(rewrite SPc14; lia) ltac:(lia) MU19); [|exact WM19].
    intros x Hx. exfalso; apply Hx; exact I. }
  assert (KF51 : rw_cells asegs m19 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_seg _ m18 m19 _ _ KF48 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF52 : rw_cells asegs m19 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_seg _ m18 m19 _ _ KF49 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF53 : rw_cells asegs m19 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180456); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180500)]) by (apply (wg_keep_seg _ m18 m19 _ _ G9_CL0 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m18 m19 _ canary ENV18 MU19 ltac:(cl_fp_lia)) as ENV19.
  assert (AGs19 : agree_on (fun x => usp <= x < USTACK_TOP) m18 m19) by (intros a Ha; apply MU19; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m18 m19 sp s0 UWF18 AGs19) as UWF19.
  (* [comment removed for export] *)
  apply (C_OPENSSL_sk_set_thunks Σ7 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_10) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 2180332) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9
           F9 fc9 m19 lo v7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 2180456) (Z_to_bv 64 0) (Z_to_bv 64 2180500) FDO MST eq_refl eq_refl ART19 MI19).
  { fold usp in SPA. cl_call_ok EU1 ST19 LOW14 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { exact INP_v7_14. }
  { exact P16_v7. }
  { exact KF53. }
  { (repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end). (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end). wg_cond. }
  { exact Hc19'. }
  clear Hc19'. intros c20 Hc20.
  destruct (ASTA_unpack RT Σ7 _ _ c20 Hc20) as (ms20 & (m20 & RS20 & (ART20 & MI20 & WM20 & ST20) & PRES20 & G10_CL0) & Hc20'). clear Hc20.
  destruct RS20 as (u0_10 & u1_10 & u2_10 & b1_10 & b2_10 & b3_10 & b4_10 & b5_10 & b6_10 & b7_10 & u3_10 & u4_10 & u5_10 & u6_10 & F10 & fc10 & ->).
  rewrite EU1 in ST20, PRES20. rewrite (ret_pc_even SITE_ossl_provider_store_new_10) in Hc20' by (unfold SITE_ossl_provider_store_new_10; clear; first [reflexivity | lia]).
  assert (AGc20 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m19 m20).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES20; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu20 : agree_on (fun x => usp <= x < USTACK_TOP) m19 m20) by (intros a Ha; exact (AGc20 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m19 m20 sp s0 UWF19 AGu20) as UWF20.
  assert (KF54 : rw_cells asegs m20 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v1 80 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_live _ _ _ _ m19 m20 v1 80 _ _ H19_0 PRES20 WM20 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H19_1 AGc20 WM20 KF55.
  assert (KF57 : rw_cells asegs m20 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v2 56 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_live _ _ _ _ m19 m20 v2 56 _ _ KF51 PRES20 WM20 INP_v2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF58 : rw_cells asegs m20 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v6 40 ART14 LV14 ltac:(cbn [app In]; exact INP_v6_12)) as DJ_v7_v6; apply (wg_keep_live _ _ _ _ m19 m20 v6 40 _ _ KF52 PRES20 WM20 INP_v6_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v6 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  destruct (af_client_consts RT AF Σ7 m20 ART20) as (_ & SHC20 & _ & _ & UT20).
  assert (ENV20 : cl_env m20 (Z_to_bv 8 1) canary).
  { assert (HFP : cl_fp [(v7, v7 + 56)]) by cl_fp_lia. apply (cl_env_agree m19 m20 _ _ ENV19). intros a Ha. apply PRES20; [right; left; exact (cl_cell_static _ Ha) | exact (HFP _ Ha)]. }
  pose proof (af_acc_live RT AF Σ7 m20 v1 80 ART20 INP_v1_14) as (WR_v1_21 & ACC_v1_21).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s10_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_10) u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v6 v7 v7 F10 fc10 m20 lo
                ST20 WHLO WHIMG WHTOP KF54 KF55 SHC20 PR64_v1 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 PR64_v7 ltac:(unfold USTACK_TOP in *; lia) UT20 ACC_v1_21 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI20) as W21.
  cl_lift W21 Hc20' c21 Hc21.
  destruct (ASTA_unpack RT Σ7 _ _ c21 Hc21) as (ms21 & (m21 & -> & MU21 & WM21 & MI21 & H21_0 & H21_1 & H21_2 & ST21) & Hc21'). clear Hc21.
  fold usp in MU21, ST21, Hc21', H21_1.
  assert (ART21 : ART RT Σ7 m21).
  { apply (wg_seg_ART RT AF Σ7 m20 m21 usp 48 [(v1, v1 + 80)] ART20 ltac:(rewrite SPc14; lia) ltac:(lia) MU21); [|exact WM21].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 80; split; [exact INP_v1_14 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF60 : rw_cells asegs m21 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m20 m21 _ _ KF57 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v2_v1 PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF61 : rw_cells asegs m21 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 40 (rt_live RT Σ2) v1 80 ART12 LV12 ltac:(cbn [app In]; exact INP_v1_4)) as DJ_v6_v1; apply (wg_keep_seg _ m20 m21 _ _ KF58 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v1 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF62 : rw_cells asegs m21 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180456); C8 (Z_to_bv 64 2180332); C8 (Z_to_bv 64 2180500)]) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v1 80 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_seg _ m20 m21 _ _ G10_CL0 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v1 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m20 m21 _ canary ENV20 MU21 ltac:(cl_fp_lia)) as ENV21.
  assert (AGs21 : agree_on (fun x => usp <= x < USTACK_TOP) m20 m21) by (intros a Ha; apply MU21; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m20 m21 sp s0 UWF20 AGs21) as UWF21.
  destruct (cl_chain_call (rt_cg RT Σ7) e_ossl_provider_store_new e_lock_new SITE_ossl_provider_store_new_11 m21 m21 ra s0 sp (Z_to_bv 64 (usp + -48)) outer CTXb14
              (proj1 CGH14 (SITE_ossl_provider_store_new_11, e_ossl_provider_store_new) ltac:(wp_in_lit)) (proj2 CGH14 (SITE_ossl_provider_store_new_11, e_lock_new) ltac:(wp_in_lit)) UWF21 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m21 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H21_1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc21 & UWCc21).
  (* [comment removed for export] *)
  apply (C_lock_new Σ7 PMc (Z_to_bv 64 SITE_ossl_provider_store_new_11) (Z_to_bv 64 (usp + -48)) gp (Z_to_bv 64 0xba3ef0) u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 a0 (Z_to_bv 64 v7) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10
           F10 fc10 m21 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART21 MI21).
  { fold usp in SPA. cl_call_ok EU1 ST21 LOW14 SPA 3. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_provider_store_new_11) by (unfold SITE_ossl_provider_store_new_11; lia). exact CTXc21. }
  { exact UWCc21. }
  { apply (cg_has_weaken _ _ _ _ _ CGH14); vm_compute; reflexivity. }
  { exact Hfr14. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV21. }
  { exact Hc21'. }
  clear Hc21'. intros c22 (Σ11 & v11 & Hc22 & LV22 & FRS22 & SP22 & CR22 & P0_v11 & P16_v11 & PU_v11 & CG22).
  wp_box1 PU_v11.
  destruct (ASTA_unpack RT Σ11 _ _ c22 Hc22) as (ms22 & (m22 & RS22 & (ART22 & MI22 & WM22 & ST22) & PRES22 & G11_ENVp & G11_MX & G11_ACC) & Hc22'). clear Hc22.
  destruct RS22 as (u0_11 & u1_11 & u2_11 & b1_11 & b2_11 & b3_11 & b4_11 & b5_11 & b6_11 & b7_11 & u3_11 & u4_11 & u5_11 & u6_11 & F11 & fc11 & ->).
  rewrite EU1 in ST22, PRES22. rewrite (ret_pc_even SITE_ossl_provider_store_new_11) in Hc22' by (unfold SITE_ossl_provider_store_new_11; clear; first [reflexivity | lia]).
  assert (AGc22 : forall a k, usp + -48 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m21 m22).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES22; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu22 : agree_on (fun x => usp <= x < USTACK_TOP) m21 m22) by (intros a Ha; exact (AGc22 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m21 m22 sp s0 UWF21 AGu22) as UWF22.
  assert (KF63 : rw_cells asegs m22 v1 [CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v6); CB 40 (repeat (Z_to_bv 8 0) 40); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v1 80 _ _ H21_0 PRES22 WM22 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H21_1 AGc22 WM22 KF64.
  assert (KF66 : rw_cells asegs m22 v2 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 2160572); C8 (Z_to_bv 64 2180372); C8 (Z_to_bv 64 2180292); C8 (Z_to_bv 64 2180416)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v2 56 _ _ KF60 PRES22 WM22 INP_v2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF67 : rw_cells asegs m22 v6 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v6 40 _ _ KF61 PRES22 WM22 INP_v6_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF68 : rw_cells asegs m22 v7 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 2180456); C8 (Z_to_bv 64 2180332); C8 (Z_to_bv 64 2180500)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v7 56 _ _ KF62 PRES22 WM22 INP_v7_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc22 : rt_sp0 RT Σ11 = rt_sp0 RT Σ) by (rewrite SP22; exact SPc14).
  assert (CGc22 : rt_cg RT Σ11 = rt_cg RT Σ) by (rewrite CG22; exact CGc14).
  assert (LOW22 : rt_sp0 RT Σ11 - STACK_WIN <= lo) by (rewrite SPc22; exact LOW).
  assert (LEN22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ7)) + 1) by (rewrite LV22; cbn [length]; lia).
  assert (LENc22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ)) + 5) by lia. clear LENc14. wp_box1 LEN14. wp_box1 CR22.
  assert (Hfr22 : (length (rt_frames RT Σ11) < FRAMES_MAX)%nat) by (rewrite FRS22; exact Hfr14).
  assert (CTXb22 : cg_ctx (rt_cg RT Σ11) e_ossl_provider_store_new (bv_unsigned ra :: outer)) by (rewrite CGc22; exact CTX).
  assert (CGH22 : cg_has (rt_cg RT Σ11) _ _) by (rewrite CGc22; exact CGH).
  assert (INP_v1_22 : In (v1, 80) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v1_14).
  assert (INP_v2_22 : In (v2, 56) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v2_14).
  assert (INP_v6_22 : In (v6, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v6_14).
  assert (INP_v7_22 : In (v7, 56) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v7_14).
  assert (INP_v11_22 : In (v11, 40) (rt_live RT Σ11)) by (rewrite LV22; left; reflexivity).
  pose proof (af_live_range RT AF Σ11 m22 v11 40 ART22 INP_v11_22) as (_ & PHI_v11 & _). rewrite SPc22 in PHI_v11.
  pose proof (afp_live_mem RT GOBJ AFP Σ11 m22 v11 40 ART22 INP_v11_22 ltac:(lia)) as (_ & PT_v11).
  pose proof (afp_live_hi RT GOBJ AFP Σ11 m22 v11 40 ART22 INP_v11_22 ltac:(lia)) as PHH_v11.
  pose proof (wg_mod16_8 _ P16_v11) as PAL_v11. assert (PR64_v11 : 0 <= v11 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v11 : v11 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v11. wp_box1 PAL_v11. wp_box1 PR64_v11.
  destruct (af_client_consts RT AF Σ11 m22 ART22) as (_ & SHC22 & _ & _ & UT22).
  pose proof (af_acc_live RT AF Σ11 m22 v1 80 ART22 INP_v1_22) as (WR_v1_23 & ACC_v1_23).
  (* [comment removed for export] *)
  pose proof (ossl_provider_store_new_s11_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_provider_store_new_11) u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v6 v7 v7 v11 F11 fc11 m22 lo
                ST22 WHLO WHIMG WHTOP KF63 KF64 SHC22 PR64_v1 ltac:(unfold USTACK_TOP in *; lia) PR64_v6 PR64_v7 ltac:(unfold USTACK_TOP in *; lia) PR64_v11 UT22 ACC_v1_23 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI22) as W23.
  cl_lift W23 Hc22' c23 Hc23.
  apply Hk. exists Σ11, v1, v2, v6, v7, v11.
  split; [| split; [rewrite LV22, LV14, LV12, LV4, LV2; reflexivity|]; split; [rewrite FRS22, FRS14, FRS12, FRS4, FRS2; reflexivity|]; split; [rewrite SP22, SP14, SP12, SP4, SP2; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v1|]; split; [exact P16_v1|]; split; [exact PU_v1|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; split; [exact P0_v6|]; split; [exact P16_v6|]; split; [exact PU_v6|]; split; [exact P0_v7|]; split; [exact P16_v7|]; split; [exact PU_v7|]; split; [exact P0_v11|]; split; [exact P16_v11|]; split; [exact PU_v11|]; rewrite CG22, CG14, CG12, CG4, CG2; reflexivity].
  apply (ASTA_conseq RT Σ11 PMc _ _ c23 Hc23). intros ms23 (m23 & -> & MU23 & WM23 & MI23 & H23_0 & H23_1 & ST23). fold usp in MU23, ST23.
  exists m23.
  split; [exists u0_11, u1_11, u2_11, (Z_to_bv 64 1), (Z_to_bv 64 0), b3_11, b4_11, b5_11, b6_11, b7_11, u3_11, u4_11, u5_11, u6_11, F11, fc11; reflexivity|].
  assert (ART23 : ART RT Σ11 m23).
  { apply (wg_seg_ART RT AF Σ11 m22 m23 usp 48 [(v1, v1 + 80)] ART22 ltac:(rewrite SPc22; lia) ltac:(lia) MU23); [|exact WM23].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 80; split; [exact INP_v1_22 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART23|]; split; [exact MI23|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 (wmono_trans asegs _ _ _ WM13 (wmono_trans asegs _ _ _ WM14 (wmono_trans asegs _ _ _ WM15 (wmono_trans asegs _ _ _ WM16 (wmono_trans asegs _ _ _ WM17 (wmono_trans asegs _ _ _ WM18 (wmono_trans asegs _ _ _ WM19 (wmono_trans asegs _ _ _ WM20 (wmono_trans asegs _ _ _ WM21 (wmono_trans asegs _ _ _ WM22 WM23)))))))))))))))))))))) | exact ST23]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 1 right; exact He | rewrite FRS2; intros e He; exact He | lia]).
    assert (NA_v1 : ~ (v1 <= bv_unsigned a < v1 + 80)) by exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(v1, 80)] v1 80 usp _ ART2 LV2 ltac:(left; reflexivity) FRS2 SP2 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha).
    wp_box1 NA_v1.
    assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; rewrite LV4; do 1 right; exact He | rewrite FRS4; intros e He; exact He | lia]).
    assert (NA_v2 : ~ (v2 <= bv_unsigned a < v2 + 56)) by exact (wg_newchunk_apart RT AF Σ1 Σ2 m4 [(v2, 56)] v2 56 usp _ ART4 LV4 ltac:(left; reflexivity) FRS4 SP4 ltac:(rewrite SPc2; unfold RT_STACK in *; lia) ltac:(lia) Ha1).
    wp_box1 NA_v2.
    wp_box1 Ha1.
    assert (Ha3 : aclient (rt_live RT Σ6) (rt_frames RT Σ6) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha2); [intros e He; rewrite LV12; do 1 right; exact He | rewrite FRS12; intros e He; exact He | lia]).
    assert (NA_v6 : ~ (v6 <= bv_unsigned a < v6 + 40)) by exact (wg_newchunk_apart RT AF Σ2 Σ6 m12 [(v6, 40)] v6 40 usp _ ART12 LV12 ltac:(left; reflexivity) FRS12 SP12 ltac:(rewrite SPc4; unfold RT_STACK in *; lia) ltac:(lia) Ha2).
    wp_box1 NA_v6.
    wp_box1 Ha2.
    assert (Ha4 : aclient (rt_live RT Σ7) (rt_frames RT Σ7) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha3); [intros e He; rewrite LV14; do 1 right; exact He | rewrite FRS14; intros e He; exact He | lia]).
    assert (NA_v7 : ~ (v7 <= bv_unsigned a < v7 + 56)) by exact (wg_newchunk_apart RT AF Σ6 Σ7 m14 [(v7, 56)] v7 56 usp _ ART14 LV14 ltac:(left; reflexivity) FRS14 SP14 ltac:(rewrite SPc12; unfold RT_STACK in *; lia) ltac:(lia) Ha3).
    wp_box1 NA_v7.
    wp_box1 Ha3.
    assert (Ha5 : aclient (rt_live RT Σ11) (rt_frames RT Σ11) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha4); [intros e He; rewrite LV22; do 1 right; exact He | rewrite FRS22; intros e He; exact He | lia]).
    assert (NA_v11 : ~ (v11 <= bv_unsigned a < v11 + 40)) by exact (wg_newchunk_apart RT AF Σ7 Σ11 m22 [(v11, 40)] v11 40 usp _ ART22 LV22 ltac:(left; reflexivity) FRS22 SP22 ltac:(rewrite SPc14; unfold RT_STACK in *; lia) ltac:(lia) Ha4).
    wp_box1 NA_v11.
    wp_box1 Ha4.
    wp_box1 Ha5.
    pose proof (cl_split RT AF Σ m usp 48 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
    rewrite (MU23 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES22 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU21 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES20 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU19 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES18 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU17 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES16 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU15 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES14 a ltac:(unfold wp_box in Ha3; destruct Ha3 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU13 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES12 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU11 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES10 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU9 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES8 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU7 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES6 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU5 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES4 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU3 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES2 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    reflexivity. }
  pose proof (af_acc_live RT AF Σ11 m23 v1 80 ART23 INP_v1_22) as (WRE_v1 & ACCE_v1).
  pose proof (af_acc_live RT AF Σ11 m23 v2 56 ART23 INP_v2_22) as (WRE_v2 & ACCE_v2).
  pose proof (af_acc_live RT AF Σ11 m23 v6 40 ART23 INP_v6_22) as (WRE_v6 & ACCE_v6).
  pose proof (af_acc_live RT AF Σ11 m23 v7 56 ART23 INP_v7_22) as (WRE_v7 & ACCE_v7).
  pose proof (af_acc_live RT AF Σ11 m23 v11 40 ART23 INP_v11_22) as (WRE_v11 & ACCE_v11).
  split; [exact (cl_env_seg _ m22 m23 _ canary G11_ENVp MU23 ltac:(cl_fp_lia))|].
  split; [exact WRE_v1|].
  split; [exact ACCE_v1|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  split; [exact WRE_v6|].
  split; [exact ACCE_v6|].
  split; [exact WRE_v7|].
  split; [exact ACCE_v7|].
  split; [exact WRE_v11|].
  split; [exact ACCE_v11|].
  split; [exact H23_0|].
  split; [pose proof (wg_live_apart RT AF Σ2 m4 [] v2 56 (rt_live RT Σ1) v1 80 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; apply (wg_keep_seg _ m22 m23 _ _ KF66 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ6 m12 [] v6 40 (rt_live RT Σ2) v1 80 ART12 LV12 ltac:(cbn [app In]; exact INP_v1_4)) as DJ_v6_v1; apply (wg_keep_seg _ m22 m23 _ _ KF67 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ7 m14 [] v7 56 (rt_live RT Σ6) v1 80 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_seg _ m22 m23 _ _ KF68 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ7) v1 80 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v11_v1; apply (wg_keep_seg _ m22 m23 _ _ G11_MX MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I.
Qed.
End ossl_provider_store_new_cps.
