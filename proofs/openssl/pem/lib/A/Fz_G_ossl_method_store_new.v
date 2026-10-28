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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_G_CRYPTO_calloc Fz_G_ossl_sa_new Th_mutex Fz_M_locknew.
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

Definition e_ossl_method_store_new : Z := 0x204724.
Definition SITE_ossl_method_store_new_1 : Z := 0x204770.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_2 : Z := 0x2047a8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_3 : Z := 0x2047bc.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_4 : Z := 0x2047d8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_5 : Z := 0x2047f8.     (* [comment removed for export] *)
Definition SITE_ossl_method_store_new_6 : Z := 0x204840.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ossl_method_store_new_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115440) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 24) (Z_to_bv 64 308352) (Z_to_bv 64 328) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 2080748) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x204724) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  zstep.
  do 8 zstore.
  do 10 zstep.
  unfold ossl_method_store_new_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s1_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115496) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 4) (Z_to_bv 64 96) (Z_to_bv 64 308352) (Z_to_bv 64 295) b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 4) s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
            F1 (Z_to_bv 64 2102656) fc1 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s1_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 : word) (v1 : Z) (F1 : bvmap 5 word) (fc1 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v1 [CB 24 (repeat (Z_to_bv 8 0) 24)] ->
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s1_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_1 u1_1 u2_1 sp s1 (Z_to_bv 64 v1) b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1)
        F1 (Z_to_bv 64 0x204770) fc1 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP FR G1 Hv1 UT HBr1 ACCr1 PALr1 HIr1 TOPr1 STKr1 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  do 7 zstep.
  unfold ossl_method_store_new_s1_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s2_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115516) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
            F2 (Z_to_bv 64 2148348) fc2 None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [CB 384 (repeat (Z_to_bv 8 0) 384)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s2_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 : word) (v1 v2 : Z) (F2 : bvmap 5 word) (fc2 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m v2 [CB 384 (repeat (Z_to_bv 8 0) 384)] ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s2_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra2 u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 lo m)
    (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 a0 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 4) s6 s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2)
        F2 (Z_to_bv 64 0x2047a8) fc2 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 FR G1 Hv1 Hv2 UT HBr2 ACCr2 PALr2 HIr2 TOPr2 STKr2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep. wg_F.
  do 4 zstep.
  unfold ossl_method_store_new_s2_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s3_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115544) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 0) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
            F3 (Z_to_bv 64 2055740) fc3 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s3_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 : word) (v1 v2 v3 : Z) (F3 : bvmap 5 word) (fc3 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [CB 384 (repeat (Z_to_bv 8 0) 384)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v3) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s3_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra3 u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 F3 fc3 lo m)
    (MS (mkR ra3 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3)
        F3 (Z_to_bv 64 0x2047bc) fc3 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR3_4 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR3_4.
  zstep.
  unfold ossl_method_store_new_s3_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s4_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v3 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115576) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) (Z_to_bv 64 (v2 + 80)) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
            F4 (Z_to_bv 64 2055740) fc4 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s4_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 : word) (v1 v2 v3 v4 : Z) (F4 : bvmap 5 word) (fc4 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v4) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s4_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra4 u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v3 v4 F4 fc4 lo m)
    (MS (mkR ra4 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4)
        F4 (Z_to_bv 64 0x2047d8) fc4 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR4_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR4_2.
  zstep.
  unfold ossl_method_store_new_s4_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s5_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v3 v4 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115516) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 (v2 + 88)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
            F5 (Z_to_bv 64 2148348) fc5 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s5_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 : word) (v1 v2 v3 v4 v5 : Z) (F5 : bvmap 5 word) (fc5 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v5) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s5_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra5 u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v3 v4 v5 F5 fc5 lo m)
    (MS (mkR ra5 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5)
        F5 (Z_to_bv 64 0x2047f8) fc5 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR5_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR5_2.
  do 3 zstep.
  zstep. wg_T.
  zstep.
  unfold ossl_method_store_new_s5_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s6_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v3 v4 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115544) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
            F6 (Z_to_bv 64 2055740) fc6 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s6_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 : word) (v1 v2 v3 v4 v5 v6 : Z) (F6 : bvmap 5 word) (fc6 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v6) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s6_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra6 u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v3 v4 v5 v6 F6 fc6 lo m)
    (MS (mkR ra6 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6)
        F6 (Z_to_bv 64 0x2047bc) fc6 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR6_4 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR6_4.
  zstep.
  unfold ossl_method_store_new_s6_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s7_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v3 v4 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115576) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 (v2 + 176)) (Z_to_bv 64 0) b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
            F7 (Z_to_bv 64 2055740) fc7 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s7_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 : word) (v1 v2 v3 v4 v5 v6 v7 : Z) (F7 : bvmap 5 word) (fc7 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v7) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s7_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra7 u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v3 v4 v5 v6 v7 F7 fc7 lo m)
    (MS (mkR ra7 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7)
        F7 (Z_to_bv 64 0x2047d8) fc7 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR7_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR7_2.
  zstep.
  unfold ossl_method_store_new_s7_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s8_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v2 v3 v4 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115516) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) (Z_to_bv 64 (v2 + 184)) (Z_to_bv 64 0) b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
            F8 (Z_to_bv 64 2148348) fc8 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s8_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 : word) (v1 v2 v3 v4 v5 v6 v7 v8 : Z) (F8 : bvmap 5 word) (fc8 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v8) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s8_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra8 u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v3 v4 v5 v6 v7 v8 F8 fc8 lo m)
    (MS (mkR ra8 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8)
        F8 (Z_to_bv 64 0x2047f8) fc8 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR8_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR8_2.
  do 3 zstep.
  zstep. wg_T.
  zstep.
  unfold ossl_method_store_new_s8_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s9_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115544) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) (Z_to_bv 64 0) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
            F9 (Z_to_bv 64 2055740) fc9 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s9_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 : Z) (F9 : bvmap 5 word) (fc9 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v9) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s9_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra9 u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v3 v4 v5 v6 v7 v8 v9 F9 fc9 lo m)
    (MS (mkR ra9 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9)
        F9 (Z_to_bv 64 0x2047bc) fc9 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR9_4 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR9_4.
  zstep.
  unfold ossl_method_store_new_s9_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s10_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115576) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 (v2 + 272)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
            F10 (Z_to_bv 64 2055740) fc10 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s10_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Z) (F10 : bvmap 5 word) (fc10 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
  0 <= v3 < 2 ^ 64 ->
  0 <= v4 < 2 ^ 64 ->
  0 <= v5 < 2 ^ 64 ->
  0 <= v6 < 2 ^ 64 ->
  0 <= v7 < 2 ^ 64 ->
  0 <= v8 < 2 ^ 64 ->
  0 <= v9 < 2 ^ 64 ->
  0 <= v10 < 2 ^ 64 ->
  img_untouched m ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v10) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s10_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra10 u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 F10 fc10 lo m)
    (MS (mkR ra10 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10)
        F10 (Z_to_bv 64 0x2047d8) fc10 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR10_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR10_2.
  zstep.
  unfold ossl_method_store_new_s10_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s11_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115516) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 (v2 + 280)) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
            F11 (Z_to_bv 64 2148348) fc11 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s11_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Z) (F11 : bvmap 5 word) (fc11 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
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
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v11) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s11_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra11 u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F11 fc11 lo m)
    (MS (mkR ra11 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11)
        F11 (Z_to_bv 64 0x2047f8) fc11 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR11_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR11_2.
  do 3 zstep.
  zstep. wg_T.
  zstep.
  unfold ossl_method_store_new_s11_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s12_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (F12 : bvmap 5 word) (fc12 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115544) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) (Z_to_bv 64 0) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
            F12 (Z_to_bv 64 2055740) fc12 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s12_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Z) (F12 : bvmap 5 word) (fc12 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
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
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v12) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s12_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra12 u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 F12 fc12 lo m)
    (MS (mkR ra12 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12)
        F12 (Z_to_bv 64 0x2047bc) fc12 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR12_4 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 3 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR12_4.
  zstep.
  unfold ossl_method_store_new_s12_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s13_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (F13 : bvmap 5 word) (fc13 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115576) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) (Z_to_bv 64 (v2 + 368)) (Z_to_bv 64 0) b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
            F13 (Z_to_bv 64 2055740) fc13 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s13_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Z) (F13 : bvmap 5 word) (fc13 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
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
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v13) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s13_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra13 u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 F13 fc13 lo m)
    (MS (mkR ra13 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13)
        F13 (Z_to_bv 64 0x2047d8) fc13 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 UT ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR13_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR13_2.
  zstep.
  unfold ossl_method_store_new_s13_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s14_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (F14 : bvmap 5 word) (fc14 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 2115648) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 384)) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (v2 + 472)) s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
            F14 (Z_to_bv 64 2055740) fc14 None m' (seg_rom asegs)
    /\ munch [(v2, v2 + 384); (v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp + -64).

Lemma ossl_method_store_new_s14_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Z) (F14 : bvmap 5 word) (fc14 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
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
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  acc asegs m v2 384 ->
  v2 mod 8 = 0 ->
  0x10007fff8000 <= v2 ->
  v2 + 384 <= 2 ^ 47 ->
  v2 + 384 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v14) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s14_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra14 u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 F14 fc14 lo m)
    (MS (mkR ra14 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1) (Z_to_bv 64 v14) b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14)
        F14 (Z_to_bv 64 0x2047f8) fc14 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr2 HBr1 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 ACCr2 PALr2 HIr2 TOPr2 STKr2 APTr2_r1 BR14_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v2, v2 + 384); (v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR14_2.
  do 3 zstep.
  zstep. wg_F.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep.
  unfold ossl_method_store_new_s14_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

(* [comment removed for export] *)
Definition ossl_method_store_new_s15_post (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (F15 : bvmap 5 word) (fc15 : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp u0_15 u1_15 u2_15 s0 s1 (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 16)) (Z_to_bv 64 0) b3_15 b4_15 b5_15 b6_15 b7_15 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
            F15 (ret_pc ra) fc15 None m' (seg_rom asegs)
    /\ munch [(v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' v1 [C8 a0; C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v15)]
    /\ rw_cells asegs m' v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma ossl_method_store_new_s15_walk : forall (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 : word) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Z) (F15 : bvmap 5 word) (fc15 : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp + -64) -> lo <= (bv_unsigned sp + -64) -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  rw_cells asegs m v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells asegs m 6736696 [C8 (Z_to_bv 64 2147450880)] ->
  0 <= v1 < 2 ^ 64 ->
  0 <= v2 < 2 ^ 64 ->
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
  acc asegs m v1 24 ->
  v1 mod 8 = 0 ->
  0x10007fff8000 <= v1 ->
  v1 + 24 <= 2 ^ 47 ->
  v1 + 24 <= lo ->
  v2 + 384 <= v1 \/ v1 + 24 <= v2 ->
  (bv_eqb (Z_to_bv 64 v15) (Z_to_bv 64 0)) = false ->
  mem_inv asegs m ->
  evt asegs (ossl_method_store_new_s15_post ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra15 u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 F15 fc15 lo m)
    (MS (mkR ra15 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0_15 u1_15 u2_15 sp (Z_to_bv 64 v1) (Z_to_bv 64 v15) b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 384)) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (v2 + 472)) s7 s8 s9 s10 s11 u3_15 u4_15 u5_15 u6_15)
        F15 (Z_to_bv 64 0x204840) fc15 None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP HBr1 HBr2 FR G1 Hv1 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 Hv8 Hv9 Hv10 Hv11 Hv12 Hv13 Hv14 Hv15 UT ACCr1 PALr1 HIr1 TOPr1 STKr1 APTr2_r1 BR15_2 MI. unfold SEGTOP_A in *. wp_box_aps.
  pose proof (munch_refl [(v1, v1 + 24); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  do 4 zstep.
  zstep. wg_F.
  zstore.
  zstep. wg_raw BR15_2.
  do 12 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold ossl_method_store_new_s15_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section ossl_method_store_new_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CRYPTO_zalloc : crypto_zalloc_env_stmt RT.
Hypothesis C_CRYPTO_calloc : CRYPTO_calloc_stmt RT.
Hypothesis C_ossl_sa_new : ossl_sa_new_stmt RT.
Hypothesis C_lock_new : crypto_lock_new_env_stmt RT.

Definition ossl_method_store_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x250 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ossl_method_store_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_ossl_method_store_new_1, e_ossl_method_store_new); (SITE_ossl_method_store_new_2, e_ossl_method_store_new); (SITE_ossl_method_store_new_3, e_ossl_method_store_new); (SITE_ossl_method_store_new_4, e_ossl_method_store_new); (SITE_ossl_method_store_new_5, e_ossl_method_store_new); (SITE_ossl_method_store_new_6, e_ossl_method_store_new); (SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc); (SITE_ln_zalloc, e_lock_new)]
                      [(SITE_ossl_method_store_new_1, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_2, e_CRYPTO_calloc); (SITE_ossl_method_store_new_2, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_3, e_ossl_sa_new); (SITE_ossl_method_store_new_3, e_CRYPTO_zalloc); (SITE_ossl_method_store_new_4, e_lock_new); (SITE_ossl_method_store_new_5, e_lock_new); (SITE_ossl_method_store_new_6, e_lock_new); (SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc); (SITE_ln_zalloc, e_CRYPTO_zalloc)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat ->
  Z.of_nat (length (rt_live RT Σ)) + 15 <= LIVE_MAX -> mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1 <= rt_credit RT Σ ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ossl_method_store_new m)))
    (fun c => exists (Σ' : rts RT) (q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q1) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(G_ALLOW_CUST, G_ALLOW_CUST + 1)] m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ wr_at asegs m' q1 24
           /\ acc asegs m' q1 24
           /\ wr_at asegs m' q2 384
           /\ acc asegs m' q2 384
           /\ wr_at asegs m' q3 32
           /\ acc asegs m' q3 32
           /\ wr_at asegs m' q4 40
           /\ acc asegs m' q4 40
           /\ wr_at asegs m' q5 40
           /\ acc asegs m' q5 40
           /\ wr_at asegs m' q6 32
           /\ acc asegs m' q6 32
           /\ wr_at asegs m' q7 40
           /\ acc asegs m' q7 40
           /\ wr_at asegs m' q8 40
           /\ acc asegs m' q8 40
           /\ wr_at asegs m' q9 32
           /\ acc asegs m' q9 32
           /\ wr_at asegs m' q10 40
           /\ acc asegs m' q10 40
           /\ wr_at asegs m' q11 40
           /\ acc asegs m' q11 40
           /\ wr_at asegs m' q12 32
           /\ acc asegs m' q12 32
           /\ wr_at asegs m' q13 40
           /\ acc asegs m' q13 40
           /\ wr_at asegs m' q14 40
           /\ acc asegs m' q14 40
           /\ wr_at asegs m' q15 40
           /\ acc asegs m' q15 40
           /\ rw_cells asegs m' q1 [C8 a0; C8 (Z_to_bv 64 q2); C8 (Z_to_bv 64 q15)]
           /\ rw_cells asegs m' q2 [C8 (Z_to_bv 64 q3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 q4); C8 (Z_to_bv 64 q5); C8 (Z_to_bv 64 q6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 q7); C8 (Z_to_bv 64 q8); C8 (Z_to_bv 64 q9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 q10); C8 (Z_to_bv 64 q11); C8 (Z_to_bv 64 q12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 q13); C8 (Z_to_bv 64 q14)]
           /\ rw_cells asegs m' q3 [CB 32 (repeat (Z_to_bv 8 0) 32)]
           /\ rw_cells asegs m' q4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q6 [CB 32 (repeat (Z_to_bv 8 0) 32)]
           /\ rw_cells asegs m' q7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q9 [CB 32 (repeat (Z_to_bv 8 0) 32)]
           /\ rw_cells asegs m' q10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q12 [CB 32 (repeat (Z_to_bv 8 0) 32)]
           /\ rw_cells asegs m' q13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q14 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' q15 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q15, 40) :: (q14, 40) :: (q13, 40) :: (q12, 32) :: (q11, 40) :: (q10, 40) :: (q9, 32) :: (q8, 40) :: (q7, 40) :: (q6, 32) :: (q5, 40) :: (q4, 40) :: (q3, 32) :: (q2, 384) :: (q1, 24) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - (mcost 24 + mcost 384 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + mcost 32 + 1 + 1 + 1) /\ 0 < q1 /\ q1 mod 16 = 0 /\ q1 + 24 < USTACK_TOP /\ 0 < q2 /\ q2 mod 16 = 0 /\ q2 + 384 < USTACK_TOP /\ 0 < q3 /\ q3 mod 16 = 0 /\ q3 + 32 < USTACK_TOP /\ 0 < q4 /\ q4 mod 16 = 0 /\ q4 + 40 < USTACK_TOP /\ 0 < q5 /\ q5 mod 16 = 0 /\ q5 + 40 < USTACK_TOP /\ 0 < q6 /\ q6 mod 16 = 0 /\ q6 + 32 < USTACK_TOP /\ 0 < q7 /\ q7 mod 16 = 0 /\ q7 + 40 < USTACK_TOP /\ 0 < q8 /\ q8 mod 16 = 0 /\ q8 + 40 < USTACK_TOP /\ 0 < q9 /\ q9 mod 16 = 0 /\ q9 + 32 < USTACK_TOP /\ 0 < q10 /\ q10 mod 16 = 0 /\ q10 + 40 < USTACK_TOP /\ 0 < q11 /\ q11 mod 16 = 0 /\ q11 + 40 < USTACK_TOP /\ 0 < q12 /\ q12 mod 16 = 0 /\ q12 + 32 < USTACK_TOP /\ 0 < q13 /\ q13 mod 16 = 0 /\ q13 + 40 < USTACK_TOP /\ 0 < q14 /\ q14 mod 16 = 0 /\ q14 + 40 < USTACK_TOP /\ 0 < q15 /\ q15 mod 16 = 0 /\ q15 + 40 < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem ossl_method_store_new_cps : ossl_method_store_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr ENV.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 64 /\ 0x10007fff8000 < usp - 64 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-64) EU1.
  assert (WHLO : lo <= usp - 64) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (wg_mcost_nonneg 24) as MC_24.
  pose proof (wg_mcost_nonneg 32) as MC_32.
  pose proof (wg_mcost_nonneg 384) as MC_384.
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST WHLO WHIMG WHTOP UT SHC MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, ST1, Hc1', H1_0.
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 64 [] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(cl_fp_lia)) as ENV1.
  assert (AGs1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply MU1; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AGs1) as UWF1.
  destruct (cl_chain_call (rt_cg RT Σ) e_ossl_method_store_new e_CRYPTO_zalloc SITE_ossl_method_store_new_1 m1 m1 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTX
              (proj1 CGH (SITE_ossl_method_store_new_1, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH (SITE_ossl_method_store_new_1, e_CRYPTO_zalloc) ltac:(wp_in_lit)) UWF1 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H1_0))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_CRYPTO_zalloc Σ PMc (Z_to_bv 64 SITE_ossl_method_store_new_1) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 24) (Z_to_bv 64 308352) (Z_to_bv 64 328) a3 a4 a5 a6 a7 a0 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 24 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ltac:(lia) ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_1) by (unfold SITE_ossl_method_store_new_1; lia). exact CTXc1. }
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
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ossl_method_store_new_1) in Hc2' by (unfold SITE_ossl_method_store_new_1; clear; first [reflexivity | lia]).
  assert (AGc2 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu2 : agree_on (fun x => usp <= x < USTACK_TOP) m1 m2) by (intros a Ha; exact (AGc2 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m1 m2 sp s0 UWF1 AGu2) as UWF2.
  cl_keep H1_0 AGc2 WM2 KF1.
  pose proof SP2 as SPc2. pose proof CG2 as CGc2.
  assert (LOW2 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SPc2; exact LOW).
  assert (LEN2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by (rewrite LV2; cbn [length]; lia).
  assert (LENc2 : Z.of_nat (length (rt_live RT Σ1)) = Z.of_nat (length (rt_live RT Σ)) + 1) by lia. wp_box1 CR2.
  assert (Hfr2 : (length (rt_frames RT Σ1) < FRAMES_MAX)%nat) by (rewrite FRS2; exact Hfr).
  assert (CTXb2 : cg_ctx (rt_cg RT Σ1) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc2; exact CTX).
  assert (CGH2 : cg_has (rt_cg RT Σ1) _ _) by (rewrite CGc2; exact CGH).
  assert (INP_v1_2 : In (v1, 24) (rt_live RT Σ1)) by (rewrite LV2; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 v1 24 ART2 INP_v1_2) as (_ & PHI_v1 & _). rewrite SPc2 in PHI_v1.
  pose proof (afp_live_mem RT GOBJ AFP Σ1 m2 v1 24 ART2 INP_v1_2 ltac:(lia)) as (_ & PT_v1).
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 v1 24 ART2 INP_v1_2 ltac:(lia)) as PHH_v1.
  pose proof (wg_mod16_8 _ P16_v1) as PAL_v1. assert (PR64_v1 : 0 <= v1 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v1 : v1 + 24 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v1. wp_box1 PAL_v1. wp_box1 PR64_v1.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (af_acc_live RT AF Σ1 m2 v1 24 ART2 INP_v1_2) as (WR_v1_3 & ACC_v1_3).
  pose proof (wp_cells_congr asegs m2 v1 [CB (Z.to_nat 24) (repeat (Z_to_bv 8 0) (Z.to_nat 24))] [CB 24 (repeat (Z_to_bv 8 0) 24)] ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m2 v1 24 G1_ZER WR_v1_3 ltac:(lia))) as HB_v1_3.
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s1_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_1) u0_1 u1_1 u2_1 b1_1 b2_1 b3_1 b4_1 b5_1 b6_1 b7_1 u3_1 u4_1 u5_1 u6_1 v1 F1 fc1 m2 lo
                ST2 WHLO WHIMG WHTOP KF1 SHC2 PR64_v1 UT2 HB_v1_3 ACC_v1_3 PAL_v1 PHH_v1 PT_v1 PSTK_v1 MI2) as W3.
  cl_lift W3 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & H3_0 & H3_1 & H3_2 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3', H3_1.
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 64 [(v1, v1 + 24)] ART2 ltac:(rewrite SPc2; lia) ltac:(lia) MU3); [|exact WM3].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 24; split; [exact INP_v1_2 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m2 m3 _ canary G1_ENVp MU3 ltac:(cl_fp_lia)) as ENV3.
  assert (AGs3 : agree_on (fun x => usp <= x < USTACK_TOP) m2 m3) by (intros a Ha; apply MU3; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m2 m3 sp s0 UWF2 AGs3) as UWF3.
  destruct (cl_chain_call (rt_cg RT Σ1) e_ossl_method_store_new e_CRYPTO_calloc SITE_ossl_method_store_new_2 m3 m3 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb2
              (proj1 CGH2 (SITE_ossl_method_store_new_2, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH2 (SITE_ossl_method_store_new_2, e_CRYPTO_calloc) ltac:(wp_in_lit)) UWF3 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m3 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H3_1))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc3 & UWCc3).
  (* [comment removed for export] *)
  apply (C_CRYPTO_calloc Σ1 PMc (Z_to_bv 64 SITE_ossl_method_store_new_2) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_1 u1_1 u2_1 sp (Z_to_bv 64 v1) (Z_to_bv 64 4) (Z_to_bv 64 96) (Z_to_bv 64 308352) (Z_to_bv 64 295) b4_1 b5_1 b6_1 b7_1 a0 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 4) s6 s7 s8 s9 s10 s11 u3_1 u4_1 u5_1 u6_1
           F1 fc1 m3 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ltac:(rewrite ?unsigned_lit by lia; lia) ltac:(vm_compute; reflexivity) ART3 MI3).
  { fold usp in SPA. cl_call_ok EU1 ST3 LOW2 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_2) by (unfold SITE_ossl_method_store_new_2; lia). exact CTXc3. }
  { exact UWCc3. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_2) by (unfold SITE_ossl_method_store_new_2; lia). apply (proj2 CGH2). wp_in_lit. }
  { apply (cg_has_weaken _ _ _ _ _ CGH2); vm_compute; reflexivity. }
  { lia. }
  { rewrite ?(unsigned_lit 4), ?(unsigned_lit 96) by lia. change (4 * 96) with 384. (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & v2 & Hc4 & LV4 & FRS4 & SP4 & CR4 & P0_v2 & P16_v2 & PU_v2 & CG4).
  wp_box1 PU_v2.
  rewrite ?(unsigned_lit 4), ?(unsigned_lit 96) in LV4, CR4, PU_v2, Hc4 by lia. change (4 * 96) with 384 in LV4, CR4, PU_v2, Hc4.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & G2_ENVp & G2_WR & G2_ACC & G2_ZER) & Hc4'). clear Hc4.
  destruct RS4 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & F2 & fc2 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_ossl_method_store_new_2) in Hc4' by (unfold SITE_ossl_method_store_new_2; clear; first [reflexivity | lia]).
  assert (AGc4 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m3 m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES4; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu4 : agree_on (fun x => usp <= x < USTACK_TOP) m3 m4) by (intros a Ha; exact (AGc4 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m3 m4 sp s0 UWF3 AGu4) as UWF4.
  assert (KF3 : rw_cells asegs m4 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m3 m4 v1 24 _ _ H3_0 PRES4 WM4 INP_v1_2); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H3_1 AGc4 WM4 KF4.
  assert (SPc4 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (rewrite SP4; exact SPc2).
  assert (CGc4 : rt_cg RT Σ2 = rt_cg RT Σ) by (rewrite CG4; exact CGc2).
  assert (LOW4 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SPc4; exact LOW).
  assert (LEN4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ1)) + 1) by (rewrite LV4; cbn [length]; lia).
  assert (LENc4 : Z.of_nat (length (rt_live RT Σ2)) = Z.of_nat (length (rt_live RT Σ)) + 2) by lia. clear LENc2. wp_box1 LEN2. wp_box1 CR4.
  assert (Hfr4 : (length (rt_frames RT Σ2) < FRAMES_MAX)%nat) by (rewrite FRS4; exact Hfr2).
  assert (CTXb4 : cg_ctx (rt_cg RT Σ2) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc4; exact CTX).
  assert (CGH4 : cg_has (rt_cg RT Σ2) _ _) by (rewrite CGc4; exact CGH).
  assert (INP_v1_4 : In (v1, 24) (rt_live RT Σ2)) by (rewrite LV4; do 1 right; exact INP_v1_2).
  assert (INP_v2_4 : In (v2, 384) (rt_live RT Σ2)) by (rewrite LV4; left; reflexivity).
  pose proof (af_live_range RT AF Σ2 m4 v2 384 ART4 INP_v2_4) as (_ & PHI_v2 & _). rewrite SPc4 in PHI_v2.
  pose proof (afp_live_mem RT GOBJ AFP Σ2 m4 v2 384 ART4 INP_v2_4 ltac:(lia)) as (_ & PT_v2).
  pose proof (afp_live_hi RT GOBJ AFP Σ2 m4 v2 384 ART4 INP_v2_4 ltac:(lia)) as PHH_v2.
  pose proof (wg_mod16_8 _ P16_v2) as PAL_v2. assert (PR64_v2 : 0 <= v2 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v2 : v2 + 384 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v2. wp_box1 PAL_v2. wp_box1 PR64_v2.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (af_acc_live RT AF Σ2 m4 v2 384 ART4 INP_v2_4) as (WR_v2_5 & ACC_v2_5).
  pose proof (wp_cells_congr asegs m4 v2 [CB (Z.to_nat 384) (repeat (Z_to_bv 8 0) (Z.to_nat 384))] [CB 384 (repeat (Z_to_bv 8 0) 384)] ltac:(reflexivity) ltac:(reflexivity) ltac:(cbn; repeat first [exact I | reflexivity | split]) (wp_zero_rw_CB asegs m4 v2 384 G2_ZER WR_v2_5 ltac:(lia))) as HB_v2_5.
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s2_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_2) u0_2 u1_2 u2_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 u3_2 u4_2 u5_2 u6_2 v1 v2 F2 fc2 m4 lo
                ST4 WHLO WHIMG WHTOP KF3 KF4 SHC4 PR64_v1 PR64_v2 UT4 HB_v2_5 ACC_v2_5 PAL_v2 PHH_v2 PT_v2 PSTK_v2 MI4) as W5.
  cl_lift W5 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & H5_0 & H5_1 & H5_2 & H5_3 & ST5) & Hc5'). clear Hc5.
  fold usp in MU5, ST5, Hc5', H5_2.
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 64 [] ART4 ltac:(rewrite SPc4; lia) ltac:(lia) MU5); [|exact WM5].
    intros x Hx. exfalso; apply Hx; exact I. }
  pose proof (cl_env_seg _ m4 m5 _ canary G2_ENVp MU5 ltac:(cl_fp_lia)) as ENV5.
  assert (AGs5 : agree_on (fun x => usp <= x < USTACK_TOP) m4 m5) by (intros a Ha; apply MU5; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m4 m5 sp s0 UWF4 AGs5) as UWF5.
  destruct (cl_chain_call (rt_cg RT Σ2) e_ossl_method_store_new e_ossl_sa_new SITE_ossl_method_store_new_3 m5 m5 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb4
              (proj1 CGH4 (SITE_ossl_method_store_new_3, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH4 (SITE_ossl_method_store_new_3, e_ossl_sa_new) ltac:(wp_in_lit)) UWF5 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m5 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H5_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc5 & UWCc5).
  (* [comment removed for export] *)
  apply (C_ossl_sa_new Σ2 PMc (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_2 u1_2 u2_2 sp (Z_to_bv 64 v1) (Z_to_bv 64 v2) b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b7_2 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_2 u4_2 u5_2 u6_2
           F2 fc2 m5 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART5 MI5).
  { fold usp in SPA. cl_call_ok EU1 ST5 LOW4 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). exact CTXc5. }
  { exact UWCc5. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). apply (proj2 CGH4). wp_in_lit. }
  { apply (cg_has_weaken _ _ _ _ _ CGH4); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV5. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & v3 & Hc6 & LV6 & FRS6 & SP6 & CR6 & P0_v3 & P16_v3 & PU_v3 & CG6).
  wp_box1 PU_v3.
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & G3_ENVp & G3_WR & G3_ACC & G3_ZER) & Hc6'). clear Hc6.
  destruct RS6 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & F3 & fc3 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_ossl_method_store_new_3) in Hc6' by (unfold SITE_ossl_method_store_new_3; clear; first [reflexivity | lia]).
  assert (AGc6 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m5 m6).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES6; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu6 : agree_on (fun x => usp <= x < USTACK_TOP) m5 m6) by (intros a Ha; exact (AGc6 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m5 m6 sp s0 UWF5 AGu6) as UWF6.
  assert (KF6 : rw_cells asegs m6 v2 [CB 384 (repeat (Z_to_bv 8 0) 384)]) by (apply (wg_keep_live _ _ _ _ m5 m6 v2 384 _ _ H5_0 PRES6 WM6 INP_v2_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF7 : rw_cells asegs m6 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m5 m6 v1 24 _ _ H5_1 PRES6 WM6 INP_v1_4); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H5_2 AGc6 WM6 KF8.
  assert (SPc6 : rt_sp0 RT Σ3 = rt_sp0 RT Σ) by (rewrite SP6; exact SPc4).
  assert (CGc6 : rt_cg RT Σ3 = rt_cg RT Σ) by (rewrite CG6; exact CGc4).
  assert (LOW6 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SPc6; exact LOW).
  assert (LEN6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ2)) + 1) by (rewrite LV6; cbn [length]; lia).
  assert (LENc6 : Z.of_nat (length (rt_live RT Σ3)) = Z.of_nat (length (rt_live RT Σ)) + 3) by lia. clear LENc4. wp_box1 LEN4. wp_box1 CR6.
  assert (Hfr6 : (length (rt_frames RT Σ3) < FRAMES_MAX)%nat) by (rewrite FRS6; exact Hfr4).
  assert (CTXb6 : cg_ctx (rt_cg RT Σ3) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc6; exact CTX).
  assert (CGH6 : cg_has (rt_cg RT Σ3) _ _) by (rewrite CGc6; exact CGH).
  assert (INP_v1_6 : In (v1, 24) (rt_live RT Σ3)) by (rewrite LV6; do 1 right; exact INP_v1_4).
  assert (INP_v2_6 : In (v2, 384) (rt_live RT Σ3)) by (rewrite LV6; do 1 right; exact INP_v2_4).
  assert (INP_v3_6 : In (v3, 32) (rt_live RT Σ3)) by (rewrite LV6; left; reflexivity).
  pose proof (af_live_range RT AF Σ3 m6 v3 32 ART6 INP_v3_6) as (_ & PHI_v3 & _). rewrite SPc6 in PHI_v3.
  pose proof (afp_live_mem RT GOBJ AFP Σ3 m6 v3 32 ART6 INP_v3_6 ltac:(lia)) as (_ & PT_v3).
  pose proof (afp_live_hi RT GOBJ AFP Σ3 m6 v3 32 ART6 INP_v3_6 ltac:(lia)) as PHH_v3.
  pose proof (wg_mod16_8 _ P16_v3) as PAL_v3. assert (PR64_v3 : 0 <= v3 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v3 : v3 + 32 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v3. wp_box1 PAL_v3. wp_box1 PR64_v3.
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & SHC6 & _ & _ & UT6).
  pose proof (af_acc_live RT AF Σ3 m6 v3 32 ART6 INP_v3_6) as (WR_v3_6 & ACC_v3_6).
  pose proof (wp_zero_rw_CB asegs m6 v3 32 G3_ZER WR_v3_6 ltac:(lia)) as HBZ_v3_6. change (Z.to_nat 32) with 32%nat in HBZ_v3_6.
  pose proof (af_acc_live RT AF Σ3 m6 v2 384 ART6 INP_v2_6) as (WR_v2_7 & ACC_v2_7).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_3) u0_3 u1_3 u2_3 b1_3 b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 u3_3 u4_3 u5_3 u6_3 v1 v2 v3 F3 fc3 m6 lo
                ST6 WHLO WHIMG WHTOP KF6 KF7 KF8 SHC6 PR64_v1 PR64_v2 PR64_v3 UT6 ACC_v2_7 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI6) as W7.
  cl_lift W7 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & H7_0 & H7_1 & H7_2 & H7_3 & ST7) & Hc7'). clear Hc7.
  fold usp in MU7, ST7, Hc7', H7_2.
  assert (ART7 : ART RT Σ3 m7).
  { apply (wg_seg_ART RT AF Σ3 m6 m7 usp 64 [(v2, v2 + 384)] ART6 ltac:(rewrite SPc6; lia) ltac:(lia) MU7); [|exact WM7].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_6 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF10 : rw_cells asegs m7 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m6 m7 _ _ HBZ_v3_6 MU7 WM7); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m6 m7 _ canary G3_ENVp MU7 ltac:(cl_fp_lia)) as ENV7.
  assert (AGs7 : agree_on (fun x => usp <= x < USTACK_TOP) m6 m7) by (intros a Ha; apply MU7; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m6 m7 sp s0 UWF6 AGs7) as UWF7.
  destruct (cl_chain_call (rt_cg RT Σ3) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_4 m7 m7 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb6
              (proj1 CGH6 (SITE_ossl_method_store_new_4, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH6 (SITE_ossl_method_store_new_4, e_lock_new) ltac:(wp_in_lit)) UWF7 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m7 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H7_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc7 & UWCc7).
  (* [comment removed for export] *)
  apply (C_lock_new Σ3 PMc (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_3 u1_3 u2_3 sp (Z_to_bv 64 v1) (Z_to_bv 64 v3) (Z_to_bv 64 0) b2_3 b3_3 b4_3 b5_3 b6_3 b7_3 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_3 u4_3 u5_3 u6_3
           F3 fc3 m7 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART7 MI7).
  { fold usp in SPA. cl_call_ok EU1 ST7 LOW6 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_4) by (unfold SITE_ossl_method_store_new_4; lia). exact CTXc7. }
  { exact UWCc7. }
  { apply (cg_has_weaken _ _ _ _ _ CGH6); vm_compute; reflexivity. }
  { exact Hfr6. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV7. }
  { exact Hc7'. }
  clear Hc7'. intros c8 (Σ4 & v4 & Hc8 & LV8 & FRS8 & SP8 & CR8 & P0_v4 & P16_v4 & PU_v4 & CG8).
  wp_box1 PU_v4.
  destruct (ASTA_unpack RT Σ4 _ _ c8 Hc8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & G4_ENVp & G4_MX & G4_ACC) & Hc8'). clear Hc8.
  destruct RS8 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & F4 & fc4 & ->).
  rewrite EU1 in ST8, PRES8. rewrite (ret_pc_even SITE_ossl_method_store_new_4) in Hc8' by (unfold SITE_ossl_method_store_new_4; clear; first [reflexivity | lia]).
  assert (AGc8 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m7 m8).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES8; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu8 : agree_on (fun x => usp <= x < USTACK_TOP) m7 m8) by (intros a Ha; exact (AGc8 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m7 m8 sp s0 UWF7 AGu8) as UWF8.
  assert (KF11 : rw_cells asegs m8 v2 [C8 (Z_to_bv 64 v3); CB 376 (repeat (Z_to_bv 8 0) 376)]) by (apply (wg_keep_live _ _ _ _ m7 m8 v2 384 _ _ H7_0 PRES8 WM8 INP_v2_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF12 : rw_cells asegs m8 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m7 m8 v1 24 _ _ H7_1 PRES8 WM8 INP_v1_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H7_2 AGc8 WM8 KF13.
  assert (KF15 : rw_cells asegs m8 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m7 m8 v3 32 _ _ KF10 PRES8 WM8 INP_v3_6); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc8 : rt_sp0 RT Σ4 = rt_sp0 RT Σ) by (rewrite SP8; exact SPc6).
  assert (CGc8 : rt_cg RT Σ4 = rt_cg RT Σ) by (rewrite CG8; exact CGc6).
  assert (LOW8 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SPc8; exact LOW).
  assert (LEN8 : Z.of_nat (length (rt_live RT Σ4)) = Z.of_nat (length (rt_live RT Σ3)) + 1) by (rewrite LV8; cbn [length]; lia).
  assert (LENc8 : Z.of_nat (length (rt_live RT Σ4)) = Z.of_nat (length (rt_live RT Σ)) + 4) by lia. clear LENc6. wp_box1 LEN6. wp_box1 CR8.
  assert (Hfr8 : (length (rt_frames RT Σ4) < FRAMES_MAX)%nat) by (rewrite FRS8; exact Hfr6).
  assert (CTXb8 : cg_ctx (rt_cg RT Σ4) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc8; exact CTX).
  assert (CGH8 : cg_has (rt_cg RT Σ4) _ _) by (rewrite CGc8; exact CGH).
  assert (INP_v1_8 : In (v1, 24) (rt_live RT Σ4)) by (rewrite LV8; do 1 right; exact INP_v1_6).
  assert (INP_v2_8 : In (v2, 384) (rt_live RT Σ4)) by (rewrite LV8; do 1 right; exact INP_v2_6).
  assert (INP_v3_8 : In (v3, 32) (rt_live RT Σ4)) by (rewrite LV8; do 1 right; exact INP_v3_6).
  assert (INP_v4_8 : In (v4, 40) (rt_live RT Σ4)) by (rewrite LV8; left; reflexivity).
  pose proof (af_live_range RT AF Σ4 m8 v4 40 ART8 INP_v4_8) as (_ & PHI_v4 & _). rewrite SPc8 in PHI_v4.
  pose proof (afp_live_mem RT GOBJ AFP Σ4 m8 v4 40 ART8 INP_v4_8 ltac:(lia)) as (_ & PT_v4).
  pose proof (afp_live_hi RT GOBJ AFP Σ4 m8 v4 40 ART8 INP_v4_8 ltac:(lia)) as PHH_v4.
  pose proof (wg_mod16_8 _ P16_v4) as PAL_v4. assert (PR64_v4 : 0 <= v4 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v4 : v4 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v4. wp_box1 PAL_v4. wp_box1 PR64_v4.
  destruct (af_client_consts RT AF Σ4 m8 ART8) as (_ & SHC8 & _ & _ & UT8).
  pose proof (af_acc_live RT AF Σ4 m8 v2 384 ART8 INP_v2_8) as (WR_v2_9 & ACC_v2_9).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s4_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_4) u0_4 u1_4 u2_4 b1_4 b2_4 b3_4 b4_4 b5_4 b6_4 b7_4 u3_4 u4_4 u5_4 u6_4 v1 v2 v3 v4 F4 fc4 m8 lo
                ST8 WHLO WHIMG WHTOP KF11 KF12 KF13 SHC8 PR64_v1 PR64_v2 PR64_v3 PR64_v4 UT8 ACC_v2_9 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI8) as W9.
  cl_lift W9 Hc8' c9 Hc9.
  destruct (ASTA_unpack RT Σ4 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & H9_0 & H9_1 & H9_2 & H9_3 & ST9) & Hc9'). clear Hc9.
  fold usp in MU9, ST9, Hc9', H9_2.
  assert (ART9 : ART RT Σ4 m9).
  { apply (wg_seg_ART RT AF Σ4 m8 m9 usp 64 [(v2, v2 + 384)] ART8 ltac:(rewrite SPc8; lia) ltac:(lia) MU9); [|exact WM9].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_8 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF16 : rw_cells asegs m9 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m8 m9 _ _ KF15 MU9 WM9); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF17 : rw_cells asegs m9 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m8 m9 _ _ G4_MX MU9 WM9); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m8 m9 _ canary G4_ENVp MU9 ltac:(cl_fp_lia)) as ENV9.
  assert (AGs9 : agree_on (fun x => usp <= x < USTACK_TOP) m8 m9) by (intros a Ha; apply MU9; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m8 m9 sp s0 UWF8 AGs9) as UWF9.
  destruct (cl_chain_call (rt_cg RT Σ4) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_5 m9 m9 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb8
              (proj1 CGH8 (SITE_ossl_method_store_new_5, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH8 (SITE_ossl_method_store_new_5, e_lock_new) ltac:(wp_in_lit)) UWF9 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m9 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H9_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc9 & UWCc9).
  (* [comment removed for export] *)
  apply (C_lock_new Σ4 PMc (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_4 u1_4 u2_4 sp (Z_to_bv 64 v1) (Z_to_bv 64 v4) (Z_to_bv 64 (v2 + 80)) (Z_to_bv 64 0) b3_4 b4_4 b5_4 b6_4 b7_4 (Z_to_bv 64 v2) (Z_to_bv 64 v2) (Z_to_bv 64 2147450880) (Z_to_bv 64 4) (Z_to_bv 64 (v2 + 88)) s7 s8 s9 s10 s11 u3_4 u4_4 u5_4 u6_4
           F4 fc4 m9 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART9 MI9).
  { fold usp in SPA. cl_call_ok EU1 ST9 LOW8 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_5) by (unfold SITE_ossl_method_store_new_5; lia). exact CTXc9. }
  { exact UWCc9. }
  { apply (cg_has_weaken _ _ _ _ _ CGH8); vm_compute; reflexivity. }
  { exact Hfr8. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV9. }
  { exact Hc9'. }
  clear Hc9'. intros c10 (Σ5 & v5 & Hc10 & LV10 & FRS10 & SP10 & CR10 & P0_v5 & P16_v5 & PU_v5 & CG10).
  wp_box1 PU_v5.
  destruct (ASTA_unpack RT Σ5 _ _ c10 Hc10) as (ms10 & (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & G5_ENVp & G5_MX & G5_ACC) & Hc10'). clear Hc10.
  destruct RS10 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & F5 & fc5 & ->).
  rewrite EU1 in ST10, PRES10. rewrite (ret_pc_even SITE_ossl_method_store_new_5) in Hc10' by (unfold SITE_ossl_method_store_new_5; clear; first [reflexivity | lia]).
  assert (AGc10 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m9 m10).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES10; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu10 : agree_on (fun x => usp <= x < USTACK_TOP) m9 m10) by (intros a Ha; exact (AGc10 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m9 m10 sp s0 UWF9 AGu10) as UWF10.
  assert (KF18 : rw_cells asegs m10 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); CB 296 (repeat (Z_to_bv 8 0) 296)]) by (apply (wg_keep_live _ _ _ _ m9 m10 v2 384 _ _ H9_0 PRES10 WM10 INP_v2_8); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF19 : rw_cells asegs m10 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m9 m10 v1 24 _ _ H9_1 PRES10 WM10 INP_v1_8); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H9_2 AGc10 WM10 KF20.
  assert (KF22 : rw_cells asegs m10 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m9 m10 v3 32 _ _ KF16 PRES10 WM10 INP_v3_8); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF23 : rw_cells asegs m10 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m9 m10 v4 40 _ _ KF17 PRES10 WM10 INP_v4_8); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc10 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP10; exact SPc8).
  assert (CGc10 : rt_cg RT Σ5 = rt_cg RT Σ) by (rewrite CG10; exact CGc8).
  assert (LOW10 : rt_sp0 RT Σ5 - STACK_WIN <= lo) by (rewrite SPc10; exact LOW).
  assert (LEN10 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ4)) + 1) by (rewrite LV10; cbn [length]; lia).
  assert (LENc10 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ)) + 5) by lia. clear LENc8. wp_box1 LEN8. wp_box1 CR10.
  assert (Hfr10 : (length (rt_frames RT Σ5) < FRAMES_MAX)%nat) by (rewrite FRS10; exact Hfr8).
  assert (CTXb10 : cg_ctx (rt_cg RT Σ5) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc10; exact CTX).
  assert (CGH10 : cg_has (rt_cg RT Σ5) _ _) by (rewrite CGc10; exact CGH).
  assert (INP_v1_10 : In (v1, 24) (rt_live RT Σ5)) by (rewrite LV10; do 1 right; exact INP_v1_8).
  assert (INP_v2_10 : In (v2, 384) (rt_live RT Σ5)) by (rewrite LV10; do 1 right; exact INP_v2_8).
  assert (INP_v3_10 : In (v3, 32) (rt_live RT Σ5)) by (rewrite LV10; do 1 right; exact INP_v3_8).
  assert (INP_v4_10 : In (v4, 40) (rt_live RT Σ5)) by (rewrite LV10; do 1 right; exact INP_v4_8).
  assert (INP_v5_10 : In (v5, 40) (rt_live RT Σ5)) by (rewrite LV10; left; reflexivity).
  pose proof (af_live_range RT AF Σ5 m10 v5 40 ART10 INP_v5_10) as (_ & PHI_v5 & _). rewrite SPc10 in PHI_v5.
  pose proof (afp_live_mem RT GOBJ AFP Σ5 m10 v5 40 ART10 INP_v5_10 ltac:(lia)) as (_ & PT_v5).
  pose proof (afp_live_hi RT GOBJ AFP Σ5 m10 v5 40 ART10 INP_v5_10 ltac:(lia)) as PHH_v5.
  pose proof (wg_mod16_8 _ P16_v5) as PAL_v5. assert (PR64_v5 : 0 <= v5 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v5 : v5 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v5. wp_box1 PAL_v5. wp_box1 PR64_v5.
  destruct (af_client_consts RT AF Σ5 m10 ART10) as (_ & SHC10 & _ & _ & UT10).
  pose proof (af_acc_live RT AF Σ5 m10 v2 384 ART10 INP_v2_10) as (WR_v2_11 & ACC_v2_11).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s5_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_5) u0_5 u1_5 u2_5 b1_5 b2_5 b3_5 b4_5 b5_5 b6_5 b7_5 u3_5 u4_5 u5_5 u6_5 v1 v2 v3 v4 v5 F5 fc5 m10 lo
                ST10 WHLO WHIMG WHTOP KF18 KF19 KF20 SHC10 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 UT10 ACC_v2_11 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI10) as W11.
  cl_lift W11 Hc10' c11 Hc11.
  destruct (ASTA_unpack RT Σ5 _ _ c11 Hc11) as (ms11 & (m11 & -> & MU11 & WM11 & MI11 & H11_0 & H11_1 & H11_2 & H11_3 & ST11) & Hc11'). clear Hc11.
  fold usp in MU11, ST11, Hc11', H11_2.
  assert (ART11 : ART RT Σ5 m11).
  { apply (wg_seg_ART RT AF Σ5 m10 m11 usp 64 [(v2, v2 + 384)] ART10 ltac:(rewrite SPc10; lia) ltac:(lia) MU11); [|exact WM11].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_10 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF24 : rw_cells asegs m11 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m10 m11 _ _ KF22 MU11 WM11); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF25 : rw_cells asegs m11 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m10 m11 _ _ KF23 MU11 WM11); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF26 : rw_cells asegs m11 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m10 m11 _ _ G5_MX MU11 WM11); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m10 m11 _ canary G5_ENVp MU11 ltac:(cl_fp_lia)) as ENV11.
  assert (AGs11 : agree_on (fun x => usp <= x < USTACK_TOP) m10 m11) by (intros a Ha; apply MU11; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m10 m11 sp s0 UWF10 AGs11) as UWF11.
  destruct (cl_chain_call (rt_cg RT Σ5) e_ossl_method_store_new e_ossl_sa_new SITE_ossl_method_store_new_3 m11 m11 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb10
              (proj1 CGH10 (SITE_ossl_method_store_new_3, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH10 (SITE_ossl_method_store_new_3, e_ossl_sa_new) ltac:(wp_in_lit)) UWF11 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m11 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H11_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc11 & UWCc11).
  (* [comment removed for export] *)
  apply (C_ossl_sa_new Σ5 PMc (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_5 u1_5 u2_5 sp (Z_to_bv 64 v1) (Z_to_bv 64 v5) (Z_to_bv 64 (v2 + 88)) (Z_to_bv 64 0) b3_5 b4_5 b5_5 b6_5 b7_5 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_5 u4_5 u5_5 u6_5
           F5 fc5 m11 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART11 MI11).
  { fold usp in SPA. cl_call_ok EU1 ST11 LOW10 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). exact CTXc11. }
  { exact UWCc11. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). apply (proj2 CGH10). wp_in_lit. }
  { apply (cg_has_weaken _ _ _ _ _ CGH10); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV11. }
  { exact Hc11'. }
  clear Hc11'. intros c12 (Σ6 & v6 & Hc12 & LV12 & FRS12 & SP12 & CR12 & P0_v6 & P16_v6 & PU_v6 & CG12).
  wp_box1 PU_v6.
  destruct (ASTA_unpack RT Σ6 _ _ c12 Hc12) as (ms12 & (m12 & RS12 & (ART12 & MI12 & WM12 & ST12) & PRES12 & G6_ENVp & G6_WR & G6_ACC & G6_ZER) & Hc12'). clear Hc12.
  destruct RS12 as (u0_6 & u1_6 & u2_6 & b1_6 & b2_6 & b3_6 & b4_6 & b5_6 & b6_6 & b7_6 & u3_6 & u4_6 & u5_6 & u6_6 & F6 & fc6 & ->).
  rewrite EU1 in ST12, PRES12. rewrite (ret_pc_even SITE_ossl_method_store_new_3) in Hc12' by (unfold SITE_ossl_method_store_new_3; clear; first [reflexivity | lia]).
  assert (AGc12 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m11 m12).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES12; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu12 : agree_on (fun x => usp <= x < USTACK_TOP) m11 m12) by (intros a Ha; exact (AGc12 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m11 m12 sp s0 UWF11 AGu12) as UWF12.
  assert (KF27 : rw_cells asegs m12 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); CB 288 (repeat (Z_to_bv 8 0) 288)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v2 384 _ _ H11_0 PRES12 WM12 INP_v2_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF28 : rw_cells asegs m12 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v1 24 _ _ H11_1 PRES12 WM12 INP_v1_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H11_2 AGc12 WM12 KF29.
  assert (KF31 : rw_cells asegs m12 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m11 m12 v3 32 _ _ KF24 PRES12 WM12 INP_v3_10); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF32 : rw_cells asegs m12 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m11 m12 v4 40 _ _ KF25 PRES12 WM12 INP_v4_10); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF33 : rw_cells asegs m12 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m11 m12 v5 40 _ _ KF26 PRES12 WM12 INP_v5_10); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc12 : rt_sp0 RT Σ6 = rt_sp0 RT Σ) by (rewrite SP12; exact SPc10).
  assert (CGc12 : rt_cg RT Σ6 = rt_cg RT Σ) by (rewrite CG12; exact CGc10).
  assert (LOW12 : rt_sp0 RT Σ6 - STACK_WIN <= lo) by (rewrite SPc12; exact LOW).
  assert (LEN12 : Z.of_nat (length (rt_live RT Σ6)) = Z.of_nat (length (rt_live RT Σ5)) + 1) by (rewrite LV12; cbn [length]; lia).
  assert (LENc12 : Z.of_nat (length (rt_live RT Σ6)) = Z.of_nat (length (rt_live RT Σ)) + 6) by lia. clear LENc10. wp_box1 LEN10. wp_box1 CR12.
  assert (Hfr12 : (length (rt_frames RT Σ6) < FRAMES_MAX)%nat) by (rewrite FRS12; exact Hfr10).
  assert (CTXb12 : cg_ctx (rt_cg RT Σ6) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc12; exact CTX).
  assert (CGH12 : cg_has (rt_cg RT Σ6) _ _) by (rewrite CGc12; exact CGH).
  assert (INP_v1_12 : In (v1, 24) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v1_10).
  assert (INP_v2_12 : In (v2, 384) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v2_10).
  assert (INP_v3_12 : In (v3, 32) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v3_10).
  assert (INP_v4_12 : In (v4, 40) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v4_10).
  assert (INP_v5_12 : In (v5, 40) (rt_live RT Σ6)) by (rewrite LV12; do 1 right; exact INP_v5_10).
  assert (INP_v6_12 : In (v6, 32) (rt_live RT Σ6)) by (rewrite LV12; left; reflexivity).
  pose proof (af_live_range RT AF Σ6 m12 v6 32 ART12 INP_v6_12) as (_ & PHI_v6 & _). rewrite SPc12 in PHI_v6.
  pose proof (afp_live_mem RT GOBJ AFP Σ6 m12 v6 32 ART12 INP_v6_12 ltac:(lia)) as (_ & PT_v6).
  pose proof (afp_live_hi RT GOBJ AFP Σ6 m12 v6 32 ART12 INP_v6_12 ltac:(lia)) as PHH_v6.
  pose proof (wg_mod16_8 _ P16_v6) as PAL_v6. assert (PR64_v6 : 0 <= v6 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v6 : v6 + 32 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v6. wp_box1 PAL_v6. wp_box1 PR64_v6.
  destruct (af_client_consts RT AF Σ6 m12 ART12) as (_ & SHC12 & _ & _ & UT12).
  pose proof (af_acc_live RT AF Σ6 m12 v6 32 ART12 INP_v6_12) as (WR_v6_12 & ACC_v6_12).
  pose proof (wp_zero_rw_CB asegs m12 v6 32 G6_ZER WR_v6_12 ltac:(lia)) as HBZ_v6_12. change (Z.to_nat 32) with 32%nat in HBZ_v6_12.
  pose proof (af_acc_live RT AF Σ6 m12 v2 384 ART12 INP_v2_12) as (WR_v2_13 & ACC_v2_13).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s6_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_3) u0_6 u1_6 u2_6 b1_6 b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 u3_6 u4_6 u5_6 u6_6 v1 v2 v3 v4 v5 v6 F6 fc6 m12 lo
                ST12 WHLO WHIMG WHTOP KF27 KF28 KF29 SHC12 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 UT12 ACC_v2_13 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI12) as W13.
  cl_lift W13 Hc12' c13 Hc13.
  destruct (ASTA_unpack RT Σ6 _ _ c13 Hc13) as (ms13 & (m13 & -> & MU13 & WM13 & MI13 & H13_0 & H13_1 & H13_2 & H13_3 & ST13) & Hc13'). clear Hc13.
  fold usp in MU13, ST13, Hc13', H13_2.
  assert (ART13 : ART RT Σ6 m13).
  { apply (wg_seg_ART RT AF Σ6 m12 m13 usp 64 [(v2, v2 + 384)] ART12 ltac:(rewrite SPc12; lia) ltac:(lia) MU13); [|exact WM13].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_12 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF34 : rw_cells asegs m13 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m12 m13 _ _ KF31 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF35 : rw_cells asegs m13 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m12 m13 _ _ KF32 MU13 WM13); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF36 : rw_cells asegs m13 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m12 m13 _ _ KF33 MU13 WM13); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF37 : rw_cells asegs m13 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m12 m13 _ _ HBZ_v6_12 MU13 WM13); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m12 m13 _ canary G6_ENVp MU13 ltac:(cl_fp_lia)) as ENV13.
  assert (AGs13 : agree_on (fun x => usp <= x < USTACK_TOP) m12 m13) by (intros a Ha; apply MU13; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m12 m13 sp s0 UWF12 AGs13) as UWF13.
  destruct (cl_chain_call (rt_cg RT Σ6) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_4 m13 m13 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb12
              (proj1 CGH12 (SITE_ossl_method_store_new_4, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH12 (SITE_ossl_method_store_new_4, e_lock_new) ltac:(wp_in_lit)) UWF13 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m13 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H13_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc13 & UWCc13).
  (* [comment removed for export] *)
  apply (C_lock_new Σ6 PMc (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_6 u1_6 u2_6 sp (Z_to_bv 64 v1) (Z_to_bv 64 v6) (Z_to_bv 64 0) b2_6 b3_6 b4_6 b5_6 b6_6 b7_6 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_6 u4_6 u5_6 u6_6
           F6 fc6 m13 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART13 MI13).
  { fold usp in SPA. cl_call_ok EU1 ST13 LOW12 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_4) by (unfold SITE_ossl_method_store_new_4; lia). exact CTXc13. }
  { exact UWCc13. }
  { apply (cg_has_weaken _ _ _ _ _ CGH12); vm_compute; reflexivity. }
  { exact Hfr12. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV13. }
  { exact Hc13'. }
  clear Hc13'. intros c14 (Σ7 & v7 & Hc14 & LV14 & FRS14 & SP14 & CR14 & P0_v7 & P16_v7 & PU_v7 & CG14).
  wp_box1 PU_v7.
  destruct (ASTA_unpack RT Σ7 _ _ c14 Hc14) as (ms14 & (m14 & RS14 & (ART14 & MI14 & WM14 & ST14) & PRES14 & G7_ENVp & G7_MX & G7_ACC) & Hc14'). clear Hc14.
  destruct RS14 as (u0_7 & u1_7 & u2_7 & b1_7 & b2_7 & b3_7 & b4_7 & b5_7 & b6_7 & b7_7 & u3_7 & u4_7 & u5_7 & u6_7 & F7 & fc7 & ->).
  rewrite EU1 in ST14, PRES14. rewrite (ret_pc_even SITE_ossl_method_store_new_4) in Hc14' by (unfold SITE_ossl_method_store_new_4; clear; first [reflexivity | lia]).
  assert (AGc14 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m13 m14).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES14; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu14 : agree_on (fun x => usp <= x < USTACK_TOP) m13 m14) by (intros a Ha; exact (AGc14 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m13 m14 sp s0 UWF13 AGu14) as UWF14.
  assert (KF38 : rw_cells asegs m14 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 280 (repeat (Z_to_bv 8 0) 280)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v2 384 _ _ H13_0 PRES14 WM14 INP_v2_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF39 : rw_cells asegs m14 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v1 24 _ _ H13_1 PRES14 WM14 INP_v1_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H13_2 AGc14 WM14 KF40.
  assert (KF42 : rw_cells asegs m14 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v3 32 _ _ KF34 PRES14 WM14 INP_v3_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF43 : rw_cells asegs m14 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m13 m14 v4 40 _ _ KF35 PRES14 WM14 INP_v4_12); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF44 : rw_cells asegs m14 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m13 m14 v5 40 _ _ KF36 PRES14 WM14 INP_v5_12); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF45 : rw_cells asegs m14 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m13 m14 v6 32 _ _ KF37 PRES14 WM14 INP_v6_12); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc14 : rt_sp0 RT Σ7 = rt_sp0 RT Σ) by (rewrite SP14; exact SPc12).
  assert (CGc14 : rt_cg RT Σ7 = rt_cg RT Σ) by (rewrite CG14; exact CGc12).
  assert (LOW14 : rt_sp0 RT Σ7 - STACK_WIN <= lo) by (rewrite SPc14; exact LOW).
  assert (LEN14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ6)) + 1) by (rewrite LV14; cbn [length]; lia).
  assert (LENc14 : Z.of_nat (length (rt_live RT Σ7)) = Z.of_nat (length (rt_live RT Σ)) + 7) by lia. clear LENc12. wp_box1 LEN12. wp_box1 CR14.
  assert (Hfr14 : (length (rt_frames RT Σ7) < FRAMES_MAX)%nat) by (rewrite FRS14; exact Hfr12).
  assert (CTXb14 : cg_ctx (rt_cg RT Σ7) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc14; exact CTX).
  assert (CGH14 : cg_has (rt_cg RT Σ7) _ _) by (rewrite CGc14; exact CGH).
  assert (INP_v1_14 : In (v1, 24) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v1_12).
  assert (INP_v2_14 : In (v2, 384) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v2_12).
  assert (INP_v3_14 : In (v3, 32) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v3_12).
  assert (INP_v4_14 : In (v4, 40) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v4_12).
  assert (INP_v5_14 : In (v5, 40) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v5_12).
  assert (INP_v6_14 : In (v6, 32) (rt_live RT Σ7)) by (rewrite LV14; do 1 right; exact INP_v6_12).
  assert (INP_v7_14 : In (v7, 40) (rt_live RT Σ7)) by (rewrite LV14; left; reflexivity).
  pose proof (af_live_range RT AF Σ7 m14 v7 40 ART14 INP_v7_14) as (_ & PHI_v7 & _). rewrite SPc14 in PHI_v7.
  pose proof (afp_live_mem RT GOBJ AFP Σ7 m14 v7 40 ART14 INP_v7_14 ltac:(lia)) as (_ & PT_v7).
  pose proof (afp_live_hi RT GOBJ AFP Σ7 m14 v7 40 ART14 INP_v7_14 ltac:(lia)) as PHH_v7.
  pose proof (wg_mod16_8 _ P16_v7) as PAL_v7. assert (PR64_v7 : 0 <= v7 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v7 : v7 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v7. wp_box1 PAL_v7. wp_box1 PR64_v7.
  destruct (af_client_consts RT AF Σ7 m14 ART14) as (_ & SHC14 & _ & _ & UT14).
  pose proof (af_acc_live RT AF Σ7 m14 v2 384 ART14 INP_v2_14) as (WR_v2_15 & ACC_v2_15).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s7_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_4) u0_7 u1_7 u2_7 b1_7 b2_7 b3_7 b4_7 b5_7 b6_7 b7_7 u3_7 u4_7 u5_7 u6_7 v1 v2 v3 v4 v5 v6 v7 F7 fc7 m14 lo
                ST14 WHLO WHIMG WHTOP KF38 KF39 KF40 SHC14 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 UT14 ACC_v2_15 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI14) as W15.
  cl_lift W15 Hc14' c15 Hc15.
  destruct (ASTA_unpack RT Σ7 _ _ c15 Hc15) as (ms15 & (m15 & -> & MU15 & WM15 & MI15 & H15_0 & H15_1 & H15_2 & H15_3 & ST15) & Hc15'). clear Hc15.
  fold usp in MU15, ST15, Hc15', H15_2.
  assert (ART15 : ART RT Σ7 m15).
  { apply (wg_seg_ART RT AF Σ7 m14 m15 usp 64 [(v2, v2 + 384)] ART14 ltac:(rewrite SPc14; lia) ltac:(lia) MU15); [|exact WM15].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_14 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF46 : rw_cells asegs m15 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m14 m15 _ _ KF42 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF47 : rw_cells asegs m15 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m14 m15 _ _ KF43 MU15 WM15); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF48 : rw_cells asegs m15 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m14 m15 _ _ KF44 MU15 WM15); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF49 : rw_cells asegs m15 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m14 m15 _ _ KF45 MU15 WM15); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF50 : rw_cells asegs m15 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m14 m15 _ _ G7_MX MU15 WM15); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m14 m15 _ canary G7_ENVp MU15 ltac:(cl_fp_lia)) as ENV15.
  assert (AGs15 : agree_on (fun x => usp <= x < USTACK_TOP) m14 m15) by (intros a Ha; apply MU15; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m14 m15 sp s0 UWF14 AGs15) as UWF15.
  destruct (cl_chain_call (rt_cg RT Σ7) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_5 m15 m15 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb14
              (proj1 CGH14 (SITE_ossl_method_store_new_5, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH14 (SITE_ossl_method_store_new_5, e_lock_new) ltac:(wp_in_lit)) UWF15 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m15 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H15_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc15 & UWCc15).
  (* [comment removed for export] *)
  apply (C_lock_new Σ7 PMc (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_7 u1_7 u2_7 sp (Z_to_bv 64 v1) (Z_to_bv 64 v7) (Z_to_bv 64 (v2 + 176)) (Z_to_bv 64 0) b3_7 b4_7 b5_7 b6_7 b7_7 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 96)) (Z_to_bv 64 2147450880) (Z_to_bv 64 3) (Z_to_bv 64 (v2 + 184)) s7 s8 s9 s10 s11 u3_7 u4_7 u5_7 u6_7
           F7 fc7 m15 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART15 MI15).
  { fold usp in SPA. cl_call_ok EU1 ST15 LOW14 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_5) by (unfold SITE_ossl_method_store_new_5; lia). exact CTXc15. }
  { exact UWCc15. }
  { apply (cg_has_weaken _ _ _ _ _ CGH14); vm_compute; reflexivity. }
  { exact Hfr14. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV15. }
  { exact Hc15'. }
  clear Hc15'. intros c16 (Σ8 & v8 & Hc16 & LV16 & FRS16 & SP16 & CR16 & P0_v8 & P16_v8 & PU_v8 & CG16).
  wp_box1 PU_v8.
  destruct (ASTA_unpack RT Σ8 _ _ c16 Hc16) as (ms16 & (m16 & RS16 & (ART16 & MI16 & WM16 & ST16) & PRES16 & G8_ENVp & G8_MX & G8_ACC) & Hc16'). clear Hc16.
  destruct RS16 as (u0_8 & u1_8 & u2_8 & b1_8 & b2_8 & b3_8 & b4_8 & b5_8 & b6_8 & b7_8 & u3_8 & u4_8 & u5_8 & u6_8 & F8 & fc8 & ->).
  rewrite EU1 in ST16, PRES16. rewrite (ret_pc_even SITE_ossl_method_store_new_5) in Hc16' by (unfold SITE_ossl_method_store_new_5; clear; first [reflexivity | lia]).
  assert (AGc16 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m15 m16).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES16; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu16 : agree_on (fun x => usp <= x < USTACK_TOP) m15 m16) by (intros a Ha; exact (AGc16 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m15 m16 sp s0 UWF15 AGu16) as UWF16.
  assert (KF51 : rw_cells asegs m16 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); CB 200 (repeat (Z_to_bv 8 0) 200)]) by (apply (wg_keep_live _ _ _ _ m15 m16 v2 384 _ _ H15_0 PRES16 WM16 INP_v2_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF52 : rw_cells asegs m16 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m15 m16 v1 24 _ _ H15_1 PRES16 WM16 INP_v1_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H15_2 AGc16 WM16 KF53.
  assert (KF55 : rw_cells asegs m16 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m15 m16 v3 32 _ _ KF46 PRES16 WM16 INP_v3_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF56 : rw_cells asegs m16 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m15 m16 v4 40 _ _ KF47 PRES16 WM16 INP_v4_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF57 : rw_cells asegs m16 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m15 m16 v5 40 _ _ KF48 PRES16 WM16 INP_v5_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF58 : rw_cells asegs m16 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m15 m16 v6 32 _ _ KF49 PRES16 WM16 INP_v6_14); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF59 : rw_cells asegs m16 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m15 m16 v7 40 _ _ KF50 PRES16 WM16 INP_v7_14); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc16 : rt_sp0 RT Σ8 = rt_sp0 RT Σ) by (rewrite SP16; exact SPc14).
  assert (CGc16 : rt_cg RT Σ8 = rt_cg RT Σ) by (rewrite CG16; exact CGc14).
  assert (LOW16 : rt_sp0 RT Σ8 - STACK_WIN <= lo) by (rewrite SPc16; exact LOW).
  assert (LEN16 : Z.of_nat (length (rt_live RT Σ8)) = Z.of_nat (length (rt_live RT Σ7)) + 1) by (rewrite LV16; cbn [length]; lia).
  assert (LENc16 : Z.of_nat (length (rt_live RT Σ8)) = Z.of_nat (length (rt_live RT Σ)) + 8) by lia. clear LENc14. wp_box1 LEN14. wp_box1 CR16.
  assert (Hfr16 : (length (rt_frames RT Σ8) < FRAMES_MAX)%nat) by (rewrite FRS16; exact Hfr14).
  assert (CTXb16 : cg_ctx (rt_cg RT Σ8) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc16; exact CTX).
  assert (CGH16 : cg_has (rt_cg RT Σ8) _ _) by (rewrite CGc16; exact CGH).
  assert (INP_v1_16 : In (v1, 24) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v1_14).
  assert (INP_v2_16 : In (v2, 384) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v2_14).
  assert (INP_v3_16 : In (v3, 32) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v3_14).
  assert (INP_v4_16 : In (v4, 40) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v4_14).
  assert (INP_v5_16 : In (v5, 40) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v5_14).
  assert (INP_v6_16 : In (v6, 32) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v6_14).
  assert (INP_v7_16 : In (v7, 40) (rt_live RT Σ8)) by (rewrite LV16; do 1 right; exact INP_v7_14).
  assert (INP_v8_16 : In (v8, 40) (rt_live RT Σ8)) by (rewrite LV16; left; reflexivity).
  pose proof (af_live_range RT AF Σ8 m16 v8 40 ART16 INP_v8_16) as (_ & PHI_v8 & _). rewrite SPc16 in PHI_v8.
  pose proof (afp_live_mem RT GOBJ AFP Σ8 m16 v8 40 ART16 INP_v8_16 ltac:(lia)) as (_ & PT_v8).
  pose proof (afp_live_hi RT GOBJ AFP Σ8 m16 v8 40 ART16 INP_v8_16 ltac:(lia)) as PHH_v8.
  pose proof (wg_mod16_8 _ P16_v8) as PAL_v8. assert (PR64_v8 : 0 <= v8 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v8 : v8 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v8. wp_box1 PAL_v8. wp_box1 PR64_v8.
  destruct (af_client_consts RT AF Σ8 m16 ART16) as (_ & SHC16 & _ & _ & UT16).
  pose proof (af_acc_live RT AF Σ8 m16 v2 384 ART16 INP_v2_16) as (WR_v2_17 & ACC_v2_17).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s8_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_5) u0_8 u1_8 u2_8 b1_8 b2_8 b3_8 b4_8 b5_8 b6_8 b7_8 u3_8 u4_8 u5_8 u6_8 v1 v2 v3 v4 v5 v6 v7 v8 F8 fc8 m16 lo
                ST16 WHLO WHIMG WHTOP KF51 KF52 KF53 SHC16 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 UT16 ACC_v2_17 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI16) as W17.
  cl_lift W17 Hc16' c17 Hc17.
  destruct (ASTA_unpack RT Σ8 _ _ c17 Hc17) as (ms17 & (m17 & -> & MU17 & WM17 & MI17 & H17_0 & H17_1 & H17_2 & H17_3 & ST17) & Hc17'). clear Hc17.
  fold usp in MU17, ST17, Hc17', H17_2.
  assert (ART17 : ART RT Σ8 m17).
  { apply (wg_seg_ART RT AF Σ8 m16 m17 usp 64 [(v2, v2 + 384)] ART16 ltac:(rewrite SPc16; lia) ltac:(lia) MU17); [|exact WM17].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_16 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF60 : rw_cells asegs m17 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m16 m17 _ _ KF55 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF61 : rw_cells asegs m17 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m16 m17 _ _ KF56 MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF62 : rw_cells asegs m17 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m16 m17 _ _ KF57 MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF63 : rw_cells asegs m17 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m16 m17 _ _ KF58 MU17 WM17); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF64 : rw_cells asegs m17 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m16 m17 _ _ KF59 MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF65 : rw_cells asegs m17 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m16 m17 _ _ G8_MX MU17 WM17); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m16 m17 _ canary G8_ENVp MU17 ltac:(cl_fp_lia)) as ENV17.
  assert (AGs17 : agree_on (fun x => usp <= x < USTACK_TOP) m16 m17) by (intros a Ha; apply MU17; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m16 m17 sp s0 UWF16 AGs17) as UWF17.
  destruct (cl_chain_call (rt_cg RT Σ8) e_ossl_method_store_new e_ossl_sa_new SITE_ossl_method_store_new_3 m17 m17 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb16
              (proj1 CGH16 (SITE_ossl_method_store_new_3, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH16 (SITE_ossl_method_store_new_3, e_ossl_sa_new) ltac:(wp_in_lit)) UWF17 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m17 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H17_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc17 & UWCc17).
  (* [comment removed for export] *)
  apply (C_ossl_sa_new Σ8 PMc (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_8 u1_8 u2_8 sp (Z_to_bv 64 v1) (Z_to_bv 64 v8) (Z_to_bv 64 (v2 + 184)) (Z_to_bv 64 0) b3_8 b4_8 b5_8 b6_8 b7_8 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_8 u4_8 u5_8 u6_8
           F8 fc8 m17 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART17 MI17).
  { fold usp in SPA. cl_call_ok EU1 ST17 LOW16 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). exact CTXc17. }
  { exact UWCc17. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). apply (proj2 CGH16). wp_in_lit. }
  { apply (cg_has_weaken _ _ _ _ _ CGH16); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV17. }
  { exact Hc17'. }
  clear Hc17'. intros c18 (Σ9 & v9 & Hc18 & LV18 & FRS18 & SP18 & CR18 & P0_v9 & P16_v9 & PU_v9 & CG18).
  wp_box1 PU_v9.
  destruct (ASTA_unpack RT Σ9 _ _ c18 Hc18) as (ms18 & (m18 & RS18 & (ART18 & MI18 & WM18 & ST18) & PRES18 & G9_ENVp & G9_WR & G9_ACC & G9_ZER) & Hc18'). clear Hc18.
  destruct RS18 as (u0_9 & u1_9 & u2_9 & b1_9 & b2_9 & b3_9 & b4_9 & b5_9 & b6_9 & b7_9 & u3_9 & u4_9 & u5_9 & u6_9 & F9 & fc9 & ->).
  rewrite EU1 in ST18, PRES18. rewrite (ret_pc_even SITE_ossl_method_store_new_3) in Hc18' by (unfold SITE_ossl_method_store_new_3; clear; first [reflexivity | lia]).
  assert (AGc18 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m17 m18).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES18; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu18 : agree_on (fun x => usp <= x < USTACK_TOP) m17 m18) by (intros a Ha; exact (AGc18 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m17 m18 sp s0 UWF17 AGu18) as UWF18.
  assert (KF66 : rw_cells asegs m18 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); CB 192 (repeat (Z_to_bv 8 0) 192)]) by (apply (wg_keep_live _ _ _ _ m17 m18 v2 384 _ _ H17_0 PRES18 WM18 INP_v2_16); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF67 : rw_cells asegs m18 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m17 m18 v1 24 _ _ H17_1 PRES18 WM18 INP_v1_16); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H17_2 AGc18 WM18 KF68.
  assert (KF70 : rw_cells asegs m18 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m17 m18 v3 32 _ _ KF60 PRES18 WM18 INP_v3_16); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF71 : rw_cells asegs m18 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m17 m18 v4 40 _ _ KF61 PRES18 WM18 INP_v4_16); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF72 : rw_cells asegs m18 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m17 m18 v5 40 _ _ KF62 PRES18 WM18 INP_v5_16); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF73 : rw_cells asegs m18 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m17 m18 v6 32 _ _ KF63 PRES18 WM18 INP_v6_16); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF74 : rw_cells asegs m18 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m17 m18 v7 40 _ _ KF64 PRES18 WM18 INP_v7_16); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF75 : rw_cells asegs m18 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m17 m18 v8 40 _ _ KF65 PRES18 WM18 INP_v8_16); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc18 : rt_sp0 RT Σ9 = rt_sp0 RT Σ) by (rewrite SP18; exact SPc16).
  assert (CGc18 : rt_cg RT Σ9 = rt_cg RT Σ) by (rewrite CG18; exact CGc16).
  assert (LOW18 : rt_sp0 RT Σ9 - STACK_WIN <= lo) by (rewrite SPc18; exact LOW).
  assert (LEN18 : Z.of_nat (length (rt_live RT Σ9)) = Z.of_nat (length (rt_live RT Σ8)) + 1) by (rewrite LV18; cbn [length]; lia).
  assert (LENc18 : Z.of_nat (length (rt_live RT Σ9)) = Z.of_nat (length (rt_live RT Σ)) + 9) by lia. clear LENc16. wp_box1 LEN16. wp_box1 CR18.
  assert (Hfr18 : (length (rt_frames RT Σ9) < FRAMES_MAX)%nat) by (rewrite FRS18; exact Hfr16).
  assert (CTXb18 : cg_ctx (rt_cg RT Σ9) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc18; exact CTX).
  assert (CGH18 : cg_has (rt_cg RT Σ9) _ _) by (rewrite CGc18; exact CGH).
  assert (INP_v1_18 : In (v1, 24) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v1_16).
  assert (INP_v2_18 : In (v2, 384) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v2_16).
  assert (INP_v3_18 : In (v3, 32) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v3_16).
  assert (INP_v4_18 : In (v4, 40) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v4_16).
  assert (INP_v5_18 : In (v5, 40) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v5_16).
  assert (INP_v6_18 : In (v6, 32) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v6_16).
  assert (INP_v7_18 : In (v7, 40) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v7_16).
  assert (INP_v8_18 : In (v8, 40) (rt_live RT Σ9)) by (rewrite LV18; do 1 right; exact INP_v8_16).
  assert (INP_v9_18 : In (v9, 32) (rt_live RT Σ9)) by (rewrite LV18; left; reflexivity).
  pose proof (af_live_range RT AF Σ9 m18 v9 32 ART18 INP_v9_18) as (_ & PHI_v9 & _). rewrite SPc18 in PHI_v9.
  pose proof (afp_live_mem RT GOBJ AFP Σ9 m18 v9 32 ART18 INP_v9_18 ltac:(lia)) as (_ & PT_v9).
  pose proof (afp_live_hi RT GOBJ AFP Σ9 m18 v9 32 ART18 INP_v9_18 ltac:(lia)) as PHH_v9.
  pose proof (wg_mod16_8 _ P16_v9) as PAL_v9. assert (PR64_v9 : 0 <= v9 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v9 : v9 + 32 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v9. wp_box1 PAL_v9. wp_box1 PR64_v9.
  destruct (af_client_consts RT AF Σ9 m18 ART18) as (_ & SHC18 & _ & _ & UT18).
  pose proof (af_acc_live RT AF Σ9 m18 v9 32 ART18 INP_v9_18) as (WR_v9_18 & ACC_v9_18).
  pose proof (wp_zero_rw_CB asegs m18 v9 32 G9_ZER WR_v9_18 ltac:(lia)) as HBZ_v9_18. change (Z.to_nat 32) with 32%nat in HBZ_v9_18.
  pose proof (af_acc_live RT AF Σ9 m18 v2 384 ART18 INP_v2_18) as (WR_v2_19 & ACC_v2_19).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s9_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_3) u0_9 u1_9 u2_9 b1_9 b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 u3_9 u4_9 u5_9 u6_9 v1 v2 v3 v4 v5 v6 v7 v8 v9 F9 fc9 m18 lo
                ST18 WHLO WHIMG WHTOP KF66 KF67 KF68 SHC18 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 UT18 ACC_v2_19 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI18) as W19.
  cl_lift W19 Hc18' c19 Hc19.
  destruct (ASTA_unpack RT Σ9 _ _ c19 Hc19) as (ms19 & (m19 & -> & MU19 & WM19 & MI19 & H19_0 & H19_1 & H19_2 & H19_3 & ST19) & Hc19'). clear Hc19.
  fold usp in MU19, ST19, Hc19', H19_2.
  assert (ART19 : ART RT Σ9 m19).
  { apply (wg_seg_ART RT AF Σ9 m18 m19 usp 64 [(v2, v2 + 384)] ART18 ltac:(rewrite SPc18; lia) ltac:(lia) MU19); [|exact WM19].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_18 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF76 : rw_cells asegs m19 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m18 m19 _ _ KF70 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF77 : rw_cells asegs m19 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m18 m19 _ _ KF71 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF78 : rw_cells asegs m19 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m18 m19 _ _ KF72 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF79 : rw_cells asegs m19 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m18 m19 _ _ KF73 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF80 : rw_cells asegs m19 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m18 m19 _ _ KF74 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF81 : rw_cells asegs m19 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m18 m19 _ _ KF75 MU19 WM19); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF82 : rw_cells asegs m19 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; apply (wg_keep_seg _ m18 m19 _ _ HBZ_v9_18 MU19 WM19); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m18 m19 _ canary G9_ENVp MU19 ltac:(cl_fp_lia)) as ENV19.
  assert (AGs19 : agree_on (fun x => usp <= x < USTACK_TOP) m18 m19) by (intros a Ha; apply MU19; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m18 m19 sp s0 UWF18 AGs19) as UWF19.
  destruct (cl_chain_call (rt_cg RT Σ9) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_4 m19 m19 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb18
              (proj1 CGH18 (SITE_ossl_method_store_new_4, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH18 (SITE_ossl_method_store_new_4, e_lock_new) ltac:(wp_in_lit)) UWF19 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m19 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H19_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc19 & UWCc19).
  (* [comment removed for export] *)
  apply (C_lock_new Σ9 PMc (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_9 u1_9 u2_9 sp (Z_to_bv 64 v1) (Z_to_bv 64 v9) (Z_to_bv 64 0) b2_9 b3_9 b4_9 b5_9 b6_9 b7_9 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_9 u4_9 u5_9 u6_9
           F9 fc9 m19 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART19 MI19).
  { fold usp in SPA. cl_call_ok EU1 ST19 LOW18 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_4) by (unfold SITE_ossl_method_store_new_4; lia). exact CTXc19. }
  { exact UWCc19. }
  { apply (cg_has_weaken _ _ _ _ _ CGH18); vm_compute; reflexivity. }
  { exact Hfr18. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV19. }
  { exact Hc19'. }
  clear Hc19'. intros c20 (Σ10 & v10 & Hc20 & LV20 & FRS20 & SP20 & CR20 & P0_v10 & P16_v10 & PU_v10 & CG20).
  wp_box1 PU_v10.
  destruct (ASTA_unpack RT Σ10 _ _ c20 Hc20) as (ms20 & (m20 & RS20 & (ART20 & MI20 & WM20 & ST20) & PRES20 & G10_ENVp & G10_MX & G10_ACC) & Hc20'). clear Hc20.
  destruct RS20 as (u0_10 & u1_10 & u2_10 & b1_10 & b2_10 & b3_10 & b4_10 & b5_10 & b6_10 & b7_10 & u3_10 & u4_10 & u5_10 & u6_10 & F10 & fc10 & ->).
  rewrite EU1 in ST20, PRES20. rewrite (ret_pc_even SITE_ossl_method_store_new_4) in Hc20' by (unfold SITE_ossl_method_store_new_4; clear; first [reflexivity | lia]).
  assert (AGc20 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m19 m20).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES20; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu20 : agree_on (fun x => usp <= x < USTACK_TOP) m19 m20) by (intros a Ha; exact (AGc20 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m19 m20 sp s0 UWF19 AGu20) as UWF20.
  assert (KF83 : rw_cells asegs m20 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 184 (repeat (Z_to_bv 8 0) 184)]) by (apply (wg_keep_live _ _ _ _ m19 m20 v2 384 _ _ H19_0 PRES20 WM20 INP_v2_18); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF84 : rw_cells asegs m20 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m19 m20 v1 24 _ _ H19_1 PRES20 WM20 INP_v1_18); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H19_2 AGc20 WM20 KF85.
  assert (KF87 : rw_cells asegs m20 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m19 m20 v3 32 _ _ KF76 PRES20 WM20 INP_v3_18); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF88 : rw_cells asegs m20 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m19 m20 v4 40 _ _ KF77 PRES20 WM20 INP_v4_18); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF89 : rw_cells asegs m20 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m19 m20 v5 40 _ _ KF78 PRES20 WM20 INP_v5_18); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF90 : rw_cells asegs m20 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m19 m20 v6 32 _ _ KF79 PRES20 WM20 INP_v6_18); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF91 : rw_cells asegs m20 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m19 m20 v7 40 _ _ KF80 PRES20 WM20 INP_v7_18); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF92 : rw_cells asegs m20 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m19 m20 v8 40 _ _ KF81 PRES20 WM20 INP_v8_18); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF93 : rw_cells asegs m20 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m19 m20 v9 32 _ _ KF82 PRES20 WM20 INP_v9_18); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc20 : rt_sp0 RT Σ10 = rt_sp0 RT Σ) by (rewrite SP20; exact SPc18).
  assert (CGc20 : rt_cg RT Σ10 = rt_cg RT Σ) by (rewrite CG20; exact CGc18).
  assert (LOW20 : rt_sp0 RT Σ10 - STACK_WIN <= lo) by (rewrite SPc20; exact LOW).
  assert (LEN20 : Z.of_nat (length (rt_live RT Σ10)) = Z.of_nat (length (rt_live RT Σ9)) + 1) by (rewrite LV20; cbn [length]; lia).
  assert (LENc20 : Z.of_nat (length (rt_live RT Σ10)) = Z.of_nat (length (rt_live RT Σ)) + 10) by lia. clear LENc18. wp_box1 LEN18. wp_box1 CR20.
  assert (Hfr20 : (length (rt_frames RT Σ10) < FRAMES_MAX)%nat) by (rewrite FRS20; exact Hfr18).
  assert (CTXb20 : cg_ctx (rt_cg RT Σ10) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc20; exact CTX).
  assert (CGH20 : cg_has (rt_cg RT Σ10) _ _) by (rewrite CGc20; exact CGH).
  assert (INP_v1_20 : In (v1, 24) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v1_18).
  assert (INP_v2_20 : In (v2, 384) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v2_18).
  assert (INP_v3_20 : In (v3, 32) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v3_18).
  assert (INP_v4_20 : In (v4, 40) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v4_18).
  assert (INP_v5_20 : In (v5, 40) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v5_18).
  assert (INP_v6_20 : In (v6, 32) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v6_18).
  assert (INP_v7_20 : In (v7, 40) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v7_18).
  assert (INP_v8_20 : In (v8, 40) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v8_18).
  assert (INP_v9_20 : In (v9, 32) (rt_live RT Σ10)) by (rewrite LV20; do 1 right; exact INP_v9_18).
  assert (INP_v10_20 : In (v10, 40) (rt_live RT Σ10)) by (rewrite LV20; left; reflexivity).
  pose proof (af_live_range RT AF Σ10 m20 v10 40 ART20 INP_v10_20) as (_ & PHI_v10 & _). rewrite SPc20 in PHI_v10.
  pose proof (afp_live_mem RT GOBJ AFP Σ10 m20 v10 40 ART20 INP_v10_20 ltac:(lia)) as (_ & PT_v10).
  pose proof (afp_live_hi RT GOBJ AFP Σ10 m20 v10 40 ART20 INP_v10_20 ltac:(lia)) as PHH_v10.
  pose proof (wg_mod16_8 _ P16_v10) as PAL_v10. assert (PR64_v10 : 0 <= v10 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v10 : v10 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v10. wp_box1 PAL_v10. wp_box1 PR64_v10.
  destruct (af_client_consts RT AF Σ10 m20 ART20) as (_ & SHC20 & _ & _ & UT20).
  pose proof (af_acc_live RT AF Σ10 m20 v2 384 ART20 INP_v2_20) as (WR_v2_21 & ACC_v2_21).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s10_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_4) u0_10 u1_10 u2_10 b1_10 b2_10 b3_10 b4_10 b5_10 b6_10 b7_10 u3_10 u4_10 u5_10 u6_10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 F10 fc10 m20 lo
                ST20 WHLO WHIMG WHTOP KF83 KF84 KF85 SHC20 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 UT20 ACC_v2_21 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI20) as W21.
  cl_lift W21 Hc20' c21 Hc21.
  destruct (ASTA_unpack RT Σ10 _ _ c21 Hc21) as (ms21 & (m21 & -> & MU21 & WM21 & MI21 & H21_0 & H21_1 & H21_2 & H21_3 & ST21) & Hc21'). clear Hc21.
  fold usp in MU21, ST21, Hc21', H21_2.
  assert (ART21 : ART RT Σ10 m21).
  { apply (wg_seg_ART RT AF Σ10 m20 m21 usp 64 [(v2, v2 + 384)] ART20 ltac:(rewrite SPc20; lia) ltac:(lia) MU21); [|exact WM21].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_20 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF94 : rw_cells asegs m21 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m20 m21 _ _ KF87 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF95 : rw_cells asegs m21 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m20 m21 _ _ KF88 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF96 : rw_cells asegs m21 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m20 m21 _ _ KF89 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF97 : rw_cells asegs m21 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m20 m21 _ _ KF90 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF98 : rw_cells asegs m21 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m20 m21 _ _ KF91 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF99 : rw_cells asegs m21 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m20 m21 _ _ KF92 MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF100 : rw_cells asegs m21 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; apply (wg_keep_seg _ m20 m21 _ _ KF93 MU21 WM21); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF101 : rw_cells asegs m21 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v2 384 ART20 LV20 ltac:(cbn [app In]; exact INP_v2_18)) as DJ_v10_v2; apply (wg_keep_seg _ m20 m21 _ _ G10_MX MU21 WM21); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v10_v2 PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m20 m21 _ canary G10_ENVp MU21 ltac:(cl_fp_lia)) as ENV21.
  assert (AGs21 : agree_on (fun x => usp <= x < USTACK_TOP) m20 m21) by (intros a Ha; apply MU21; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m20 m21 sp s0 UWF20 AGs21) as UWF21.
  destruct (cl_chain_call (rt_cg RT Σ10) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_5 m21 m21 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb20
              (proj1 CGH20 (SITE_ossl_method_store_new_5, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH20 (SITE_ossl_method_store_new_5, e_lock_new) ltac:(wp_in_lit)) UWF21 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m21 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H21_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc21 & UWCc21).
  (* [comment removed for export] *)
  apply (C_lock_new Σ10 PMc (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_10 u1_10 u2_10 sp (Z_to_bv 64 v1) (Z_to_bv 64 v10) (Z_to_bv 64 (v2 + 272)) (Z_to_bv 64 0) b3_10 b4_10 b5_10 b6_10 b7_10 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 192)) (Z_to_bv 64 2147450880) (Z_to_bv 64 2) (Z_to_bv 64 (v2 + 280)) s7 s8 s9 s10 s11 u3_10 u4_10 u5_10 u6_10
           F10 fc10 m21 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART21 MI21).
  { fold usp in SPA. cl_call_ok EU1 ST21 LOW20 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_5) by (unfold SITE_ossl_method_store_new_5; lia). exact CTXc21. }
  { exact UWCc21. }
  { apply (cg_has_weaken _ _ _ _ _ CGH20); vm_compute; reflexivity. }
  { exact Hfr20. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV21. }
  { exact Hc21'. }
  clear Hc21'. intros c22 (Σ11 & v11 & Hc22 & LV22 & FRS22 & SP22 & CR22 & P0_v11 & P16_v11 & PU_v11 & CG22).
  wp_box1 PU_v11.
  destruct (ASTA_unpack RT Σ11 _ _ c22 Hc22) as (ms22 & (m22 & RS22 & (ART22 & MI22 & WM22 & ST22) & PRES22 & G11_ENVp & G11_MX & G11_ACC) & Hc22'). clear Hc22.
  destruct RS22 as (u0_11 & u1_11 & u2_11 & b1_11 & b2_11 & b3_11 & b4_11 & b5_11 & b6_11 & b7_11 & u3_11 & u4_11 & u5_11 & u6_11 & F11 & fc11 & ->).
  rewrite EU1 in ST22, PRES22. rewrite (ret_pc_even SITE_ossl_method_store_new_5) in Hc22' by (unfold SITE_ossl_method_store_new_5; clear; first [reflexivity | lia]).
  assert (AGc22 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m21 m22).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES22; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu22 : agree_on (fun x => usp <= x < USTACK_TOP) m21 m22) by (intros a Ha; exact (AGc22 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m21 m22 sp s0 UWF21 AGu22) as UWF22.
  assert (KF102 : rw_cells asegs m22 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); CB 104 (repeat (Z_to_bv 8 0) 104)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v2 384 _ _ H21_0 PRES22 WM22 INP_v2_20); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF103 : rw_cells asegs m22 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v1 24 _ _ H21_1 PRES22 WM22 INP_v1_20); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H21_2 AGc22 WM22 KF104.
  assert (KF106 : rw_cells asegs m22 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v3 32 _ _ KF94 PRES22 WM22 INP_v3_20); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF107 : rw_cells asegs m22 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v4 40 _ _ KF95 PRES22 WM22 INP_v4_20); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF108 : rw_cells asegs m22 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v5 40 _ _ KF96 PRES22 WM22 INP_v5_20); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF109 : rw_cells asegs m22 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v6 32 _ _ KF97 PRES22 WM22 INP_v6_20); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF110 : rw_cells asegs m22 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v7 40 _ _ KF98 PRES22 WM22 INP_v7_20); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF111 : rw_cells asegs m22 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v8 40 _ _ KF99 PRES22 WM22 INP_v8_20); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF112 : rw_cells asegs m22 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m21 m22 v9 32 _ _ KF100 PRES22 WM22 INP_v9_20); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF113 : rw_cells asegs m22 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m21 m22 v10 40 _ _ KF101 PRES22 WM22 INP_v10_20); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc22 : rt_sp0 RT Σ11 = rt_sp0 RT Σ) by (rewrite SP22; exact SPc20).
  assert (CGc22 : rt_cg RT Σ11 = rt_cg RT Σ) by (rewrite CG22; exact CGc20).
  assert (LOW22 : rt_sp0 RT Σ11 - STACK_WIN <= lo) by (rewrite SPc22; exact LOW).
  assert (LEN22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ10)) + 1) by (rewrite LV22; cbn [length]; lia).
  assert (LENc22 : Z.of_nat (length (rt_live RT Σ11)) = Z.of_nat (length (rt_live RT Σ)) + 11) by lia. clear LENc20. wp_box1 LEN20. wp_box1 CR22.
  assert (Hfr22 : (length (rt_frames RT Σ11) < FRAMES_MAX)%nat) by (rewrite FRS22; exact Hfr20).
  assert (CTXb22 : cg_ctx (rt_cg RT Σ11) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc22; exact CTX).
  assert (CGH22 : cg_has (rt_cg RT Σ11) _ _) by (rewrite CGc22; exact CGH).
  assert (INP_v1_22 : In (v1, 24) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v1_20).
  assert (INP_v2_22 : In (v2, 384) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v2_20).
  assert (INP_v3_22 : In (v3, 32) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v3_20).
  assert (INP_v4_22 : In (v4, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v4_20).
  assert (INP_v5_22 : In (v5, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v5_20).
  assert (INP_v6_22 : In (v6, 32) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v6_20).
  assert (INP_v7_22 : In (v7, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v7_20).
  assert (INP_v8_22 : In (v8, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v8_20).
  assert (INP_v9_22 : In (v9, 32) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v9_20).
  assert (INP_v10_22 : In (v10, 40) (rt_live RT Σ11)) by (rewrite LV22; do 1 right; exact INP_v10_20).
  assert (INP_v11_22 : In (v11, 40) (rt_live RT Σ11)) by (rewrite LV22; left; reflexivity).
  pose proof (af_live_range RT AF Σ11 m22 v11 40 ART22 INP_v11_22) as (_ & PHI_v11 & _). rewrite SPc22 in PHI_v11.
  pose proof (afp_live_mem RT GOBJ AFP Σ11 m22 v11 40 ART22 INP_v11_22 ltac:(lia)) as (_ & PT_v11).
  pose proof (afp_live_hi RT GOBJ AFP Σ11 m22 v11 40 ART22 INP_v11_22 ltac:(lia)) as PHH_v11.
  pose proof (wg_mod16_8 _ P16_v11) as PAL_v11. assert (PR64_v11 : 0 <= v11 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v11 : v11 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v11. wp_box1 PAL_v11. wp_box1 PR64_v11.
  destruct (af_client_consts RT AF Σ11 m22 ART22) as (_ & SHC22 & _ & _ & UT22).
  pose proof (af_acc_live RT AF Σ11 m22 v2 384 ART22 INP_v2_22) as (WR_v2_23 & ACC_v2_23).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s11_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_5) u0_11 u1_11 u2_11 b1_11 b2_11 b3_11 b4_11 b5_11 b6_11 b7_11 u3_11 u4_11 u5_11 u6_11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F11 fc11 m22 lo
                ST22 WHLO WHIMG WHTOP KF102 KF103 KF104 SHC22 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 PR64_v11 UT22 ACC_v2_23 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI22) as W23.
  cl_lift W23 Hc22' c23 Hc23.
  destruct (ASTA_unpack RT Σ11 _ _ c23 Hc23) as (ms23 & (m23 & -> & MU23 & WM23 & MI23 & H23_0 & H23_1 & H23_2 & H23_3 & ST23) & Hc23'). clear Hc23.
  fold usp in MU23, ST23, Hc23', H23_2.
  assert (ART23 : ART RT Σ11 m23).
  { apply (wg_seg_ART RT AF Σ11 m22 m23 usp 64 [(v2, v2 + 384)] ART22 ltac:(rewrite SPc22; lia) ltac:(lia) MU23); [|exact WM23].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_22 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF114 : rw_cells asegs m23 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m22 m23 _ _ KF106 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF115 : rw_cells asegs m23 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m22 m23 _ _ KF107 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF116 : rw_cells asegs m23 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m22 m23 _ _ KF108 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF117 : rw_cells asegs m23 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m22 m23 _ _ KF109 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF118 : rw_cells asegs m23 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m22 m23 _ _ KF110 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF119 : rw_cells asegs m23 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m22 m23 _ _ KF111 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF120 : rw_cells asegs m23 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; apply (wg_keep_seg _ m22 m23 _ _ KF112 MU23 WM23); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF121 : rw_cells asegs m23 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v2 384 ART20 LV20 ltac:(cbn [app In]; exact INP_v2_18)) as DJ_v10_v2; apply (wg_keep_seg _ m22 m23 _ _ KF113 MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v10_v2 PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF122 : rw_cells asegs m23 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v2 384 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_20)) as DJ_v11_v2; apply (wg_keep_seg _ m22 m23 _ _ G11_MX MU23 WM23); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m22 m23 _ canary G11_ENVp MU23 ltac:(cl_fp_lia)) as ENV23.
  assert (AGs23 : agree_on (fun x => usp <= x < USTACK_TOP) m22 m23) by (intros a Ha; apply MU23; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m22 m23 sp s0 UWF22 AGs23) as UWF23.
  destruct (cl_chain_call (rt_cg RT Σ11) e_ossl_method_store_new e_ossl_sa_new SITE_ossl_method_store_new_3 m23 m23 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb22
              (proj1 CGH22 (SITE_ossl_method_store_new_3, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH22 (SITE_ossl_method_store_new_3, e_ossl_sa_new) ltac:(wp_in_lit)) UWF23 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m23 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H23_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc23 & UWCc23).
  (* [comment removed for export] *)
  apply (C_ossl_sa_new Σ11 PMc (Z_to_bv 64 SITE_ossl_method_store_new_3) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_11 u1_11 u2_11 sp (Z_to_bv 64 v1) (Z_to_bv 64 v11) (Z_to_bv 64 (v2 + 280)) (Z_to_bv 64 0) b3_11 b4_11 b5_11 b6_11 b7_11 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_11 u4_11 u5_11 u6_11
           F11 fc11 m23 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART23 MI23).
  { fold usp in SPA. cl_call_ok EU1 ST23 LOW22 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). exact CTXc23. }
  { exact UWCc23. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_3) by (unfold SITE_ossl_method_store_new_3; lia). apply (proj2 CGH22). wp_in_lit. }
  { apply (cg_has_weaken _ _ _ _ _ CGH22); vm_compute; reflexivity. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV23. }
  { exact Hc23'. }
  clear Hc23'. intros c24 (Σ12 & v12 & Hc24 & LV24 & FRS24 & SP24 & CR24 & P0_v12 & P16_v12 & PU_v12 & CG24).
  wp_box1 PU_v12.
  destruct (ASTA_unpack RT Σ12 _ _ c24 Hc24) as (ms24 & (m24 & RS24 & (ART24 & MI24 & WM24 & ST24) & PRES24 & G12_ENVp & G12_WR & G12_ACC & G12_ZER) & Hc24'). clear Hc24.
  destruct RS24 as (u0_12 & u1_12 & u2_12 & b1_12 & b2_12 & b3_12 & b4_12 & b5_12 & b6_12 & b7_12 & u3_12 & u4_12 & u5_12 & u6_12 & F12 & fc12 & ->).
  rewrite EU1 in ST24, PRES24. rewrite (ret_pc_even SITE_ossl_method_store_new_3) in Hc24' by (unfold SITE_ossl_method_store_new_3; clear; first [reflexivity | lia]).
  assert (AGc24 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m23 m24).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES24; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu24 : agree_on (fun x => usp <= x < USTACK_TOP) m23 m24) by (intros a Ha; exact (AGc24 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m23 m24 sp s0 UWF23 AGu24) as UWF24.
  assert (KF123 : rw_cells asegs m24 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); CB 96 (repeat (Z_to_bv 8 0) 96)]) by (apply (wg_keep_live _ _ _ _ m23 m24 v2 384 _ _ H23_0 PRES24 WM24 INP_v2_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF124 : rw_cells asegs m24 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m23 m24 v1 24 _ _ H23_1 PRES24 WM24 INP_v1_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H23_2 AGc24 WM24 KF125.
  assert (KF127 : rw_cells asegs m24 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m23 m24 v3 32 _ _ KF114 PRES24 WM24 INP_v3_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF128 : rw_cells asegs m24 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v4 40 _ _ KF115 PRES24 WM24 INP_v4_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF129 : rw_cells asegs m24 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v5 40 _ _ KF116 PRES24 WM24 INP_v5_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF130 : rw_cells asegs m24 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m23 m24 v6 32 _ _ KF117 PRES24 WM24 INP_v6_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF131 : rw_cells asegs m24 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v7 40 _ _ KF118 PRES24 WM24 INP_v7_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF132 : rw_cells asegs m24 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v8 40 _ _ KF119 PRES24 WM24 INP_v8_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF133 : rw_cells asegs m24 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m23 m24 v9 32 _ _ KF120 PRES24 WM24 INP_v9_22); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF134 : rw_cells asegs m24 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v10 40 _ _ KF121 PRES24 WM24 INP_v10_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF135 : rw_cells asegs m24 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m23 m24 v11 40 _ _ KF122 PRES24 WM24 INP_v11_22); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc24 : rt_sp0 RT Σ12 = rt_sp0 RT Σ) by (rewrite SP24; exact SPc22).
  assert (CGc24 : rt_cg RT Σ12 = rt_cg RT Σ) by (rewrite CG24; exact CGc22).
  assert (LOW24 : rt_sp0 RT Σ12 - STACK_WIN <= lo) by (rewrite SPc24; exact LOW).
  assert (LEN24 : Z.of_nat (length (rt_live RT Σ12)) = Z.of_nat (length (rt_live RT Σ11)) + 1) by (rewrite LV24; cbn [length]; lia).
  assert (LENc24 : Z.of_nat (length (rt_live RT Σ12)) = Z.of_nat (length (rt_live RT Σ)) + 12) by lia. clear LENc22. wp_box1 LEN22. wp_box1 CR24.
  assert (Hfr24 : (length (rt_frames RT Σ12) < FRAMES_MAX)%nat) by (rewrite FRS24; exact Hfr22).
  assert (CTXb24 : cg_ctx (rt_cg RT Σ12) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc24; exact CTX).
  assert (CGH24 : cg_has (rt_cg RT Σ12) _ _) by (rewrite CGc24; exact CGH).
  assert (INP_v1_24 : In (v1, 24) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v1_22).
  assert (INP_v2_24 : In (v2, 384) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v2_22).
  assert (INP_v3_24 : In (v3, 32) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v3_22).
  assert (INP_v4_24 : In (v4, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v4_22).
  assert (INP_v5_24 : In (v5, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v5_22).
  assert (INP_v6_24 : In (v6, 32) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v6_22).
  assert (INP_v7_24 : In (v7, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v7_22).
  assert (INP_v8_24 : In (v8, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v8_22).
  assert (INP_v9_24 : In (v9, 32) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v9_22).
  assert (INP_v10_24 : In (v10, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v10_22).
  assert (INP_v11_24 : In (v11, 40) (rt_live RT Σ12)) by (rewrite LV24; do 1 right; exact INP_v11_22).
  assert (INP_v12_24 : In (v12, 32) (rt_live RT Σ12)) by (rewrite LV24; left; reflexivity).
  pose proof (af_live_range RT AF Σ12 m24 v12 32 ART24 INP_v12_24) as (_ & PHI_v12 & _). rewrite SPc24 in PHI_v12.
  pose proof (afp_live_mem RT GOBJ AFP Σ12 m24 v12 32 ART24 INP_v12_24 ltac:(lia)) as (_ & PT_v12).
  pose proof (afp_live_hi RT GOBJ AFP Σ12 m24 v12 32 ART24 INP_v12_24 ltac:(lia)) as PHH_v12.
  pose proof (wg_mod16_8 _ P16_v12) as PAL_v12. assert (PR64_v12 : 0 <= v12 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v12 : v12 + 32 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v12. wp_box1 PAL_v12. wp_box1 PR64_v12.
  destruct (af_client_consts RT AF Σ12 m24 ART24) as (_ & SHC24 & _ & _ & UT24).
  pose proof (af_acc_live RT AF Σ12 m24 v12 32 ART24 INP_v12_24) as (WR_v12_24 & ACC_v12_24).
  pose proof (wp_zero_rw_CB asegs m24 v12 32 G12_ZER WR_v12_24 ltac:(lia)) as HBZ_v12_24. change (Z.to_nat 32) with 32%nat in HBZ_v12_24.
  pose proof (af_acc_live RT AF Σ12 m24 v2 384 ART24 INP_v2_24) as (WR_v2_25 & ACC_v2_25).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s12_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_3) u0_12 u1_12 u2_12 b1_12 b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 u3_12 u4_12 u5_12 u6_12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 F12 fc12 m24 lo
                ST24 WHLO WHIMG WHTOP KF123 KF124 KF125 SHC24 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 PR64_v11 PR64_v12 UT24 ACC_v2_25 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI24) as W25.
  cl_lift W25 Hc24' c25 Hc25.
  destruct (ASTA_unpack RT Σ12 _ _ c25 Hc25) as (ms25 & (m25 & -> & MU25 & WM25 & MI25 & H25_0 & H25_1 & H25_2 & H25_3 & ST25) & Hc25'). clear Hc25.
  fold usp in MU25, ST25, Hc25', H25_2.
  assert (ART25 : ART RT Σ12 m25).
  { apply (wg_seg_ART RT AF Σ12 m24 m25 usp 64 [(v2, v2 + 384)] ART24 ltac:(rewrite SPc24; lia) ltac:(lia) MU25); [|exact WM25].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_24 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF136 : rw_cells asegs m25 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m24 m25 _ _ KF127 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF137 : rw_cells asegs m25 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m24 m25 _ _ KF128 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF138 : rw_cells asegs m25 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m24 m25 _ _ KF129 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF139 : rw_cells asegs m25 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m24 m25 _ _ KF130 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF140 : rw_cells asegs m25 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m24 m25 _ _ KF131 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF141 : rw_cells asegs m25 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m24 m25 _ _ KF132 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF142 : rw_cells asegs m25 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; apply (wg_keep_seg _ m24 m25 _ _ KF133 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF143 : rw_cells asegs m25 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v2 384 ART20 LV20 ltac:(cbn [app In]; exact INP_v2_18)) as DJ_v10_v2; apply (wg_keep_seg _ m24 m25 _ _ KF134 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v10_v2 PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF144 : rw_cells asegs m25 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v2 384 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_20)) as DJ_v11_v2; apply (wg_keep_seg _ m24 m25 _ _ KF135 MU25 WM25); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF145 : rw_cells asegs m25 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ12 m24 [] v12 32 (rt_live RT Σ11) v2 384 ART24 LV24 ltac:(cbn [app In]; exact INP_v2_22)) as DJ_v12_v2; apply (wg_keep_seg _ m24 m25 _ _ HBZ_v12_24 MU25 WM25); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v12_v2 PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m24 m25 _ canary G12_ENVp MU25 ltac:(cl_fp_lia)) as ENV25.
  assert (AGs25 : agree_on (fun x => usp <= x < USTACK_TOP) m24 m25) by (intros a Ha; apply MU25; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m24 m25 sp s0 UWF24 AGs25) as UWF25.
  destruct (cl_chain_call (rt_cg RT Σ12) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_4 m25 m25 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb24
              (proj1 CGH24 (SITE_ossl_method_store_new_4, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH24 (SITE_ossl_method_store_new_4, e_lock_new) ltac:(wp_in_lit)) UWF25 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m25 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H25_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc25 & UWCc25).
  (* [comment removed for export] *)
  apply (C_lock_new Σ12 PMc (Z_to_bv 64 SITE_ossl_method_store_new_4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_12 u1_12 u2_12 sp (Z_to_bv 64 v1) (Z_to_bv 64 v12) (Z_to_bv 64 0) b2_12 b3_12 b4_12 b5_12 b6_12 b7_12 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_12 u4_12 u5_12 u6_12
           F12 fc12 m25 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART25 MI25).
  { fold usp in SPA. cl_call_ok EU1 ST25 LOW24 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_4) by (unfold SITE_ossl_method_store_new_4; lia). exact CTXc25. }
  { exact UWCc25. }
  { apply (cg_has_weaken _ _ _ _ _ CGH24); vm_compute; reflexivity. }
  { exact Hfr24. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV25. }
  { exact Hc25'. }
  clear Hc25'. intros c26 (Σ13 & v13 & Hc26 & LV26 & FRS26 & SP26 & CR26 & P0_v13 & P16_v13 & PU_v13 & CG26).
  wp_box1 PU_v13.
  destruct (ASTA_unpack RT Σ13 _ _ c26 Hc26) as (ms26 & (m26 & RS26 & (ART26 & MI26 & WM26 & ST26) & PRES26 & G13_ENVp & G13_MX & G13_ACC) & Hc26'). clear Hc26.
  destruct RS26 as (u0_13 & u1_13 & u2_13 & b1_13 & b2_13 & b3_13 & b4_13 & b5_13 & b6_13 & b7_13 & u3_13 & u4_13 & u5_13 & u6_13 & F13 & fc13 & ->).
  rewrite EU1 in ST26, PRES26. rewrite (ret_pc_even SITE_ossl_method_store_new_4) in Hc26' by (unfold SITE_ossl_method_store_new_4; clear; first [reflexivity | lia]).
  assert (AGc26 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m25 m26).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES26; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu26 : agree_on (fun x => usp <= x < USTACK_TOP) m25 m26) by (intros a Ha; exact (AGc26 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m25 m26 sp s0 UWF25 AGu26) as UWF26.
  assert (KF146 : rw_cells asegs m26 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 88 (repeat (Z_to_bv 8 0) 88)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v2 384 _ _ H25_0 PRES26 WM26 INP_v2_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF147 : rw_cells asegs m26 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v1 24 _ _ H25_1 PRES26 WM26 INP_v1_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H25_2 AGc26 WM26 KF148.
  assert (KF150 : rw_cells asegs m26 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v3 32 _ _ KF136 PRES26 WM26 INP_v3_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF151 : rw_cells asegs m26 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v4 40 _ _ KF137 PRES26 WM26 INP_v4_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF152 : rw_cells asegs m26 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v5 40 _ _ KF138 PRES26 WM26 INP_v5_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF153 : rw_cells asegs m26 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v6 32 _ _ KF139 PRES26 WM26 INP_v6_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF154 : rw_cells asegs m26 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v7 40 _ _ KF140 PRES26 WM26 INP_v7_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF155 : rw_cells asegs m26 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v8 40 _ _ KF141 PRES26 WM26 INP_v8_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF156 : rw_cells asegs m26 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v9 32 _ _ KF142 PRES26 WM26 INP_v9_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF157 : rw_cells asegs m26 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v10 40 _ _ KF143 PRES26 WM26 INP_v10_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF158 : rw_cells asegs m26 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m25 m26 v11 40 _ _ KF144 PRES26 WM26 INP_v11_24); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF159 : rw_cells asegs m26 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m25 m26 v12 32 _ _ KF145 PRES26 WM26 INP_v12_24); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc26 : rt_sp0 RT Σ13 = rt_sp0 RT Σ) by (rewrite SP26; exact SPc24).
  assert (CGc26 : rt_cg RT Σ13 = rt_cg RT Σ) by (rewrite CG26; exact CGc24).
  assert (LOW26 : rt_sp0 RT Σ13 - STACK_WIN <= lo) by (rewrite SPc26; exact LOW).
  assert (LEN26 : Z.of_nat (length (rt_live RT Σ13)) = Z.of_nat (length (rt_live RT Σ12)) + 1) by (rewrite LV26; cbn [length]; lia).
  assert (LENc26 : Z.of_nat (length (rt_live RT Σ13)) = Z.of_nat (length (rt_live RT Σ)) + 13) by lia. clear LENc24. wp_box1 LEN24. wp_box1 CR26.
  assert (Hfr26 : (length (rt_frames RT Σ13) < FRAMES_MAX)%nat) by (rewrite FRS26; exact Hfr24).
  assert (CTXb26 : cg_ctx (rt_cg RT Σ13) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc26; exact CTX).
  assert (CGH26 : cg_has (rt_cg RT Σ13) _ _) by (rewrite CGc26; exact CGH).
  assert (INP_v1_26 : In (v1, 24) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v1_24).
  assert (INP_v2_26 : In (v2, 384) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v2_24).
  assert (INP_v3_26 : In (v3, 32) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v3_24).
  assert (INP_v4_26 : In (v4, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v4_24).
  assert (INP_v5_26 : In (v5, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v5_24).
  assert (INP_v6_26 : In (v6, 32) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v6_24).
  assert (INP_v7_26 : In (v7, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v7_24).
  assert (INP_v8_26 : In (v8, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v8_24).
  assert (INP_v9_26 : In (v9, 32) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v9_24).
  assert (INP_v10_26 : In (v10, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v10_24).
  assert (INP_v11_26 : In (v11, 40) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v11_24).
  assert (INP_v12_26 : In (v12, 32) (rt_live RT Σ13)) by (rewrite LV26; do 1 right; exact INP_v12_24).
  assert (INP_v13_26 : In (v13, 40) (rt_live RT Σ13)) by (rewrite LV26; left; reflexivity).
  pose proof (af_live_range RT AF Σ13 m26 v13 40 ART26 INP_v13_26) as (_ & PHI_v13 & _). rewrite SPc26 in PHI_v13.
  pose proof (afp_live_mem RT GOBJ AFP Σ13 m26 v13 40 ART26 INP_v13_26 ltac:(lia)) as (_ & PT_v13).
  pose proof (afp_live_hi RT GOBJ AFP Σ13 m26 v13 40 ART26 INP_v13_26 ltac:(lia)) as PHH_v13.
  pose proof (wg_mod16_8 _ P16_v13) as PAL_v13. assert (PR64_v13 : 0 <= v13 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v13 : v13 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v13. wp_box1 PAL_v13. wp_box1 PR64_v13.
  destruct (af_client_consts RT AF Σ13 m26 ART26) as (_ & SHC26 & _ & _ & UT26).
  pose proof (af_acc_live RT AF Σ13 m26 v2 384 ART26 INP_v2_26) as (WR_v2_27 & ACC_v2_27).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s13_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_4) u0_13 u1_13 u2_13 b1_13 b2_13 b3_13 b4_13 b5_13 b6_13 b7_13 u3_13 u4_13 u5_13 u6_13 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 F13 fc13 m26 lo
                ST26 WHLO WHIMG WHTOP KF146 KF147 KF148 SHC26 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 PR64_v11 PR64_v12 PR64_v13 UT26 ACC_v2_27 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI26) as W27.
  cl_lift W27 Hc26' c27 Hc27.
  destruct (ASTA_unpack RT Σ13 _ _ c27 Hc27) as (ms27 & (m27 & -> & MU27 & WM27 & MI27 & H27_0 & H27_1 & H27_2 & H27_3 & ST27) & Hc27'). clear Hc27.
  fold usp in MU27, ST27, Hc27', H27_2.
  assert (ART27 : ART RT Σ13 m27).
  { apply (wg_seg_ART RT AF Σ13 m26 m27 usp 64 [(v2, v2 + 384)] ART26 ltac:(rewrite SPc26; lia) ltac:(lia) MU27); [|exact WM27].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_26 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF160 : rw_cells asegs m27 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; apply (wg_keep_seg _ m26 m27 _ _ KF150 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF161 : rw_cells asegs m27 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; apply (wg_keep_seg _ m26 m27 _ _ KF151 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF162 : rw_cells asegs m27 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; apply (wg_keep_seg _ m26 m27 _ _ KF152 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF163 : rw_cells asegs m27 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; apply (wg_keep_seg _ m26 m27 _ _ KF153 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF164 : rw_cells asegs m27 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; apply (wg_keep_seg _ m26 m27 _ _ KF154 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF165 : rw_cells asegs m27 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; apply (wg_keep_seg _ m26 m27 _ _ KF155 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF166 : rw_cells asegs m27 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; apply (wg_keep_seg _ m26 m27 _ _ KF156 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF167 : rw_cells asegs m27 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v2 384 ART20 LV20 ltac:(cbn [app In]; exact INP_v2_18)) as DJ_v10_v2; apply (wg_keep_seg _ m26 m27 _ _ KF157 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v10_v2 PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF168 : rw_cells asegs m27 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v2 384 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_20)) as DJ_v11_v2; apply (wg_keep_seg _ m26 m27 _ _ KF158 MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF169 : rw_cells asegs m27 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ12 m24 [] v12 32 (rt_live RT Σ11) v2 384 ART24 LV24 ltac:(cbn [app In]; exact INP_v2_22)) as DJ_v12_v2; apply (wg_keep_seg _ m26 m27 _ _ KF159 MU27 WM27); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v12_v2 PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF170 : rw_cells asegs m27 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ13 m26 [] v13 40 (rt_live RT Σ12) v2 384 ART26 LV26 ltac:(cbn [app In]; exact INP_v2_24)) as DJ_v13_v2; apply (wg_keep_seg _ m26 m27 _ _ G13_MX MU27 WM27); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v13_v2 PHI_v13 PT_v13 PHH_v13 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m26 m27 _ canary G13_ENVp MU27 ltac:(cl_fp_lia)) as ENV27.
  assert (AGs27 : agree_on (fun x => usp <= x < USTACK_TOP) m26 m27) by (intros a Ha; apply MU27; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m26 m27 sp s0 UWF26 AGs27) as UWF27.
  destruct (cl_chain_call (rt_cg RT Σ13) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_5 m27 m27 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb26
              (proj1 CGH26 (SITE_ossl_method_store_new_5, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH26 (SITE_ossl_method_store_new_5, e_lock_new) ltac:(wp_in_lit)) UWF27 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m27 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H27_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc27 & UWCc27).
  (* [comment removed for export] *)
  apply (C_lock_new Σ13 PMc (Z_to_bv 64 SITE_ossl_method_store_new_5) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_13 u1_13 u2_13 sp (Z_to_bv 64 v1) (Z_to_bv 64 v13) (Z_to_bv 64 (v2 + 368)) (Z_to_bv 64 0) b3_13 b4_13 b5_13 b6_13 b7_13 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 288)) (Z_to_bv 64 2147450880) (Z_to_bv 64 1) (Z_to_bv 64 (v2 + 376)) s7 s8 s9 s10 s11 u3_13 u4_13 u5_13 u6_13
           F13 fc13 m27 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART27 MI27).
  { fold usp in SPA. cl_call_ok EU1 ST27 LOW26 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_5) by (unfold SITE_ossl_method_store_new_5; lia). exact CTXc27. }
  { exact UWCc27. }
  { apply (cg_has_weaken _ _ _ _ _ CGH26); vm_compute; reflexivity. }
  { exact Hfr26. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV27. }
  { exact Hc27'. }
  clear Hc27'. intros c28 (Σ14 & v14 & Hc28 & LV28 & FRS28 & SP28 & CR28 & P0_v14 & P16_v14 & PU_v14 & CG28).
  wp_box1 PU_v14.
  destruct (ASTA_unpack RT Σ14 _ _ c28 Hc28) as (ms28 & (m28 & RS28 & (ART28 & MI28 & WM28 & ST28) & PRES28 & G14_ENVp & G14_MX & G14_ACC) & Hc28'). clear Hc28.
  destruct RS28 as (u0_14 & u1_14 & u2_14 & b1_14 & b2_14 & b3_14 & b4_14 & b5_14 & b6_14 & b7_14 & u3_14 & u4_14 & u5_14 & u6_14 & F14 & fc14 & ->).
  rewrite EU1 in ST28, PRES28. rewrite (ret_pc_even SITE_ossl_method_store_new_5) in Hc28' by (unfold SITE_ossl_method_store_new_5; clear; first [reflexivity | lia]).
  assert (AGc28 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m27 m28).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES28; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu28 : agree_on (fun x => usp <= x < USTACK_TOP) m27 m28) by (intros a Ha; exact (AGc28 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m27 m28 sp s0 UWF27 AGu28) as UWF28.
  assert (KF171 : rw_cells asegs m28 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v2 384 _ _ H27_0 PRES28 WM28 INP_v2_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF172 : rw_cells asegs m28 v1 [C8 a0; CB 16 (repeat (Z_to_bv 8 0) 16)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v1 24 _ _ H27_1 PRES28 WM28 INP_v1_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H27_2 AGc28 WM28 KF173.
  assert (KF175 : rw_cells asegs m28 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v3 32 _ _ KF160 PRES28 WM28 INP_v3_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF176 : rw_cells asegs m28 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v4 40 _ _ KF161 PRES28 WM28 INP_v4_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF177 : rw_cells asegs m28 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v5 40 _ _ KF162 PRES28 WM28 INP_v5_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF178 : rw_cells asegs m28 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v6 32 _ _ KF163 PRES28 WM28 INP_v6_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF179 : rw_cells asegs m28 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v7 40 _ _ KF164 PRES28 WM28 INP_v7_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF180 : rw_cells asegs m28 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v8 40 _ _ KF165 PRES28 WM28 INP_v8_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF181 : rw_cells asegs m28 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v9 32 _ _ KF166 PRES28 WM28 INP_v9_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF182 : rw_cells asegs m28 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v10 40 _ _ KF167 PRES28 WM28 INP_v10_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF183 : rw_cells asegs m28 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v11 40 _ _ KF168 PRES28 WM28 INP_v11_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF184 : rw_cells asegs m28 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m27 m28 v12 32 _ _ KF169 PRES28 WM28 INP_v12_26); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF185 : rw_cells asegs m28 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m27 m28 v13 40 _ _ KF170 PRES28 WM28 INP_v13_26); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v13 PT_v13 PHH_v13 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc28 : rt_sp0 RT Σ14 = rt_sp0 RT Σ) by (rewrite SP28; exact SPc26).
  assert (CGc28 : rt_cg RT Σ14 = rt_cg RT Σ) by (rewrite CG28; exact CGc26).
  assert (LOW28 : rt_sp0 RT Σ14 - STACK_WIN <= lo) by (rewrite SPc28; exact LOW).
  assert (LEN28 : Z.of_nat (length (rt_live RT Σ14)) = Z.of_nat (length (rt_live RT Σ13)) + 1) by (rewrite LV28; cbn [length]; lia).
  assert (LENc28 : Z.of_nat (length (rt_live RT Σ14)) = Z.of_nat (length (rt_live RT Σ)) + 14) by lia. clear LENc26. wp_box1 LEN26. wp_box1 CR28.
  assert (Hfr28 : (length (rt_frames RT Σ14) < FRAMES_MAX)%nat) by (rewrite FRS28; exact Hfr26).
  assert (CTXb28 : cg_ctx (rt_cg RT Σ14) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc28; exact CTX).
  assert (CGH28 : cg_has (rt_cg RT Σ14) _ _) by (rewrite CGc28; exact CGH).
  assert (INP_v1_28 : In (v1, 24) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v1_26).
  assert (INP_v2_28 : In (v2, 384) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v2_26).
  assert (INP_v3_28 : In (v3, 32) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v3_26).
  assert (INP_v4_28 : In (v4, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v4_26).
  assert (INP_v5_28 : In (v5, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v5_26).
  assert (INP_v6_28 : In (v6, 32) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v6_26).
  assert (INP_v7_28 : In (v7, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v7_26).
  assert (INP_v8_28 : In (v8, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v8_26).
  assert (INP_v9_28 : In (v9, 32) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v9_26).
  assert (INP_v10_28 : In (v10, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v10_26).
  assert (INP_v11_28 : In (v11, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v11_26).
  assert (INP_v12_28 : In (v12, 32) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v12_26).
  assert (INP_v13_28 : In (v13, 40) (rt_live RT Σ14)) by (rewrite LV28; do 1 right; exact INP_v13_26).
  assert (INP_v14_28 : In (v14, 40) (rt_live RT Σ14)) by (rewrite LV28; left; reflexivity).
  pose proof (af_live_range RT AF Σ14 m28 v14 40 ART28 INP_v14_28) as (_ & PHI_v14 & _). rewrite SPc28 in PHI_v14.
  pose proof (afp_live_mem RT GOBJ AFP Σ14 m28 v14 40 ART28 INP_v14_28 ltac:(lia)) as (_ & PT_v14).
  pose proof (afp_live_hi RT GOBJ AFP Σ14 m28 v14 40 ART28 INP_v14_28 ltac:(lia)) as PHH_v14.
  pose proof (wg_mod16_8 _ P16_v14) as PAL_v14. assert (PR64_v14 : 0 <= v14 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v14 : v14 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v14. wp_box1 PAL_v14. wp_box1 PR64_v14.
  destruct (af_client_consts RT AF Σ14 m28 ART28) as (_ & SHC28 & _ & _ & UT28).
  pose proof (af_acc_live RT AF Σ14 m28 v1 24 ART28 INP_v1_28) as (WR_v1_29 & ACC_v1_29).
  pose proof (af_acc_live RT AF Σ14 m28 v2 384 ART28 INP_v2_28) as (WR_v2_29 & ACC_v2_29).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s14_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_5) u0_14 u1_14 u2_14 b1_14 b2_14 b3_14 b4_14 b5_14 b6_14 b7_14 u3_14 u4_14 u5_14 u6_14 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 F14 fc14 m28 lo
                ST28 WHLO WHIMG WHTOP KF171 KF172 KF173 SHC28 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 PR64_v11 PR64_v12 PR64_v13 PR64_v14 UT28 ACC_v1_29 PAL_v1 PHH_v1 PT_v1 PSTK_v1 ACC_v2_29 PAL_v2 PHH_v2 PT_v2 PSTK_v2 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI28) as W29.
  cl_lift W29 Hc28' c29 Hc29.
  destruct (ASTA_unpack RT Σ14 _ _ c29 Hc29) as (ms29 & (m29 & -> & MU29 & WM29 & MI29 & H29_0 & H29_1 & H29_2 & H29_3 & ST29) & Hc29'). clear Hc29.
  fold usp in MU29, ST29, Hc29', H29_2.
  assert (ART29 : ART RT Σ14 m29).
  { apply (wg_seg_ART RT AF Σ14 m28 m29 usp 64 [(v2, v2 + 384); (v1, v1 + 24)] ART28 ltac:(rewrite SPc28; lia) ltac:(lia) MU29); [|exact WM29].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v2, 384; split; [exact INP_v2_28 | lia] | clear Hx; rename Hx2 into Hx]. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 24; split; [exact INP_v1_28 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  assert (KF186 : rw_cells asegs m29 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v2 384 ART6 LV6 ltac:(cbn [app In]; exact INP_v2_4)) as DJ_v3_v2; pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v1 24 ART6 LV6 ltac:(cbn [app In]; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m28 m29 _ _ KF175 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v3_v2 DJ_v3_v1 PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF187 : rw_cells asegs m29 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v2 384 ART8 LV8 ltac:(cbn [app In]; exact INP_v2_6)) as DJ_v4_v2; pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v1 24 ART8 LV8 ltac:(cbn [app In]; exact INP_v1_6)) as DJ_v4_v1; apply (wg_keep_seg _ m28 m29 _ _ KF176 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v4_v2 DJ_v4_v1 PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF188 : rw_cells asegs m29 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v2 384 ART10 LV10 ltac:(cbn [app In]; exact INP_v2_8)) as DJ_v5_v2; pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v1 24 ART10 LV10 ltac:(cbn [app In]; exact INP_v1_8)) as DJ_v5_v1; apply (wg_keep_seg _ m28 m29 _ _ KF177 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v5_v2 DJ_v5_v1 PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF189 : rw_cells asegs m29 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v2 384 ART12 LV12 ltac:(cbn [app In]; exact INP_v2_10)) as DJ_v6_v2; pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v1 24 ART12 LV12 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v6_v1; apply (wg_keep_seg _ m28 m29 _ _ KF178 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v6_v2 DJ_v6_v1 PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF190 : rw_cells asegs m29 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v2 384 ART14 LV14 ltac:(cbn [app In]; exact INP_v2_12)) as DJ_v7_v2; pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v1 24 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_seg _ m28 m29 _ _ KF179 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v7_v2 DJ_v7_v1 PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF191 : rw_cells asegs m29 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v2 384 ART16 LV16 ltac:(cbn [app In]; exact INP_v2_14)) as DJ_v8_v2; pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v1 24 ART16 LV16 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v8_v1; apply (wg_keep_seg _ m28 m29 _ _ KF180 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v8_v2 DJ_v8_v1 PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF192 : rw_cells asegs m29 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v2 384 ART18 LV18 ltac:(cbn [app In]; exact INP_v2_16)) as DJ_v9_v2; pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v1 24 ART18 LV18 ltac:(cbn [app In]; exact INP_v1_16)) as DJ_v9_v1; apply (wg_keep_seg _ m28 m29 _ _ KF181 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v9_v2 DJ_v9_v1 PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF193 : rw_cells asegs m29 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v2 384 ART20 LV20 ltac:(cbn [app In]; exact INP_v2_18)) as DJ_v10_v2; pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v1 24 ART20 LV20 ltac:(cbn [app In]; exact INP_v1_18)) as DJ_v10_v1; apply (wg_keep_seg _ m28 m29 _ _ KF182 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v10_v2 DJ_v10_v1 PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF194 : rw_cells asegs m29 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v2 384 ART22 LV22 ltac:(cbn [app In]; exact INP_v2_20)) as DJ_v11_v2; pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v1 24 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_20)) as DJ_v11_v1; apply (wg_keep_seg _ m28 m29 _ _ KF183 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v11_v2 DJ_v11_v1 PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF195 : rw_cells asegs m29 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (pose proof (wg_live_apart RT AF Σ12 m24 [] v12 32 (rt_live RT Σ11) v2 384 ART24 LV24 ltac:(cbn [app In]; exact INP_v2_22)) as DJ_v12_v2; pose proof (wg_live_apart RT AF Σ12 m24 [] v12 32 (rt_live RT Σ11) v1 24 ART24 LV24 ltac:(cbn [app In]; exact INP_v1_22)) as DJ_v12_v1; apply (wg_keep_seg _ m28 m29 _ _ KF184 MU29 WM29); intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v12_v2 DJ_v12_v1 PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF196 : rw_cells asegs m29 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ13 m26 [] v13 40 (rt_live RT Σ12) v2 384 ART26 LV26 ltac:(cbn [app In]; exact INP_v2_24)) as DJ_v13_v2; pose proof (wg_live_apart RT AF Σ13 m26 [] v13 40 (rt_live RT Σ12) v1 24 ART26 LV26 ltac:(cbn [app In]; exact INP_v1_24)) as DJ_v13_v1; apply (wg_keep_seg _ m28 m29 _ _ KF185 MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v13_v2 DJ_v13_v1 PHI_v13 PT_v13 PHH_v13 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  assert (KF197 : rw_cells asegs m29 v14 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (pose proof (wg_live_apart RT AF Σ14 m28 [] v14 40 (rt_live RT Σ13) v2 384 ART28 LV28 ltac:(cbn [app In]; exact INP_v2_26)) as DJ_v14_v2; pose proof (wg_live_apart RT AF Σ14 m28 [] v14 40 (rt_live RT Σ13) v1 24 ART28 LV28 ltac:(cbn [app In]; exact INP_v1_26)) as DJ_v14_v1; apply (wg_keep_seg _ m28 m29 _ _ G14_MX MU29 WM29); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx DJ_v14_v2 DJ_v14_v1 PHI_v14 PT_v14 PHH_v14 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]).
  pose proof (cl_env_seg _ m28 m29 _ canary G14_ENVp MU29 ltac:(cl_fp_lia)) as ENV29.
  assert (AGs29 : agree_on (fun x => usp <= x < USTACK_TOP) m28 m29) by (intros a Ha; apply MU29; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I).
  pose proof (uw_chain_agree outer m28 m29 sp s0 UWF28 AGs29) as UWF29.
  destruct (cl_chain_call (rt_cg RT Σ14) e_ossl_method_store_new e_lock_new SITE_ossl_method_store_new_6 m29 m29 ra s0 sp (Z_to_bv 64 (usp + -64)) outer CTXb28
              (proj1 CGH28 (SITE_ossl_method_store_new_6, e_ossl_method_store_new) ltac:(wp_in_lit)) (proj2 CGH28 (SITE_ossl_method_store_new_6, e_lock_new) ltac:(wp_in_lit)) UWF29 ltac:(intros a _; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (usp + -64 + Z.of_nat (cells_size [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m29 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] H29_2))
              ltac:(rewrite EU1; fold usp; lia) SPT) as (CTXc29 & UWCc29).
  (* [comment removed for export] *)
  apply (C_lock_new Σ14 PMc (Z_to_bv 64 SITE_ossl_method_store_new_6) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0xba3ef0) u0_14 u1_14 u2_14 sp (Z_to_bv 64 v1) (Z_to_bv 64 (v1 + 8)) (Z_to_bv 64 0) (Z_to_bv 64 0) b3_14 b4_14 b5_14 b6_14 b7_14 (Z_to_bv 64 v2) (Z_to_bv 64 (v2 + 384)) (Z_to_bv 64 2147450880) (Z_to_bv 64 0) (Z_to_bv 64 (v2 + 472)) s7 s8 s9 s10 s11 u3_14 u4_14 u5_14 u6_14
           F14 fc14 m29 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary FDO MST eq_refl ART29 MI29).
  { fold usp in SPA. cl_call_ok EU1 ST29 LOW28 SPA 4. }
  { rewrite EU1. unfold RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ossl_method_store_new_6) by (unfold SITE_ossl_method_store_new_6; lia). exact CTXc29. }
  { exact UWCc29. }
  { apply (cg_has_weaken _ _ _ _ _ CGH28); vm_compute; reflexivity. }
  { exact Hfr28. }
  { lia. }
  { (repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia. }
  { exact ENV29. }
  { exact Hc29'. }
  clear Hc29'. intros c30 (Σ15 & v15 & Hc30 & LV30 & FRS30 & SP30 & CR30 & P0_v15 & P16_v15 & PU_v15 & CG30).
  wp_box1 PU_v15.
  destruct (ASTA_unpack RT Σ15 _ _ c30 Hc30) as (ms30 & (m30 & RS30 & (ART30 & MI30 & WM30 & ST30) & PRES30 & G15_ENVp & G15_MX & G15_ACC) & Hc30'). clear Hc30.
  destruct RS30 as (u0_15 & u1_15 & u2_15 & b1_15 & b2_15 & b3_15 & b4_15 & b5_15 & b6_15 & b7_15 & u3_15 & u4_15 & u5_15 & u6_15 & F15 & fc15 & ->).
  rewrite EU1 in ST30, PRES30. rewrite (ret_pc_even SITE_ossl_method_store_new_6) in Hc30' by (unfold SITE_ossl_method_store_new_6; clear; first [reflexivity | lia]).
  assert (AGc30 : forall a k, usp + -64 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m29 m30).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES30; [left; lia|]. cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I. }
  assert (AGu30 : agree_on (fun x => usp <= x < USTACK_TOP) m29 m30) by (intros a Ha; exact (AGc30 (bv_unsigned a) 1 ltac:(lia) ltac:(lia) a ltac:(lia))).
  pose proof (uw_chain_agree outer m29 m30 sp s0 UWF29 AGu30) as UWF30.
  assert (KF198 : rw_cells asegs m30 v1 [C8 a0; C8 (Z_to_bv 64 v2); CB 8 (repeat (Z_to_bv 8 0) 8)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v1 24 _ _ H29_0 PRES30 WM30 INP_v1_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v1 PT_v1 PHH_v1 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF199 : rw_cells asegs m30 v2 [C8 (Z_to_bv 64 v3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v4); C8 (Z_to_bv 64 v5); C8 (Z_to_bv 64 v6); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v7); C8 (Z_to_bv 64 v8); C8 (Z_to_bv 64 v9); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v10); C8 (Z_to_bv 64 v11); C8 (Z_to_bv 64 v12); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 v13); C8 (Z_to_bv 64 v14)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v2 384 _ _ H29_1 PRES30 WM30 INP_v2_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v2 PT_v2 PHH_v2 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  cl_keep H29_2 AGc30 WM30 KF200.
  assert (KF202 : rw_cells asegs m30 v3 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v3 32 _ _ KF186 PRES30 WM30 INP_v3_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v3 PT_v3 PHH_v3 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF203 : rw_cells asegs m30 v4 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v4 40 _ _ KF187 PRES30 WM30 INP_v4_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v4 PT_v4 PHH_v4 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF204 : rw_cells asegs m30 v5 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v5 40 _ _ KF188 PRES30 WM30 INP_v5_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v5 PT_v5 PHH_v5 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF205 : rw_cells asegs m30 v6 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v6 32 _ _ KF189 PRES30 WM30 INP_v6_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v6 PT_v6 PHH_v6 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF206 : rw_cells asegs m30 v7 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v7 40 _ _ KF190 PRES30 WM30 INP_v7_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v7 PT_v7 PHH_v7 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF207 : rw_cells asegs m30 v8 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v8 40 _ _ KF191 PRES30 WM30 INP_v8_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v8 PT_v8 PHH_v8 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF208 : rw_cells asegs m30 v9 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v9 32 _ _ KF192 PRES30 WM30 INP_v9_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v9 PT_v9 PHH_v9 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF209 : rw_cells asegs m30 v10 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v10 40 _ _ KF193 PRES30 WM30 INP_v10_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v10 PT_v10 PHH_v10 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF210 : rw_cells asegs m30 v11 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v11 40 _ _ KF194 PRES30 WM30 INP_v11_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v11 PT_v11 PHH_v11 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF211 : rw_cells asegs m30 v12 [CB 32 (repeat (Z_to_bv 8 0) 32)]) by (apply (wg_keep_live _ _ _ _ m29 m30 v12 32 _ _ KF195 PRES30 WM30 INP_v12_28); [lia | cbn [cells_size csize Nat.add]; lia | intros x Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v12 PT_v12 PHH_v12 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF212 : rw_cells asegs m30 v13 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v13 40 _ _ KF196 PRES30 WM30 INP_v13_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v13 PT_v13 PHH_v13 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (KF213 : rw_cells asegs m30 v14 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))) by (apply (wg_keep_live _ _ _ _ m29 m30 v14 40 _ _ KF197 PRES30 WM30 INP_v14_28); [lia | unfold mutex_cells; cbn [cells_size csize Nat.add]; lia | intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; first [ clear - Hx PHI_v14 PT_v14 PHH_v14 NUM; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I | cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I ]]).
  assert (SPc30 : rt_sp0 RT Σ15 = rt_sp0 RT Σ) by (rewrite SP30; exact SPc28).
  assert (CGc30 : rt_cg RT Σ15 = rt_cg RT Σ) by (rewrite CG30; exact CGc28).
  assert (LOW30 : rt_sp0 RT Σ15 - STACK_WIN <= lo) by (rewrite SPc30; exact LOW).
  assert (LEN30 : Z.of_nat (length (rt_live RT Σ15)) = Z.of_nat (length (rt_live RT Σ14)) + 1) by (rewrite LV30; cbn [length]; lia).
  assert (LENc30 : Z.of_nat (length (rt_live RT Σ15)) = Z.of_nat (length (rt_live RT Σ)) + 15) by lia. clear LENc28. wp_box1 LEN28. wp_box1 CR30.
  assert (Hfr30 : (length (rt_frames RT Σ15) < FRAMES_MAX)%nat) by (rewrite FRS30; exact Hfr28).
  assert (CTXb30 : cg_ctx (rt_cg RT Σ15) e_ossl_method_store_new (bv_unsigned ra :: outer)) by (rewrite CGc30; exact CTX).
  assert (CGH30 : cg_has (rt_cg RT Σ15) _ _) by (rewrite CGc30; exact CGH).
  assert (INP_v1_30 : In (v1, 24) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v1_28).
  assert (INP_v2_30 : In (v2, 384) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v2_28).
  assert (INP_v3_30 : In (v3, 32) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v3_28).
  assert (INP_v4_30 : In (v4, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v4_28).
  assert (INP_v5_30 : In (v5, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v5_28).
  assert (INP_v6_30 : In (v6, 32) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v6_28).
  assert (INP_v7_30 : In (v7, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v7_28).
  assert (INP_v8_30 : In (v8, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v8_28).
  assert (INP_v9_30 : In (v9, 32) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v9_28).
  assert (INP_v10_30 : In (v10, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v10_28).
  assert (INP_v11_30 : In (v11, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v11_28).
  assert (INP_v12_30 : In (v12, 32) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v12_28).
  assert (INP_v13_30 : In (v13, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v13_28).
  assert (INP_v14_30 : In (v14, 40) (rt_live RT Σ15)) by (rewrite LV30; do 1 right; exact INP_v14_28).
  assert (INP_v15_30 : In (v15, 40) (rt_live RT Σ15)) by (rewrite LV30; left; reflexivity).
  pose proof (af_live_range RT AF Σ15 m30 v15 40 ART30 INP_v15_30) as (_ & PHI_v15 & _). rewrite SPc30 in PHI_v15.
  pose proof (afp_live_mem RT GOBJ AFP Σ15 m30 v15 40 ART30 INP_v15_30 ltac:(lia)) as (_ & PT_v15).
  pose proof (afp_live_hi RT GOBJ AFP Σ15 m30 v15 40 ART30 INP_v15_30 ltac:(lia)) as PHH_v15.
  pose proof (wg_mod16_8 _ P16_v15) as PAL_v15. assert (PR64_v15 : 0 <= v15 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_v15 : v15 + 40 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_v15. wp_box1 PAL_v15. wp_box1 PR64_v15.
  destruct (af_client_consts RT AF Σ15 m30 ART30) as (_ & SHC30 & _ & _ & UT30).
  pose proof (af_acc_live RT AF Σ15 m30 v1 24 ART30 INP_v1_30) as (WR_v1_31 & ACC_v1_31).
  try (pose proof (wg_live_apart RT AF Σ2 m4 [] v2 384 (rt_live RT Σ1) v1 24 ART4 LV4 ltac:(cbn [app In]; exact INP_v1_2)) as DJ_v2_v1; idtac).
  (* [comment removed for export] *)
  pose proof (ossl_method_store_new_s15_walk ra sp gp (Z_to_bv 64 0xba3ef0) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SITE_ossl_method_store_new_6) u0_15 u1_15 u2_15 b1_15 b2_15 b3_15 b4_15 b5_15 b6_15 b7_15 u3_15 u4_15 u5_15 u6_15 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 F15 fc15 m30 lo
                ST30 WHLO WHIMG WHTOP KF198 KF199 KF200 SHC30 PR64_v1 PR64_v2 PR64_v3 PR64_v4 PR64_v5 PR64_v6 PR64_v7 PR64_v8 PR64_v9 PR64_v10 PR64_v11 PR64_v12 PR64_v13 PR64_v14 PR64_v15 UT30 ACC_v1_31 PAL_v1 PHH_v1 PT_v1 PSTK_v1 DJ_v2_v1 ltac:((repeat match goal with H : wp_box (_ mod _ = 0) |- _ => unfold wp_box in H end); (repeat match goal with H : wp_box (0 <= _ < 2 ^ 64) |- _ => unfold wp_box in H end); wg_cond) MI30) as W31.
  cl_lift W31 Hc30' c31 Hc31.
  apply Hk. exists Σ15, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15.
  split; [| split; [rewrite LV30, LV28, LV26, LV24, LV22, LV20, LV18, LV16, LV14, LV12, LV10, LV8, LV6, LV4, LV2; reflexivity|]; split; [rewrite FRS30, FRS28, FRS26, FRS24, FRS22, FRS20, FRS18, FRS16, FRS14, FRS12, FRS10, FRS8, FRS6, FRS4, FRS2; reflexivity|]; split; [rewrite SP30, SP28, SP26, SP24, SP22, SP20, SP18, SP16, SP14, SP12, SP10, SP8, SP6, SP4, SP2; reflexivity|]; split; [(repeat match goal with H : wp_box (rt_credit _ _ = _) |- _ => unfold wp_box in H end); lia|]; split; [exact P0_v1|]; split; [exact P16_v1|]; split; [exact PU_v1|]; split; [exact P0_v2|]; split; [exact P16_v2|]; split; [exact PU_v2|]; split; [exact P0_v3|]; split; [exact P16_v3|]; split; [exact PU_v3|]; split; [exact P0_v4|]; split; [exact P16_v4|]; split; [exact PU_v4|]; split; [exact P0_v5|]; split; [exact P16_v5|]; split; [exact PU_v5|]; split; [exact P0_v6|]; split; [exact P16_v6|]; split; [exact PU_v6|]; split; [exact P0_v7|]; split; [exact P16_v7|]; split; [exact PU_v7|]; split; [exact P0_v8|]; split; [exact P16_v8|]; split; [exact PU_v8|]; split; [exact P0_v9|]; split; [exact P16_v9|]; split; [exact PU_v9|]; split; [exact P0_v10|]; split; [exact P16_v10|]; split; [exact PU_v10|]; split; [exact P0_v11|]; split; [exact P16_v11|]; split; [exact PU_v11|]; split; [exact P0_v12|]; split; [exact P16_v12|]; split; [exact PU_v12|]; split; [exact P0_v13|]; split; [exact P16_v13|]; split; [exact PU_v13|]; split; [exact P0_v14|]; split; [exact P16_v14|]; split; [exact PU_v14|]; split; [exact P0_v15|]; split; [exact P16_v15|]; split; [exact PU_v15|]; rewrite CG30, CG28, CG26, CG24, CG22, CG20, CG18, CG16, CG14, CG12, CG10, CG8, CG6, CG4, CG2; reflexivity].
  apply (ASTA_conseq RT Σ15 PMc _ _ c31 Hc31). intros ms31 (m31 & -> & MU31 & WM31 & MI31 & H31_0 & H31_1 & H31_2 & ST31). fold usp in MU31, ST31.
  exists m31.
  split; [exists u0_15, u1_15, u2_15, (Z_to_bv 64 (v1 + 16)), (Z_to_bv 64 0), b3_15, b4_15, b5_15, b6_15, b7_15, u3_15, u4_15, u5_15, u6_15, F15, fc15; reflexivity|].
  assert (ART31 : ART RT Σ15 m31).
  { apply (wg_seg_ART RT AF Σ15 m30 m31 usp 64 [(v1, v1 + 24)] ART30 ltac:(rewrite SPc30; lia) ltac:(lia) MU31); [|exact WM31].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists v1, 24; split; [exact INP_v1_30 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART31|]; split; [exact MI31|]; split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 (wmono_trans asegs _ _ _ WM8 (wmono_trans asegs _ _ _ WM9 (wmono_trans asegs _ _ _ WM10 (wmono_trans asegs _ _ _ WM11 (wmono_trans asegs _ _ _ WM12 (wmono_trans asegs _ _ _ WM13 (wmono_trans asegs _ _ _ WM14 (wmono_trans asegs _ _ _ WM15 (wmono_trans asegs _ _ _ WM16 (wmono_trans asegs _ _ _ WM17 (wmono_trans asegs _ _ _ WM18 (wmono_trans asegs _ _ _ WM19 (wmono_trans asegs _ _ _ WM20 (wmono_trans asegs _ _ _ WM21 (wmono_trans asegs _ _ _ WM22 (wmono_trans asegs _ _ _ WM23 (wmono_trans asegs _ _ _ WM24 (wmono_trans asegs _ _ _ WM25 (wmono_trans asegs _ _ _ WM26 (wmono_trans asegs _ _ _ WM27 (wmono_trans asegs _ _ _ WM28 (wmono_trans asegs _ _ _ WM29 (wmono_trans asegs _ _ _ WM30 WM31)))))))))))))))))))))))))))))) | exact ST31]|].
  split.
  { intros a Ha Ho.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 1 right; exact He | rewrite FRS2; intros e He; exact He | lia]).
    assert (NA_v1 : ~ (v1 <= bv_unsigned a < v1 + 24)) by exact (wg_newchunk_apart RT AF Σ Σ1 m2 [(v1, 24)] v1 24 usp _ ART2 LV2 ltac:(left; reflexivity) FRS2 SP2 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha).
    wp_box1 NA_v1.
    assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha1); [intros e He; rewrite LV4; do 1 right; exact He | rewrite FRS4; intros e He; exact He | lia]).
    assert (NA_v2 : ~ (v2 <= bv_unsigned a < v2 + 384)) by exact (wg_newchunk_apart RT AF Σ1 Σ2 m4 [(v2, 384)] v2 384 usp _ ART4 LV4 ltac:(left; reflexivity) FRS4 SP4 ltac:(rewrite SPc2; unfold RT_STACK in *; lia) ltac:(lia) Ha1).
    wp_box1 NA_v2.
    wp_box1 Ha1.
    assert (Ha3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha2); [intros e He; rewrite LV6; do 1 right; exact He | rewrite FRS6; intros e He; exact He | lia]).
    assert (NA_v3 : ~ (v3 <= bv_unsigned a < v3 + 32)) by exact (wg_newchunk_apart RT AF Σ2 Σ3 m6 [(v3, 32)] v3 32 usp _ ART6 LV6 ltac:(left; reflexivity) FRS6 SP6 ltac:(rewrite SPc4; unfold RT_STACK in *; lia) ltac:(lia) Ha2).
    wp_box1 NA_v3.
    wp_box1 Ha2.
    assert (Ha4 : aclient (rt_live RT Σ4) (rt_frames RT Σ4) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha3); [intros e He; rewrite LV8; do 1 right; exact He | rewrite FRS8; intros e He; exact He | lia]).
    assert (NA_v4 : ~ (v4 <= bv_unsigned a < v4 + 40)) by exact (wg_newchunk_apart RT AF Σ3 Σ4 m8 [(v4, 40)] v4 40 usp _ ART8 LV8 ltac:(left; reflexivity) FRS8 SP8 ltac:(rewrite SPc6; unfold RT_STACK in *; lia) ltac:(lia) Ha3).
    wp_box1 NA_v4.
    wp_box1 Ha3.
    assert (Ha5 : aclient (rt_live RT Σ5) (rt_frames RT Σ5) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha4); [intros e He; rewrite LV10; do 1 right; exact He | rewrite FRS10; intros e He; exact He | lia]).
    assert (NA_v5 : ~ (v5 <= bv_unsigned a < v5 + 40)) by exact (wg_newchunk_apart RT AF Σ4 Σ5 m10 [(v5, 40)] v5 40 usp _ ART10 LV10 ltac:(left; reflexivity) FRS10 SP10 ltac:(rewrite SPc8; unfold RT_STACK in *; lia) ltac:(lia) Ha4).
    wp_box1 NA_v5.
    wp_box1 Ha4.
    assert (Ha6 : aclient (rt_live RT Σ6) (rt_frames RT Σ6) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha5); [intros e He; rewrite LV12; do 1 right; exact He | rewrite FRS12; intros e He; exact He | lia]).
    assert (NA_v6 : ~ (v6 <= bv_unsigned a < v6 + 32)) by exact (wg_newchunk_apart RT AF Σ5 Σ6 m12 [(v6, 32)] v6 32 usp _ ART12 LV12 ltac:(left; reflexivity) FRS12 SP12 ltac:(rewrite SPc10; unfold RT_STACK in *; lia) ltac:(lia) Ha5).
    wp_box1 NA_v6.
    wp_box1 Ha5.
    assert (Ha7 : aclient (rt_live RT Σ7) (rt_frames RT Σ7) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha6); [intros e He; rewrite LV14; do 1 right; exact He | rewrite FRS14; intros e He; exact He | lia]).
    assert (NA_v7 : ~ (v7 <= bv_unsigned a < v7 + 40)) by exact (wg_newchunk_apart RT AF Σ6 Σ7 m14 [(v7, 40)] v7 40 usp _ ART14 LV14 ltac:(left; reflexivity) FRS14 SP14 ltac:(rewrite SPc12; unfold RT_STACK in *; lia) ltac:(lia) Ha6).
    wp_box1 NA_v7.
    wp_box1 Ha6.
    assert (Ha8 : aclient (rt_live RT Σ8) (rt_frames RT Σ8) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha7); [intros e He; rewrite LV16; do 1 right; exact He | rewrite FRS16; intros e He; exact He | lia]).
    assert (NA_v8 : ~ (v8 <= bv_unsigned a < v8 + 40)) by exact (wg_newchunk_apart RT AF Σ7 Σ8 m16 [(v8, 40)] v8 40 usp _ ART16 LV16 ltac:(left; reflexivity) FRS16 SP16 ltac:(rewrite SPc14; unfold RT_STACK in *; lia) ltac:(lia) Ha7).
    wp_box1 NA_v8.
    wp_box1 Ha7.
    assert (Ha9 : aclient (rt_live RT Σ9) (rt_frames RT Σ9) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha8); [intros e He; rewrite LV18; do 1 right; exact He | rewrite FRS18; intros e He; exact He | lia]).
    assert (NA_v9 : ~ (v9 <= bv_unsigned a < v9 + 32)) by exact (wg_newchunk_apart RT AF Σ8 Σ9 m18 [(v9, 32)] v9 32 usp _ ART18 LV18 ltac:(left; reflexivity) FRS18 SP18 ltac:(rewrite SPc16; unfold RT_STACK in *; lia) ltac:(lia) Ha8).
    wp_box1 NA_v9.
    wp_box1 Ha8.
    assert (Ha10 : aclient (rt_live RT Σ10) (rt_frames RT Σ10) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha9); [intros e He; rewrite LV20; do 1 right; exact He | rewrite FRS20; intros e He; exact He | lia]).
    assert (NA_v10 : ~ (v10 <= bv_unsigned a < v10 + 40)) by exact (wg_newchunk_apart RT AF Σ9 Σ10 m20 [(v10, 40)] v10 40 usp _ ART20 LV20 ltac:(left; reflexivity) FRS20 SP20 ltac:(rewrite SPc18; unfold RT_STACK in *; lia) ltac:(lia) Ha9).
    wp_box1 NA_v10.
    wp_box1 Ha9.
    assert (Ha11 : aclient (rt_live RT Σ11) (rt_frames RT Σ11) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha10); [intros e He; rewrite LV22; do 1 right; exact He | rewrite FRS22; intros e He; exact He | lia]).
    assert (NA_v11 : ~ (v11 <= bv_unsigned a < v11 + 40)) by exact (wg_newchunk_apart RT AF Σ10 Σ11 m22 [(v11, 40)] v11 40 usp _ ART22 LV22 ltac:(left; reflexivity) FRS22 SP22 ltac:(rewrite SPc20; unfold RT_STACK in *; lia) ltac:(lia) Ha10).
    wp_box1 NA_v11.
    wp_box1 Ha10.
    assert (Ha12 : aclient (rt_live RT Σ12) (rt_frames RT Σ12) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha11); [intros e He; rewrite LV24; do 1 right; exact He | rewrite FRS24; intros e He; exact He | lia]).
    assert (NA_v12 : ~ (v12 <= bv_unsigned a < v12 + 32)) by exact (wg_newchunk_apart RT AF Σ11 Σ12 m24 [(v12, 32)] v12 32 usp _ ART24 LV24 ltac:(left; reflexivity) FRS24 SP24 ltac:(rewrite SPc22; unfold RT_STACK in *; lia) ltac:(lia) Ha11).
    wp_box1 NA_v12.
    wp_box1 Ha11.
    assert (Ha13 : aclient (rt_live RT Σ13) (rt_frames RT Σ13) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha12); [intros e He; rewrite LV26; do 1 right; exact He | rewrite FRS26; intros e He; exact He | lia]).
    assert (NA_v13 : ~ (v13 <= bv_unsigned a < v13 + 40)) by exact (wg_newchunk_apart RT AF Σ12 Σ13 m26 [(v13, 40)] v13 40 usp _ ART26 LV26 ltac:(left; reflexivity) FRS26 SP26 ltac:(rewrite SPc24; unfold RT_STACK in *; lia) ltac:(lia) Ha12).
    wp_box1 NA_v13.
    wp_box1 Ha12.
    assert (Ha14 : aclient (rt_live RT Σ14) (rt_frames RT Σ14) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha13); [intros e He; rewrite LV28; do 1 right; exact He | rewrite FRS28; intros e He; exact He | lia]).
    assert (NA_v14 : ~ (v14 <= bv_unsigned a < v14 + 40)) by exact (wg_newchunk_apart RT AF Σ13 Σ14 m28 [(v14, 40)] v14 40 usp _ ART28 LV28 ltac:(left; reflexivity) FRS28 SP28 ltac:(rewrite SPc26; unfold RT_STACK in *; lia) ltac:(lia) Ha13).
    wp_box1 NA_v14.
    wp_box1 Ha13.
    assert (Ha15 : aclient (rt_live RT Σ15) (rt_frames RT Σ15) usp (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha14); [intros e He; rewrite LV30; do 1 right; exact He | rewrite FRS30; intros e He; exact He | lia]).
    assert (NA_v15 : ~ (v15 <= bv_unsigned a < v15 + 40)) by exact (wg_newchunk_apart RT AF Σ14 Σ15 m30 [(v15, 40)] v15 40 usp _ ART30 LV30 ltac:(left; reflexivity) FRS30 SP30 ltac:(rewrite SPc28; unfold RT_STACK in *; lia) ltac:(lia) Ha14).
    wp_box1 NA_v15.
    wp_box1 Ha14.
    wp_box1 Ha15.
    pose proof (cl_split RT AF Σ m usp 64 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha) as SPL.
    cbn [app outside] in Ho. unfold G_ALLOW_CUST in Ho.
    rewrite (MU31 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES30 a ltac:(unfold wp_box in Ha14; destruct Ha14 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU29 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES28 a ltac:(unfold wp_box in Ha13; destruct Ha13 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU27 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES26 a ltac:(unfold wp_box in Ha12; destruct Ha12 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU25 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES24 a ltac:(unfold wp_box in Ha11; destruct Ha11 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU23 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES22 a ltac:(unfold wp_box in Ha10; destruct Ha10 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU21 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES20 a ltac:(unfold wp_box in Ha9; destruct Ha9 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU19 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES18 a ltac:(unfold wp_box in Ha8; destruct Ha8 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU17 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES16 a ltac:(unfold wp_box in Ha7; destruct Ha7 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU15 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES14 a ltac:(unfold wp_box in Ha6; destruct Ha6 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU13 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES12 a ltac:(unfold wp_box in Ha5; destruct Ha5 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU11 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES10 a ltac:(unfold wp_box in Ha4; destruct Ha4 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU9 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES8 a ltac:(unfold wp_box in Ha3; destruct Ha3 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU7 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES6 a ltac:(unfold wp_box in Ha2; destruct Ha2 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU5 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES4 a ltac:(unfold wp_box in Ha1; destruct Ha1 as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU3 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (PRES2 a ltac:(unfold wp_box in Ha; destruct Ha as [H|H]; [left; lia | right; exact H]) ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(unfold G_ALLOW_CUST in *; idtac))).
    reflexivity. }
  pose proof (af_acc_live RT AF Σ15 m31 v1 24 ART31 INP_v1_30) as (WRE_v1 & ACCE_v1).
  pose proof (af_acc_live RT AF Σ15 m31 v2 384 ART31 INP_v2_30) as (WRE_v2 & ACCE_v2).
  pose proof (af_acc_live RT AF Σ15 m31 v3 32 ART31 INP_v3_30) as (WRE_v3 & ACCE_v3).
  pose proof (af_acc_live RT AF Σ15 m31 v4 40 ART31 INP_v4_30) as (WRE_v4 & ACCE_v4).
  pose proof (af_acc_live RT AF Σ15 m31 v5 40 ART31 INP_v5_30) as (WRE_v5 & ACCE_v5).
  pose proof (af_acc_live RT AF Σ15 m31 v6 32 ART31 INP_v6_30) as (WRE_v6 & ACCE_v6).
  pose proof (af_acc_live RT AF Σ15 m31 v7 40 ART31 INP_v7_30) as (WRE_v7 & ACCE_v7).
  pose proof (af_acc_live RT AF Σ15 m31 v8 40 ART31 INP_v8_30) as (WRE_v8 & ACCE_v8).
  pose proof (af_acc_live RT AF Σ15 m31 v9 32 ART31 INP_v9_30) as (WRE_v9 & ACCE_v9).
  pose proof (af_acc_live RT AF Σ15 m31 v10 40 ART31 INP_v10_30) as (WRE_v10 & ACCE_v10).
  pose proof (af_acc_live RT AF Σ15 m31 v11 40 ART31 INP_v11_30) as (WRE_v11 & ACCE_v11).
  pose proof (af_acc_live RT AF Σ15 m31 v12 32 ART31 INP_v12_30) as (WRE_v12 & ACCE_v12).
  pose proof (af_acc_live RT AF Σ15 m31 v13 40 ART31 INP_v13_30) as (WRE_v13 & ACCE_v13).
  pose proof (af_acc_live RT AF Σ15 m31 v14 40 ART31 INP_v14_30) as (WRE_v14 & ACCE_v14).
  pose proof (af_acc_live RT AF Σ15 m31 v15 40 ART31 INP_v15_30) as (WRE_v15 & ACCE_v15).
  split; [exact (cl_env_seg _ m30 m31 _ canary G15_ENVp MU31 ltac:(cl_fp_lia))|].
  split; [exact WRE_v1|].
  split; [exact ACCE_v1|].
  split; [exact WRE_v2|].
  split; [exact ACCE_v2|].
  split; [exact WRE_v3|].
  split; [exact ACCE_v3|].
  split; [exact WRE_v4|].
  split; [exact ACCE_v4|].
  split; [exact WRE_v5|].
  split; [exact ACCE_v5|].
  split; [exact WRE_v6|].
  split; [exact ACCE_v6|].
  split; [exact WRE_v7|].
  split; [exact ACCE_v7|].
  split; [exact WRE_v8|].
  split; [exact ACCE_v8|].
  split; [exact WRE_v9|].
  split; [exact ACCE_v9|].
  split; [exact WRE_v10|].
  split; [exact ACCE_v10|].
  split; [exact WRE_v11|].
  split; [exact ACCE_v11|].
  split; [exact WRE_v12|].
  split; [exact ACCE_v12|].
  split; [exact WRE_v13|].
  split; [exact ACCE_v13|].
  split; [exact WRE_v14|].
  split; [exact ACCE_v14|].
  split; [exact WRE_v15|].
  split; [exact ACCE_v15|].
  split; [exact H31_0|].
  split; [exact H31_1|].
  split; [pose proof (wg_live_apart RT AF Σ3 m6 [] v3 32 (rt_live RT Σ2) v1 24 ART6 LV6 ltac:(cbn [app In]; exact INP_v1_4)) as DJ_v3_v1; apply (wg_keep_seg _ m30 m31 _ _ KF202 MU31 WM31); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ4 m8 [] v4 40 (rt_live RT Σ3) v1 24 ART8 LV8 ltac:(cbn [app In]; exact INP_v1_6)) as DJ_v4_v1; apply (wg_keep_seg _ m30 m31 _ _ KF203 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ5 m10 [] v5 40 (rt_live RT Σ4) v1 24 ART10 LV10 ltac:(cbn [app In]; exact INP_v1_8)) as DJ_v5_v1; apply (wg_keep_seg _ m30 m31 _ _ KF204 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ6 m12 [] v6 32 (rt_live RT Σ5) v1 24 ART12 LV12 ltac:(cbn [app In]; exact INP_v1_10)) as DJ_v6_v1; apply (wg_keep_seg _ m30 m31 _ _ KF205 MU31 WM31); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ7 m14 [] v7 40 (rt_live RT Σ6) v1 24 ART14 LV14 ltac:(cbn [app In]; exact INP_v1_12)) as DJ_v7_v1; apply (wg_keep_seg _ m30 m31 _ _ KF206 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ8 m16 [] v8 40 (rt_live RT Σ7) v1 24 ART16 LV16 ltac:(cbn [app In]; exact INP_v1_14)) as DJ_v8_v1; apply (wg_keep_seg _ m30 m31 _ _ KF207 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ9 m18 [] v9 32 (rt_live RT Σ8) v1 24 ART18 LV18 ltac:(cbn [app In]; exact INP_v1_16)) as DJ_v9_v1; apply (wg_keep_seg _ m30 m31 _ _ KF208 MU31 WM31); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ10 m20 [] v10 40 (rt_live RT Σ9) v1 24 ART20 LV20 ltac:(cbn [app In]; exact INP_v1_18)) as DJ_v10_v1; apply (wg_keep_seg _ m30 m31 _ _ KF209 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ11 m22 [] v11 40 (rt_live RT Σ10) v1 24 ART22 LV22 ltac:(cbn [app In]; exact INP_v1_20)) as DJ_v11_v1; apply (wg_keep_seg _ m30 m31 _ _ KF210 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ12 m24 [] v12 32 (rt_live RT Σ11) v1 24 ART24 LV24 ltac:(cbn [app In]; exact INP_v1_22)) as DJ_v12_v1; apply (wg_keep_seg _ m30 m31 _ _ KF211 MU31 WM31); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ13 m26 [] v13 40 (rt_live RT Σ12) v1 24 ART26 LV26 ltac:(cbn [app In]; exact INP_v1_24)) as DJ_v13_v1; apply (wg_keep_seg _ m30 m31 _ _ KF212 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  split; [pose proof (wg_live_apart RT AF Σ14 m28 [] v14 40 (rt_live RT Σ13) v1 24 ART28 LV28 ltac:(cbn [app In]; exact INP_v1_26)) as DJ_v14_v1; apply (wg_keep_seg _ m30 m31 _ _ KF213 MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I|].
  pose proof (wg_live_apart RT AF Σ15 m30 [] v15 40 (rt_live RT Σ14) v1 24 ART30 LV30 ltac:(cbn [app In]; exact INP_v1_28)) as DJ_v15_v1; apply (wg_keep_seg _ m30 m31 _ _ G15_MX MU31 WM31); intros x Hx; unfold mutex_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbn [app outside]; unfold G_ALLOW_CUST in *; repeat (split; [lia|]); exact I.
Qed.
End ossl_method_store_new_cps.
