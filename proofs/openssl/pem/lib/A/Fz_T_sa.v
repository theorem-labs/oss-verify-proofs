(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sa_hdr (lv pad top ne nodes : word) : list cell := [C4 lv; C4 pad; C8 top; C8 ne; C8 nodes].

Lemma sa_slot : forall n, 0 <= n < 16 -> Z.shiftl (Z.land n 15) 3 = 8 * n.
Proof.
  intros n Hn. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sa_slot60 : forall n, 0 <= n < 16 -> bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) ≪ 60)) ≫ 57 = 8 * n.
Proof.
  intros n Hn. rewrite (unsigned_lit n) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 60) with (2 ^ 57 * 8).
  replace (n * (2 ^ 57 * 8)) with (8 * n * 2 ^ 57) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Definition T_sa_get_leaf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA n LV NODES : Z) (pad top ne v : word),
    a0 = Z_to_bv 64 SA -> 0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
    ro_cells asegs m SA (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) -> acc asegs m SA 32 ->
    a1 = Z_to_bv 64 n -> 0 <= n < 16 -> n <= bv_unsigned top -> bv_unsigned ne <> 0 -> 0 <= LV < 2 ->
    0 < NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo ->
    ro_cells asegs m (NODES + 8 * n) [C8 v] -> acc asegs m NODES 128 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20cddc) fc None m (seg_rom asegs)).

Theorem T_sa_get_leaf_proof : T_sa_get_leaf_stmt.
Proof.
  unfold T_sa_get_leaf_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until v.
  intros -> SA0 SAL SALO HC HACC -> HN HT HNE HLV HNO NAL NLO VC NACC UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pn := NODES + 8 * n) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 3 zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K2; zify_cond K2. { exfalso. lia. }                              (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K4; zify_cond K4. { exfalso. lia. }
  do 3 zstep. if_cases K5; zify_cond K5; rewrite (t_sx32_small LV), signed_of_Z in K5 by lia.   (* [comment removed for export] *)
  2:{ exfalso. lia. }
  zstep. if_cases K8; zify_cond K8. { exfalso. lia. }
  do 2 zstep. rewrite (sa_slot n HN).                                                           (* [comment removed for export] *)
  zstep.                                                                                  (* [comment removed for export] *)
  fold Pn. assert (HPn : NODES <= Pn /\ Pn + 8 <= NODES + 128) by (unfold Pn; lia).
  do 3 zstep. zstep. th_if_lit.
  zstep.
  do 5 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_sa_get_empty_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA : Z) (lv pad top nodes : word),
    a0 = Z_to_bv 64 SA -> 0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
    ro_cells asegs m SA (sa_hdr lv pad top (Z_to_bv 64 0) nodes) -> acc asegs m SA 32 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x20cddc) fc None m (seg_rom asegs)).

Theorem T_sa_get_empty_proof : T_sa_get_empty_stmt.
Proof.
  unfold T_sa_get_empty_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until nodes.
  intros -> SA0 SAL SALO HC HACC UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  do 3 zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.
