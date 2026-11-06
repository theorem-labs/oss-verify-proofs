(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac SFModel.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_ukit.
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
    ro_cells bsegs m SA (sa_hdr (Z_to_bv 64 LV) pad top ne (Z_to_bv 64 NODES)) -> acc bsegs m SA 32 ->
    a1 = Z_to_bv 64 n -> 0 <= n < 16 -> n <= bv_unsigned top -> bv_unsigned ne <> 0 -> 0 <= LV < 2 ->
    0 < NODES -> NODES mod 8 = 0 -> NODES + 128 <= lo ->
    ro_cells bsegs m (NODES + 8 * n) [C8 v] -> acc bsegs m NODES 128 ->
    img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv bsegs m ->
    evt bsegs (fun ms' => exists (a1' a2' a3' a4' a5' a7' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4' a5' a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2096a4) fc None m (seg_rom bsegs)).

Theorem T_sa_get_leaf_proof : T_sa_get_leaf_stmt.
Proof.
  unfold T_sa_get_leaf_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until v.
  intros -> SA0 SAL SALO HC HACC -> HN HT HNE HLV HNO NAL NLO VC NACC UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 top) as RTOP. unfold bv_modulus in RTOP. cbn in RTOP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  set (Pn := NODES + 8 * n) in *.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep. ubs_if.                                                                 (* [comment removed for export] *)
  do 3 zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }                            (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small LV) by lia.
  zstep. rewrite ubs_sw32 by lia.                                                         (* [comment removed for export] *)
  zstep. if_cases K3; zify_cond K3; signed_lits_in K3. { exfalso. lia. }                  (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. if_cases K4; zify_cond K4. { exfalso. lia. }
  zstep. if_cases K5; zify_cond K5.                                                       (* [comment removed for export] *)
  2:{ exfalso. assert (HL : LV = 0 \/ LV = 1) by lia.
      destruct HL as [HL|HL]; rewrite HL in K6, K7; cbv in K6, K7; [discriminate K7 | discriminate K6]. }
  zstep. if_cases K8; zify_cond K8. { exfalso. lia. }
  assert (SL60 : forall k, 0 <= k < 16 -> Z.land (k ≪ 60) 18446744073709551615 ≫ 57 = 8 * k).
  { clear. intros k Hk. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 60) with (2 ^ 57 * 8).
    replace (k * (2 ^ 57 * 8)) with (8 * k * 2 ^ 57) by lia. rewrite Z.div_mul by lia. lia. }
  do 2 zstep. rewrite (SL60 n HN).                                                        (* [comment removed for export] *)
  zstep. zstep. if_cases K9; zify_cond K9. { exfalso. rewrite ubs_lxor_ones in K9 by lia. lia. }   (* [comment removed for export] *)
  zstep. zstep. zstep. ubs_if.                                                            (* [comment removed for export] *)
  fold Pn. assert (HPn : NODES <= Pn /\ Pn + 8 <= NODES + 128) by (unfold Pn; lia).
  do 3 zstep. zstep. th_if_lit.
  zstep.
  do 4 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

(* [comment removed for export] *)
Definition T_sa_get_empty_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo SA : Z) (lv pad top nodes : word),
    a0 = Z_to_bv 64 SA -> 0 < SA -> SA mod 8 = 0 -> SA + 32 <= lo ->
    ro_cells bsegs m SA (sa_hdr lv pad top (Z_to_bv 64 0) nodes) -> acc bsegs m SA 32 ->
    img_untouched m -> ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk bsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv bsegs m ->
    evt bsegs (fun ms' => exists (a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
                 /\ stk bsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2096a4) fc None m (seg_rom bsegs)).

Theorem T_sa_get_empty_proof : T_sa_get_empty_stmt.
Proof.
  unfold T_sa_get_empty_stmt, sa_hdr, g_shadow_memory_dynamic_address, SHB. intros until nodes.
  intros -> SA0 SAL SALO HC HACC UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep. ubs_if.
  do 3 zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 2 zstep.
  do 4 zstep.
  th_release FR (bv_unsigned sp).
  finish.
Qed.
