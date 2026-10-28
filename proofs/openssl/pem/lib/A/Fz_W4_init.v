(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_W4_kit Fz_W4_defs Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition W4_decode_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C lo : Z) (num ln fl : word) (ed : list byte),
    a0 = Z_to_bv 64 C -> 0 < C -> C mod 8 = 0 -> C + 92 <= lo ->
    (C + 92 <= 0x10000 \/ 0xbc6000 <= C) -> (C + 92 <= 0x7fff8000 \/ 0x10007fff8000 <= C) ->
    rw_cells asegs m C (ectx_cells num ed ln fl) -> length ed = 80%nat -> acc asegs m C 92 ->
    img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
    stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom asegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (C, C + 4); (C + 84, C + 92)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo (bv_unsigned sp)
                 /\ rw_cells asegs m' C (ectx_cells z64 ed z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_EVP_DecodeInit) fc None m (seg_rom asegs)).

Theorem W4_decode_init_proof : W4_decode_init_stmt.
Proof.
  unfold W4_decode_init_stmt, ectx_cells, g_shadow_memory_dynamic_address, SHB, e_EVP_DecodeInit.
  intros until ed. intros -> C0 CAL CLO CIM CSH CTX LED ACC UT SHC ST LO0 LO HTOP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (C, C + 4); (C + 84, C + 92)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 zstep.
  (* [comment removed for export] *)
  do 3 zstep. do 3 zstep. zstep. th_if_lit. zstep.
  (* [comment removed for export] *)
  do 4 zstep. zstep. th_if_lit. zstep.
  (* [comment removed for export] *)
  zstep. chk_pass ACC (C + 88) 4 0x31f444 11 12. zstep.
  do 3 zstep. th_release FR (bv_unsigned sp). zstep. finish.
Qed.
