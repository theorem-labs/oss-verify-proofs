(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W4_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition W4_decode_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (C lo : Z) (num ln fl : word) (ed : list byte),
    a0 = Z_to_bv 64 C -> 0 < C -> C mod 4 = 0 ->
    rw_cells usegs m C (ectx_cells num ed ln fl) -> length ed = 80%nat ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (C + 92 <= lo \/ bv_unsigned sp <= C) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 z64 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (C, C + 4); (C + 84, C + 92)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' C (ectx_cells z64 ed z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x191d28) fc None m (seg_rom usegs)).

Theorem W4_decode_init_proof : W4_decode_init_stmt.
Proof.
  unfold W4_decode_init_stmt, ectx_cells. intros until ed. intros -> HC HA CTX LED ST LO0 LO S1 MI.
  pose proof (rw_cells_bound _ _ _ _ CTX) as CB. cbn [cells_size csize Nat.add] in CB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (C, C + 4); (C + 84, C + 92)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  ths. ubs_if. ths. ths. ubs_if.
  do 3 ths.
  do 4 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.
