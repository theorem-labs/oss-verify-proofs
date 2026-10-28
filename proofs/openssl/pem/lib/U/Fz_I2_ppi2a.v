(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_M_calloc Fz_M_realloc Fz_kit_ra Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_lock Fz_T_sk F_strlen F_memcpy Fz_K_hash Fz_K_rep Fz_K_getrn Fz_K_retrieve Fz_K_insert Fz_K_pstr1 Fz_K_pstr2 Fz_K_pstr3 Fz_K_skstmt Fz_K_pstr Fz_K_pstrf Fz_K_pstrg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation wz := (Z_to_bv 64) (only parsing).
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition PPI_TAB : Z := 0x3a9f8.
Definition A_PROVIDER : Z := 0x2a37f. Definition A_VERSION : Z := 0x23a5b. Definition A_FIPS : Z := 0x3907e. Definition A_OUTPUT : Z := 0x28d4c.
Definition A_INPUT : Z := 0x14262. Definition A_STRUCTURE : Z := 0x24db5. Definition A_YES : Z := 0x1eab9. Definition A_NO : Z := 0x2ceca.

(* [comment removed for export] *)
Lemma ppi_seg0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  a0 = Z_to_bv 64 CTX_A ->
  stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_PROVIDER) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 6) (Z_to_bv 64 PPI_TAB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells usegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_PROPERTY_PARSE_INIT) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros -> ST LO0 LO MI. unfold FZ_PROPERTY_PARSE_INIT, CTX_A, A_PROVIDER, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST. do 6 ths.
  do 6 zstep.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_VERSION) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 5) (Z_to_bv 64 0x3a9fc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 6) (Z_to_bv 64 PPI_TAB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_VERSION, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg2 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_FIPS) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 4) (Z_to_bv 64 0x3aa00) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 5) (Z_to_bv 64 0x3a9fc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_FIPS, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg3 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_OUTPUT) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 3) (Z_to_bv 64 0x3aa04) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 4) (Z_to_bv 64 0x3aa00) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_OUTPUT, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg4 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_INPUT) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 2) (Z_to_bv 64 0x3aa08) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 3) (Z_to_bv 64 0x3aa04) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_INPUT, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg5 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 A_STRUCTURE) a4 a5 a6 a7
                    (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 1) (Z_to_bv 64 0x3aa0c) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 2) (Z_to_bv 64 0x3aa08) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_STRUCTURE, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg6 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff4c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 A_YES) a4 a5 a6 a7
                    (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x3aa10) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff24) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 6) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PPI_TAB) (Z_to_bv 64 1) (Z_to_bv 64 0x3aa0c) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff24) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_YES, PPI_TAB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit. zstep. zstep. zstep. th_if_lit.
  do 6 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg7 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0xeff64) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 CTX_A) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 A_NO) a4 a5 a6 a7
                    (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x3aa10) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xf0b7c) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -48))
    (MS (mkR (Z_to_bv 64 0xeff4c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x3aa10) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff4c) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST LO0 LO SP64 MI. unfold CTX_A, A_NO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. th_if_lit.
  do 5 zstep.
  zstep. th_frame 16%nat [8; 8]%nat ST. do 2 ths. do 3 zstep. do 2 zstep.
  zstep.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => th_release FRh (bv_unsigned sp + -48) end.
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ppi_seg8 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) (rae s0e s1e s2e s3e s4e : word),
  stk usegs m lo (bv_unsigned sp + -48) -> 0 <= lo -> lo <= bv_unsigned sp - 64 -> 64 <= bv_unsigned sp -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -48) [C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  evt usegs (fun ms' => exists (a1' : word) (m' : mem),
      ms' = MS (mkR rae sp gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7
                    s2e s3e s4e s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rae) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0xeff64) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 CTX_A) (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0x3aa10) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xeff64) fc None m (seg_rom usegs)).
Proof.
  intros until s4e. intros ST LO0 LO SP64 MI FR. unfold CTX_A.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. zstep. th_if_lit. zstep.
  do 6 zstep. zstep.
  th_release FR (bv_unsigned sp).
  zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition lit_ok (A : Z) (str slack : list byte) : Prop :=
  ro_bytes usegs A (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\ str <> [] /\ (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ 0x10000 <= A /\ A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 /\ Z.of_nat (length str) < 2 ^ 20.

Definition s_provider : list byte := to_bytes [112; 114; 111; 118; 105; 100; 101; 114].   Definition k_provider : list byte := to_bytes [111; 115; 115; 108; 95; 112].
Definition s_version : list byte := to_bytes [118; 101; 114; 115; 105; 111; 110].         Definition k_version : list byte := to_bytes [103; 101; 116; 95; 112].
Definition s_fips : list byte := to_bytes [102; 105; 112; 115].                           Definition k_fips : list byte := to_bytes [99; 114; 121; 112; 116].
Definition s_output : list byte := to_bytes [111; 117; 116; 112; 117; 116].               Definition k_output : list byte := to_bytes [72; 69; 82; 69; 45].
Definition s_input : list byte := to_bytes [105; 110; 112; 117; 116].                     Definition k_input : list byte := to_bytes [37; 108; 108; 100; 0; 79; 80].
Definition s_structure : list byte := to_bytes [115; 116; 114; 117; 99; 116; 117; 114; 101]. Definition k_structure : list byte := to_bytes [70; 65; 76; 83; 69; 0; 99].
Definition s_yes : list byte := to_bytes [121; 101; 115].                                Definition k_yes : list byte := to_bytes [112; 114; 111].
Definition s_no : list byte := to_bytes [110; 111].                                      Definition k_no : list byte := to_bytes [112; 97; 114].

Ltac lit_tac := split; [apply ro_bytes_b_sound; vm_compute; reflexivity|];
  split; [vm_compute; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH|];
  split; [cbn; discriminate|]; cbn; lia.
Lemma lit_provider : lit_ok A_PROVIDER s_provider k_provider. Proof. unfold lit_ok, A_PROVIDER, s_provider, k_provider. lit_tac. Qed.
Lemma lit_version : lit_ok A_VERSION s_version k_version. Proof. unfold lit_ok, A_VERSION, s_version, k_version. lit_tac. Qed.
Lemma lit_fips : lit_ok A_FIPS s_fips k_fips. Proof. unfold lit_ok, A_FIPS, s_fips, k_fips. lit_tac. Qed.
Lemma lit_output : lit_ok A_OUTPUT s_output k_output. Proof. unfold lit_ok, A_OUTPUT, s_output, k_output. lit_tac. Qed.
Lemma lit_input : lit_ok A_INPUT s_input k_input. Proof. unfold lit_ok, A_INPUT, s_input, k_input. lit_tac. Qed.
Lemma lit_structure : lit_ok A_STRUCTURE s_structure k_structure. Proof. unfold lit_ok, A_STRUCTURE, s_structure, k_structure. lit_tac. Qed.
Lemma lit_yes : lit_ok A_YES s_yes k_yes. Proof. unfold lit_ok, A_YES, s_yes, k_yes. lit_tac. Qed.
Lemma lit_no : lit_ok A_NO s_no k_no. Proof. unfold lit_ok, A_NO, s_no, k_no. lit_tac. Qed.

(* [comment removed for export] *)
Definition H_PROVIDER : Z := 0x672244bb. Definition H_VERSION : Z := 0x64dc8d0b. Definition H_FIPS : Z := 0x6093f86e. Definition H_OUTPUT : Z := 0xdbaceec9.
Definition H_INPUT : Z := 0x5a0038b. Definition H_STRUCTURE : Z := 0x72db842e. Definition H_YES : Z := 0x55e72115. Definition H_NO : Z := 0x255844.
Lemma hash_provider : lh_strhash s_provider = H_PROVIDER. Proof. vm_compute. reflexivity. Qed.
Lemma hash_version : lh_strhash s_version = H_VERSION. Proof. vm_compute. reflexivity. Qed.
Lemma hash_fips : lh_strhash s_fips = H_FIPS. Proof. vm_compute. reflexivity. Qed.
Lemma hash_output : lh_strhash s_output = H_OUTPUT. Proof. vm_compute. reflexivity. Qed.
Lemma hash_input : lh_strhash s_input = H_INPUT. Proof. vm_compute. reflexivity. Qed.
Lemma hash_structure : lh_strhash s_structure = H_STRUCTURE. Proof. vm_compute. reflexivity. Qed.
Lemma hash_yes : lh_strhash s_yes = H_YES. Proof. vm_compute. reflexivity. Qed.
Lemma hash_no : lh_strhash s_no = H_NO. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition nb16 (b1 b3 b4 b5 b6 : list pnode) : list (list pnode) := [[]; b1; []; b3; b4; b5; b6; []; []; []; []; []; []; []; []; []].
Lemma nb16_empty : repeat [] 16 = nb16 [] [] [] [] []. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nd_neq : forall (l : list bptr) (i j : nat) (x y : bptr), List.NoDup l -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> x <> y.
Proof.
  intros l i j x y ND Hi Hj NE E. subst y. apply NE. clear NE. revert i j Hi Hj. induction ND as [|a l NI ND IH]; intros [|i] [|j] Hi Hj; cbn [nth_error] in Hi, Hj.
  - discriminate Hi. - discriminate Hi. - discriminate Hj. - discriminate Hj.
  - reflexivity.
  - exfalso. apply NI. inversion Hi; subst. eapply nth_error_In. exact Hj.
  - exfalso. apply NI. inversion Hj; subst. eapply nth_error_In. exact Hi.
  - f_equal. exact (IH i j Hi Hj).
Qed.

(* [comment removed for export] *)
Definition orig (LBall : list block) (L : @clist bptr) (q : bptr) : Prop := In q (map blk_id LBall) \/ In q (map fst L).
Lemma orig_of_in : forall LBall L (p : bptr) A n, In (p, A, n) LBall -> orig LBall L p.
Proof. intros LBall L p A n H. left. apply in_map_iff. exists (p, A, n). auto. Qed.

(* [comment removed for export] *)
Lemma lb_remove_prefix : forall (pre1 : list block) (b : block) (pre2 LBall l : list block),
  l = pre1 ++ b :: pre2 ++ LBall -> List.NoDup (map blk_id l) -> lb_remove (blk_id b) l = pre1 ++ pre2 ++ LBall.
Proof.
  intros pre1 b pre2 LBall l -> ND.
  assert (N1 : ~ In (blk_id b) (map blk_id pre1)).
  { intros X. rewrite map_app in ND. apply nodup_app_inv in ND. destruct ND as (_ & _ & DIS). apply (DIS _ X). cbn [map]. left. reflexivity. }
  assert (N2 : ~ In (blk_id b) (map blk_id (pre2 ++ LBall))).
  { rewrite map_app in ND. apply nodup_app_inv in ND. destruct ND as (_ & ND2 & _). cbn [map] in ND2. inversion ND2; subst. assumption. }
  rewrite lb_remove_app. rewrite (lb_remove_notin' _ _ N1). rewrite lb_remove_cons_eq by reflexivity. rewrite (lb_remove_notin' _ _ N2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cells_C8_CB : forall m A (v : word) n (bs : list byte), length bs = n ->
  rw_cells usegs m A [C8 v; CB n bs] -> rw_cells usegs m A [CB (8 + n)%nat (le8 v ++ bs)].
Proof.
  intros m A v n bs LEN H. eapply th_cells_congr; [| | | exact H].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
  - cbn. rewrite LEN. split; [reflexivity| exact I].
Qed.

End WithCeiling0.
