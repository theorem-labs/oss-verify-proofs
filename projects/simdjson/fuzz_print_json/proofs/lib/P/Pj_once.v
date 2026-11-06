(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OSSVerify.simdjson.fuzz_print_json.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition mutex_lock_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(0xe2e14, 0xe2e18)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].

Lemma mutex_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rw_cells psegs m 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] -> mem_inv psegs m ->
  evt psegs (mutex_lock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe2e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc6b50) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros MUT MI.
  pose proof (munch_refl [(0xe2e14, 0xe2e18)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  lstep. lstep. lstep. if_false.
  lstep. lstep.
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. lstep. if_true. lstep. lstep.
  unfold mutex_lock_post. sys_finish.
Qed.

Definition mutex_unlock_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0xe2e14, 0xe2e18)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma mutex_unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (0x105000 <= lo)%Z ->
  rw_cells psegs m 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] -> mem_inv psegs m ->
  evt psegs (mutex_unlock_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe2e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc703c) fc None m (seg_rom psegs)).
Proof.
  intros until lo. intros ST LO LOLO MUT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0xe2e14, 0xe2e18)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  carve_frame 96%nat ST.
  do 13 lstep. do 5 lstep.
  replace (Z_to_bv 64 (Z.land (bv_unsigned (zx32 z64)) 15)) with z64 by (vm_compute; reflexivity).
  replace (Z_to_bv 64 (Z.land (bv_unsigned (zx32 z64)) 128)) with z64 by (vm_compute; reflexivity).
  replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  if_true.
  lstep. lstep. lstep.
  amo_step. replace (sx32 (Z_to_bv 64 16)) with (Z_to_bv 64 16) by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. lstep. lstep.
  if_true.
  lstep. if_true.
  do 14 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold mutex_unlock_post. sys_finish.
Qed.

Definition cond_broadcast_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0xe2e40, 0xe2e48); (0xe2e58, 0xe2e5c); (0xe2e60, 0xe2e68)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xe2e38 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma cond_broadcast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary tl : word) (pad1 : list byte) (pad2 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (0x105000 <= lo)%Z ->
  rw_cells psegs m 0xd0940 [C8 (Z_to_bv 64 0x1039e8)] -> rw_cells psegs m 0x1039e8 [C8 canary] ->
  rw_cells psegs m 0xe2e38 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv psegs m ->
  evt psegs (cond_broadcast_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo canary pad1 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe2e38) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xc5ee0) fc None m (seg_rom psegs)).
Proof.
  intros until pad2. intros ST LO LOLO GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xe2e40, 0xe2e48); (0xe2e58, 0xe2e5c); (0xe2e60, 0xe2e68)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  lstep. lstep. if_true. lstep. lstep.
  carve_frame 80%nat ST.
  do 17 lstep.
  amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. lstep. lstep. if_true.
  lstep. lstep. lstep. lstep. if_false. lstep. if_true. lstep. if_true.
  lstep. lstep. lstep. lstep.
  amo_step. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  lstep. if_false. amo_step. lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. if_true.
  lstep. lstep. if_false. lstep. if_true.
  lstep. lstep. lstep.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; rewrite bv_eqb_Z, Z.eqb_refl; reflexivity)
  end.
  cbv_concl_iota.
  do 10 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold cond_broadcast_post. sys_finish.
Qed.

Definition call_once_post (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0xe1fb8, 0xe1fc4); (0xe20f8, 0xe20fc); (0xe2e14, 0xe2e18); (0xe2e40, 0xe2e48); (0xe2e58, 0xe2e5c); (0xe2e60, 0xe2e68)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xe1fb8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells psegs m' 0xe1fb8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells psegs m' 0xe20f8 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells psegs m' 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m' 0xe2e38 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_0 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x105000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xe1fb8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells psegs m 0xe1fb8 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells psegs m 0xe20f8 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells psegs m 0xe2e10 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xd0940 [C8 (Z_to_bv 64 0x1039e8)] -> rw_cells psegs m 0x1039e8 [C8 canary] ->
  rw_cells psegs m 0xe2e38 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv psegs m ->
  evt psegs (call_once_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe1fb8) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0xab668) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xace2c) fc None m (seg_rom psegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0xe1fb8, 0xe1fc4); (0xe20f8, 0xe20fc); (0xe2e14, 0xe2e18); (0xe2e40, 0xe2e48); (0xe2e58, 0xe2e5c); (0xe2e60, 0xe2e68)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 64%nat ST.
  do 15 lstep.
  call mutex_lock_spec; [hyp_by_addr | exact MI |].
  rename POST into MUT.
  lstep. lstep. lstep. if_true. lstep. lstep. if_true.
  lstep. lstep. lstep. lstep. lstep.
  call_sp mutex_unlock_spec; [exact ST | lia | lia | exact MUT | assumption |].
  rename PC into ST. rename POST into MUT.

  lstep. lstep.
  lstep. lstep. lstep. lstep. lstep. lstep.
  amo_step. amo32_fix_lit.
  replace (sx32 (Z_to_bv 64 k)) with (Z_to_bv 64 k)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  lstep. lstep. lstep.
  lstep. lstep. lstep.
  call mutex_lock_spec; [exact MUT | assumption |].
  rename POST into MUT.
  lstep. lstep. lstep. lstep. lstep. lstep. lstep.
  call_sp mutex_unlock_spec; [exact ST | lia | lia | exact MUT | assumption |].
  rename PC into ST. rename POST into MUT.
  lstep. lstep.
  call_sp cond_broadcast_spec; [exact ST | lia | lia | exact GOT | exact CAN | exact CV | exact LP | assumption |].
  rename PC into ST. rename POST into CV.
  do 9 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold call_once_post. sys_finish.
Qed.
