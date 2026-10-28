(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(0x6ab484, 0x6ab488)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].

Lemma mutex_lock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] -> mem_inv bsegs m ->
  evt bsegs (mutex_lock_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6ab480) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x163d9c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MUT MI.
  pose proof (munch_refl [(0x6ab484, 0x6ab488)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0x6ab484, 0x6ab488)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

Lemma mutex_unlock_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 96)%Z -> (0x6ce000 <= lo)%Z ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] -> mem_inv bsegs m ->
  evt bsegs (mutex_unlock_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6ab480) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x164288) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST LO LOLO MUT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0x6ab484, 0x6ab488)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0x6ab4b0, 0x6ab4b8); (0x6ab4c8, 0x6ab4cc); (0x6ab4d0, 0x6ab4d8)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma cond_broadcast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary tl : word) (pad1 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (0x6ce000 <= lo)%Z ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m ->
  evt bsegs (cond_broadcast_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo canary pad1 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6ab4a8) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x162034) fc None m (seg_rom bsegs)).
Proof.
  intros until pad2. intros ST LO LOLO GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x6ab4b0, 0x6ab4b8); (0x6ab4c8, 0x6ab4cc); (0x6ab4d0, 0x6ab4d8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0x6aa628, 0x6aa634); (0x6aa768, 0x6aa76c); (0x6ab484, 0x6ab488); (0x6ab4b0, 0x6ab4b8); (0x6ab4c8, 0x6ab4cc); (0x6ab4d0, 0x6ab4d8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6aa628); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells bsegs m' 0x6aa628 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs m' 0x6aa768 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs m' 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_0 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6aa628); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells bsegs m 0x6aa628 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m ->
  evt bsegs (call_once_post ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aa628) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x14637c) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x147b40) fc None m (seg_rom bsegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x6aa628, 0x6aa634); (0x6aa768, 0x6aa76c); (0x6ab484, 0x6ab488); (0x6ab4b0, 0x6ab4b8); (0x6ab4c8, 0x6ab4cc); (0x6ab4d0, 0x6ab4d8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
