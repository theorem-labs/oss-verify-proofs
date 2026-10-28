(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Pj_steps Pj_once.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memset.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition call_once_post_28 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xedee8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells usegs m' 0xedee8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells usegs m' 0xedf08 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells usegs m' 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' 0xeec48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_28 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells usegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xedee8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells usegs m 0xedee8 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells usegs m 0xedf08 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells usegs m 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0xeec48 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv usegs m ->
  evt usegs (call_once_post_28 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xedee8) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0xb6e48) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb860c) fc None m (seg_rom usegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
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
  unfold call_once_post_28. sys_finish.
Qed.

Definition append_post_28 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d8); C8 (Z_to_bv 64 0xee4e0)]
    /\ rw_cells usegs m' 0xee4d0 [CB 8 (repeat (Z_to_bv 8 0) 8)].

Lemma append_spec_28 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (0x111000 <= lo)%Z ->
  rw_cells usegs m 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d0); C8 (Z_to_bv 64 0xee4e0)] ->
  rw_cells usegs m 0xee4d0 [CB 8 junk8] -> mem_inv usegs m ->
  evt usegs (append_post_28 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xee3d8) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb5af8) fc None m (seg_rom usegs)).
Proof.
  intros until junk8. intros ST LO LOLO VEC SLOT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 80%nat ST.
  do 17 lstep. if_true. lstep. if_false.
  do 5 lstep.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xee4d0 0 8 junk8)%Z; [exact SLOT | assumption | lia | lia | lia | lia |].
  rename POST into SLOT. change (Z.to_nat 8) with 8%nat in SLOT. change (0 mod 256)%Z with 0%Z in SLOT.
  do 15 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold append_post_28. sys_finish.
Qed.

Definition install_post_28 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xee1f8, 0xee200); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8);
              (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0xedee8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 29)]
    /\ rw_cells usegs m' 0xedf08 [C4 (Z_to_bv 64 29)]
    /\ rw_cells usegs m' 0xee1f8 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells usegs m' 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d8); C8 (Z_to_bv 64 0xee4e0)]
    /\ rw_cells usegs m' 0xee4d0 [C8 (Z_to_bv 64 0xee1f0)]
    /\ rw_cells usegs m' 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' 0xeec48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma install_spec_28 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 240)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells usegs m 0xedee8 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells usegs m 0xedf08 [C4 (Z_to_bv 64 28)] ->
  rw_cells usegs m 0xee1f8 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells usegs m 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d0); C8 (Z_to_bv 64 0xee4e0)] ->
  rw_cells usegs m 0xee4d0 [CB 8 junk8] ->
  rw_cells usegs m 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0xeec48 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv usegs m ->
  evt usegs (install_post_28 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v canary pad1 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xee3c8) (Z_to_bv 64 0xee1f0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0594) fc None m (seg_rom usegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI IDF NID RC RV VEC SLOT MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xee1f8, 0xee200); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8);
              (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 80%nat ST.
  do 7 lstep.
  do 9 lstep. if_false.
  do 10 lstep.
  lazymatch type of FR with
  | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
      apply (rw_cells_app usegs _ _ [c0; c1; c2; c3] rest) in FR; destruct FR as [PACK FR]
  end.
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in FR by lia.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = (bv_unsigned sp + -80)%Z) by (apply unsigned_lit; lia).
  replace (bv_unsigned sp + -56)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 24)%Z in PACK by lia.
  replace (bv_unsigned sp + -72)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 8)%Z in PACK by lia.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 16)%Z by lia.
  rewrite <- Hsp in PACK at 1. rewrite <- Hsp in ST.
  call call_once_spec_28;
    [exact ST | lia | lia | lia | exact PACK | exact IDF | exact NID | lia | exact MUT | exact GOT | exact CAN | exact CV | exact LP | assumption |].
  rename PC into ST. rewrite Hsp in ST. clear PACK. rename PC0 into PACK. rename PC1 into IDF. rename PC2 into NID. rename PC3 into MUT. rename POST into CV.
  change (28 + 1)%Z with 29%Z in *.
  lstep.
  replace (sx32 (Z_to_bv 64 29)) with (Z_to_bv 64 29) by (vm_compute; reflexivity).
  lstep. lstep.
  amo_step.
  change (amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1)) with (Z_to_bv 64 v + Z_to_bv 64 1 : word) in RC. rewrite lit_add_lit in RC.
  lstep. lstep. lstep. lstep. lstep. lstep.
  lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. lstep.
  call_sp append_spec_28; [exact ST | lia | lia | exact VEC | exact SLOT | assumption |].
  rename PC into ST. rename PC0 into VEC. rename POST into SLOT.
  lstep. lstep. lstep. lstep. lstep.
  replace (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with z64 by (apply bv_eq; vm_compute; reflexivity).
  lstep. if_true.
  lstep. lstep. lstep.
  do 8 lstep.
  rewrite ?unsigned_lit in PACK by lia.
  release_frame PACK ST (bv_unsigned sp + -48)%Z.
  release_frame FR ST (bv_unsigned sp).
  unfold install_post_28. sys_finish.
Qed.

Definition seg_post_28 (sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x9e004) sp gp tp t0 t1 t2 (Z_to_bv 64 0xee3c8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0xedf90) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9e004) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xee1f0, 0xee200); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8); (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0xedee8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 0x1d)]
    /\ rw_cells usegs m' 0xedf08 [C4 (Z_to_bv 64 0x1d)]
    /\ rw_cells usegs m' 0xee1f0 [C8 (Z_to_bv 64 0xdbbb0)]
    /\ rw_cells usegs m' 0xee1f8 [C8 (Z_to_bv 64 1)]
    /\ rw_cells usegs m' 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d8); C8 (Z_to_bv 64 0xee4e0)]
    /\ rw_cells usegs m' 0xee4d0 [C8 (Z_to_bv 64 0xee1f0)]
    /\ rw_cells usegs m' 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' 0xeec48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma seg_spec_28 : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 240)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells usegs m 0xedee8 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xedf08 [C4 (Z_to_bv 64 0x1c)] ->
  rw_cells usegs m 0xee1f0 [C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xee1f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xee3d8 [C8 (Z_to_bv 64 0xee3f0); C8 (Z_to_bv 64 0xee4d0); C8 (Z_to_bv 64 0xee4e0)] ->
  rw_cells usegs m 0xee4d0 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells usegs m 0xeec20 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0xeec48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv usegs m ->
  evt usegs (seg_post_28 sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0xee3c8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0xedf90) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9dfe8) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI IDF NID FC0 RC VEC SLOT MUT GOT CAN CV MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xedee8, 0xedef4); (0xedf08, 0xedf0c); (0xee1f0, 0xee200); (0xee3e0, 0xee3e8); (0xee4d0, 0xee4d8); (0xeec24, 0xeec28); (0xeec50, 0xeec58); (0xeec68, 0xeec6c); (0xeec70, 0xeec78)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  do 7 lstep.
  call (install_spec_28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z); [exact ST | lia | lia | lia | exact IDF | exact NID | exact RC | lia | exact VEC | exact SLOT | exact MUT | exact GOT | exact CAN | exact CV | reflexivity | assumption |].
  change (0 + 1)%Z with 1%Z in *.
  unfold seg_post_28. sys_finish.
Qed.
