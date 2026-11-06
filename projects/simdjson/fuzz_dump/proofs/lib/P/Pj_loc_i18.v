(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue F_memset Pj_steps Pj_once.
From OSSVerify.simdjson.fuzz_dump.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition call_once_post_18 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xde368); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells psegs m' 0xde368 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells psegs m' 0xde3e8 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells psegs m' 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m' 0xdf128 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_18 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x101000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells psegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0xde368); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells psegs m 0xde368 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells psegs m 0xde3e8 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells psegs m 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xccc30 [C8 (Z_to_bv 64 0xffcd8)] -> rw_cells psegs m 0xffcd8 [C8 canary] ->
  rw_cells psegs m 0xdf128 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv psegs m ->
  evt psegs (call_once_post_18 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xde368) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0xa7950) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa9114) fc None m (seg_rom psegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m) as MU.
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
  unfold call_once_post_18. sys_finish.
Qed.

Definition append_post_18 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (0xde8c0, 0xde8c8); (0xde960, 0xde968)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde968); C8 (Z_to_bv 64 0xde9c0)]
    /\ rw_cells psegs m' 0xde960 [CB 8 (repeat (Z_to_bv 8 0) 8)].

Lemma append_spec_18 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 80)%Z -> (0x101000 <= lo)%Z ->
  rw_cells psegs m 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde960); C8 (Z_to_bv 64 0xde9c0)] ->
  rw_cells psegs m 0xde960 [CB 8 junk8] -> mem_inv psegs m ->
  evt psegs (append_post_18 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xde8b8) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6600) fc None m (seg_rom psegs)).
Proof.
  intros until junk8. intros ST LO LOLO VEC SLOT MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xde8c0, 0xde8c8); (0xde960, 0xde968)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 80%nat ST.
  do 17 lstep. if_true. lstep. if_false.
  do 5 lstep.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 0xde960 0 8 junk8)%Z; [exact SLOT | assumption | lia | lia | lia | lia |].
  rename POST into SLOT. change (Z.to_nat 8) with 8%nat in SLOT. change (0 mod 256)%Z with 0%Z in SLOT.
  do 15 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold append_post_18. sys_finish.
Qed.

Definition install_post_18 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xde678, 0xde680); (0xde8c0, 0xde8c8); (0xde960, 0xde968);
              (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xde368 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 19)]
    /\ rw_cells psegs m' 0xde3e8 [C4 (Z_to_bv 64 19)]
    /\ rw_cells psegs m' 0xde678 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells psegs m' 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde968); C8 (Z_to_bv 64 0xde9c0)]
    /\ rw_cells psegs m' 0xde960 [C8 (Z_to_bv 64 0xde670)]
    /\ rw_cells psegs m' 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m' 0xdf128 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma install_spec_18 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 240)%Z -> (0x101000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells psegs m 0xde368 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells psegs m 0xde3e8 [C4 (Z_to_bv 64 18)] ->
  rw_cells psegs m 0xde678 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells psegs m 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde960); C8 (Z_to_bv 64 0xde9c0)] ->
  rw_cells psegs m 0xde960 [CB 8 junk8] ->
  rw_cells psegs m 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xccc30 [C8 (Z_to_bv 64 0xffcd8)] -> rw_cells psegs m 0xffcd8 [C8 canary] ->
  rw_cells psegs m 0xdf128 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv psegs m ->
  evt psegs (install_post_18 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v canary pad1 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xde8a8) (Z_to_bv 64 0xde670) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x903f4) fc None m (seg_rom psegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI IDF NID RC RV VEC SLOT MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xde678, 0xde680); (0xde8c0, 0xde8c8); (0xde960, 0xde968);
              (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 80%nat ST.
  do 7 lstep.
  do 9 lstep. if_false.
  do 10 lstep.
  lazymatch type of FR with
  | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
      apply (rw_cells_app psegs _ _ [c0; c1; c2; c3] rest) in FR; destruct FR as [PACK FR]
  end.
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in FR by lia.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = (bv_unsigned sp + -80)%Z) by (apply unsigned_lit; lia).
  replace (bv_unsigned sp + -56)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 24)%Z in PACK by lia.
  replace (bv_unsigned sp + -72)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 8)%Z in PACK by lia.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 16)%Z by lia.
  rewrite <- Hsp in PACK at 1. rewrite <- Hsp in ST.
  call call_once_spec_18;
    [exact ST | lia | lia | lia | exact PACK | exact IDF | exact NID | lia | exact MUT | exact GOT | exact CAN | exact CV | exact LP | assumption |].
  rename PC into ST. rewrite Hsp in ST. clear PACK. rename PC0 into PACK. rename PC1 into IDF. rename PC2 into NID. rename PC3 into MUT. rename POST into CV.
  change (18 + 1)%Z with 19%Z in *.
  lstep.
  replace (sx32 (Z_to_bv 64 19)) with (Z_to_bv 64 19) by (vm_compute; reflexivity).
  lstep. lstep.
  amo_step.
  change (amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1)) with (Z_to_bv 64 v + Z_to_bv 64 1 : word) in RC. rewrite lit_add_lit in RC.
  lstep. lstep. lstep. lstep. lstep. lstep.
  lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. lstep.
  call_sp append_spec_18; [exact ST | lia | lia | exact VEC | exact SLOT | assumption |].
  rename PC into ST. rename PC0 into VEC. rename POST into SLOT.
  lstep. lstep. lstep. lstep. lstep.
  replace (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with z64 by (apply bv_eq; vm_compute; reflexivity).
  lstep. if_true.
  lstep. lstep. lstep.
  do 8 lstep.
  rewrite ?unsigned_lit in PACK by lia.
  release_frame PACK ST (bv_unsigned sp + -48)%Z.
  release_frame FR ST (bv_unsigned sp).
  unfold install_post_18. sys_finish.
Qed.

Definition seg_post_18 (sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x8e9a4) sp gp tp t0 t1 t2 (Z_to_bv 64 0xde8a8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0xde470) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x8e9a4) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xde670, 0xde680); (0xde8c0, 0xde8c8); (0xde960, 0xde968); (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xde368 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 0x13)]
    /\ rw_cells psegs m' 0xde3e8 [C4 (Z_to_bv 64 0x13)]
    /\ rw_cells psegs m' 0xde670 [C8 (Z_to_bv 64 0xcbe38)]
    /\ rw_cells psegs m' 0xde678 [C8 (Z_to_bv 64 1)]
    /\ rw_cells psegs m' 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde968); C8 (Z_to_bv 64 0xde9c0)]
    /\ rw_cells psegs m' 0xde960 [C8 (Z_to_bv 64 0xde670)]
    /\ rw_cells psegs m' 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells psegs m' 0xdf128 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma seg_spec_18 : forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 240)%Z -> (0x101000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells psegs m 0xde368 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xde3e8 [C4 (Z_to_bv 64 0x12)] ->
  rw_cells psegs m 0xde670 [C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xde678 [C8 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xde8b8 [C8 (Z_to_bv 64 0xde8d0); C8 (Z_to_bv 64 0xde960); C8 (Z_to_bv 64 0xde9c0)] ->
  rw_cells psegs m 0xde960 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells psegs m 0xdf100 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xccc30 [C8 (Z_to_bv 64 0xffcd8)] -> rw_cells psegs m 0xffcd8 [C8 canary] ->
  rw_cells psegs m 0xdf128 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv psegs m ->
  evt psegs (seg_post_18 sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0xde8a8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0xde470) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8e988) fc None m (seg_rom psegs)).
Proof.
  intros until canary. intros ST LO LOLO HI IDF NID FC0 RC VEC SLOT MUT GOT CAN CV MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0xde368, 0xde374); (0xde3e8, 0xde3ec); (0xde670, 0xde680); (0xde8c0, 0xde8c8); (0xde960, 0xde968); (0xdf104, 0xdf108); (0xdf130, 0xdf138); (0xdf148, 0xdf14c); (0xdf150, 0xdf158)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  do 7 lstep.
  call (install_spec_18 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z); [exact ST | lia | lia | lia | exact IDF | exact NID | exact RC | lia | exact VEC | exact SLOT | exact MUT | exact GOT | exact CAN | exact CV | reflexivity | assumption |].
  change (0 + 1)%Z with 1%Z in *.
  unfold seg_post_18. sys_finish.
Qed.
