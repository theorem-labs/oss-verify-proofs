(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit Sj_num_amem. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Pj_mciA Pj_loc_akitA Pj_onceA.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition call_once_post_0 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6a66a8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells asegs m' 0x6a66a8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells asegs m' 0x6a67e8 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells asegs m' 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x6a7528 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_0 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6ca000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells asegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6a66a8); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells asegs m 0x6a66a8 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells asegs m 0x6a67e8 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells asegs m 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] -> ro_cells asegs m 0x6c7ea8 [C8 canary] ->
  rw_cells asegs m 0x6a7528 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv asegs m ->
  evt asegs (call_once_post_0 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a66a8) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x141a90) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x143254) fc None m (seg_rom asegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
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
  unfold call_once_post_0. sys_finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition append_postA_0 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6a6cb8 [C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6cd8); C8 (Z_to_bv 64 0x6a6dc0)]
    /\ rw_cells asegs m' 0x6a6cd0 [CB 8 (repeat (Z_to_bv 8 0) 8)]).

Lemma append_aevt_0 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk asegs m lo (bv_unsigned sp) -> (lo + 80 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells asegs m 0x6a6cb8 [C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6dc0)] ->
  rw_cells asegs m 0x6a6cd0 [CB 8 junk8] -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', append_postA_0 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a6cb8) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140740) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until junk8. intros ST LO LOR SPT SPA VEC SLOT MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8)]%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat ST.
  do 17 lstep. if_true. lstep. if_false.
  do 5 lstep.
  acall_sp (memsetA_spec RT RTC PMc FDO MST Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  F fc _ 0x6a6cd0 0 8 junk8 lo); [exact SLOT | lia | lia | lia | lia | a_chk | a_cl | exact ARTX | assumption | a_call_ok | apost_call].
  rename PC into ST. rename POST into SLOT. change (Z.to_nat 8) with 8%nat in SLOT. change (0 mod 256)%Z with 0%Z in SLOT.
  do 15 lstep.
  release_frame FR ST (bv_unsigned sp).
  afinish.
Qed.

Definition install_postA_0 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6998, 0x6a69a0); (0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6a66a8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x6a67e8 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x6a6998 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells asegs m' 0x6a6cb8 [C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6cd8); C8 (Z_to_bv 64 0x6a6dc0)]
    /\ rw_cells asegs m' 0x6a6cd0 [C8 (Z_to_bv 64 0x6a6990)]
    /\ rw_cells asegs m' 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x6a7528 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)]).

Lemma install_aevt_0 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells asegs m 0x6a66a8 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells asegs m 0x6a67e8 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6998 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells asegs m 0x6a6cb8 [C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6dc0)] ->
  rw_cells asegs m 0x6a6cd0 [CB 8 junk8] ->
  rw_cells asegs m 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] -> ro_cells asegs m 0x6c7ea8 [C8 canary] ->
  rw_cells asegs m 0x6a7528 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', install_postA_0 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo v canary pad1 pad2 m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a6ca8) (Z_to_bv 64 0x6a6990) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x128e7c) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until pad2. intros ST LO LOR SPT SPA HI IDF NID RC RV VEC SLOT MUT GOT CAN CV LP MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6998, 0x6a69a0); (0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6998, 0x6a69a0); (0x6a6cc0, 0x6a6cc8); (0x6a6cd0, 0x6a6cd8);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat ST.
  do 7 lstep.
  do 9 lstep. if_false.
  do 10 lstep.
  lazymatch type of FR with
  | rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
      apply (rw_cells_app asegs _ _ [c0; c1; c2; c3] rest) in FR; destruct FR as [PACK FR]
  end.
  cbn [cells_size csize Nat.add] in FR.
  replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in FR by lia.
  assert (Hsp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = (bv_unsigned sp + -80)%Z) by (apply unsigned_lit; lia).
  replace (bv_unsigned sp + -56)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 24)%Z in PACK by lia.
  replace (bv_unsigned sp + -72)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 8)%Z in PACK by lia.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 16)%Z by lia.
  rewrite <- Hsp in PACK at 1. rewrite <- Hsp in ST.
  call call_once_spec_0;
    [exact ST | lia | lia | lia | exact PACK | exact IDF | exact NID | lia | exact MUT | exact GOT | exact CAN | exact CV | exact LP | assumption |].
  rename PC into ST. rewrite Hsp in ST. clear PACK. rename PC0 into PACK. rename PC1 into IDF. rename PC2 into NID. rename PC3 into MUT. rename POST into CV.
  change (0 + 1)%Z with 1%Z in *.
  lstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
  lstep. lstep.
  amo_step.
  change (amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1)) with (Z_to_bv 64 v + Z_to_bv 64 1 : word) in RC. rewrite lit_add_lit in RC.
  lstep. lstep. lstep. lstep. lstep. lstep.
  lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. lstep.
  acall_sp (append_aevt_0 Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | exact VEC | exact SLOT | assumption | exact ARTX | apost_call].
  rename PC into ST. rename PC0 into VEC. rename POST into SLOT.
  lstep. lstep. lstep. lstep. lstep.
  replace (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with z64 by (apply bv_eq; vm_compute; reflexivity).
  lstep. if_true.
  lstep. lstep. lstep.
  do 8 lstep.
  rewrite ?unsigned_lit in PACK by lia.
  release_frame PACK ST (bv_unsigned sp + -48)%Z.
  release_frame FR ST (bv_unsigned sp).
  afinish.
Qed.

Definition seg_postA_0 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) j8 (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x128894) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 0x6a6ca8) (Z_to_bv 64 0x6a6cd0) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 0x6a6870) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x128894) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6990, 0x6a69a0); (0x6a6ca8, 0x6a6dcb);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x6a66a8 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x6a67e8 [C4 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x6a6990 [C8 (Z_to_bv 64 0x168990)]
    /\ rw_cells asegs m' 0x6a6998 [C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x6a6ca8 [C8 (Z_to_bv 64 0x167f70); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x6a6cb8 [C8 (Z_to_bv 64 0x6a6cd0); C8 (Z_to_bv 64 0x6a6cd8); C8 (Z_to_bv 64 0x6a6dc0)]
    /\ rw_cells asegs m' 0x6a6cd0 [C8 (Z_to_bv 64 0x6a6990)]
    /\ rw_cells asegs m' 0x6a6cd8 [CB 232 (repeat (Z_to_bv 8 0) 232)]
    /\ rw_cells asegs m' 0x6a6dc0 [C8 (Z_to_bv 64 1); C2 (Z_to_bv 64 0x4302); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x6a7528 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).

Lemma seg_aevt_0 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 288 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells asegs m 0x6a66a8 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a67e8 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6990 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6998 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6ca8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6cb8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x6a6cd0 [CB 240 (repeat (Z_to_bv 8 0) 240)] ->
  rw_cells asegs m 0x6a6dc0 [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x6a7500 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] -> ro_cells asegs m 0x6c7ea8 [C8 canary] ->
  rw_cells asegs m 0x6a7528 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv asegs m -> ART RT Σ m ->
  (forall ms', seg_postA_0 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a6ca8) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x128804) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI IDF NID FC0 RC IMPH VEC SLOTS TAIL MUT GOT CAN CV MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 288, bv_unsigned sp); (0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6990, 0x6a69a0); (0x6a6ca8, 0x6a6dcb);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x6a66a8, 0x6a66b4); (0x6a67e8, 0x6a67ec); (0x6a6990, 0x6a69a0); (0x6a6ca8, 0x6a6dcb);
              (0x6a7504, 0x6a7508); (0x6a7530, 0x6a7538); (0x6a7548, 0x6a754c); (0x6a7550, 0x6a7558)]%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 48%nat ST.
  do 21 lstep.
  lstep.
  acall_sp (memsetA_spec RT RTC PMc FDO MST Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  F fc _ 0x6a6cd0 0 240 (repeat (Z_to_bv 8 0) 240) lo); [exact SLOTS | lia | lia | lia | lia | a_chk | a_cl | exact ARTX | assumption | a_call_ok | apost_call].
  rename PC into ST. rename POST into SLOTS. change (Z.to_nat 240) with 240%nat in SLOTS. change (0 mod 256)%Z with 0%Z in SLOTS.
  apply (rw_cells_split_CB asegs _ _ [] 240 _ [] [8; 232]%nat) in SLOTS; [|reflexivity].
  cbn [mk_CB_cells app] in SLOTS.
  apply (rw_cells_app asegs _ _ [_] [_]) in SLOTS. destruct SLOTS as [SLOT SLOTS].
  cbn [cells_size csize Nat.add] in SLOTS. change (0x6a6cd0 + Z.of_nat 8)%Z with 0x6a6cd8%Z in SLOTS.
  change (firstn 8 (repeat (Z_to_bv 8 0) 240)) with (repeat (Z_to_bv 8 0) 8) in SLOT.
  change (firstn 232 (skipn 8 (repeat (Z_to_bv 8 0) 240))) with (repeat (Z_to_bv 8 0) 232) in SLOTS.
  do 13 lstep.
  lstep.
  acall_sp (install_aevt_0 Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact IDF | exact NID | exact RC | lia | exact VEC | exact SLOT | exact MUT | exact GOT | exact CAN | exact CV | reflexivity | assumption | exact ARTX | apost_call].
  change (0 + 1)%Z with 1%Z in *.
  afinish.
Qed.

End AevtPieces.
