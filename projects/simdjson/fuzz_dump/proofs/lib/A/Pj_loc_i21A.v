(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 IcptSpec D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new
     Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA.
From OSSVerify.simdjson.fuzz_dump.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition call_once_post_21 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x69d598); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells asegs m' 0x69d598 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells asegs m' 0x69d5e8 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells asegs m' 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x69e328 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)].

Lemma call_once_spec_21 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6c1000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells asegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x69d598); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells asegs m 0x69d598 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells asegs m 0x69d5e8 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells asegs m 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x162ca8 [C8 (Z_to_bv 64 0x6beca8)] -> ro_cells asegs m 0x6beca8 [C8 canary] ->
  rw_cells asegs m 0x69e328 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv asegs m ->
  evt asegs (call_once_post_21 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x69d598) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x139b20) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b2e4) fc None m (seg_rom asegs)).
Proof.
  intros until pad2. intros ST LO LOLO HI PACK FLAG NID RK MUT GOT CAN CV LP MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m) as MU.
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
  unfold call_once_post_21. sys_finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition append_postA_21 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x69dac0, 0x69dac8); (0x69db78, 0x69db80)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db80); C8 (Z_to_bv 64 0x69dbc0)]
    /\ rw_cells asegs m' 0x69db78 [CB 8 (repeat (Z_to_bv 8 0) 8)]).

Lemma append_aevt_21 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk asegs m lo (bv_unsigned sp) -> (lo + 80 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells asegs m 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db78); C8 (Z_to_bv 64 0x69dbc0)] ->
  rw_cells asegs m 0x69db78 [CB 8 junk8] -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', append_postA_21 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x69dab8) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1387d0) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until junk8. intros ST LO LOR SPT SPA VEC SLOT MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x69dac0, 0x69dac8); (0x69db78, 0x69db80)]%Z.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat ST.
  do 17 lstep. if_true. lstep. if_false.
  do 5 lstep.
  acall_sp (memsetA_spec RT RTC PMc FDO MST Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  F fc _ 0x69db78 0 8 junk8 lo); [exact SLOT | lia | lia | lia | lia | a_chk | a_cl | exact ARTX | assumption | a_call_ok | apost_call].
  rename PC into ST. rename POST into SLOT. change (Z.to_nat 8) with 8%nat in SLOT. change (0 mod 256)%Z with 0%Z in SLOT.
  do 15 lstep.
  release_frame FR ST (bv_unsigned sp).
  afinish.
Qed.

Definition install_postA_21 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a8, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80);
              (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x69d598 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 22)]
    /\ rw_cells asegs m' 0x69d5e8 [C4 (Z_to_bv 64 22)]
    /\ rw_cells asegs m' 0x69d8a8 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells asegs m' 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db80); C8 (Z_to_bv 64 0x69dbc0)]
    /\ rw_cells asegs m' 0x69db78 [C8 (Z_to_bv 64 0x69d8a0)]
    /\ rw_cells asegs m' 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x69e328 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)]).

Lemma install_aevt_21 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells asegs m 0x69d598 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells asegs m 0x69d5e8 [C4 (Z_to_bv 64 21)] ->
  rw_cells asegs m 0x69d8a8 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells asegs m 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db78); C8 (Z_to_bv 64 0x69dbc0)] ->
  rw_cells asegs m 0x69db78 [CB 8 junk8] ->
  rw_cells asegs m 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x162ca8 [C8 (Z_to_bv 64 0x6beca8)] -> ro_cells asegs m 0x6beca8 [C8 canary] ->
  rw_cells asegs m 0x69e328 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv asegs m -> ART RT Σ m ->
  (forall ms', install_postA_21 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo v canary pad1 pad2 m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x69daa8) (Z_to_bv 64 0x69d8a0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x122990) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until pad2. intros ST LO LOR SPT SPA HI IDF NID RC RV VEC SLOT MUT GOT CAN CV LP MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a8, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80);
              (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a8, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80);
              (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z.
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
  call call_once_spec_21;
    [exact ST | lia | lia | lia | exact PACK | exact IDF | exact NID | lia | exact MUT | exact GOT | exact CAN | exact CV | exact LP | assumption |].
  rename PC into ST. rewrite Hsp in ST. clear PACK. rename PC0 into PACK. rename PC1 into IDF. rename PC2 into NID. rename PC3 into MUT. rename POST into CV.
  change (21 + 1)%Z with 22%Z in *.
  lstep.
  replace (sx32 (Z_to_bv 64 22)) with (Z_to_bv 64 22) by (vm_compute; reflexivity).
  lstep. lstep.
  amo_step.
  change (amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1)) with (Z_to_bv 64 v + Z_to_bv 64 1 : word) in RC. rewrite lit_add_lit in RC.
  lstep. lstep. lstep. lstep. lstep. lstep.
  lstep. if_false.
  lstep. lstep. if_false.
  lstep. lstep. lstep.
  acall_sp (append_aevt_21 Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | exact VEC | exact SLOT | assumption | exact ARTX | apost_call].
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

Definition seg_postA_21 (Σ : rts RT) (sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x120bc8) sp gp tp t0 t1 t2 (Z_to_bv 64 0x69daa8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x69d670) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x120bc8) fc None m' (seg_rom asegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a0, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80); (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ ART RT Σ m'
    /\ (stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x69d598 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 0x16)]
    /\ rw_cells asegs m' 0x69d5e8 [C4 (Z_to_bv 64 0x16)]
    /\ rw_cells asegs m' 0x69d8a0 [C8 (Z_to_bv 64 0x1615a0)]
    /\ rw_cells asegs m' 0x69d8a8 [C8 (Z_to_bv 64 1)]
    /\ rw_cells asegs m' 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db80); C8 (Z_to_bv 64 0x69dbc0)]
    /\ rw_cells asegs m' 0x69db78 [C8 (Z_to_bv 64 0x69d8a0)]
    /\ rw_cells asegs m' 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0x69e328 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).

Lemma seg_aevt_21 : forall Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk asegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells asegs m 0x69d598 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x69d5e8 [C4 (Z_to_bv 64 0x15)] ->
  rw_cells asegs m 0x69d8a0 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x69d8a8 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x69dab8 [C8 (Z_to_bv 64 0x69dad0); C8 (Z_to_bv 64 0x69db78); C8 (Z_to_bv 64 0x69dbc0)] ->
  rw_cells asegs m 0x69db78 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells asegs m 0x69e300 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells asegs m 0x162ca8 [C8 (Z_to_bv 64 0x6beca8)] -> ro_cells asegs m 0x6beca8 [C8 canary] ->
  rw_cells asegs m 0x69e328 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv asegs m -> ART RT Σ m ->
  (forall ms', seg_postA_21 Σ sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x69daa8) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x69d670) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x120bac) fc None m (seg_rom asegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI IDF NID FC0 RC VEC SLOT MUT GOT CAN CV MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a0, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80); (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  astart (bv_unsigned sp) [(0x69d598, 0x69d5a4); (0x69d5e8, 0x69d5ec); (0x69d8a0, 0x69d8b0); (0x69dac0, 0x69dac8); (0x69db78, 0x69db80); (0x69e304, 0x69e308); (0x69e330, 0x69e338); (0x69e348, 0x69e34c); (0x69e350, 0x69e358)]%Z.
  apply (aevt_evt RT AF PMc MST).
  do 7 lstep.
  acall (install_aevt_21 Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact IDF | exact NID | exact RC | lia | exact VEC | exact SLOT | exact MUT | exact GOT | exact CAN | exact CV | reflexivity | assumption | exact ARTX | apost_call].
  change (0 + 1)%Z with 1%Z in *.
  afinish.
Qed.

End AevtPieces.
