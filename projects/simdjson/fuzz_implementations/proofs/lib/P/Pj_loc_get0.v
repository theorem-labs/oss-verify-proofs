(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_imp Pj_loc_get Imp_ios_defs.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition classic_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ja1 ja2 ja3 ja4 ja5 jb1 jb2 jb3 jb4 jb5 jb6 jb7 jb8 jb9 jb10 jb11 jb12 jb13 jb14 jb15 jb16 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe87b0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp - 576, bv_unsigned sp); (0xe85d8, 0xe87ba); (0xe87d0, 0xe9488)]%Z m m'
    /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' 0xe85d8 (impb_A ja1 ja2 ja3 ja4 ja5)
    /\ rw_cells psegs m' 0xe87b0 [C8 (Z_to_bv 64 0xe8bd8); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
    /\ rw_cells psegs m' 0xe87d0 (impb_B jb1 jb2 jb3 jb4 jb5 jb6 jb7 jb8 jb9 jb10 jb11 jb12 jb13 jb14 jb15 jb16).

Lemma classic_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 576)%Z -> (0x10b000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells psegs m 0xe85d8 imp0_A ->
  rw_cells psegs m 0xe87b0 [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells psegs m 0xe87d0 imp0_B ->
  rw_cells psegs m 0xd66b0 [C8 (Z_to_bv 64 0x10a008)] -> rw_cells psegs m 0x10a008 [C8 canary] ->
  rw_cells psegs m 0x10a02b [C1 (Z_to_bv 8 0)] -> rw_cells psegs m 0x10a100 [C4 (Z_to_bv 64 0)] -> mem_inv psegs m ->
  evt psegs (classic_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a788) fc None m (seg_rom psegs)).
Proof.
  intros until canary. intros ST LO LOLO HI RA CLS RB GOT CAN NL LK MI.
  unfold imp0_A in RA. unfold imp0_B in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 576, bv_unsigned sp); (0xe85d8, 0xe87ba); (0xe87d0, 0xe9488)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  carve_frame 32%nat ST.
  do 10 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp imp_ctor_spec; [exact ST | lia | lia | lia | exact RA | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption |].
  rename PC into ST. rename PC0 into RA. rename POST into RB. unfold impb_A in RA.
  do 16 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold classic_post. sys_finish; eassumption.
Qed.

Definition locale_ctor_postX (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo D K : Z) (W : list (Z * Z)) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch ((bv_unsigned sp - K, bv_unsigned sp) :: (D, D + 8) :: W)%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' D [C8 (Z_to_bv 64 0xe8bd8)]
    /\ LOCB m' /\ locx m'.

Ltac cells_sub H n k A' nm :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let T := fresh "T" in
      pose proof (proj2 (rw_cells_split_n segs m A cs n A' H eq_refl)) as T; cbv [skipn] in T;
      lazymatch type of T with rw_cells _ _ _ ?cs2 =>
        pose proof (proj1 (rw_cells_split_n segs m A' cs2 k (A' + Z.of_nat (cells_size (firstn k cs2)))%Z T eq_refl)) as nm;
        cbv [firstn] in nm; clear T end
  end.

Lemma locale_ctor_spec0S : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte) (canary : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 608)%Z -> (0x10b000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  LOC0 m -> rw_cells psegs m D [CB 8 j] -> (0xd66b8 <= D)%Z -> (D + 8 <= 0xe85d8)%Z ->
  rw_cells psegs m 0xd66b0 [C8 (Z_to_bv 64 0x10a008)] -> rw_cells psegs m 0x10a008 [C8 canary] ->
  rw_cells psegs m 0x10a02b [C1 (Z_to_bv 8 0)] -> rw_cells psegs m 0x10a100 [C4 (Z_to_bv 64 0)] -> mem_inv psegs m ->
  evt psegs (locale_ctor_postX ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D 608 [(0xe85d8, 0xe9488)%Z] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa059c) fc None m (seg_rom psegs)).
Proof.
  intros until canary. intros ST LO LOLO HI L0 DST RD1 RD2 GOT CAN NL LK MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp); (D, D + 8); (0xe85d8, 0xe9488)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold LOC0, loc0_cells in L0.
  retype L0 [CB 472 (repeat (Z_to_bv 8 0) 472);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             CB 3256 (repeat (Z_to_bv 8 0) 3256)].
  take L0 1%nat 0xe87b0%Z RA. take L0 3%nat 0xe87ba%Z CLS. take L0 1%nat 0xe87c0%Z P1.
  take L0 3%nat 0xe87ca%Z GLB. take L0 1%nat 0xe87d0%Z P2. rename L0 into RB.
  carve_frame 32%nat ST.
  do 11 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  lstep.
  call_sp classic_spec; [exact ST | lia | lia | lia | exact RA | exact CLS | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption |].
  rename PC into ST. rename PC0 into RA. rename PC1 into CLS. rename POST into RB. unfold impb_A in RA. unfold impb_B in RB.
  do 4 lstep.
  if_true.
  do 12 lstep.
  if_true.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).

  glue RA CLS. glue RA P1. glue RA GLB. glue RA P2. glue RA RB.
  pose proof RA as RX. cells_sub RX 4%nat 2%nat 0xe8720%Z LX1. cells_sub RX 7%nat 2%nat 0xe8730%Z LX2. cells_sub RX 29%nat 1%nat 0xe88f0%Z LX3. cells_sub RX 33%nat 1%nat 0xe8a80%Z LX4. cells_sub RX 35%nat 1%nat 0xe8a90%Z LX5. cells_sub RX 52%nat 2%nat 0xe8c20%Z LX6. clear RX.
  merge_at RA 51%nat 4%nat. merge_at RA 32%nat 5%nat. merge_at RA 28%nat 3%nat. merge_at RA 20%nat 3%nat. merge_at RA 13%nat 5%nat. merge_at RA 3%nat 7%nat.
  unfold locale_ctor_postX. sys_finish.
  - unfold LOCB, locb_cells. do 15 eexists. exact RA.
  - unfold locx, locx3. repeat match goal with |- _ /\ _ => split end; [exact LX3 | exact LX4 | exact LX5 | exact LX1 | exact LX2 | exact LX6].
Qed.

