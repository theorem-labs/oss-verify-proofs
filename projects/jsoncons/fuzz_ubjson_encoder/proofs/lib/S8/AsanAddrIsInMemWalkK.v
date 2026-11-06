(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import SumsLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAIM_codeK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition aim_clob : list reg := [5; 6; 7; 11; 14; 15; 16; 17; 28].

Definition addrisinmem_spec (SEGS : list Segment) (entry got1 got2 got3 g1 g2 g3 : Z) : Prop :=
  forall (mem rom : word -> option byte) (regs : bvmap 5 word) (a sz : word) (bs1 bs2 bs3 bs4 bs5 bs6 : list byte),
  getr regs 10 = a -> getr regs 11 = sz ->
  getr regs 9 = Z_to_bv 64 0x7fff8000 -> getr regs 14 = Z_to_bv 64 0x7fff7fff ->
  rdn SEGS mem (Z_to_bv 64 got1) 8 = Some bs1 -> bytes_le_to_Z bs1 = g1 ->
  rdn SEGS mem (Z_to_bv 64 got2) 8 = Some bs2 -> bytes_le_to_Z bs2 = g2 ->
  rdn SEGS mem (Z_to_bv 64 got3) 8 = Some bs3 -> bytes_le_to_Z bs3 = g3 ->
  rdn SEGS mem (Z_to_bv 64 g1) 8 = Some bs4 -> bytes_le_to_Z bs4 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 g2) 8 = Some bs5 -> bytes_le_to_Z bs5 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 g3) 8 = Some bs6 -> bytes_le_to_Z bs6 = (2^47 - 1)%Z ->
  (8 <= bv_unsigned sz)%Z -> (bv_unsigned sz mod 8 = 0)%Z ->
  ((bv_unsigned a + bv_unsigned sz <= 0x7fff7000)%Z
   \/ (0x10007fff8000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned sz <= 2^47)%Z) ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 entry) mem rom) (mkst regs' (Z_to_bv 64 (entry + 0x22c)) mem rom)
    /\ getr regs' 11 = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)
    /\ regs_agree (fun r => In r aim_clob) regs regs'.

Theorem asan_addrisinmem : addrisinmem_spec Asan.M.loaded_segments 0x7b514 0x1391c0 0x1391c8 0x1391d0 0x1426e8 0x1426f0 0x1426e0.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x7b514) with (0x7b514 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x7b514 + 556)) with (0x7b740 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn Asan.M.loaded_segments mem (0x1426e8 : word) 8 = Some bs4) by (replace (0x1426e8 : word) with (Z_to_bv 64 0x1426e8) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn Asan.M.loaded_segments mem (0x1426f0 : word) 8 = Some bs5) by (replace (0x1426f0 : word) with (Z_to_bv 64 0x1426f0) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn Asan.M.loaded_segments mem (0x1426e0 : word) 8 = Some bs6) by (replace (0x1426e0 : word) with (Z_to_bv 64 0x1426e0) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  -
    eexists. split.
    ab_tk F_7b4c4 D_7b4c4 condz.
    av F_7b69c D_7b69c (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7b6a0 D_7b6a0 condz.
    an F_7b6a4 D_7b6a4.
    an F_7b6a8 D_7b6a8. rewrite Hsum.
    ab_tk F_7b6ac D_7b6ac condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  -
    eexists. split.
    ab_ft F_7b4c4 D_7b4c4 condz.
    an F_7b4c8 D_7b4c8.
    ld_step F_7b4cc D_7b4cc bs1 (0x1426e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7b4d0 D_7b4d0.
    ld_step F_7b4d4 D_7b4d4 bs2 (0x1426f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7b4d8 D_7b4d8 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7b4dc D_7b4dc bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7b4e0 D_7b4e0.
    ab_tk F_7b4e4 D_7b4e4 condz.
    an F_7b4ec D_7b4ec.
    ld_step F_7b4f0 D_7b4f0 bs3 (0x1426e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7b4f4 D_7b4f4 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7b4f8 D_7b4f8.
    an F_7b4fc D_7b4fc.
    ab_ft F_7b500 D_7b500 condz.
    ab_tk F_7b504 D_7b504 condz.
    ld_step F_7b5cc D_7b5cc bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7b5d0 D_7b5d0.
    an F_7b5d4 D_7b5d4.
    ab_ft F_7b5d8 D_7b5d8 condz.
    ab_tk F_7b5dc D_7b5dc condz.
    av F_7b69c D_7b69c (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7b6a0 D_7b6a0 condz.
    an F_7b6a4 D_7b6a4.
    an F_7b6a8 D_7b6a8. rewrite Hsum.
    ab_ft F_7b6ac D_7b6ac condz.
    an F_7b6b0 D_7b6b0.
    ld_step F_7b6b4 D_7b6b4 bs1 (0x1426e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7b6b8 D_7b6b8.
    ld_step F_7b6bc D_7b6bc bs2 (0x1426f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7b6c0 D_7b6c0 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7b6c4 D_7b6c4 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7b6c8 D_7b6c8.
    ab_tk F_7b6cc D_7b6cc condz.
    an F_7b6d4 D_7b6d4.
    ld_step F_7b6d8 D_7b6d8 bs3 (0x1426e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7b6dc D_7b6dc bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7b6e0 D_7b6e0.
    an F_7b6e4 D_7b6e4.
    ab_ft F_7b6e8 D_7b6e8 condz.
    ab_ft F_7b6ec D_7b6ec condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
