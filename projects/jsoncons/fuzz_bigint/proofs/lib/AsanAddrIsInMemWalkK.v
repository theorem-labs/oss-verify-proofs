(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import SumsLib AsanAIM_codeK.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition aim_clob : list reg := [5; 6; 7; 11; 14; 15; 16; 17; 28].

(* [comment removed for export] *)
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

Theorem asan_addrisinmem : addrisinmem_spec Asan.M.loaded_segments 0x60fd0 0xd58c0 0xd58c8 0xd58d0 0xde828 0xde830 0xde820.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x60fd0) with (0x60fd0 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x60fd0 + 556)) with (0x611fc : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn Asan.M.loaded_segments mem (0xde828 : word) 8 = Some bs4) by (replace (0xde828 : word) with (Z_to_bv 64 0xde828) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn Asan.M.loaded_segments mem (0xde830 : word) 8 = Some bs5) by (replace (0xde830 : word) with (Z_to_bv 64 0xde830) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn Asan.M.loaded_segments mem (0xde820 : word) 8 = Some bs6) by (replace (0xde820 : word) with (Z_to_bv 64 0xde820) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  - (* [comment removed for export] *)
    eexists. split.
    ab_tk F_60fd0 D_60fd0 condz.
    av F_611a8 D_611a8 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_611ac D_611ac condz.
    an F_611b0 D_611b0.
    an F_611b4 D_611b4. rewrite Hsum.
    ab_tk F_611b8 D_611b8 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  - (* [comment removed for export] *)
    eexists. split.
    ab_ft F_60fd0 D_60fd0 condz.
    an F_60fd4 D_60fd4.
    ld_step F_60fd8 D_60fd8 bs1 (0xde828 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_60fdc D_60fdc.
    ld_step F_60fe0 D_60fe0 bs2 (0xde830 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_60fe4 D_60fe4 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_60fe8 D_60fe8 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_60fec D_60fec.
    ab_tk F_60ff0 D_60ff0 condz.
    an F_60ff8 D_60ff8.
    ld_step F_60ffc D_60ffc bs3 (0xde820 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_61000 D_61000 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_61004 D_61004.
    an F_61008 D_61008.
    ab_ft F_6100c D_6100c condz.
    ab_tk F_61010 D_61010 condz.
    ld_step F_610d8 D_610d8 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_610dc D_610dc.
    an F_610e0 D_610e0.
    ab_ft F_610e4 D_610e4 condz.
    ab_tk F_610e8 D_610e8 condz.
    av F_611a8 D_611a8 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_611ac D_611ac condz.
    an F_611b0 D_611b0.
    an F_611b4 D_611b4. rewrite Hsum.
    ab_ft F_611b8 D_611b8 condz.
    an F_611bc D_611bc.
    ld_step F_611c0 D_611c0 bs1 (0xde828 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_611c4 D_611c4.
    ld_step F_611c8 D_611c8 bs2 (0xde830 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_611cc D_611cc bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_611d0 D_611d0 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_611d4 D_611d4.
    ab_tk F_611d8 D_611d8 condz.
    an F_611e0 D_611e0.
    ld_step F_611e4 D_611e4 bs3 (0xde820 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_611e8 D_611e8 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_611ec D_611ec.
    an F_611f0 D_611f0.
    ab_ft F_611f4 D_611f4 condz.
    ab_ft F_611f8 D_611f8 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
