(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import SumsLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAIM_codeKB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
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

Theorem asan_addrisinmem : addrisinmem_spec AsanUbsan.M.loaded_segments 0x7bd3c 0x13d8d0 0x13d8d8 0x13d8e0 0x146de8 0x146df0 0x146de0.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x7bd3c) with (0x7bd3c : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x7bd3c + 556)) with (0x7bf68 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn AsanUbsan.M.loaded_segments mem (0x146de8 : word) 8 = Some bs4) by (replace (0x146de8 : word) with (Z_to_bv 64 0x146de8) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn AsanUbsan.M.loaded_segments mem (0x146df0 : word) 8 = Some bs5) by (replace (0x146df0 : word) with (Z_to_bv 64 0x146df0) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn AsanUbsan.M.loaded_segments mem (0x146de0 : word) 8 = Some bs6) by (replace (0x146de0 : word) with (Z_to_bv 64 0x146de0) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  -
    eexists. split.
    ab_tk F_7bcec D_7bcec condz.
    av F_7bec4 D_7bec4 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7bec8 D_7bec8 condz.
    an F_7becc D_7becc.
    an F_7bed0 D_7bed0. rewrite Hsum.
    ab_tk F_7bed4 D_7bed4 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  -
    eexists. split.
    ab_ft F_7bcec D_7bcec condz.
    an F_7bcf0 D_7bcf0.
    ld_step F_7bcf4 D_7bcf4 bs1 (0x146de8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7bcf8 D_7bcf8.
    ld_step F_7bcfc D_7bcfc bs2 (0x146df0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7bd00 D_7bd00 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7bd04 D_7bd04 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7bd08 D_7bd08.
    ab_tk F_7bd0c D_7bd0c condz.
    an F_7bd14 D_7bd14.
    ld_step F_7bd18 D_7bd18 bs3 (0x146de0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7bd1c D_7bd1c bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7bd20 D_7bd20.
    an F_7bd24 D_7bd24.
    ab_ft F_7bd28 D_7bd28 condz.
    ab_tk F_7bd2c D_7bd2c condz.
    ld_step F_7bdf4 D_7bdf4 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7bdf8 D_7bdf8.
    an F_7bdfc D_7bdfc.
    ab_ft F_7be00 D_7be00 condz.
    ab_tk F_7be04 D_7be04 condz.
    av F_7bec4 D_7bec4 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7bec8 D_7bec8 condz.
    an F_7becc D_7becc.
    an F_7bed0 D_7bed0. rewrite Hsum.
    ab_ft F_7bed4 D_7bed4 condz.
    an F_7bed8 D_7bed8.
    ld_step F_7bedc D_7bedc bs1 (0x146de8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7bee0 D_7bee0.
    ld_step F_7bee4 D_7bee4 bs2 (0x146df0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7bee8 D_7bee8 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7beec D_7beec bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7bef0 D_7bef0.
    ab_tk F_7bef4 D_7bef4 condz.
    an F_7befc D_7befc.
    ld_step F_7bf00 D_7bf00 bs3 (0x146de0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7bf04 D_7bf04 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7bf08 D_7bf08.
    an F_7bf0c D_7bf0c.
    ab_ft F_7bf10 D_7bf10 condz.
    ab_ft F_7bf14 D_7bf14 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
