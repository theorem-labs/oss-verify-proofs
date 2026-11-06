(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SumsLib Pm8_code_81000_82000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
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

Theorem asan_addrisinmem : addrisinmem_spec Asan.M.loaded_segments 0x81d70 0x153140 0x153148 0x153150 0x15d6a8 0x15d6b0 0x15d6a0.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x81d70) with (0x81d70 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x81d70 + 556)) with (0x81f9c : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn Asan.M.loaded_segments mem (0x15d6a8 : word) 8 = Some bs4) by (replace (0x15d6a8 : word) with (Z_to_bv 64 0x15d6a8) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn Asan.M.loaded_segments mem (0x15d6b0 : word) 8 = Some bs5) by (replace (0x15d6b0 : word) with (Z_to_bv 64 0x15d6b0) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn Asan.M.loaded_segments mem (0x15d6a0 : word) 8 = Some bs6) by (replace (0x15d6a0 : word) with (Z_to_bv 64 0x15d6a0) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  -
    eexists. split.
    ab_tk F_81d20 D_81d20 condz.
    av F_81ef8 D_81ef8 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_81efc D_81efc condz.
    an F_81f00 D_81f00.
    an F_81f04 D_81f04. rewrite Hsum.
    ab_tk F_81f08 D_81f08 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  -
    eexists. split.
    ab_ft F_81d20 D_81d20 condz.
    an F_81d24 D_81d24.
    ld_step F_81d28 D_81d28 bs1 (0x15d6a8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_81d2c D_81d2c.
    ld_step F_81d30 D_81d30 bs2 (0x15d6b0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_81d34 D_81d34 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_81d38 D_81d38 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_81d3c D_81d3c.
    ab_tk F_81d40 D_81d40 condz.
    an F_81d48 D_81d48.
    ld_step F_81d4c D_81d4c bs3 (0x15d6a0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_81d50 D_81d50 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_81d54 D_81d54.
    an F_81d58 D_81d58.
    ab_ft F_81d5c D_81d5c condz.
    ab_tk F_81d60 D_81d60 condz.
    ld_step F_81e28 D_81e28 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_81e2c D_81e2c.
    an F_81e30 D_81e30.
    ab_ft F_81e34 D_81e34 condz.
    ab_tk F_81e38 D_81e38 condz.
    av F_81ef8 D_81ef8 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_81efc D_81efc condz.
    an F_81f00 D_81f00.
    an F_81f04 D_81f04. rewrite Hsum.
    ab_ft F_81f08 D_81f08 condz.
    an F_81f0c D_81f0c.
    ld_step F_81f10 D_81f10 bs1 (0x15d6a8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_81f14 D_81f14.
    ld_step F_81f18 D_81f18 bs2 (0x15d6b0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_81f1c D_81f1c bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_81f20 D_81f20 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_81f24 D_81f24.
    ab_tk F_81f28 D_81f28 condz.
    an F_81f30 D_81f30.
    ld_step F_81f34 D_81f34 bs3 (0x15d6a0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_81f38 D_81f38 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_81f3c D_81f3c.
    an F_81f40 D_81f40.
    ab_ft F_81f44 D_81f44 condz.
    ab_ft F_81f48 D_81f48 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
