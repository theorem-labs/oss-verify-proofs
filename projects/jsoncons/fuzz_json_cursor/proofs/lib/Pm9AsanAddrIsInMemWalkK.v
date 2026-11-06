(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SumsLib Pm9_code_82000_83000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
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

Theorem asan_addrisinmem : addrisinmem_spec AsanUbsan.M.loaded_segments 0x82130 0x154508 0x154510 0x154518 0x15e9e8 0x15e9f0 0x15e9e0.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x82130) with (0x82130 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x82130 + 556)) with (0x8235c : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn AsanUbsan.M.loaded_segments mem (0x15e9e8 : word) 8 = Some bs4) by (replace (0x15e9e8 : word) with (Z_to_bv 64 0x15e9e8) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn AsanUbsan.M.loaded_segments mem (0x15e9f0 : word) 8 = Some bs5) by (replace (0x15e9f0 : word) with (Z_to_bv 64 0x15e9f0) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn AsanUbsan.M.loaded_segments mem (0x15e9e0 : word) 8 = Some bs6) by (replace (0x15e9e0 : word) with (Z_to_bv 64 0x15e9e0) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  -
    eexists. split.
    ab_tk F_820e8 D_820e8 condz.
    av F_822c0 D_822c0 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_822c4 D_822c4 condz.
    an F_822c8 D_822c8.
    an F_822cc D_822cc. rewrite Hsum.
    ab_tk F_822d0 D_822d0 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  -
    eexists. split.
    ab_ft F_820e8 D_820e8 condz.
    an F_820ec D_820ec.
    ld_step F_820f0 D_820f0 bs1 (0x15e9e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_820f4 D_820f4.
    ld_step F_820f8 D_820f8 bs2 (0x15e9f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_820fc D_820fc bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_82100 D_82100 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_82104 D_82104.
    ab_tk F_82108 D_82108 condz.
    an F_82110 D_82110.
    ld_step F_82114 D_82114 bs3 (0x15e9e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_82118 D_82118 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_8211c D_8211c.
    an F_82120 D_82120.
    ab_ft F_82124 D_82124 condz.
    ab_tk F_82128 D_82128 condz.
    ld_step F_821f0 D_821f0 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_821f4 D_821f4.
    an F_821f8 D_821f8.
    ab_ft F_821fc D_821fc condz.
    ab_tk F_82200 D_82200 condz.
    av F_822c0 D_822c0 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_822c4 D_822c4 condz.
    an F_822c8 D_822c8.
    an F_822cc D_822cc. rewrite Hsum.
    ab_ft F_822d0 D_822d0 condz.
    an F_822d4 D_822d4.
    ld_step F_822d8 D_822d8 bs1 (0x15e9e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_822dc D_822dc.
    ld_step F_822e0 D_822e0 bs2 (0x15e9f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_822e4 D_822e4 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_822e8 D_822e8 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_822ec D_822ec.
    ab_tk F_822f0 D_822f0 condz.
    an F_822f8 D_822f8.
    ld_step F_822fc D_822fc bs3 (0x15e9e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_82300 D_82300 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_82304 D_82304.
    an F_82308 D_82308.
    ab_ft F_8230c D_8230c condz.
    ab_ft F_82310 D_82310 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
