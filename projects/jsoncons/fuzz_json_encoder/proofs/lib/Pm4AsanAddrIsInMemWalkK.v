(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SumsLib Pm4_code_83000_84000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
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

Theorem asan_addrisinmem : addrisinmem_spec Asan.M.loaded_segments 0x8313c 0x160c20 0x160c28 0x160c30 0x16abe8 0x16abf0 0x16abe0.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x8313c) with (0x8313c : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x8313c + 556)) with (0x83368 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn Asan.M.loaded_segments mem (0x16abe8 : word) 8 = Some bs4) by (replace (0x16abe8 : word) with (Z_to_bv 64 0x16abe8) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn Asan.M.loaded_segments mem (0x16abf0 : word) 8 = Some bs5) by (replace (0x16abf0 : word) with (Z_to_bv 64 0x16abf0) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn Asan.M.loaded_segments mem (0x16abe0 : word) 8 = Some bs6) by (replace (0x16abe0 : word) with (Z_to_bv 64 0x16abe0) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  - (* [comment removed for export] *)
    eexists. split.
    ab_tk F_830ec D_830ec condz.
    av F_832c4 D_832c4 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_832c8 D_832c8 condz.
    an F_832cc D_832cc.
    an F_832d0 D_832d0. rewrite Hsum.
    ab_tk F_832d4 D_832d4 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  - (* [comment removed for export] *)
    eexists. split.
    ab_ft F_830ec D_830ec condz.
    an F_830f0 D_830f0.
    ld_step F_830f4 D_830f4 bs1 (0x16abe8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_830f8 D_830f8.
    ld_step F_830fc D_830fc bs2 (0x16abf0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_83100 D_83100 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_83104 D_83104 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_83108 D_83108.
    ab_tk F_8310c D_8310c condz.
    an F_83114 D_83114.
    ld_step F_83118 D_83118 bs3 (0x16abe0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_8311c D_8311c bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_83120 D_83120.
    an F_83124 D_83124.
    ab_ft F_83128 D_83128 condz.
    ab_tk F_8312c D_8312c condz.
    ld_step F_831f4 D_831f4 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_831f8 D_831f8.
    an F_831fc D_831fc.
    ab_ft F_83200 D_83200 condz.
    ab_tk F_83204 D_83204 condz.
    av F_832c4 D_832c4 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_832c8 D_832c8 condz.
    an F_832cc D_832cc.
    an F_832d0 D_832d0. rewrite Hsum.
    ab_ft F_832d4 D_832d4 condz.
    an F_832d8 D_832d8.
    ld_step F_832dc D_832dc bs1 (0x16abe8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_832e0 D_832e0.
    ld_step F_832e4 D_832e4 bs2 (0x16abf0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_832e8 D_832e8 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_832ec D_832ec bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_832f0 D_832f0.
    ab_tk F_832f4 D_832f4 condz.
    an F_832fc D_832fc.
    ld_step F_83300 D_83300 bs3 (0x16abe0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_83304 D_83304 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_83308 D_83308.
    an F_8330c D_8330c.
    ab_ft F_83310 D_83310 condz.
    ab_ft F_83314 D_83314 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
