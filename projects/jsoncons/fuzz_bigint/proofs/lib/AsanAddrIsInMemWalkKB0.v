(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import SumsLib AsanAIM_codeKB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
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

Theorem asan_addrisinmem : addrisinmem_spec AsanUbsan.M.loaded_segments 0x61250 0xd64d0 0xd64d8 0xd64e0 0xdf428 0xdf430 0xdf420.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x61250) with (0x61250 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x61250 + 556)) with (0x6147c : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn AsanUbsan.M.loaded_segments mem (0xdf428 : word) 8 = Some bs4) by (replace (0xdf428 : word) with (Z_to_bv 64 0xdf428) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn AsanUbsan.M.loaded_segments mem (0xdf430 : word) 8 = Some bs5) by (replace (0xdf430 : word) with (Z_to_bv 64 0xdf430) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn AsanUbsan.M.loaded_segments mem (0xdf420 : word) 8 = Some bs6) by (replace (0xdf420 : word) with (Z_to_bv 64 0xdf420) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  - (* [comment removed for export] *)
    eexists. split.
    ab_tk F_61250 D_61250 condz.
    av F_61428 D_61428 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_6142c D_6142c condz.
    an F_61430 D_61430.
    an F_61434 D_61434. rewrite Hsum.
    ab_tk F_61438 D_61438 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  - (* [comment removed for export] *)
    eexists. split.
    ab_ft F_61250 D_61250 condz.
    an F_61254 D_61254.
    ld_step F_61258 D_61258 bs1 (0xdf428 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_6125c D_6125c.
    ld_step F_61260 D_61260 bs2 (0xdf430 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_61264 D_61264 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_61268 D_61268 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_6126c D_6126c.
    ab_tk F_61270 D_61270 condz.
    an F_61278 D_61278.
    ld_step F_6127c D_6127c bs3 (0xdf420 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_61280 D_61280 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_61284 D_61284.
    an F_61288 D_61288.
    ab_ft F_6128c D_6128c condz.
    ab_tk F_61290 D_61290 condz.
    ld_step F_61358 D_61358 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_6135c D_6135c.
    an F_61360 D_61360.
    ab_ft F_61364 D_61364 condz.
    ab_tk F_61368 D_61368 condz.
    av F_61428 D_61428 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_6142c D_6142c condz.
    an F_61430 D_61430.
    an F_61434 D_61434. rewrite Hsum.
    ab_ft F_61438 D_61438 condz.
    an F_6143c D_6143c.
    ld_step F_61440 D_61440 bs1 (0xdf428 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_61444 D_61444.
    ld_step F_61448 D_61448 bs2 (0xdf430 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_6144c D_6144c bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_61450 D_61450 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_61454 D_61454.
    ab_tk F_61458 D_61458 condz.
    an F_61460 D_61460.
    ld_step F_61464 D_61464 bs3 (0xdf420 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_61468 D_61468 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_6146c D_6146c.
    an F_61470 D_61470.
    ab_ft F_61474 D_61474 condz.
    ab_ft F_61478 D_61478 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
