(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SumsLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import AsanAIM_codeK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
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

Theorem asan_addrisinmem : addrisinmem_spec AsanUbsan.M.loaded_segments 0x7ab90 0x1374c8 0x1374d0 0x1374d8 0x140928 0x140930 0x140920.
Proof.
  unfold addrisinmem_spec.
  intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
  replace (Z_to_bv 64 0x7ab90) with (0x7ab90 : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 (0x7ab90 + 556)) with (0x7adbc : word) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
  replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
  pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
  assert (R4' : rdn AsanUbsan.M.loaded_segments mem (0x140928 : word) 8 = Some bs4) by (replace (0x140928 : word) with (Z_to_bv 64 0x140928) by (apply bv_eq; reflexivity); exact R4).
  assert (R5' : rdn AsanUbsan.M.loaded_segments mem (0x140930 : word) 8 = Some bs5) by (replace (0x140930 : word) with (Z_to_bv 64 0x140930) by (apply bv_eq; reflexivity); exact R5).
  assert (R6' : rdn AsanUbsan.M.loaded_segments mem (0x140920 : word) 8 = Some bs6) by (replace (0x140920 : word) with (Z_to_bv 64 0x140920) by (apply bv_eq; reflexivity); exact R6).
  assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
  { unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
  assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
  { unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
  destruct Hcase as [HL | [HH1 HH2]].
  - (* [comment removed for export] *)
    eexists. split.
    ab_tk F_7a778 D_7a778 condz.
    av F_7a950 D_7a950 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7a954 D_7a954 condz.
    an F_7a958 D_7a958.
    an F_7a95c D_7a95c. rewrite Hsum.
    ab_tk F_7a960 D_7a960 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
  - (* [comment removed for export] *)
    eexists. split.
    ab_ft F_7a778 D_7a778 condz.
    an F_7a77c D_7a77c.
    ld_step F_7a780 D_7a780 bs1 (0x140928 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7a784 D_7a784.
    ld_step F_7a788 D_7a788 bs2 (0x140930 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7a78c D_7a78c bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7a790 D_7a790 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7a794 D_7a794.
    ab_tk F_7a798 D_7a798 condz.
    an F_7a7a0 D_7a7a0.
    ld_step F_7a7a4 D_7a7a4 bs3 (0x140920 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7a7a8 D_7a7a8 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7a7ac D_7a7ac.
    an F_7a7b0 D_7a7b0.
    ab_ft F_7a7b4 D_7a7b4 condz.
    ab_tk F_7a7b8 D_7a7b8 condz.
    ld_step F_7a880 D_7a880 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7a884 D_7a884.
    an F_7a888 D_7a888.
    ab_ft F_7a88c D_7a88c condz.
    ab_tk F_7a890 D_7a890 condz.
    av F_7a950 D_7a950 (Z_to_bv 64 0) ltac:(exact Hand7).
    ab_ft F_7a954 D_7a954 condz.
    an F_7a958 D_7a958.
    an F_7a95c D_7a95c. rewrite Hsum.
    ab_ft F_7a960 D_7a960 condz.
    an F_7a964 D_7a964.
    ld_step F_7a968 D_7a968 bs1 (0x140928 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
    an F_7a96c D_7a96c.
    ld_step F_7a970 D_7a970 bs2 (0x140930 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
    ld_step F_7a974 D_7a974 bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
    ld_step F_7a978 D_7a978 bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
    an F_7a97c D_7a97c.
    ab_tk F_7a980 D_7a980 condz.
    an F_7a988 D_7a988.
    ld_step F_7a98c D_7a98c bs3 (0x140920 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
    ld_step F_7a990 D_7a990 bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
    an F_7a994 D_7a994.
    an F_7a998 D_7a998.
    ab_ft F_7a99c D_7a99c condz.
    ab_ft F_7a9a0 D_7a9a0 condz.
    apply mst_refl.
    split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
