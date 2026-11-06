(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SumsLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
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
Theorem asan_addrisinmem : addrisinmem_spec Asan.M.loaded_segments 0x7a238 0x132640 0x132648 0x132650 0x13b9e8 0x13b9f0 0x13b9e0.
Proof.
unfold addrisinmem_spec.
intros mem rom regs a sz bs1 bs2 bs3 bs4 bs5 bs6 Ha Hsz Hs1 Ha4 R1 V1 R2 V2 R3 V3 R4 V4 R5 V5 R6 V6 Hsz8 Hszal Hcase.
replace (Z_to_bv 64 0x7a238) with (0x7a238 : word) by (apply bv_eq; reflexivity).
replace (Z_to_bv 64 (0x7a238 + 556)) with (0x7a464 : word) by (apply bv_eq; reflexivity).
replace (Z_to_bv 64 0x7fff8000) with (0x7fff8000 : word) in Hs1 by (apply bv_eq; reflexivity).
replace (Z_to_bv 64 0x7fff7fff) with (0x7fff7fff : word) in Ha4 by (apply bv_eq; reflexivity).
pose proof (u64_range a) as Ua. pose proof (u64_range sz) as Usz.
assert (R4' : rdn Asan.M.loaded_segments mem (0x13b9e8 : word) 8 = Some bs4) by (replace (0x13b9e8 : word) with (Z_to_bv 64 0x13b9e8) by (apply bv_eq; reflexivity); exact R4).
assert (R5' : rdn Asan.M.loaded_segments mem (0x13b9f0 : word) 8 = Some bs5) by (replace (0x13b9f0 : word) with (Z_to_bv 64 0x13b9f0) by (apply bv_eq; reflexivity); exact R5).
assert (R6' : rdn Asan.M.loaded_segments mem (0x13b9e0 : word) 8 = Some bs6) by (replace (0x13b9e0 : word) with (Z_to_bv 64 0x13b9e0) by (apply bv_eq; reflexivity); exact R6).
assert (Hand7 : v_andi sz 7 = Z_to_bv 64 0).
{ unfold v_andi. f_equal. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3)%Z with 8%Z. exact Hszal. }
assert (Hsum : v_addi (v_add a sz) (-8) = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)).
{ unfold v_addi, v_add. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia. }
destruct Hcase as [HL | [HH1 HH2]].
-
eexists. split.
ab_tk (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)) condz.
av (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)) (Z_to_bv 64 0) ltac:(exact Hand7).
ab_ft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)) condz.
an (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)).
an (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)). rewrite Hsum.
ab_tk (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)) condz.
apply mst_refl.
split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
-
eexists. split.
ab_ft (ltac:(oF' 0x7a238%Z)) (ltac:(oD' 0x7a238%Z)) condz.
an (ltac:(oF' 0x7a23c%Z)) (ltac:(oD' 0x7a23c%Z)).
ld_step (ltac:(oF' 0x7a240%Z)) (ltac:(oD' 0x7a240%Z)) bs1 (0x13b9e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
an (ltac:(oF' 0x7a244%Z)) (ltac:(oD' 0x7a244%Z)).
ld_step (ltac:(oF' 0x7a248%Z)) (ltac:(oD' 0x7a248%Z)) bs2 (0x13b9f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
ld_step (ltac:(oF' 0x7a24c%Z)) (ltac:(oD' 0x7a24c%Z)) bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
ld_step (ltac:(oF' 0x7a250%Z)) (ltac:(oD' 0x7a250%Z)) bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
an (ltac:(oF' 0x7a254%Z)) (ltac:(oD' 0x7a254%Z)).
ab_tk (ltac:(oF' 0x7a258%Z)) (ltac:(oD' 0x7a258%Z)) condz.
an (ltac:(oF' 0x7a260%Z)) (ltac:(oD' 0x7a260%Z)).
ld_step (ltac:(oF' 0x7a264%Z)) (ltac:(oD' 0x7a264%Z)) bs3 (0x13b9e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
ld_step (ltac:(oF' 0x7a268%Z)) (ltac:(oD' 0x7a268%Z)) bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
an (ltac:(oF' 0x7a26c%Z)) (ltac:(oD' 0x7a26c%Z)).
an (ltac:(oF' 0x7a270%Z)) (ltac:(oD' 0x7a270%Z)).
ab_ft (ltac:(oF' 0x7a274%Z)) (ltac:(oD' 0x7a274%Z)) condz.
ab_tk (ltac:(oF' 0x7a278%Z)) (ltac:(oD' 0x7a278%Z)) condz.
ld_step (ltac:(oF' 0x7a340%Z)) (ltac:(oD' 0x7a340%Z)) bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
an (ltac:(oF' 0x7a344%Z)) (ltac:(oD' 0x7a344%Z)).
an (ltac:(oF' 0x7a348%Z)) (ltac:(oD' 0x7a348%Z)).
ab_ft (ltac:(oF' 0x7a34c%Z)) (ltac:(oD' 0x7a34c%Z)) condz.
ab_tk (ltac:(oF' 0x7a350%Z)) (ltac:(oD' 0x7a350%Z)) condz.
av (ltac:(oF' 0x7a410%Z)) (ltac:(oD' 0x7a410%Z)) (Z_to_bv 64 0) ltac:(exact Hand7).
ab_ft (ltac:(oF' 0x7a414%Z)) (ltac:(oD' 0x7a414%Z)) condz.
an (ltac:(oF' 0x7a418%Z)) (ltac:(oD' 0x7a418%Z)).
an (ltac:(oF' 0x7a41c%Z)) (ltac:(oD' 0x7a41c%Z)). rewrite Hsum.
ab_ft (ltac:(oF' 0x7a420%Z)) (ltac:(oD' 0x7a420%Z)) condz.
an (ltac:(oF' 0x7a424%Z)) (ltac:(oD' 0x7a424%Z)).
ld_step (ltac:(oF' 0x7a428%Z)) (ltac:(oD' 0x7a428%Z)) bs1 (0x13b9e8 : word) ltac:(exact R1) ltac:(rewrite V1; reflexivity).
an (ltac:(oF' 0x7a42c%Z)) (ltac:(oD' 0x7a42c%Z)).
ld_step (ltac:(oF' 0x7a430%Z)) (ltac:(oD' 0x7a430%Z)) bs2 (0x13b9f0 : word) ltac:(exact R2) ltac:(rewrite V2; reflexivity).
ld_step (ltac:(oF' 0x7a434%Z)) (ltac:(oD' 0x7a434%Z)) bs4 (Z_to_bv 64 0) ltac:(first [exact R4 | exact R4']) ltac:(rewrite V4; reflexivity).
ld_step (ltac:(oF' 0x7a438%Z)) (ltac:(oD' 0x7a438%Z)) bs5 (Z_to_bv 64 0) ltac:(first [exact R5 | exact R5']) ltac:(rewrite V5; reflexivity).
an (ltac:(oF' 0x7a43c%Z)) (ltac:(oD' 0x7a43c%Z)).
ab_tk (ltac:(oF' 0x7a440%Z)) (ltac:(oD' 0x7a440%Z)) condz.
an (ltac:(oF' 0x7a448%Z)) (ltac:(oD' 0x7a448%Z)).
ld_step (ltac:(oF' 0x7a44c%Z)) (ltac:(oD' 0x7a44c%Z)) bs3 (0x13b9e0 : word) ltac:(exact R3) ltac:(rewrite V3; reflexivity).
ld_step (ltac:(oF' 0x7a450%Z)) (ltac:(oD' 0x7a450%Z)) bs6 (Z_to_bv 64 (2^47 - 1)) ltac:(first [exact R6 | exact R6']) ltac:(rewrite V6; reflexivity).
an (ltac:(oF' 0x7a454%Z)) (ltac:(oD' 0x7a454%Z)).
an (ltac:(oF' 0x7a458%Z)) (ltac:(oD' 0x7a458%Z)).
ab_ft (ltac:(oF' 0x7a45c%Z)) (ltac:(oD' 0x7a45c%Z)) condz.
ab_ft (ltac:(oF' 0x7a460%Z)) (ltac:(oD' 0x7a460%Z)) condz.
apply mst_refl.
split. { gres. reflexivity. } unfold aim_clob; solve_regs_agree.
Qed.
