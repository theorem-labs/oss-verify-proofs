(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables ArtMem ArtRegs ArtAtomics ArtTac JatClassId.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatClassId2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClassId."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatClassId2.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3bvmap"; "0M"; "4msteps"; "5art_cid_w"; "6art_cid2_kept"; "7getr"; "7mkst"; "8loaded_segments"; "0fx"; "0r"; "0regs"]; ["0regs'"; "0rom"; "0s"; "9BV"; "9bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Ltac art_step F D :=
stepn F D;
try (lazymatch goal with
| |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ =>
lazymatch v with
| Z_to_bv 64 ?z => is_Z_lit z
| _ => let x := fresh "x" in remember v as x
end
end).
Section FPX. Context {fx : PropExec.FPState}.
Definition art_cid2_kept (r : reg) : Prop :=
r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Section SE.
Local Abbreviation SEC_T_art_classid2_hi_run := (ltac2:(TCodec.tc2 tcn__JatClassId2 "R0&5y5'DyR0%211%5241'0y8%611%311p061'3&:r4(C+C(1%33@21%6251r1%93@21'4'2'7&<&;v=r6+ZX\H%?3J1=/01Jr5%756521C+ZXcD%D3O1B/01O%;5:A15G%>3=51+;%I3Q61G%L2E1&8r3%211%Q13Q841%Q;1Q<&9%11Lr2%Q5271r8%Q7213%Q93Q@31p061pN91%Q12;1%Q22C1qQ2QD1%Q52QE1p0Q71pQ6QH1pQ4QC1p>QD1pQ0QJ1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_art_classid2_hi_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_classid2_hi_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_classid2_hi_run) 2%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_classid2_hi_run) 3%nat 0%nat).
Lemma art_classid2_hi_run : ltac:(sec_stmt2 constr:(SEC_T_art_classid2_hi_run) 4%nat 0%nat).
Proof using Type regs M rom s.
intros H19.
pose (x1 := (v_srli s (1)%Z)). assert (E1 : x1 = (v_srli s (1)%Z)) by reflexivity. clearbody x1.
pose (x2 := (v_or s x1)). assert (E2 : x2 = (v_or s x1)) by reflexivity. clearbody x2.
pose (x3 := (v_srli x2 (2)%Z)). assert (E3 : x3 = (v_srli x2 (2)%Z)) by reflexivity. clearbody x3.
pose (x4 := (v_or x2 x3)). assert (E4 : x4 = (v_or x2 x3)) by reflexivity. clearbody x4.
pose (x5 := (v_srli x4 (4)%Z)). assert (E5 : x5 = (v_srli x4 (4)%Z)) by reflexivity. clearbody x5.
pose (x6 := (v_or x4 x5)). assert (E6 : x6 = (v_or x4 x5)) by reflexivity. clearbody x6.
pose (x7 := (v_srli x6 (8)%Z)). assert (E7 : x7 = (v_srli x6 (8)%Z)) by reflexivity. clearbody x7.
pose (x8 := (v_or x6 x7)). assert (E8 : x8 = (v_or x6 x7)) by reflexivity. clearbody x8.
pose (x9 := (v_srli x8 (16)%Z)). assert (E9 : x9 = (v_srli x8 (16)%Z)) by reflexivity. clearbody x9.
pose (x10 := (v_or x8 x9)). assert (E10 : x10 = (v_or x8 x9)) by reflexivity. clearbody x10.
pose (x11 := (v_srli x10 (32)%Z)). assert (E11 : x11 = (v_srli x10 (32)%Z)) by reflexivity. clearbody x11.
pose (x12 := (v_or x10 x11)). assert (E12 : x12 = (v_or x10 x11)) by reflexivity. clearbody x12.
pose (x13 := (v_xori x12 (-1)%Z)). assert (E13 : x13 = (v_xori x12 (-1)%Z)) by reflexivity. clearbody x13.
pose (x14 := (v_srli x13 (1)%Z)). assert (E14 : x14 = (v_srli x13 (1)%Z)) by reflexivity. clearbody x14.
pose (x15 := (v_and x14 (Z_to_bv 64 6148914691236517205))). assert (E15 : x15 = (v_and x14 (Z_to_bv 64 6148914691236517205))) by reflexivity. clearbody x15.
pose (x16 := (v_sub x13 x15)). assert (E16 : x16 = (v_sub x13 x15)) by reflexivity. clearbody x16.
pose (x17 := (v_and x16 (Z_to_bv 64 3689348814741910323))). assert (E17 : x17 = (v_and x16 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x17.
pose (x18 := (v_srli x16 (2)%Z)). assert (E18 : x18 = (v_srli x16 (2)%Z)) by reflexivity. clearbody x18.
pose (x19 := (v_and x18 (Z_to_bv 64 3689348814741910323))). assert (E19 : x19 = (v_and x18 (Z_to_bv 64 3689348814741910323))) by reflexivity. clearbody x19.
pose (x20 := (v_add x17 x19)). assert (E20 : x20 = (v_add x17 x19)) by reflexivity. clearbody x20.
pose (x21 := (v_srli x20 (4)%Z)). assert (E21 : x21 = (v_srli x20 (4)%Z)) by reflexivity. clearbody x21.
pose (x22 := (v_add x20 x21)). assert (E22 : x22 = (v_add x20 x21)) by reflexivity. clearbody x22.
pose (x23 := (v_and x22 (Z_to_bv 64 1085102592571150095))). assert (E23 : x23 = (v_and x22 (Z_to_bv 64 1085102592571150095))) by reflexivity. clearbody x23.
pose (x24 := (v_mul x23 (Z_to_bv 64 72340172838076673))). assert (E24 : x24 = (v_mul x23 (Z_to_bv 64 72340172838076673))) by reflexivity. clearbody x24.
pose (x25 := (v_srli x24 (56)%Z)). assert (E25 : x25 = (v_srli x24 (56)%Z)) by reflexivity. clearbody x25.
pose (x26 := (v_subw (Z_to_bv 64 62) x25)). assert (E26 : x26 = (v_subw (Z_to_bv 64 62) x25)) by reflexivity. clearbody x26.
pose (x27 := (v_slli x25 (1)%Z)). assert (E27 : x27 = (v_slli x25 (1)%Z)) by reflexivity. clearbody x27.
pose (x28 := (v_srl s x26)). assert (E28 : x28 = (v_srl s x26)) by reflexivity. clearbody x28.
pose (x29 := (v_sllw (Z_to_bv 64 18446744073709551615) x26)). assert (E29 : x29 = (v_sllw (Z_to_bv 64 18446744073709551615) x26)) by reflexivity. clearbody x29.
pose (x30 := (v_xori x27 (126)%Z)). assert (E30 : x30 = (v_xori x27 (126)%Z)) by reflexivity. clearbody x30.
pose (x31 := (v_andi x28 (1)%Z)). assert (E31 : x31 = (v_andi x28 (1)%Z)) by reflexivity. clearbody x31.
pose (x32 := (v_xori x29 (-1)%Z)). assert (E32 : x32 = (v_xori x29 (-1)%Z)) by reflexivity. clearbody x32.
pose (x33 := (v_and s x32)). assert (E33 : x33 = (v_and s x32)) by reflexivity. clearbody x33.
pose (x34 := (v_or x30 x31)). assert (E34 : x34 = (v_or x30 x31)) by reflexivity. clearbody x34.
pose (x35 := (v_sltu (Z_to_bv 64 0) x33)). assert (E35 : x35 = (v_sltu (Z_to_bv 64 0) x33)) by reflexivity. clearbody x35.
pose (x36 := (v_add x34 x35)). assert (E36 : x36 = (v_add x34 x35)) by reflexivity. clearbody x36.
pose (x37 := (v_addi x36 (-2)%Z)). assert (E37 : x37 = (v_addi x36 (-2)%Z)) by reflexivity. clearbody x37.
eexists. split; [|split].
- rwH.
stepn (ltac:(oF' 0x52198%Z)) (ltac:(oD' 0x52198%Z)). rwH. rewrite <- E1.
stepn (ltac:(oF' 0x5219c%Z)) (ltac:(oD' 0x5219c%Z)).
stepn (ltac:(oF' 0x521a0%Z)) (ltac:(oD' 0x521a0%Z)).
stepn (ltac:(oF' 0x521a4%Z)) (ltac:(oD' 0x521a4%Z)).
stepn (ltac:(oF' 0x521a8%Z)) (ltac:(oD' 0x521a8%Z)).
stepn (ltac:(oF' 0x521ac%Z)) (ltac:(oD' 0x521ac%Z)). rwH. rewrite <- E2.
stepn (ltac:(oF' 0x521b0%Z)) (ltac:(oD' 0x521b0%Z)).
stepn (ltac:(oF' 0x521b4%Z)) (ltac:(oD' 0x521b4%Z)).
stepn (ltac:(oF' 0x521b8%Z)) (ltac:(oD' 0x521b8%Z)).
stepn (ltac:(oF' 0x521bc%Z)) (ltac:(oD' 0x521bc%Z)).
stepn (ltac:(oF' 0x521c0%Z)) (ltac:(oD' 0x521c0%Z)). rwH. rewrite <- E3.
stepn (ltac:(oF' 0x521c4%Z)) (ltac:(oD' 0x521c4%Z)). rwH. rewrite <- E4.
stepn (ltac:(oF' 0x521c8%Z)) (ltac:(oD' 0x521c8%Z)).
stepn (ltac:(oF' 0x521cc%Z)) (ltac:(oD' 0x521cc%Z)).
stepn (ltac:(oF' 0x521d0%Z)) (ltac:(oD' 0x521d0%Z)).
stepn (ltac:(oF' 0x521d4%Z)) (ltac:(oD' 0x521d4%Z)).
stepn (ltac:(oF' 0x521d8%Z)) (ltac:(oD' 0x521d8%Z)).
stepn (ltac:(oF' 0x521dc%Z)) (ltac:(oD' 0x521dc%Z)).
stepn (ltac:(oF' 0x521e0%Z)) (ltac:(oD' 0x521e0%Z)).
stepn (ltac:(oF' 0x521e4%Z)) (ltac:(oD' 0x521e4%Z)).
stepn (ltac:(oF' 0x521e8%Z)) (ltac:(oD' 0x521e8%Z)). rwH. rewrite <- E5.
stepn (ltac:(oF' 0x521ec%Z)) (ltac:(oD' 0x521ec%Z)). rwH. rewrite <- E6.
stepn (ltac:(oF' 0x521f0%Z)) (ltac:(oD' 0x521f0%Z)). rwH. rewrite <- E7.
stepn (ltac:(oF' 0x521f4%Z)) (ltac:(oD' 0x521f4%Z)). rwH. rewrite <- E8.
stepn (ltac:(oF' 0x521f8%Z)) (ltac:(oD' 0x521f8%Z)). rwH. rewrite <- E9.
stepn (ltac:(oF' 0x521fc%Z)) (ltac:(oD' 0x521fc%Z)). rwH. rewrite <- E10.
stepn (ltac:(oF' 0x52200%Z)) (ltac:(oD' 0x52200%Z)). rwH. rewrite <- E11.
stepn (ltac:(oF' 0x52204%Z)) (ltac:(oD' 0x52204%Z)). rwH. rewrite <- E12.
stepn (ltac:(oF' 0x52208%Z)) (ltac:(oD' 0x52208%Z)). rwH. rewrite <- E13.
stepn (ltac:(oF' 0x5220c%Z)) (ltac:(oD' 0x5220c%Z)). rwH. rewrite <- E14.
stepn (ltac:(oF' 0x52210%Z)) (ltac:(oD' 0x52210%Z)). rwH. rewrite <- E15.
stepn (ltac:(oF' 0x52214%Z)) (ltac:(oD' 0x52214%Z)). rwH. rewrite <- E16.
stepn (ltac:(oF' 0x52218%Z)) (ltac:(oD' 0x52218%Z)). rwH. rewrite <- E17.
stepn (ltac:(oF' 0x5221c%Z)) (ltac:(oD' 0x5221c%Z)). rwH. rewrite <- E18.
stepn (ltac:(oF' 0x52220%Z)) (ltac:(oD' 0x52220%Z)). rwH. rewrite <- E19.
stepn (ltac:(oF' 0x52224%Z)) (ltac:(oD' 0x52224%Z)). rwH. rewrite <- E20.
stepn (ltac:(oF' 0x52228%Z)) (ltac:(oD' 0x52228%Z)). rwH. rewrite <- E21.
stepn (ltac:(oF' 0x5222c%Z)) (ltac:(oD' 0x5222c%Z)). rwH. rewrite <- E22.
stepn (ltac:(oF' 0x52230%Z)) (ltac:(oD' 0x52230%Z)).
stepn (ltac:(oF' 0x52234%Z)) (ltac:(oD' 0x52234%Z)). rwH. rewrite <- E23.
stepn (ltac:(oF' 0x52238%Z)) (ltac:(oD' 0x52238%Z)).
stepn (ltac:(oF' 0x5223c%Z)) (ltac:(oD' 0x5223c%Z)). rwH. rewrite <- E24.
stepn (ltac:(oF' 0x52240%Z)) (ltac:(oD' 0x52240%Z)). rwH. rewrite <- E25.
stepn (ltac:(oF' 0x52244%Z)) (ltac:(oD' 0x52244%Z)). rwH. rewrite <- E26.
stepn (ltac:(oF' 0x52248%Z)) (ltac:(oD' 0x52248%Z)). rwH. rewrite <- E27.
stepn (ltac:(oF' 0x5224c%Z)) (ltac:(oD' 0x5224c%Z)). rwH. rewrite <- E28.
stepn (ltac:(oF' 0x52250%Z)) (ltac:(oD' 0x52250%Z)). rwH. rewrite <- E29.
stepn (ltac:(oF' 0x52254%Z)) (ltac:(oD' 0x52254%Z)). rwH. rewrite <- E30.
stepn (ltac:(oF' 0x52258%Z)) (ltac:(oD' 0x52258%Z)). rwH. rewrite <- E31.
stepn (ltac:(oF' 0x5225c%Z)) (ltac:(oD' 0x5225c%Z)). rwH. rewrite <- E32.
stepn (ltac:(oF' 0x52260%Z)) (ltac:(oD' 0x52260%Z)). rwH. rewrite <- E33.
stepn (ltac:(oF' 0x52264%Z)) (ltac:(oD' 0x52264%Z)). rwH. rewrite <- E34.
stepn (ltac:(oF' 0x52268%Z)) (ltac:(oD' 0x52268%Z)). rwH. rewrite <- E35.
stepn (ltac:(oF' 0x5226c%Z)) (ltac:(oD' 0x5226c%Z)). rwH. rewrite <- E36.
stepn (ltac:(oF' 0x52270%Z)) (ltac:(oD' 0x52270%Z)). rwH. rewrite <- E37.
apply mst_refl.
- gres. subst. reflexivity.
- intros r (N1 & N2 & N3 & N4 & N5 & N6). kept_solve.
Qed.
End SE.
End FPX.
