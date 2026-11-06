(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib As0Tables ArtMem ArtRegs ArtAtomics ArtTac JbtClassId.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtClassId2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtClassId."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtClassId2.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "3bvmap"; "0M"; "4msteps"; "5art_cid_w"; "6art_cid2_kept"; "7getr"; "7mkst"; "8loaded_segments"; "0fx"; "0r"; "0regs"]; ["0regs'"; "0rom"; "0s"; "9BV"; "9bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
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
Local Abbreviation SEC_T_art_classid2_hi_run := (ltac2:(TCodec.tc2 tcn__JbtClassId2 "R0&5y5'DyR0%211%5241'0y8%611%311p061'3&:r4(C+C(1%33@21%6251r1%93@21'4'2'7&<&;v=r6+ZYS8%?3J1=/01Jr5%756521C+ZYZ4%D3O1B/01O%;5:A15G%>3=51+;%I3Q61G%L2E1&8r3%211%Q13Q841%Q;1Q<&9%11Lr2%Q5271r8%Q7213%Q93Q@31p061pN91%Q12;1%Q22C1qQ2QD1%Q52QE1p0Q71pQ6QH1pQ4QC1p>QD1pQ0QJ1")) (only parsing).
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
stepn (ltac:(oF' 0x52468%Z)) (ltac:(oD' 0x52468%Z)). rwH. rewrite <- E1.
stepn (ltac:(oF' 0x5246c%Z)) (ltac:(oD' 0x5246c%Z)).
stepn (ltac:(oF' 0x52470%Z)) (ltac:(oD' 0x52470%Z)).
stepn (ltac:(oF' 0x52474%Z)) (ltac:(oD' 0x52474%Z)).
stepn (ltac:(oF' 0x52478%Z)) (ltac:(oD' 0x52478%Z)).
stepn (ltac:(oF' 0x5247c%Z)) (ltac:(oD' 0x5247c%Z)). rwH. rewrite <- E2.
stepn (ltac:(oF' 0x52480%Z)) (ltac:(oD' 0x52480%Z)).
stepn (ltac:(oF' 0x52484%Z)) (ltac:(oD' 0x52484%Z)).
stepn (ltac:(oF' 0x52488%Z)) (ltac:(oD' 0x52488%Z)).
stepn (ltac:(oF' 0x5248c%Z)) (ltac:(oD' 0x5248c%Z)).
stepn (ltac:(oF' 0x52490%Z)) (ltac:(oD' 0x52490%Z)). rwH. rewrite <- E3.
stepn (ltac:(oF' 0x52494%Z)) (ltac:(oD' 0x52494%Z)). rwH. rewrite <- E4.
stepn (ltac:(oF' 0x52498%Z)) (ltac:(oD' 0x52498%Z)).
stepn (ltac:(oF' 0x5249c%Z)) (ltac:(oD' 0x5249c%Z)).
stepn (ltac:(oF' 0x524a0%Z)) (ltac:(oD' 0x524a0%Z)).
stepn (ltac:(oF' 0x524a4%Z)) (ltac:(oD' 0x524a4%Z)).
stepn (ltac:(oF' 0x524a8%Z)) (ltac:(oD' 0x524a8%Z)).
stepn (ltac:(oF' 0x524ac%Z)) (ltac:(oD' 0x524ac%Z)).
stepn (ltac:(oF' 0x524b0%Z)) (ltac:(oD' 0x524b0%Z)).
stepn (ltac:(oF' 0x524b4%Z)) (ltac:(oD' 0x524b4%Z)).
stepn (ltac:(oF' 0x524b8%Z)) (ltac:(oD' 0x524b8%Z)). rwH. rewrite <- E5.
stepn (ltac:(oF' 0x524bc%Z)) (ltac:(oD' 0x524bc%Z)). rwH. rewrite <- E6.
stepn (ltac:(oF' 0x524c0%Z)) (ltac:(oD' 0x524c0%Z)). rwH. rewrite <- E7.
stepn (ltac:(oF' 0x524c4%Z)) (ltac:(oD' 0x524c4%Z)). rwH. rewrite <- E8.
stepn (ltac:(oF' 0x524c8%Z)) (ltac:(oD' 0x524c8%Z)). rwH. rewrite <- E9.
stepn (ltac:(oF' 0x524cc%Z)) (ltac:(oD' 0x524cc%Z)). rwH. rewrite <- E10.
stepn (ltac:(oF' 0x524d0%Z)) (ltac:(oD' 0x524d0%Z)). rwH. rewrite <- E11.
stepn (ltac:(oF' 0x524d4%Z)) (ltac:(oD' 0x524d4%Z)). rwH. rewrite <- E12.
stepn (ltac:(oF' 0x524d8%Z)) (ltac:(oD' 0x524d8%Z)). rwH. rewrite <- E13.
stepn (ltac:(oF' 0x524dc%Z)) (ltac:(oD' 0x524dc%Z)). rwH. rewrite <- E14.
stepn (ltac:(oF' 0x524e0%Z)) (ltac:(oD' 0x524e0%Z)). rwH. rewrite <- E15.
stepn (ltac:(oF' 0x524e4%Z)) (ltac:(oD' 0x524e4%Z)). rwH. rewrite <- E16.
stepn (ltac:(oF' 0x524e8%Z)) (ltac:(oD' 0x524e8%Z)). rwH. rewrite <- E17.
stepn (ltac:(oF' 0x524ec%Z)) (ltac:(oD' 0x524ec%Z)). rwH. rewrite <- E18.
stepn (ltac:(oF' 0x524f0%Z)) (ltac:(oD' 0x524f0%Z)). rwH. rewrite <- E19.
stepn (ltac:(oF' 0x524f4%Z)) (ltac:(oD' 0x524f4%Z)). rwH. rewrite <- E20.
stepn (ltac:(oF' 0x524f8%Z)) (ltac:(oD' 0x524f8%Z)). rwH. rewrite <- E21.
stepn (ltac:(oF' 0x524fc%Z)) (ltac:(oD' 0x524fc%Z)). rwH. rewrite <- E22.
stepn (ltac:(oF' 0x52500%Z)) (ltac:(oD' 0x52500%Z)).
stepn (ltac:(oF' 0x52504%Z)) (ltac:(oD' 0x52504%Z)). rwH. rewrite <- E23.
stepn (ltac:(oF' 0x52508%Z)) (ltac:(oD' 0x52508%Z)).
stepn (ltac:(oF' 0x5250c%Z)) (ltac:(oD' 0x5250c%Z)). rwH. rewrite <- E24.
stepn (ltac:(oF' 0x52510%Z)) (ltac:(oD' 0x52510%Z)). rwH. rewrite <- E25.
stepn (ltac:(oF' 0x52514%Z)) (ltac:(oD' 0x52514%Z)). rwH. rewrite <- E26.
stepn (ltac:(oF' 0x52518%Z)) (ltac:(oD' 0x52518%Z)). rwH. rewrite <- E27.
stepn (ltac:(oF' 0x5251c%Z)) (ltac:(oD' 0x5251c%Z)). rwH. rewrite <- E28.
stepn (ltac:(oF' 0x52520%Z)) (ltac:(oD' 0x52520%Z)). rwH. rewrite <- E29.
stepn (ltac:(oF' 0x52524%Z)) (ltac:(oD' 0x52524%Z)). rwH. rewrite <- E30.
stepn (ltac:(oF' 0x52528%Z)) (ltac:(oD' 0x52528%Z)). rwH. rewrite <- E31.
stepn (ltac:(oF' 0x5252c%Z)) (ltac:(oD' 0x5252c%Z)). rwH. rewrite <- E32.
stepn (ltac:(oF' 0x52530%Z)) (ltac:(oD' 0x52530%Z)). rwH. rewrite <- E33.
stepn (ltac:(oF' 0x52534%Z)) (ltac:(oD' 0x52534%Z)). rwH. rewrite <- E34.
stepn (ltac:(oF' 0x52538%Z)) (ltac:(oD' 0x52538%Z)). rwH. rewrite <- E35.
stepn (ltac:(oF' 0x5253c%Z)) (ltac:(oD' 0x5253c%Z)). rwH. rewrite <- E36.
stepn (ltac:(oF' 0x52540%Z)) (ltac:(oD' 0x52540%Z)). rwH. rewrite <- E37.
apply mst_refl.
- gres. subst. reflexivity.
- intros r (N1 & N2 & N3 & N4 & N5 & N6). kept_solve.
Qed.
End SE.
End FPX.
