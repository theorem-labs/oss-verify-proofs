(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0LibMainRet () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M."; "stdpp.bitvector.definitions."], [["1option"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "3bvmap"; "4msteps"; "5getr"; "5mkst"; "6loaded_segments"; "0fx"; "0mem"; "0r"; "0regs"; "0regs'"]; ["0rom"; "7BV"; "7Z_to_bv"; "7bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Ubsan.M.loaded_segments) pc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Theorem main_ret_0 : ltac2:(TCodec.tc2 tcn__Ju0LibMainRet "RA&6y5'CyR0%211%5241'0y8%611%311p061'3&8r3(A+:(1%33@21%6251&Bz%22B1%;3B41'4'2'7&:&9v;r5+V_l@%A3L1?/01Lr4%756521Er1+V`P@%G3Q21E/01Q2%<5;416J%?3>61+8%L3Q91J%O281%Q13Q81G%Q12:L%Q33Q:1I%Q=1Q>&5+1%Q43QA1Q2%Q834@1%411r2%Q;371<%711%Q=39Q;Q7%911+;%Q=3QJ1Q;%QA3=K1%=11r6%QC21Q2r:%QE21Q4%QG3QN31p061p0;1p0>1p0B1pLH1%Q@2J1%QA2M1%QB2Q21qQ0R61%QE2R71p0QG1pQ2R41pJR51pNR;1").
Proof.
intros regs mem rom Ha0.
destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
-
eexists. split.
+ stepb_tk (ltac:(oF' 0x33f90%Z)) (ltac:(oD' 0x33f90%Z)) ltac:(exact Hc).
stepn (ltac:(oF' 0x33f9c%Z)) (ltac:(oD' 0x33f9c%Z)).
stepn (ltac:(oF' 0x340e4%Z)) (ltac:(oD' 0x340e4%Z)).
stepret (ltac:(oF' 0x340e8%Z)) (ltac:(oD' 0x340e8%Z)) (Z_to_bv 64 0x33fa0) ltac:(reflexivity).
stepn (ltac:(oF' 0x33fa0%Z)) (ltac:(oD' 0x33fa0%Z)).
stepn (ltac:(oF' 0x33fa4%Z)) (ltac:(oD' 0x33fa4%Z)).
stepb_tk (ltac:(oF' 0x33fa8%Z)) (ltac:(oD' 0x33fa8%Z)) ltac:(cond_compute).
apply mst_refl.
+ repeat split; gres; try reflexivity.
intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
-
eexists. split.
+ stepb_ft (ltac:(oF' 0x33f90%Z)) (ltac:(oD' 0x33f90%Z)) ltac:(exact Hc).
stepn (ltac:(oF' 0x33f94%Z)) (ltac:(oD' 0x33f94%Z)).
stepn (ltac:(oF' 0x33f98%Z)) (ltac:(oD' 0x33f98%Z)).
apply mst_refl.
+ repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX_1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
