(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0Readers () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0Readers.FPX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "stdpp.bitvector.definitions."], [["1Some"; "1cons"; "1list"; "1nil"; "1option"; "2I"; "2and"; "2eq"; "2ex"; "3word_to_le_bytes"; "4bvmap"; "0M"; "5msteps"; "6ret_ok"; "7only_a0"; "8getr"]; ["8mkst"; "8rdn"; "9loaded_segments"; "0fx"; "0regs"; "0regs'"; "0ret"; "0rom"; ":BV"; ":Z_to_bv"; ":bv"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section FPX. Context {fx : PropExec.FPState}.
Definition only_a0 (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> getr regs' r = getr regs r.
#[local] Ltac post_only_a0 :=
intros r Hr; gres; try reflexivity;
repeat (rewrite getr_other by (exact Hr || (symmetry; exact Hr) || reg_neq_tac)); reflexivity.
Lemma asan_inited_run : ltac2:(TCodec.tc2 tcn__Jb0Readers "R<&:y5'JyR0%211%5241'4y8%611%311p061'7&?r4(H+1(5%33@21%6251r1%93@21&=r2%211'2%11A%D11&A&Br5+QWehH%A3L1?/01Lu1%746521(0(1&I%12OG(3%11Q0%53Q131%72A1%Q03A91'8'6'<&@vCr8+_nj<%Q53Q@1Q3/01Q@r7r6%8576321%958Q5K32%;3M21+:%Q=3QJ1Q;%Q@2Q91%H2QJQ>%QC3QJ21&>%12?Q=%D231%E291qQ<QN1%H2QO1p0J1p0Q?1p0QC1pQ>R41pQ@QO1pHR01pQ:R61").
Proof.
intros regs M rom ret H1 Hret HM.
eexists. split.
- stepn (ltac:(oF' 0x7fb4c%Z)) (ltac:(oD' 0x7fb4c%Z)).
mlb (ltac:(oF' 0x7fb50%Z)) (ltac:(oD' 0x7fb50%Z)) (0x13d718 : word) HM.
stepfence (ltac:(oF' 0x7fb54%Z)) (ltac:(oD' 0x7fb54%Z)).
stepn (ltac:(oF' 0x7fb58%Z)) (ltac:(oD' 0x7fb58%Z)).
stepn (ltac:(oF' 0x7fb5c%Z)) (ltac:(oD' 0x7fb5c%Z)).
stepret (ltac:(oF' 0x7fb60%Z)) (ltac:(oD' 0x7fb60%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.
Lemma get_malloc_context_size_run : ltac2:(TCodec.tc2 tcn__Jb0Readers "R:&:y5'JyR0%211%5241'4y8%611%311p061'7&?r4(H+1(5%33@21%6251r1%93@21&=r2%211'2%11A%D11&A&Br5+QWeiL%A3L1?/01Lu4%746521(0&9&I+N%22Q41%4271%62@1%O3@81'8'6'<&@vCr8+`Uo4%Q43Q?1Q2/01Q?r7r6%8576321%958Q4J32%;3L21+:%Q<3QI1Q:%Q?2Q81%QA3QH1E&>%12>Q;%C231%D281qQ<QL1%G2QM1p0I1p0Q=1p0QA1pQ>R21pQ@QM1pHQN1pQ:R41").
Proof.
intros regs M rom ret H1 Hret HM.
eexists. split.
- stepn (ltac:(oF' 0x817e4%Z)) (ltac:(oD' 0x817e4%Z)).
mlw (ltac:(oF' 0x817e8%Z)) (ltac:(oD' 0x817e8%Z)) (0x13d73c : word) HM.
stepfence (ltac:(oF' 0x817ec%Z)) (ltac:(oD' 0x817ec%Z)).
stepret (ltac:(oF' 0x817f0%Z)) (ltac:(oD' 0x817f0%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.
Lemma rss_limit_exceeded_run : ltac2:(TCodec.tc2 tcn__Jb0Readers "R=&:y5'JyR0%211%5241'4y8%611%311p061'7&?r4(H+1(5%33@21%6251r1%93@21&=r2%211'2%11A%D11&A&Br5+QgkU2%A3L1?/01Lu1%746521(0(1&Iz%22Q01(3%11Q1%63Q231%82B1%Q13B:1'8'6'<&@vCr8+`fPD%Q63QA1Q4/01QAr7r6%8576321%958Q6L32%;3N21+:%Q>3QK1Q<%QA2Q:1%I2QKH%QD3QK21&>%12?Q>%D231%E291qQ<QO1%H2R01p0J1p0Q@1p0QD1pQ>R51pQ@R01pHR11pQ:R71").
Proof.
intros regs M rom ret H1 Hret HM.
eexists. split.
- stepn (ltac:(oF' 0x85814%Z)) (ltac:(oD' 0x85814%Z)).
mlb (ltac:(oF' 0x85818%Z)) (ltac:(oD' 0x85818%Z)) (0x1beca2 : word) HM.
stepn (ltac:(oF' 0x8581c%Z)) (ltac:(oD' 0x8581c%Z)).
stepret (ltac:(oF' 0x85820%Z)) (ltac:(oD' 0x85820%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.
Lemma allocator_may_return_null_run : ltac2:(TCodec.tc2 tcn__Jb0Readers "R<&:y5'JyR0%211%5241'4y8%611%311p061'7&?r4(H+1(5%33@21%6251r1%93@21&=r2%211'2%11A%D11&A&Br5+QgkU1%A3L1?/01Lu1%746521(0(1&I%12OG(3%11Q0%53Q131%72A1%Q03A91'8'6'<&@vCr8+`eo<%Q53Q@1Q3/01Q@r7r6%8576321%958Q5K32%;3M21+:%Q=3QJ1Q;%Q@2Q91%H2QJQ>%QC3QJ21&>%12?Q=%D231%E291qQ<QN1%H2QO1p0J1p0Q?1p0QC1pQ>R41pQ@QO1pHR01pQ:R61").
Proof.
intros regs M rom ret H1 Hret HM.
eexists. split.
- stepn (ltac:(oF' 0x857ec%Z)) (ltac:(oD' 0x857ec%Z)).
mlb (ltac:(oF' 0x857f0%Z)) (ltac:(oD' 0x857f0%Z)) (0x1beca1 : word) HM.
stepn (ltac:(oF' 0x857f4%Z)) (ltac:(oD' 0x857f4%Z)).
stepret (ltac:(oF' 0x857f8%Z)) (ltac:(oD' 0x857f8%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.
Lemma can_poison_memory_run : ltac2:(TCodec.tc2 tcn__Jb0Readers "R<&:y5'JyR0%211%5241'4y8%611%311p061'7&?r4(H+1(5%33@21%6251r1%93@21&=r2%211'2%11A%D11&A&Br5+QW`dL%A3L1?/01Lu1%746521(0(1&I%12OG(3%11Q0%53Q131%72A1%Q03A91'8'6'<&@vCr8+_YTL%Q53Q@1Q3/01Q@r7r6%8576321%958Q5K32%;3M21+:%Q=3QJ1Q;%Q@2Q91%H2QJQ>%QC3QJ21&>%12?Q=%D231%E291qQ<QN1%H2QO1p0J1p0Q?1p0QC1pQ>R41pQ@QO1pHR01pQ:R61").
Proof.
intros regs M rom ret H1 Hret HM.
eexists. split.
- stepn (ltac:(oF' 0x7a49c%Z)) (ltac:(oD' 0x7a49c%Z)).
mlb (ltac:(oF' 0x7a4a0%Z)) (ltac:(oD' 0x7a4a0%Z)) (0x13c29c : word) HM.
stepfence (ltac:(oF' 0x7a4a4%Z)) (ltac:(oD' 0x7a4a4%Z)).
stepn (ltac:(oF' 0x7a4a8%Z)) (ltac:(oD' 0x7a4a8%Z)).
stepret (ltac:(oF' 0x7a4ac%Z)) (ltac:(oD' 0x7a4ac%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; vm_compute; reflexivity | post_only_a0].
Qed.
End FPX.
