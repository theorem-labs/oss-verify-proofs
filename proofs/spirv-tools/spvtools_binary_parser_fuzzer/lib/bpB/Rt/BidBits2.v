(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BZBridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BidBits.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BidBits2 () := "K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission3bpB2Rt>BothAllocModel8class_idK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BidBits=forall_rangeZI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BidBits>class_id_rangeC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BidBitsBforall_rangeZ_specC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BidBits2>class_id_chk30I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205".
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma class_id_chk30 : forall_rangeZ (fun s => class_id s <=? 30) 1 65536 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BidBits2 ()) [] "h01sp;2p;1p;3g0000j28Tg000Jj17Tg001Mj12Tg0022j11Tg002Wj13Tg0035j26Tg003Rj34Tg004Sj35Tf0R0#1#1p=0g004mR1g005MR2'8g005m%70g006KR0#2#2#2#1#3'6W0%30%00#0#0#0#0#0#0#0#334=512do"). Qed.
Lemma class_id_le30 : forall size, 1 <= size <= 65536 -> 1 <= class_id size <= 30.
Proof.
ltac2:(KReplay.run1 (kr_t_BidBits2 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51Ch61Hh71mh81nh91Ah:2Hsh;2_Hh<1sh=4sizep;1p;2p;3p;4p;7p;8g002Wj1:Tg0070j20Tg0022j14Tg007LR0j25Tg007gj2STg000Jj11Tg008ij27Tg001Mj1<Tg0035j2=Tg009Ej1CTg009ej1ATg00:Ej1@Tg00:cj1UTg00;Aj1TTg00;lj28Tg00<Oj2RTg0000j2KTg00=1j2JTg00=]j3HTg00><j4GTg00>nj2FTg00?Lj2ETg00?oj1ITg00@Qj3DTg00A4j4?Tg00A_j2BTg00B<j7LTg00CBj2MTg00Cbj7NTg004Sj3OTg00DFj7PTg00Djj8QTf0R1#4#4p=2g005mR2f1R3g00ENP1C?p=9P3g00F5R4g00FTR5P5g00G4R6P1g00GTFNp=3g004mR7g005MR87O1p=6f2R9P4P5P5P6P3P1FPp=;f3R:P4P5P5P6P9P3P1GQp=>g006KR4#:R;/01%44#2#2R<#4#2#2#2#2#2#:R=,01'5R>1S31%13R?,0;%:<R<,7?'5P0%19R?,0;17?<%1:R?,0;%<4#<#<#4#:R@,0?'5P1f4#1,0;f5R?#1/7<%11/=@X<2R<P;P=f6RAg00H4g00I7RB#CRC%ABRB%@2%U2RD%T2REg00IcRF,82182=RG'9'31RE6R6P1P91K781J19#6dAH2F3CGR8b2b3b410F=P1b1PCPB1F23RFPDPE182;R71E24R4'9,3ERH194G,3E5;E%I5R5P2P4g00JAAD27GC?,3E9;EHC>P6P8b2b3b4X0210;3R71B;=,73'5\>^02P1f7PAO2b1FLP<PAO1#6P01=31#61093[R010311=93#6RA[10:9\A1M31P3n2001000000120000000X72X82P0^72^82P1f8#1R0P@P3O3100@PCPBPFPDPE182@,94,3ER4P5PEPHP5A;EH4C>C>P6P8b2b3b4X02101@10;9109@'5\7[^02P1f:#1P3P?O3b1b5b6b5W;W9P3P1O2n2001000000121000000b6W:X=2o"). Qed.
