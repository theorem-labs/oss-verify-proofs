(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_dt_xsrc_T Cut_dt_xsrc_R0 Cut_dt_xsrc_R1 Cut_dt_xsrc_R2.
Definition dict_Cut_dt_xsrc_R3 : CCD.pt := CCD.mk_table 1187%positive "((0 -144)(2 0(1 2)#1)(0 1048574)(5#3 1 4611686018427387904)(0 1048575)(5#5 1 4611686018427387904)(0 1048576)(5#7 1 4611686018427387904)((1 11)0)(0#9 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9344)(0 9344)(6#15#16)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#15#16#9(0 8))((1 32)0)(7#15#16#21(0 24))(7#9(0 8)#21(0 24))(0 9200)(9#15#24)((1 2)-144)(9#26(0 112))((1 2)-8)(0#28 8(1 1))((1 2)-16)(0#30 8(1 8))((1 2)-24)(0#32 8(1 9))((1 2)-32)(9#34(0 8))(#4#6#8#10#11#12#13#14#17#18#19#20#22#23#25#27#29#31#33#35)((1 2)-9344#16)(#37)(0 1048573)(273660 273732 273732 273808 422204 270980 273836 273736 273812 763484 764892)(0#40)(0#41(1 0))(0(4 1)#42)(0#41#43)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(8(1 8))(9(1 9))(10(0 1))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(1 273808)(4 0(0 -1)(1 66))(5#63 1 18446744073709551614)(5(1 66)2 18446744073709551615)(5(1 66)1 18446744073709551615)(2 3(1 66)(0 0))(5#67 1 1)(9#26(0 104))((1 2)-40)(0#70 4(1 34))((1 2)-36)(0#72 4(1 33))(5(1 33)1 21)(#4#6#64#65#66#68#8#10#11#12#13#14#17#18#19#20#22#23#25#69#71#73#29#31#33#35#74))"%pstring.
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R3 224%positive "(273696((1 0)(1 98)#2(1 3)(1 4)(1 99)(1 100)(1 101)(1 11)(1 9)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(1 108)(1 109)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 110)(1 111)(1 112)(1 113))#36 114#38()#39)"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R3 3%positive "()"%pstring.
Definition hints10 : list (nat * CC.subst) := hints6.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R3 233%positive "(#44(((273808(#45#46#47#48(5(1 99))(6(1 100))(7(1 101))#49#50#51(11(1 103))(12(1 104))(13(1 105))(14(1 106))(15(1 107))(16(1 108))(17(1 109))#52#53#54#55#56#57#58#59#60#61(28(1 110))(29(1 111))(30(1 112))(31(1 113)))()#36)#62))()())"%pstring.
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R3 210%positive "(273784((1 0)(1 83)#2(1 3)(1 4)(1 84)(1 85)(1 86)(1 11)(1 10)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 94)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 95)(1 96)(1 97)(1 98))#75 99#38()#39)"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R3 3%positive "()"%pstring.
Definition hints11 : list (nat * CC.subst) := hints7.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R3 220%positive "(#44(((273808(#45#46#47#48(5(1 84))(6(1 85))(7(1 86))#49#50#51(11(1 88))(12(1 89))(13(1 90))(14(1 91))(15(1 92))(16(1 93))(17(1 94))#52#53#54#55#56#57#58#59#60#61(28(1 95))(29(1 96))(30(1 97))(31(1 98)))()#75)#62))()())"%pstring.
