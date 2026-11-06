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
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_write_string_xsrc_T Cut_write_string_xsrc_R0 Cut_write_string_xsrc_R1 Cut_write_string_xsrc_R2.
Definition dict_Cut_write_string_xsrc_R3 : CCD.pt := CCD.mk_table 1411%positive "((2 0(1 2)(0 -32))(0 1048574)(5#2 1 4611686018427387904)(0 1048575)(5#4 1 4611686018427387904)(0 1048576)(5#6 1 4611686018427387904)(4 0(0 -1)(1 12))(2 0#8(0 2))(5#9 1 1)(5(1 12)1 1)(5(1 12)1 255)(2 1(1 12)(0 1))(2 4#13(0 1))(5#14 1 1)((1 2)-32)(0#16 8(1 18))((1 2)-24)(0#18 8(1 9))((1 2)-16)(0#20 8(1 8))((1 2)-8)(0#22 8(1 1))((1 10)8)(0#24 8(1 32))((1 10)24)(4 0(0 16)(1 36))(0#26 1#27)(5(1 36)0 15)((1 10)27)(0#30 1(0 0))((1 10)296)(0#32 8(1 35))((1 11)0)(0#34 8(1 33))((1 11)8)(0#36 8(1 34))(5(1 12)0 255)(5(1 34)0 140737488355328)(5(1 35)0 18446744073709551615)(6#32(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 11)1099511627776 140737488355328)(4(1 11)8)((1 2)-8704)(0 8672)(9#48#49)(0 8704)(6#48#51)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#48#51#55(0 408))((1 32)0)(7#48#51#57(0 24))(7#55(0 408)#57(0 24))(7#48#51#34(0 16))(7#55(0 408)#34(0 16))(7#57(0 24)#34(0 16))((1 2)-8704#51)((1 10)296(0 8))(#63#64)(0 1048573)(253060 253196 421620 422204 255860 254836 763484 764892)(0#67)(0#68(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(8(1 8))(9(1 9))(2 0(1 34)(1 35))(2 0#76(0 2))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(1 253196)(5(1 64)0 1125899906842624)(2 1(1 12)(0 3))(2 4#90(0 1))(5#91 0 0)(2 1(1 12)(0 2))(2 4#93(0 1))(5#94 0 0)(5#14 0 0)(2 0(1 35)(1 64))(2 0#97(0 2)))"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R3 319%positive "(253156((1 0)(1 80)#1(1 3)(1 4)(1 81)(1 82)(1 83)(1 10)(1 11)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 92)(1 93)(1 94)(1 95))(#3#5#7#10#11#12#15#17#19#21#23#25#28#29#31#33#35#37#38#39#40#41#42#43#44#45#46#47#50#52#53#54#56#58#59#60#61#62)96#65()#66)"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R3 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R3 342%positive "(#69(((253196(#70#71#72#73(5(1 81))(6(1 82))(7(1 83))#74#75(10#77)(11(1 35))(12(1 86))(13(1 87))(14(1 88))(15(1 89))(16(1 90))(17(1 91))#78#79#80#81#82#83#84#85#86#87(28(1 92))(29(1 93))(30(1 94))(31(1 95)))()((0#32 8#77)#3#5#7#10#11#12#15#17#19#21#23#25#28#29#31#35#37#38#39#40#41#42#43#44#45#46#47#50#52#53#54#56#58#59#60#61#62))#88))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R3 329%positive "(253324((1 0)(1 81)#1(1 3)(1 4)(1 82)(1 83)(1 84)(1 10)(1 64)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)(2 0(1 10)(0 8))(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 93)(1 94)(1 95)(1 96))(#3#89#5#7#92#95#96#17#19#21#23#25#28#29#31#33#35#37#38#39#40#41#42#43#44#45#46#47#50#52#53#54#56#58#59#60#61#62)97#65()#66)"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R3 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints4.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R3 342%positive "(#69(((253196(#70#71#72#73(5(1 82))(6(1 83))(7(1 84))#74#75(10#98)(11(1 86))(12(1 87))(13(1 88))(14(1 89))(15(1 90))(16(1 91))(17(1 92))#78#79#80#81#82#83#84#85#86#87(28(1 93))(29(1 94))(30(1 95))(31(1 96)))()((0#32 8#98)#3#89#5#7#92#95#96#17#19#21#23#25#28#29#31#35#37#38#39#40#41#42#43#44#45#46#47#50#52#53#54#56#58#59#60#61#62))#88))()())"%pstring.
