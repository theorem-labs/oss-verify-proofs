(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums EncSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_string_nested_xsrc_T Cut_visit_string_nested_xsrc_R0.
Definition dict_Cut_visit_string_nested_xsrc_R1 : CCD.pt := CCD.mk_table 1881%positive "((2 0(1 2)(0 -48))((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 14)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 13)(1 12)(1 11)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(4 0(0 32)(1 33))(2 0#3(1 34))(#4 -32)(0#5 4(1 38))(#4 -28)(0#7 1(0 0))(#4 -26)(0#9 1(0 1))(#4 -8)(0#11 8(1 36))(6#11(0 8))(9#5(0 32))(0 1048576)(5#15 1 4611686018427387904)(4 0(0 -1)(1 38))(2 0#17(0 2))(5#18 1 1)(5(1 38)1 1)(2 1(1 38)(0 1))(2 4#21(0 1))(5#22 1 1)((1 2)-48)(0#24 8(1 20))((1 2)-40)(0#26 8(1 19))((1 2)-32)(0#28 8(1 18))((1 2)-24)(0#30 8(1 9))((1 2)-16)(0#32 8(1 8))((1 2)-8)(0#34 8(1 1))((1 10)8)(0#36 8(1 32))(5(1 37)0 18446744073709551615)((1 10)296)(6#39(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10576)(9#45#46)(0 10624)(6#45#48)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#45#48#52(0 408))((1 32)0)(7#45#48#54(0 24))(7#52(0 408)#54(0 24))(3 65536 813152)((1 10)264)(0#58 8(1 34))((1 10)272)(0#60 8#4)(5(1 38)0 1)(5(1 40)0 1)(5(1 33)1 1024)(4 0(0 -32)(1 33))(2 0#65(1 35))(5#66 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#45#48#72(1 35))(7#52(0 408)#72(1 35))(7#54(0 24)#72(1 35))((1 11)0)(7#76(0 16)#72(1 35))(5(1 12)0 255)(5(1 11)1099511627776 140737488355328)(4(1 11)8)(7#45#48#76(0 16))(7#52(0 408)#76(0 16))(7#54(0 24)#76(0 16))((1 2)-10624#48)((1 10)296(0 8))(#4 -8(0 8))(#84#85#86)(0 1048575)((1 34)(1 35))(247440 247640 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#90)(5#88 1 4611686018427387904)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(15(1 57))(16(1 58))(17(1 59))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(2 0(1 38)(0 -2))(5#112 0 18446744073709551614)(5(1 38)0 0)(5#22 0 0)(2 0(1 36)(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_string_nested_xsrc_R1 174%positive "(247520#2(#6#8#10#12#13#14#16#19#20#23#25#27#29#31#33#35#37#38#40#41#42#43#44#47#49#50#51#53#55#56#57#59#61#62#63#64#67#68#69#70#71#73#74#75#77#78#79#80#81#82#83)64#87()#88)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_string_nested_xsrc_R1 6%positive "(#89)"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_string_nested_xsrc_R1 391%positive "((0#91(4#92(1 0)))(((253060((1(0 247584))(2#1)#93#94#95#96#97(8(1 10))(9(1 14))(10(1 10))(11(1 11))(12(1 12))(13(1 13))(14(1 14))#98#99#100(18(1 13))(19(1 12))(20(1 11))#101#102#103#104#105#106#107#108#109#110#111)()(#92#6#8#10#12#13#14#16#19#20#23#25#27#29#31#33#35#37#38#40#41#42#43#44#47#49#50#51#53#55#56#57#59#61#62#63#64#67#68#69#70#71#73#74#75#77#78#79#80#81#82#83))(1 253060)))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_string_nested_xsrc_R1 174%positive "(247584#2(#6#8#12#13#14#16#113#114#115#25#27#29#31#33#35#37#38#40#41#42#43#44#47#49#50#51#53#55#56#57#59#61#62#63#64#67#68#69#70#71#73#74#75#77#78#79#80#81#82#83)64#87()#88)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_string_nested_xsrc_R1 6%positive "(#89)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_string_nested_xsrc_R1 389%positive "((0#91(1 0))(((247640((1(1 1))(2(1 2))#93#94#95#96#97(8(1 8))(9(1 9))(10(0 1))(11#116)(12(1 54))(13(1 55))(14(1 56))#98#99#100(18(1 18))(19(1 19))(20(1 20))#101#102#103#104#105#106#107#108#109#110#111)()((0#11 8#116)#6#8#13(9#5(0 24))#16#113#114#115#25#27#29#31#33#35#37#38#40#41#42#43#44#47#49#50#51#53#55#56#59#61#62#63#64#67#68#69#70#71#73#74#75#77#78#79#80#81#82#83))(1 247640)))()())"%pstring.
