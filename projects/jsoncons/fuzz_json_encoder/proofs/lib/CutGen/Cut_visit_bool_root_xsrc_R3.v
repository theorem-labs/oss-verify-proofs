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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_bool_root_xsrc_T Cut_visit_bool_root_xsrc_R0 Cut_visit_bool_root_xsrc_R1 Cut_visit_bool_root_xsrc_R2.
Definition dict_Cut_visit_bool_root_xsrc_R3 : CCD.pt := CCD.mk_table 1663%positive "((2 0(1 2)(0 -32))(0 66317)(0 1048574)(5#3 1 4611686018427387904)(5(1 69)5 5)((0 0)883736)(0#6 1(0 1))((0 0)883737)(0#8 1(0 1))((0 0)883720)(0#10 8#2)((0 0)883728)(0#12 8(0 5))(0 1048575)(5#14 1 4611686018427387904)(5(1 53)5 5)(0 1048576)(5#17 1 4611686018427387904)(4 0(0 -1)(1 11))(2 0#19(0 1))(5#20 1 1)(5(1 11)0 0)(2 1(1 11)(0 0))(2 4#23(0 1))(5#24 1 1)((1 2)-24)(0#26 8(1 9))((1 2)-16)(0#28 8(1 8))((1 2)-8)(0#30 8(1 1))((1 10)8)(0#32 8(1 32))((1 10)296)(0#34 8(1 37))(5(1 37)0 18446744073709551615)(6#34(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#42#43)((1 2)-32)(9#45(0 8))(0 10624)(6#42#47)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#42#47#51(0 408))((1 32)0)(7#42#47#53(0 24))(7#51(0 408)#53(0 24))(3 65536 813152)((1 10)264)(0#57 8(1 34))((1 10)272)(0#59 8(1 34))(5(1 11)0 1)((0 0)883696)(7#42#47#62(0 18))(7#51(0 408)#62(0 18))(7#53(0 24)#62(0 18))(7#42#47#10(0 18))(7#51(0 408)#10(0 18))(7#53(0 24)#10(0 18))((1 2)-10624#47)((1 10)296(0 8))(#69#70)(0 1048573)(247212 247436 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#73)(5#72 1 4611686018427387904)(4#75(1 0))(0#74#76)(2#1)(3(1 3))(4(1 4))(5(1 81))(6(1 82))(7(1 83))(8(1 10))(10(1 84))(11(1 85))(12(1 86))(13(1 87))(14(1 88))(15(1 89))(16(1 90))(17(1 91))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 92))(29(1 93))(30(1 94))(31(1 95))(0 72237)(5(1 69)4 4)((0 0)883712)(0#109 1(0 1))((0 0)883713)(0#111 1(0 1))(0#62 8#107)((0 0)883704)(0#114 8(0 4))(5(1 53)4 4)(2 0(1 11)(0 -1))(5#117 0 0)(5(1 11)1 1)(5#24 0 0))"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R3 323%positive "(247376((1 0)(1 80)#1(1 3)(1 4)(1 81)(1 82)(1 83)(1 10)#2(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 92)(1 93)(1 94)(1 95))(#4#5#7#9#11#13#15#16#18#21#22#25#27#29#31#33#35#36#37#38#39#40#41#44#46#48#49#50#52#54#55#56#58#60#61#63#64#65#66#67#68)96#71()#72)"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R3 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R3 272%positive "(#77(((274904((1(0 247380))#78#79#80#81#82#83#84(9#2)#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106)()(#75#4#5#7#9#11#13#15#16#18#21#22#25#27#29#31#33#35#36#37#38#39#40#41#44#46#48#49#50#52#54#55#56#58#60#61#63#64#65#66#67#68))(1 274904)))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R3 337%positive "(247340((1 0)(1 80)#1(1 3)(1 4)(1 81)(1 82)(1 83)(1 10)#107(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 92)(1 93)(1 94)(1 95))(#4#108#110#112#113#115#15#116#18#118#119#120#27#29#31#33#35#36#37#38#39#40#41#44#46#48#49#50#52#54#55#56#58#60#61#63#64#65#66#67#68)96#71()#72)"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R3 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints4.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R3 286%positive "(#77(((274788((1(0 247344))#78#79#80#81#82#83#84(9#107)#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106)()(#75#4#108#110#112#113#115#15#116#18#118#119#120#27#29#31#33#35#36#37#38#39#40#41#44#46#48#49#50#52#54#55#56#58#60#61#63#64#65#66#67#68))(1 274788)))()())"%pstring.
