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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_end_object_last_xsrc_T Cut_visit_end_object_last_xsrc_R0.
Definition dict_Cut_visit_end_object_last_xsrc_R1 : CCD.pt := CCD.mk_table 1889%positive "((2 0(1 2)(0 -48))((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 9)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(0 1048576)(5#3 1 4611686018427387904)((1 10)272)(4 0(0 32)(1 33))(2 0#6(1 34))(2 0#7(0 -32))(0#5 8#8)(4 0(0 -1)(1 40))(2 0#10(0 1))(5#11 1 1)(5(1 40)0 0)(2 1(1 40)(0 0))(2 4#14(0 1))(5#15 1 1)((1 10)288)(0#17 4(0 0))((1 10)400)(0#19 4(0 0))((1 2)-24)(0#21 8(1 9))((1 2)-16)(0#23 8(1 8))((1 2)-8)(0#25 8(1 1))((1 10)8)(0#27 8(1 32))((1 10)36)(0#29 1(0 4))(6#17(0 4))(6#19(0 4))(6#5(0 8))((1 10)296)(5(1 37)0 18446744073709551615)(6#34(0 8))((1 10)352)(0 83540)(0#37 8#38)((1 10)360)(0#40 8(0 1))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10576)(9#46#47)((1 2)-48)(9#49(0 24))(0 10624)(6#46#51)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#46#51#55(0 408))((1 32)0)(7#46#51#57(0 24))(7#55(0 408)#57(0 24))(3 65536 813152)((1 10)264)(0#61 8(1 34))(#7 -32)(0#63 4(1 38))(5(1 38)0 1)(#7 -28)(0#66 1(0 0))(#7 -27)(0#68 1(1 39))(#7 -26)(0#70 1(1 40))(5(1 40)0 1)(#7 -8)(0#73 8(1 36))(9#63(0 32))(4 0(0 -32)(1 33))(2 0#76(1 35))(5#77 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#46#51#83(1 35))(7#55(0 408)#83(1 35))(7#57(0 24)#83(1 35))(5(1 33)1 1)((1 2)-10624#51)((1 10)272(0 8))((1 10)288(0 4))((1 10)296(0 8))((1 10)400(0 4))(#88#89#90#91#92)(0 1048575)((1 34)(1 35))(244800 244964 421620 251692 763484 764892)(0#96)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(9(1 9))(2 0(1 37)(0 1))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(2 0(1 40)(0 -1))(5#123 0 0)(5(1 40)1 1)(5#15 0 0)(5#94 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_end_object_last_xsrc_R1 185%positive "(244904#2(#4#9#12#13#16#18#20#22#24#26#28#30#31#32#33(0#34 8(1 37))#35#36#39#41#42#43#44#45#48#50#52#53#54#56#58#59#60#62#64#65#67#69#71#72#74#75#78#79#80#81#82#84#85#86#87)64#93()#94)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_end_object_last_xsrc_R1 6%positive "(#95)"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_end_object_last_xsrc_R1 361%positive "((0#97(1 0))(((244964((1(1 1))(2(1 2))#98#99#100#101#102(8(1 8))#103(10(0 1))(11#104)(12(1 37))(13(1 34))#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122)()((0#34 8#104)#4#9#12#13#16#18#20#22#24#26#28#30#31#32#33#35#36#39#41#42#43#44#45#48#50#52#53#54#56#58#59#60#62#64#65#67#69#71#72#74#75#78#79#80#81#82#84#85#86#87))(1 244964)))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_end_object_last_xsrc_R1 181%positive "(244876#2(#4#124#125#126#18#20#22#24#26#28#30#31#32#33#35#36#39#41#42#43#44#45#48#50#52#53#54#56#58#59#60#62(0#5 8#7)#64#65#67#69#71#72#74#75#78#79#80#81#82#84#85#86#87)64#93()#94)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_end_object_last_xsrc_R1 6%positive "(#95)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_end_object_last_xsrc_R1 361%positive "((0#97(4#127(1 0)))(((421620((1(0 244904))(2#1)#98#99#100#101#102(8(1 10))#103(10(1 32))(11#38)(12(0 1))(13#8)#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122)()(#127#9#4#124#125#126#18#20#22#24#26#28#30#31#32#33#35#36#39#41#42#43#44#45#48#50#52#53#54#56#58#59#60#62#64#65#67#69#71#72#74#75#78#79#80#81#82#84#85#86#87))(1 421620)))()())"%pstring.
