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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_bool_root_xsrc_T Cut_visit_bool_root_xsrc_R0.
Definition dict_Cut_visit_bool_root_xsrc_R1 : CCD.pt := CCD.mk_table 1548%positive "((2 0(1 2)(0 -32))(0 66317)(5(1 53)5 5)((0 0)883736)(0#4 1(0 1))((0 0)883737)(0#6 1(0 1))((0 0)883720)(0#8 8#2)((0 0)883728)(0#10 8(0 5))(0 1048576)(5#12 1 4611686018427387904)(4 0(0 -1)(1 11))(2 0#14(0 1))(5#15 1 1)(5(1 11)0 0)(2 1(1 11)(0 0))(2 4#18(0 1))(5#19 1 1)((1 2)-24)(0#21 8(1 9))((1 2)-16)(0#23 8(1 8))((1 2)-8)(0#25 8(1 1))((1 10)8)(0#27 8(1 32))((1 10)296)(0#29 8(1 37))(5(1 37)0 18446744073709551615)(6#29(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#37#38)((1 2)-32)(9#40(0 8))(0 10624)(6#37#42)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#37#42#46(0 408))((1 32)0)(7#37#42#48(0 24))(7#46(0 408)#48(0 24))(3 65536 813152)((1 10)264)(0#52 8(1 34))((1 10)272)(0#54 8(1 34))(5(1 11)0 1)((0 0)883696)(7#37#42#57(0 18))(7#46(0 408)#57(0 18))(7#48(0 24)#57(0 18))(7#37#42#8(0 18))(7#46(0 408)#8(0 18))(7#48(0 24)#8(0 18))((1 2)-10624#42)((1 10)296(0 8))(#64#65)(0 1048575)(247212 247436 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#68)(5#67 1 4611686018427387904)(4#70(1 0))(0#69#71)(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 10))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(0 72237)(5(1 53)4 4)((0 0)883712)(0#103 1(0 1))((0 0)883713)(0#105 1(0 1))(0#57 8#101)((0 0)883704)(0#108 8(0 4))(2 0(1 11)(0 -1))(5#110 0 0)(5(1 11)1 1)(5#19 0 0))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R1 314%positive "(247352((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)#2(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#5#7#9#11#13#16#17#20#22#24#26#28#30#31#32#33#34#35#36#39#41#43#44#45#47#49#50#51#53#55#56#58#59#60#61#62#63)64#66()#67)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R1 260%positive "(#72(((274904((1(0 247360))#73#74#75#76#77#78#79(9#2)(10#2)#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100)()(#70#3#5#7#9#11#13#16#17#20#22#24#26#28#30#31#32#33#34#35#36#39#41#43#44#45#47#49#50#51#53#55#56#58#59#60#61#62#63))(1 274904)))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R1 328%positive "(247316((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)#101(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#102#104#106#107#109#13#111#112#113#22#24#26#28#30#31#32#33#34#35#36#39#41#43#44#45#47#49#50#51#53#55#56#58#59#60#61#62#63)64#66()#67)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R1 276%positive "(#72(((274788((1(0 247324))#73#74#75#76#77#78#79(9#101)(10#101)#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100)()(#70#102#104#106#107#109#13#111#112#113#22#24#26#28#30#31#32#33#34#35#36#39#41#43#44#45#47#49#50#51#53#55#56#58#59#60#61#62#63))(1 274788)))()())"%pstring.
