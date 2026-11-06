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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_uint64_nested_xsrc_T Cut_visit_uint64_nested_xsrc_R0.
Definition dict_Cut_visit_uint64_nested_xsrc_R1 : CCD.pt := CCD.mk_table 1468%positive "((2 0(1 2)(0 -32))(4 0(0 32)(1 33))(2 0#2(1 34))(#3 -32)(0#4 4(1 38))(#3 -28)(0#6 1(0 0))(#3 -26)(0#8 1(0 1))(#3 -8)(0#10 8(1 36))(6#10(0 8))(9#4(0 32))(0 1048576)(5#14 1 4611686018427387904)(4 0(0 -1)(1 38))(2 0#16(0 2))(5#17 1 1)(5(1 38)1 1)(2 1(1 38)(0 1))(2 4#20(0 1))(5#21 1 1)((1 2)-24)(0#23 8(1 9))((1 2)-16)(0#25 8(1 8))((1 2)-8)(0#27 8(1 1))((1 10)8)(0#29 8(1 32))(5(1 37)0 18446744073709551615)((1 10)296)(6#32(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#38#39)((1 2)-32)(9#41(0 8))(0 10624)(6#38#43)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#38#43#47(0 408))((1 32)0)(7#38#43#49(0 24))(7#47(0 408)#49(0 24))(3 65536 813152)((1 10)264)(0#53 8(1 34))((1 10)272)(0#55 8#3)(5(1 38)0 1)(5(1 40)0 1)(5(1 33)1 1024)(4 0(0 -32)(1 33))(2 0#60(1 35))(5#61 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#38#43#67(1 35))(7#47(0 408)#67(1 35))(7#49(0 24)#67(1 35))((1 2)-10624#43)((1 10)296(0 8))(#3 -8(0 8))(#71#72#73)(0 1048575)((1 34)(1 35))(242212 242376 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#77)(5#75 1 4611686018427387904)(3(1 3))(4(1 4))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(5(1 48)0 1125899906842624)(2 0(1 38)(0 -2))(5#93 0 18446744073709551614)(5(1 38)0 0)(5#21 0 0)(#3 -27)(0#97 1(1 39))(0#8 1(1 40)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_uint64_nested_xsrc_R1 331%positive "(242268((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#5#7#9#11#12#13#15#18#19#22#24#26#28#30#31#33#34#35#36#37#40#42#44#45#46#48#50#51#52#54#56#57#58#59#62#63#64#65#66#68#69#70)64#74()#75)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_uint64_nested_xsrc_R1 6%positive "(#76)"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_uint64_nested_xsrc_R1 407%positive "((0#78(4#79(1 0)))(((252268((1(0 242320))(2#1)#80#81(5(1 49))(6(1 50))(7(1 51))(8(1 10))(9(1 11))(10(1 11))(11(2 0(1 10)(0 8)))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))#82#83#84#85#86#87#88#89#90#91(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#79#5#7#9#11#12#13#15#18#19#22#24#26#28#30#31#33#34#35#36#37#40#42#44#45#46#48#50#51#52#54#56#57#58#59#62#63#64#65#66#68#69#70))(1 252268)))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_uint64_nested_xsrc_R1 352%positive "(242320((1 0)(1 49)#1(1 3)(1 4)(1 50)(1 51)(1 52)(1 10)(1 11)(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#92#15#94#95#96#24#26#28#30(0#32 8(1 37))#31#33#34#35#36#37#40#42#44#45#46#48#50#51#52#54#56#5#57#7#98#99#58#11#12#13#59#62#63#64#65#66#68#69#70)65#74()#75)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_uint64_nested_xsrc_R1 6%positive "(#76)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_uint64_nested_xsrc_R1 437%positive "((0#78(1 0))(((242376((1(1 1))(2(1 2))#80#81(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 9))(10(0 1))(11#3)(12(1 37))(13(1 34))(14(1 57))(15(1 58))(16(1 59))(17(1 60))#82#83#84#85#86#87#88#89#90#91(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()((0#10 8(2 0(1 36)(0 1)))(0#32 8(2 0(1 37)(1 48)))#92#15#94#95#96#24#26#28#30#31#33#34#35#36#37#40#42#44#45#46#48#50#51#54#56#5#57#7#98#99#58#12(9#4(0 24))#59#62#63#64#65#66#68#69#70))(1 242376)))()())"%pstring.
