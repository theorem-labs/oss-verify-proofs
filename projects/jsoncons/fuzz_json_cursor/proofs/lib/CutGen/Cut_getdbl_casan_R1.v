(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getdbl_casan_T Cut_getdbl_casan_R0.
Definition dict_Cut_getdbl_casan_R1 : CCD.pt := CCD.mk_table 1905%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 10)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(3 1359872 1392640)((0 0)1427896)(0#5 8#2)(3 84976 84984)((0 0)2147624442)(1#8(0 1))((0 0)2147461502)(1#10(0 1))((1 10)0)(1#12(0 24))(5(0 24)1 4611686018427387904)((1 2)-33)(0#15 1(1 12))((1 2)-32)(0#17 8(1 18))((1 2)-24)(0#19 8(1 9))((1 2)-16)(0#21 8(1 8))((1 2)-8)(0#23 8(1 1))(9#12(0 24))(6#12(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#29 2147450880)(1#30(0 3))((0 0)2147446784)(0 17592186048512)(7#32#33#12(0 24))((1 11)0)(9#35(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#39 2147450880)(1#40(0 5))(7#32#33#35(0 40))((1 13)0)(9#43(0 16))(6#43(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#48 2147450880)(1#49(0 2))(7#32#33#43(0 16))((1 2)-14384)(0 14351)(9#52#53)(0 14384)(6#52#55)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#52#55#12(0 24))(7#52#55#35(0 40))(7#52#55#43(0 16))(7#12(0 24)#35(0 40))(7#12(0 24)#43(0 16))(7#35(0 40)#43(0 16))(0#35 8(0 128))((1 2)-14384#55)(#66)(837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#68)(5(0 23)1 4611686018427387904)(4#70(1 0))(0#69#71)(0 838340)(1#73)(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(1 11))(2 0(1 11)(0 24))(10#83)(11(0 0))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#74#75#76#77#78#79#80#81#82#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105)((1 2)-40)(0#107 1(0 46))((1 2)-44)(0#109 4(0 0))((1 2)-48)(0#111 1(0 0))(0 14336)(9#52#113)((1 2)-47)(9#115(0 3))((1 2)-39)(9#117(0 6))(1 838412)((0 0)6883756)(0#120 4(0 1)))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_casan_R1 146%positive "(838320#3(#4#6#7#9#11#13#14#16#18#20#22#24#4#6#25#26#27#28#31#34#36#37#38#41#42#44#45#46#47#50#51#54#56#57#58#59#60#61#62#63#64#65)56#67()(0 23))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_casan_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_casan_R1 178%positive "(#72(((838412#106()(#70#108#110#112#4#6#7#9#11#13#14#16#18#20#22#24#4#6#25#26#27#28#31#34#36#37#38#41#42#44#45#46#47#50#51#114#116#118#56#57#58#59#60#61#62#63#64#65))#119))()())"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_casan_R1 150%positive "(838320#3(#4#6#7#9#11#13#14#16#18#20#22#24#4#6#25#26#27#28#31#34#36#37#38#41#42#44#45#46#47#50#51#54#56#57#58#59#60#61#62#63#64#65#121)56#67()(0 23))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_casan_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_casan_R1 182%positive "(#72(((838412#106()(#70#108#110#112#4#6#7#9#11#13#14#16#18#20#22#24#4#6#25#26#27#28#31#34#36#37#38#41#42#44#45#46#47#50#51#114#116#118#56#57#58#59#60#61#62#63#64#65#121))#119))()())"%pstring.
