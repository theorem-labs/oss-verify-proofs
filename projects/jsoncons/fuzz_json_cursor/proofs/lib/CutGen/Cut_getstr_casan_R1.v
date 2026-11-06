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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getstr_casan_T Cut_getstr_casan_R0.
Definition dict_Cut_getstr_casan_R1 : CCD.pt := CCD.mk_table 2206%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 42)#1(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(1 11)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 54)(1 55)(1 56)(1 57))(3 1359872 1392640)((0 0)1427896)(0#5 8#2)(5(0 24)1 4611686018427387904)((1 2)-33)(0#8 1(1 12))((1 2)-32)(0#10 8(1 18))((1 2)-24)(0#12 8(1 9))((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))((1 10)0)(9#18(0 24))(6#18(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#23 2147450880)(1#24(0 3))((0 0)2147446784)(0 17592186048512)(7#26#27#18(0 24))((1 11)0)(9#29(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#33 2147450880)(1#34(0 5))(7#26#27#29(0 40))((1 13)0)(9#37(0 16))(6#37(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#42 2147450880)(1#43(0 2))(7#26#27#37(0 16))((1 2)-14384)(0 14351)(9#46#47)(0 14384)(6#46#49)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#46#49#18(0 24))(7#46#49#29(0 40))(7#46#49#37(0 16))(7#18(0 24)#29(0 40))(7#18(0 24)#37(0 16))(7#29(0 40)#37(0 16))(0#29 8(0 1))((1 11)24)(0#60 8(1 32))((1 11)32)(0#62 8(1 33))(5(1 33)0 22)(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#59#61#63#64)((1 2)-14384#49)(#66)(837940 837940 837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#68)(0#69(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 43))(6(1 44))(7(1 45))(8(1 8))(9(1 9))(10(1 46))(11(1 47))(12(1 48))(13(1 49))(14(1 50))(15(1 51))(16(1 52))(17(1 53))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 54))(29(1 55))(30(1 56))(31(1 57))(#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101)(1 838856)(5(1 33)23 67108863)(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#59#61#63#104)((1 40)(1 41))(0 4097)(0#29 8#107)(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#108#61#63#64)(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#108#61#63#104))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getstr_casan_R1 28%positive "(838492#3#65 58#67()(0 23))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getstr_casan_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_casan_R1 35%positive "(#70(((838856#102()#65)#103))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getstr_casan_R1 29%positive "(838492#3#105 58#67()(0 23))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getstr_casan_R1 7%positive "(#106)"%pstring.
Definition hints5 : list (nat * CC.subst) := hints1.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_casan_R1 36%positive "(#70(((838856#102()#105)#103))()())"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getstr_casan_R1 29%positive "(838492#3#109 58#67()(0 23))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getstr_casan_R1 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints2.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_casan_R1 36%positive "(#70(((838856#102()#109)#103))()())"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getstr_casan_R1 29%positive "(838492#3#110 58#67()(0 23))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getstr_casan_R1 7%positive "(#106)"%pstring.
Definition hints7 : list (nat * CC.subst) := hints3.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_casan_R1 36%positive "(#70(((838856#102()#110)#103))()())"%pstring.
