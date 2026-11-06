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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getint_casan_T Cut_getint_casan_R0.
Definition dict_Cut_getint_casan_R1 : CCD.pt := CCD.mk_table 1561%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 10)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(3 1359872 1392640)((0 0)1427896)(0#5 8#2)((1 10)0)(1#7(0 24))(5(0 24)1 4611686018427387904)((1 2)-33)(0#10 1(1 12))((1 2)-32)(0#12 8(1 18))((1 2)-24)(0#14 8(1 9))((1 2)-16)(0#16 8(1 8))((1 2)-8)(0#18 8(1 1))(9#7(0 24))(6#7(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#24 2147450880)(1#25(0 3))((0 0)2147446784)(0 17592186048512)(7#27#28#7(0 24))((1 11)0)(9#30(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#34 2147450880)(1#35(0 5))(7#27#28#30(0 40))((1 13)0)(9#38(0 16))(6#38(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#43 2147450880)(1#44(0 2))(7#27#28#38(0 16))((1 2)-14384)(0 14351)(9#47#48)(0 14384)(6#47#50)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#47#50#7(0 24))(7#47#50#30(0 40))(7#47#50#38(0 16))(7#7(0 24)#30(0 40))(7#7(0 24)#38(0 16))(7#30(0 40)#38(0 16))(0#30 8(0 16))((1 11)24)(0#61 8(1 32))((1 2)-14384#50)(#63)(837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#65)(5(0 23)1 4611686018427387904)(4#67(1 0))(0#66#68)(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(1 11))(10(1 32))(11(1 10))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(0#30 8(0 32)))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getint_casan_R1 140%positive "(838512#3(#4#6#8#9#11#13#15#17#19#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#60#62)56#64()(0 23))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getint_casan_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R1 258%positive "(#69(((841088((1(0 838544))#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99)()(#67#4#6#8#9#11#13#15#17#19#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#60#62))(1 841088)))()())"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getint_casan_R1 141%positive "(838196#3(#4#6#8#9#11#13#15#17#19#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#100#62)56#64()(0 23))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getint_casan_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R1 259%positive "(#69(((839488((1(0 838228))#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99)()(#67#4#6#8#9#11#13#15#17#19#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#100#62))(1 839488)))()())"%pstring.
