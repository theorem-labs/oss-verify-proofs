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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getint_casan_T Cut_getint_casan_R0 Cut_getint_casan_R1.
Definition dict_Cut_getint_casan_R2 : CCD.pt := CCD.mk_table 1905%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)(1 11)(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(3 1359872 1392640)((0 0)1427896)(0#5 8#2)(5(0 23)1 4611686018427387904)(5(0 24)1 4611686018427387904)((1 2)-33)(0#9 1(1 12))((1 2)-32)(0#11 8(1 18))((1 2)-24)(0#13 8(1 9))((1 2)-16)(0#15 8(1 8))((1 2)-8)(0#17 8(1 1))((1 10)0)(9#19(0 24))(6#19(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#24 2147450880)(1#25(0 3))((0 0)2147446784)(0 17592186048512)(7#27#28#19(0 24))((1 11)0)(9#30(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#34 2147450880)(1#35(0 5))(7#27#28#30(0 40))((1 13)0)(9#38(0 16))(6#38(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#43 2147450880)(1#44(0 2))(7#27#28#38(0 16))((1 2)-14384)(0 14351)(9#47#48)(0 14384)(6#47#50)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#47#50#19(0 24))(7#47#50#30(0 40))(7#47#50#38(0 16))(7#19(0 24)#30(0 40))(7#19(0 24)#38(0 16))(7#30(0 40)#38(0 16))(0#30 8(0 16))((1 11)24)(0#61 8(1 32))(#4#6#7#4#6#8#10#12#14#16#18#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#60#62)((1 2)-14384#50)(#64)(837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#66)(0#67(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(1 60))(11(1 61))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71))(#69#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99)(1 838856)(0#30 8(0 32))(#4#6#7#4#6#8#10#12#14#16#18#4#6#20#21#22#23#26#29#31#32#33#36#37#39#40#41#42#45#46#49#51#52#53#54#55#56#57#58#59#102#62))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getint_casan_R2 28%positive "(838544#3#63 72#65()(0 22))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getint_casan_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R2 35%positive "(#68(((838856#100()#63)#101))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getint_casan_R2 29%positive "(838228#3#103 72#65()(0 22))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getint_casan_R2 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R2 36%positive "(#68(((838856#100()#103)#101))()())"%pstring.
