(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getdbl_cboth_T Cut_getdbl_cboth_R0 Cut_getdbl_cboth_R1 Cut_getdbl_cboth_R2.
Definition dict_Cut_getdbl_cboth_R3 : CCD.pt := CCD.mk_table 1944%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 59)#1(1 3)(1 4)(1 60)(1 61)(1 62)(1 10)(1 11)(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 71)(1 72)(1 73)(1 74))(3 1368064 1400832)((0 0)1432824)(0#5 8#2)(5(0 22)1 4611686018427387904)(5(0 23)1 4611686018427387904)((1 2)-40)(0#9 1(0 46))((1 2)-44)(0#11 4(0 0))((1 2)-48)(0#13 1(0 0))(5(0 24)1 4611686018427387904)((1 2)-33)(0#16 1(1 12))((1 2)-32)(0#18 8(1 18))((1 2)-24)(0#20 8(1 9))((1 2)-16)(0#22 8(1 8))((1 2)-8)(0#24 8(1 1))((1 10)0)(9#26(0 24))(6#26(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#31 2147450880)(1#32(0 3))((0 0)2147446784)(0 17592186048512)(7#34#35#26(0 24))((1 11)0)(9#37(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#41 2147450880)(1#42(0 5))(7#34#35#37(0 40))((1 13)0)(9#45(0 16))(6#45(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#50 2147450880)(1#51(0 2))(7#34#35#45(0 16))((1 2)-14384)(0 14304)(9#54#55)((1 2)-47)(9#57(0 3))((1 2)-39)(9#59(0 6))(0 14384)(6#54#61)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#54#61#26(0 24))(7#54#61#37(0 40))(7#54#61#45(0 16))(7#26(0 24)#37(0 40))(7#26(0 24)#45(0 16))(7#37(0 40)#45(0 16))(0#37 8(0 128))(#4#6#7#8#10#12#14#4#6#15#17#19#21#23#25#4#6#27#28#29#30#33#36#38#39#40#43#44#46#47#48#49#52#53#56#58#60#62#63#64#65#66#67#68#69#70#71)((1 2)-14384#61)(#73)(841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#75)(0#76(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 60))(6(1 61))(7(1 62))(8(1 8))(9(1 9))(10(0 0))(11(1 64))(12(1 65))(13(1 66))(14(1 67))(15(1 68))(16(1 69))(17(1 70))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 71))(29(1 72))(30(1 73))(31(1 74))(#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108)(842596#109()#72)(1 842596)(#110#111)(#112))"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R3 28%positive "(842204#3#72 75#74()(0 21))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R3 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints4.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R3 14%positive "(#77#113()())"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R3 28%positive "(842204#3#72 75#74()(0 21))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R3 17%positive "(((1 57)(1 58)))"%pstring.
Definition hints7 : list (nat * CC.subst) := hints5.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R3 14%positive "(#77#113()())"%pstring.
