(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm8CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fsinf_casan_T Cut_fsinf_casan_R0 Cut_fsinf_casan_R1 Cut_fsinf_casan_R2 Cut_fsinf_casan_R3.
Definition dict_Cut_fsinf_casan_R4 : CCDD.pt := CCDD.mk_table 1958%positive "((0 -8416)(2 0(1 2)#1)(0 7015056)(0 18446744073709550542)(0 1152921504606846973)(5#5 1 4611686018427387904)(0 1152921504606846974)(5#7 1 4611686018427387904)(0 1152921504606846975)(5#9 1 4611686018427387904)(0 1152921504606846976)(5#11 1 4611686018427387904)((1 10)8)(2 0(1 32)(0 3))(0#13 8#14)((1 2)-120)(0#16 8(1 33))((1 2)-6128)(0#18 8(0 0))((1 2)-112)(0#20 8(1 34))((1 2)-104)(0#22 8(1 27))((1 2)-96)(0#24 8(1 26))((1 2)-88)(0#26 8(1 25))((1 2)-80)(0#28 8(1 24))((1 2)-72)(0#30 8(1 23))((1 2)-64)(0#32 8(1 22))((1 2)-56)(0#34 8(1 21))((1 2)-48)(0#36 8(1 20))((1 2)-40)(0#38 8(1 19))((1 2)-32)(0#40 8(1 18))((1 2)-24)(0#42 8(1 9))((1 2)-16)(0#44 8(1 8))((1 2)-8)(0#46 8(1 1))(5(1 2)140735332491744 140737488355328)(4(1 2)16)(3 65536 1392640)((1 2)-8672)(0 8672)(6#51#52)(0 2544)(9#51#54)((1 2)-6120)(0 6000)(9#56#57)(6#13(0 8))(5(1 10)140735332483072 140737488355072)(7#13(0 192)#51#52)(5(1 32)4096 140737488355328)((0 0)7015056)(0#63 8(1 33))((1 32)0)(7#65(0 4)#51#52)(7#65(0 4)#13(0 192))(#6#8#10#12#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#64#66#67)((1 2)-8672#52)((1 10)8(0 8))(#69#70)(0 1152921504606846972)(1310100 1310100 1310100 1310100 1312956 1256288 1312788 1312796 1312800 1312204 1314956 1314968 1315008 1315248 1315252 1315204 1315268 1312432 1312436 1312440 1330948 1331976)(0#73)(0#74(1 0))(0(4 1)#75)(0#74#76)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 36))(6(1 37))(7(1 38))(8(1 8))(9(1 9))(10(1 39))(11(1 40))(0 6384)(12#89)(13(1 33))(14(1 43))(15(1 44))(16(1 45))(17(1 46))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 47))(29(1 48))(30(1 49))(31(1 50))(#78#79#80#81#82#83#84#85#86#87#88#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109)(1 1312956)(2 0(1 32)(0 4))(0#13 8#112)(7#65(0 5)#51#52)(7#65(0 5)#13(0 192))(#6#8#10#12#113#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#64#114#115))"%pstring.

Definition t14 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_casan_R4 199%positive "(1312808((1 0)(1 35)#2(1 3)(1 4)(1 36)(1 37)(1 38)(0 0)(0 1)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)(0 53)(1 19)#3(1 10)#4(0 1)(0 1)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))#68 51#71()#72)"%pstring.
Definition BL14 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_casan_R4 3%positive "()"%pstring.
Definition hints14 : list (nat * CC.subst) := hints12.
Definition o14 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_casan_R4 36%positive "(#77(((1312956#110()#68)#111))()())"%pstring.

Definition t15 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_casan_R4 219%positive "(1312808((1 0)(1 35)#2(1 3)(1 4)(1 36)(1 37)(1 38)(0 0)(0 18446744073709551615)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)(0 53)(1 19)#3(1 10)#4(0 1)(0 1)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))#116 51#71()#72)"%pstring.
Definition BL15 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_casan_R4 3%positive "()"%pstring.
Definition hints15 : list (nat * CC.subst) := hints13.
Definition o15 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_casan_R4 37%positive "(#77(((1312956#110()#116)#111))()())"%pstring.
