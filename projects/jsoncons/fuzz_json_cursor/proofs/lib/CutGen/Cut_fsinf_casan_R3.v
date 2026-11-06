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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fsinf_casan_T Cut_fsinf_casan_R0 Cut_fsinf_casan_R1 Cut_fsinf_casan_R2.
Definition dict_Cut_fsinf_casan_R3 : CCDD.pt := CCDD.mk_table 1844%positive "((0 -8416)(2 0(1 2)#1)(0 2139095040)(0 4096)(0 7015056)(0 18446744073709550542)(0 1152921504606846974)(5#7 1 4611686018427387904)(0 1152921504606846975)(5#9 1 4611686018427387904)(0 1152921504606846976)(5#11 1 4611686018427387904)((1 10)8)(2 0(1 32)(0 3))(0#13 8#14)((1 2)-120)(0#16 8(1 33))((1 2)-6128)(0#18 8(0 0))((1 2)-112)(0#20 8(1 34))((1 2)-104)(0#22 8(1 27))((1 2)-96)(0#24 8(1 26))((1 2)-88)(0#26 8(1 25))((1 2)-80)(0#28 8(1 24))((1 2)-72)(0#30 8(1 23))((1 2)-64)(0#32 8(1 22))((1 2)-56)(0#34 8(1 21))((1 2)-48)(0#36 8(1 20))((1 2)-40)(0#38 8(1 19))((1 2)-32)(0#40 8(1 18))((1 2)-24)(0#42 8(1 9))((1 2)-16)(0#44 8(1 8))((1 2)-8)(0#46 8(1 1))(5(1 2)140735332491744 140737488355328)(4(1 2)16)(3 65536 1392640)((1 2)-8672)(0 8672)(6#51#52)(0 2544)(9#51#54)((1 2)-6120)(0 6000)(9#56#57)(6#13(0 8))(5(1 10)140735332483072 140737488355072)(7#13(0 192)#51#52)(5(1 32)4096 140737488355328)((1 10)184)(0 18446744073709551615)(0#63 8#64)((1 10)192)(0#66 8(0 0))((0 0)7015056)(0#68 8(1 33))((1 32)0)(7#70(0 4)#51#52)(7#70(0 4)#13(0 192))(0#70 1(0 105))((1 32)1)(0#74 1(0 110))((1 32)2)(0#76 1(0 102))((1 32)3)(0#78 1(0 0))((1 2)-8672#52)((1 10)8(0 8))(#80#81)(0 1152921504606846973)(1310100 1310100 1310100 1310100 1312956 1256288 1312788 1312796 1312800 1312204 1314956 1314968 1315008 1315248 1315252 1315204 1315268 1312432 1312436 1312440 1330948 1331976)(0#84)(5#83 1 4611686018427387904)(4#86(1 0))(0#85#87)(0 1312808)(1#89)(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 0))(10#3)(11(0 73))(12(0 73))(13#4)(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(0 53))(19(1 19))(20#5)(21(1 10))(22#6)(23(0 1))(24(0 1))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(1 1256288)(2 0(1 32)(0 4))(0#13 8#121)(7#70(0 5)#51#52)(7#70(0 5)#13(0 192))(0#70 1(0 45))(0#74 1(0 105))(0#76 1(0 110))(0#78 1(0 102))((1 32)4)(0#129 1(0 0)))"%pstring.

Definition t12 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_casan_R3 301%positive "(1312804((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)(0 1)#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#10#12#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#65#67#69#71#72#73#75#77#79)35#82()#83)"%pstring.
Definition BL12 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_casan_R3 3%positive "()"%pstring.
Definition hints12 : list (nat * CC.subst) := hints8.
Definition o12 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_casan_R3 270%positive "(#88(((1256288(#90#91#92#93#94#95#96#97(9(0 1))#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119)()(#86#8#10#12#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#65#67#69#71#72#73#75#77#79))#120))()())"%pstring.

Definition t13 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_casan_R3 310%positive "(1312804((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)#64#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#10#12#122#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#65#67#69#123#124#125#126#127#128#130)35#82()#83)"%pstring.
Definition BL13 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_casan_R3 3%positive "()"%pstring.
Definition hints13 : list (nat * CC.subst) := hints9.
Definition o13 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_casan_R3 279%positive "(#88(((1256288(#90#91#92#93#94#95#96#97(9#64)#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119)()(#86#8#10#12#122#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#47#48#49#50#53#55#58#59#60#61#62#65#67#69#123#124#125#126#127#128#130))#120))()())"%pstring.
