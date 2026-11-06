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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_convert_casan_T Cut_convert_casan_R0 Cut_convert_casan_R1 Cut_convert_casan_R2 Cut_convert_casan_R3.
Definition dict_Cut_convert_casan_R4 : CCD.pt := CCD.mk_table 2355%positive "((0 -112)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 55296)(0 2147450880)(6 1 0 4(1 32))(2 6#6(0 12))(0 -129)(2 9#7#8)(2 0#9(0 128))(0 65533)(2 9#6(0 63))(0 -128)(2 0#12#13)((1 0)(1 96)#2(1 3)(1 4)(1 97)(1 98)(1 99)#3(0 0)(1 100)(1 101)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(0 0)(1 12)(1 10)#3#4#5(0 128)#10#11#14(1 108)(1 109)(1 110)(1 111))(3 1388760 1392480)((0 0)1427896)(0#17 8#5)(5(0 97)1 4611686018427387904)(5(0 98)1 4611686018427387904)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)((1 2)-112)(0#23 8(0 0))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(3 6#6(0 16))(2 4(0 16)#27)(5#28 0 0)(5(1 32)132 4294967295)(5(1 32)131 4294967295)(2 1#27(0 0))(2 4#32(0 1))(5#33 0 0)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(3 6#6(0 11))(2 1#37(0 0))(2 4#38(0 1))(5#39 0 0)(5(1 32)128 4294967295)(2 4#6(0 128))(5#42 0 0)(0 2048)(2 6#6(0 11))(4 0#44#45)(2 1#46#4)(2 4#47(0 1))(5#48 0 0)((1 2)-104)(0#50 8(1 27))((1 2)-96)(0#52 8(1 26))((1 2)-88)(0#54 8(1 25))((1 2)-80)(0#56 8(1 24))((1 2)-72)(0#58 8(1 23))((1 2)-64)(0#60 8(1 22))((1 2)-56)(0#62 8(1 21))((1 2)-48)(0#64 8(1 20))((1 2)-40)(0#66 8(1 19))((1 2)-32)(0#68 8(1 18))((1 2)-24)(0#70 8(1 9))((1 2)-16)(0#72 8(1 8))((1 2)-8)(0#74 8(1 1))(5(1 32)0 4294967295)(5(1 10)7024640 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#78#79#80(0 4))(5(1 12)7024640 140737479966696)(4(1 12)8)((1 2)-4496)(0 4384)(9#84#85)(0 4496)(6#84#87)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#84#87#80(0 4))((1 12)0)(7#84#87#92(0 24))(4(1 10)8)(#16#18#19#16#18#20#16#18#21#16#18#22#24#25#26#29#30#31#34#35#36#40#41#43#49#51#53#55#57#59#61#63#65#67#69#71#73#75#16#18#76#77#81#82#83#86#88#89#90#91#93#94)((1 2)-4496#87)(#96)((1 94)(1 95))(812508 812508 812972 985020 1330948 1331976)(0#99)(0#100(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 97))(6(1 98))(7(1 99))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 102))(13(1 103))(14(1 104))(15(1 105))(16(1 106))(17(1 107))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 108))(29(1 109))(30(1 110))(31(1 111))(#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132)(1 812972)(#16#18#19#16#18#20#16#18#21#16#18#22#24#25#26#29#30#31#34#35#36#40#41#43#49#51#53#55#57#59#61#63#65#67#69#71#73#75#16#18#76#77#81#82#83#86#88#89#90#91#93))"%pstring.

Definition t26 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R4 30%positive "(812864#15#95 112#97()(0 96))"%pstring.
Definition BL26 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R4 6%positive "(#98)"%pstring.
Definition hints26 : list (nat * CC.subst) := hints22.
Definition o26 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R4 36%positive "(#101(((812972#133()#95)#134))()())"%pstring.

Definition t27 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R4 31%positive "(812864#15#135 112#97()(0 96))"%pstring.
Definition BL27 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R4 6%positive "(#98)"%pstring.
Definition hints27 : list (nat * CC.subst) := hints25.
Definition o27 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R4 37%positive "(#101(((812972#133()#135)#134))()())"%pstring.
