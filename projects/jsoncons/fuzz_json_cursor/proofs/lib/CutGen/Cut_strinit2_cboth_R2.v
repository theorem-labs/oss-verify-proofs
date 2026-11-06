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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strinit2_cboth_T Cut_strinit2_cboth_R0 Cut_strinit2_cboth_R1.
Definition dict_Cut_strinit2_cboth_R2 : CCD.pt := CCD.mk_table 1600%positive "((2 0(1 2)(0 -64))(0 2147450880)(3 1368064 1400832)((0 0)1432824)(0#4 8#2)(2 0(1 44)(0 23))(2 6#6(0 3))(#7 2147450880)(1#8(0 1))(5(0 23)1 4611686018427387904)((1 10)8)(0#11 8(0 23))((1 10)0)(0#13 8(0 27))((1 10)16)(0#15 8(1 44))(5(1 44)4096 140737479966719)(4(1 44)16)((1 44)0)(6#19(0 26))((0 0)2147446784)(0 17592186048512)(7#21#22#19(0 26))((0 0)1368064)(0 36864)(7#24#25#19(0 26))(7#4(0 8)#19(0 26))(7#19(0 26)#13(0 24))((1 2)-4176)(0 4176)(7#19(0 26)#29#30)(5(0 24)1 4611686018427387904)((1 2)-56)(0#33 8(1 21))((1 2)-48)(0#35 8(1 20))((1 2)-40)(0#37 8(1 19))((1 2)-32)(0#39 8(1 18))((1 2)-24)(0#41 8(1 9))((1 2)-16)(0#43 8(1 8))((1 2)-8)(0#45 8(1 1))(6#13(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#50 2147450880)(1#51(0 3))(2 0(1 10)(0 8))(2 6#53(0 3))(#54 2147450880)(1#55(0 1))(2 0(1 10)(0 16))(2 6#57(0 3))(#58 2147450880)(1#59(0 1))(7#21#22#13(0 24))(0 4120)(9#29#62)(6#29#30)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#29#30#13(0 24))(5(1 12)23 23)((1 2)-4176#30)(849628 849628 849628 849628 849924 1363704 522512 1336512 1337540)(0#70)(0#71(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(11(0 0))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71))(1 849924)(2 6(1 12)(0 3))(4 0(0 8)#104)(2 0#105(0 9))(2 0(1 12)(1 44))(0#11 8(1 12))(0#13 8#106)(2 0#105(0 8))(6#19#110)(7#21#22#19#110)(7#24#25#19#110)(7#4(0 8)#19#110)(7#19#110#13(0 24))(7#19#110#29#30)(5(1 12)24 67108863))"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit2_cboth_R2 349%positive "(849860((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(0 23)(1 11)(1 44)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 10)(1 44)(0 27)#2(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#3#5#9#10#12#14#16#3#5#17#18(9#19(0 26))#20#23#26#27#28#31#32#34#36#38#40#42#44#46#3#5#47#48#49#52#56#60#61#63#64#65#66#67#68)72(#69((1 44)23(0 1)))()(0 22))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit2_cboth_R2 17%positive "(((1 44)(0 26)))"%pstring.
Definition hints7 : list (nat * CC.subst) := hints5.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_strinit2_cboth_R2 293%positive "(#72(((849924(#73#74#75#76#77#78#79#80#81(10#6)#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102)()((0((1 44)23)1(0 0))#3#5#9#10#12#14#16#3#5#17#18(9#19(0 23))(9((1 44)24)(0 2))#20#23#26#27#28#31#32#34#36#38#40#42#44#46#3#5#47#48#49#52#56#60#61#63#64#65#66#67#68))#103))()())"%pstring.

Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit2_cboth_R2 384%positive "(849860((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 12)(1 11)(1 44)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 10)(1 44)#106#2(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#3#5(1((2 6#107(0 3))2147450880)(0 1))#10#108#109#16#3#5#17#18(9#19#110)#111#112#113#114#115#116#32#34#36#38#40#42#44#46#3#5#47#48#49#52#56#60#61#63#64#65#66#67#117)72(#69(#107 0(0 1)))()(0 22))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit2_cboth_R2 15%positive "(((1 44)#110))"%pstring.
Definition hints8 : list (nat * CC.subst) := hints6.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_strinit2_cboth_R2 329%positive "(#72(((849924(#73#74#75#76#77#78#79#80#81(10#107)#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102)()((0(#107 0)1(0 0))#3#5#10#108#109#16#3#5#17#18(9#19(1 12))(9(#107 1)(2 0(2 0(4 0(0 -1)(1 12))#105)(0 7)))#111#112#113#114#115#116#32#34#36#38#40#42#44#46#3#5#47#48#49#52#56#60#61#63#64#65#66#67#117))#103))()())"%pstring.
