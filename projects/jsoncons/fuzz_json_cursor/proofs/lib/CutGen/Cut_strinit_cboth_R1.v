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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strinit_cboth_T Cut_strinit_cboth_R0.
Definition dict_Cut_strinit_cboth_R1 : CCD.pt := CCD.mk_table 1651%positive "((2 0(1 2)(0 -64))(2 0(1 10)(0 1))(0 2147450880)(3 1368064 1400832)((0 0)1432824)(0#5 8#3)(2 0(1 10)(1 32))(2 0#7(0 1))(2 6#8(0 3))(#9 2147450880)(1#10(0 1))(5(0 24)1 4611686018427387904)((1 10)0)(4 0(0 2)(1 32))(0#13 1#14)((1 2)-56)(0#16 8(1 21))((1 2)-48)(0#18 8(1 20))((1 2)-40)(0#20 8(1 19))((1 2)-32)(0#22 8(1 18))((1 2)-24)(0#24 8(1 9))((1 2)-16)(0#26 8(1 8))((1 2)-8)(0#28 8(1 1))((1 10)1)(6#13(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#34 2147450880)(1#35(0 3))(2 0(1 10)(0 8))(2 6#37(0 3))(#38 2147450880)(1#39(0 1))(2 0(1 10)(0 16))(2 6#41(0 3))(#42 2147450880)(1#43(0 1))((0 0)2147446784)(0 17592186048512)(7#45#46#13(0 24))((1 2)-4176)(0 4120)(9#48#49)(0 4176)(6#48#51)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#48#51#13(0 24))(5(1 32)1 22)((1 2)-4176#51)(720088 720088 720088 720088 720384 1363704 522512 1336512 1337540)(0#58)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(5(1 44)4096 140737479966719)(4(1 44)16)((1 44)0)(9#82(0 26))(6#82(0 26))(7#45#46#82(0 26))((0 0)1368064)(0 36864)(7#86#87#82(0 26))(7#5(0 8)#82(0 26))(7#82(0 26)#13(0 24))(7#82(0 26)#48#51)(9#13(0 24))(5(1 12)23 23)((1 10)0(0 24))(5(0 23)1 4611686018427387904)(4#95(1 0))(0#59#96)(0 720320)(1#98)(2#1)(9(1 11))(10(1 44))(11(1 11))(18(1 10))(19(1 44))(21#3)((1 10)8)((1 10)16)(0#108 8(1 44))(1 522512)(2 6(1 12)(0 3))(4 0(0 8)#111)(2 0#112(0 8))(9#82#113)(6#82#113)(7#45#46#82#113)(7#86#87#82#113)(7#5(0 8)#82#113)(7#82#113#13(0 24))(7#82#113#48#51)(5(1 12)24 67108863)(2 0#112(0 9)))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_cboth_R1 304%positive "(720320((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 32)(1 11)#2(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)#2(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#4#6#11#12#15#17#19#21#23#25#27#29#4#6(9#30(0 23))#31#32#33#36#40#44#47#50#52#53#54#55#56#11)56(#57(#8 0(0 1)))()(0 23))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_cboth_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints1.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_cboth_R1 347%positive "((0#59(1 0))(((720384((1(1 1))(2(1 2))#60#61#62#63#64(8(1 8))(9(1 9))(10#8)(11(0 0))(12(1 46))#65#66#67#68#69(18(1 18))(19(1 19))(20(1 20))(21(1 21))#70#71#72#73#74#75#76#77#78#79)()((0(#7 1)1(0 0))#4#6#11#12#15#17#19#21#23#25#27#29#4#6(9#30(1 32))(9(#7 2)(2 0(4 0(0 -1)(1 32))(0 22)))#31#32#33#36#40#44#47#50#52#53#54#55#56#11))(1 720384)))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_cboth_R1 328%positive "(720228((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(0 23)(1 11)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)(1 19)(0 26)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#4#6#80#81#83#84#85#88#89#90#91#12#17#19#21#23#25#27#29#4#6#92#31#32#33#36#40#44#47#50#52#53#54#55#93)56(#57#94((1 44)23(0 1)))()(0 23))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_cboth_R1 17%positive "(((1 44)(0 26)))"%pstring.
Definition hints5 : list (nat * CC.subst) := hints2.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_cboth_R1 286%positive "(#97(((522512(#99#100#60#61#62#63#64(8(0 23))#101#102#103(12(0 23))#65#66#67#68#69#104#105(20(0 27))#106#70#71#72#73#74#75#76#77#78#79)()(#95(0#107 8(0 23))(0#13 8(0 27))#109#4#6#80#81#83#84#85#88#89#90#91#12#17#19#21#23#25#27#29#4#6#31#32#33#36#40#44#47#50#52#53#54#55#93))#110))()())"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_cboth_R1 344%positive "(720228((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 12)(1 11)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)(1 19)#113#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#4#6#80#81#114#115#116#117#118#119#120#12#17#19#21#23#25#27#29#4#6#92#31#32#33#36#40#44#47#50#52#53#54#55#121)56(#57#94((2 0(1 12)(1 44))0(0 1)))()(0 23))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_cboth_R1 15%positive "(((1 44)#113))"%pstring.
Definition hints6 : list (nat * CC.subst) := hints3.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_cboth_R1 290%positive "(#97(((522512(#99#100#60#61#62#63#64(8(1 12))#101#102#103(12(1 12))#65#66#67#68#69#104#105(20#122)#106#70#71#72#73#74#75#76#77#78#79)()(#95(0#107 8(1 12))(0#13 8#122)#109#4#6#80#81#114#115#116#117#118#119#120#12#17#19#21#23#25#27#29#4#6#31#32#33#36#40#44#47#50#52#53#54#55#121))#110))()())"%pstring.
