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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getdbl_cboth_T Cut_getdbl_cboth_R0 Cut_getdbl_cboth_R1.
Definition dict_Cut_getdbl_cboth_R2 : CCD.pt := CCD.mk_table 2165%positive "((0 842168)(2 0(1 2)(0 -48))(0 2147450880)((1 0)#1#2(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 56)(0 0)(0 0)(0 0)(1 48)(1 49)(1 50)(1 51)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(5(0 23)1 4611686018427387904)((1 2)-40)(0#6 1(0 46))((1 2)-44)(0#8 4(0 0))((1 2)-48)(0#10 1(0 0))((1 2)-80)(0#12 8#3)((1 2)-72)(0#14 8(1 11))((1 2)-64)(0#16 8(1 10))((1 2)-56)(0#18 8#1)(3 1368064 1400832)((0 0)1432824)(0#21 8#3)(3 84664 84672)((0 0)2147625075)(1#24(0 1))((0 0)2147461463)(1#26(0 1))(2 6#2(0 3))(#28 2147450880)(1#29(0 1))(2 0(1 2)(0 -44))(2 6#31(0 3))(#32 2147450880)(1#33(0 1))(2 0(1 2)(0 -40))(2 6#35(0 3))(#36 2147450880)(1#37(0 1))((1 10)0)(1#39(0 24))(5(0 24)1 4611686018427387904)((1 2)-33)(0#42 1(1 12))((1 2)-32)(0#44 8(1 18))((1 2)-24)(0#46 8(1 9))((1 2)-16)(0#48 8(1 8))((1 2)-8)(0#50 8(1 1))(9#39(0 24))(6#39(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#56 2147450880)(1#57(0 3))((0 0)2147446784)(0 17592186048512)(7#59#60#39(0 24))((1 11)0)(9#62(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#66 2147450880)(1#67(0 5))(7#59#60#62(0 40))((1 13)0)(9#70(0 16))(6#70(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#75 2147450880)(1#76(0 2))(7#59#60#70(0 16))((1 2)-14384)(0 14304)(9#79#80)((1 2)-47)(9#82(0 3))((1 2)-39)(9#84(0 6))(0 14384)(6#79#86)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#79#86#39(0 24))(7#79#86#62(0 40))(7#79#86#70(0 16))(7#39(0 24)#62(0 40))(7#39(0 24)#70(0 16))(7#62(0 40)#70(0 16))(0#62 8(0 128))((1 2)-14384#86)(#97)(841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#99)(5(0 22)1 4611686018427387904)(4#101(1 0))(0#100#102)(0 842204)(1#104)(2#2)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(1 11))(10#2)(11(1 10))(12(0 0))(13(0 0))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132#133#134#135)(1 846852)((0 0)6888684)(0#138 4(0 1)))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R2 188%positive "(842192#4(#5#7#9#11#13#15#17#19#20#22#23#25#27#30#34#38#40#41#43#45#47#49#51#20#22#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#85#87#88#89#90#91#92#93#94#95#96)57#98()(0 22))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R2 201%positive "(#103(((846852#136()(#101#5#7#9#11#13#15#17#19#20#22#23#25#27#30#34#38#40#41#43#45#47#49#51#20#22#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#85#87#88#89#90#91#92#93#94#95#96))#137))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R2 192%positive "(842192#4(#5#7#9#11#13#15#17#19#20#22#23#25#27#30#34#38#40#41#43#45#47#49#51#20#22#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#85#87#88#89#90#91#92#93#94#95#96#139)57#98()(0 22))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R2 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R2 205%positive "(#103(((846852#136()(#101#5#7#9#11#13#15#17#19#20#22#23#25#27#30#34#38#40#41#43#45#47#49#51#20#22#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#85#87#88#89#90#91#92#93#94#95#96#139))#137))()())"%pstring.
