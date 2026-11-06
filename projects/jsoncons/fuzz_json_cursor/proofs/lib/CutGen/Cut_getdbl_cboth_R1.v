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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getdbl_cboth_T Cut_getdbl_cboth_R0.
Definition dict_Cut_getdbl_cboth_R1 : CCD.pt := CCD.mk_table 2160%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 10)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(3 1368064 1400832)((0 0)1432824)(0#5 8#2)(3 84664 84672)((0 0)2147625075)(1#8(0 1))((0 0)2147461463)(1#10(0 1))(2 6#1(0 3))(#12 2147450880)(1#13(0 1))(2 0(1 2)(0 -44))(2 6#15(0 3))(#16 2147450880)(1#17(0 1))(2 0(1 2)(0 -40))(2 6#19(0 3))(#20 2147450880)(1#21(0 1))((1 10)0)(1#23(0 24))(5(0 24)1 4611686018427387904)((1 2)-33)(0#26 1(1 12))((1 2)-32)(0#28 8(1 18))((1 2)-24)(0#30 8(1 9))((1 2)-16)(0#32 8(1 8))((1 2)-8)(0#34 8(1 1))(9#23(0 24))(6#23(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#40 2147450880)(1#41(0 3))((0 0)2147446784)(0 17592186048512)(7#43#44#23(0 24))((1 11)0)(9#46(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#50 2147450880)(1#51(0 5))(7#43#44#46(0 40))((1 13)0)(9#54(0 16))(6#54(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#59 2147450880)(1#60(0 2))(7#43#44#54(0 16))((1 2)-14384)(0 14351)(9#63#64)(0 14384)(6#63#66)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#63#66#23(0 24))(7#63#66#46(0 40))(7#63#66#54(0 16))(7#23(0 24)#46(0 40))(7#23(0 24)#54(0 16))(7#46(0 40)#54(0 16))(0#46 8(0 128))((1 2)-14384#66)(#77)(841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#79)(5(0 23)1 4611686018427387904)(4#81(1 0))(0#80#82)(0 842168)(1#84)(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(1 11))(2 0(1 11)(0 24))(10#94)(11(0 0))(12(0 0))(13(0 0))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#85#86#87#88#89#90#91#92#93#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)((1 2)-40)(0#118 1(0 46))((1 2)-44)(0#120 4(0 0))((1 2)-48)(0#122 1(0 0))((1 2)-80)(0#124 8#2)((1 2)-72)(0#126 8(1 11))((1 2)-64)(0#128 8(1 10))((1 2)-56)(0#130 8#84)(0 14304)(9#63#132)((1 2)-47)(9#134(0 3))((1 2)-39)(9#136(0 6))(1 842188)((0 0)6888684)(0#139 4(0 1)))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R1 155%positive "(842152#3(#4#6#7#9#11#14#18#22#24#25#27#29#31#33#35#4#6#36#37#38#39#42#45#47#48#49#52#53#55#56#57#58#61#62#65#67#68#69#70#71#72#73#74#75#76)56#78()(0 23))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R1 203%positive "(#83(((842188#117()(#81#119#121#123#125#127#129#131#4#6#7#9#11#14#18#22#24#25#27#29#31#33#35#4#6#36#37#38#39#42#45#47#48#49#52#53#55#56#57#58#61#62#133#135#137#67#68#69#70#71#72#73#74#75#76))#138))()())"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_cboth_R1 159%positive "(842152#3(#4#6#7#9#11#14#18#22#24#25#27#29#31#33#35#4#6#36#37#38#39#42#45#47#48#49#52#53#55#56#57#58#61#62#65#67#68#69#70#71#72#73#74#75#76#140)56#78()(0 23))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_cboth_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_cboth_R1 207%positive "(#83(((842188#117()(#81#119#121#123#125#127#129#131#4#6#7#9#11#14#18#22#24#25#27#29#31#33#35#4#6#36#37#38#39#42#45#47#48#49#52#53#55#56#57#58#61#62#133#135#137#67#68#69#70#71#72#73#74#75#76#140))#138))()())"%pstring.
