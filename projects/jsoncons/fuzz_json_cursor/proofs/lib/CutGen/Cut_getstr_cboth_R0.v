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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getstr_cboth_T.
Definition dict_Cut_getstr_cboth_R0 : CCD.pt := CCD.mk_table 1526%positive "((841728 841728 841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#1)(5(0 24)1 4611686018427387904)(4#3(1 0))(0#2#4)(0 842272)(1#6)(2 0(1 2)(0 -48))(2#8)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(1 10))(11(1 32))(12(1 33))(2 0(1 2)(0 -33))(13#20)(14(1 14))(15(1 15))(16(1 16))(17(1 17))(0 2147450880)(18#26)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(#7#9#10#11#12#13#14#15#16#17#18#19#21#22#23#24#25#27#28#29#30#31#32#33#34#35#36#37#38#39#40)((1 2)-33)(0#42 1(1 12))((1 2)-32)(0#44 8(1 18))((1 2)-24)(0#46 8(1 9))((1 2)-16)(0#48 8(1 8))((1 2)-8)(0#50 8(1 1))(3 1368064 1400832)((0 0)1432824)(0#53 8#26)((1 10)0)(9#55(0 24))(6#55(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#60 2147450880)(1#61(0 3))((0 0)2147446784)(0 17592186048512)(7#63#64#55(0 24))((1 11)0)(9#66(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#70 2147450880)(1#71(0 5))(7#63#64#66(0 40))((1 13)0)(9#74(0 16))(6#74(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#79 2147450880)(1#80(0 2))(7#63#64#74(0 16))((1 2)-14384)(0 14351)(9#83#84)(0 14384)(6#83#86)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#83#86#55(0 24))(7#83#86#66(0 40))(7#83#86#74(0 16))(7#55(0 24)#66(0 40))(7#55(0 24)#74(0 16))(7#66(0 40)#74(0 16))(0#66 8(0 1))((1 11)24)(0#97 8(1 32))((1 11)32)(0#99 8(1 33))(5(1 33)0 22)(1 849628)(5(1 33)23 67108863)(0 4097)(0#66 8#104))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_cboth_R0 150%positive "(#5(((849628#41()(#3#43#45#47#49#51#52#54#56#57#58#59#62#65#67#68#69#72#73#75#76#77#78#81#82#85#87#88#89#90#91#92#93#94#95#96#98#100#101))#102))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_cboth_R0 150%positive "(#5(((849628#41()(#3#43#45#47#49#51#52#54#56#57#58#59#62#65#67#68#69#72#73#75#76#77#78#81#82#85#87#88#89#90#91#92#93#94#95#96#98#100#103))#102))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_cboth_R0 151%positive "(#5(((849628#41()(#3#43#45#47#49#51#52#54#56#57#58#59#62#65#67#68#69#72#73#75#76#77#78#81#82#85#87#88#89#90#91#92#93#94#95#105#98#100#101))#102))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_cboth_R0 151%positive "(#5(((849628#41()(#3#43#45#47#49#51#52#54#56#57#58#59#62#65#67#68#69#72#73#75#76#77#78#81#82#85#87#88#89#90#91#92#93#94#95#105#98#100#103))#102))()())"%pstring.
