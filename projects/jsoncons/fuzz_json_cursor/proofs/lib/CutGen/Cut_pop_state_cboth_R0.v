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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pop_state_cboth_T.
Definition dict_Cut_pop_state_cboth_R0 : CCD.pt := CCD.mk_table 1566%positive "((780820 780820 781352 413656 727976 1336512 1337540)(0#1)(5(0 16)1 4611686018427387904)(4#3(1 0))(0#2#4)(0 780916)(1#6)(2 0(1 2)(0 -96))(2#8)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#8)(10(0 96))(0 1432824)(11#18)(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 10))(0 2147450880)(20#28)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(#7#9#10#11#12#13#14#15#16#17#19#20#21#22#23#24#25#26#27#29#30#31#32#33#34#35#36#37#38#39#40)((1 2)-72)(0#42 8(1 23))((1 2)-64)(0#44 8(1 22))((1 2)-56)(0#46 8(1 21))((1 2)-48)(0#48 8(1 20))((1 2)-40)(0#50 8(1 19))((1 2)-32)(0#52 8(1 18))((1 2)-24)(0#54 8(1 9))((1 2)-16)(0#56 8(1 8))((1 2)-8)(0#58 8(1 1))((1 2)-96)(0#60 8(0 0))(3 1393824 1397544)((0 0)1432824)(0#63 8#28)((0 0)1432832)(0#65 4(0 1))((1 10)248)(0#67 8(1 32))((1 10)256)(2 0(1 32)(1 33))(0#69 8#70)(6#69(0 8))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 0(1 10)(0 248))(2 6#75(0 3))(#76 2147450880)(1#77(0 2))((0 0)2147446784)(0 17592186048512)(7#79#80#67(0 16))(#70 -1)(0#82 1(1 35))(5(1 35)0 255)(2 0#70(0 -1))(2 6#85(0 3))(#86 2147450880)(0#87 1(1 34))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)1 4096)(5(1 36)1 4096)(4 0(0 -1)(1 33))(2 0#93(1 36))(5#94 0 4096)((1 2)-4256)(0 4160)(9#96#97)((1 2)-88)(9#99(0 16))(0 4256)(6#96#101)(5(1 2)140735332487328 140737488355328)(4(1 2)32)(7#96#101#67(0 16))(7#96#101#82(0 1))(7#67(0 16)#82(0 1))(2 6(1 32)(0 3))(#108 2147450880)(2 0(1 36)(0 7))(2 6#110(0 3))(7#77(0 2)#109#111)(7#67(0 16)#109#111)(1 413656))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_pop_state_cboth_R0 169%positive "(#5(((413656#41()(#3#43#45#47#49#51#53#55#57#59#61#62#64#66#68#71#72#73#74#78#81#83#84#88#89#90#91#92#95#98#100#102#103#104#105#106#107#112#113(5(1 34)0 0)))#114))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_pop_state_cboth_R0 223%positive "(#5(((413656#41()(#3#43#45#47#49#51#53#55#57#59#61#62#64#66#68#71#72#73#74#78#81#83#84#88#89#90#91#92#95#98#100#102#103#104#105#106#107#112#113(5(1 34)1 7)(5(2 0(1 34)(4 0(0 -1)(2 9(2 0(1 33)(0 7))(0 7))))1 7)))#114))()())"%pstring.
