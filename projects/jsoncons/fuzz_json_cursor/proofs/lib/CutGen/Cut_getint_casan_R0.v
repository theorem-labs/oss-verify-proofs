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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getint_casan_T.
Definition dict_Cut_getint_casan_R0 : CCD.pt := CCD.mk_table 1299%positive "((837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#1)(5(0 24)1 4611686018427387904)(4#3(1 0))(0#2#4)(2 0(1 2)(0 -48))(2#6)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(1 10))(11(0 0))(12(0 24))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(0 2147450880)(18#23)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-33)(0#38 1(1 12))((1 2)-32)(0#40 8(1 18))((1 2)-24)(0#42 8(1 9))((1 2)-16)(0#44 8(1 8))((1 2)-8)(0#46 8(1 1))(3 1359872 1392640)((0 0)1427896)(0#49 8#23)((1 10)0)(9#51(0 24))(6#51(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#56 2147450880)(1#57(0 3))((0 0)2147446784)(0 17592186048512)(7#59#60#51(0 24))((1 11)0)(9#62(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#66 2147450880)(1#67(0 5))(7#59#60#62(0 40))((1 13)0)(9#70(0 16))(6#70(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#75 2147450880)(1#76(0 2))(7#59#60#70(0 16))((1 2)-14384)(0 14351)(9#79#80)(0 14384)(6#79#82)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#79#82#51(0 24))(7#79#82#62(0 40))(7#79#82#70(0 16))(7#51(0 24)#62(0 40))(7#51(0 24)#70(0 16))(7#62(0 40)#70(0 16))((1 11)24)(0#92 8(1 32))(1 520976))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R0 251%positive "(#5(((520976((1(0 838512))#7#8#9#10#11#12#13#14#15#16#17#18#19#20#21#22#24#25#26#27#28#29#30#31#32#33#34#35#36#37)()(#3#39#41#43#45#47#48#50#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#84#85#86#87#88#89#90#91(0#62 8(0 16))#93))#94))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_getint_casan_R0 251%positive "(#5(((520976((1(0 838196))#7#8#9#10#11#12#13#14#15#16#17#18#19#20#21#22#24#25#26#27#28#29#30#31#32#33#34#35#36#37)()(#3#39#41#43#45#47#48#50#52#53#54#55#58#61#63#64#65#68#69#71#72#73#74#77#78#81#83#84#85#86#87#88#89#90#91(0#62 8(0 32))#93))#94))()())"%pstring.
