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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_set_ec2_casan_T.
Definition dict_Cut_set_ec2_casan_R0 : CCD.pt := CCD.mk_table 791%positive "((825268 825268 825404 858236 435756 858316 1330948 1331976)(0#1)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(0 1407120)(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 10)0)((1 2)-32)(0#29 8(1 18))((1 2)-24)(0#31 8(1 9))((1 2)-16)(0#33 8(1 8))((1 2)-8)(0#35 8(1 1))(3 1388760 1392480)((0 0)1427896)(0 2147450880)(0#38 8#39)(6#28(0 16))(5(1 10)140735332484096 140737488355312)(4(1 10)8)(2 6(1 10)(0 3))(#44 2147450880)(1#45(0 2))((0 0)2147446784)(0 17592186048512)(7#47#48#28(0 16))(5(1 11)1 31)((1 2)-1024)(9#51(0 992))(0 1024)(6#51#53)(5(1 2)140735332484096 140737488355328)(4(1 2)16)(7#51#53#28(0 16))((0 0)6877256)(5(0 20)1 4611686018427387904))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec2_casan_R0 272%positive "((0#2(1 0))(((825404((1(1 1))(2(1 2))#3#4#5#6#7(8(1 8))(9(1 9))(10(2 0(1 10)(0 8)))(11#8)#9#10#11#12#13#14(18(1 18))#15#16#17#18#19#20#21#22#23#24#25#26#27)()((0((1 10)8)8#8)(0#28 8(1 11))#30#32#34#36#37#40#41#42#43#46#49#50#52#54#55#56#57(0#58 1(0 1))))(1 825404)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec2_casan_R0 284%positive "((0#2(4#59(1 0)))(((858236((1(0 825420))(2(2 0(1 2)(0 -32)))#3#4#5#6#7(8(1 10))(9(1 11))(10(0 6877256))(11(0 6879192))#9#10#11#12#13#14(18#39)#15#16#17#18#19#20#21#22#23#24#25#26#27)()(#59#30#32#34#36#37#40(9#28(0 16))#41#42#43#46#49#50#52#54#55#56#57(0#58 1(0 0))))(1 858236)))()())"%pstring.
