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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_set_ec_cboth_T.
Definition dict_Cut_set_ec_cboth_R0 : CCD.pt := CCD.mk_table 772%positive "((749196 749196 749336 863640 436716 863720 1336512 1337540)(0#1)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 10)0)((1 2)-32)(0#28 8(1 18))((1 2)-24)(0#30 8(1 9))((1 2)-16)(0#32 8(1 8))((1 2)-8)(0#34 8(1 1))(3 1393824 1397544)((0 0)1432824)(0 2147450880)(0#37 8#38)(6#27(0 16))(5(1 10)7028736 140737479966704)(4(1 10)8)(2 6(1 10)(0 3))(#43 2147450880)(1#44(0 2))((0 0)2147446784)(0 17592186048512)(7#46#47#27(0 16))(5(1 11)1 31)((1 2)-1024)(9#50(0 992))(0 1024)(6#50#52)(5(1 2)140735332484096 140737488355328)(4(1 2)16)(7#50#52#27(0 16))((0 0)6882184)(5(0 20)1 4611686018427387904))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec_cboth_R0 273%positive "((0#2(1 0))(((749336((1(1 1))(2(1 2))#3#4#5#6#7(8(1 8))(9(1 9))(10(1 10))(11(0 0))#8#9#10#11#12#13(18(1 18))#14#15#16#17#18#19#20#21#22#23#24#25#26)()((0((1 10)8)8(0 1412184))(0#27 8(1 11))#29#31#33#35#36#39#40#41#42#45#48#49#51#53#54#55#56(0#57 1(0 1))))(1 749336)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec_cboth_R0 283%positive "((0#2(4#58(1 0)))(((863640((1(0 749352))(2(2 0(1 2)(0 -32)))#3#4#5#6#7(8(1 10))(9(1 11))(10(0 6882184))(11(0 6880944))#8#9#10#11#12#13(18#38)#14#15#16#17#18#19#20#21#22#23#24#25#26)()(#58#29#31#33#35#36#39(9#27(0 16))#40#41#42#45#48#49#51#53#54#55#56(0#57 1(0 0))))(1 863640)))()())"%pstring.
