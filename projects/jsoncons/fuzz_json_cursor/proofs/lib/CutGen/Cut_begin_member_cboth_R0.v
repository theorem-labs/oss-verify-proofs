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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_begin_member_cboth_T.
Definition dict_Cut_begin_member_cboth_R0 : CCD.pt := CCD.mk_table 96%positive "((5(0 100)1 4611686018427387904)(2 0(1 2)(0 -96))(0 2147450880)((1 10)208)((1 2)-9792)(0 9792))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_begin_member_cboth_R0 900%positive "((0(0(800616 801080 801084 413284 801208 1336512 1337540))(4#1(1 0)))(((413284((1(0 800716))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#2)(10(0 64))(11(0 1432824))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 11))(20(1 10))(21(1 21))(22(1 22))(23#3)(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-96)8(0 0))(3 1393824 1397544)(0((0 0)1432824)8#3)(0((0 0)1432832)4(0 1))(6#4(0 1))(5(1 10)7028736 140737479966448)(4(1 10)8)(1((2 6(2 0(1 10)(0 208))(0 3))2147450880)(0 1))(7((0 0)2147446784)(0 17592186048512)#4(0 1))(9#5(0 9696))(9((1 2)-88)(0 16))(6#5#6)(5(1 2)140735332492864 140737488355328)(4(1 2)32)(7#5#6#4(0 1))))(1 413284)))()())"%pstring.
