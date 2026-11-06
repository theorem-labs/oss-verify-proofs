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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vis_end_array_casan_T.
Definition dict_Cut_vis_end_array_casan_R0 : CCD.pt := CCD.mk_table 86%positive "((5(0 100)1 4611686018427387904)(0 2147450880)((1 10)8)((1 10)0)((1 2)-2624)(0 2624))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vis_end_array_casan_R0 740%positive "((0(0(828232 828372 520976 519796 1330948 1331976))(4#1(1 0)))(((520976((1(0 828280))(2(2 0(1 2)(0 -64)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9#2)(10(2 0(1 2)(0 -48)))(11(0 0))(12(0 24))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1388760 1392480)(0((0 0)1427896)8#2)(9#3(0 40))(6#3(0 40))(5(1 10)7024640 140737479966672)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 6))(7((0 0)2147446784)(0 17592186048512)#4(0 48))(9#5(0 2600))(6#5#6)(5(1 2)140735332485696 140737488355328)(4(1 2)16)(7#5#6#4(0 48))))(1 520976)))()())"%pstring.
