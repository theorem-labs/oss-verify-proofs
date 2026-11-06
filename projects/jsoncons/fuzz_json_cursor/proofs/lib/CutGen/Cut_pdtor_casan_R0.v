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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pdtor_casan_T.
Definition dict_Cut_pdtor_casan_R0 : CCD.pt := CCD.mk_table 149%positive "((5(0 10)1 4611686018427387904)(2 0(1 2)(0 -32))((1 10)0)((0 0)2147446784)(0 17592186048512)((1 2)-4272)(0 4272)((1 32)0)((1 35)0)(2 0(1 36)(0 -1)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_casan_R0 1334%positive "((0(0(725196 725688 726216 975272 1330948 1331976))(4#1(1 0)))(((726216((1(0 725272))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(0 2147450880))(10#2)(11(0 1427896))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-32)8(2 0(1 10)(0 248)))(0#3 8(0 1363968))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 10)24)1(0 0))(0((1 10)48)1(0 0))(0((1 10)72)1(0 0))(0((1 10)96)8(0 1364920))(0((1 10)128)8(2 0(1 10)(0 96)))(0((1 10)224)8(1 36))(0((1 10)240)8(1 35))(5(2 9(6 0 0 1(1 36))(0 1))1 1)(5(1 36)265 140737488355328)(0((1 10)248)8(1 32))(0((1 10)256)8(2 0(1 32)(1 33)))(0((1 10)264)8(2 0(1 32)(1 34)))(9((1 10)8)(0 16))(9((1 10)232)(0 8))(6#3(0 272))(5(1 10)1048576 140737488351232)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 34))(7#4#5#3(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(5(1 33)0 4096)(5(2 0(4 0(0 -1)(1 33))(1 34))0 4096)(5(1 35)4096 140737479966720)(4(1 35)16)(9#6(0 4240))(6#6#7)(5(1 2)140735332487344 140737488355328)(4(1 2)16)(1((2 6#2(0 3))2147450880)(0 1))(7#6#7#3(0 272))(7#6#7#8(1 34))(7#3(0 272)#8(1 34))(7#6#7#9#10)(7#3(0 272)#9#10)(7#8(1 34)#9#10)(7#4#5#8(1 34))(7#4#5#9#10)))(1 726216)))()())"%pstring.
