(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_dtor_xasan_T.
Definition dict_Cut_vec_dtor_xasan_R0 : CCD.pt := CCD.mk_table 251%positive "((5(0 8)1 4611686018427387904)(0 2147450880)(2 6(1 10)(0 3))((1 10)0)(#3 2147450880)((0 0)2147446784)(0 17592186048512)((1 32)0)(2 6(1 32)(0 3))(#9 2147450880)((1 2)-4192)(0 4192)((1 33)0)(2 6(1 33)(0 3))(#14 2147450880)(2 0(1 35)(0 7))(2 6#16(0 3)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xasan_R0 1075%positive "((0(0(730236 730472 1031544 730684 730524 1387168 1388196))(4#1(1 0)))(((730684((1(0 730352))(2(2 0(1 2)(0 -32)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9#2)(10(1 32))(11(1 34))(12(1 33))(13(0 0))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(2 0#3#2))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 32)8)8(1 33))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0#4 8(1 32))(5(1 10)1048576 140737488355320)(4(1 10)8)(1#5(0 1))(7#6#7#4(0 8))(0#8 8(1 33))(0((1 32)16)8(2 0(1 33)(1 35)))(6#8(0 24))(5(1 32)1048576 140737488354816)(4(1 32)8)(1#10(0 3))(7#6#7#8(0 24))(5(1 33)17594333495296 140737479966720)(4(1 33)16)(5(1 35)1 4096)(5(2 0(4 0(0 -1)(1 34))(1 35))0 4096)(5(1 34)0 4096)(9#11(0 4160))(6#11#12)(5(1 2)140735332487264 140737488355328)(4(1 2)16)(7#11#12#8(0 24))(7#11#12#4(0 8))(7#4(0 8)#8(0 24))(7#11#12#13(1 35))(7#8(0 24)#13(1 35))(7#4(0 8)#13(1 35))(7#10(0 3)#15#17)(7#5(0 1)#15#17)(7#8(0 24)#15#17)(7#4(0 8)#15#17)))(1 730684)))()())"%pstring.
