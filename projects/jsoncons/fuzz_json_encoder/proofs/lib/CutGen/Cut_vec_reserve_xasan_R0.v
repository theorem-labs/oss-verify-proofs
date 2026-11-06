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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xasan_T.
Definition dict_Cut_vec_reserve_xasan_R0 : CCD.pt := CCD.mk_table 137%positive "((5(0 16)1 4611686018427387904)(2 0(1 2)(0 -80))((1 10)0)(2 6(1 10)(0 3))(#4 2147450880)((1 2)-8192)(0 8192)(2 6#2(0 3))(#8 2147450880))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xasan_R0 860%positive "((0(0(840148 840376 1414360 730524 524864 841184 1387168 1388196))(4#1(1 0)))(((1414360((1(0 840284))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(0 66))(10(0 66))(11(0 0))(12(0 0))(13(2 6(2 0(1 10)(0 8))(0 3)))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(0 0))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-40)8(1 10))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1444792 1448528)(0((0 0)1482488)8(0 2147450880))(0#3 8(0 0))(0((1 10)8)8(0 0))(0((1 10)16)8(0 0))(6#3(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(1#5(0 3))(7((0 0)2147446784)(0 17592186048512)#3(0 24))(5(1 11)66 66)(9#6(0 8152))(6#6#7)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#9(0 10))(7#6#7#3(0 24))(7#5(0 3)#9(0 10))))(1 1414360)))()())"%pstring.
