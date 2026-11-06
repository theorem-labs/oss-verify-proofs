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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_to_codepoint_xasan_T.
Definition dict_Cut_to_codepoint_xasan_R0 : CCD.pt := CCD.mk_table 139%positive "((809452 810180 809556 1387168 1388196)(0#1)(2 6(1 12)(0 3))((1 12)0)((1 32)151382)((1 10)0)((0 0)2147446784)(0 17592186048512)((1 2)-16))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_to_codepoint_xasan_R0 955%positive "((0#2(16 0(0#2(1 0))))(((810180((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(0 18955))(6(0 151640))(7(0 18446744073709551554))(8(1 8))(9(1 9))(10(2 0(1 10)(0 1)))(11(0 0))(12(1 12))(13(1 13))(14(0 55296))(15(0 0))(16(2 0#3(0 2147450880)))(17(0 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(0 0))(29(1 29))(30(1 30))(31(1 31)))()((0#4 4(1 32))(0#5 1(0 0))(0((1 2)-8)8(1 1))(3 1444792 1448528)(3 151296 151808)(1((0 0)2147469802)(0 17))(1((0 0)2147469835)(0 3))(0#6 1(1 32))(5(1 32)0 127)(5(1 13)0 0)(5(1 10)4096 140737488355326)(5(2 0(4 0(0 -1)(1 10))(1 11))1 140737488355328)(5(1 11)4097 140737488355327)(1((2 6(1 10)(0 3))2147450880)(0 1))(7#7#8#6(0 1))(6#4(0 4))(5(1 12)1449984 140737488355324)(1(#3 2147450880)(0 1))(7#7#8#4(0 4))(6#9(0 16))(9#9(0 8))(5(1 2)140735332483088 140737488355328)(4(1 2)16)(7#7#8#9(0 16))(7#4(0 4)#6(0 1))(7#9(0 16)#4(0 4))(7#9(0 16)#6(0 1))))(1 810180)))((8#5 1 32 0))())"%pstring.
