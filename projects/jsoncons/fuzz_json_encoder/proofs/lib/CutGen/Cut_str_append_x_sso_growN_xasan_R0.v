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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_append_x_sso_growN_xasan_T.
Definition dict_Cut_str_append_x_sso_growN_xasan_R0 : CCD.pt := CCD.mk_table 132%positive "((5(0 100)1 4611686018427387904)(2 0(1 12)(1 32))(2 6#2(0 3))(4 0(0 8)#3)(2 0#4(0 8))((1 10)0)(4 0(0 2)(1 32))((1 2)-4368)(0 4368))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_append_x_sso_growN_xasan_R0 1159%positive "((0(0(1040708 1040956 1414360 524856 524860 1031544 1387168 1388196))(4#1(1 0)))(((1414360((1(0 1038684))(2(2 0(1 2)(0 -144)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 12))(9(1 32))(10#5)(11(0 18446744073709551584))(12#2)(13(1 32))(14(1 32))(15(0 0))(16(1 12))(17(1 11))(18(1 10))(19(0 22))(20(0 0))(21(2 0(1 10)(0 1)))(22(1 32))(23(1 11))(24#5)(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-144)8(1 26))(0((1 2)-136)8(1 25))(0((1 2)-128)8(1 24))(0((1 2)-120)8(1 23))(0((1 2)-112)8(1 22))(0((1 2)-104)8(1 21))(0((1 2)-96)8(1 20))(0((1 2)-88)8(1 19))(0((1 2)-80)8(1 32))(0((1 2)-72)8(1 12))(0((1 2)-64)8(1 10))(0((1 2)-56)8(0 1040864))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1417216 1449984)(0((0 0)1482488)8(0 2147450880))(0#6 1#7)(0#6 8(2 0#7(4 0(0 256)(1 33))))(5(1 32)0 22)(5(1 33)0 72057594037927935)(5(1 12)23 70368744177664)(5#2 45 70368744177664)(2((1 10)1)(1 32)0)(9#6(0 24))(6#6(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(9#8(0 4224))(9((1 2)-48)(0 8))(6#8#9)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#8#9#6(0 24))))(1 1414360)))()())"%pstring.
