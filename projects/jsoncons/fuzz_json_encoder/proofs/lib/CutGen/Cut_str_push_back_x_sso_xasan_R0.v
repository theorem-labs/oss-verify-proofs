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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_push_back_x_sso_xasan_T.
Definition dict_Cut_str_push_back_x_sso_xasan_R0 : CCD.pt := CCD.mk_table 86%positive "((2 0(1 10)(1 32))(4 0(0 2)(1 32))(2 0#2(0 2))((1 10)0)((1 10)1)((1 2)-4368)(0 4368))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_sso_xasan_R0 846%positive "((0(0(1041292 1041596 1387168 1388196))(1 0))(((1041596((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(2 0#1(0 1)))(11(1 11))(12#3)(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0(#1 2)1(0 0))(0(#1 1)1(1 11))(0#4 1#3)(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1417216 1449984)(0((0 0)1482488)8(0 2147450880))(5(1 11)0 255)(5(1 32)0 21)(2#5(1 32)0)(9#5(1 32))(9(#1 3)(2 0(4 0(0 -1)(1 32))(0 21)))(6#4(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(9#6(0 4304))(6#6#7)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#6#7#4(0 24))))(1 1041596)))()())"%pstring.
