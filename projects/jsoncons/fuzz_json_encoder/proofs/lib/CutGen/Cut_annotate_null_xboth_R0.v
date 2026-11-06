(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_annotate_null_xboth_T.
Definition dict_Cut_annotate_null_xboth_R0 : CCD.pt := CCD.mk_table 32%positive "(((1 10)0)((1 2)-4128)(0 4128))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_null_xboth_R0 753%positive "((0(0(732972 733116 1402040 1403068))(1 0))(((733116((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(0 0))(11(0 0))(12(0 0))(13(0 0))(14(0 1))(15(0 1))(16(2 6(2 0(1 10)(0 16))(0 3)))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((1 2)-24)8(0 733104))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1459384 1463120)(0((0 0)1497016)8(0 2147450880))(0#1 8(0 0))(0((1 10)8)8(0 0))(0((1 10)16)8(0 0))(5(1 10)1048576 140737488355304)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 3))(7((0 0)2147446784)(0 17592186048512)#1(0 24))(9#2(0 4104))(6#2#3)(5(1 2)140735332487200 140737488355328)(4(1 2)16)(7#2#3#1(0 24))))(1 733116)))()())"%pstring.
