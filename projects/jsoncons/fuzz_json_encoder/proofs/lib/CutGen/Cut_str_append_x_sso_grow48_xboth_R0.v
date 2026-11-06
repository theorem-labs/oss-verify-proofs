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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_append_x_sso_grow48_xboth_T.
Definition dict_Cut_str_append_x_sso_grow48_xboth_R0 : CCD.pt := CCD.mk_table 79%positive "((5(0 100)1 4611686018427387904)((1 10)0)(4 0(0 2)(1 32))((1 2)-4368)(0 4368))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_append_x_sso_grow48_xboth_R0 1160%positive "((0(0(1055420 1055668 1429232 527112 527116 1046256 1402040 1403068))(4#1(1 0)))(((1429232((1(0 1053396))(2(2 0(1 2)(0 -144)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 12))(9(1 32))(10(0 48))(11(0 18446744073709551584))(12(0 44))(13(1 32))(14(1 32))(15(0 0))(16(1 12))(17(1 11))(18(1 10))(19(0 22))(20(0 0))(21(2 0(1 10)(0 1)))(22(1 32))(23(1 11))(24(0 48))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-144)8(1 26))(0((1 2)-136)8(1 25))(0((1 2)-128)8(1 24))(0((1 2)-120)8(1 23))(0((1 2)-112)8(1 22))(0((1 2)-104)8(1 21))(0((1 2)-96)8(1 20))(0((1 2)-88)8(1 19))(0((1 2)-80)8(1 32))(0((1 2)-72)8(1 12))(0((1 2)-64)8(1 10))(0((1 2)-56)8(0 1055576))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1433600 1466368)(0((0 0)1497016)8(0 2147450880))(0#2 1#3)(0#2 8(2 0#3(4 0(0 256)(1 33))))(5(1 32)0 22)(5(1 33)0 72057594037927935)(5(1 12)1 44)(5(2 0(1 12)(1 32))23 44)(2((1 10)1)(1 32)0)(9#2(0 24))(6#2(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)(9#4(0 4224))(9((1 2)-48)(0 8))(6#4#5)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#4#5#2(0 24))))(1 1429232)))()())"%pstring.
