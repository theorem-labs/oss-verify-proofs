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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xboth_T.
Definition dict_Cut_vec_reserve_xboth_R0 : CCD.pt := CCD.mk_table 169%positive "((5(0 16)1 4611686018427387904)(2 0(1 2)(0 -32))(2 0(1 2)(0 -56))(0 2147450880)((1 10)0)(2 6(1 10)(0 3))(#6 2147450880)((1 2)-8192)(0 8192)(2 6#3(0 3))(#10 2147450880))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xboth_R0 1016%positive "((0(0(856176 856332 1429232 732972 527120 857884 1402040 1403068))(4#1(1 0)))(((1429232((1(0 856896))(2(2 0(1 2)(0 -128)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8#2)(9(0 66))(10(0 66))(11(0 0))(12(0 1497016))(13(1 10))(14(2 6(2 0(1 10)(0 8))(0 3)))(15(1 15))(16(1 16))(17(1 17))(18#3)(19(0 0))(20(2 0(2 6#2(0 3))#4))(21#4)(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-24)8(1 10))(0((1 2)-32)8(0 0))(0((1 2)-120)8(1 21))(0((1 2)-112)8(1 20))(0((1 2)-104)8(1 19))(0((1 2)-96)8(1 18))(0((1 2)-88)8(1 9))(0((1 2)-80)8(1 10))(0((1 2)-72)8(0 856300))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1459384 1463120)(0((0 0)1497016)8#4)(0#5 8(0 0))(0((1 10)8)8(0 0))(0((1 10)16)8(0 0))(6#5(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(1#7(0 3))(7((0 0)2147446784)(0 17592186048512)#5(0 24))(5(1 11)66 66)(9#8(0 8072))(9((1 2)-64)(0 32))(6#8#9)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#11(0 5))(7#8#9#5(0 24))(7#7(0 3)#11(0 5))))(1 1429232)))()())"%pstring.
