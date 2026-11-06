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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strapp_fast_xboth_T.
Definition dict_Cut_strapp_fast_xboth_R0 : CCD.pt := CCD.mk_table 369%positive "((1055420 1055668 527112 1402040 1403068)(0#1)(5(0 100)1 4611686018427387904)(2 0(1 33)(1 34))(4 0(0 -1)(1 12))(4 0(0 2)(1 32))(4 0(0 -1)(1 33))(2 0#6#7)(2 0#5#8)(2 0#9(0 -1))(2 0#8(0 -1))(5(1 12)1 67108863)(5(1 33)0 67108862)(5#8 2 140737488355328)(5#11 1 140737488355327)(2 0#6(0 1))(6 0 0 1#16)(2 9#17(0 1))(5#18 1 1)((1 10)0)((1 34)0)((1 2)-4368)(0 4368)((1 11)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_strapp_fast_xboth_R0 1352%positive "((0#2(16 0(0#2(16 1(16 2(16 3(16 4(3(11 12 2 67108863(16 5(16 6(2(1 40)0(1 0)(1 0)))))(16 7(0#2(4#3(1 0))))))))))))(((527112((1(0 1055600))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 12))(10#4)(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 11))(18(1 33))(19(1 34))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#3(5#10 0 140737488355326)(5(2 4#11(1 12))0 0)#12#13#14#15#19(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1433600 1466368)(0((0 0)1497016)8(0 2147450880))(0#20 8#16)(0((1 10)8)8(1 33))(0((1 10)16)8(1 34))(5(1 32)12 70368744177664)(5(1 33)0 67108864)(2#21(1 33)0)(0(#4 0)1(0 0))(9#21#6)(6#21#6)(5(1 34)4096 140737488355328)(4(1 34)16)(5#11 0 140737488355328)(9#20(0 24))(6#20(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)(9#22(0 4328))(6#22#23)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#22#23#20(0 24))(7#22#23#21#6)(7#20(0 24)#21#6)(5(1 12)1 67108864)(5(2 0(1 12)(1 33))1 67108863)(2#24(1 12)1)(9#24(1 12))(5(1 11)4096 140737488355328)(5(2 0(1 11)(1 12))4096 140737488355328)(7#22#23#24(1 12))(7#20(0 24)#24(1 12))(7#21#6#24(1 12))(5#10 0 140737488355328)))(1 527112)))((0#19)(0#15)(0#14)(0#13)(0#12)(1#11(1 12)1)(3((0 -1)(6 -1)))(1(1 12)#11 0))())"%pstring.
