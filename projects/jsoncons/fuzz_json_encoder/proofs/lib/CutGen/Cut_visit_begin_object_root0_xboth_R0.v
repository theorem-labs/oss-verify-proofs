(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB EncSums2XB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_begin_object_root0_xboth_T.
Definition dict_Cut_visit_begin_object_root0_xboth_R0 : CCD.pt := CCD.mk_table 237%positive "((0 1048576)(5#1 1 4611686018427387904)(0 -112)(2 0(1 2)#3)(2 0(1 10)(0 296))(2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 2147450880)((1 10)400)((1 10)288)((1 10)296)((0 0)2147446784)(0 17592186048512)((1 10)0)((1 32)0)((1 2)-13824)(0 13824))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_begin_object_root0_xboth_R0 1682%positive "((0(0(747548 749212 1055420 770716 846316 1402040 1403068))(4#2(1 0)))(((846316((1(0 748888))(2#4)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9#5)(10#6)(11(2 0(1 2)(0 -96)))(12(2 0(1 2)(0 -89)))(13(2 0(1 2)(0 -97)))(14#5)(15#4)(16(1 16))(17(1 17))(18(2 0(1 10)(0 8)))(19(2 0(1 10)(0 344)))(20#7)(21#6)(22#8)(23(2 0(2 6#7(0 3))#8))(24(0 0))(25(0 0))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-112)8(2 0(1 37)(0 1)))(0((1 2)-89)1(0 0))(0((1 2)-97)1(0 0))(0((1 2)-96)4(0 0))(0#9 4(0 1))(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1459384 1463120)(0((0 0)1497016)8#8)(0((1 10)8)8(1 32))(0((1 10)16)8(0 1435024))(3 1435000 1435008)(1((0 0)2147630255)(0 1))(0((1 10)28)1(0 0))(0((1 10)29)1(0 0))(0((1 10)30)1(0 0))(0((1 10)31)1(0 0))(0((1 10)32)1(0 0))(0((1 10)36)1(0 4))(0((1 10)40)8(0 120))(0((1 10)240)4(0 1024))(0((1 10)264)8(0 0))(0((1 10)272)8(0 0))(0((1 10)280)8(0 0))(0#10 4(4 0(0 4)(1 33)))(6#10(0 4))(0#11 8(1 37))(5(1 37)0 18446744073709551615)(6#11(0 8))(0((1 10)320)8(0 150396))(0((1 10)328)8(0 2))(0((1 10)336)8(0 150408))(0((1 10)344)8(0 1))(6#9(0 4))(5(1 10)7094272 140737479966312)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 51))(7#12#13#14(0 408))(5(1 32)7094272 140737479966696)(4(1 32)8)(1((2 6(1 32)(0 3))2147450880)(0 3))(7#12#13#15(0 24))(7#16#17#14(0 408))(7#16#17#15(0 24))(7#14(0 408)#15(0 24))(9#16(0 13712))(9((1 2)-104)(0 7))(9((1 2)-92)(0 3))(6#16#17)(5(1 2)140735332496896 140737488355328)(4(1 2)16)(7#12#13#16#17)(5(1 33)0 0)))(1 846316)))()())"%pstring.
