(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xboth_T.
Definition dict_Cut_visit_null_root_xboth_R0 : CCD.pt := CCD.mk_table 191%positive "((0 1048576)(5#1 1 4611686018427387904)(2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 2147450880)((1 10)296)((0 0)2147446784)(0 17592186048512)((1 10)0)((1 32)0)((1 2)-13824)(0 13824)((0 0)6946376))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xboth_R0 1266%positive "((0(0(756100 756612 772528 1055420 778032 848468 848584 773284 774952 777096 1402040 1403068))(4#2(1 0)))(((778032((1(0 756400))(2(2 0(1 2)(0 -80)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8#3)(9#4)(10(1 34))(11(1 34))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(2 0(1 10)(0 296)))(19(1 10))(20(2 0(1 10)(0 8)))(21#5)(22(2 0(2 6#3(0 3))#5))(23(2 0(2 6#4(0 3))#5))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1459384 1463120)(0((0 0)1497016)8#5)(3 65536 1466368)(0((1 10)8)8(1 32))(0((1 10)40)8(0 120))(0#6 8(1 37))(5(1 37)0 18446744073709551615)(6#6(0 8))(5(1 10)7094272 140737479966312)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 51))(7#7#8#9(0 408))(5(1 32)7094272 140737479966696)(4(1 32)8)(1((2 6(1 32)(0 3))2147450880)(0 3))(7#7#8#10(0 24))(9#11(0 13744))(9((1 2)-80)(0 8))(6#11#12)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#7#8#11#12)(7#11#12#9(0 408))(7#11#12#10(0 24))(7#9(0 408)#10(0 24))(0((1 10)264)8(1 34))(0((1 10)272)8(1 34))(7#11#12#13(0 18))(7#9(0 408)#13(0 18))(7#10(0 24)#13(0 18))))(1 778032)))()())"%pstring.
