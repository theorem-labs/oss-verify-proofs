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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_harness_al_xboth_T.
Definition dict_Cut_harness_al_xboth_R0 : CCD.pt := CCD.mk_table 81%positive "((5(0 100)1 4611686018427387904)(0 -160)(2 0(1 2)#2)(0 2147450880)((1 2)-18432))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_harness_al_xboth_R0 984%positive "((0(0(724512 726616 421720 542624 542336 727212 727572 729448 1073140 730872 731512 733456 1227348 1046256 534160 422244 528300 728244 731020 1402040 1403068))(4#1(1 0)))(((421720((1(0 724628))(2#3)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#3)(10(0 1728))(11(0 1497016))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18#4)(19(1 19))(20(1 20))(21(1 21))(22(1 11))(23(1 23))(24(1 10))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-104)8(1 27))(0((1 2)-96)8(1 26))(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-160)8(0 0))(3 1433600 1466368)(0((0 0)1497016)8#4)(0((0 0)1497024)4(0 1))(4(1 2)32)(9#5(0 18272))(9((1 2)-152)(0 48))(6#5(0 18432))(5(1 2)140735332501504 140737488355328)(5(1 11)23 67108863)(5(1 10)4096 140737479966719)))(1 421720)))()())"%pstring.
