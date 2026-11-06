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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_sdtor_xasan_T.
Definition dict_Cut_sdtor_xasan_R0 : CCD.pt := CCD.mk_table 140%positive "((5(0 12)1 4611686018427387904)(0 16384)(0 2147450880)(0 6934032)((1 10)0)((0 0)2147446784)(0 17592186048512)((1 2)-4224)(0 4224)((1 32)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xasan_R0 1003%positive "((0(0(730848 1031544 531904 1387168 1388196))(4#1(1 0)))(((1031544((1(0 730944))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 9))(10(1 32))(11#2)(12(0 0))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19#3)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1417216 1449984)(0((0 0)1482488)8#3)(0((1 10)32)8#4)(0((1 10)264)8(1 32))(0((1 10)272)8#2)(0((1 10)136)8#4)(0((1 10)144)8(0 0))(0((1 10)152)8(0 0))(0((1 10)160)8(0 0))(0((1 10)176)8(0 0))(0((1 10)200)8(0 0))(9#5(0 32))(9((1 10)88)(0 8))(6#5(0 592))(5(1 10)7077888 140737488351232)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 74))(7#6#7#5(0 592))(5(1 32)4096 140737479966720)(4(1 32)16)(9#8(0 4184))(6#8#9)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(7#8#9#5(0 592))(7#8#9#10#2)(7#5(0 592)#10#2)(7#6#7#10#2)))(1 1031544)))()())"%pstring.
