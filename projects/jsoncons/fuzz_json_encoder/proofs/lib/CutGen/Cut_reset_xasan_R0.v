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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_reset_xasan_T.
Definition dict_Cut_reset_xasan_R0 : CCD.pt := CCD.mk_table 287%positive "((5(0 40)1 4611686018427387904)(2 0(1 10)(0 248))(0 2147450880)((1 10)0)(2 6(1 10)(0 3))(#5 2147450880)(2 0(1 10)(0 211))(2 6#7(0 3))(#8 2147450880)(2 0(1 10)(0 212))(2 6#10(0 3))(#11 2147450880)((1 2)-8288)(0 8288)((1 32)0)(2 6(1 32)(0 3))(#16 2147450880)(2 0(1 34)(0 7))(2 6#18(0 3)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xasan_R0 1195%positive "((0(0(844500 844784 730684 841320 526044 1387168 1388196))(4#1(1 0)))(((730684((1(0 844600))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9#2)(10#2)(11(1 33))(12(1 32))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 10)256)8(1 32))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1444792 1448528)(0((0 0)1482488)8#3)(0((1 10)248)8(1 32))(0((1 10)264)8(2 0(1 32)(1 34)))(9((1 10)144)(0 4))(9((1 10)160)(0 8))(9((1 10)168)(0 16))(9((1 10)208)(0 1))(9((1 10)211)(0 2))(6#4(0 272))(5(1 10)7077888 140737488351232)(4(1 10)8)(1#6(0 34))(1#9(0 1))(1#12(0 1))(7((0 0)2147446784)(0 17592186048512)#4(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 4096)(5(1 34)1 4096)(5(2 0(4 0(0 -1)(1 33))(1 34))0 4096)(9#13(0 8256))(6#13#14)(5(1 2)140735332491360 140737488355328)(4(1 2)16)(7#13#14#4(0 272))(7#13#14#15(1 34))(7#4(0 272)#15(1 34))(7#6(0 34)#17#19)(7#9(0 1)#17#19)(7#12(0 1)#17#19)(7#6(0 34)#4(0 272))(7#9(0 1)#4(0 272))(7#12(0 1)#4(0 272))(7#4(0 272)#17#19)))(1 730684)))()())"%pstring.
