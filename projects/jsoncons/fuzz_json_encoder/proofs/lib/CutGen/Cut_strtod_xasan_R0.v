(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm4CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import StrtodAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strtod_xasan_T.
Definition dict_Cut_strtod_xasan_R0 : CCDD.pt := CCDD.mk_table 151%positive "((0 1152921504606846976)(5#1 1 4611686018427387904)(0 -272)(2 0(1 2)#3)(0 18446744073709551615)((1 2)-8944)(0 8944)((0 0)7069712)((1 11)0)((1 4)-164))"%pstring.
Definition o0 : CAD.pout := CCDD.dec_pout_t dict_Cut_strtod_xasan_R0 946%positive "((0(0(1383752 1383908 1366320 1335140 1387168 1388196))(4#2(1 0)))(((1366320((1(0 1383840))(2#4)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 11))(9(1 10))(10#4)(11(0 1))(12(0 1))(13(1 10))(14(0 0))(15(0 0))(16(0 0))(17(1 17))(18(0 7069712))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-88)8#5)(0((1 2)-72)8(0 0))(0((1 2)-80)8(0 0))(0((1 2)-256)8#5)(0((1 2)-264)8(1 10))(0((1 2)-184)8(1 10))(0((1 2)-40)8(1 32))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(5(1 2)140735332492016 140737488355328)(4(1 2)16)(3 65536 1449984)(6#6#7)(9#6(0 8680))(9((1 2)-248)(0 64))(9((1 2)-176)(0 88))(9((1 2)-64)(0 24))(0#8 8(1 32))(5(1 10)4096 140737488355328)(5(1 33)1 67108864)(6#9(0 8))(9#9(0 8))(7#9(0 8)#6#7)(5(1 11)32 140737488355320)(7#9(0 8)#8(0 8))(7#9(0 8)#10(0 4))(7#10(0 4)#6#7)(5(1 4)6938576 6938577)))(1 1366320)))()())"%pstring.
