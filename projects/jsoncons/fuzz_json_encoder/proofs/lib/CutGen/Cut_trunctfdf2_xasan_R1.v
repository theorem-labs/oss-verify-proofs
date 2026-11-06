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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_trunctfdf2_xasan_T Cut_trunctfdf2_xasan_R0.
Definition dict_Cut_trunctfdf2_xasan_R1 : CCDD.pt := CCDD.mk_table 211%positive "((0 4503599627370496)(4 0#1(1 37))(0 -9223372036854775808)(2 6(1 36)(0 63))(4 0#3#4)(2 8#2#5)(2 8#6(1 35))(0 1099511620416)(5#8 1 4611686018427387904)(5(1 2)140735332483072 140737488355328)(4(1 2)16)(#9#10#11))"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_trunctfdf2_xasan_R1 212%positive "(1335352((1 0)(1 1)(1 2)(1 3)(1 4)(1 32)(1 33)(1 34)(1 8)(1 9)#7#6#2(1 38)(1 39)(1 40)(1 41)(1 42)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 43)(1 44)(1 45)(1 46))#12 47()()(0 1099511620415))"%pstring.
Definition BL7 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_trunctfdf2_xasan_R1 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints3.
Definition o7 : CAD.pout := CCDD.dec_pout_t dict_Cut_trunctfdf2_xasan_R1 326%positive "((1 0)(((1335352((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 32))(6(1 33))(7(1 34))(8(1 8))(9(1 9))(10#7)(11#6)(12#2)(13(1 38))(14(1 39))(15(1 40))(16(1 41))(17(1 42))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 43))(29(1 44))(30(1 45))(31(1 46)))()#12)(1 1335352)))()())"%pstring.
