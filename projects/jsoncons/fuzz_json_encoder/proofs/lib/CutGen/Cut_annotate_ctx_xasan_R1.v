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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_annotate_ctx_xasan_T Cut_annotate_ctx_xasan_R0.
Definition dict_Cut_annotate_ctx_xasan_R1 : CCD.pt := CCD.mk_table 532%positive "((5(0 8)1 4611686018427387904)((1 2)-16)(0#2 8(1 8))((1 2)-8)(0#4 8(1 1))(3 1444792 1448528)((0 0)1482488)(0 2147450880)(0#7 8#8)(5(1 10)1048576 140737488355304)(4(1 10)8)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#12#13#14(0 24))(5(1 32)16 140737488355312)(4(1 32)16)(5(1 34)1 32768)(4 0(0 -1)(1 33))(2 0#19(1 34))(5#20 0 32768)(5(1 33)0 32768)(5(1 11)0 1024)((1 2)-4112)(0 4096)(9#24#25)(0 4112)(6#24#27)(5(1 2)140735332487184 140737488355328)(4(1 2)16)(7#24#27#14(0 24))(#1#3#5#6#9#10#11#15#16#17#18#21#22#23#26#28#29#30#31))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_annotate_ctx_xasan_R1 239%positive "(763412((1 0)(1 40)(2 0(1 2)(0 -16))(1 3)(1 4)(1 41)(1 42)(1 43)(1 8)(1 9)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))#32 56(((1 2)-4112#27))()(0 7))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_annotate_ctx_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_ctx_xasan_R1 380%positive "((0(0(763296 763424 540712 1387168 1388196))(1 0))(((763424((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 8))(9(1 9))(10(1 44))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()#32)(1 763424)))()())"%pstring.
