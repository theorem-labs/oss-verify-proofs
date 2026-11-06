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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_opnew_xasan_T Cut_opnew_xasan_R0.
Definition dict_Cut_opnew_xasan_R1 : CCD.pt := CCD.mk_table 358%positive "((5(1 36)4096 140737479966719)(4(1 36)16)((1 36)0)(9#3(1 10))(6#3(1 10))((0 0)2147446784)(0 17592186048512)(7#6#7#3(1 10))(0 1048576)(5#9 1 4611686018427387904)((1 2)-16)(0#11 8(1 8))((1 2)-8)(0#13 8(1 1))(5(1 10)1 134217728)((1 2)-4112)(0 4096)(9#16#17)(0 4112)(6#16#19)(5(1 2)140735332487184 140737488355328)(4(1 2)16)(#1#2#4#5#8#10#12#14#15#18#20#21#22))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_opnew_xasan_R1 247%positive "(1414388((1 0)(1 32)(2 0(1 2)(0 -16))(1 3)(1 4)(1 33)(1 34)(1 35)(1 10)(1 9)(1 36)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))#23 48(((1 2)-4112#19))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_opnew_xasan_R1 17%positive "(((1 36)(1 10)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_opnew_xasan_R1 384%positive "((0(0(1414360 1414428 531908 1387168 1388196))(1 0))(((1414428((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10(1 36))(11(1 37))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()#23)(1 1414428)))()())"%pstring.
