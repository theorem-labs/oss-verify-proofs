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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_lit_false_first_xboth_T Cut_lit_false_first_xboth_R0 Cut_lit_false_first_xboth_R1.
Definition dict_Cut_lit_false_first_xboth_R2 : CCD.pt := CCD.mk_table 349%positive "(((0 0)6946440)(0#1 1(0 1))((0 0)6946441)(0#3 1(0 1))(5(0 9)1 4611686018427387904)((0 0)6946432)(0#6 8(0 5))((0 0)6946424)(0 165472)(0#8 8#9)(5(0 10)1 4611686018427387904)((1 2)-16)(0#12 8(1 8))((1 2)-8)(0#14 8(1 1))(6#8(0 18))((1 2)-80)(9#17(0 64))(6#17(0 80))(5(1 2)140735332483152 140737488355328)(4(1 2)16)(#2#4#5#7#10#11#13#15#16#18#19#20#21))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_lit_false_first_xboth_R2 266%positive "(848696((1 0)(1 48)(2 0(1 2)(0 -16))(1 3)(1 4)(1 49)(1 50)(1 51)(0 6946424)(1 9)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))#22 64(((1 2)-80(0 80))((0 0)6946424(0 18)))()(0 8))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_lit_false_first_xboth_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_lit_false_first_xboth_R2 382%positive "((0(0(848584 848640 929220 929300 1402040 1403068))(1 0))(((848640((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10#9)(11(0 5))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()#22)(1 848640)))()())"%pstring.
