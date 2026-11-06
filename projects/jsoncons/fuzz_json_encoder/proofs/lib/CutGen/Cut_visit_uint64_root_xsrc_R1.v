(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums EncSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_uint64_root_xsrc_T Cut_visit_uint64_root_xsrc_R0.
Definition dict_Cut_visit_uint64_root_xsrc_R1 : CCD.pt := CCD.mk_table 565%positive "((5(1 48)0 1125899906842624)(0 1048576)(5#2 1 4611686018427387904)((1 2)-24)(0#4 8(1 9))((1 2)-16)(0#6 8(1 8))((1 2)-8)(0#8 8(1 1))((1 10)8)(0#10 8(1 32))((1 10)296)(5(1 37)0 18446744073709551615)(6#12(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#19#20)((1 2)-32)(9#22(0 8))(0 10624)(6#19#24)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#19#24#28(0 408))((1 32)0)(7#19#24#30(0 24))(7#28(0 408)#30(0 24))(3 65536 813152)((1 10)264)(0#34 8(1 34))((1 10)272)(0#36 8(1 34)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_uint64_root_xsrc_R1 340%positive "(242320((1 0)(1 49)(2 0(1 2)(0 -32))(1 3)(1 4)(1 50)(1 51)(1 52)(1 10)(1 11)(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#1#3#5#7#9#11(0#12 8(1 37))#13#14#15#16#17#18#21#23#25#26#27#29#31#32#33#35#37)65(((1 2)-10624#24)((1 10)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_uint64_root_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_uint64_root_xsrc_R1 514%positive "((0(0(242212 242376 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(1 0))(((242376((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 9))(10(0 1))(11(1 34))(12(1 37))(13(1 34))(14(1 57))(15(1 58))(16(1 59))(17(1 60))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()((0#12 8(2 0(1 37)(1 48)))#1#3#5#7#9#11#13#14#15#16#17#18#21#23#25#26#27#29#31#32#33#35#37))(1 242376)))()())"%pstring.
