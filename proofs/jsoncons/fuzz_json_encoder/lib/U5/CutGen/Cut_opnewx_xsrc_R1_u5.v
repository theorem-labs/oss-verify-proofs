(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5 MallocXSum_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_opnewx_xsrc_T_u5 Cut_opnewx_xsrc_R0_u5.
Definition dict_Cut_opnewx_xsrc_R1 : CCD.pt := CCD.mk_table 367%positive "((5(1 32)4096 140737488355328)(4(1 32)16)((1 32)0)(9#3(1 10))(6#3(1 10))((0 0)65536)(0 974848)(7#3(1 10)#6#7)((1 2)-8240)(0 8240)(7#3(1 10)#9#10)(0 1048576)(5#12 1 4611686018427387904)((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))(5(1 10)1 281474976710655)(0 8224)(9#9#19)(6#9#10)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(#1#2#4#5#8#11#13#15#17#18#20#21#22#23))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_opnewx_xsrc_R1 261%positive "(798620((1 0)(1 33)(2 0(1 2)(0 -16))(1 3)(1 4)(1 34)(1 35)(1 36)(1 10)(1 9)(1 32)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 45)(1 46)(1 47)(1 48))#24 49(((1 2)-8240#10)((1 32)0(1 10)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_opnewx_xsrc_R1 17%positive "(((1 32)(1 10)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_opnewx_xsrc_R1 378%positive "((0(0(798592 798660 719096 778312 779720))(1 0))(((798660((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 34))(6(1 35))(7(1 36))(8(1 8))(9(1 9))(10(1 32))(11(1 38))(12(1 39))(13(1 40))(14(1 41))(15(1 42))(16(1 43))(17(1 44))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 45))(29(1 46))(30(1 47))(31(1 48)))()#24)(1 798660)))()())"%pstring.
