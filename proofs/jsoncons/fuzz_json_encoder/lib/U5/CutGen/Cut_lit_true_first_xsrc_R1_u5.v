(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_lit_true_first_xsrc_T_u5 Cut_lit_true_first_xsrc_R0_u5.
Definition dict_Cut_lit_true_first_xsrc_R1 : CCD.pt := CCD.mk_table 318%positive "((2 0(1 2)(0 -16))(0 898528)((0 0)898544)(0#3 1(0 0))((0 0)898545)(0#5 1(0 2))(5(0 10)1 4611686018427387904)((1 2)-16)(0#8 8(1 8))((1 2)-8)(0#10 8(1 1))((0 0)898528)((0 0)898536)(6#12(0 18))((1 2)-64)(9#15(0 48))(6#15(0 64))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 827984)(5(0 9)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_lit_true_first_xsrc_R1 293%positive "(286988((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)#2(1 9)(0 1)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#4#6#7#9#11(0#12 8(0 0))(0#13 8(0 0))#14#16#17#18#19#20)48(((1 2)-64(0 64))((0 0)898528(0 18)))()(0 9))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_lit_true_first_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_lit_true_first_xsrc_R1 454%positive "((0(0(286916 286972 310088 310168 778312 779720))(4#21(1 0)))(((310168((1(0 287028))(2#1)(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8#2)(9(1 9))(10(0 898544))(11(0 4))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#21(0#13 8(0 4))(0#12 8(0 72237))#4#6#7#9#11#14#16#17#18#19#20))(1 310168)))()())"%pstring.
