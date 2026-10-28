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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_lit_null_first_xsrc_T_u5.
Definition dict_Cut_lit_null_first_xsrc_R0 : CCD.pt := CCD.mk_table 56%positive "((5(0 10)1 4611686018427387904)((0 0)898504)((1 2)-64))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_lit_null_first_xsrc_R0 629%positive "((0(0(258088 258144 310088 310168 778312 779720))(4#1(1 0)))(((310088((1(0 258160))(2(2 0(1 2)(0 -16)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 898504))(9(1 9))(10(0 898520))(11(0 897088))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((0 0)898520)1(0 0))(0((0 0)898521)1(0 0))(0#2 8(0 0))(0((0 0)898512)8(0 0))(6#2(0 18))(9#3(0 48))(6#3(0 64))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 827984)))(1 310088)))()())"%pstring.
