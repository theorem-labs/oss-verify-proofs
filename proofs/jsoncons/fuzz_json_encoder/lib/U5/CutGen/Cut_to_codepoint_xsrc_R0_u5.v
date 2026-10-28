(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_to_codepoint_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 855%positive "((0(0(275692 275912 276196 275784 276224 275736 778312 779720))(16 0(0(0(275692 275912 276196 275784 276224 275736 778312 779720))(1 0))))(((276224((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(0 18446744073709466959))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(2 0(1 10)(0 1)))(11(0 0))(12(1 12))(13(1 13))(14(0 1))(15(0 0))(16(0 55296))(17(0 16))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((1 12)0)4(1 32))(0((1 32)84398)1(0 0))(0((1 10)0)1(1 32))(5(1 32)0 127)(5(1 13)0 0)(5(1 10)4096 140737488355326)(5(2 0(4 0(0 -1)(1 10))(1 11))1 140737488355328)(5(1 11)4097 140737488355327)(3 82068 86472)(6((1 12)0)(0 4))(5(1 12)1099511627776 140737488355328)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 12)0)(0 4)((1 10)0)(0 1))))(1 276224)))((8((1 32)84398)1 32 0))())"%pstring.
