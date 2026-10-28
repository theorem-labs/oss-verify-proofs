(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_iosbinit_csrc_T_u.
Definition dict_Cut_iosbinit_csrc_R0 : CCD.pt := CCD.mk_table 56%positive "((431220 581452 751764 753172)(0#1)((1 42)8)((1 2)-16))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_iosbinit_csrc_R0 745%positive "((0#2(0(2)(0#2(1 0))))(((581452((1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 65))(6(1 66))(7(1 67))(8(1 40))(9(1 41))(10(2 0(1 42)(0 48)))(11(1 69))(12(1 70))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()((1((1 42)56)(0 80))(0((1 42)32)4(0 0))(0((1 42)24)8(0 0))(0((1 42)16)8(0 6))(0#3 4(0 4098))(0((1 42)40)8(1 43))(0((1 42)36)4(0 0))(0#4 8(1 40))(0((1 2)-8)8(1 33))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(6#4(0 16))(5(1 42)1099511627776 140737488355328)(5(1 43)1 140737488355328)(9((1 42)12)(0 4))(9((1 42)48)(0 8))(9((1 42)136)(0 0))(6#3(0 128))(7#4(0 16)((1 42)0)(0 152))))(1 581452)))()())"%pstring.
