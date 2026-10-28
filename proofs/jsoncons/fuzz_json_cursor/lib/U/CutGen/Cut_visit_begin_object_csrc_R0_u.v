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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_visit_begin_object_csrc_T_u.
Definition dict_Cut_visit_begin_object_csrc_R0 : CCD.pt := CCD.mk_table 66%positive "((269616 269704 751764 753172)(0#1)((1 42)8)((1 2)-24)((1 2)-64))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_begin_object_csrc_R0 885%positive "((0#2(0(2)(0#2(0(1)(0#2(1 0))))))(((269704((1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 81))(6(1 82))(7(1 83))(8(1 40))(9(1 41))(10(0 1))(11(1 85))(12(1 86))(13(1 87))(14(1 88))(15(1 89))(16(1 90))(17(1 91))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 92))(29(1 93))(30(1 94))(31(1 95)))()((0((1 42)17)1(7 0 0 1 1))(0((1 42)18)1(7 0 0 2 1))(0((1 42)19)1(7 0 0 3 1))(0((1 42)20)1(7 0 0 4 1))(0((1 42)21)1(7 0 0 5 1))(0((1 42)22)1(7 0 0 6 1))(0((1 42)23)1(7 0 0 7 1))(0((1 42)24)8(0 0))(0((1 42)32)8(0 0))(0((1 42)40)8(0 0))(0((1 42)16)1(1 43))(0#3 8(0 256))(1((1 2)-48)(0 24))(0#4 8(1 41))(0((1 2)-16)8(1 40))(0((1 2)-8)8(1 33))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 42)4096 140737488355328)(9((1 42)48)(0 0))(6#3(0 40))(9#5(0 16))(9#4(0 0))(6#5(0 64))(7#5(0 64)((1 42)0)(0 48))(2((1 2)-56)(0 8)0)))(1 269704)))()())"%pstring.
