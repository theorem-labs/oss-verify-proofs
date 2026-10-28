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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_strinit_sso_csrc_T_u.
Definition o0 : CA.pout := CCD.dec_pout 1116%positive "((0(0(235792 235980 692548 752792 751764 753172))(16 0(4(5(0 1048576)1 4611686018427387904)(1 0))))(((752792((1(0 235936))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 12))(9(1 11))(10(2 0(1 10)(0 1)))(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 10))(19(2 0(1 10)(0 1)))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 1048576)1 4611686018427387904)(5(2 0(4 0(0 -1)(1 12))(0 23))0 4611686018427387904)(0((1 10)0)1(4 0(0 2)(1 12)))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(9((1 10)1)(0 23))(6((1 10)0)(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9((1 2)-8288)(0 8240))(6((1 2)-8288)(0 8288))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-8288)(0 8288)((1 10)0)(0 24))(2((1 11)0)(1 12)1)(9((1 11)0)(1 12))(5(1 11)4096 140737488355328)(7((1 2)-8288)(0 8288)((1 11)0)(1 12))(7((1 10)0)(0 24)((1 11)0)(1 12))(5(1 12)1 22)))(1 752792)))((0(5(2 0(4 0(0 -1)(1 12))(0 23))0 4611686018427387904)))())"%pstring.
