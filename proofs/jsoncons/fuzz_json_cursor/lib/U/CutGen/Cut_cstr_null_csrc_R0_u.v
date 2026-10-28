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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_cstr_null_csrc_T_u.
Definition o0 : CA.pout := CCD.dec_pout 896%positive "((0(0(283280 283476 751764 753172))(0(1)(0(0(283280 283476 751764 753172))(1 0))))(((283476((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10(2 0(4 0(0 -1)(1 10))(0 -2)))(11(1 37))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()((0((1 10)5)1(0 0))(0((1 10)1)1(0 110))(0((1 10)2)1(0 117))(0((1 10)3)1(0 108))(0((1 10)4)1(0 108))(0((1 10)0)1(0 8))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(9((1 10)6)(0 18))(6((1 10)0)(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9((1 2)-8304)(0 8256))(6((1 2)-8304)(0 8304))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-8304)(0 8304)((1 10)0)(0 24))(3 65536 801400)))(1 283476)))()())"%pstring.
