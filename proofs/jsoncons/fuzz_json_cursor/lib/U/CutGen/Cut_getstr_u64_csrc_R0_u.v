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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_getstr_u64_csrc_T_u.
Definition o0 : CA.pout := CCD.dec_pout 973%positive "((0(0(274124 274316 276664 283280 274864 275196 275744 238924 274816 274420 274584 274672 274688 274732 751764 753172))(1 0))(((274864((1(0 274316))(2(2 0(1 2)(0 -48)))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 42))(9(1 43))(10(1 65))(11(1 42))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0((1 42)16)8(0 0))(0((1 42)8)8(0 0))(0((1 42)0)8(0 0))(0((1 2)-25)1(1 44))(0((1 2)-24)8(1 41))(0((1 2)-16)8(1 40))(0((1 2)-8)8(1 33))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(9((1 2)-48)(0 23))(6((1 2)-48)(0 48))(5(1 42)1099511627776 140737488355328)(6((1 42)0)(0 24))(5(1 43)4096 140737488355328)(0((1 43)0)8(0 32))(9((1 43)8)(0 16))(0((1 43)24)8(1 65))(0((1 43)32)8(1 66))(3 65536 801400)(7((1 2)-48)(0 48)((1 42)0)(0 24))(7((1 2)-48)(0 48)((1 43)0)(0 40))(7((1 43)0)(0 40)((1 42)0)(0 24))))(1 274864)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout 565%positive "((0(0(274124 274316 276664 283280 274864 275196 275744 238924 274816 274420 274584 274672 274688 274732 751764 753172))(1 0))(((274732((1(1 64))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 65))(9(1 66))(10(1 42))(11(1 43))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((5(1 2)1099511627776 140737488355328)(4(1 2)16)(0((1 2)-8)8(1 64))(0((1 2)-16)8(1 65))(0((1 2)-24)8(1 66))))(1 274732)))()())"%pstring.
