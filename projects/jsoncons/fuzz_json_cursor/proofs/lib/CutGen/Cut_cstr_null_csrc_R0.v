(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cstr_null_csrc_T.
Definition dict_Cut_cstr_null_csrc_R0 : CCD.pt := CCD.mk_table 66%positive "((275692 275876 744000 745408)(0#1)((1 10)0)((1 2)-8304)(0 8304))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_null_csrc_R0 762%positive "((0#2(0(1)(0#2(1 0))))(((275876((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10(2 0(1 10)(0 1)))(11(1 37))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()((0((1 10)5)1(0 0))(0((1 10)1)1(0 110))(0((1 10)2)1(0 117))(0((1 10)3)1(0 108))(0((1 10)4)1(0 108))(0#3 1(0 8))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(9((1 10)6)(0 18))(6#3(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#4(0 8256))(6#4#5)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#4#5#3(0 24))(3 65536 793640)))(1 275876)))()())"%pstring.
