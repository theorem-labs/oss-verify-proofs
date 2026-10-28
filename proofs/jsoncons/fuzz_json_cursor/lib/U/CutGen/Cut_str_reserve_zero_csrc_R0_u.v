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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_str_reserve_zero_csrc_T_u.
Definition dict_Cut_str_reserve_zero_csrc_R0 : CCD.pt := CCD.mk_table 70%positive "((0 1048576)(5#1 1 4611686018427387904)((1 10)0)((1 2)-8320)(0 8320))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_reserve_zero_csrc_R0 815%positive "((0(0(409144 409636 692548 692228 751764 753172))(4#2(1 0)))(((692548((1(0 772072))(2(2 0(1 2)(0 -96)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 264))(9(0 263))(10(0 264))(11(0 0))(12(0 0))(13(0 22))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(0 264))(20(0 0))(21(0 22))(22(0 0))(23(0 18446744073709551615))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-96)8(1 10))(0((1 2)-88)8(0 409404))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(1#3(0 24))(6#3(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#4(0 8224))(9((1 2)-80)(0 8))(6#4#5)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#4#5#3(0 24))))(1 692548)))()())"%pstring.
