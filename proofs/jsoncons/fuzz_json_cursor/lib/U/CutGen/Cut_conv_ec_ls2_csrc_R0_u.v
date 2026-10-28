(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_conv_ec_ls2_csrc_T_u.
Definition dict_Cut_conv_ec_ls2_csrc_R0 : CCD.pt := CCD.mk_table 23%positive "(((1 10)0)((1 2)-256))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_ls2_csrc_R0 683%positive "((0(0(238924 239008 751764 753172))(1 0))(((239008((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 10))(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((1 10)8)8(0 805536))(0#1 8(1 11))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((0 0)871920)1(0 1))(6#1(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)(9#2(0 232))(6#2(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 801400)(7#2(0 256)#1(0 16))(7#1(0 16)((0 0)65536)(0 950272))))(1 239008)))()())"%pstring.
