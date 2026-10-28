(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_conv_ec_ls1_csrc_T_u.
Definition dict_Cut_conv_ec_ls1_csrc_R0 : CCD.pt := CCD.mk_table 80%positive "((5(0 10)1 4611686018427387904)((0 0)871920)((0 0)1009736)((1 10)0)((1 2)-256))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_ls1_csrc_R0 909%positive "((0(0(238924 239008 283488 283568 683904 751764 753172))(4#1(1 0)))(((283488((1(0 239024))(2(2 0(1 2)(0 -32)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(0 871920))(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0#2 1(0 0))(0((0 0)871921)1(0 0))(6#2(0 2))(0#3 1(0 0))(0((0 0)1009740)4(0 0))(0((0 0)1009744)4(0 1))(0((0 0)1009752)8(0 1009760))(0((0 0)1009760)8(0 0))(0((0 0)1009768)8(0 684300))(0((0 0)1010024)8(0 235124))(6#3(0 544))(9#4(0 16))(6#4(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)(9#5(0 232))(6#5(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 801400)(7#5(0 256)#4(0 16))(7#4(0 16)((0 0)65536)(0 950272))))(1 283488)))()())"%pstring.
