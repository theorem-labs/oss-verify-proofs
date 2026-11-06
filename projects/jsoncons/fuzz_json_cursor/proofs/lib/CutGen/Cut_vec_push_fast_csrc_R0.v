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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vec_push_fast_csrc_T.
Definition dict_Cut_vec_push_fast_csrc_R0 : CCD.pt := CCD.mk_table 97%positive "((2 0(1 32)(1 33))((1 10)0)(4 0(0 -1)(1 33))(2 0#3(1 34))((1 32)0)((1 2)-8304)(0 8304)((1 11)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_fast_csrc_R0 1037%positive "((0(0(257220 257468 684944 684624 744000 745408))(1 0))(((257468((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 35))(11(1 11))(12#1)(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((1 10)8)8(2 0#1(0 1)))(0(#1 0)1(1 35))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0#2 8(1 32))(0((1 10)16)8(2 0(1 32)(1 34)))(5(1 33)0 1026)(5(1 34)1 140737488355328)(5#4 1 140737488355328)(5(1 35)0 255)(5(1 11)1099511627776 140737488355328)(2#5(1 33)0)(9#5(1 33))(9(#1 1)(2 0#4(0 -1)))(6#5(1 34))(5(1 32)4096 140737488355328)(4(1 32)16)(6#2(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#6(0 8240))(6#6#7)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#6#7#2(0 24))(7#6#7#5(1 34))(7#6#7#8(0 1))(7#2(0 24)#5(1 34))(7#8(0 1)#5(1 34))))(1 257468)))()())"%pstring.
