(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_x_fast_xsrc_T_u5.
Definition dict_Cut_str_push_back_x_fast_xsrc_R0 : CCD.pt := CCD.mk_table 219%positive "((436872 437176 778312 779720)(0#1)(2 0(1 33)(1 34))(2 0(1 33)(0 1))(4 0(0 2)(1 32))(2 0#5(0 1))(6 0 0 1#6)(2 9#7(0 1))(5#8 1 1)((1 10)0)((1 10)16)(4 0(0 -1)(1 33))(2 0#5#12)(2 0#13(0 -2))((1 34)0)((1 2)-8304)(0 8304))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_fast_xsrc_R0 936%positive "((0#2(16 0(0#2(1 0))))(((437176((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10#3)(11#4)(12#7)(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0(#3 1)1(0 0))(0(#3 0)1(1 11))(0((1 10)8)8#4)#9(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0#10 8#6)(0#11 8(1 34))(5(1 32)12 70368744177664)(5(1 11)0 255)(5(1 33)0 140737488355328)(5#14 0 140737488355328)(2#15(1 33)0)(9#15(1 33))(9(#3 2)#14)(6#15#5)(5(1 34)4096 140737488355328)(4(1 34)16)(9#10(0 8))(9#11(0 8))(6#10(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(9#16(0 8240))(6#16#17)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#16#17#10(0 24))(7#16#17#15#5)(7#10(0 24)#15#5)))(1 437176)))((0#9))())"%pstring.
