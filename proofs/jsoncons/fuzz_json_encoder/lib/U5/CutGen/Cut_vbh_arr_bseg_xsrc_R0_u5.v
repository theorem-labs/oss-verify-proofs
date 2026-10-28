(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_vbh_arr_bseg_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 1328%positive "((0(0(248064 256028 778312 779720))(1 0))(((256028((1(0 248476))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(2 0(1 8)(0 264)))(10(1 8))(11(0 2))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(2 0(4 0(0 32)(1 33))(1 34)))(19(0 1))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((2 0(4 0(0 32)(1 33))(1 34))-26)1(0 1))(0((1 2)23)1(0 0))(0((1 8)296)8(2 0(1 37)(0 2)))(0((1 8)264)8(1 34))(0((1 8)272)8(2 0(4 0(0 32)(1 33))(1 34)))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 33)1 1023)(5(1 34)4096 140737488355328)(4(1 34)16)(7((1 8)0)(0 408)((1 34)0)(1 35))(5(1 35)32 32768)(5(2 0(4 0(0 -32)(1 33))(1 35))0 32768)(5(1 37)0 18446744073709551615)(6((1 8)296)(0 8))(0((1 8)328)8(0 2))(0((1 8)31)1(0 0))(0((1 8)32)1(0 0))(0((2 0(4 0(0 32)(1 33))(1 34))-32)4(0 1))(0((2 0(4 0(0 32)(1 33))(1 34))-28)1(0 0))(0((2 0(4 0(0 32)(1 33))(1 34))-8)8(1 36))(5(1 36)0 18446744073709551615)(9((1 34)0)(2 0(4 0(0 32)(1 33))(0 -26)))(9((2 0(4 0(0 32)(1 33))(1 34))-25)(2 0(2 0(4 0(0 -32)(1 33))(1 35))(0 25)))(6((1 34)0)(1 35))(2((1 34)0)(2 0(4 0(0 32)(1 33))(0 -32))0)(9((1 2)0)(0 23))(6((1 2)0)(0 24))(7((1 2)0)(0 24)((1 8)0)(0 408))(7((1 2)0)(0 24)((1 34)0)(1 35))))(1 256028)))()())"%pstring.
