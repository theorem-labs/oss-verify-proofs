(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_atexit_xsrc_T.
Definition dict_Cut_atexit_xsrc_R0 : CCD.pt := CCD.mk_table 27%positive "(((1 2)-48)((0 0)1021544))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_atexit_xsrc_R0 790%positive "((0(0(695784 695980 763484 764892))(1 0))(((695980((1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(10(0 0))(11(0 0))(12(0 8))(13(0 0))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0((0 0)1021552)4(0 2))(0((0 0)1021840)8(1 43))(0((0 0)1021584)8(1 42))(0#1 8(1 52))(0((1 2)-40)8(1 51))(0((1 2)-32)8(1 50))(0((1 2)-24)8(1 41))(0((1 2)-16)8(1 40))(0((1 2)-8)8(1 33))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(6#1(0 48))(0((0 0)1022131)1(0 0))(0#2 1(0 0))(0((0 0)1021548)4(0 0))(0((0 0)1021560)8(0 1021568))(0((0 0)1021568)8(0 0))(0((0 0)1021576)8(0 696180))(0((0 0)1021832)8(0 236824))(6#2(0 544))))(1 695980)))()())"%pstring.
