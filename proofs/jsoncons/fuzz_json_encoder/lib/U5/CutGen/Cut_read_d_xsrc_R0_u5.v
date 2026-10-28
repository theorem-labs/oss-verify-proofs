(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_read_d_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 602%positive "((0(0(291700 292024 240548 291736 292044 778312 779720))(1 0))(((291736((1(1 64))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 65))(9(1 66))(10(1 42))(11(1 43))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 67))(19(1 68))(20(1 69))(21(1 70))(22(1 71))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((5(1 2)1099511627776 140737488355328)(4(1 2)16)(0((1 2)-8)8(1 64))(0((1 2)-16)8(1 65))(0((1 2)-24)8(1 66))(0((1 2)-32)8(1 67))(0((1 2)-40)8(1 68))(0((1 2)-48)8(1 69))(0((1 2)-56)8(1 70))(0((1 2)-64)8(1 71))))(1 291736)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout 522%positive "((0(0(291700 292024 240548 291736 292044 778312 779720))(1 0))(((292044((1(1 64))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 65))(9(1 66))(10(1 42))(11(1 43))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 67))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((5(1 2)1099511627776 140737488355328)(4(1 2)16)(0((1 2)-8)8(1 64))(0((1 2)-16)8(1 65))(0((1 2)-24)8(1 66))(0((1 2)-32)8(1 67))))(1 292044)))()())"%pstring.
