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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strinit_long_xsrc_T.
Definition dict_Cut_strinit_long_xsrc_R0 : CCD.pt := CCD.mk_table 119%positive "((0 1048576)(5#1 1 4611686018427387904)(2 6(1 12)(0 3))(4 0(0 8)#3)(2 0#4(0 8))((1 10)0)((1 2)-8288)(0 8288)((1 11)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_long_xsrc_R0 831%positive "((0(0(237416 237592 704428 764512 763484 764892))(4#2(1 0)))(((704428((1(0 783792))(2(2 0(1 2)(0 -64)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8#5)(9(1 11))(10#5)(11(0 18446744073709551608))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 10))(19(1 19))(20#5)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-64)8(1 12))(0((1 2)-56)8(0 237520))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(9#6(0 24))(6#6(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#7(0 8224))(6#7#8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#7#8#6(0 24))(2#9(1 12)1)(9#9(1 12))(5(1 11)4096 140737488355328)(7#7#8#9(1 12))(7#6(0 24)#9(1 12))(5(1 12)24 67108864)))(1 704428)))()())"%pstring.
