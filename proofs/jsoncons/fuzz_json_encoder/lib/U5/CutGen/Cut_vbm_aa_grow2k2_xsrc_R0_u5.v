(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_vbm_aa_grow2k2_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 1603%positive "((0(0(248476 248696 798592 778312 718776 778312 779720))(4(5(0 1048576)1 4611686018427387904)(1 0)))(((798592((1(0 286088))(2(2 0(1 2)(0 -144)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 8))(9(0 4))(10(0 256))(11(0 8))(12(0 4))(13(2 0(1 8)(0 264)))(14(0 0))(15(1 2))(16(1 16))(17(1 17))(18(2 0(1 8)(0 296)))(19(2 0(1 2)(0 15)))(20(2 0(1 2)(0 23)))(21(2 0(1 2)(0 16)))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 1048576)1 4611686018427387904)(0((1 2)-144)8(2 0(1 2)(0 -96)))(0((1 2)-136)8(0 285604))(0((1 2)-64)8(2 0(1 8)(0 264)))(0((1 2)-72)8(0 0))(0((1 2)-120)8(1 2))(0((1 2)-112)8(2 0(1 8)(0 264)))(0((1 2)-104)8(0 285336))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(0 1))(0((1 2)-32)8(2 0(1 32)(0 128)))(0((1 2)-24)8(2 0(1 8)(0 264)))(0((1 2)-16)8(1 8))(0((1 2)-8)8(0 248568))(0((1 2)0)8(2 0(1 35)(0 1)))(0((1 2)15)1(0 0))(0((1 2)16)4(0 1))(0((1 8)264)8(1 32))(0((1 8)272)8(2 0(1 32)(0 128)))(0((1 8)280)8(2 0(1 32)(0 128)))(6((1 8)264)(0 24))(0((1 8)296)8(1 35))(5(1 35)0 18446744073709551615)(0((1 8)376)8(0 1))(0((1 8)28)1(0 0))(0((1 8)30)1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(9((1 2)-8384)(0 8240))(9((1 2)-128)(0 8))(9((1 2)-96)(0 24))(6((1 2)-8384)(0 8384))(9((1 2)8)(0 7))(9((1 2)20)(0 3))(0((1 2)23)1(0 0))(6((1 2)0)(0 24))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-8384)(0 8408)((1 8)0)(0 408))(9((1 32)0)(0 128))(6((1 32)0)(0 128))(5(1 32)4096 140737488355328)(4(1 32)16)(7((1 2)-8384)(0 8408)((1 32)0)(0 128))(7((1 8)0)(0 408)((1 32)0)(0 128))(2((1 32)0)(0 128)0)))(1 798592)))()())"%pstring.
