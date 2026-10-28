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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_write_bignum_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 1190%positive "((0(0(259716 260608 436288 778312 779720))(4(5(0 1048576)1 4611686018427387904)(1 0)))(((436288((1(0 259796))(2(2 0(1 2)(0 -176)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(1 32))(11(1 33))(12(1 34))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 1048576)1 4611686018427387904)(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 10)8)8(1 32))(0((1 10)27)1(0 0))(0((1 10)296)8(1 35))(0((1 11)0)8(1 33))(0((1 11)8)8(1 34))(5(1 34)0 140737488355328)(5(1 35)0 18446744073709551615)(6((1 10)296)(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 11)1099511627776 140737488355328)(4(1 11)8)(9((1 2)-8672)(0 8496))(9((1 2)-176)(0 144))(6((1 2)-8672)(0 8672))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-8672)(0 8672)((1 10)0)(0 408))(7((1 2)-8672)(0 8672)((1 32)0)(0 24))(7((1 10)0)(0 408)((1 32)0)(0 24))(7((1 2)-8672)(0 8672)((1 11)0)(0 16))(7((1 10)0)(0 408)((1 11)0)(0 16))(7((1 32)0)(0 24)((1 11)0)(0 16))))(1 436288)))()())"%pstring.
