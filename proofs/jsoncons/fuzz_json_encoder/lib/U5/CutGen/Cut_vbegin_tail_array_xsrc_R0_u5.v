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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_vbegin_tail_array_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 1175%positive "((0(0(248696 248820 436288 778312 779720))(4(5(0 1048576)1 4611686018427387904)(1 0)))(((436288((1(0 248776))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 32))(11(0 83693))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 1048576)1 4611686018427387904)(0((1 8)288)4(2 0(4 0(0 4)(1 33))(0 4)))(0((1 8)272)8(1 10))(0((1 8)8)8(1 32))(0((1 8)36)1(0 4))(5(1 33)0 1023)(6((1 8)288)(0 4))(6((1 8)272)(0 8))(0((1 8)296)8(1 34))(5(1 34)0 18446744073709551615)(6((1 8)296)(0 8))(0((1 8)368)8(0 83693))(0((1 8)376)8(0 1))(0((1 2)56)8(1 40))(0((1 2)48)8(1 41))(0((1 2)40)8(1 42))(0((1 2)32)8(1 43))(0((1 2)24)8(1 44))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 10)4096 140737488355328)(4(1 10)8)(9((1 2)-8496)(0 8496))(6((1 2)-8496)(0 8496))(9((1 2)0)(0 24))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-8496)(0 8560)((1 8)0)(0 408))(7((1 2)-8496)(0 8560)((1 32)0)(0 24))(7((1 8)0)(0 408)((1 32)0)(0 24))(3 65536 827984)))(1 436288)))()())"%pstring.
