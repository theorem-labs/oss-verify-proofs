(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums2.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_visit_double_root_xsrc_T_u5.
Definition o0 : CA.pout := CCD.dec_pout 1495%positive "((0(0(245280 246268 245616 245516 245588 245820 246304 246464 256492 436288 258088 258796 245328 245436 245448 245476 245556 778312 779720))(0(3 1)(0(0(245280 246268 245616 245516 245588 245820 246304 246464 256492 436288 258088 258796 245328 245436 245448 245476 245556 778312 779720))(4(5(0 1048576)1 4611686018427387904)(1 0)))))(((245328((1(1 1))(2(2 0(1 2)(0 -96)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 13))(10(1 34))(11(1 34))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 12))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 1048576)1 4611686018427387904)(0((1 2)-48)8(1 48))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 10)8)8(1 32))(0((1 10)16)8(0 803360))(0((1 10)88)2(1 41))(5(1 41)0 65535)(0((1 10)296)8(1 37))(5(1 37)0 18446744073709551615)(6((1 10)296)(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(9((1 2)-10624)(0 10528))(9((1 2)-96)(0 48))(9((1 2)-40)(0 0))(6((1 2)-10624)(0 10624))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7((1 2)-10624)(0 10624)((1 10)0)(0 408))(7((1 2)-10624)(0 10624)((1 32)0)(0 24))(7((1 10)0)(0 408)((1 32)0)(0 24))(3 65536 827984)(0((1 10)264)8(1 34))(0((1 10)272)8(1 34))(7((1 2)-10624)(0 10624)((0 0)898504)(0 18))(7((1 10)0)(0 408)((0 0)898504)(0 18))(7((1 32)0)(0 24)((0 0)898504)(0 18))))(1 245328)))()())"%pstring.
