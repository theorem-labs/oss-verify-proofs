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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_memmove_preB_xsrc_T_u5.
Definition dict_Cut_memmove_preB_xsrc_R0 : CCD.pt := CCD.mk_table 293%positive "((2(1 32)0(1 0)(1 0))(779340 778312 778312 779720)(0#2)(4 0(0 -1)(1 10))(4 0(0 -1)(1 12))(2 0(1 11)#5)(2 0#4#6)(4 0(0 -2)(1 12))(4 0(0 -1)(1 11))(2 0#9#5)(2 0(1 10)#10)(5#7 9223372036854775808 18446744073709551614)(2 1(1 10)(1 11))(5(1 11)0 4611686018427387903)(5(1 10)1 4611686018427387904))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_memmove_preB_xsrc_R0 842%positive "((16 0(16 1(3(11 10 1 4611686018427387903(11 11 1 4611686018427387903(11 11 1 4611686018427387902(16 2(16 3#1)))))(16 4(0#3(16 5(3(11 12 2 4611686018427387904(16 6(16 7#1)))(16 8(0#3(1 0))))))))))(((778312((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 10))(11(1 11))(12(1 12))(13#7)(14#8)(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5#11 0 9223372036854775806)(5(2 4#8#7)0 0)#12(5(2 0(2 0(1 10)#9)(0 -1))0 4611686018427387903)(5(2 4#13(0 1))0 0)#14#15(5(1 10)0 4611686018427387904)(5(1 11)0 4611686018427387904)(5(1 12)1 4611686018427387904)(5#11 0 4611686018427387904)))(1 778312)))((0#15)(0#14)(1#13(0 1)1)(3((0 1)(1 1)))(1(0 1)#13 0)(0#12)(1#8#7 1)(3((0 1)(2 1)))(1#7#8 0))())"%pstring.
