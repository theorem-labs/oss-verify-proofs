(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbegin_tail_object_xsrc_T.
Definition dict_Cut_vbegin_tail_object_xsrc_R0 : CCD.pt := CCD.mk_table 153%positive "((0 1048576)(5#1 1 4611686018427387904)(0 83539)(4 0(0 4)(1 33))(2 0#4(0 4))((1 8)288)((1 8)272)((1 8)296)((1 2)-8496)(0 8496)(0 8592)((1 8)0)((1 32)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vbegin_tail_object_xsrc_R0 916%positive "((0(0(244644 244728 421620 763484 764892))(4#2(1 0)))(((421620((1(0 244680))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 32))(11#3)(12(0 1))(13#5)(14#4)(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0#6 4#5)(0#7 8(1 18))(0((1 8)8)8(1 32))(0((1 8)36)1(0 4))(5(1 33)0 1023)(6#6(0 4))(6#7(0 8))(0#8 8(1 34))(5(1 34)0 18446744073709551615)(6#8(0 8))(0((1 8)336)8#3)(0((1 8)344)8(0 1))(0((1 2)88)8(1 40))(0((1 2)80)8(1 41))(0((1 2)72)8(1 42))(0((1 2)64)8(1 43))(0((1 2)56)8(1 44))(0((1 2)48)8(1 45))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(9#9#10)(6#9#10)(9((1 2)0)(0 48))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#9#11#12(0 408))(7#9#11#13(0 24))(7#12(0 408)#13(0 24))(3 65536 813152)))(1 421620)))()())"%pstring.
