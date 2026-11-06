(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums EncSums2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_double_nested_xsrc_T.
Definition dict_Cut_visit_double_nested_xsrc_R0 : CCD.pt := CCD.mk_table 308%positive "((242548 243296 242884 242736 242816 243056 243476 243596 252124 421620 253336 254004 242596 242664 242676 242712 242784 763484 764892)(0#1)(0 1048576)(5#3 1 4611686018427387904)(4 0(0 32)(1 33))(2 0#5(1 34))((1 2)-40)((1 10)296)((1 2)-10624)(0 10624)((1 10)0)((1 32)0)(#6 -32)(#6 -8)((1 34)0)((0 0)883672))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_double_nested_xsrc_R0 1325%positive "((0#2(0(3 1)(0#2(4#4(1 0)))))(((242596((1(1 1))(2(2 0(1 2)(0 -96)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 13))(10#6)(11(1 34))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 12))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#4(0((1 2)-48)8(1 48))(0#7 8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 10)8)8(1 32))(0((1 10)16)8(0 788528))(0((1 10)88)2(1 41))(5(1 41)0 65535)(0#8 8(1 37))(5(1 37)0 18446744073709551615)(6#8(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(9#9(0 10528))(9((1 2)-96)(0 48))(9#7(0 0))(6#9#10)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#9#10#11(0 408))(7#9#10#12(0 24))(7#11(0 408)#12(0 24))(3 65536 813152)(0((1 10)264)8(1 34))(0((1 10)272)8#6)(0#13 4(1 38))(5(1 38)0 1)(0(#6 -28)1(0 0))(0(#6 -27)1(1 39))(0(#6 -26)1(1 40))(5(1 40)0 1)(0#14 8(1 36))(6#14(0 8))(9#13(0 32))(5(1 33)1 1024)(5(2 0(4 0(0 -32)(1 33))(1 35))0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)(7#9#10#15(1 35))(7#11(0 408)#15(1 35))(7#12(0 24)#15(1 35))(7#9#10#16(0 18))(7#11(0 408)#16(0 18))(7#12(0 24)#16(0 18))(7#15(1 35)#16(0 18))))(1 242596)))()())"%pstring.
