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
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xsrc_T.
Definition dict_Cut_visit_null_root_xsrc_R0 : CCD.pt := CCD.mk_table 105%positive "((0 1048576)(5#1 1 4611686018427387904)((1 10)296)((1 2)-10624)(0 10624)((1 10)0)((1 32)0)((0 0)883672))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xsrc_R0 922%positive "((0(0(247028 247208 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(4#2(1 0)))(((253336((1(0 247124))(2(2 0(1 2)(0 -32)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 9))(10(1 34))(11(1 34))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 10)8)8(1 32))(0#3 8(1 37))(5(1 37)0 18446744073709551615)(6#3(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(9#4(0 10592))(9((1 2)-32)(0 8))(6#4#5)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#4#5#6(0 408))(7#4#5#7(0 24))(7#6(0 408)#7(0 24))(3 65536 813152)(0((1 10)264)8(1 34))(0((1 10)272)8(1 34))(7#4#5#8(0 18))(7#6(0 408)#8(0 18))(7#7(0 24)#8(0 18))))(1 253336)))()())"%pstring.
