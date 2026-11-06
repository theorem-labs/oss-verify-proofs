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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_ao_grow2_xsrc_T.
Definition dict_Cut_vbm_ao_grow2_xsrc_R0 : CCD.pt := CCD.mk_table 155%positive "((0 1048576)(5#1 1 4611686018427387904)(4 0(0 32)(1 33))(2 7#3(0 4))(2 0(1 8)(0 264))((1 8)264)(2 0(1 32)#3)((1 2)-8256)((1 2)8)(0 8304)((1 8)0)((1 32)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_ao_grow2_xsrc_R0 945%positive "((0(0(245392 246500 783764 763484 704108 763484 764892))(4#2(1 0)))(((783764((1(0 274376))(2(2 0(1 2)(0 -16)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8#4)(9#5)(10(4 0(0 32)#4))(11#4)(12(0 0))(13#3)(14(0 2))(15(1 15))(16(1 16))(17(1 17))(18(2 0(1 35)(0 1)))(19(0 0))(20#3)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-16)8(1 8))(0((1 2)-8)8(0 246380))(0((1 2)40)8#5)(0#6 8(1 32))(0((1 8)272)8#7)(0((1 8)280)8#7)(6#6(0 24))(0((1 8)296)8(1 35))(5(1 35)0 18446744073709551615)(0((1 8)376)8(0 1))(0((1 8)28)1(0 0))(0((1 8)30)1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(9#8(0 8240))(6#8(0 8256))(9#9(0 32))(6#9(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#8#10#11(0 408))(5(1 33)2 512)(5(2 1#4(2 7#3(0 5)))2 512)(5(2 1#4(1 33))2 512)(9#12#3)(6#12#3)(5(1 32)4096 140737488355328)(4(1 32)16)(7#8#10#12#3)(7#11(0 408)#12#3)(2#12#3 0)))(1 783764)))()())"%pstring.
