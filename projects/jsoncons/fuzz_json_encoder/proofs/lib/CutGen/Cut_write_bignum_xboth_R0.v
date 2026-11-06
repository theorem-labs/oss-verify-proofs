(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsXB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_write_bignum_xboth_T.
Definition dict_Cut_write_bignum_xboth_R0 : CCD.pt := CCD.mk_table 168%positive "((0 1048576)(5#1 1 4611686018427387904)(0 -128)(2 0(1 2)#3)(0 2147450880)((1 10)296)((1 11)0)((0 0)2147446784)(0 17592186048512)((1 10)0)((1 32)0)((1 2)-4528)(0 4528))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_write_bignum_xboth_R0 1392%positive "((0(0(782480 784840 421260 1055420 542600 1402040 1403068))(4#2(1 0)))(((421260((1(0 782596))(2#4)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#4)(10(0 544))(11(0 1497016))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 10))(21(1 11))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26#5)(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#2(0((1 2)-104)8(1 27))(0((1 2)-96)8(1 26))(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-128)8(0 0))(3 1459384 1463120)(0((0 0)1497016)8#5)(0((0 0)1497024)4(0 1))(0((1 10)8)8(1 32))(0((1 10)27)1(0 0))(0#6 8(1 35))(5(1 35)0 18446744073709551615)(6#6(0 8))(0#7 8(1 33))(0((1 11)8)8(1 34))(5(1 34)0 140737488355328)(5(1 10)7094272 140737479966312)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 51))(7#8#9#10(0 408))(5(1 32)7094272 140737479966696)(4(1 32)8)(1((2 6(1 32)(0 3))2147450880)(0 3))(7#8#9#11(0 24))(5(1 11)7094272 140737479966704)(4(1 11)8)(1((2 6(1 11)(0 3))2147450880)(0 2))(7#8#9#7(0 16))(7#12#13#10(0 408))(7#12#13#11(0 24))(7#10(0 408)#11(0 24))(7#12#13#7(0 16))(7#10(0 408)#7(0 16))(7#11(0 24)#7(0 16))(9#12(0 4400))(9((1 2)-120)(0 16))(6#12#13)(5(1 2)140735332487600 140737488355328)(4(1 2)32)(7#8#9#12#13)))(1 421260)))()())"%pstring.
