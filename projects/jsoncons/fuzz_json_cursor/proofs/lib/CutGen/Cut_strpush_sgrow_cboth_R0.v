(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strpush_sgrow_cboth_T.
Definition dict_Cut_strpush_sgrow_cboth_R0 : CCD.pt := CCD.mk_table 63%positive "((5(0 100)1 4611686018427387904)((1 10)0)((1 2)-4368)(0 4368))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_strpush_sgrow_cboth_R0 823%positive "((0(0(990424 990728 1363704 520748 1336512 1337540))(4#1(1 0)))(((1363704((1(0 990620))(2(2 0(1 2)(0 -64)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 11))(9(1 10))(10(0 48))(11(1 11))(12(0 44))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(2 0(1 10)(0 1)))(19(0 48))(20(0 22))(21(0 23))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(3 1368064 1400832)(0((0 0)1432824)8(0 2147450880))(0#2 1(0 44))(2((1 10)1)(0 22)0)(5(1 11)0 255)(9#2(0 24))(6#2(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(9#3(0 4304))(6#3#4)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#3#4#2(0 24))))(1 1363704)))()())"%pstring.
