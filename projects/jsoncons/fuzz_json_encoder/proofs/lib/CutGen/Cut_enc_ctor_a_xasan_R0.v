(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_enc_ctor_a_xasan_T.
Definition dict_Cut_enc_ctor_a_xasan_R0 : CCD.pt := CCD.mk_table 146%positive "((5(0 40)1 4611686018427387904)(2 0(1 2)(0 -96))(0 2147450880)((1 10)0)((0 0)2147446784)(0 17592186048512)((1 11)0)((1 32)0)((1 2)-4880)(0 4880))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_enc_ctor_a_xasan_R0 1465%positive "((0(0(725968 733592 418576 540344 526044 524864 1387168 1388196))(4#1(1 0)))(((418576((1(0 726080))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#2)(10(0 352))(11(0 1482488))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18#3)(19(1 19))(20(1 12))(21(1 11))(22(1 10))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-96)8(0 0))(3 1417216 1449984)(3 65536 361956)(0((0 0)1482488)8#3)(0((0 0)1482496)4(0 1))(1((0 0)2147631446)(0 1))(1((0 0)2147461520)(0 1))(1((0 0)2147628405)(0 1))(1((0 0)2147628406)(0 1))(1((0 0)2147628395)(0 1))(1((0 0)2147628616)(0 3))(1((0 0)2147628624)(0 3))(1((0 0)2147471652)(0 3))(1((0 0)2147471660)(0 3))(9#4(0 408))(6#4(0 408))(5(1 10)7077888 140737479966312)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 51))(7#5#6#4(0 408))(0#7 8(1 32))(9#7(0 8))(6#7(0 8))(4(1 11)8)(1((2 6(1 11)(0 3))2147450880)(0 1))(7#5#6#7(0 8))(5(1 11)7077888 140737488355320)(9#8(0 24))(4(1 32)8)(1((2 6(1 32)(0 3))2147450880)(0 3))(7#5#6#8(0 24))(5(1 32)7077888 140737479966696)(7#4(0 408)#7(0 8))(7#4(0 408)#8(0 24))(7#7(0 8)#8(0 24))(9#9(0 4784))(6#9#10)(5(1 2)140735332487952 140737488355328)(4(1 2)32)(7#9#10#4(0 408))(7#9#10#7(0 8))(7#9#10#8(0 24))))(1 418576)))()())"%pstring.
