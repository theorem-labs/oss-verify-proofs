(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cctor_casan_T.
Definition dict_Cut_cctor_casan_R0 : CCD.pt := CCD.mk_table 151%positive "((5(0 60)1 4611686018427387904)(0 -160)(2 0(1 2)#2)(0 2147450880)((0 0)2147446784)(0 17592186048512)((1 10)0)((1 11)0)((1 12)0)((1 2)-11008)(0 11008))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_cctor_casan_R0 1374%positive "((0(0(720100 721248 413508 520976 819492 535276 1330948 1331976))(4#1(1 0)))(((413508((1(0 720220))(2#3)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#3)(10(0 352))(11(0 1427896))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 11))(22(1 10))(23(1 23))(24(1 24))(25#4)(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-136)8(1 12))(0((1 2)-104)8(1 27))(0((1 2)-96)8(1 26))(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-160)8(0 0))(3 1359872 1392640)(0((0 0)1427896)8#4)(0((0 0)1427904)4(0 1))(1((0 0)2147621472)(0 1))(1((0 0)2147621498)(0 1))(1((0 0)2147621499)(0 1))(1((0 0)2147623346)(0 1))(5(1 10)7024640 140737479966064)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 82))(7#5#6#7(0 656))(5(1 11)7024640 140737479966448)(4(1 11)8)(1((2 6(1 11)(0 3))2147450880)(0 34))(7#5#6#8(0 272))(5(1 12)7024640 140737479966704)(4(1 12)8)(1((2 6(1 12)(0 3))2147450880)(0 2))(7#5#6#9(0 16))(7#7(0 656)#8(0 272))(7#7(0 656)#9(0 16))(7#8(0 272)#9(0 16))(9#10(0 10848))(9((1 2)-152)(0 16))(9((1 2)-128)(0 24))(6#10#11)(5(1 2)140735332494080 140737488355328)(4(1 2)32)(7#10#11#7(0 656))(7#10#11#8(0 272))(7#10#11#9(0 16))))(1 413508)))()())"%pstring.
