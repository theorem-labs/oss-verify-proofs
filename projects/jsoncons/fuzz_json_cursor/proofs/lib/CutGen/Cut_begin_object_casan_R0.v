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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_begin_object_casan_T.
Definition dict_Cut_begin_object_casan_R0 : CCD.pt := CCD.mk_table 190%positive "((5(0 100)1 4611686018427387904)(0 -128)(2 0(1 2)#2)(0 2147450880)((1 10)0)(2 6(1 10)(0 3))(#6 2147450880)((0 0)2147446784)(0 17592186048512)((1 11)0)((1 12)0)((1 2)-9792)(0 9792)((1 11)8))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_begin_object_casan_R0 1648%positive "((0(0(781384 782008 412324 807200 829020 822600 747008 1330948 1331976))(4#1(1 0)))(((412324((1(0 781496))(2#3)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#3)(10(0 64))(11(0 1427896))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 10))(20(1 12))(21(1 11))(22(1 22))(23(1 23))(24#4)(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-128)8(0 0))(3 1388760 1392480)(0((0 0)1427896)8#4)(0((0 0)1427904)4(0 1))(1((0 0)2147621540)(0 1))(1((0 0)2147621501)(0 1))(3 1363488 1365344)(6#5(0 272))(0((1 10)8)4(0 1024))(0((1 10)96)8(0 1364920))(0((1 10)128)8(2 0(1 10)(0 96)))(0((1 10)144)4(1 34))(5(1 34)0 1024)(0((1 10)208)1(1 35))(0((1 10)211)1(0 1))(0((1 10)213)1(0 1))(5(1 10)7024640 140737479966448)(4(1 10)8)(1#7(0 34))(7#8#9#5(0 272))(0#10 8(0 1365216))(5(1 11)7024640 140737479966672)(4(1 11)8)(1((2 6(1 11)(0 3))2147450880)(0 1))(7#8#9#10(0 8))(0#11 4(0 0))(6#11(0 16))(5(1 12)7024640 140737479966704)(4(1 12)8)(1((2 6(1 12)(0 3))2147450880)(0 2))(7#8#9#11(0 16))(9#12(0 9664))(9((1 2)-120)(0 32))(6#12#13)(5(1 2)140735332492864 140737488355328)(4(1 2)32)(7#12#13#5(0 272))(7#12#13#11(0 16))(7#12#13#10(0 8))(7#5(0 272)#11(0 16))(7#5(0 272)#10(0 8))(7#11(0 16)#10(0 8))(7#12#13#14(0 40))(7#5(0 272)#14(0 40))(7#11(0 16)#14(0 40))(7#10(0 8)#14(0 40))(7#8#9#14(0 40))(7#7(0 34)#11(0 16))(7#7(0 34)((0 0)6877256)(0 2))(7#7(0 34)((0 0)7015072)(0 544))))(1 412324)))()())"%pstring.
