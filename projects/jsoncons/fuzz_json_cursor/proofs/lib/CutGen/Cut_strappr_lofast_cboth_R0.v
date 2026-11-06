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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strappr_lofast_cboth_T.
Definition dict_Cut_strappr_lofast_cboth_R0 : CCD.pt := CCD.mk_table 316%positive "((5(0 100)1 4611686018427387904)(0 -160)(2 0(1 2)#2)(0 2147450880)(2 0(1 11)(1 35))((1 10)0)(4 0(0 2)(1 32))((1 34)0)(4 0(0 -1)(1 33))((0 0)2147446784)(0 17592186048512)(2 6(1 10)(0 3))(#12 2147450880)((1 2)-4880)(0 4880)(0 -192)(2 0(1 2)#16)(2 6#17(0 3))(#18 2147450880)((1 11)0)(4 0(0 -1)(1 11))(4 0(0 -1)(1 35)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_strappr_lofast_cboth_R0 1530%positive "((0(0(816864 817876 413656 522512 1336512 1337540))(4#1(1 0)))(((413656((1(0 816984))(2#3)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#3)(10(0 96))(11(0 1432824))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18#4)(19(1 10))(20(1 11))(21#5)(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#1(0((1 2)-104)8(1 27))(0((1 2)-96)8(1 26))(0((1 2)-88)8(1 25))(0((1 2)-80)8(1 24))(0((1 2)-72)8(1 23))(0((1 2)-64)8(1 22))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0((1 2)-160)8(0 0))(3 1393824 1397544)(0((0 0)1432824)8#4)(0((0 0)1432832)4(0 1))(0#6 8(2 0#7(0 1)))(0((1 10)8)8(1 33))(0((1 10)16)8(1 34))(5(1 32)12 70368744177664)(5(1 33)0 67108864)(2#8(1 33)0)(9#8#7)(6#8#7)(5(1 34)4096 140737488355328)(4(1 34)16)(5(2 0(2 0#7#9)(0 -1))0 140737488355328)(7#10#11#8#7)(9#6(0 24))(6#6(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(1#13(0 3))(7#10#11#6(0 24))(9#14(0 4720))(9((1 2)-152)(0 48))(6#14#15)(5(1 2)140735332487952 140737488355328)(4(1 2)32)(1#19(0 3))(7#14#15#6(0 24))(7#14#15#8#7)(7#6(0 24)#8#7)(7#13(0 3)#19(0 3))(5(1 35)1 67108864)(5(2 0(1 33)(1 35))1 67108863)(2#20(1 35)1)(9#20(1 35))(5(1 11)4096 140737488355328)(5#5 4096 140737488355328)(7#10#11#20(1 35))(7#14#15#20(1 35))(7#6(0 24)#20(1 35))(7#8#7#20(1 35))(5(2 0#21(2 0(1 34)#22))0 140737488355328)(5(2 0#21(1 34))1 140737488355328)(5(2 0(2 0#7(2 0#9#22))(0 -1))0 140737488355328)))(1 413656)))()())"%pstring.
