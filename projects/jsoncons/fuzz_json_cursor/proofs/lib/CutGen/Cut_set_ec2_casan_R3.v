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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_set_ec2_casan_T Cut_set_ec2_casan_R0 Cut_set_ec2_casan_R1 Cut_set_ec2_casan_R2.
Definition dict_Cut_set_ec2_casan_R3 : CCD.pt := CCD.mk_table 540%positive "((0 2147450880)(3 1388760 1392480)((0 0)1427896)(0#3 8#1)(5(0 18)1 4611686018427387904)(5(0 19)1 4611686018427387904)(5(0 20)1 4611686018427387904)((1 2)-32)(0#8 8(1 18))((1 2)-24)(0#10 8(1 9))((1 2)-16)(0#12 8(1 8))((1 2)-8)(0#14 8(1 1))((1 10)0)(6#16(0 16))(5(1 10)140735332484096 140737488355312)(4(1 10)8)(2 6(1 10)(0 3))(#20 2147450880)(1#21(0 2))((0 0)2147446784)(0 17592186048512)(7#23#24#16(0 16))(5(1 11)1 31)((1 2)-1024)(9#27(0 992))(0 1024)(6#27#29)(5(1 2)140735332484096 140737488355328)(4(1 2)16)(7#27#29#16(0 16))(0 1407120))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_set_ec2_casan_R3 329%positive "(825468((1 0)(1 64)(2 0(1 2)(0 -32))(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)(1 11)(1 68)(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)#1(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#2#4#5#2#4#6#2#4#7#9#11#13#15#2#4(9#16(0 16))#17#18#19#22#25#26#28#30#31#32#33)80(((1 2)-1024#29)((1 10)0(0 16)))()(0 17))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_set_ec2_casan_R3 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints3.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec2_casan_R3 503%positive "((0(0(825268 825268 825404 858236 435756 858316 1330948 1331976))(1 0))(((825404((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 8))(9(1 9))(10(2 0(1 10)(0 8)))(11#34)(12(1 70))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()((0((1 10)8)8#34)(0#16 8(1 11))#2#4#5#2#4#6#2#4#7#9#11#13#15#2#4#17#18#19#22#25#26#28#30#31#32#33))(1 825404)))()())"%pstring.
