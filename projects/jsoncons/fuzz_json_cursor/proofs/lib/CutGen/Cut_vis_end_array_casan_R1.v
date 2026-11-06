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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vis_end_array_casan_T Cut_vis_end_array_casan_R0.
Definition dict_Cut_vis_end_array_casan_R1 : CCD.pt := CCD.mk_table 484%positive "((2 0(1 2)(0 -64))(0 2147450880)(3 1388760 1392480)((0 0)1427896)(0#4 8#2)(5(0 100)1 4611686018427387904)((1 2)-24)(0#7 8(1 9))((1 2)-16)(0#9 8(1 8))((1 2)-8)(0#11 8(1 1))((1 10)8)(6#13(0 40))(5(1 10)7024640 140737479966672)(4(1 10)8)(2 6(1 10)(0 3))(#17 2147450880)(1#18(0 6))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#20#21#22(0 48))((1 2)-2624)(0 2600)(9#24#25)(0 2624)(6#24#27)(5(1 2)140735332485696 140737488355328)(4(1 2)16)(7#24#27#22(0 48))(5(0 99)1 4611686018427387904))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vis_end_array_casan_R1 307%positive "(828280((1 0)(1 34)#1(1 3)(1 4)(1 35)(1 36)(1 37)(1 10)#2(2 0(1 2)(0 -48))(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 46)(1 47)(1 48)(1 49))(#3#5#6#8#10#12#3#5(9#13(0 40))#14#15#16#19#23#26#28#29#30#31)50(((1 2)-2624#27)((1 10)8(0 40)))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vis_end_array_casan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vis_end_array_casan_R1 519%positive "((0(0(828232 828372 520976 519796 1330948 1331976))(4#32(1 0)))(((519796((1(0 828352))(2#1)(3(1 3))(4(1 4))(5(1 35))(6(1 36))(7(1 37))(8(1 10))(9#2)(10(2 0(1 10)(0 17)))(11(2 0(1 2)(0 -55)))(12(0 31))(13(1 41))(14(1 42))(15(1 43))(16(1 44))(17(1 45))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 46))(29(1 47))(30(1 48))(31(1 49)))()(#32(0((1 10)16)1(0 0))(0#13 8(0 2048))#3#5#6#8#10#12#3#5(9((1 10)17)(0 31))#14#15#16#19#23#26#28#29#30#31))(1 519796)))()())"%pstring.
