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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vis_begin_object_cboth_T Cut_vis_begin_object_cboth_R0.
Definition dict_Cut_vis_begin_object_cboth_R1 : CCD.pt := CCD.mk_table 508%positive "((2 0(1 2)(0 -64))(0 2147450880)(3 1393824 1397544)((0 0)1432824)(0#4 8#2)(5(0 100)1 4611686018427387904)((1 2)-32)(0#7 8(1 18))((1 2)-24)(0#9 8(1 9))((1 2)-16)(0#11 8(1 8))((1 2)-8)(0#13 8(1 1))((1 10)8)(6#15(0 40))(5(1 10)7028736 140737479966672)(4(1 10)8)(2 6(1 10)(0 3))(#19 2147450880)(1#20(0 6))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#22#23#24(0 48))((1 2)-2624)(0 2592)(9#26#27)(0 2624)(6#26#29)(5(1 2)140735332485696 140737488355328)(4(1 2)16)(7#26#29#24(0 48))(5(0 99)1 4611686018427387904))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vis_begin_object_cboth_R1 310%positive "(831616((1 0)(1 34)#1(1 3)(1 4)(1 35)(1 36)(1 37)(1 10)(1 11)(2 0(1 2)(0 -56))(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 46)(1 47)(1 48)(1 49))(#3#5#6#8#10#12#14#3#5(9#15(0 40))#16#17#18#21#25#28#30#31#32#33)50(((1 2)-2624#29)((1 10)8(0 40)))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vis_begin_object_cboth_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vis_begin_object_cboth_R1 522%positive "((0(0(831560 831708 521936 520756 1336512 1337540))(4#34(1 0)))(((520756((1(0 831684))(2#1)(3(1 3))(4(1 4))(5(1 35))(6(1 36))(7(1 37))(8(1 10))(9(1 11))(10(2 0(1 10)(0 17)))(11(2 0(1 2)(0 -63)))(12(0 31))(13(1 41))(14(1 42))(15(1 43))(16(1 44))(17(1 45))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 46))(29(1 47))(30(1 48))(31(1 49)))()(#34(0((1 10)16)1(1 11))(0#15 8(0 256))#3#5#6#8#10#12#14#3#5(9((1 10)17)(0 31))#16#17#18#21#25#28#30#31#32#33))(1 520756)))()())"%pstring.
