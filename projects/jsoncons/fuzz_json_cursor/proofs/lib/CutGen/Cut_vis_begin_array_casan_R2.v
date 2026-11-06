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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vis_begin_array_casan_T Cut_vis_begin_array_casan_R0 Cut_vis_begin_array_casan_R1.
Definition dict_Cut_vis_begin_array_casan_R2 : CCD.pt := CCD.mk_table 623%positive "((0 2147450880)(3 1388760 1392480)((0 0)1427896)(0#3 8#1)(5(0 99)1 4611686018427387904)((1 10)16)(0#6 1(1 11))((1 10)8)(0 1024)(0#8 8#9)(5(0 100)1 4611686018427387904)((1 2)-32)(0#12 8(1 18))((1 2)-24)(0#14 8(1 9))((1 2)-16)(0#16 8(1 8))((1 2)-8)(0#18 8(1 1))((1 10)17)(9#20(0 31))(6#8(0 40))(5(1 10)7024640 140737479966672)(4(1 10)8)(2 6(1 10)(0 3))(#25 2147450880)(1#26(0 6))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#28#29#30(0 48))((1 2)-2624)(0 2592)(9#32#33)(0 2624)(6#32#35)(5(1 2)140735332485696 140737488355328)(4(1 2)16)(7#32#35#30(0 48))(#2#4#5#7#10#2#4#11#13#15#17#19#2#4#21#22#23#24#27#31#34#36#37#38#39))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vis_begin_array_casan_R2 264%positive "(829680((1 0)(1 50)(2 0(1 2)(0 -64))(1 3)(1 4)(1 51)(1 52)(1 53)(1 10)(1 11)(2 0(1 10)(0 17))(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)#1(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 62)(1 63)(1 64)(1 65))#40 66(((1 2)-2624#35)((1 10)8(0 40)))()(0 98))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vis_begin_array_casan_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vis_begin_array_casan_R2 386%positive "((0(0(829556 829704 520976 519796 1330948 1331976))(1 0))(((829704((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 51))(6(1 52))(7(1 53))(8(1 8))(9(1 9))(10(0 1))(11(1 55))(12(1 56))(13(1 57))(14(1 58))(15(1 59))(16(1 60))(17(1 61))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 62))(29(1 63))(30(1 64))(31(1 65)))()#40)(1 829704)))()())"%pstring.
