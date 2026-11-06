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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vec_reserve_casan_T Cut_vec_reserve_casan_R0.
Definition dict_Cut_vec_reserve_casan_R1 : CCD.pt := CCD.mk_table 743%positive "((2 0(1 2)(0 -80))(3 1388760 1392480)((0 0)1427896)(0 2147450880)(0#3 8#4)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#8(0 66))((0 0)2147446784)(0 17592186048512)(7#10#11#8(0 66))(5(0 16)1 4611686018427387904)((1 2)-40)(0#14 8(1 10))((1 2)-32)(0#16 8(1 18))((1 2)-24)(0#18 8(1 9))((1 2)-16)(0#20 8(1 8))((1 2)-8)(0#22 8(1 1))((1 10)0)(0#24 8(0 0))((1 10)8)(0#26 8(0 0))((1 10)16)(0#28 8(0 0))(6#24(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#33 2147450880)(1#34(0 3))(7#10#11#24(0 24))(5(1 11)66 66)((1 2)-8192)(0 8192)(6#38#39)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(2 6#1(0 3))(#43 2147450880)(1#44(0 10))(7#38#39#24(0 24))(7#34(0 3)#44(0 10))(5(0 15)1 4611686018427387904)(2 0(1 44)(0 66)))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_casan_R1 344%positive "(827204((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(0 66)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(0 0)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#2#5#6#7(9#8(0 66))#9#12#13#15#17#19#21#23#2#5#25#27#29#30#31#32#35#36#37(9#38(0 8152))#40#41#42#45#46#47)56(((1 2)-8192#39)((1 10)0(0 24)))()(0 15))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_casan_R1 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_casan_R1 735%positive "((0(0(827068 827296 1358140 726504 519796 808492 1330948 1331976))(4#48(1 0)))(((726504((1(0 808152))(2(2 0(1 2)(0 -128)))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(2 0(1 2)(0 -72)))(9(1 10))(10(1 10))(11(0 1427896))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 44))(19#4)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#48(0((1 2)-120)8(1 19))(0((1 2)-112)8(1 44))(0((1 2)-104)8#49)(0((1 2)-96)8(1 10))(0((1 2)-88)8(0 827240))(0((1 2)-48)8#49)(0((1 2)-56)8(1 44))(0((1 2)-64)8(1 44))(0((1 2)-72)8(1 44))#2#5#6#7#9#12#13#15#17#19#21#23#2#5#25#27#29#30#31#32#35#36#37(9#38(0 8072))(9((1 2)-80)(0 8))#40#41#42#45#46#47))(1 726504)))()())"%pstring.
