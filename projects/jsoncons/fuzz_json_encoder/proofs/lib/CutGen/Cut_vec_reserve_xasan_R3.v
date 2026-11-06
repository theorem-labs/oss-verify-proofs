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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xasan_T Cut_vec_reserve_xasan_R0 Cut_vec_reserve_xasan_R1 Cut_vec_reserve_xasan_R2.
Definition dict_Cut_vec_reserve_xasan_R3 : CCD.pt := CCD.mk_table 970%positive "((0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#3 8#1)(5(0 14)1 4611686018427387904)(5(0 15)1 4611686018427387904)((1 2)-120)(0#7 8(1 19))((1 2)-112)(0#9 8(1 44))((1 2)-104)(2 0(1 44)(0 66))(0#11 8#12)((1 2)-96)(0#14 8(1 10))((1 2)-88)(0 840320)(0#16 8#17)((1 2)-48)((1 2)-56)((1 2)-64)((1 2)-72)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#25(0 66))((0 0)2147446784)(0 17592186048512)(7#27#28#25(0 66))(5(0 16)1 4611686018427387904)((1 2)-40)(0#31 8(1 10))((1 2)-32)(0#33 8(1 18))((1 2)-24)(0#35 8(1 9))((1 2)-16)(0#37 8(1 8))((1 2)-8)(0#39 8(1 1))((1 10)0)((1 10)8)((1 10)16)(6#41(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#47 2147450880)(1#48(0 3))(7#27#28#41(0 24))(5(1 11)66 66)((1 2)-8192)(0 8072)(9#52#53)((1 2)-80)(9#55(0 8))(0 8192)(6#52#57)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(2 0(1 2)(0 -80))(2 6#61(0 3))(#62 2147450880)(1#63(0 10))(7#52#57#41(0 24))(7#48(0 3)#63(0 10))(5(0 13)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xasan_R3 461%positive "(840956((1 0)(1 72)(2 0(1 2)(0 -128))(1 3)(1 4)(1 73)(1 74)(1 75)(2 0(1 2)(0 -72))(1 10)(1 44)(1 77)(1 78)(1 79)(1 80)(1 81)(1 82)(1 83)(1 44)#1(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 84)(1 85)(1 86)(1 87))(#2#4#5#2#4#6#8#10#13#15#18(0#19 8#12)(0#20 8(1 44))(0#21 8(1 44))(0#22 8(1 44))#2#4#23#24#26#29#30#32#34#36#38#40#2#4(0#41 8(0 0))(0#42 8(0 0))(0#43 8(0 0))#44#45#46#49#50#51#54#56#58#59#60#64#65#66)88(((1 2)-8192#57)((1 10)0(0 24)))()(0 13))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xasan_R3 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xasan_R3 584%positive "((0(0(840148 840376 1414360 730524 524864 841184 1387168 1388196))(4#67(1 0)))(((841184((1#17)(2#61)(3(1 3))(4(1 4))(5(1 73))(6(1 74))(7(1 75))(8(1 10))(9#12)(10(1 10))(11(0 0))(12(0 0))(13(1 79))(14(1 80))(15(1 81))(16(1 82))(17(1 83))(18(1 44))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 84))(29(1 85))(30(1 86))(31(1 87)))()(#67(0#22 8(0 0))(0#19 8(0 0))(0#43 8#12)(0#20 8(0 0))(0#42 8(1 44))(0#21 8(0 0))(0#41 8(1 44))#5#6#8#10#13#15#18#23#24#26#29#30#32#34#36#38#40#44#45#46#49#50#51#54#56#58#59#60#64#65#66))(1 841184)))()())"%pstring.
