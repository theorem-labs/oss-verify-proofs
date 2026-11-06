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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xasan_T Cut_vec_reserve_xasan_R0 Cut_vec_reserve_xasan_R1 Cut_vec_reserve_xasan_R2 Cut_vec_reserve_xasan_R3.
Definition dict_Cut_vec_reserve_xasan_R4 : CCD.pt := CCD.mk_table 1010%positive "((2 0(1 2)(0 -80))(2 0(1 44)(0 66))(3 1444792 1448528)((0 0)1482488)(0 2147450880)(0#4 8#5)(5(0 13)1 4611686018427387904)((1 2)-72)(0#8 8(0 0))((1 2)-48)(0#10 8(0 0))((1 10)16)(0#12 8#2)((1 2)-56)(0#14 8(0 0))((1 10)8)(0#16 8(1 44))((1 2)-64)(0#18 8(0 0))((1 10)0)(0#20 8(1 44))(5(0 14)1 4611686018427387904)(5(0 15)1 4611686018427387904)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#26(0 66))((0 0)2147446784)(0 17592186048512)(7#28#29#26(0 66))(5(0 16)1 4611686018427387904)((1 2)-40)(0#32 8(1 10))((1 2)-32)(0#34 8(1 18))((1 2)-24)(0#36 8(1 9))((1 2)-16)(0#38 8(1 8))((1 2)-8)(0#40 8(1 1))(6#20(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(7#28#29#20(0 24))(5(1 11)66 66)((1 2)-8192)(0 8072)(9#47#48)((1 2)-80)(9#50(0 8))(0 8192)(6#47#52)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(7#47#52#20(0 24))(2 6(1 10)(0 3))(#57 2147450880)(2 6#1(0 3))(#59 2147450880)(7#58(0 3)#60(0 10))(#3#6#7#9#11#13#15#17#19#21#22#23#24#25#27#30#31#33#35#37#39#41#42#43#44#45#46#49#51#53#54#55#56#61))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xasan_R4 243%positive "(840320((1 0)(1 88)#1(1 3)(1 4)(1 89)(1 90)(1 91)(1 10)#2(1 92)(1 93)(1 94)(1 95)(1 96)(1 97)(1 98)(1 99)(1 44)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 100)(1 101)(1 102)(1 103))#62 104(((1 2)-8192#52)((1 10)0(0 24)))()(0 12))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xasan_R4 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints4 : list (nat * CC.subst) := hints3.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xasan_R4 404%positive "((0(0(840148 840376 1414360 730524 524864 841184 1387168 1388196))(1 0))(((840376((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 89))(6(1 90))(7(1 91))(8(1 8))(9(1 9))(10(0 0))(11(0 0))(12(1 94))(13(1 95))(14(1 96))(15(1 97))(16(1 98))(17(1 99))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 100))(29(1 101))(30(1 102))(31(1 103)))()#62)(1 840376)))()())"%pstring.
