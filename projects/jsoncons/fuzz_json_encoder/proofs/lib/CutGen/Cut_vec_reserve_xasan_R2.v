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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xasan_T Cut_vec_reserve_xasan_R0 Cut_vec_reserve_xasan_R1.
Definition dict_Cut_vec_reserve_xasan_R2 : CCD.pt := CCD.mk_table 1070%positive "((0 -128)(2 0(1 2)#1)(2 0(1 2)(0 -72))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#6 8#4)(5(0 15)1 4611686018427387904)((1 2)-120)(0#9 8(1 19))((1 2)-112)(0#11 8(1 44))((1 2)-104)(2 0(1 44)(0 66))(0#13 8#14)((1 2)-96)(0#16 8(1 10))((1 2)-88)(0 840320)(0#18 8#19)((1 2)-48)(0#21 8#14)((1 2)-56)(0#23 8(1 44))((1 2)-64)(0#25 8(1 44))((1 2)-72)(0#27 8(1 44))(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#31(0 66))((0 0)2147446784)(0 17592186048512)(7#33#34#31(0 66))(5(0 16)1 4611686018427387904)((1 2)-40)(0#37 8(1 10))((1 2)-32)(0#39 8(1 18))((1 2)-24)(0#41 8(1 9))((1 2)-16)(0#43 8(1 8))((1 2)-8)(0#45 8(1 1))((1 10)0)(0#47 8(0 0))((1 10)8)(0#49 8(0 0))((1 10)16)(0#51 8(0 0))(6#47(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#56 2147450880)(1#57(0 3))(7#33#34#47(0 24))(5(1 11)66 66)((1 2)-8192)(0 8072)(9#61#62)((1 2)-80)(9#64(0 8))(0 8192)(6#61#66)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(2 0(1 2)(0 -80))(2 6#70(0 3))(#71 2147450880)(1#72(0 10))(7#61#66#47(0 24))(7#57(0 3)#72(0 10))(5(0 14)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xasan_R2 354%positive "(840868((1 0)(1 56)#2(1 3)(1 4)(1 57)(1 58)(1 59)#3(1 10)(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 44)#4(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#5#7#8#10#12#15#17#20#22#24#26#28#5#7#29#30#32#35#36#38#40#42#44#46#5#7#48#50#52#53#54#55#58#59#60#63#65#67#68#69#73#74#75)72(((1 2)-8192#66)((1 10)0(0 24)))()(0 14))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xasan_R2 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xasan_R2 526%positive "((0(0(840148 840376 1414360 730524 524864 841184 1387168 1388196))(4#76(1 0)))(((524864((1(0 840956))(2#2)(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8#3)(9(1 10))(10(1 44))(11(0 0))(12(0 0))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 44))(19#4)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()(#76#5#7#8#10#12#15#17#20#22#24#26#28#5#7#29#30#32#35#36#38#40#42#44#46#5#7#48#50#52#53#54#55#58#59#60#63#65#67#68#69#73#74#75))(1 524864)))()())"%pstring.
