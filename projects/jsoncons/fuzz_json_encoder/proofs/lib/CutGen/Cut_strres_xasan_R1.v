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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strres_xasan_T Cut_strres_xasan_R0.
Definition dict_Cut_strres_xasan_R1 : CCD.pt := CCD.mk_table 920%positive "((2 0(1 2)(0 -80))(0 18446744073709551615)(3 1417216 1449984)((0 0)1482488)(0 2147450880)(0#4 8#5)(5(1 44)4096 140737479966719)(4(1 44)16)((1 44)0)(9#9(0 264))(6#9(0 264))((0 0)2147446784)(0 17592186048512)(7#12#13#9(0 264))((0 0)1417216)(0 32768)(7#15#16#9(0 264))(7#4(0 8)#9(0 264))((1 10)0)(7#9(0 264)#19(0 24))((1 2)-4368)(0 4368)(7#9(0 264)#21#22)(5(0 24)1 4611686018427387904)((1 2)-72)(0#25 8(1 23))((1 2)-64)(0#27 8(1 22))((1 2)-56)(0#29 8(1 21))((1 2)-48)(0#31 8(1 20))((1 2)-40)(0#33 8(1 19))((1 2)-32)(0#35 8(1 18))((1 2)-24)(0#37 8(1 9))((1 2)-16)(0#39 8(1 8))((1 2)-8)(0#41 8(1 1))(0#19 8(0 0))((1 10)8)(0#44 8(0 0))((1 10)16)(0#46 8(0 0))(9#19(0 24))(6#19(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#52 2147450880)(1#53(0 3))(7#12#13#19(0 24))(0 4296)(9#21#56)(6#21#22)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#21#22#19(0 24))(5(0 23)1 4611686018427387904)(2 0(1 10)(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strres_xasan_R1 342%positive "(1040424((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(0 263)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 18)(0 264)(0 0)(0 22)(0 0)#2(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#3#6#7#8#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#42#3#6#43#45#47#48#49#50#51#54#55#57#58#59#60#61)56(((1 2)-4368#22)((1 10)0(0 24)))()(0 23))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strres_xasan_R1 18%positive "(((1 44)(0 264)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_strres_xasan_R1 496%positive "((0(0(1040164 1040656 1414360 524856 1387168 1388196))(4#62(1 0)))(((524856((1(0 1040552))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(0 263))(10(1 44))(11#63)(12(0 1))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 44))(19#63)(20(0 0))(21(0 22))(22(0 0))(23#2)(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#62#3#6#7#8#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#42#3#6#43#45#47#48#49#50#51#54#55#57#58#59#60#61))(1 524856)))()())"%pstring.
