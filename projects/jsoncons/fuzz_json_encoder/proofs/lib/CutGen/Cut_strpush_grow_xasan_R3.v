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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strpush_grow_xasan_T Cut_strpush_grow_xasan_R0 Cut_strpush_grow_xasan_R1 Cut_strpush_grow_xasan_R2.
Definition dict_Cut_strpush_grow_xasan_R3 : CCD.pt := CCD.mk_table 1014%positive "((4 0(0 4)(1 32))(2 0#1(0 -2))(2 6#2(0 3))(4 0(0 8)#3)(2 0#4(0 8))(4 0(0 2)(1 32))(2 0#6(0 -1))(3 1417216 1449984)((0 0)1482488)(0 2147450880)(0#9 8#10)(5(0 98)1 4611686018427387904)((1 44)0)(2#13#7 0)(5(0 99)1 4611686018427387904)(5(1 44)4096 140737479966719)(4(1 44)16)(6#13#5)((0 0)2147446784)(0 17592186048512)(7#19#20#13#5)((0 0)1417216)(0 32768)(7#22#23#13#5)(7#9(0 8)#13#5)((1 10)0)(7#13#5#26(0 24))((1 2)-4368)(0 4368)(7#13#5#28#29)((1 34)0)(7#13#5#31#6)(5(0 100)1 4611686018427387904)(2 0#6(0 1))(6 0 0 1#34)(2 9#35(0 1))(5#36 1 1)((1 2)-64)(0#38 8(1 22))((1 2)-56)(0#40 8(1 21))((1 2)-48)(0#42 8(1 20))((1 2)-40)(0#44 8(1 19))((1 2)-32)(0#46 8(1 18))((1 2)-24)(0#48 8(1 9))((1 2)-16)(0#50 8(1 8))((1 2)-8)(0#52 8(1 1))((1 10)8)((1 10)16)(5(1 32)12 33554432)(5(1 11)0 255)(5(1 34)4096 140737488355328)(4(1 34)16)(6#26(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(0 4304)(9#28#63)(6#28#29)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#28#29#26(0 24))(7#28#29#31#6)(7#26(0 24)#31#6)(2 0#6(1 44)))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strpush_grow_xasan_R3 438%positive "(1041524((1 0)(1 72)(2 0(1 2)(0 -64))(1 3)(1 4)(1 73)(1 74)(1 75)(1 11)(1 10)(1 76)(1 77)(1 78)(1 79)(1 80)(1 81)(1 82)(1 83)(1 34)#5#7#6(1 44)(1 23)(1 24)(1 25)(1 26)(1 27)(1 84)(1 85)(1 86)(1 87))(#8#11#12#8#11#14#15#8#11#16#17(9#13#5)#18#21#24#25#27#30#32#33#37#39#41#43#45#47#49#51#53#8#11(0#26 8#34)(0#54 8#7)(0#55 8(1 34))#56#57#58#59(9#26(0 24))#60#61#62#64#65#66#67#68#69#70)88(((1 2)-4368#29)((1 10)0(0 24))((1 44)0#5))()(0 97))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strpush_grow_xasan_R3 13%positive "(((1 44)#5))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_strpush_grow_xasan_R3 661%positive "((0(0(1041292 1041596 1414360 524856 1031544 1387168 1388196))(1 0))(((1041596((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 73))(6(1 74))(7(1 75))(8(1 8))(9(1 9))(10(2 0#71(0 -1)))(11#6)(12(1 78))(13(1 79))(14(1 80))(15(1 81))(16(1 82))(17(1 83))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 84))(29(1 85))(30(1 86))(31(1 87)))()((0(#71 0)1(0 0))(0(#71 -1)1(1 11))(0#54 8#6)(0#55 8(1 44))(0#26 8(2 0#4(0 9)))#8#11#12#8#11#14#15#8#11#16#17(9#13#7)(9(#71 1)(2 0(2 0(4 0(0 -2)(1 32))#4)(0 7)))#18#21#24#25#27#30#32#33#37#39#41#43#45#47#49#51#53#8#11#56#57#58#59#60#61#62#64#65#66#67#68#69#70))(1 1041596)))()())"%pstring.
