(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_push_back_x_sso_full_xboth_T Cut_str_push_back_x_sso_full_xboth_R0.
Definition dict_Cut_str_push_back_x_sso_full_xboth_R1 : CCD.pt := CCD.mk_table 797%positive "((2 0(1 2)(0 -64))(2 0(1 10)(0 1))(3 1433600 1466368)((0 0)1497016)(0 2147450880)(0#4 8#5)(5(1 44)4096 140737479966719)(4(1 44)16)((1 44)0)(9#9(0 48))(6#9(0 48))((0 0)2147446784)(0 17592186048512)(7#12#13#9(0 48))((0 0)1433600)(0 36864)(7#15#16#9(0 48))(7#4(0 8)#9(0 48))((1 10)0)(7#9(0 48)#19(0 24))((1 2)-4368)(0 4368)(7#9(0 48)#21#22)(5(0 100)1 4611686018427387904)((1 2)-64)(0#25 8(1 22))((1 2)-56)(0#27 8(1 21))((1 2)-48)(0#29 8(1 20))((1 2)-40)(0#31 8(1 19))((1 2)-32)(0#33 8(1 18))((1 2)-24)(0#35 8(1 9))((1 2)-16)(0#37 8(1 8))((1 2)-8)(0#39 8(1 1))(0#19 1(0 44))(5(1 11)0 255)((1 10)1)(2#43(0 22)0)(9#19(0 24))(6#19(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)(0 4304)(9#21#49)(6#21#22)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#21#22#19(0 24))(5(0 99)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_sso_full_xboth_R1 348%positive "(1056200((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 11)(1 10)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(0 48)(0 22)(0 23)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#3#6#7#8#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#3#6#41#42#44#45#46#47#48#50#51#52#53#54)56(((1 2)-4368#22)((1 10)0(0 24))((1 44)0(0 48)))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_sso_full_xboth_R1 17%positive "(((1 44)(0 48)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_sso_full_xboth_R1 499%positive "((0(0(1056004 1056308 1429232 527112 1046256 1402040 1403068))(4#55(1 0)))(((527112((1(0 1056216))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 11))(9(1 10))(10(1 44))(11#2)(12(0 22))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#2)(19(0 48))(20(0 22))(21(0 23))(22(1 44))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#55#3#6#7#8#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#3#6#41#42#44#45#46#47#48#50#51#52#53#54))(1 527112)))()())"%pstring.
