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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strres_xboth_T Cut_strres_xboth_R0 Cut_strres_xboth_R1.
Definition dict_Cut_strres_xboth_R2 : CCD.pt := CCD.mk_table 835%positive "((3 1433600 1466368)((0 0)1497016)(0 2147450880)(0#2 8#3)((1 44)0)(1#5(0 1))(5(0 23)1 4611686018427387904)(5(1 44)4096 140737479966719)(4(1 44)16)(9#5(0 264))(6#5(0 264))((0 0)2147446784)(0 17592186048512)(7#12#13#5(0 264))((0 0)1433600)(0 36864)(7#15#16#5(0 264))(7#2(0 8)#5(0 264))((1 10)0)(7#5(0 264)#19(0 24))((1 2)-4368)(0 4368)(7#5(0 264)#21#22)(5(0 24)1 4611686018427387904)((1 2)-72)(0#25 8(1 23))((1 2)-64)(0#27 8(1 22))((1 2)-56)(0#29 8(1 21))((1 2)-48)(0#31 8(1 20))((1 2)-40)(0#33 8(1 19))((1 2)-32)(0#35 8(1 18))((1 2)-24)(0#37 8(1 9))((1 2)-16)(0#39 8(1 8))((1 2)-8)(0#41 8(1 1))((1 10)8)(0#43 8(0 0))((1 10)16)(6#19(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#49 2147450880)(1#50(0 3))(7#12#13#19(0 24))(0 4296)(9#21#53)(6#21#22)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#21#22#19(0 24)))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strres_xboth_R2 425%positive "(1055264((1 0)(1 56)(2 0(1 2)(0 -80))(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)(0 263)(1 44)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 44)(2 0(1 10)(0 1))(0 0)(0 22)(0 0)(0 18446744073709551615)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#1#4#6#7#1#4#8#9#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#42#1#4(0#19 8(0 0))#44(0#45 8(0 0))(9#19(0 24))#46#47#48#51#52#54#55#56#57#58)72(((1 2)-4368#22)((1 10)0(0 24)))()(0 22))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strres_xboth_R2 18%positive "(((1 44)(0 264)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_strres_xboth_R2 525%positive "((0(0(1054876 1055368 1429232 527112 1402040 1403068))(1 0))(((1055368((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(0 265))(11(1 61))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()((0#45 8(1 44))#44(0#19 8(0 265))#1#4#6#7#1#4#8#9#10#11#14#17#18#20#23#24#26#28#30#32#34#36#38#40#42#1#4#46#47#48#51#52#54#55#56#57#58))(1 1055368)))()())"%pstring.
