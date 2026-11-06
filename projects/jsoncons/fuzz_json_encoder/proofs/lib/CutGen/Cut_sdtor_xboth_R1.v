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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_sdtor_xboth_T Cut_sdtor_xboth_R0.
Definition dict_Cut_sdtor_xboth_R1 : CCD.pt := CCD.mk_table 864%positive "((2 0(1 2)(0 -48))(0 2147450880)(3 1433600 1466368)((0 0)1497016)(0#4 8#2)(5(0 12)1 4611686018427387904)((1 2)-40)(0#7 8(1 19))((1 2)-32)(0#9 8(1 18))((1 2)-24)(0#11 8(1 9))((1 2)-16)(0#13 8(1 8))((1 2)-8)(0#15 8(1 1))((1 10)32)(0 6948560)(0#17 8#18)((1 10)264)(0#20 8(1 32))((1 10)272)(0 16384)(0#22 8#23)((1 10)136)(0#25 8#18)((1 10)144)(0#27 8(0 0))((1 10)152)(0#29 8(0 0))((1 10)160)(0#31 8(0 0))((1 10)176)(0#33 8(0 0))((1 10)200)(0#35 8(0 0))((1 10)0)((1 10)88)(6#37(0 592))(5(1 10)7094272 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#42 2147450880)(1#43(0 74))((0 0)2147446784)(0 17592186048512)(7#45#46#37(0 592))(5(1 32)4096 140737479966720)(4(1 32)16)((1 2)-4224)(0 4184)(9#50#51)(0 4224)(6#50#53)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(7#50#53#37(0 592))((1 32)0)(7#50#53#58#23)(7#37(0 592)#58#23)(7#45#46#58#23)(5(0 11)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_sdtor_xboth_R1 355%positive "(733552((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 9)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 18)#2(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#3#5#6#8#10#12#14#16#3#5#19#21#24#26#28#30#32#34#36(9#37(0 32))(9#38(0 8))#39#40#41#44#47#48#49#52#54#55#56#57#59#60#61)56(((1 2)-4224#53)((1 10)0(0 592)))()(0 11))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_sdtor_xboth_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xboth_R1 593%positive "((0(0(733456 1046256 534160 1402040 1403068))(4#62(1 0)))(((534160((1(0 1076560))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(2 0(1 10)(0 88)))(9(0 0))(10(0 0))(11#18)(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#62(0#38 8(0 1449912))#8#10#12#14#16(0((1 10)24)8(0 1450008))(0((1 10)8)8(0 1434808))#3#5#6#3#5#19#21#24#26#28#30#32#34#36(9#37(0 8))(9((1 10)16)(0 8))#39#40#41#44#47#48#49#52#54#55#56#57#59#60#61))(1 534160)))()())"%pstring.
