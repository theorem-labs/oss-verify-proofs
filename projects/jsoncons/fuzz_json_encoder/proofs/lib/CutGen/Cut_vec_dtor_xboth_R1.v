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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_dtor_xboth_T Cut_vec_dtor_xboth_R0.
Definition dict_Cut_vec_dtor_xboth_R1 : CCD.pt := CCD.mk_table 2000%positive "((2 0(1 2)(0 -32))(0 2147450880)(2 6(1 10)(0 3))(2 0#3#2)((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)#2(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#4(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(3 1459384 1463120)((0 0)1497016)(0#7 8#2)(5(0 8)1 4611686018427387904)((1 32)8)(0#10 8(1 33))(2 0(1 34)(0 1))(5#12 1 1)(5(1 34)0 0)(2 0(1 33)(1 34))(2 1(1 33)#15)(2 4#16(0 1))(5#17 1 1)((1 2)-32)(0#19 8(1 18))((1 2)-24)(0#21 8(1 9))((1 2)-16)(0#23 8(1 8))((1 2)-8)(0#25 8(1 1))((1 10)0)(0#27 8(1 32))(5(1 10)1048576 140737488355320)(4(1 10)8)(#3 2147450880)(1#31(0 1))((0 0)2147446784)(0 17592186048512)(7#33#34#27(0 8))((1 32)0)(0#36 8(1 33))((1 32)16)(2 0(1 33)(1 35))(0#38 8#39)(6#36(0 24))(5(1 32)1048576 140737488354816)(4(1 32)8)(2 6(1 32)(0 3))(#44 2147450880)(1#45(0 3))(7#33#34#36(0 24))(5(1 33)17594333495296 140737479966720)(4(1 33)16)(5(1 35)1 4096)(4 0(0 -1)(1 34))(2 0#51(1 35))(5#52 0 4096)(5(1 34)0 4096)((1 2)-4192)(0 4152)(9#55#56)(0 4192)(6#55#58)(5(1 2)140735332487264 140737488355328)(4(1 2)16)(7#55#58#36(0 24))(7#55#58#27(0 8))(7#27(0 8)#36(0 24))((1 33)0)(7#55#58#65(1 35))(7#36(0 24)#65(1 35))(7#27(0 8)#65(1 35))(2 6(1 33)(0 3))(#69 2147450880)(2 0(1 35)(0 7))(2 6#71(0 3))(7#45(0 3)#70#72)(7#31(0 1)#70#72)(7#36(0 24)#70#72)(7#27(0 8)#70#72)((1 2)-4192#58)((1 32)0(0 24))(#77#78)((1 33)(1 35))(732544 732784 1046256 733160 732972 1402040 1403068)(0#81)(5(0 7)1 4611686018427387904)(4#83(1 0))(0#82#84)(0 732668)(1#86)(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9#2)(10(1 32))(11(0 0))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#4)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117)(1 732972)(5#51 18446744073709547520 18446744073709551615)(2 0#51(0 -1))(5#121 0 18446744073709551614)(5(1 34)1 4096)(5#17 0 0))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xboth_R1 148%positive "(732640#5(#6#8#9#11#13#14#18#20#22#24#26#28#29#30#32#35#37#40#41#42#43#46#47#48#49#50#53#54#57#59#60#61#62#63#64#66#67#68#73#74#75#76)56#79()(0 7))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xboth_R1 6%positive "(#80)"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xboth_R1 160%positive "(#85(((732972#118()(#83#6#8#9#11#13#14#18#20#22#24#26#28#29#30#32#35#37#40#41#42#43#46#47#48#49#50#53#54#57#59#60#61#62#63#64#66#67#68#73#74#75#76))#119))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xboth_R1 159%positive "(732640#5(#6#8#9#11#120#120#122#123#124#20#22#24#26#28#29#30#32#35#37#40#41#42#43#46#47#48#49#50#53#54#57#59#60#61#62#63#64#66#67#68#73#74#75#76)56#79()(0 7))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xboth_R1 6%positive "(#80)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xboth_R1 171%positive "(#85(((732972#118()(#83#6#8#9#11#120#120#122#123#124#20#22#24#26#28#29#30#32#35#37#40#41#42#43#46#47#48#49#50#53#54#57#59#60#61#62#63#64#66#67#68#73#74#75#76))#119))()())"%pstring.
