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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_reset_xboth_T Cut_reset_xboth_R0.
Definition dict_Cut_reset_xboth_R1 : CCD.pt := CCD.mk_table 2297%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 248))(0 2147450880)((1 0)(1 35)#1(1 3)(1 4)(1 36)(1 37)(1 38)(1 10)#2(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))(3 1459384 1463120)((0 0)1497016)(0#6 8#3)(5(0 40)1 4611686018427387904)((1 10)256)(0#9 8(1 32))(2 0(1 33)(0 1))(5#11 1 1)(5(1 33)0 0)(2 0(1 32)(1 33))(2 1(1 32)#14)(2 4#15(0 1))(5#16 1 1)((1 2)-32)(0#18 8(1 18))((1 2)-24)(0#20 8(1 9))((1 2)-16)(0#22 8(1 8))((1 2)-8)(0#24 8(1 1))((1 10)248)(0#26 8(1 32))((1 10)264)(2 0(1 32)(1 34))(0#28 8#29)((1 10)144)(9#31(0 4))((1 10)160)(9#33(0 8))((1 10)168)(9#35(0 16))((1 10)208)(9#37(0 1))((1 10)211)(9#39(0 2))((1 10)0)(6#41(0 272))(5(1 10)7094272 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#45 2147450880)(1#46(0 34))(2 0(1 10)(0 211))(2 6#48(0 3))(#49 2147450880)(1#50(0 1))(2 0(1 10)(0 212))(2 6#52(0 3))(#53 2147450880)(1#54(0 1))((0 0)2147446784)(0 17592186048512)(7#56#57#41(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 4096)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#63(1 34))(5#64 0 4096)((1 2)-8288)(0 8232)(9#66#67)((1 2)-48)(9#69(0 16))(0 8288)(6#66#71)(5(1 2)140735332491360 140737488355328)(4(1 2)16)(7#66#71#41(0 272))((1 32)0)(7#66#71#76(1 34))(7#41(0 272)#76(1 34))(2 6(1 32)(0 3))(#79 2147450880)(2 0(1 34)(0 7))(2 6#81(0 3))(7#46(0 34)#80#82)(7#50(0 1)#80#82)(7#54(0 1)#80#82)(7#46(0 34)#41(0 272))(7#50(0 1)#41(0 272))(7#54(0 1)#41(0 272))(7#41(0 272)#80#82)((1 2)-8288#71)((1 10)144(0 4))((1 10)160(0 24))((1 10)208(0 1))((1 10)211(0 2))((1 10)256(0 8))(#90#91#92#93#94#95)((1 32)(1 34))(861128 861388 733160 858048 1402040 1403068)(0#98)(5(0 39)1 4611686018427387904)(4#100(1 0))(0#99#101)(0 861192)(1#103)(2#1)(3(1 3))(4(1 4))(5(1 36))(6(1 37))(7(1 38))(8(1 10))(9#2)(10#2)(2 0(1 2)(0 -33))(11#114)(12(1 41))(13(1 42))(14(1 43))(15(1 44))(16(1 45))(17(1 46))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 47))(29(1 48))(30(1 49))(31(1 50))(#104#105#106#107#108#109#110#111#112#113#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132#133#134#135)((1 2)-33)(0#137 1(0 0))(9#69(0 15))(1 858048)(5#63 18446744073709547520 18446744073709551615)(2 0#63(0 -1))(5#142 0 18446744073709551614)(5(1 33)1 4096)(5#16 0 0))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_reset_xboth_R1 162%positive "(861176#4(#5#7#8#10#12#13#17#19#21#23#25#5#7#27#30#32#34#36#38#40#42#43#44#47#51#55#58#59#60#61#62#65#68#70#72#73#74#75#77#78#83#84#85#86#87#88#89)51#96()(0 39))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_reset_xboth_R1 6%positive "(#97)"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xboth_R1 180%positive "(#102(((858048#136()(#100#138#5#7#8#10#12#13#17#19#21#23#25#5#7#27#30#32#34#36#38#40#42#43#44#47#51#55#58#59#60#61#62#65#68#139#72#73#74#75#77#78#83#84#85#86#87#88#89))#140))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_reset_xboth_R1 173%positive "(861176#4(#5#7#8#10#141#141#143#144#145#19#21#23#25#5#7#27#30#32#34#36#38#40#42#43#44#47#51#55#58#59#60#61#62#65#68#70#72#73#74#75#77#78#83#84#85#86#87#88#89)51#96()(0 39))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_reset_xboth_R1 6%positive "(#97)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xboth_R1 191%positive "(#102(((858048#136()(#100#138#5#7#8#10#141#141#143#144#145#19#21#23#25#5#7#27#30#32#34#36#38#40#42#43#44#47#51#55#58#59#60#61#62#65#68#139#72#73#74#75#77#78#83#84#85#86#87#88#89))#140))()())"%pstring.
