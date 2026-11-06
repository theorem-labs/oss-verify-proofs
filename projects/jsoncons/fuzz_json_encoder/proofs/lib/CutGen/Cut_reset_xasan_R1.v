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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_reset_xasan_T Cut_reset_xasan_R0.
Definition dict_Cut_reset_xasan_R1 : CCD.pt := CCD.mk_table 1189%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 248))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#5 8#3)(5(0 40)1 4611686018427387904)((1 10)256)(0#8 8(1 32))((1 2)-32)(0#10 8(1 18))((1 2)-24)(0#12 8(1 9))((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))((1 10)248)(0#18 8(1 32))((1 10)264)(2 0(1 32)(1 34))(0#20 8#21)((1 10)144)(9#23(0 4))((1 10)160)(9#25(0 8))((1 10)168)(9#27(0 16))((1 10)208)(9#29(0 1))((1 10)211)(9#31(0 2))((1 10)0)(6#33(0 272))(5(1 10)7077888 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#37 2147450880)(1#38(0 34))(2 0(1 10)(0 211))(2 6#40(0 3))(#41 2147450880)(1#42(0 1))(2 0(1 10)(0 212))(2 6#44(0 3))(#45 2147450880)(1#46(0 1))((0 0)2147446784)(0 17592186048512)(7#48#49#33(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 4096)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#55(1 34))(5#56 0 4096)((1 2)-8288)(0 8288)(6#58#59)(5(1 2)140735332491360 140737488355328)(4(1 2)16)(7#58#59#33(0 272))((1 32)0)(7#58#59#64(1 34))(7#33(0 272)#64(1 34))(2 6(1 32)(0 3))(#67 2147450880)(2 0(1 34)(0 7))(2 6#69(0 3))(7#38(0 34)#68#70)(7#42(0 1)#68#70)(7#46(0 1)#68#70)(7#38(0 34)#33(0 272))(7#42(0 1)#33(0 272))(7#46(0 1)#33(0 272))(7#33(0 272)#68#70)(5(0 39)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_reset_xasan_R1 431%positive "(844600((1 0)(1 35)#1(1 3)(1 4)(1 36)(1 37)(1 38)(1 10)#2(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))(#4#6#7#9#11#13#15#17#4#6#19#22#24#26#28#30#32#34#35#36#39#43#47#50#51#52#53#54#57(9#58(0 8256))#60#61#62#63#65#66#71#72#73#74#75#76#77)51(((1 2)-8288#59)((1 10)144(0 4))((1 10)160(0 8))((1 10)208(0 1))((1 10)211(0 2))((1 10)256(0 8)))()(0 39))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_reset_xasan_R1 17%positive "(((1 32)(1 34)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xasan_R1 558%positive "((0(0(844500 844784 730684 841320 526044 1387168 1388196))(4#78(1 0)))(((841320((1(0 844616))(2#1)(3(1 3))(4(1 4))(5(1 36))(6(1 37))(7(1 38))(8(1 10))(9#2)(10#2)(11(2 0(1 2)(0 -33)))(12(1 41))(13(1 42))(14(1 43))(15(1 44))(16(1 45))(17(1 46))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 47))(29(1 48))(30(1 49))(31(1 50)))()(#78(0((1 2)-33)1(0 0))#4#6#7#9#11#13#15#17#4#6#19#22#24#26#28#30#32#34#35#36#39#43#47#50#51#52#53#54#57(9#58(0 8255))#60#61#62#63#65#66#71#72#73#74#75#76#77))(1 841320)))()())"%pstring.
