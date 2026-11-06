(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_annotate_casan_T.
Definition dict_Cut_annotate_casan_R0 : CCD.pt := CCD.mk_table 1094%positive "((807940 726664 808492 726504 808064 726788 808592 726624 535644 1330948 1331976)(0#1)(5(0 8)1 4611686018427387904)(4#3(1 0))(0#2#4)(2 0(1 2)(0 -16))(2#6)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 32))(2 0(1 32)(1 34))(11#16)(2 0(1 32)(1 33))(12#18)(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-16)(0#36 8(1 8))((1 2)-8)(0#38 8(1 1))(3 1388760 1392480)((0 0)1427896)(0 2147450880)(0#41 8#42)((1 10)0)(0#44 8(1 32))((1 10)16)(0#46 8#16)(5(1 10)1048576 140737488355304)(4(1 10)8)(2 6(1 10)(0 3))(#50 2147450880)(1#51(0 3))((0 0)2147446784)(0 17592186048512)(7#53#54#44(0 24))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#59(1 34))(5#60 0 4096)(5(1 33)0 4096)((1 2)-4112)(0 4096)(9#63#64)(0 4112)(6#63#66)(5(1 2)140735332487184 140737488355328)(4(1 2)16)(7#63#66#44(0 24))((1 10)8)(0#71 8#18)(5(1 11)0 4096)(#3#37#39#40#43#45#47#48#49#52#55#56#57#58#61#62#65#67#68#69#70#72#73)(1 535644)(2 0(1 11)(1 32))(15(1 15)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_casan_R0 157%positive "(#5(((535644((1(0 808052))#7#8#9#10#11#12#13#14#15#17#19(13(2 0(1 11)#18))(14(1 32))(15#16)#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()#74)#75))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_casan_R0 150%positive "(#5(((535644((1(0 726776))#7#8#9#10#11#12#13#14#15#17(12#76)(13#18)(14#16)(15(1 32))#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()#74)#75))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_casan_R0 231%positive "(#5(((535644((1(0 808580))#7#8#9#10#11#12#13#14#15#17(12#16)(13#76)(14(2 6(2 0(1 10)(0 16))(0 3)))#77#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()(#3#37#39#40#43#45#47#48#49#52#55#56#57#58#61#62#65#67#68#69#70#73))#75))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_casan_R0 226%positive "(#5(((535644((1(0 726612))#7#8#9#10#11#12#13#14#15#17#19(13#16)(14(2 6(2 0(1 10)(0 8))(0 3)))#77#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()(#3#37#39#40#43#45#47#48#49#52#55#56#57#58#61#62#65#67#68#69#70#72))#75))()())"%pstring.
