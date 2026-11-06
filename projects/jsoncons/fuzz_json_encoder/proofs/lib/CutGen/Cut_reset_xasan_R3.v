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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_reset_xasan_T Cut_reset_xasan_R0 Cut_reset_xasan_R1 Cut_reset_xasan_R2.
Definition dict_Cut_reset_xasan_R3 : CCD.pt := CCD.mk_table 1436%positive "((2 0(1 10)(0 248))(2 0(1 10)(0 168))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#5 8#3)(5(0 38)1 4611686018427387904)((1 10)144)(0#8 4(0 0))((1 10)160)(0#10 8(0 1))((1 10)212)(0#12 1(0 0))((1 10)211)(0#14 1(0 1))((1 10)208)(0#16 1(0 1))(#1 0)(0#18 8(1 32))(#1 8)(2 0(1 32)(0 1))(0#20 8#21)(#1 16)(2 0(1 32)(1 34))(0#23 8#24)(5(0 39)1 4611686018427387904)((1 2)-33)(0#27 1(0 0))(5(0 40)1 4611686018427387904)((1 2)-32)(0#30 8(1 18))((1 2)-24)(0#32 8(1 9))((1 2)-16)(0#34 8(1 8))((1 2)-8)(0#36 8(1 1))((1 10)168)(9#38(0 16))((1 10)0)(6#40(0 272))(5(1 10)7077888 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#44 2147450880)(1#45(0 34))(2 0(1 10)(0 211))(2 6#47(0 3))(#48 2147450880)(1#49(0 1))(2 0(1 10)(0 212))(2 6#51(0 3))(#52 2147450880)(1#53(0 1))((0 0)2147446784)(0 17592186048512)(7#55#56#40(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 4096)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#62(1 34))(5#63 0 4096)((1 2)-8288)(0 8255)(9#65#66)(0 8288)(6#65#68)(5(1 2)140735332491360 140737488355328)(4(1 2)16)(7#65#68#40(0 272))((1 32)0)(7#65#68#73(1 34))(7#40(0 272)#73(1 34))(2 6(1 32)(0 3))(#76 2147450880)(2 0(1 34)(0 7))(2 6#78(0 3))(7#45(0 34)#77#79)(7#49(0 1)#77#79)(7#53(0 1)#77#79)(7#45(0 34)#40(0 272))(7#49(0 1)#40(0 272))(7#53(0 1)#40(0 272))(7#40(0 272)#77#79)(#4#6#7#9#11#13#15#17#4#6#19#22#25#26#28#4#6#29#31#33#35#37#4#6#39#41#42#43#46#50#54#57#58#59#60#61#64#67#69#70#71#72#74#75#80#81#82#83#84#85#86))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_reset_xasan_R3 310%positive "(844764((1 0)(1 67)(2 0(1 2)(0 -48))(1 3)(1 4)(1 68)(1 69)(1 70)(1 10)#1#2(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 78)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 79)(1 80)(1 81)(1 82))#87 83(((1 2)-8288#68)((1 10)144(0 4))((1 10)160(0 8))((1 10)208(0 1))((1 10)211(0 2))((1 10)256(0 8)))()(0 37))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_reset_xasan_R3 17%positive "(((1 32)(1 34)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xasan_R3 390%positive "((0(0(844500 844784 730684 841320 526044 1387168 1388196))(1 0))(((844784((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 68))(6(1 69))(7(1 70))(8(1 8))(9(1 9))(10#2)(11(1 72))(12(1 73))(13(1 74))(14(1 75))(15(1 76))(16(1 77))(17(1 78))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 79))(29(1 80))(30(1 81))(31(1 82)))()#87)(1 844784)))()())"%pstring.
