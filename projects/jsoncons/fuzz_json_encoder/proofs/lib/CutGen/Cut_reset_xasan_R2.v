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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_reset_xasan_T Cut_reset_xasan_R0 Cut_reset_xasan_R1.
Definition dict_Cut_reset_xasan_R2 : CCD.pt := CCD.mk_table 1213%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 248))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#5 8#3)(#2 0)(0#7 8(1 32))(#2 8)(2 0(1 32)(0 1))(0#9 8#10)(#2 16)(2 0(1 32)(1 34))(0#12 8#13)(5(0 39)1 4611686018427387904)((1 2)-33)(0#16 1(0 0))(5(0 40)1 4611686018427387904)((1 2)-32)(0#19 8(1 18))((1 2)-24)(0#21 8(1 9))((1 2)-16)(0#23 8(1 8))((1 2)-8)(0#25 8(1 1))((1 10)144)((1 10)160)((1 10)168)(9#29(0 16))((1 10)208)((1 10)211)((1 10)0)(6#33(0 272))(5(1 10)7077888 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#37 2147450880)(1#38(0 34))(2 0(1 10)(0 211))(2 6#40(0 3))(#41 2147450880)(1#42(0 1))(2 0(1 10)(0 212))(2 6#44(0 3))(#45 2147450880)(1#46(0 1))((0 0)2147446784)(0 17592186048512)(7#48#49#33(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 4096)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#55(1 34))(5#56 0 4096)((1 2)-8288)(0 8255)(9#58#59)(0 8288)(6#58#61)(5(1 2)140735332491360 140737488355328)(4(1 2)16)(7#58#61#33(0 272))((1 32)0)(7#58#61#66(1 34))(7#33(0 272)#66(1 34))(2 6(1 32)(0 3))(#69 2147450880)(2 0(1 34)(0 7))(2 6#71(0 3))(7#38(0 34)#70#72)(7#42(0 1)#70#72)(7#46(0 1)#70#72)(7#38(0 34)#33(0 272))(7#42(0 1)#33(0 272))(7#46(0 1)#33(0 272))(7#33(0 272)#70#72)(5(0 38)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_reset_xasan_R2 463%positive "(844616((1 0)(1 51)#1(1 3)(1 4)(1 52)(1 53)(1 54)(1 10)#2(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 62)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 63)(1 64)(1 65)(1 66))(#4#6#8#11#14#15#17#4#6#18#20#22#24#26#4#6(9#27(0 4))(9#28(0 8))#30(9#31(0 1))(9#32(0 2))#34#35#36#39#43#47#50#51#52#53#54#57#60#62#63#64#65#67#68#73#74#75#76#77#78#79)67(((1 2)-8288#61)((1 10)144(0 4))((1 10)160(0 8))((1 10)208(0 1))((1 10)211(0 2))((1 10)256(0 8)))()(0 38))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_reset_xasan_R2 17%positive "(((1 32)(1 34)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_reset_xasan_R2 603%positive "((0(0(844500 844784 730684 841320 526044 1387168 1388196))(4#80(1 0)))(((526044((1(0 844764))(2#1)(3(1 3))(4(1 4))(5(1 52))(6(1 53))(7(1 54))(8(1 10))(9#2)(10(2 0(1 10)(0 168)))(11(0 0))(12(0 16))(13(1 58))(14(1 59))(15(1 60))(16(1 61))(17(1 62))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 63))(29(1 64))(30(1 65))(31(1 66)))()(#80(0#27 4(0 0))(0#28 8(0 1))(0((1 10)212)1(0 0))(0#32 1(0 1))(0#31 1(0 1))#4#6#8#11#14#15#17#4#6#18#20#22#24#26#4#6#30#34#35#36#39#43#47#50#51#52#53#54#57#60#62#63#64#65#67#68#73#74#75#76#77#78#79))(1 526044)))()())"%pstring.
