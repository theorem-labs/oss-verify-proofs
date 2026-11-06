(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_wd_xasan_T Cut_wd_xasan_R0.
Definition dict_Cut_wd_xasan_R1 : CCD.pt := CCD.mk_table 1191%positive "((2 0(1 2)(0 -96))(0 1048576)(5#2 1 4611686018427387904)((1 2)-88)(0#4 8(1 48))((1 2)-80)(0#6 8(1 24))((1 2)-72)(0#8 8(1 23))((1 2)-64)(0#10 8(1 22))((1 2)-56)(0#12 8(1 21))((1 2)-48)(0#14 8(1 20))((1 2)-40)(0#16 8(1 19))((1 2)-32)(0#18 8(1 18))((1 2)-24)(0#20 8(1 9))((1 2)-16)(0#22 8(1 8))((1 2)-8)(0#24 8(1 1))((1 2)-96)(0#26 8(0 0))(3 1444792 1448528)((0 0)1482488)(0 2147450880)(0#29 8#30)((0 0)1482496)(0#32 4(0 1))((1 11)0)(0#34 8(1 32))(5(1 11)7077888 140737488355320)(4(1 11)8)(2 6(1 11)(0 3))(#38 2147450880)(1#39(0 1))((0 0)2147446784)(0 17592186048512)(7#41#42#34(0 8))(5(1 32)7077888 140737479966696)(4(1 32)8)((1 32)0)(7#41#42#46(0 24))(7#34(0 8)#46(0 24))((1 10)0)(0#49 1(0 0))((1 10)4)(0#51 4(0 0))((1 10)8)(0#53 1(1 33))(5(1 33)0 255)(9#49(0 12))(5(1 10)7077888 140737479966708)(7#41#42#49(0 12))(2 6(1 10)(0 3))(#59 2147450880)(0#60 1(0 0))(2 0(1 10)(0 4))(2 6#62(0 3))(#63 2147450880)(0#64 1(0 0))(2 0(1 10)(0 8))(2 6#66(0 3))(#67 2147450880)(0#68 1(0 0))((1 2)-12800)(0 12704)(9#70#71)(9#6(0 0))(0 12800)(6#70#74)(5(1 2)140735332495872 140737488355328)(4(1 2)32)(7#41#42#70#74)(7#70#74#34(0 8))(7#70#74#46(0 24))(7#70#74#49(0 12))(0 1048575)(5#82 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_wd_xasan_R1 342%positive "(772216((1 0)(1 1)#1(1 3)(1 4)(1 5)(1 6)(1 7)(1 2)#1(1 10)(1 11)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 11)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3#5#7#9#11#13#15#17#19#21#23#25#27#28#31#33#35#36#37#40#43#44#45#47#48#50#52#54#55#56#57#58#61#65#69#72#73#75#76#77#78#79#80#81)49(((1 2)-12800#74))()#82)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_wd_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_wd_xasan_R1 542%positive "((0(0(772144 773452 419004 825600 540344 772212 773608 1387168 1388196))(4#83(1 0)))(((419004((1(0 772256))(2#1)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 2))(9#1)(10(0 768))(11(0 1482488))(12(0 1))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 11))(21(1 10))(22(1 22))(23(1 23))(24#30)(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#83#3#5#7#9#11#13#15#17#19#21#23#25#27#28#31#33#35#36#37#40#43#44#45#47#48#50#52#54#55#56#57#58#61#65#69#72#73#75#76#77#78#79#80#81))(1 419004)))()())"%pstring.
