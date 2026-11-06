(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm4CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import StrtodAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strtod_xasan_T Cut_strtod_xasan_R0.
Definition dict_Cut_strtod_xasan_R1 : CCDD.pt := CCDD.mk_table 802%positive "((0 -272)(2 0(1 2)#1)(0 7069712)((1 2)-264)(0#4 8(1 34))(0 1152921504606846976)(5#6 1 4611686018427387904)((1 2)-88)(0 18446744073709551615)(0#8 8#9)((1 2)-72)(0#11 8(0 0))((1 2)-80)(0#13 8(0 0))((1 2)-256)(0#15 8#9)((1 2)-184)(0#17 8(1 10))((1 2)-40)(0#19 8(1 32))((1 2)-32)(0#21 8(1 18))((1 2)-24)(0#23 8(1 9))((1 2)-16)(0#25 8(1 8))((1 2)-8)(0#27 8(1 1))(5(1 2)140735332492016 140737488355328)(4(1 2)16)((1 2)-8944)(0 8944)(6#31#32)(0 8680)(9#31#34)((1 2)-248)(9#36(0 64))((1 2)-176)(9#38(0 88))((1 2)-64)(9#40(0 24))((0 0)7069712)(0#42 8(1 32))(5(1 10)4096 140737488355328)(5(1 33)1 67108864)((1 11)0)(6#46(0 8))(7#46(0 8)#31#32)(5(1 11)32 140737488355320)(7#46(0 8)#42(0 8))((1 4)-164)(7#46(0 8)#51(0 4))(7#51(0 4)#31#32)(5(1 4)6938576 6938577)(0 1152921504606846975)(5#55 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_strtod_xasan_R1 362%positive "(1383840((1 0)(1 35)#2(1 3)(1 4)(1 36)(1 37)(1 38)(1 11)(1 10)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))(#5#7#10#12#14#16#18#20#22#24#26#28#29#30(3 65536 1449984)#33#35#37#39#41#43#44#45#47(9#46(0 8))#48#49#50#52#53#54)51(((1 2)-8944#32)((1 11)0(0 8))((1 4)-164(0 4)))()#55)"%pstring.
Definition BL1 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_strtod_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CAD.pout := CCDD.dec_pout_t dict_Cut_strtod_xasan_R1 501%positive "((0(0(1383752 1383908 1366320 1335140 1387168 1388196))(4#56(1 0)))(((1335140((1(0 1383876))(2#2)(3(1 3))(4(1 4))(5(1 36))(6(1 37))(7(1 38))(8(1 11))(9(1 10))(10(1 39))(11(1 40))(12(1 34))(13(1 10))(14(1 10))(15(1 44))(16(1 45))(17(1 46))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 47))(29(1 48))(30(1 49))(31(1 50)))()(#56(0#46 8(1 34))#5#7#10#12#14#16#18#20#22#24#26#28#29#30#33#35#37#39#41#43#44#45#47#48#49#50#52#53#54))(1 1335140)))()())"%pstring.
