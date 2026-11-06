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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fsinf_xasan_T Cut_fsinf_xasan_R0 Cut_fsinf_xasan_R1.
Definition dict_Cut_fsinf_xasan_R2 : CCDD.pt := CCDD.mk_table 2379%positive "((0 -8416)(2 0(1 2)#1)(0 2139095040)(0 4096)(0 7069712)(0 18446744073709550542)(0 1152921504606846975)(5#7 1 4611686018427387904)(0 1152921504606846976)(5#9 1 4611686018427387904)((1 10)8)(2 0(1 32)(0 3))(0#11 8#12)((1 2)-120)(0#14 8(1 33))((1 2)-6128)(0#16 8(0 0))((1 2)-112)(0#18 8(1 34))((1 2)-104)(0#20 8(1 27))((1 2)-96)(0#22 8(1 26))((1 2)-88)(0#24 8(1 25))((1 2)-80)(0#26 8(1 24))((1 2)-72)(0#28 8(1 23))((1 2)-64)(0#30 8(1 22))((1 2)-56)(0#32 8(1 21))((1 2)-48)(0#34 8(1 20))((1 2)-40)(0#36 8(1 19))((1 2)-32)(0#38 8(1 18))((1 2)-24)(0#40 8(1 9))((1 2)-16)(0#42 8(1 8))((1 2)-8)(0#44 8(1 1))(5(1 2)140735332491744 140737488355328)(4(1 2)16)(3 65536 1449984)((1 2)-8672)(0 8672)(6#49#50)(0 2544)(9#49#52)((1 2)-6120)(0 6000)(9#54#55)(6#11(0 8))(5(1 10)140735332483072 140737488355072)(7#11(0 192)#49#50)(5(1 32)4096 140737488355328)((1 10)184)(0 18446744073709551615)(0#61 8#62)((1 10)192)(0#64 8(0 0))((0 0)7069712)(0#66 8(1 33))((1 32)0)(7#68(0 4)#49#50)(7#68(0 4)#11(0 192))(0#68 1(0 105))((1 32)1)(0#72 1(0 110))((1 32)2)(0#74 1(0 102))((1 32)3)(0#76 1(0 0))((1 2)-8672#50)((1 10)8(0 8))(#78#79)(0 1152921504606846974)(5#81 1 4611686018427387904)(4#82(1 0))(1(1 1))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 0))(10#3)(11(0 73))(12(0 73))(13#4)(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(0 53))(19(1 19))(20#5)(21(1 10))(22#6)(23(0 1))(24(0 1))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(1 1369020)(2 0(1 32)(0 4))(0#11 8#115)(7#68(0 5)#49#50)(7#68(0 5)#11(0 192))(0#68 1(0 45))(0#72 1(0 105))(0#74 1(0 110))(0#76 1(0 102))((1 32)4)(0#123 1(0 0))(#8#10#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#67#69#70)(1366320 1366320 1366320 1366320 1369176 1312508 1369008 1369016 1369020 1368424 1371176 1371188 1371228 1371468 1371472 1371424 1371488 1368652 1368656 1368660 1387168 1388196)(0#126)(0#127(1 0))(0(4 1)#128)(0#127#129)(2(1 2))(5(1 36))(6(1 37))(7(1 38))(8(1 8))(9(1 9))(10(1 39))(11(1 40))(0 6384)(12#139)(13(1 33))(14(1 43))(15(1 44))(16(1 45))(17(1 46))(18(1 18))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(28(1 47))(29(1 48))(30(1 49))(31(1 50))(#84#131#86#87#132#133#134#135#136#137#138#140#141#142#143#144#145#146#101#147#148#149#150#151#107#108#109#152#153#154#155)(1 1369176)(#8#10#116#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#67#117#118))"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xasan_R2 298%positive "(1369020((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)(0 1)#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#10#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#63#65#67#69#70#71#73#75#77)35#80()#81)"%pstring.
Definition BL8 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xasan_R2 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints4.
Definition o8 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xasan_R2 261%positive "(#83(((1369020(#84#85#86#87#88#89#90#91(9(0 1))#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113)()(#82#8#10#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#63#65#67#69#70#71#73#75#77))#114))()())"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xasan_R2 307%positive "(1369020((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)#62#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#10#116#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#63#65#67#117#118#119#120#121#122#124)35#80()#81)"%pstring.
Definition BL9 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xasan_R2 3%positive "()"%pstring.
Definition hints9 : list (nat * CC.subst) := hints5.
Definition o9 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xasan_R2 270%positive "(#83(((1369020(#84#85#86#87#88#89#90#91(9#62)#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113)()(#82#8#10#116#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#45#46#47#48#51#53#56#57#58#59#60#63#65#67#117#118#119#120#121#122#124))#114))()())"%pstring.
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xasan_R2 200%positive "(1369028((1 0)(1 35)#2(1 3)(1 4)(1 36)(1 37)(1 38)(0 5)(0 1)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))#125 51#80()#81)"%pstring.
Definition BL10 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xasan_R2 3%positive "()"%pstring.
Definition hints10 : list (nat * CC.subst) := hints6.
Definition o10 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xasan_R2 38%positive "(#130(((1369176#156()#125)#157))()())"%pstring.
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xasan_R2 198%positive "(1369028((1 0)(1 35)#2(1 3)(1 4)(1 36)(1 37)(1 38)(0 5)#62(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 45)(1 46)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 47)(1 48)(1 49)(1 50))#158 51#80()#81)"%pstring.
Definition BL11 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xasan_R2 3%positive "()"%pstring.
Definition hints11 : list (nat * CC.subst) := hints7.
Definition o11 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xasan_R2 38%positive "(#130(((1369176#156()#158)#157))()())"%pstring.
