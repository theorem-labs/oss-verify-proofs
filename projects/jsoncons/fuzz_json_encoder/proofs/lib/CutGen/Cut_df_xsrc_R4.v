(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T Cut_df_xsrc_R0 Cut_df_xsrc_R1 Cut_df_xsrc_R2 Cut_df_xsrc_R3.
Definition dict_Cut_df_xsrc_R4 : CCD.pt := CCD.mk_table 2061%positive "((0 -160)(2 0(1 2)#1)(0 1048573)(5#3 1 4611686018427387904)(0 1048574)(5#5 1 4611686018427387904)(2 1(1 49)(0 0))(2 4#7(0 1))(0 1048575)(5#9 1 4611686018427387904)(0 1048576)(5#11 1 4611686018427387904)((1 2)-48)(0#13 8(1 48))((1 2)-40)(0#15 8(1 19))((1 2)-32)(0#17 8(1 18))((1 2)-24)(0#19 8(1 9))((1 2)-16)(0#21 8(1 8))((1 2)-8)(0#23 8(1 1))((1 11)0)(0#25 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#31#32)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#31#32#25(0 8))((1 32)0)(7#31#32#37(0 24))(7#25(0 8)#37(0 24))(0 9152)(9#31#40)(9#15(0 0))((1 2)-9200#32)(#43)(0 1048572)(273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892)(0#46)(0 524284)(5#48 1 4611686018427387904)(5#45 0 4611686018427387904)(0 524288)(5#51 0 4611686018427387904)(1(1 1))(2#2)(3(1 3))(4(1 4))(8(1 11))(9(1 10))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(0 9040)(9#31#68)((1 2)-160)(9#13(0 8))(2 0(1 49)(0 -1))(5#72 0 18446744073709551614)(5(1 49)1 18446744073709551615)(5#8 0 0)(5#45 1 4611686018427387904)(9(1 9))(18(1 18))((1 0)(1 84)#2(1 3)(1 4)(1 85)(1 86)(1 87)(1 11)(1 10)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 94)(1 95)(1 48)(1 55)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 96)(1 97)(1 98)(1 99))(5(1 88)1 25)((1 2)-148)(9#81(0 100))(0 524285)(5#83 1 4611686018427387904)(4 0(0 -1)(1 83))(2 0#85(0 1))(5#86 1 1)(5(1 83)0 0)(2 1(1 83)(0 0))(2 4#89(0 1))(5#90 1 1)(0 524286)(5#92 1 4611686018427387904)(2 1(1 72)(0 22))(2 4#94(0 1))(5#95 0 0)(5(1 72)0 34)(9#70(0 8))(0 524287)(5#99 1 4611686018427387904)(5(1 55)1 25)(5#51 1 4611686018427387904)((1 2)-152)(9#103(0 104))((1 2)-160(0 8))(#105)(5(1 85))(6(1 86))(7(1 87))(14(1 92))(15(1 93))(16(1 94))(17(1 95))(28(1 96))(29(1 97))(30(1 98))(31(1 99))(2 0(1 83)(0 -1))(5#118 0 18446744073709551614)(5(1 83)1 18446744073709551615)(5#90 0 0)(#84#119#120#121#93#96#97#98#100#101#82#102#26#27#28#29#30#33#34#35#36#38#39#69#104#24#22#20#18#16#71))"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R4 325%positive "(273936((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(1 11)(1 10)(1 10)(1 49)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 50)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#4#6(5(2 0(4 0(0 -1)(1 49))(0 1))1 1)(5(1 49)0 0)(5#8 1 1)#10#12#14#16#18#20#22#24#26#27#28#29#30#33#34#35#36#38#39#41#42)51#44()#45)"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R4 3%positive "()"%pstring.
Definition hints9 : list (nat * CC.subst) := hints6.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R4 424%positive "((0#47(16 0(16 1(16 2(4#49(4#50(4#52(1 0))))))))(((273940(#53#54#55#56(5(1 5))(6(1 6))(7(1 7))#57#58(10(1 10))(11(1 49))(12(0 77328))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 50))#59#60#61#62#63#64#65#66#67(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#26#27#28#29#30#33#34#35#36#38#39#69(9#70(0 112))#24#22#20#18#16#71#49#50#52))(0 1((48(1 50))(50(1 49))))))((6(1 2)-9200 9040)(6(1 2)-160 112)(6(1 2)-48 8))())"%pstring.
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R4 283%positive "(273904((1 0)(1 66)#2(1 3)(1 4)(1 67)(1 68)(1 69)(1 11)(1 9)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 78)(1 79)(1 80)(1 81))(#4#6#73#74#75#10#12#14#16#18#20#22#24#26#27#28#29#30#33#34#35#36#38#39#41#42)82#44()#45)"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R4 3%positive "()"%pstring.
Definition hints10 : list (nat * CC.subst) := hints7.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R4 336%positive "((0#47(4#76(1 0)))(((422204((1(0 273916))#54#55#56(5(1 67))(6(1 68))(7(1 69))#57#77(10(1 32))(11(0 48))(12(1 72))(13(1 73))(14(1 74))(15(1 75))(16(1 76))(17(1 77))#78#59#60#61#62#63#64#65#66#67(28(1 78))(29(1 79))(30(1 80))(31(1 81)))()(#76#4#6#73#74#75#10#12#14#16#18#20#22#24#26#27#28#29#30#33#34#35#36#38#39#41#42))(1 422204)))()())"%pstring.
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R4 129%positive "(274080#79(#80#82#84#87#88#91#93#96#97#98#100#101#82#102#26#27#28#29#30#33#34#35#36#38#39#69#104#24#22#20#18#16#71)100#106()#48)"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R4 3%positive "()"%pstring.
Definition hints11 : list (nat * CC.subst) := hints8.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R4 326%positive "((0#47(4#49(1 0)))(((269344((1(0 274108))#54#55#56#107#108#109#57#58(10(2 0(1 2)(0 -148)))(11(1 88))(12(1 10))(13(1 11))#110#111#112#113(18(1 48))(19(1 88))#60#61#62#63#64#65#66#67#114#115#116#117)()(#49#80#82#84#87#88#91#93#96#97#98#100#101#82#102#26#27#28#29#30#33#34#35#36#38#39#69#104#24#22#20#18#16#71))(1 269344)))()())"%pstring.
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R4 29%positive "(274108#79#122 100#106()#48)"%pstring.
Definition BL12 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R4 3%positive "()"%pstring.
Definition hints12 : list (nat * CC.subst) := hints8.
Definition o12 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R4 203%positive "((0#47(0(4 1)(0#47(1 0))))(((274036(#53(2(1 2))#55#56#107#108#109(8(1 8))#77(10(0 1))(11(1 89))(12(1 90))(13(1 91))#110#111#112#113#78#59#60#61#62#63#64#65#66#67#114#115#116#117)()#122)(1 274036)))()())"%pstring.
