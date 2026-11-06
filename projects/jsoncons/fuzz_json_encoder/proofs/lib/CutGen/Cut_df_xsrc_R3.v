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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T Cut_df_xsrc_R0 Cut_df_xsrc_R1 Cut_df_xsrc_R2.
Definition dict_Cut_df_xsrc_R3 : CCD.pt := CCD.mk_table 1559%positive "((0 -160)(2 0(1 2)#1)(0 1048574)(5#3 1 4611686018427387904)(4 0(0 -1)(1 49))(2 0#5(0 1))(5#6 1 1)(5(1 49)0 0)(2 1(1 49)(0 0))(2 4#9(0 1))(5#10 1 1)(0 1048575)(5#12 1 4611686018427387904)(0 1048576)(5#14 1 4611686018427387904)((1 2)-48)(0#16 8(1 48))((1 2)-40)(0#18 8(1 19))((1 2)-32)(0#20 8(1 18))((1 2)-24)(0#22 8(1 9))((1 2)-16)(0#24 8(1 8))((1 2)-8)(0#26 8(1 1))((1 11)0)(0#28 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#34#35)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#34#35#28(0 8))((1 32)0)(7#34#35#40(0 24))(7#28(0 8)#40(0 24))(0 9152)(9#34#43)(9#18(0 0))((1 2)-9200#35)(#46)(0 1048573)(273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892)(0#49)(5#48 1 4611686018427387904)(4#51(1 0))(0#50#52)(2#2)(3(1 3))(4(1 4))(8(1 11))(9(1 10))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(2 0(1 49)(0 -1))(5#69 0 18446744073709551614)(5(1 49)1 18446744073709551615)(5#10 0 0)(0 524286)(5#73 1 4611686018427387904)(2 1(1 72)(0 22))(2 4#75(0 1))(5#76 0 0)(5(1 72)0 34)((1 2)-160)(9#79(0 8))(0 524287)(5#81 1 4611686018427387904)(5(1 55)1 25)((1 2)-148)(9#84(0 100))(0 524288)(5#86 1 4611686018427387904)(0 9040)(9#34#88)((1 2)-152)(9#90(0 104))(9#16(0 8))(0 524285)(5#93 1 4611686018427387904)(5(1 68))(6(1 69))(7(1 70))(0 -148)(2 0(1 2)#98)(10#99)(15(1 76))(16(1 77))(17(1 78))(18(1 48))(19(1 55))(28(1 79))(29(1 80))(30(1 81))(31(1 82))(2 1(1 83)(0 0))(2 4#110(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R3 275%positive "(273928((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(1 11)(1 9)(1 10)(1 49)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#4#7#8#11#13#15#17#19#21#23#25#27#29#30#31#32#33#36#37#38#39#41#42#44#45)50#47()#48)"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R3 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints4.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R3 310%positive "(#53(((273932((1(1 1))#54#55#56(5(1 5))(6(1 6))(7(1 7))#57#58(10(1 10))(11(1 49))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))#59#60#61#62#63#64#65#66#67#68(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#51#4#7#8#11#13#15#17#19#21#23#25#27#29#30#31#32#33#36#37#38#39#41#42#44#45))(1 273932)))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R3 281%positive "(273892((1 0)(1 50)#2(1 3)(1 4)(1 51)(1 52)(1 53)(1 11)(1 9)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 62)(1 63)(1 64)(1 65))(#4#70#71#72#13#15#17#19#21#23#25#27#29#30#31#32#33#36#37#38#39#41#42#44#45)66#47()#48)"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R3 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints4.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R3 325%positive "(#53(((422204((1(0 273904))#54#55#56(5(1 51))(6(1 52))(7(1 53))#57(9(1 9))(10(1 32))(11(0 46))(12(1 56))(13(1 57))(14(1 58))(15(1 59))(16(1 60))(17(1 61))#59#60#61#62#63#64#65#66#67#68(28(1 62))(29(1 63))(30(1 64))(31(1 65)))()(#51#4#70#71#72#13#15#17#19#21#23#25#27#29#30#31#32#33#36#37#38#39#41#42#44#45))(1 422204)))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R3 304%positive "(274048((1 0)(1 67)#2(1 3)(1 4)(1 68)(1 69)(1 70)(1 11)(1 10)(1 83)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 78)(1 48)(1 55)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 79)(1 80)(1 81)(1 82))(#74#77#78#80#82#83#85#87#29#30#31#32#33#36#37#38#39#41#42#89#91#27#25#23#21#19#92)84(((1 2)-160(0 8)))()#93)"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R3 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints5.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R3 772%positive "((3(11 83 0 0(16 0(0#50(4#94(1 0)))))(11 83 1 18446744073709551615(16 1(0#50(4#94(1 1))))))(((719568((1(0 274080))#54#55#56#95#96#97#57#58#100(11(0 100))(12(0 77440))(13(0 17))(14(1 48))#101#102#103#104#105#61#62#63#64#65#66#67#68#106#107#108#109)()(#94(5(2 0(4 0(0 -1)(1 83))(0 1))1 1)(5(1 83)0 0)(5#111 1 1)#74#77#78#80#82#83#85#87#29#30#31#32#33#36#37#38#39#41#42#89#91#27#25#23#21#19#92))(1 719568))((269344((1(0 274108))#54#55#56#95#96#97#57#58#100(11(1 55))(12(1 10))(13(1 11))(14(1 75))#101#102#103#104#105#61#62#63#64#65#66#67#68#106#107#108#109)()(#94(5(2 0(1 83)(0 -1))0 18446744073709551614)(5(1 83)1 18446744073709551615)(5#111 0 0)#74#77#78#80#82#83#85#87#29#30#31#32#33#36#37#38#39#41#42#89#91#27#25#23#21#19#92))(1 269344)))((1#110(0 1)1)(1(0 1)#110 0))())"%pstring.
