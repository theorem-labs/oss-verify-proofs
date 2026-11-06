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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T Cut_df_xsrc_R0 Cut_df_xsrc_R1 Cut_df_xsrc_R2 Cut_df_xsrc_R3 Cut_df_xsrc_R4.
Definition dict_Cut_df_xsrc_R5 : CCD.pt := CCD.mk_table 1711%positive "((0 -160)(2 0(1 2)#1)(0 1048572)(5#3 1 4611686018427387904)(0 1048573)(5#5 1 4611686018427387904)(0 1048574)(5#7 1 4611686018427387904)(2 0(1 49)(0 -1))(5#9 0 18446744073709551614)(5(1 49)1 18446744073709551615)(2 1(1 49)(0 0))(2 4#12(0 1))(5#13 0 0)(0 1048575)(5#15 1 4611686018427387904)(0 1048576)(5#17 1 4611686018427387904)((1 2)-48)(0#19 8(1 48))((1 2)-40)(0#21 8(1 19))((1 2)-32)(0#23 8(1 18))((1 2)-24)(0#25 8(1 9))((1 2)-16)(0#27 8(1 8))((1 2)-8)(0#29 8(1 1))((1 11)0)(0#31 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#37#38)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#37#38#31(0 8))((1 32)0)(7#37#38#43(0 24))(7#31(0 8)#43(0 24))(0 9152)(9#37#46)(9#21(0 0))(#4#6#8#10#11#14#16#18#20#22#24#26#28#30#32#33#34#35#36#39#40#41#42#44#45#47#48)(273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892)(0#50)(0#51(1 0))(0(4 1)#52)(0#51#53)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(8(1 8))(9(1 9))(10(0 1))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(1 274036)(0 524284)(5#73 1 4611686018427387904)(5(1 88)1 25)((1 2)-148)(9#76(0 100))(0 524285)(5#78 1 4611686018427387904)(4 0(0 -1)(1 83))(2 0#80(0 1))(5#81 1 1)(5(1 83)0 0)(2 1(1 83)(0 0))(2 4#84(0 1))(5#85 1 1)(0 524286)(5#87 1 4611686018427387904)(2 1(1 72)(0 22))(2 4#89(0 1))(5#90 0 0)(5(1 72)0 34)((1 2)-160)(9#93(0 8))(0 524287)(5#95 1 4611686018427387904)(5(1 55)1 25)(0 524288)(5#98 1 4611686018427387904)(0 9040)(9#37#100)((1 2)-152)(9#102(0 104))(9#19(0 8))(#74#75#77#79#82#83#86#88#91#92#94#96#97#77#99#32#33#34#35#36#39#40#41#42#44#45#101#103#30#28#26#24#22#104))"%pstring.
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R5 231%positive "(273916((1 0)(1 82)#2(1 3)(1 4)(1 83)(1 84)(1 85)(1 11)(1 9)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 94)(1 95)(1 96)(1 97))#49 98(((1 2)-9200#38))()(0 1048571))"%pstring.
Definition BL13 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R5 3%positive "()"%pstring.
Definition hints13 : list (nat * CC.subst) := hints10.
Definition o13 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R5 220%positive "(#54(((274036(#55#56#57#58(5(1 83))(6(1 84))(7(1 85))#59#60#61(11(1 87))(12(1 88))(13(1 89))(14(1 90))(15(1 91))(16(1 92))(17(1 93))#62#63#64#65#66#67#68#69#70#71(28(1 94))(29(1 95))(30(1 96))(31(1 97)))()#49)#72))()())"%pstring.
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R5 250%positive "(274108((1 0)(1 100)#2(1 3)(1 4)(1 101)(1 102)(1 103)(1 11)(1 10)(1 104)(1 105)(1 106)(1 107)(1 108)(1 109)(1 110)(1 111)(1 48)(1 88)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 112)(1 113)(1 114)(1 115))#105 116(((1 2)-160(0 8)))()(0 524283))"%pstring.
Definition BL14 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R5 3%positive "()"%pstring.
Definition hints14 : list (nat * CC.subst) := hints11.
Definition o14 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R5 235%positive "(#54(((274036(#55#56#57#58(5(1 101))(6(1 102))(7(1 103))#59#60#61(11(1 105))(12(1 106))(13(1 107))(14(1 108))(15(1 109))(16(1 110))(17(1 111))#62#63#64#65#66#67#68#69#70#71(28(1 112))(29(1 113))(30(1 114))(31(1 115)))()#105)#72))()())"%pstring.
