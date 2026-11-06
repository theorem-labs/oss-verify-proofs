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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T Cut_df_xsrc_R0 Cut_df_xsrc_R1.
Definition dict_Cut_df_xsrc_R2 : CCD.pt := CCD.mk_table 1239%positive "((0 -160)(2 0(1 2)#1)(0 1048575)(5#3 1 4611686018427387904)(0 1048576)(5#5 1 4611686018427387904)((1 2)-48)(0#7 8(1 48))((1 2)-40)(0#9 8(1 19))((1 2)-32)(0#11 8(1 18))((1 2)-24)(0#13 8(1 9))((1 2)-16)(0#15 8(1 8))((1 2)-8)(0#17 8(1 1))((1 11)0)(0#19 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#25#26)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#25#26#19(0 8))((1 32)0)(7#25#26#31(0 24))(7#19(0 8)#31(0 24))(0 9152)(9#25#34)(9#9(0 0))(0 1048574)(273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892)(0#38)(5#37 1 4611686018427387904)(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 11))(9(1 9))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(2 1(1 49)(0 0))(2 4#69(0 1))(2 1(1 72)(0 22))(2 4#71(0 1))(5#72 0 0)(5(1 72)0 34)((1 2)-160)(9#75(0 8))(0 524287)(5#77 1 4611686018427387904)(5(1 55)1 25)((1 2)-148)(9#80(0 100))(0 524288)(5#82 1 4611686018427387904)(0 9040)(9#25#84)((1 2)-152)(9#86(0 104))(9#7(0 8))(0 524286)(5#89 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R2 277%positive "(273876((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(1 11)(1 9)(1 10)(1 49)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#4#6#8#10#12#14#16#18#20#21#22#23#24#27#28#29#30#32#33#35#36)50(((1 2)-9200#26))()#37)"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R2 669%positive "((3(11 49 0 0(16 0(0#39(4#40(1 0)))))(11 49 1 18446744073709551615(16 1(0#39(4#40(1 1))))))(((273924((1(1 1))#41#42#43#44#45#46#47#48(10(1 10))(11(1 49))#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67#68)()(#40(5(2 0(4 0(0 -1)(1 49))(0 1))1 1)(5(1 49)0 0)(5#70 1 1)#4#6#8#10#12#14#16#18#20#21#22#23#24#27#28#29#30#32#33#35#36))(1 273924))((422204((1(0 273892))#41#42#43#44#45#46#47#48(10(1 32))(11(0 48))#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67#68)()(#40(5(2 0(1 49)(0 -1))0 18446744073709551614)(5(1 49)1 18446744073709551615)(5#70 0 0)#4#6#8#10#12#14#16#18#20#21#22#23#24#27#28#29#30#32#33#35#36))(1 422204)))((1#69(0 1)1)(1(0 1)#69 0))())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R2 301%positive "(273992((1 0)(1 67)#2(1 3)(1 4)(1 68)(1 69)(1 70)(1 11)(1 10)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 78)(1 48)(1 55)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 79)(1 80)(1 81)(1 82))(#73#74#76#78#79#81#83#20#21#22#23#24#27#28#29#30#32#33#85#87#18#16#14#12#10#88)83(((1 2)-160(0 8)))()#89)"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R2 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R2 362%positive "((0#39(0(4 1)(4#90(1 0))))(((274044((1(1 67))#41#42#43(5(1 68))(6(1 69))(7(1 70))#47(9(1 10))(10(0 22))(11(1 72))(12(1 73))(13(1 74))(14(1 75))(15(1 76))(16(1 77))(17(1 78))(18(1 48))(19(1 55))#57#58#59#60#61#62#63#64(28(1 79))(29(1 80))(30(1 81))(31(1 82)))()(#90#73#74#76#78#79#81#83#20#21#22#23#24#27#28#29#30#32#33#85#87#18#16#14#12#10#88))(1 274044)))()())"%pstring.
