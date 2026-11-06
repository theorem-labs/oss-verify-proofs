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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_dt_xsrc_T Cut_dt_xsrc_R0 Cut_dt_xsrc_R1.
Definition dict_Cut_dt_xsrc_R2 : CCD.pt := CCD.mk_table 1558%positive "((0 -144)(2 0(1 2)#1)(0 1048575)(5#3 1 4611686018427387904)(0 1048576)(5#5 1 4611686018427387904)((1 11)0)(0#7 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9344)(0 9344)(6#13#14)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#13#14#7(0 8))((1 32)0)(7#13#14#19(0 24))(7#7(0 8)#19(0 24))(0 9200)(9#13#22)((1 2)-144)(9#24(0 112))((1 2)-8)(0#26 8(1 1))((1 2)-16)(0#28 8(1 8))((1 2)-24)(0#30 8(1 9))((1 2)-32)(9#32(0 8))((1 2)-9344#14)(#34)(0 1048574)(273660 273732 273732 273808 422204 270980 273836 273736 273812 763484 764892)(0#37)(5#36 1 4611686018427387904)(4#39(1 0))(0#38#40)(2#2)(3(1 3))(4(1 4))(8(1 11))(9(1 9))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))((1 0)(1 67)#2(1 3)(1 4)(1 68)(1 69)(1 70)(1 11)(1 10)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 78)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 79)(1 80)(1 81)(1 82))(4 0(0 -1)(1 66))(5#58 1 18446744073709551614)(5(1 66)2 18446744073709551615)(5(1 66)1 18446744073709551615)(2 3(1 66)(0 0))(5#62 1 1)(9#24(0 104))((1 2)-40)(0#65 4(1 34))((1 2)-36)(0#67 4(1 33))(5(1 33)1 21)(5(1 68))(6(1 69))(7(1 70))(16(1 77))(17(1 78))(28(1 79))(29(1 80))(30(1 81))(31(1 82))(5(1 66)0 18446744073709551613)(5(1 66)0 18446744073709551614)(5#62 0 0)(#4#79#79#80#81#6#8#9#10#11#12#15#16#17#18#20#21#23#64#66#68#27#29#31#33#69)(0#38(1 0))(0(4 1)#83)(0#38#84)(1(1 1))(2(1 2))(8(1 8))(10(0 1))(1 273808)(#4#6#8#9#10#11#12#15#16#17#18#20#21#23#64#66#68#27#29#31#33#69))"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R2 260%positive "(273684((1 0)(1 82)#2(1 3)(1 4)(1 83)(1 84)(1 85)(1 11)(1 9)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 94)(1 95)(1 96)(1 97))(#4#6#8#9#10#11#12#15#16#17#18#20#21#23#25#27#29#31#33)98#35()#36)"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R2 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints3.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R2 299%positive "(#41(((422204((1(0 273696))#42#43#44(5(1 83))(6(1 84))(7(1 85))#45#46(10(1 32))(11(0 48))(12(1 88))(13(1 89))(14(1 90))(15(1 91))(16(1 92))(17(1 93))#47#48#49#50#51#52#53#54#55#56(28(1 94))(29(1 95))(30(1 96))(31(1 97)))()(#39#4#6#8#9#10#11#12#15#16#17#18#20#21#23#25#27#29#31#33))(1 422204)))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R2 98%positive "(273756#57(#4#59#60#61#63#6#8#9#10#11#12#15#16#17#18#20#21#23#64#66#68#27#29#31#33#69)83#35()#36)"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R2 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints4.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R2 305%positive "(#41(((270980((1(0 273784))#42#43#44#70#71#72#45(9(1 10))(10(2 0(1 2)(0 -140)))(11(1 33))(12(6 1 0 4(1 34)))(13(0 18446744073709551612))(14(0 17))(15(1 11))#73#74#47#48#49#50#51#52#53#54#55#56#75#76#77#78)()(#39#4#59#60#61#63#6#8#9#10#11#12#15#16#17#18#20#21#23#64#66#68#27#29#31#33#69))(1 270980)))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R2 26%positive "(273784#57#82 83#35()#36)"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R2 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints4.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R2 160%positive "(#85(((273808(#86#87#43#44#70#71#72#88#46#89(11(1 72))(12(1 73))(13(1 74))(14(1 75))(15(1 76))#73#74#47#48#49#50#51#52#53#54#55#56#75#76#77#78)()#82)#90))()())"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R2 209%positive "(273832((1 0)(1 66)#2(1 3)(1 4)(1 67)(1 68)(1 69)(1 11)(1 10)(0 1)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 78)(1 79)(1 80)(1 81))#91 82#35()#36)"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R2 3%positive "()"%pstring.
Definition hints9 : list (nat * CC.subst) := hints5.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R2 220%positive "(#85(((273808(#86#87#43#44(5(1 67))(6(1 68))(7(1 69))#88#46#89(11(1 71))(12(1 72))(13(1 73))(14(1 74))(15(1 75))(16(1 76))(17(1 77))#47#48#49#50#51#52#53#54#55#56(28(1 78))(29(1 79))(30(1 80))(31(1 81)))()#91)#90))()())"%pstring.
