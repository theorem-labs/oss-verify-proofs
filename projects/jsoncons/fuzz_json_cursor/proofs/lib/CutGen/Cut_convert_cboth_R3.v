(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_convert_cboth_T Cut_convert_cboth_R0 Cut_convert_cboth_R1 Cut_convert_cboth_R2.
Definition dict_Cut_convert_cboth_R3 : CCD.pt := CCD.mk_table 3519%positive "((0 -128)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 18446744073709399103)(6 1 0 4(1 32))(2 9#5(0 63))(2 0#6#1)(0 2147450880)(0 152512)((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)#3(0 0)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 12)#4#3(0 0)#7#3#7#8#7#9(1 90)(1 91)(1 92)(1 93))(3 1393824 1397544)((0 0)1432824)(0#12 8#8)(5(0 98)1 4611686018427387904)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#5(0 16))(2 1#19(0 0))(2 4#20(0 1))(5#21 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(3 6#5(0 11))(2 1#25(0 0))(2 4#26(0 1))(5#27 0 0)(5(1 32)128 4294967295)(2 4#5(0 128))(5#30 0 0)(0 2048)(2 6#5(0 11))(4 0#32#33)(0 55296)(2 1#34#35)(2 4#36(0 1))(5#37 0 0)((1 2)-128)(0 65533)(0#39 8#40)((1 2)-112)(0#42 8#35)((1 2)-120)(0#44 8(0 0))((1 2)-104)(0#46 8(1 27))((1 2)-96)(0#48 8(1 26))((1 2)-88)(0#50 8(1 25))((1 2)-80)(0#52 8(1 24))((1 2)-72)(0#54 8(1 23))((1 2)-64)(0#56 8(1 22))((1 2)-56)(0#58 8(1 21))((1 2)-48)(0#60 8(1 20))((1 2)-40)(0#62 8(1 19))((1 2)-32)(0#64 8(1 18))((1 2)-24)(0#66 8(1 9))((1 2)-16)(0#68 8(1 8))((1 2)-8)(0#70 8(1 1))(5(1 32)0 4294967295)(5(1 10)7028736 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#74#75#76(0 4))(5(1 12)7028736 140737479966696)(4(1 12)8)(3 152352 152608)((1 2)-4496)(0 4368)(9#81#82)(0 4496)(6#81#84)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#81#84#76(0 4))((1 12)0)(7#81#84#89(0 24))(4(1 10)8)(#11#13#14#11#13#15#11#13#16#17#18#22#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#91)((1 2)-4496#84)(#93)((1 76)(1 77))(814184 814184 814828 990424 1336512 1337540)(0#96)(0#97(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 79))(6(1 80))(7(1 81))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 84))(13(1 85))(14(1 86))(15(1 87))(16(1 88))(17(1 89))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 90))(29(1 91))(30(1 92))(31(1 93))(#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129)(1 814828)(0 18446744073709551549)((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)#3(0 0)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 12)#4#3(0 0)#132#3#132#8#132#9(1 90)(1 91)(1 92)(1 93))(0#44 8(0 6))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#19)(5#137 1 1)(5#21 0 0)(#11#13#14#11#13#15#11#13#16#134#135#136#138#17#18#139#23#24#28#29#31#38#41#43#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#91)(11(0 6))(#99#100#101#102#103#104#105#106#107#108#141#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129)(3 6#5(0 6))(2 9#143(0 63))(2 0#144#1)((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)(1 10)(0 0)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 12)#4#3(0 0)#145#3#7#8#7#9(1 90)(1 91)(1 92)(1 93))(5#137 0 0)(5(0 97)1 4611686018427387904)(4#148(1 0))(0#97#149)(0 814696)(1#151)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#7(0 255))(11#157)(18(1 12))(19#4)(20#3)(21(0 0))(22#145)(23#3)(24#7)(25#8)(26#7)(27#9)(#152#153#101#102#103#104#105#154#155#156#158#110#111#112#113#114#115#159#160#161#162#163#164#165#166#167#168#126#127#128#129)(1 990424)(4(1 10)4)(#11#13#14#11#13#15#11#13#16#17#18#22#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#171)(#11#13#14#11#13#15#11#13#16#134#135#136#138#17#18#139#23#24#28#29#31#38#41#43#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#171))"%pstring.

Definition t20 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 29%positive "(814696#10#92 94#94()(0 97))"%pstring.
Definition BL20 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints20 : list (nat * CC.subst) := hints13.
Definition o20 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 35%positive "(#98(((814828#130()#92)#131))()())"%pstring.

Definition t21 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 31%positive "(814696#133#140 94#94()(0 97))"%pstring.
Definition BL21 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints21 : list (nat * CC.subst) := hints14.
Definition o21 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 36%positive "(#98(((814828#142()#140)#131))()())"%pstring.

Definition t22 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 188%positive "(814676#146(#11#13#14#11#13#15#11#13#16#135#136#147#17#18#139#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#91)94#94()(0 97))"%pstring.
Definition BL22 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints22 : list (nat * CC.subst) := hints15.
Definition o22 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 199%positive "(#150(((990424#169()(#148#11#13#14#11#13#15#11#13#16#135#136#147#17#18#139#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#91))#170))()())"%pstring.

Definition t23 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 30%positive "(814696#10#172 94#94()(0 97))"%pstring.
Definition BL23 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints23 : list (nat * CC.subst) := hints17.
Definition o23 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 36%positive "(#98(((814828#130()#172)#131))()())"%pstring.

Definition t24 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 31%positive "(814696#133#173 94#94()(0 97))"%pstring.
Definition BL24 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints24 : list (nat * CC.subst) := hints18.
Definition o24 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 36%positive "(#98(((814828#142()#173)#131))()())"%pstring.

Definition t25 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R3 189%positive "(814676#146(#11#13#14#11#13#15#11#13#16#135#136#147#17#18#139#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#171)94#94()(0 97))"%pstring.
Definition BL25 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R3 6%positive "(#95)"%pstring.
Definition hints25 : list (nat * CC.subst) := hints19.
Definition o25 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R3 200%positive "(#150(((990424#169()(#148#11#13#14#11#13#15#11#13#16#135#136#147#17#18#139#23#24#28#29#31#38#41#43#45#47#49#51#53#55#57#59#61#63#65#67#69#71#11#13#72#73#77#78#79#80#83#85#86#87#88#90#171))#170))()())"%pstring.
