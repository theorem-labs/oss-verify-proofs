(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_convert_casan_T Cut_convert_casan_R0 Cut_convert_casan_R1 Cut_convert_casan_R2.
Definition dict_Cut_convert_casan_R3 : CCD.pt := CCD.mk_table 3456%positive "((0 -112)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 55296)(0 2147450880)(6 1 0 4(1 32))(2 6#6(0 6))(0 -129)(2 9#7#8)(2 0#9(0 128))(0 65533)(2 9#6(0 63))(0 -128)(2 0#12#13)((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)#3(0 0)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(0 0)(1 12)(1 10)#3#4#5(0 128)#10#11#14(1 90)(1 91)(1 92)(1 93))(3 1388760 1392480)((0 0)1427896)(0#17 8#5)(5(0 98)1 4611686018427387904)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#6(0 16))(2 1#24(0 0))(2 4#25(0 1))(5#26 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(3 6#6(0 11))(2 1#30(0 0))(2 4#31(0 1))(5#32 0 0)(5(1 32)128 4294967295)(2 4#6(0 128))(5#35 0 0)(0 2048)(2 6#6(0 11))(4 0#37#38)(2 1#39#4)(2 4#40(0 1))(5#41 0 0)((1 2)-104)(0#43 8(1 27))((1 2)-96)(0#45 8(1 26))((1 2)-88)(0#47 8(1 25))((1 2)-80)(0#49 8(1 24))((1 2)-72)(0#51 8(1 23))((1 2)-64)(0#53 8(1 22))((1 2)-56)(0#55 8(1 21))((1 2)-48)(0#57 8(1 20))((1 2)-40)(0#59 8(1 19))((1 2)-32)(0#61 8(1 18))((1 2)-24)(0#63 8(1 9))((1 2)-16)(0#65 8(1 8))((1 2)-8)(0#67 8(1 1))(5(1 32)0 4294967295)(5(1 10)7024640 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#71#72#73(0 4))(5(1 12)7024640 140737479966696)(4(1 12)8)((1 2)-4496)(0 4392)(9#77#78)(0 4496)(6#77#80)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#77#80#73(0 4))((1 12)0)(7#77#80#85(0 24))(4(1 10)8)(#16#18#19#16#18#20#16#18#21#22#23#27#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#79#81#82#83#84#86#87)((1 2)-4496#80)(#89)((1 76)(1 77))(812508 812508 812972 985020 1330948 1331976)(0#92)(0#93(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 79))(6(1 80))(7(1 81))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 84))(13(1 85))(14(1 86))(15(1 87))(16(1 88))(17(1 89))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 90))(29(1 91))(30(1 92))(31(1 93))(#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125)(1 812972)(0 1023)(0 18446744073709551549)((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)#3(0 6)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(0 0)(1 12)(1 10)#3#4#5(0 128)#128#11#129(1 90)(1 91)(1 92)(1 93))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#24)(5#133 1 1)(5#26 0 0)(#16#18#19#16#18#20#16#18#21#131#132#134#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#79#81#82#83#84#86#87)(11(0 6))(#95#96#97#98#99#100#101#102#103#104#137#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125)(2 6#6(0 12))(2 9#139#8)(2 0#140(0 128))((1 0)(1 78)#2(1 3)(1 4)(1 79)(1 80)(1 81)(1 10)(0 0)(1 82)(1 83)(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(0 0)(1 12)(1 10)#3#4#5(0 128)#141#11#14(1 90)(1 91)(1 92)(1 93))((1 2)-112)(0#143 8(0 0))(5#133 0 0)(0 4384)(9#77#146)(5(0 97)1 4611686018427387904)(4#148(1 0))(0#93#149)(0 812864)(1#151)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#14(0 255))(11#157)(18(0 0))(19(1 12))(20(1 10))(21#3)(22#4)(23#5)(24(0 128))(25#141)(26#11)(27#14)(#152#153#97#98#99#100#101#154#155#156#158#106#107#108#109#110#111#159#160#161#162#163#164#165#166#167#168#122#123#124#125)(1 985020)(#16#18#19#16#18#20#16#18#21#22#23#27#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#79#81#82#83#84#86)(#16#18#19#16#18#20#16#18#21#131#132#134#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#79#81#82#83#84#86))"%pstring.

Definition t20 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 29%positive "(812864#15#88 94#90()(0 97))"%pstring.
Definition BL20 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints20 : list (nat * CC.subst) := hints13.
Definition o20 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 35%positive "(#94(((812972#126()#88)#127))()())"%pstring.

Definition t21 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 31%positive "(812864#130#136 94#90()(0 97))"%pstring.
Definition BL21 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints21 : list (nat * CC.subst) := hints14.
Definition o21 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 36%positive "(#94(((812972#138()#136)#127))()())"%pstring.

Definition t22 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 181%positive "(812848#142(#16#18#19#16#18#20#16#18#21#144#131#132#145#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#147#81#82#83#84#86#87)94#90()(0 97))"%pstring.
Definition BL22 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints22 : list (nat * CC.subst) := hints15.
Definition o22 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 192%positive "(#150(((985020#169()(#148#16#18#19#16#18#20#16#18#21#144#131#132#145#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#147#81#82#83#84#86#87))#170))()())"%pstring.

Definition t23 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 30%positive "(812864#15#171 94#90()(0 97))"%pstring.
Definition BL23 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints23 : list (nat * CC.subst) := hints17.
Definition o23 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 36%positive "(#94(((812972#126()#171)#127))()())"%pstring.

Definition t24 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 31%positive "(812864#130#172 94#90()(0 97))"%pstring.
Definition BL24 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints24 : list (nat * CC.subst) := hints18.
Definition o24 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 36%positive "(#94(((812972#138()#172)#127))()())"%pstring.

Definition t25 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R3 178%positive "(812848#142(#16#18#19#16#18#20#16#18#21#144#131#132#145#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#147#81#82#83#84#86)94#90()(0 97))"%pstring.
Definition BL25 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R3 6%positive "(#91)"%pstring.
Definition hints25 : list (nat * CC.subst) := hints19.
Definition o25 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R3 189%positive "(#150(((985020#169()(#148#16#18#19#16#18#20#16#18#21#144#131#132#145#22#23#135#28#29#33#34#36#42#44#46#48#50#52#54#56#58#60#62#64#66#68#16#18#69#70#74#75#76#147#81#82#83#84#86))#170))()())"%pstring.
