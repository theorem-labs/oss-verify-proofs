(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_convert_xasan_T Cut_convert_xasan_R0 Cut_convert_xasan_R1.
Definition dict_Cut_convert_xasan_R2 : CCD.pt := CCD.mk_table 3450%positive "((0 -112)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 55296)(0 2147450880)(0 65536)(0 65533)(6 1 0 4(1 32))(2 9#8(0 63))(0 -128)(2 0#9#10)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)#3(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(0 0)(1 12)(1 10)#3#4#5(0 128)#6#7#11(1 72)(1 73)(1 74)(1 75))(3 1444792 1448528)((0 0)1482488)(0#14 8#5)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)(3 6#8(0 11))(2 1#18(0 0))(2 4#19(0 1))(5#20 1 1)(5(1 32)128 4294967295)(2 4#8(0 128))(5#23 0 0)(0 2048)(2 6#8(0 11))(4 0#25#26)(2 1#27#4)(2 4#28(0 1))(5#29 0 0)((1 2)-104)(0#31 8(1 27))((1 2)-96)(0#33 8(1 26))((1 2)-88)(0#35 8(1 25))((1 2)-80)(0#37 8(1 24))((1 2)-72)(0#39 8(1 23))((1 2)-64)(0#41 8(1 22))((1 2)-56)(0#43 8(1 21))((1 2)-48)(0#45 8(1 20))((1 2)-40)(0#47 8(1 19))((1 2)-32)(0#49 8(1 18))((1 2)-24)(0#51 8(1 9))((1 2)-16)(0#53 8(1 8))((1 2)-8)(0#55 8(1 1))(5(1 32)0 4294967295)(5(1 10)7077888 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#59#60#61(0 4))(5(1 12)7077888 140737479966696)(4(1 12)8)((1 2)-4496)(0 4392)(9#65#66)(0 4496)(6#65#68)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#65#68#61(0 4))((1 12)0)(7#65#68#73(0 24))(4(1 10)8)(#13#15#16#13#15#17#21#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74#75)((1 2)-4496#68)(#77)((1 58)(1 59))(908744 908744 909208 1041292 1387168 1388196)(0#80)(0#81(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 61))(6(1 62))(7(1 63))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 66))(13(1 67))(14(1 68))(15(1 69))(16(1 70))(17(1 71))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 72))(29(1 73))(30(1 74))(31(1 75))(#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113)(1 909208)(2 6#8(0 6))(0 -129)(2 9#116#117)(2 0#118(0 128))((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(0 0)(1 12)(1 10)#3#4#5(0 128)#119#7#11(1 72)(1 73)(1 74)(1 75))(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#8(0 16))(2 1#123(0 0))(2 4#124(0 1))(5#125 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(5#20 0 0)(5(0 98)1 4611686018427387904)(4#130(1 0))(0#81#131)(0 909100)(1#133)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#11(0 255))(11#139)(18(0 0))(19(1 12))(20(1 10))(21#3)(22#4)(23#5)(24(0 128))(25#119)(26#7)(27#11)(#134#135#85#86#87#88#89#136#137#138#140#94#95#96#97#98#99#141#142#143#144#145#146#147#148#149#150#110#111#112#113)(1 1041292)(0 1023)(0 18446744073709551549)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)(0 6)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(0 0)(1 12)(1 10)#3#4#5(0 128)#153#7#154(1 72)(1 73)(1 74)(1 75))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#123)(5#158 1 1)(5#125 0 0)(9(0 6))(11(0 189))(25#153)(27#154)(#134#135#85#86#87#88#89#136#161#138#162#94#95#96#97#98#99#141#142#143#144#145#146#147#163#149#164#110#111#112#113)(2 6#8(0 12))(2 9#166#117)(2 0#167(0 128))((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)#7(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(0 0)(1 12)(1 10)#3#4#5(0 128)#168#119#11(1 72)(1 73)(1 74)(1 75))((1 2)-112)(0#170 8(0 0))(5#158 0 0)(0 4384)(9#65#173)(0 909084)(1#175)(8(1 10))(2 9#119(0 191))(11#178)(25#168)(#176#135#85#86#87#88#89#177#137#138#179#94#95#96#97#98#99#141#142#143#144#145#146#147#180#149#150#110#111#112#113)(#13#15#16#13#15#17#21#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74))"%pstring.
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 29%positive "(909100#12#76 76#78()(0 98))"%pstring.
Definition BL12 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints12 : list (nat * CC.subst) := hints3.
Definition o12 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 35%positive "(#82(((909208#114()#76)#115))()())"%pstring.
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 160%positive "(909084#120(#13#15#16#13#15#17#121#122#126#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74#75)76#78()(0 98))"%pstring.
Definition BL13 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints13 : list (nat * CC.subst) := hints4.
Definition o13 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 172%positive "(#132(((1041292#151()(#130#13#15#16#13#15#17#121#122#126#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74#75))#152))()())"%pstring.
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 172%positive "(909084#155(#13#15#16#13#15#17#156#157#159#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74#75)76#78()(0 98))"%pstring.
Definition BL14 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints14 : list (nat * CC.subst) := hints5.
Definition o14 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 184%positive "(#132(((1041292#165()(#130#13#15#16#13#15#17#156#157#159#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74#75))#152))()())"%pstring.
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 177%positive "(909012#169(#13#15#16#13#15#17#171#156#157#172#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#174#69#70#71#72#74#75)76#78()(0 98))"%pstring.
Definition BL15 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints15 : list (nat * CC.subst) := hints6.
Definition o15 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 189%positive "(#132(((1041292#181()(#130#13#15#16#13#15#17#171#156#157#172#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#174#69#70#71#72#74#75))#152))()())"%pstring.
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 30%positive "(909100#12#182 76#78()(0 98))"%pstring.
Definition BL16 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints16 : list (nat * CC.subst) := hints8.
Definition o16 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 36%positive "(#82(((909208#114()#182)#115))()())"%pstring.
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 157%positive "(909084#120(#13#15#16#13#15#17#121#122#126#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74)76#78()(0 98))"%pstring.
Definition BL17 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints17 : list (nat * CC.subst) := hints9.
Definition o17 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 169%positive "(#132(((1041292#151()(#130#13#15#16#13#15#17#121#122#126#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74))#152))()())"%pstring.
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 169%positive "(909084#155(#13#15#16#13#15#17#156#157#159#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74)76#78()(0 98))"%pstring.
Definition BL18 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints18 : list (nat * CC.subst) := hints10.
Definition o18 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 181%positive "(#132(((1041292#165()(#130#13#15#16#13#15#17#156#157#159#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#67#69#70#71#72#74))#152))()())"%pstring.
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xasan_R2 174%positive "(909012#169(#13#15#16#13#15#17#171#156#157#172#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#174#69#70#71#72#74)76#78()(0 98))"%pstring.
Definition BL19 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xasan_R2 6%positive "(#79)"%pstring.
Definition hints19 : list (nat * CC.subst) := hints11.
Definition o19 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xasan_R2 186%positive "(#132(((1041292#181()(#130#13#15#16#13#15#17#171#156#157#172#121#122#160#127#128#129#22#24#30#32#34#36#38#40#42#44#46#48#50#52#54#56#13#15#57#58#62#63#64#174#69#70#71#72#74))#152))()())"%pstring.
