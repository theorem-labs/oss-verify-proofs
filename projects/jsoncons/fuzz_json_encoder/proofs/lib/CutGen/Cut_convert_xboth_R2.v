(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_convert_xboth_T Cut_convert_xboth_R0 Cut_convert_xboth_R1.
Definition dict_Cut_convert_xboth_R2 : CCD.pt := CCD.mk_table 3481%positive "((0 -128)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 18446744073709385119)(6 1 0 4(1 32))(2 9#5(0 63))(2 0#6#1)(0 2147450880)(0 166496)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)#3(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(1 12)#4#3(0 0)(0 0)#3#7#8(0 0)#9(1 72)(1 73)(1 74)(1 75))(3 1459384 1463120)((0 0)1497016)(0#12 8#8)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)(3 6#5(0 11))(2 1#16(0 0))(2 4#17(0 1))(5#18 1 1)(5(1 32)128 4294967295)(2 4#5(0 128))(5#21 0 0)(0 2048)(2 6#5(0 11))(4 0#23#24)(0 55296)(2 1#25#26)(2 4#27(0 1))(5#28 0 0)((1 2)-128)(0 65533)(0#30 8#31)((1 2)-112)(0#33 8#26)((1 2)-120)(0#35 8(0 0))((1 2)-104)(0#37 8(1 27))((1 2)-96)(0#39 8(1 26))((1 2)-88)(0#41 8(1 25))((1 2)-80)(0#43 8(1 24))((1 2)-72)(0#45 8(1 23))((1 2)-64)(0#47 8(1 22))((1 2)-56)(0#49 8(1 21))((1 2)-48)(0#51 8(1 20))((1 2)-40)(0#53 8(1 19))((1 2)-32)(0#55 8(1 18))((1 2)-24)(0#57 8(1 9))((1 2)-16)(0#59 8(1 8))((1 2)-8)(0#61 8(1 1))(5(1 32)0 4294967295)(5(1 10)7094272 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#65#66#67(0 4))(5(1 12)7094272 140737479966696)(4(1 12)8)(3 166400 166656)((1 2)-4496)(0 4368)(9#72#73)(0 4496)(6#72#75)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#72#75#67(0 4))((1 12)0)(7#72#75#80(0 24))(4(1 10)8)(#11#13#14#11#13#15#19#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82)((1 2)-4496#75)(#84)((1 58)(1 59))(923544 923544 924188 1056004 1402040 1403068)(0#87)(0#88(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 61))(6(1 62))(7(1 63))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 66))(13(1 67))(14(1 68))(15(1 69))(16(1 70))(17(1 71))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 72))(29(1 73))(30(1 74))(31(1 75))(#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120)(1 924188)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(1 12)#4#3(0 0)#7#3#7#8#7#9(1 72)(1 73)(1 74)(1 75))(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#5(0 16))(2 1#126(0 0))(2 4#127(0 1))(5#128 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(5#18 0 0)(5(0 98)1 4611686018427387904)(4#133(1 0))(0#88#134)(0 924056)(1#136)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#7(0 255))(11#142)(18(1 12))(19#4)(20#3)(21(0 0))(22#7)(23#3)(24#7)(25#8)(26#7)(27#9)(#137#138#92#93#94#95#96#139#140#141#143#101#102#103#104#105#106#144#145#146#147#148#149#150#151#152#153#117#118#119#120)(1 1056004)(0 18446744073709551549)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(1 12)#4#3(0 0)#156#3#156#8#156#9(1 72)(1 73)(1 74)(1 75))(0#35 8(0 6))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#126)(5#161 1 1)(5#128 0 0)(11(0 189))(22#156)(24#156)(26#156)(#137#138#92#93#94#95#96#139#140#141#164#101#102#103#104#105#106#144#145#146#147#165#149#166#151#167#153#117#118#119#120)(3 6#5(0 6))(2 9#169(0 63))(2 0#170#1)((1 0)(1 60)#2(1 3)(1 4)(1 61)(1 62)(1 63)(1 10)(0 0)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 71)(1 12)#4#3(0 0)#171#3#171#8#7#9(1 72)(1 73)(1 74)(1 75))(5#161 0 0)(0 924036)(1#174)(8(1 10))(2 9#171(0 255))(11#177)(22#171)(#175#138#92#93#94#95#96#176#140#141#178#101#102#103#104#105#106#144#145#146#147#179#149#150#151#152#153#117#118#119#120)(4(1 10)4)(#11#13#14#11#13#15#19#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181))"%pstring.
(* [comment removed for export] *)
Definition t12 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 29%positive "(924056#10#83 76#85()(0 98))"%pstring.
Definition BL12 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints12 : list (nat * CC.subst) := hints3.
Definition o12 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 35%positive "(#89(((924188#121()#83)#122))()())"%pstring.
(* [comment removed for export] *)
Definition t13 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 172%positive "(924036#123(#11#13#14#11#13#15#124#125#129#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82)76#85()(0 98))"%pstring.
Definition BL13 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints13 : list (nat * CC.subst) := hints4.
Definition o13 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 184%positive "(#135(((1056004#154()(#133#11#13#14#11#13#15#124#125#129#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82))#155))()())"%pstring.
(* [comment removed for export] *)
Definition t14 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 185%positive "(924036#157(#11#13#14#11#13#15#158#159#160#162#124#125#163#130#131#132#20#22#29#32#34#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82)76#85()(0 98))"%pstring.
Definition BL14 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints14 : list (nat * CC.subst) := hints5.
Definition o14 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 197%positive "(#135(((1056004#168()(#133#11#13#14#11#13#15#158#159#160#162#124#125#163#130#131#132#20#22#29#32#34#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82))#155))()())"%pstring.
(* [comment removed for export] *)
Definition t15 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 184%positive "(924016#172(#11#13#14#11#13#15#159#160#173#124#125#163#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82)76#85()(0 98))"%pstring.
Definition BL15 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints15 : list (nat * CC.subst) := hints6.
Definition o15 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 196%positive "(#135(((1056004#180()(#133#11#13#14#11#13#15#159#160#173#124#125#163#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#82))#155))()())"%pstring.
(* [comment removed for export] *)
Definition t16 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 30%positive "(924056#10#182 76#85()(0 98))"%pstring.
Definition BL16 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints16 : list (nat * CC.subst) := hints8.
Definition o16 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 36%positive "(#89(((924188#121()#182)#122))()())"%pstring.
(* [comment removed for export] *)
Definition t17 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 173%positive "(924036#123(#11#13#14#11#13#15#124#125#129#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181)76#85()(0 98))"%pstring.
Definition BL17 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints17 : list (nat * CC.subst) := hints9.
Definition o17 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 185%positive "(#135(((1056004#154()(#133#11#13#14#11#13#15#124#125#129#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181))#155))()())"%pstring.
(* [comment removed for export] *)
Definition t18 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 186%positive "(924036#157(#11#13#14#11#13#15#158#159#160#162#124#125#163#130#131#132#20#22#29#32#34#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181)76#85()(0 98))"%pstring.
Definition BL18 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints18 : list (nat * CC.subst) := hints10.
Definition o18 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 198%positive "(#135(((1056004#168()(#133#11#13#14#11#13#15#158#159#160#162#124#125#163#130#131#132#20#22#29#32#34#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181))#155))()())"%pstring.
(* [comment removed for export] *)
Definition t19 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R2 185%positive "(924016#172(#11#13#14#11#13#15#159#160#173#124#125#163#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181)76#85()(0 98))"%pstring.
Definition BL19 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R2 6%positive "(#86)"%pstring.
Definition hints19 : list (nat * CC.subst) := hints11.
Definition o19 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R2 197%positive "(#135(((1056004#180()(#133#11#13#14#11#13#15#159#160#173#124#125#163#130#131#132#20#22#29#32#34#36#38#40#42#44#46#48#50#52#54#56#58#60#62#11#13#63#64#68#69#70#71#74#76#77#78#79#81#181))#155))()())"%pstring.
