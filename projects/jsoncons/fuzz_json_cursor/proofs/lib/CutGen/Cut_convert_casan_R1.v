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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_convert_casan_T Cut_convert_casan_R0.
Definition dict_Cut_convert_casan_R1 : CCD.pt := CCD.mk_table 3794%positive "((0 -112)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 55296)(0 2147450880)(0 65536)(0 65533)(6 1 0 4(1 32))((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)#3(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(0 0)(1 12)(1 10)#3#4#5(0 128)#6#7#8(1 54)(1 55)(1 56)(1 57))(3 1388760 1392480)((0 0)1427896)(0#11 8#5)(5(0 100)1 4611686018427387904)(5(1 32)0 4294967293)(5(1 32)0 4294967294)(2 4#8(0 128))(5#16 1 1)(0 2048)(2 6#8(0 11))(4 0#18#19)(2 1#20#4)(2 4#21(0 1))(5#22 0 0)((1 2)-104)(0#24 8(1 27))((1 2)-96)(0#26 8(1 26))((1 2)-88)(0#28 8(1 25))((1 2)-80)(0#30 8(1 24))((1 2)-72)(0#32 8(1 23))((1 2)-64)(0#34 8(1 22))((1 2)-56)(0#36 8(1 21))((1 2)-48)(0#38 8(1 20))((1 2)-40)(0#40 8(1 19))((1 2)-32)(0#42 8(1 18))((1 2)-24)(0#44 8(1 9))((1 2)-16)(0#46 8(1 8))((1 2)-8)(0#48 8(1 1))(5(1 32)0 4294967295)(5(1 10)7024640 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#52#53#54(0 4))(5(1 12)7024640 140737479966696)(4(1 12)8)((1 2)-4496)(0 4392)(9#58#59)(0 4496)(6#58#61)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#58#61#54(0 4))((1 12)0)(7#58#61#66(0 24))(4(1 10)8)(#10#12#13#14#15#17#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68)((1 2)-4496#61)(#70)((1 40)(1 41))(812508 812508 812972 985020 1330948 1331976)(0#73)(0#74(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 43))(6(1 44))(7(1 45))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 48))(13(1 49))(14(1 50))(15(1 51))(16(1 52))(17(1 53))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 54))(29(1 55))(30(1 56))(31(1 57))(#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106)(1 812972)(2 9#8(0 63))(0 -128)(2 0#109#110)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(0 0)(1 12)(1 10)#3#4#5(0 128)#6#7#111(1 54)(1 55)(1 56)(1 57))(3 6#8(0 11))(2 1#113(0 0))(2 4#114(0 1))(5#115 1 1)(5(1 32)128 4294967295)(5#16 0 0)(5(0 99)1 4611686018427387904)(4#119(1 0))(0#74#120)(0 812864)(1#122)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#111(0 255))(11#128)(18(0 0))(19(1 12))(20(1 10))(21#3)(22#4)(23#5)(24(0 128))(25#6)(26#7)(27#111)(#123#124#78#79#80#81#82#125#126#127#129#87#88#89#90#91#92#130#131#132#133#134#135#136#137#138#139#103#104#105#106)(1 985020)(2 6#8(0 6))(0 -129)(2 9#142#143)(2 0#144(0 128))((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(0 0)(1 12)(1 10)#3#4#5(0 128)#145#7#111(1 54)(1 55)(1 56)(1 57))(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#8(0 16))(2 1#149(0 0))(2 4#150(0 1))(5#151 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(5#115 0 0)(0 812848)(1#156)(8(1 10))(2 9#145(0 191))(11#159)(25#145)(#157#124#78#79#80#81#82#158#126#127#160#87#88#89#90#91#92#130#131#132#133#134#135#136#161#138#139#103#104#105#106)(0 1023)(0 18446744073709551549)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 6)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(0 0)(1 12)(1 10)#3#4#5(0 128)#163#7#164(1 54)(1 55)(1 56)(1 57))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#149)(5#168 1 1)(5#151 0 0)(9(0 6))(11(0 191))(25#163)(27#164)(#157#124#78#79#80#81#82#158#171#127#172#87#88#89#90#91#92#130#131#132#133#134#135#136#173#138#174#103#104#105#106)(2 6#8(0 12))(2 9#176#143)(2 0#177(0 128))((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)#7(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(0 0)(1 12)(1 10)#3#4#5(0 128)#178#145#111(1 54)(1 55)(1 56)(1 57))((1 2)-112)(0#180 8(0 0))(5#168 0 0)(0 4384)(9#58#183)(0 812776)(1#185)(9#7)(2 9#178(0 191))(11#188)(25#178)(26#145)(#186#124#78#79#80#81#82#158#187#127#189#87#88#89#90#91#92#130#131#132#133#134#135#136#190#191#139#103#104#105#106)(#10#12#13#14#15#17#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 28%positive "(812864#9#69 58#71()(0 99))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 35%positive "(#75(((812972#107()#69)#108))()())"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 133%positive "(812848#112(#10#12#13#116#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68)58#71()(0 99))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints3 : list (nat * CC.subst) := hints0.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 144%positive "(#121(((985020#140()(#119#10#12#13#116#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68))#141))()())"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 153%positive "(812836#146(#10#12#13#147#148#152#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68)58#71()(0 99))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 164%positive "(#121(((985020#162()(#119#10#12#13#147#148#152#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68))#141))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 165%positive "(812836#165(#10#12#13#166#167#169#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68)58#71()(0 99))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints5 : list (nat * CC.subst) := hints0.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 176%positive "(#121(((985020#175()(#119#10#12#13#166#167#169#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67#68))#141))()())"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 170%positive "(812764#179(#10#12#13#181#166#167#182#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#184#62#63#64#65#67#68)58#71()(0 99))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints6 : list (nat * CC.subst) := hints0.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 181%positive "(#121(((985020#192()(#119#10#12#13#181#166#167#182#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#184#62#63#64#65#67#68))#141))()())"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 29%positive "(812864#9#193 58#71()(0 99))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints7 : list (nat * CC.subst) := hints1.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 36%positive "(#75(((812972#107()#193)#108))()())"%pstring.

Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 130%positive "(812848#112(#10#12#13#116#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67)58#71()(0 99))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints8 : list (nat * CC.subst) := hints1.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 141%positive "(#121(((985020#140()(#119#10#12#13#116#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67))#141))()())"%pstring.

Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 150%positive "(812836#146(#10#12#13#147#148#152#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67)58#71()(0 99))"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints9 : list (nat * CC.subst) := hints1.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 161%positive "(#121(((985020#162()(#119#10#12#13#147#148#152#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67))#141))()())"%pstring.

Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 162%positive "(812836#165(#10#12#13#166#167#169#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67)58#71()(0 99))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints10 : list (nat * CC.subst) := hints1.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 173%positive "(#121(((985020#175()(#119#10#12#13#166#167#169#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#60#62#63#64#65#67))#141))()())"%pstring.

Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_casan_R1 167%positive "(812764#179(#10#12#13#181#166#167#182#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#184#62#63#64#65#67)58#71()(0 99))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_casan_R1 6%positive "(#72)"%pstring.
Definition hints11 : list (nat * CC.subst) := hints1.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_convert_casan_R1 178%positive "(#121(((985020#192()(#119#10#12#13#181#166#167#182#147#148#170#153#154#155#117#118#23#25#27#29#31#33#35#37#39#41#43#45#47#49#10#12#50#51#55#56#57#184#62#63#64#65#67))#141))()())"%pstring.
