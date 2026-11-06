(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm5CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fsinf_xboth_T Cut_fsinf_xboth_R0.
Definition dict_Cut_fsinf_xboth_R1 : CCDD.pt := CCDD.mk_table 1904%positive "((0 -8416)(2 0(1 2)#1)(0 18446744073709551613)(0 4096)(0 7084240)(0 18446744073709550542)(0 1152921504606846976)(5#7 1 4611686018427387904)((1 10)8)(2 0(1 32)(0 3))(0#9 8#10)((1 2)-120)(0#12 8(1 33))((1 2)-6128)(0#14 8(0 0))((1 2)-112)(0#16 8(1 34))((1 2)-104)(0#18 8(1 27))((1 2)-96)(0#20 8(1 26))((1 2)-88)(0#22 8(1 25))((1 2)-80)(0#24 8(1 24))((1 2)-72)(0#26 8(1 23))((1 2)-64)(0#28 8(1 22))((1 2)-56)(0#30 8(1 21))((1 2)-48)(0#32 8(1 20))((1 2)-40)(0#34 8(1 19))((1 2)-32)(0#36 8(1 18))((1 2)-24)(0#38 8(1 9))((1 2)-16)(0#40 8(1 8))((1 2)-8)(0#42 8(1 1))(5(1 2)140735332491744 140737488355328)(4(1 2)16)(3 65536 1466368)((1 2)-8672)(0 8672)(6#47#48)(0 2544)(9#47#50)((1 2)-6120)(0 6000)(9#52#53)(6#9(0 8))(5(1 10)140735332483072 140737488355072)(7#9(0 192)#47#48)(5(1 32)4096 140737488355328)((1 10)184)(0 18446744073709551615)(0#59 8#60)((1 10)192)(0#62 8(0 0))((0 0)7084240)(0#64 8(1 33))((1 32)0)(7#66(0 4)#47#48)(7#66(0 4)#9(0 192))(0#66 1(0 105))((1 32)1)(0#70 1(0 110))((1 32)2)(0#72 1(0 102))((1 32)3)(0#74 1(0 0))((1 2)-8672#48)((1 10)8(0 8))(#76#77)(0 1152921504606846975)(1381192 1381192 1381192 1381192 1384048 1327220 1383880 1383888 1383892 1383296 1386048 1386060 1386100 1386340 1386344 1386296 1386360 1383524 1383528 1383532 1402040 1403068)(0#80)(5#79 1 4611686018427387904)(4#82(1 0))(0#81#83)(1(1 1))(2#2)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(0 0))(9(0 1))(0 2139095040)(10#94)(11(0 73))(12(0 73))(13#4)(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(0 53))(19(1 19))(20#5)(21(1 10))(22#6)(23(0 1))(24(0 1))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(1 1383888)(2 0(1 32)(0 4))(0#9 8#118)(7#66(0 5)#47#48)(7#66(0 5)#9(0 192))(0#66 1(0 45))(0#70 1(0 105))(0#72 1(0 110))(0#74 1(0 102))((1 32)4)(0#126 1(0 0))(9#60)(0 2143289344)(0#66 1(0 110))(0#70 1(0 97))(0 1383900)(1#132)(8(0 5))(10#129)(11(0 40))(12(0 78))(1 1327220)(0#72 1(0 97))(0#74 1(0 110)))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xboth_R1 295%positive "(1383884((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)(0 1)#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#11#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#67#68#69#71#73#75)35#78()#79)"%pstring.
Definition BL4 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xboth_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xboth_R1 256%positive "(#84(((1383888(#85#86#87#88#89#90#91#92#93#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)()(#82#8#11#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#67#68#69#71#73#75))#117))()())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xboth_R1 304%positive "(1383884((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 0)#60#3(0 73)(0 73)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#119#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#120#121#122#123#124#125#127)35#78()#79)"%pstring.
Definition BL5 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xboth_R1 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints1.
Definition o5 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xboth_R1 268%positive "(#84(((1383888(#85#86#87#88#89#90#91#92#128#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)()(#82#8#119#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#120#121#122#123#124#125#127))#117))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xboth_R1 300%positive "(1383300((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 5)(0 1)#129(0 40)(0 78)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#11#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#67#68#130#131#124#75)35#78()#79)"%pstring.
Definition BL6 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xboth_R1 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints2.
Definition o6 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xboth_R1 264%positive "(#84(((1327220(#133#86#87#88#89#90#91#134#93#135#136#137#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)()(#82#8#11#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#67#68#130#131#124#75))#138))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fsinf_xboth_R1 305%positive "(1383300((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(0 5)#60#129(0 40)(0 78)#4(1 14)(1 15)(1 16)(1 17)(0 53)(1 19)#5(1 10)#6(0 1)(0 1)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#8#119#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#120#121#122#71#139#140#127)35#78()#79)"%pstring.
Definition BL7 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fsinf_xboth_R1 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints3.
Definition o7 : CAD.pout := CCDD.dec_pout_t dict_Cut_fsinf_xboth_R1 272%positive "(#84(((1327220(#133#86#87#88#89#90#91#134#128#135#136#137#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)()(#82#8#119#13#15#17#19#21#23#25#27#29#31#33#35#37#39#41#43#44#45#46#49#51#54#55#56#57#58#61#63#65#120#121#122#71#139#140#127))#138))()())"%pstring.
