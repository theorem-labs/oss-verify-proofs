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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_convert_cboth_T Cut_convert_cboth_R0.
Definition dict_Cut_convert_cboth_R1 : CCD.pt := CCD.mk_table 3896%positive "((0 -128)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 18446744073709399103)(0 2147450880)(0 152512)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)#3(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(1 12)#4#3(0 0)(0 0)#3(0 0)#5(0 0)#6(1 54)(1 55)(1 56)(1 57))(3 1393824 1397544)((0 0)1432824)(0#9 8#5)(5(0 100)1 4611686018427387904)(5(1 32)0 4294967293)(5(1 32)0 4294967294)(6 1 0 4(1 32))(2 4#14(0 128))(5#15 1 1)(0 2048)(2 6#14(0 11))(4 0#17#18)(0 55296)(2 1#19#20)(2 4#21(0 1))(5#22 0 0)((1 2)-128)(0 65533)(0#24 8#25)((1 2)-112)(0#27 8#20)((1 2)-120)(0#29 8(0 0))((1 2)-104)(0#31 8(1 27))((1 2)-96)(0#33 8(1 26))((1 2)-88)(0#35 8(1 25))((1 2)-80)(0#37 8(1 24))((1 2)-72)(0#39 8(1 23))((1 2)-64)(0#41 8(1 22))((1 2)-56)(0#43 8(1 21))((1 2)-48)(0#45 8(1 20))((1 2)-40)(0#47 8(1 19))((1 2)-32)(0#49 8(1 18))((1 2)-24)(0#51 8(1 9))((1 2)-16)(0#53 8(1 8))((1 2)-8)(0#55 8(1 1))(5(1 32)0 4294967295)(5(1 10)7028736 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#59#60#61(0 4))(5(1 12)7028736 140737479966696)(4(1 12)8)(3 152352 152608)((1 2)-4496)(0 4368)(9#66#67)(0 4496)(6#66#69)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#66#69#61(0 4))((1 12)0)(7#66#69#74(0 24))(4(1 10)8)(#8#10#11#12#13#16#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76)((1 2)-4496#69)(#78)((1 40)(1 41))(814184 814184 814828 990424 1336512 1337540)(0#81)(0#82(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 43))(6(1 44))(7(1 45))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 48))(13(1 49))(14(1 50))(15(1 51))(16(1 52))(17(1 53))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 54))(29(1 55))(30(1 56))(31(1 57))(#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114)(1 814828)(2 9#14(0 63))(2 0#117#1)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(1 12)#4#3(0 0)(0 0)#3#118#5(0 0)#6(1 54)(1 55)(1 56)(1 57))(3 6#14(0 11))(2 1#120(0 0))(2 4#121(0 1))(5#122 1 1)(5(1 32)128 4294967295)(5#15 0 0)(5(0 99)1 4611686018427387904)(4#126(1 0))(0#82#127)(0 814696)(1#129)(2#2)(8#3)(9(0 0))(10(1 12))(2 9#118(0 255))(11#135)(18(1 12))(19#4)(20#3)(21(0 0))(22(0 0))(23#3)(24#118)(25#5)(26(0 0))(27#6)(#130#131#86#87#88#89#90#132#133#134#136#95#96#97#98#99#100#137#138#139#140#141#142#143#144#145#146#111#112#113#114)(1 990424)(3 6#14(0 6))(2 9#149(0 63))(2 0#150#1)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(1 12)#4#3(0 0)#118#3#151#5#118#6(1 54)(1 55)(1 56)(1 57))(5(1 32)132 4294967295)(5(1 32)131 4294967295)(3 6#14(0 16))(2 1#155(0 0))(2 4#156(0 1))(5#157 1 1)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(5#122 0 0)(0 814676)(1#162)(8(1 10))(2 9#151(0 255))(11#165)(22#118)(26#118)(#163#131#86#87#88#89#90#164#133#134#166#95#96#97#98#99#100#137#138#139#140#167#142#143#144#168#146#111#112#113#114)(0 18446744073709551549)(0 18446744073709551551)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(1 12)#4#3(0 0)#170#3#171#5#170#6(1 54)(1 55)(1 56)(1 57))(0#29 8(0 6))(5(1 32)134 4294967295)(5(1 32)133 4294967295)(2 4(0 16)#155)(5#176 1 1)(5#157 0 0)(11(0 191))(22#170)(24#170)(26#170)(#163#131#86#87#88#89#90#164#133#134#179#95#96#97#98#99#100#137#138#139#140#180#142#181#144#182#146#111#112#113#114)(3 6#149(0 6))(2 9#184(0 63))(2 0#185#1)((1 0)(1 42)#2(1 3)(1 4)(1 43)(1 44)(1 45)(1 10)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 53)(1 12)#4#3(0 0)#151#3#186#5#118#6(1 54)(1 55)(1 56)(1 57))(5#176 0 0)(0 814656)(1#189)(2 9#186(0 255))(11#191)(22#151)(24#151)(#190#131#86#87#88#89#90#164#133#134#192#95#96#97#98#99#100#137#138#139#140#193#142#194#144#168#146#111#112#113#114)(4(1 10)4)(#8#10#11#12#13#16#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 28%positive "(814696#7#77 58#79()(0 99))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 35%positive "(#83(((814828#115()#77)#116))()())"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 143%positive "(814676#119(#8#10#11#123#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76)58#79()(0 99))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints3 : list (nat * CC.subst) := hints0.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 154%positive "(#128(((990424#147()(#126#8#10#11#123#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76))#148))()())"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 163%positive "(814656#152(#8#10#11#153#154#158#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76)58#79()(0 99))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 174%positive "(#128(((990424#169()(#126#8#10#11#153#154#158#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76))#148))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 176%positive "(814656#172(#8#10#11#173#174#175#177#153#154#178#159#160#161#124#125#23#26#28#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76)58#79()(0 99))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints5 : list (nat * CC.subst) := hints0.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 187%positive "(#128(((990424#183()(#126#8#10#11#173#174#175#177#153#154#178#159#160#161#124#125#23#26#28#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76))#148))()())"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 175%positive "(814636#187(#8#10#11#174#175#188#153#154#178#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76)58#79()(0 99))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints6 : list (nat * CC.subst) := hints0.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 186%positive "(#128(((990424#195()(#126#8#10#11#174#175#188#153#154#178#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#76))#148))()())"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 29%positive "(814696#7#197 58#79()(0 99))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints7 : list (nat * CC.subst) := hints1.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 36%positive "(#83(((814828#115()#197)#116))()())"%pstring.

Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 144%positive "(814676#119(#8#10#11#123#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196)58#79()(0 99))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints8 : list (nat * CC.subst) := hints1.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 155%positive "(#128(((990424#147()(#126#8#10#11#123#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196))#148))()())"%pstring.

Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 164%positive "(814656#152(#8#10#11#153#154#158#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196)58#79()(0 99))"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints9 : list (nat * CC.subst) := hints1.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 175%positive "(#128(((990424#169()(#126#8#10#11#153#154#158#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196))#148))()())"%pstring.

Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 177%positive "(814656#172(#8#10#11#173#174#175#177#153#154#178#159#160#161#124#125#23#26#28#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196)58#79()(0 99))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints10 : list (nat * CC.subst) := hints1.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 188%positive "(#128(((990424#183()(#126#8#10#11#173#174#175#177#153#154#178#159#160#161#124#125#23#26#28#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196))#148))()())"%pstring.

Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_cboth_R1 176%positive "(814636#187(#8#10#11#174#175#188#153#154#178#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196)58#79()(0 99))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_cboth_R1 6%positive "(#80)"%pstring.
Definition hints11 : list (nat * CC.subst) := hints1.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_convert_cboth_R1 187%positive "(#128(((990424#195()(#126#8#10#11#174#175#188#153#154#178#159#160#161#124#125#23#26#28#30#32#34#36#38#40#42#44#46#48#50#52#54#56#8#10#57#58#62#63#64#65#68#70#71#72#73#75#196))#148))()())"%pstring.
