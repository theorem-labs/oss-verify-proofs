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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_push_xasan_T Cut_vec_push_xasan_R0.
Definition dict_Cut_vec_push_xasan_R1 : CCD.pt := CCD.mk_table 2930%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 8))(2 0(1 32)(1 33))(2 6#2(0 3))(0 2147450880)(2 0#4#5)((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)#2(1 11)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)#3#6#5(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(3 1444792 1448528)((0 0)1482488)(0#9 8#5)(2 6#3(0 3))(#11 2147450880)(0#12 1(1 36))(5(0 16)1 4611686018427387904)(4 0(0 -1)(1 33))(2 0#15(1 34))(5#16 1 123143280689152)(2 0(1 32)(1 34))(2 4#3#18)(5#19 1 1)((1 2)-48)(0#21 8(1 20))((1 2)-40)(0#23 8(1 19))((1 2)-32)(0#25 8(1 18))((1 2)-24)(0#27 8(1 9))((1 2)-16)(0#29 8(1 8))((1 2)-8)(0#31 8(1 1))((1 10)0)(0#33 8(1 32))((1 10)8)(0#35 8#3)((1 10)16)(0#37 8#18)(6#33(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#42 2147450880)(1#43(0 3))((0 0)2147446784)(0 17592186048512)(7#45#46#33(0 24))((1 11)0)(0#48 1(1 37))(5(1 37)0 255)(5(1 11)1048576 140737488355327)(7#45#46#48(0 1))(2 6(1 11)(0 3))(#53 2147450880)(0#54 1(1 35))((1 32)0)(2#56(1 33)0)(6#56(1 34))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 134217728)(5#16 0 134217728)(5(1 34)1 134217728)((1 2)-8240)(0 8192)(9#64#65)(0 8240)(6#64#67)(5(1 2)140735332491312 140737488355328)(4(1 2)16)(7#64#67#33(0 24))(7#64#67#48(0 1))(7#64#67#56(1 34))(7#33(0 24)#56(1 34))(7#48(0 1)#56(1 34))(7#33(0 24)#48(0 1))(2 6(1 32)(0 3))(#77 2147450880)(2 0(1 34)(0 7))(2 6#79(0 3))(7#43(0 3)#78#80)(7#54(0 1)#78#80)(7#33(0 24)#78#80)(7#48(0 1)#78#80)(5(1 35)0 0)(5(1 36)0 0)((1 2)-8240#67)((1 10)0(0 24))((1 32)0(1 34))(#87#88#89)((1 32)(1 34))(841320 841320 841320 841320 841520 842060 841580 1387168 1388196)(0#92)(0#93(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(2 0#3(0 1))(10#104)(11(0 0))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(#95#96#97#98#99#100#101#102#103#105#106#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126)(0#35 8#104)(#3 0)(0#129 1(1 37))(1 841520)(2 0(1 48)(1 50))((1 0)(1 51)#1(1 3)(1 4)(1 52)(1 53)(1 54)#2(1 11)#132(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 62)#3#6#5(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 63)(1 64)(1 65)(1 66))(0#33 8(1 48))(2 0(1 48)(1 49))(0#37 8#135)(4 0(0 -1)(1 34))(2 0(1 33)#137)(5#138 0 123143280689151)(5#19 0 0)(#87#88)((1 48)(1 49))(5(1 52))(6(1 53))(7(1 54))(10#132)(12(1 57))(13(1 58))(14(1 59))(15(1 60))(16(1 61))(17(1 62))(28(1 63))(29(1 64))(30(1 65))(31(1 66))(#95#96#97#98#143#144#145#102#103#146#106#147#148#149#150#151#152#113#114#115#116#117#118#119#120#121#122#153#154#155#156)(0#35 8#132)(5(1 36)1 7)(2 9(1 33)(0 7))(4 0(0 -1)#160)(2 0(1 36)#161)(5#162 1 7)(12#160)(#95#96#97#98#99#100#101#102#103#105#106#164#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126)(5(1 35)1 7)(2 9(1 11)(0 7))(4 0(0 -1)#167)(2 0(1 35)#168)(5#169 1 7))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 174%positive "(841424#7(#8#10#13#14#17#20#22#24#26#28#30#32#8#10#34#36#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#86)64#90()(0 15))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 6%positive "(#91)"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 174%positive "(#94(((841520#127()(#128#130#14#17#20#22#24#26#28#30#32#34#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#86))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 169%positive "(841480#133(#8#10#134#136#14#139#140#22#24#26#28#30#32#8#10#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#86)67#141()(0 15))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 7%positive "(#142)"%pstring.
Definition hints5 : list (nat * CC.subst) := hints0.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 168%positive "(#94(((841520#157()(#158#134#136#14#139#140#22#24#26#28#30#32#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#86))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 179%positive "(841424#7(#8#10#13#14#17#20#22#24#26#28#30#32#8#10#34#36#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#159#163)64#90()(0 15))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 6%positive "(#91)"%pstring.
Definition hints6 : list (nat * CC.subst) := hints1.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 179%positive "(#94(((841520#165()(#128#130#14#17#20#22#24#26#28#30#32#34#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#159#163))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 174%positive "(841480#133(#8#10#134#136#14#139#140#22#24#26#28#30#32#8#10#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#159#163)67#141()(0 15))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 7%positive "(#142)"%pstring.
Definition hints7 : list (nat * CC.subst) := hints1.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 173%positive "(#94(((841520#157()(#158#134#136#14#139#140#22#24#26#28#30#32#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#85#159#163))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 179%positive "(841424#7(#8#10#13#14#17#20#22#24#26#28#30#32#8#10#34#36#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#86)64#90()(0 15))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 6%positive "(#91)"%pstring.
Definition hints8 : list (nat * CC.subst) := hints2.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 179%positive "(#94(((841520#127()(#128#130#14#17#20#22#24#26#28#30#32#34#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#86))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 174%positive "(841480#133(#8#10#134#136#14#139#140#22#24#26#28#30#32#8#10#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#86)67#141()(0 15))"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 7%positive "(#142)"%pstring.
Definition hints9 : list (nat * CC.subst) := hints2.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 173%positive "(#94(((841520#157()(#158#134#136#14#139#140#22#24#26#28#30#32#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#86))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 184%positive "(841424#7(#8#10#13#14#17#20#22#24#26#28#30#32#8#10#34#36#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#159#163)64#90()(0 15))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 6%positive "(#91)"%pstring.
Definition hints10 : list (nat * CC.subst) := hints3.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 184%positive "(#94(((841520#165()(#128#130#14#17#20#22#24#26#28#30#32#34#38#39#40#41#44#47#49#50#51#52#55#57#58#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#159#163))#131))()())"%pstring.
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xasan_R1 179%positive "(841480#133(#8#10#134#136#14#139#140#22#24#26#28#30#32#8#10#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#159#163)67#141()(0 15))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xasan_R1 7%positive "(#142)"%pstring.
Definition hints11 : list (nat * CC.subst) := hints3.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xasan_R1 178%positive "(#94(((841520#157()(#158#134#136#14#139#140#22#24#26#28#30#32#39#40#41#44#47#49#50#51#52#55#59#60#61#62#63#66#68#69#70#71#72#73#74#75#76#81#82#83#84#166#170#159#163))#131))()())"%pstring.
