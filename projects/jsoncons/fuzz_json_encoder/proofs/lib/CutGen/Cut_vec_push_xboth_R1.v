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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_push_xboth_T Cut_vec_push_xboth_R0.
Definition dict_Cut_vec_push_xboth_R1 : CCD.pt := CCD.mk_table 3143%positive "((2 0(1 2)(0 -80))(0 2147450880)(2 0(1 32)(1 33))((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 11)#2(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(3 1459384 1463120)((0 0)1497016)(0#6 8#2)(2 6#3(0 3))(#8 2147450880)(0#9 1(1 36))(5(0 16)1 4611686018427387904)((1 2)-64)(2 0#3(0 1))(0#12 8#13)((1 2)-72)(0#15 8#3)((1 2)-80)(0#17 8(1 10))((1 2)-56)(2 0(1 10)(0 8))(2 6#20(0 3))(2 0#21#2)(0#19 8#22)((1 2)-48)(0#24 8#20)((1 2)-40)(0 858136)(0#26 8#27)(4 0(0 -1)(1 33))(2 0#29(1 34))(5#30 1 123143280689152)(2 0(1 32)(1 34))(2 4#3#32)(5#33 1 1)((1 2)-32)(0#35 8(1 18))((1 2)-24)(0#37 8(1 9))((1 2)-16)(0#39 8(1 8))((1 2)-8)(0#41 8(1 1))((1 10)0)(0#43 8(1 32))((1 10)8)(0#45 8#3)((1 10)16)(0#47 8#32)(6#43(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#52 2147450880)(1#53(0 3))((0 0)2147446784)(0 17592186048512)(7#55#56#43(0 24))((1 11)0)(0#58 1(1 37))(5(1 37)0 255)(5(1 11)1048576 140737488355327)(7#55#56#58(0 1))(2 6(1 11)(0 3))(#63 2147450880)(0#64 1(1 35))((1 32)0)(2#66(1 33)0)(6#66(1 34))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 33)0 134217728)(5#30 0 134217728)(5(1 34)1 134217728)((1 2)-8240)(0 8160)(9#74#75)(0 8240)(6#74#77)(5(1 2)140735332491312 140737488355328)(4(1 2)16)(2 6#1(0 3))(#81 2147450880)(1#82(0 3))(7#74#77#43(0 24))(7#74#77#58(0 1))(7#74#77#66(1 34))(7#43(0 24)#66(1 34))(7#58(0 1)#66(1 34))(7#43(0 24)#58(0 1))(2 6(1 32)(0 3))(#90 2147450880)(2 0(1 34)(0 7))(2 6#92(0 3))(7#53(0 3)#91#93)(7#64(0 1)#91#93)(7#43(0 24)#91#93)(7#58(0 1)#91#93)(7#82(0 3)#91#93)(7#53(0 3)#82(0 3))(5(1 35)0 0)(5(1 36)0 0)((1 2)-8240#77)((1 10)0(0 24))((1 32)0(1 34))(#102#103#104)((1 32)(1 34))(858048 858048 858048 858048 858196 859068 858448 1402040 1403068)(0#107)(0#108(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10#13)(11(0 2))(12(0 0))(13#13)(14#2)(15(0 0))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132#133#134#135#136#137#138#139#140)(0#45 8#13)((1 2)-88)(0 858388)(0#143 8#144)(0#15 8#13)(#3 0)(0#147 1(1 37))(0 8152)(9#74#149)(1 858196)(2 0(1 2)(0 -32))(2 0(1 48)(1 50))((1 0)(1 51)#152(1 3)(1 4)(1 52)(1 53)(1 54)#20#22#153(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 62)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 63)(1 64)(1 65)(1 66))(0#43 8(1 48))(2 0(1 48)(1 49))(0#47 8#156)(5(1 48)17594333495296 140737479966720)(5(1 50)0 134217728)(4 0(0 -1)(1 34))(2 0(1 33)#160)(5#161 0 123143280689151)(5#33 0 0)(0 8208)(9#74#164)(#102#103)((1 48)(1 49))(5(1 52))(6(1 53))(7(1 54))(10#153)(12(1 57))(13(1 58))(14(1 59))(15(1 60))(16(1 61))(17(1 62))(28(1 63))(29(1 64))(30(1 65))(31(1 66))(#110#111#112#113#168#169#170#117#118#171#120#172#173#174#175#176#177#127#128#129#130#131#132#133#134#135#136#178#179#180#181)(0#45 8#153)(5(1 36)1 7)(2 9(1 33)(0 7))(4 0(0 -1)#185)(2 0(1 36)#186)(5#187 1 7)(5(1 35)1 7)(2 9(1 11)(0 7))(4 0(0 -1)#190)(2 0(1 35)#191)(5#192 1 7))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 196%positive "(858316#4(#5#7#10#11#14#16#18#23#25#28#31#34#36#38#40#42#5#7#44#46#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#76#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#101)64#105()(0 15))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#106)"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 204%positive "(#109(((858196#141()(#142#145#146#148#11#14#18#23#25#28#31#34#36#38#40#42#44#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#150#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#101))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 181%positive "(858156#154(#5#7#155#157#158#159#11#162#163#36#38#40#42#5#7#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#101)67#166()(0 15))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#167)"%pstring.
Definition hints5 : list (nat * CC.subst) := hints0.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 183%positive "(#109(((858196#182()(#183#155#157#158#159#11#162#163#36#38#40#42#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#101))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 200%positive "(858316#4(#5#7#10#11#14#16#18#23#25#28#31#34#36#38#40#42#5#7#44#46#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#76#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#184#188)64#105()(0 15))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#106)"%pstring.
Definition hints6 : list (nat * CC.subst) := hints1.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 208%positive "(#109(((858196#141()(#142#145#146#148#11#14#18#23#25#28#31#34#36#38#40#42#44#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#150#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#184#188))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 185%positive "(858156#154(#5#7#155#157#158#159#11#162#163#36#38#40#42#5#7#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#184#188)67#166()(0 15))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#167)"%pstring.
Definition hints7 : list (nat * CC.subst) := hints1.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 187%positive "(#109(((858196#182()(#183#155#157#158#159#11#162#163#36#38#40#42#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#100#184#188))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 200%positive "(858316#4(#5#7#10#11#14#16#18#23#25#28#31#34#36#38#40#42#5#7#44#46#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#76#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#101)64#105()(0 15))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#106)"%pstring.
Definition hints8 : list (nat * CC.subst) := hints2.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 208%positive "(#109(((858196#141()(#142#145#146#148#11#14#18#23#25#28#31#34#36#38#40#42#44#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#150#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#101))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 185%positive "(858156#154(#5#7#155#157#158#159#11#162#163#36#38#40#42#5#7#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#101)67#166()(0 15))"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#167)"%pstring.
Definition hints9 : list (nat * CC.subst) := hints2.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 187%positive "(#109(((858196#182()(#183#155#157#158#159#11#162#163#36#38#40#42#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#101))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 204%positive "(858316#4(#5#7#10#11#14#16#18#23#25#28#31#34#36#38#40#42#5#7#44#46#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#76#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#184#188)64#105()(0 15))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#106)"%pstring.
Definition hints10 : list (nat * CC.subst) := hints3.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 212%positive "(#109(((858196#141()(#142#145#146#148#11#14#18#23#25#28#31#34#36#38#40#42#44#48#49#50#51#54#57#59#60#61#62#65#67#68#69#70#71#72#73#150#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#184#188))#151))()())"%pstring.
(* [comment removed for export] *)
Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_push_xboth_R1 189%positive "(858156#154(#5#7#155#157#158#159#11#162#163#36#38#40#42#5#7#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#184#188)67#166()(0 15))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_push_xboth_R1 7%positive "(#167)"%pstring.
Definition hints11 : list (nat * CC.subst) := hints3.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_vec_push_xboth_R1 191%positive "(#109(((858196#182()(#183#155#157#158#159#11#162#163#36#38#40#42#49#50#51#54#57#59#60#61#62#65#69#70#71#72#73#165#78#79#80#83#84#85#86#87#88#89#94#95#96#97#98#99#189#193#184#188))#151))()())"%pstring.
