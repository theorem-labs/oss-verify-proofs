(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSums ParseSums3C.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pn_csrc_T Cut_pn_csrc_R0 Cut_pn_csrc_R1.
Definition dict_Cut_pn_csrc_R2 : CCD.pt := CCD.mk_table 3469%positive "((0 -112)(2 0(1 2)#1)(4 0(0 -1)(1 46))(2 0(1 32)#3)(2 0(1 11)#4)((1 13)0)(0#6 4(1 88))(5(1 88)0 31)(4 0(0 16)(1 46))(2 0#9(0 1))(5#10 1 4611686018427387904)(5(1 71)132 67108864)(4 0(0 -1)(1 32))(4 0(0 -1)(1 35))(4 0(0 2)(1 71))(2 0(1 46)#15)(2 0#14#16)(2 0#13#17)(2 0#18(0 -1))(5#19 0 140737488355328)(4#15 8)(5(1 70)4096 140737488355328)(4(1 70)16)((1 70)0)((0 0)65536)(0 942080)(7#24#15#25#26)((1 2)-9568)(0 9568)(7#24#15#28#29)((1 11)0)(7#24#15#31(1 32))((1 12)0)(7#24#15#33(0 48))((1 10)0)(7#24#15#35(0 272))(7#24#15#6(0 16))((1 37)0)(7#24#15#38(1 39))(2 0#3(1 70))(2 0(1 35)#40)(2 0(1 32)#41)(#42 0)(7#43(0 1)#28#29)(7#43(0 1)#31(1 32))(7#43(0 1)#33(0 48))(7#43(0 1)#35(0 272))(7#43(0 1)#6(0 16))(7#43(0 1)#38(1 39))(2 0#9(0 2))(5#50 1 4611686018427387904)(5(1 34)132 67108864)(4 0(0 2)(1 34))(2 0#53#14)(2 0#54(0 -1))(5#55 0 140737488355328)(4#53 8)(5(1 36)4096 140737488355328)(4(1 36)16)(6#35(0 272))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(6#6(0 16))(5(1 13)1099511627776 140737488355328)(0 770344)(0#33 8#65)(5(1 12)1099511627776 140737488355328)(2#31(1 32)1)(9#31(1 32))(5(1 32)0 16384)(5(1 11)4096 140737488355328)(5(1 37)4096 140737488355328)(5(1 38)1 1027)(5(1 39)66 1056)(4 0(0 -1)(1 38))(2 0#75(1 39))(5#76 0 1056)(5(1 33)0 67108863)(5(1 42)0 7)((1 2)-8)(0#80 8(1 1))((1 2)-16)(0#82 8(1 8))((1 2)-24)(0#84 8(1 9))((1 2)-32)(0#86 8(1 18))((1 2)-40)(0#88 8(1 19))((1 2)-48)(0#90 8(1 20))((1 2)-56)(0#92 8(1 21))((1 2)-64)(0#94 8(1 22))((1 2)-72)(0#96 8(1 23))((1 2)-80)(0#98 8(1 24))((1 2)-88)(0#100 8(1 25))((1 2)-96)(0#102 8(1 26))(0 9472)(9#28#104)(6#28#29)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 793640)(7#28#29#35(0 272))(7#28#29#6(0 16))(7#28#29#33(0 48))(7#28#29#31(1 32))((1 36)0)(7#28#29#114#53)(7#28#29#38(1 39))(7#35(0 272)#6(0 16))(7#35(0 272)#33(0 48))(7#35(0 272)#31(1 32))(7#35(0 272)#114#53)(7#35(0 272)#38(1 39))(7#6(0 16)#33(0 48))(7#6(0 16)#31(1 32))(7#6(0 16)#114#53)(7#6(0 16)#38(1 39))(7#33(0 48)#31(1 32))(7#33(0 48)#114#53)(7#33(0 48)#38(1 39))(7#31(1 32)#114#53)(7#31(1 32)#38(1 39))(7#114#53#38(1 39))(7#114#53#25#26)(7#38(1 39)#25#26)(7#31(1 32)#25#26)(5(1 35)0 67108863)(2 0(1 33)#14)(2 0#13#136)(5#137 0 67108864)(5(1 46)1 16384)(5#4 0 16384)(5#50 0 4611686018427387904)(#7#8#11#12#20#21#22#23#27#30#32#34#36#37#39#44#45#46#47#48#49#51#52#56#57#58#59#60#61#62#63#64#66#67#68#69#70#71#72#73#74#77#78#79#81#83#85#87#89#91#93#95#97#99#101#103#105#106#107#108#109#110#111#112#113#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132#133#134#135#138#139#140#141)((1 2)-9568#29)(#143)(4 0(0 2)(1 90))((1 89)#145)((1 91)(1 92))(252140 252272 252316 252728 252336 252372 253012 253032 253068 252340 252388 252744 253084 253412 252476 252896 253164 252952 252640 252528 253336 253252 253612 252780 252844 252424 253568 253524 253120 253520 259824 244064 249024 249068 252276 252320 252340 252388 252744 253016 253036 253084 252292 252356 252396 252620 252752 253052 253092 253228 252228 744000 745408)(0#148)(0#149(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 94))(6(1 95))(7(1 96))(8(1 8))(9(1 9))(10#5)(11(1 98))(12(1 99))(13(1 100))(14(1 101))(15(1 102))(16(1 103))(17(1 104))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 105))(29(1 106))(30(1 107))(31(1 108))(#151#152#153#154#155#156#157#158#159#160#161#162#163#164#165#166#167#168#169#170#171#172#173#174#175#176#177#178#179#180#181)(253520#182()#142)(1 253520)(#183#184)(#185))"%pstring.

Definition t45 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pn_csrc_R2 217%positive "(253460((1 0)(1 93)#2(1 3)(1 4)(1 94)(1 95)(1 96)(1 10)(1 11)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 104)(1 13)(1 12)#5(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 27)(1 105)(1 106)(1 107)(1 108))#142 109#144()#9)"%pstring.
Definition BL45 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pn_csrc_R2 11%positive "(#146#147)"%pstring.
Definition hints45 : list (nat * CC.subst) := hints29.
Definition o45 : CA.pout := CCD.dec_pout_t dict_Cut_pn_csrc_R2 15%positive "(#150#186()())"%pstring.

Definition t46 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pn_csrc_R2 217%positive "(252520((1 0)(1 93)#2(1 3)(1 4)(1 94)(1 95)(1 96)(1 10)(1 11)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 104)(1 13)(1 12)(1 60)(1 61)(1 62)#5(1 63)(1 64)(1 65)(1 27)(1 105)(1 106)(1 107)(1 108))#142 109#144()#9)"%pstring.
Definition BL46 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pn_csrc_R2 11%positive "(#146#147)"%pstring.
Definition hints46 : list (nat * CC.subst) := hints30.
Definition o46 : CA.pout := CCD.dec_pout_t dict_Cut_pn_csrc_R2 15%positive "(#150#186()())"%pstring.

Definition t47 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pn_csrc_R2 217%positive "(252940((1 0)(1 93)#2(1 3)(1 4)(1 94)(1 95)(1 96)(1 10)(1 11)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 104)(1 13)(1 12)(1 60)#5(1 61)(1 62)(1 63)(1 64)(1 65)(1 27)(1 105)(1 106)(1 107)(1 108))#142 109#144()#9)"%pstring.
Definition BL47 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pn_csrc_R2 11%positive "(#146#147)"%pstring.
Definition hints47 : list (nat * CC.subst) := hints31.
Definition o47 : CA.pout := CCD.dec_pout_t dict_Cut_pn_csrc_R2 15%positive "(#150#186()())"%pstring.

Definition t48 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pn_csrc_R2 217%positive "(253208((1 0)(1 93)#2(1 3)(1 4)(1 94)(1 95)(1 96)(1 10)(1 11)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 104)(1 13)(1 12)(1 60)(1 61)(1 62)(1 63)#5(1 64)(1 65)(1 27)(1 105)(1 106)(1 107)(1 108))#142 109#144()#9)"%pstring.
Definition BL48 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pn_csrc_R2 11%positive "(#146#147)"%pstring.
Definition hints48 : list (nat * CC.subst) := hints32.
Definition o48 : CA.pout := CCD.dec_pout_t dict_Cut_pn_csrc_R2 15%positive "(#150#186()())"%pstring.
