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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_scalbn_xboth_T Cut_scalbn_xboth_R0 Cut_scalbn_xboth_R1.
Definition dict_Cut_scalbn_xboth_R2 : CCDD.pt := CCDD.mk_table 1602%positive "((0 18446744073709548656)(0 1099511627775)(5#2 1 4611686018427387904)(2 4#1(1 10))(4 0(0 -1)(1 10))(0 -1992)(2 0#5#6)(5#7 0 18446744073709549624)(5(1 10)0 18446744073709549624)(0 18446744073709549624)(2 4#10(1 10))(5#11 0 0)(0 1099511627776)(5#13 1 4611686018427387904)(0 18446744073709550593)(2 3#15(1 10))(5#16 0 0)(0 1024)(2 3(1 10)#18)(5#19 1 1)(5(1 2)140735332483072 140737488355328)(4(1 2)16)(3 65536 1466368)(0 1099511627774)(1355212 1355336 1355360 1355232 1355256 1355288 1355312 1355352 1355356 1355212 1355236 1355260 1355284 1355308 1355332 1355356 1402040 1403068)(0#25)(0 1982)(5#27 1 4611686018427387904)(5#24 0 4611686018427387904)(0 1099511625792)(5#30 0 4611686018427387904)(4#31(1 0))(4#29#32)(4#28#33)(0#26#34)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(0 1938)(2 0(1 10)#45)(11#1)(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(#21#22#23#28#29#31)(46(1 31))(45(1 30))(44(1 29))(43(1 28))(42(1 17))(41(1 16))(40(1 15))(39(1 14))(38(1 13))(37(1 12))(36#1)(34(1 7))(33(1 6))(32(1 5))(0 18446744073709550594)(0 3069)(2 4(1 10)#84)(0 -2047)(2 0(1 10)#86)(5#87 0 18446744073709549568)(5(1 10)2047 18446744073709551615)(0 2047)(2 4(1 10)#90)(5#91 0 0)(5(1 10)1024 18446744073709551615)(5#19 0 0)(0 -2046)(2 0(1 10)#95)(11#84)(36#84)(0 1023)(0 4503599627370496)(4 0#100(1 35))(0 4607182418800017408)(2 0#101#102)(0 1099511625791)(5#104 1 4611686018427387904)(5#30 1 4611686018427387904)(#105#106#21#22#23))"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_scalbn_xboth_R2 364%positive "(1355316((1 0)(1 1)(1 2)(1 3)(1 4)(1 5)(1 6)(1 7)(1 8)(1 9)(1 10)#1(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3(5(2 0(1 10)(0 2960))1 968)(5(1 10)18446744073709548657 18446744073709549624)(5(1 10)18446744073709548656 18446744073709549624)(5#4 1 1)#8#9#12#14#17#20#21#22#23)32()()#24)"%pstring.
Definition BL5 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_scalbn_xboth_R2 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints2.
Definition o5 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_xboth_R2 183%positive "(#35(((1355336(#36#37#38#39#40#41#42#43#44(10#46)#47#48#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67)()#68)(0 1(#69#70#71#72#73#74#75#76#77#78#79(35#46)#80#81#82))))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_scalbn_xboth_R2 305%positive "(1355316((1 0)(1 1)(1 2)(1 3)(1 4)(1 5)(1 6)(1 7)(1 8)(1 9)#1#1(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3(5(2 0#5(0 -2960))0 18446744073709548656)(5(1 10)0 18446744073709548656)(5#4 0 0)#8#9#12#14#17#20#21#22#23)32()()#24)"%pstring.
Definition BL6 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_scalbn_xboth_R2 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints2.
Definition o6 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_xboth_R2 183%positive "(#35(((1355336(#36#37#38#39#40#41#42#43#44(10#83)#47#48#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67)()#68)(0 1(#69#70#71#72#73#74#75#76#77#78#79(35#83)#80#81#82))))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_scalbn_xboth_R2 278%positive "(1355260((1 0)(1 1)(1 2)(1 3)(1 4)(1 5)(1 6)(1 7)(1 8)(1 9)(1 10)#84(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3(5(2 0#5#84)1 1022)(5(1 10)2047 3068)(5#85 1 1)#88#89#92#14#93#94#21#22#23)32()()#24)"%pstring.
Definition BL7 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_scalbn_xboth_R2 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints3.
Definition o7 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_xboth_R2 183%positive "(#35(((1355336(#36#37#38#39#40#41#42#43#44(10#96)#97#48#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67)()#68)(0 1(#69#70#71#72#73#74#75#76#77#78#98(35#96)#80#81#82))))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_scalbn_xboth_R2 317%positive "(1355260((1 0)(1 1)(1 2)(1 3)(1 4)(1 5)(1 6)(1 7)(1 8)(1 9)#84#84(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3(5(2 0(1 10)(0 -3069))0 18446744073709548546)(5(1 10)3069 18446744073709551615)(5#85 0 0)#88#89#92#14#93#94#21#22#23)32()()#24)"%pstring.
Definition BL8 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_scalbn_xboth_R2 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints3.
Definition o8 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_xboth_R2 183%positive "(#35(((1355336(#36#37#38#39#40#41#42#43#44(10#99)#97#48#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67)()#68)(0 1(#69#70#71#72#73#74#75#76#77#78#98(35#99)#80#81#82))))()())"%pstring.
(* [comment removed for export] *)
Definition t9 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_scalbn_xboth_R2 221%positive "(1355360((1 0)(1 1)(1 2)(1 3)(1 4)(1 32)(1 33)(1 34)(1 8)(1 9)#103#102(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 43)(1 44)(1 45)(1 46))#107 47()()(0 1099511625790))"%pstring.
Definition BL9 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_scalbn_xboth_R2 3%positive "()"%pstring.
Definition hints9 : list (nat * CC.subst) := hints4.
Definition o9 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_xboth_R2 235%positive "((1 0)(((1355360(#36#37#38#39(5(1 32))(6(1 33))(7(1 34))#43#44(10#103)(11#102)(12(1 37))(13(1 38))(14(1 39))(15(1 40))(16(1 41))(17(1 42))#54#55#56#57#58#59#60#61#62#63(28(1 43))(29(1 44))(30(1 45))(31(1 46)))()#107)(1 1355360)))()())"%pstring.
