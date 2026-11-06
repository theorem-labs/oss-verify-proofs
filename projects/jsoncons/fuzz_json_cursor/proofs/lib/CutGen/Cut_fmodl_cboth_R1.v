(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm9CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import FmodlAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fmodl_cboth_T Cut_fmodl_cboth_R0.
Definition dict_Cut_fmodl_cboth_R1 : CCDD.pt := CCDD.mk_table 2153%positive "((2 0(1 2)(0 -80))(0 1152921504606846976)(5#2 1 4611686018427387904)((1 2)-80)(0#4 8(1 24))((1 2)-72)(0#6 8(1 23))((1 2)-64)(0#8 8(1 22))((1 2)-56)(0#10 8(1 21))((1 2)-48)(0#12 8(1 20))((1 2)-40)(0#14 8(1 19))((1 2)-32)(0#16 8(1 18))((1 2)-24)(0#18 8(1 9))((1 2)-16)(0#20 8(1 8))((1 2)-8)(0#22 8(1 1))(5(1 2)140735332483264 140737488355328)(4(1 2)16)((1 2)-192)(6#26(0 192))(9#26(0 112))((1 2)-192(0 192))(#29)(0 1152921504606846975)(1323912 1324004 1324260 1324320 1324424 1324492 1324492 1324520 1324480 1324036 1324080 1287112 1282300 1282688 1287376 1284972 1261692 1324216 1324368 1324612 1324260 1324320 1324424 1324480 1324492 1324480 1324496 1336512 1337540)(0#32)(5#31 1 4611686018427387904)(2#1)(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(25(1 25))(26(1 26))(27(1 27))(0 576460752303423488)(5#44 1 4611686018427387904)(0 576460752303423487)(5#46 1 4611686018427387904)(5(1 58))(6(1 59))(7(1 60))(8(1 36))(9(1 37))(10(1 61))(11(1 62))(14(1 65))(15(1 66))(16(1 67))(17(1 68))(18(1 46))(19(1 47))(20(1 48))(21(1 49))(22(1 50))(23(1 51))(24(1 52))(28(1 69))(29(1 70))(30(1 71))(31(1 72))(4 0(0 -1)(1 46))(2 0#70(1 47))(2 0(1 57)(1 58))(0 -120)(2 0#72#73)(2 0(1 57)#73)(0 144115188075855872)(2 0(1 58)#76)(5#77 1 4611686018427387904)(5(1 39)4 18446744073709551615)(5(1 39)3 18446744073709551615)(4 0(0 -1)(1 38))(2 4(1 47)(1 46))(4 0(0 -1)#82)(2 0(1 39)#83)(2 0#81#84)(2 8#85#71)(2 1#86(0 0))(2 4#87(0 1))(5#88 1 1)(5(1 39)2 18446744073709551615)(5(1 39)1 18446744073709551615)(2 3#85(0 0))(5#92 0 0)(2 8(1 39)(1 47))(2 4(0 0)#94)(5#95 1 1)(5(1 38)281474976710656 562949953421311)(5(1 58)1 70000)(5(1 57)0 65535)(0 144115188075855871)(2 0(1 58)#100)(0 1324472)(1#102)(12(1 37))(13(1 36))(19#71)(5#101 1 4611686018427387904)(1 1282688)(0 72057594037927936)(5#109 1 4611686018427387904)(0 72057594037927935)(5#111 1 4611686018427387904)(0 281474976710656)(2 0(1 51)(0 120))(0 65535)(2 9#114#115)(2 9(1 50)(1 39))(2 8#116#117)(4 0#113#118)(0 281474976710655)(2 9(1 38)#120)(2 0#119#121)(0 58720256)(0 18446744073709551615)(0 18014398509481984)(5#125 1 4611686018427387904)(2 3(0 0)(1 51))(5#127 0 0)(0 18014398509481983)(5#129 1 4611686018427387904))"%pstring.

Definition t10 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fmodl_cboth_R1 250%positive "(1323980((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)(1 11)(1 10)(1 36)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 12)(1 13)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#3#5#7#9#11#13#15#17#19#21#23#24#25#27#28)48#30()#31)"%pstring.
Definition BL10 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fmodl_cboth_R1 3%positive "()"%pstring.
Definition hints10 : list (nat * CC.subst) := hints0.
Definition o10 : CAD.pout := CCDD.dec_pout_t dict_Cut_fmodl_cboth_R1 347%positive "((0#33(4#34(1 0)))(((1282300((1(0 1324000))#35#36#37#38#39#40(8(1 11))(9(1 10))(10(1 12))(11(1 13))(12(1 36))(13(1 37))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 12))(19(1 13))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))#41#42#43(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#34#3#5#7#9#11#13#15#17#19#21#23#24#25#27#28))(1 1282300)))()())"%pstring.

Definition t11 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fmodl_cboth_R1 251%positive "(1324024((1 0)(1 57)#1(1 3)(1 4)(1 58)(1 59)(1 60)(1 36)(1 37)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 68)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 25)(1 26)(1 27)(1 69)(1 70)(1 71)(1 72))(#45#24#25#27#28#5#7#9#11#13#15#17#19#21#23)73#30()#46)"%pstring.
Definition BL11 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fmodl_cboth_R1 3%positive "()"%pstring.
Definition hints11 : list (nat * CC.subst) := hints1.
Definition o11 : CAD.pout := CCDD.dec_pout_t dict_Cut_fmodl_cboth_R1 217%positive "((0#33(4#47(1 0)))(((1287376((1(0 1324036))#35#36#37#48#49#50#51#52#53#54(12(1 61))(13(1 62))#55#56#57#58#59#60#61#62#63#64#65#41#42#43#66#67#68#69)()(#47#45#24#25#27#28#5#7#9#11#13#15#17#19#21#23))(1 1287376)))()())"%pstring.

Definition t12 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fmodl_cboth_R1 279%positive "(1324460((1 0)(1 59)#1(1 3)(1 4)(1 60)(1 61)(1 62)(1 36)(1 37)(1 63)(1 64)(1 65)(1 66)(1 67)(1 68)(1 69)(1 70)(1 46)#71(1 48)(1 49)(1 50)#74#75(1 25)(1 26)(1 27)(1 71)(1 72)(1 73)(1 74))(#78#79#80#89#90#91#93#96#97#98#99#97#96#24#25#27#28#5#7#9#11#13#15#17#19#21#23)75#30()#101)"%pstring.
Definition BL12 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fmodl_cboth_R1 3%positive "()"%pstring.
Definition hints12 : list (nat * CC.subst) := hints3.
Definition o12 : CAD.pout := CCDD.dec_pout_t dict_Cut_fmodl_cboth_R1 332%positive "((0#33(16 0(1 0)))(((1282688(#103#35#36#37(5(1 60))(6(1 61))(7(1 62))#51#52(10(1 63))(11(1 64))#104#105(14(1 67))(15(1 68))(16(1 69))(17(1 70))#59#106#61#62#63(23#74)(24#75)#41#42#43(28(1 71))(29(1 72))(30(1 73))(31(1 74)))()(#107#78#79#80#89#90#91#93#96#97#98#99#97#96#24#25#27#28#5#7#9#11#13#15#17#19#21#23))#108))((0(0#107)))())"%pstring.

Definition t13 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fmodl_cboth_R1 280%positive "(1324460((1 0)(1 57)#1(1 3)(1 4)(1 58)(1 59)(1 60)(1 36)(1 37)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 68)(1 46)#71(1 48)(1 49)(1 50)(1 51)(1 52)(1 25)(1 26)(1 27)(1 69)(1 70)(1 71)(1 72))(#110#79#80#89#90#91#93#96#97#97#96#24#25#27#28#5#7#9#11#13#15#17#19#21#23)73#30()#111)"%pstring.
Definition BL13 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fmodl_cboth_R1 3%positive "()"%pstring.
Definition hints13 : list (nat * CC.subst) := hints4.
Definition o13 : CAD.pout := CCDD.dec_pout_t dict_Cut_fmodl_cboth_R1 222%positive "((0#33(4#112(1 0)))(((1282688(#103#35#36#37#48#49#50#51#52#53#54#104#105#55#56#57#58#59#106#61#62#63#64#65#41#42#43#66#67#68#69)()(#112#110#79#80#89#90#91#93#96#97#97#96#24#25#27#28#5#7#9#11#13#15#17#19#21#23))#108))()())"%pstring.

Definition t14 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_fmodl_cboth_R1 243%positive "(1324616((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)(1 47)#122#123#119#120#124#116#114(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 52)(1 25)(1 26)(1 27)(1 53)(1 54)(1 55)(1 56))(#126#128#24#25#27#28#5#7#9#11#13#15#17#19#21#23)57#30()#129)"%pstring.
Definition BL14 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_fmodl_cboth_R1 3%positive "()"%pstring.
Definition hints14 : list (nat * CC.subst) := hints7.
Definition o14 : CAD.pout := CCDD.dec_pout_t dict_Cut_fmodl_cboth_R1 292%positive "((0#33(4#130(1 0)))(((1261692((1(0 1324620))#35#36#37#38#39#40(8(1 47))(9#122)(10#123)(11#119)(12#120)(13#124)(14#116)(15#114)(16(1 44))(17(1 45))#59#60#61#62#63#64#65#41#42#43(28(1 53))(29(1 54))(30(1 55))(31(1 56)))()(#130#126#128#24#25#27#28#5#7#9#11#13#15#17#19#21#23))(1 1261692)))()())"%pstring.
