(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSums ParseSums2 ParseSomeKn.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallKn.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums2.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import VisitSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_end_integer_value_csrc_T Cut_end_integer_value_csrc_R0 Cut_end_integer_value_csrc_R1 Cut_end_integer_value_csrc_R2.
Definition dict_Cut_end_integer_value_csrc_R3 : CCD.pt := CCD.mk_table 4450%positive "((2 0(1 2)(0 -64))((1 0)(1 92)#1(1 3)(1 4)(1 93)(1 94)(1 95)(1 10)(1 12)(1 96)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 11)(1 37)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 104)(1 105)(1 106)(1 107))((1 12)0)(0#3 4(1 87))(5(1 87)0 31)(5(0 98)1 4611686018427387904)((1 11)8)(0#7 8(0 1))((1 11)32)(0#9 8(1 37))((1 11)40)(0#11 8(1 36))(5(0 99)1 4611686018427387904)((1 2)-56)(0#14 8(1 36))((1 2)-64)(0#16 8(1 37))(0 -9223372036854775808)(2 0(1 54)#18)(5#19 1 9223372036854775807)(5(1 54)9223372036854775809 18446744073709551615)(5(1 54)9223372036854775808 18446744073709551615)(0 9223372036854775808)(2 4#23(1 54))(5#24 1 1)(4 0(0 -1)(1 60))(2 0#26(0 1))(5#27 1 1)(5(1 60)0 0)(2 1(1 60)(0 0))(2 4#30(0 1))(5#31 1 1)(5(1 60)0 34)(5(0 100)1 4611686018427387904)(2 0(1 36)(0 -1))(5#35 0 67108862)(2 1(1 36)(0 0))(2 4#37(0 1))(5#38 0 0)((1 2)-40)(0#40 8(1 19))((1 2)-32)(0#42 8(1 18))((1 2)-24)(0#44 8(1 9))((1 2)-16)(0#46 8(1 8))((1 2)-8)(0#48 8(1 1))(4 0(0 -1)(1 52))(2 0#50(0 46))(5#51 1 1)(5(1 52)45 45)(5(1 52)45 255)(2 1(1 52)(0 45))(2 4#55(0 1))(5#56 1 1)(5(1 52)0 255)(4 0(0 2)(1 35))(2 0#59(0 1))(6 0 0 1#60)(2 9#61(0 1))(5#62 1 1)(5(1 35)132 67108864)(4 0(0 -1)(1 36))(2 0#59#65)(2 0#66(0 -1))(5#67 0 140737488355328)(4#59 8)(5(1 37)4096 140737488355328)(4(1 37)16)(5(1 38)4096 140737488355328)(5(1 39)1 1027)(5(1 40)66 1056)(4 0(0 -1)(1 39))(2 0#75(1 40))(5#76 0 1056)(5(1 36)0 67108863)(5(1 41)0 1025)(5(0 17)0 255)(5(1 43)0 255)(5(1 44)0 255)(5(0 1)0 1)(5(1 46)0 1)((1 2)-576)((1 37)0)(7#85(0 576)#86#59)((1 38)0)(7#85(0 576)#88(1 40))((1 10)0)(7#90(0 272)#86#59)(7#90(0 272)#88(1 40))(7#3(0 16)#86#59)(7#3(0 16)#88(1 40))((1 11)0)(7#95(0 48)#86#59)(7#95(0 48)#88(1 40))(7#86#59#88(1 40))((0 0)65536)(0 942080)(7#86#59#99#100)(7#88(1 40)#99#100)(6#90(0 272))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(6#3(0 16))(5(1 12)1099511627776 140737488355328)(0 770344)(0#95 8#108)(5(1 11)1099511627776 140737488355328)(9#85(0 480))((1 2)-48)(9#112(0 8))(6#85(0 576))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 793640)(7#85(0 576)#90(0 272))(7#85(0 576)#3(0 16))(7#85(0 576)#95(0 48))(7#90(0 272)#3(0 16))(7#90(0 272)#95(0 48))(7#3(0 16)#95(0 48))(#4#5#6#8#10#12#13#15#17#20#21#22#25#28#29#32#33#34#36#39#41#43#45#47#49#52#53#54#57#58#63#64#68#69#70#71#72#73#74#77#78#79#80#81#82#83#84#87#89#91#92#93#94#96#97#98#101#102#103#104#105#106#107#109#110#111#113#114#115#116#117#118#119#120#121#122#123)((1 2)-576(0 576))(#125)(4 0(0 2)(1 89))((1 88)#127)((1 90)(1 91))(249024 255904 256300 256968 256820 264872 264908 265532 249048 256384 744000 745408)(0#130)(0#131(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 93))(6(1 94))(7(1 95))(8(1 8))(9(1 9))(10(1 96))(11(1 97))(12(1 98))(13(1 99))(14(1 100))(15(1 101))(16(1 102))(17(1 103))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 104))(29(1 105))(30(1 106))(31(1 107))(#133#134#135#136#137#138#139#140#141#142#143#144#145#146#147#148#149#150#151#152#153#154#155#156#157#158#159#160#161#162#163)(1 255904)(2 0(1 10)(0 225))((1 0)(1 92)#1(1 3)(1 4)(1 93)(1 94)(1 95)(1 10)(1 12)(1 96)(1 97)(1 98)(1 99)(1 100)(1 101)(1 102)(1 103)(1 11)#166(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 104)(1 105)(1 106)(1 107))(0#7 8(0 16))(4 0(0 -1)(1 54))(0#9 8#169)(0#112 8#169)(2 0#169#18)(5#172 0 9223372036854775808)(5(1 54)0 9223372036854775808)(5#24 0 0)(9#16(0 16))(#4#5#6#168#170#13#171#173#174#175#28#29#32#33#34#36#39#41#43#45#47#49#52#53#54#57#58#63#64#68#69#70#71#72#73#74#77#78#79#80#81#82#83#84#87#89#91#92#93#94#96#97#98#101#102#103#104#105#106#107#109#110#111#176#114#115#116#117#118#119#120#121#122#123)(2 0(1 60)(0 -1))(5#178 0 33)(5#31 0 0)(#4#5#6#8#10#12#13#15#17#179#180#33#34#36#39#41#43#45#47#49#52#53#54#57#58#63#64#68#69#70#71#72#73#74#77#78#79#80#81#82#83#84#87#89#91#92#93#94#96#97#98#101#102#103#104#105#106#107#109#110#111#113#114#115#116#117#118#119#120#121#122#123)(0#7 8(0 32))(0#9 8(1 54))(0#112 8(1 54))(5#56 0 0)(9#85(0 536))(#4#5#6#182#183#13#28#29#32#184#33#34#41#43#45#47#49#185#58#63#64#68#69#70#71#72#73#74#77#78#79#80#81#82#83#84#87#89#91#92#93#94#96#97#98#101#102#103#104#105#106#107#109#110#186#114#115#116#117#118#119#120#121#122#123)(1 256300)(9#85(0 512))(#4#5#6#8#10#12#13#15#17#179#180#184#33#34#41#43#45#47#49#185#58#63#64#68#69#70#71#72#73#74#77#78#79#80#81#82#83#84#87#89#91#92#93#94#96#97#98#101#102#103#104#105#106#107#109#110#189#113#114#115#116#117#118#119#120#121#122#123))"%pstring.

Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_end_integer_value_csrc_R3 31%positive "(255880#2#124 108#126()(0 97))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_end_integer_value_csrc_R3 11%positive "(#128#129)"%pstring.
Definition hints10 : list (nat * CC.subst) := hints5.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_end_integer_value_csrc_R3 37%positive "(#132(((255904#164()#124)#165))()())"%pstring.

Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_end_integer_value_csrc_R3 33%positive "(255880#167#177 108#126()(0 97))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_end_integer_value_csrc_R3 11%positive "(#128#129)"%pstring.
Definition hints11 : list (nat * CC.subst) := hints6.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_end_integer_value_csrc_R3 37%positive "(#132(((255904#164()#177)#165))()())"%pstring.

Definition t12 : CC.cutpoint := CCD.dec_cp_t dict_Cut_end_integer_value_csrc_R3 31%positive "(255880#2#181 108#126()(0 97))"%pstring.
Definition BL12 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_end_integer_value_csrc_R3 11%positive "(#128#129)"%pstring.
Definition hints12 : list (nat * CC.subst) := hints7.
Definition o12 : CA.pout := CCD.dec_pout_t dict_Cut_end_integer_value_csrc_R3 37%positive "(#132(((255904#164()#181)#165))()())"%pstring.

Definition t13 : CC.cutpoint := CCD.dec_cp_t dict_Cut_end_integer_value_csrc_R3 33%positive "(256276#167#187 108#126()(0 97))"%pstring.
Definition BL13 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_end_integer_value_csrc_R3 11%positive "(#128#129)"%pstring.
Definition hints13 : list (nat * CC.subst) := hints8.
Definition o13 : CA.pout := CCD.dec_pout_t dict_Cut_end_integer_value_csrc_R3 37%positive "(#132(((256300#164()#187)#188))()())"%pstring.

Definition t14 : CC.cutpoint := CCD.dec_cp_t dict_Cut_end_integer_value_csrc_R3 31%positive "(256276#2#190 108#126()(0 97))"%pstring.
Definition BL14 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_end_integer_value_csrc_R3 11%positive "(#128#129)"%pstring.
Definition hints14 : list (nat * CC.subst) := hints9.
Definition o14 : CA.pout := CCD.dec_pout_t dict_Cut_end_integer_value_csrc_R3 37%positive "(#132(((256300#164()#190)#188))()())"%pstring.
