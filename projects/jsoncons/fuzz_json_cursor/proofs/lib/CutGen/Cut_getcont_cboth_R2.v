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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getcont_cboth_T Cut_getcont_cboth_R0 Cut_getcont_cboth_R1.
Definition dict_Cut_getcont_cboth_R2 : CCD.pt := CCD.mk_table 2185%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)(1 11)(1 10)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(3 1368064 1400832)((0 0)1432824)(0#5 8#2)((1 10)0)(1#7(0 24))(5(0 23)1 4611686018427387904)(5(0 24)1 4611686018427387904)((1 2)-33)(0#11 1(1 12))((1 2)-32)(0#13 8(1 18))((1 2)-24)(0#15 8(1 9))((1 2)-16)(0#17 8(1 8))((1 2)-8)(0#19 8(1 1))(9#7(0 24))(6#7(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#25 2147450880)(1#26(0 3))((0 0)2147446784)(0 17592186048512)(7#28#29#7(0 24))((1 11)0)(9#31(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#35 2147450880)(1#36(0 5))(7#28#29#31(0 40))((1 13)0)(9#39(0 16))(6#39(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#44 2147450880)(1#45(0 2))(7#28#29#39(0 16))((1 2)-14384)(0 14351)(9#48#49)(0 14384)(6#48#51)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#48#51#7(0 24))(7#48#51#31(0 40))(7#48#51#39(0 16))(7#7(0 24)#31(0 40))(7#7(0 24)#39(0 16))(7#31(0 40)#39(0 16))(0#31 8(0 256))(#4#6#8#9#4#6#10#12#14#16#18#20#4#6#21#22#23#24#27#30#32#33#34#37#38#40#41#42#43#46#47#50#52#53#54#55#56#57#58#59#60#61)((1 2)-14384#51)(#63)(841728 841728 841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#65)(0#66(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(1 10))(11(1 61))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71))(#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98)(1 842596)(0#31 8(0 512))(#4#6#8#9#4#6#10#12#14#16#18#20#4#6#21#22#23#24#27#30#32#33#34#37#38#40#41#42#43#46#47#50#52#53#54#55#56#57#58#59#60#101)(0 1024)(0#31 8#103)(#4#6#8#9#4#6#10#12#14#16#18#20#4#6#21#22#23#24#27#30#32#33#34#37#38#40#41#42#43#46#47#50#52#53#54#55#56#57#58#59#60#104)(0 2048)(0#31 8#106)(#4#6#8#9#4#6#10#12#14#16#18#20#4#6#21#22#23#24#27#30#32#33#34#37#38#40#41#42#43#46#47#50#52#53#54#55#56#57#58#59#60#107))"%pstring.

Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getcont_cboth_R2 28%positive "(842484#3#62 72#64()(0 22))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getcont_cboth_R2 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints4.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R2 34%positive "(#67(((842596#99()#62)#100))()())"%pstring.

Definition t9 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getcont_cboth_R2 29%positive "(842484#3#102 72#64()(0 22))"%pstring.
Definition BL9 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getcont_cboth_R2 3%positive "()"%pstring.
Definition hints9 : list (nat * CC.subst) := hints5.
Definition o9 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R2 35%positive "(#67(((842596#99()#102)#100))()())"%pstring.

Definition t10 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getcont_cboth_R2 29%positive "(842484#3#105 72#64()(0 22))"%pstring.
Definition BL10 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getcont_cboth_R2 3%positive "()"%pstring.
Definition hints10 : list (nat * CC.subst) := hints6.
Definition o10 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R2 35%positive "(#67(((842596#99()#105)#100))()())"%pstring.

Definition t11 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getcont_cboth_R2 29%positive "(842484#3#108 72#64()(0 22))"%pstring.
Definition BL11 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getcont_cboth_R2 3%positive "()"%pstring.
Definition hints11 : list (nat * CC.subst) := hints7.
Definition o11 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R2 35%positive "(#67(((842596#99()#108)#100))()())"%pstring.
