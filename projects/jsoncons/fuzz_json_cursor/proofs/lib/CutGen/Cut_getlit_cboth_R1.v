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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getlit_cboth_T Cut_getlit_cboth_R0.
Definition dict_Cut_getlit_cboth_R1 : CCD.pt := CCD.mk_table 1991%positive "((2 0(1 2)(0 -48))(0 2147450880)((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(3 1368064 1400832)((0 0)1432824)(0#5 8#2)(5(0 24)1 4611686018427387904)((1 2)-33)(0#8 1(1 12))((1 2)-32)(0#10 8(1 18))((1 2)-24)(0#12 8(1 9))((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))((1 10)0)(9#18(0 24))(6#18(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#23 2147450880)(1#24(0 3))((0 0)2147446784)(0 17592186048512)(7#26#27#18(0 24))((1 11)0)(9#29(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#33 2147450880)(1#34(0 5))(7#26#27#29(0 40))((1 13)0)(9#37(0 16))(6#37(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#42 2147450880)(1#43(0 2))(7#26#27#37(0 16))((1 2)-14384)(0 14351)(9#46#47)(0 14384)(6#46#49)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#46#49#18(0 24))(7#46#49#29(0 40))(7#46#49#37(0 16))(7#18(0 24)#29(0 40))(7#18(0 24)#37(0 16))(7#29(0 40)#37(0 16))(0#29 8(0 4))(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#59)((1 2)-14384#49)(#61)(841728 841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#63)(0#64(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 8))(9(1 9))(10(1 44))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90#91#92#93#94#95#96)(1 842596)(0#29 8(0 8))((1 11)24)(0#100 1(0 1))(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#99#101)(0#100 1(0 0))(#4#6#7#9#11#13#15#17#4#6#19#20#21#22#25#28#30#31#32#35#36#38#39#40#41#44#45#48#50#51#52#53#54#55#56#57#58#99#103))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getlit_cboth_R1 28%positive "(842508#3#60 56#62()(0 23))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getlit_cboth_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints0.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getlit_cboth_R1 33%positive "(#65(((842596#97()#60)#98))()())"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getlit_cboth_R1 29%positive "(842508#3#102 56#62()(0 23))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getlit_cboth_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints1.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_getlit_cboth_R1 34%positive "(#65(((842596#97()#102)#98))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getlit_cboth_R1 29%positive "(842508#3#104 56#62()(0 23))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getlit_cboth_R1 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints2.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_getlit_cboth_R1 34%positive "(#65(((842596#97()#104)#98))()())"%pstring.
