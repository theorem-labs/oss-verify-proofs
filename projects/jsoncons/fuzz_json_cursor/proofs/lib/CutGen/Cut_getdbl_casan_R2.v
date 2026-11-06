(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getdbl_casan_T Cut_getdbl_casan_R0 Cut_getdbl_casan_R1.
Definition dict_Cut_getdbl_casan_R2 : CCD.pt := CCD.mk_table 1910%positive "((0 838340)(2 0(1 2)(0 -48))(0 2147450880)((1 0)#1#2(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 11)(1 56)(0 0)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#3(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(5(0 23)1 4611686018427387904)((1 2)-40)(0#6 1(0 46))((1 2)-44)(0#8 4(0 0))((1 2)-48)(0#10 1(0 0))(3 1359872 1392640)((0 0)1427896)(0#13 8#3)(3 84976 84984)((0 0)2147624442)(1#16(0 1))((0 0)2147461502)(1#18(0 1))((1 10)0)(1#20(0 24))(5(0 24)1 4611686018427387904)((1 2)-33)(0#23 1(1 12))((1 2)-32)(0#25 8(1 18))((1 2)-24)(0#27 8(1 9))((1 2)-16)(0#29 8(1 8))((1 2)-8)(0#31 8(1 1))(9#20(0 24))(6#20(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#37 2147450880)(1#38(0 3))((0 0)2147446784)(0 17592186048512)(7#40#41#20(0 24))((1 11)0)(9#43(0 40))(5(1 11)7024640 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#47 2147450880)(1#48(0 5))(7#40#41#43(0 40))((1 13)0)(9#51(0 16))(6#51(0 16))(5(1 13)7024640 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#56 2147450880)(1#57(0 2))(7#40#41#51(0 16))((1 2)-14384)(0 14336)(9#60#61)((1 2)-47)(9#63(0 3))((1 2)-39)(9#65(0 6))(0 14384)(6#60#67)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#60#67#20(0 24))(7#60#67#43(0 40))(7#60#67#51(0 16))(7#20(0 24)#43(0 40))(7#20(0 24)#51(0 16))(7#43(0 40)#51(0 16))(0#43 8(0 128))((1 2)-14384#67)(#78)(837940 837940 838856 845488 842800 838412 520976 728032 857780 839488 841088 1330948 1331976)(0#80)(5(0 22)1 4611686018427387904)(4#82(1 0))(0#81#83)(0 838428)(1#85)(2#2)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9(1 11))(10#2)(11(1 10))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#3)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)(1 842800)((0 0)6883756)(0#119 4(0 1)))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_casan_R2 167%positive "(838416#4(#5#7#9#11#12#14#15#17#19#21#22#24#26#28#30#32#12#14#33#34#35#36#39#42#44#45#46#49#50#52#53#54#55#58#59#62#64#66#68#69#70#71#72#73#74#75#76#77)57#79()(0 22))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_casan_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_casan_R2 178%positive "(#84(((842800#117()(#82#5#7#9#11#12#14#15#17#19#21#22#24#26#28#30#32#12#14#33#34#35#36#39#42#44#45#46#49#50#52#53#54#55#58#59#62#64#66#68#69#70#71#72#73#74#75#76#77))#118))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_getdbl_casan_R2 171%positive "(838416#4(#5#7#9#11#12#14#15#17#19#21#22#24#26#28#30#32#12#14#33#34#35#36#39#42#44#45#46#49#50#52#53#54#55#58#59#62#64#66#68#69#70#71#72#73#74#75#76#77#120)57#79()(0 22))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_getdbl_casan_R2 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints3.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_getdbl_casan_R2 182%positive "(#84(((842800#117()(#82#5#7#9#11#12#14#15#17#19#21#22#24#26#28#30#32#12#14#33#34#35#36#39#42#44#45#46#49#50#52#53#54#55#58#59#62#64#66#68#69#70#71#72#73#74#75#76#77#120))#118))()())"%pstring.
