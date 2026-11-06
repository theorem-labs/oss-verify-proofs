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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cstr_casan_T Cut_cstr_casan_R0 Cut_cstr_casan_R1.
Definition dict_Cut_cstr_casan_R2 : CCD.pt := CCD.mk_table 1499%positive "((2 0(1 2)(0 -64))(2 0(1 10)(0 1))(0 2147450880)(3 1359872 1392640)((0 0)1427896)(0#5 8#3)(2 0(1 10)(0 5))(2 6#7(0 3))(#8 2147450880)(1#9(0 1))(5(0 23)1 4611686018427387904)((1 10)0)(0#12 1(0 8))(5(0 24)1 4611686018427387904)((1 2)-56)(0#15 8(1 21))((1 2)-48)(0#17 8(1 20))((1 2)-40)(0#19 8(1 19))((1 2)-32)(0#21 8(1 18))((1 2)-24)(0#23 8(1 9))((1 2)-16)(0#25 8(1 8))((1 2)-8)(0#27 8(1 1))((1 10)1)(9#29(0 23))(6#12(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#34 2147450880)(1#35(0 3))((0 0)2147446784)(0 17592186048512)(7#37#38#12(0 24))((1 2)-4176)(0 4120)(9#40#41)(0 4176)(6#40#43)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#40#43#12(0 24))(#4#6#10#11#13#4#6#14#16#18#20#22#24#26#28#4#6#30#31#32#33#36#39#42#44#45#46#47)((1 2)-4176#43)(#7 0(0 1))(#49#50)(857780 857780 857780 858072 435532 521552 1330948 1331976)(0#52)(0#53(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10#7)(11(0 0))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71))(#55#56#57#58#59#60#61#62#63#64#65#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85)((1 10)5)(0#87 1(0 0))(9#29(0 4))((1 10)6)(9#90(0 18))(#88#4#6#10#11#13#4#6#14#16#18#20#22#24#26#28#4#6#89#91#31#32#33#36#39#42#44#45#46#47)(858072#86()#92)(1 858072)(#93#94)(#95)(2 0(1 10)(0 6))(2 6#97(0 3))(#98 2147450880)(1#99(0 1))(0#12 1(0 10)))"%pstring.

Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R2 204%positive "(858016((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(0 155456)(0 4)#2(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 10)#2(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))#48 72#51()(0 22))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R2 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints3.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R2 13%positive "(#54#96()())"%pstring.

Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R2 204%positive "(858016((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(0 155392)(0 4)#2(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 10)#2(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))#48 72#51()(0 22))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R2 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints4.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R2 13%positive "(#54#96()())"%pstring.

Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R2 296%positive "(858016((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(0 155424)(0 5)#2(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 10)#2(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#4#6#100#11#101#4#6#14#16#18#20#22#24#26#28#4#6#30#31#32#33#36#39#42#44#45#46#47)72(#49(#97 0(0 1)))()(0 22))"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R2 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints5.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R2 247%positive "(#54(((858072(#55#56#57#58#59#60#61#62#63(10#97)#65#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85)()((0#90 1(0 0))#4#6#100#11#101#4#6#14#16#18#20#22#24#26#28#4#6(9#29(0 5))(9((1 10)7)(0 17))#31#32#33#36#39#42#44#45#46#47))#94))()())"%pstring.
