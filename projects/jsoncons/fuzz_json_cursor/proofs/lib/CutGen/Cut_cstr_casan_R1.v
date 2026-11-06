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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cstr_casan_T Cut_cstr_casan_R0.
Definition dict_Cut_cstr_casan_R1 : CCD.pt := CCD.mk_table 1234%positive "((2 0(1 2)(0 -64))(0 155456)(0 2147450880)(3 1359872 1392640)((0 0)1427896)(0#5 8#3)(5(0 24)1 4611686018427387904)((1 2)-56)(0#8 8(1 21))((1 2)-48)(0#10 8(1 20))((1 2)-40)(0#12 8(1 19))((1 2)-32)(0#14 8(1 18))((1 2)-24)(0#16 8(1 9))((1 2)-16)(0#18 8(1 8))((1 2)-8)(0#20 8(1 1))((1 10)0)(9#22(0 24))(6#22(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#27 2147450880)(1#28(0 3))((0 0)2147446784)(0 17592186048512)(7#30#31#22(0 24))((1 2)-4176)(0 4120)(9#33#34)(0 4176)(6#33#36)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#33#36#22(0 24))(#4#6#7#9#11#13#15#17#19#21#4#6#23#24#25#26#29#32#35#37#38#39#40)((1 2)-4176#36)((1 10)0(0 24))(2 0(1 10)(0 5))(#44 0(0 1))(#42#43#45)(857780 857780 857780 858072 435532 521552 1330948 1331976)(0#47)(5(0 23)1 4611686018427387904)(4#49(1 0))(0#48#50)(0 858016)(1#52)(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(9(0 4))(2 0(1 10)(0 1))(10#61)(12(0 4))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 10))(19#61)(20(1 20))(21#3)(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(0#22 1(0 8))((1 10)1)(9#84(0 23))(#49#83#4#6#7#9#11#13#15#17#19#21#4#6#85#24#25#26#29#32#35#37#38#39#40)(1 521552)(0 155392)(0 155424))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R1 203%positive "(857840((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)#2(1 9)(0 4)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)(1 19)(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))#41 56#46()(0 23))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints0.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R1 130%positive "(#51(((521552(#53#54#55#56#57#58#59(8#2)#60#62(11#2)#63#64#65#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82)()#86)#87))()())"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R1 204%positive "(857840((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)#88(1 9)(0 4)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)(1 19)(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))#41 56#46()(0 23))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints1.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R1 132%positive "(#51(((521552(#53#54#55#56#57#58#59(8#88)#60#62(11#88)#63#64#65#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82)()#86)#87))()())"%pstring.

Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_cstr_casan_R1 233%positive "(857840((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)#89(1 9)(0 5)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 10)(1 19)(1 20)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))#41 56(#42#43((2 0(1 10)(0 6))0(0 1)))()(0 23))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_cstr_casan_R1 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints2.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R1 222%positive "(#51(((521552(#53#54#55#56#57#58#59(8#89)(9(0 5))#62(11#89)(12(0 5))#64#65#66#67#68#69#70#71#72#73#74#75#76#77#78#79#80#81#82)()(#49(0#22 1(0 10))#4#6#7#9#11#13#15#17#19#21#4#6#85#24#25#26#29#32#35#37#38#39#40))#87))()())"%pstring.
