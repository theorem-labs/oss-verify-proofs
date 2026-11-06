(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_after_value_xasan_T Cut_after_value_xasan_R0.
Definition dict_Cut_after_value_xasan_R1 : CCD.pt := CCD.mk_table 1093%positive "((2 0(1 2)(0 -96))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#4 8#2)((0 0)1482496)(0#6 4(0 1))(5(1 37)7077888 140737479966656)(4(1 37)64)((1 37)0)(6#10(0 64))(2 6(1 37)(0 3))(#12 2147450880)(6#13(0 8))((0 0)2147446784)(0 17592186048512)(7#15#16#10(0 64))((1 2)-1152)(0 1152)(7#18#19#10(0 64))((1 37)56)(0#21 8(1 32))((1 32)0)(6#23(0 1))(5(1 32)7077888 140737479966719)(7#15#16#23(0 1))(7#10(0 64)#23(0 1))(7#18#19#23(0 1))((1 10)208)(7#10(0 64)#29(0 1))(7#23(0 1)#29(0 1))(2 0(1 10)(0 208))(2 6#32(0 3))(#33 2147450880)(7#13(0 8)#34(0 1))(5(0 100)1 4611686018427387904)((1 2)-72)(0#37 8(1 23))((1 2)-64)(0#39 8(1 22))((1 2)-56)(0#41 8(1 21))((1 2)-48)(0#43 8(1 20))((1 2)-40)(0#45 8(1 19))((1 2)-32)(0#47 8(1 18))((1 2)-24)(0#49 8(1 9))((1 2)-16)(0#51 8(1 8))((1 2)-8)(0#53 8(1 1))((1 2)-96)(0#55 8(0 0))(6#29(0 1))(5(1 10)7077888 140737479966448)(4(1 10)8)(1#34(0 1))(7#15#16#29(0 1))(0 1056)(9#18#62)((1 2)-88)(6#18#19)(5(1 2)140735332484224 140737488355328)(4(1 2)32)(7#18#19#29(0 1))(5(0 99)1 4611686018427387904)(0 110998)(0 903708)(0 18446744073709551603)(0 18446744073709551601))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_after_value_xasan_R1 437%positive "(903808((1 0)(1 33)#1(1 3)(1 4)(1 34)(1 35)(1 36)(1 2)#1(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 44)(1 18)(1 11)(1 10)(1 21)(1 22)#2(1 24)(1 25)(1 26)(1 27)(1 45)(1 46)(1 47)(1 48))(#3#5#7#8#9(9#10(0 64))#11(1#13(0 8))#14#17#20#22#24#25#26#27#28#30#31#35#36#38#40#42#44#46#48#50#52#54#56#3#5#7#57#58#59#60#61#63(9#64(0 16))#65#66#67#68)49(((1 2)-1152#19)((1 10)208(0 1))((1 37)0(0 24))((1 37)32(0 24))(#12 2147450880(0 8)))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_after_value_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_after_value_xasan_R1 808%positive "((0(0(903708 904172 904176 417392 899700 1387168 1388196))(4#69(1 0)))(((899700((1(0 903956))(2#1)(3(1 3))(4(1 4))(5(1 34))(6(1 35))(7(1 36))(8(1 2))(9#1)(10(1 10))(11#70)(12#71)(13#72)(14(1 41))(15(1 42))(16(1 43))(17(1 44))(18(1 37))(19(1 11))(20(1 10))(21(1 37))(22(2 0#12#2))(23#2)(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 45))(29(1 46))(30(1 47))(31(1 48)))()(#69(0(#12 2147450883)1#73)(0(#12 2147450882)1#73)(0(#12 2147450881)1#73)(0#13 1#73)(0(#12 2147450887)1#72)(0(#12 2147450886)1#72)(0(#12 2147450885)1#72)(0(#12 2147450884)1(0 18446744073709551608))(0((1 37)16)8#71)(0((1 37)8)8#70)(0#10 8(0 1102416563))(0((1 2)-80)8(1 37))#3#5#7#8#9(9((1 37)24)(0 40))#11#14#17#20#22#24#25#26#27#28#30#31#35#36#38#40#42#44#46#48#50#52#54#56#3#5#7#57#58#59#60#61#63(9#64(0 8))#65#66#67#68))(1 899700)))()())"%pstring.
