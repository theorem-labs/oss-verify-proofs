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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_push_back_x_grow_xasan_T Cut_str_push_back_x_grow_xasan_R0.
Definition dict_Cut_str_push_back_x_grow_xasan_R1 : CCD.pt := CCD.mk_table 1067%positive "((2 0(1 2)(0 -64))(4 0(0 4)(1 32))(2 0#2(0 -2))(2 6#3(0 3))(4 0(0 8)#4)(2 0#5(0 8))(4 0(0 2)(1 32))(2 0#7(0 -1))(3 1417216 1449984)((0 0)1482488)(0 2147450880)(0#10 8#11)(5(1 44)4096 140737479966719)(4(1 44)16)((1 44)0)(9#15#6)(6#15#6)((0 0)2147446784)(0 17592186048512)(7#18#19#15#6)((0 0)1417216)(0 32768)(7#21#22#15#6)(7#10(0 8)#15#6)((1 10)0)(7#15#6#25(0 24))((1 2)-4368)(0 4368)(7#15#6#27#28)((1 34)0)(7#15#6#30#7)(5(0 100)1 4611686018427387904)(2 0#7(0 1))(6 0 0 1#33)(2 9#34(0 1))(5#35 1 1)((1 2)-64)(0#37 8(1 22))((1 2)-56)(0#39 8(1 21))((1 2)-48)(0#41 8(1 20))((1 2)-40)(0#43 8(1 19))((1 2)-32)(0#45 8(1 18))((1 2)-24)(0#47 8(1 9))((1 2)-16)(0#49 8(1 8))((1 2)-8)(0#51 8(1 1))(0#25 8#33)((1 10)8)(0#54 8#8)((1 10)16)(0#56 8(1 34))(5(1 32)12 70368744177664)(5(1 11)0 255)(2#30#8 0)(9#30#7)(6#30#7)(5(1 34)4096 140737488355328)(4(1 34)16)(9#25(0 24))(6#25(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(0 4304)(9#27#69)(6#27#28)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#27#28#25(0 24))(7#27#28#30#7)(7#25(0 24)#30#7)(5(0 99)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_grow_xasan_R1 373%positive "(1041488((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 11)(1 10)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 34)#6#8#7(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#9#12#13#14#16#17#20#23#24#26#29#31#32#36#38#40#42#44#46#48#50#52#9#12#53#55#57#58#59#60#61#62#63#64#65#66#67#68#70#71#72#73#74#75#76)56(((1 2)-4368#28)((1 10)0(0 24))((1 44)0#6))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_grow_xasan_R1 23%positive "(((1 44)#6)((1 34)#7))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_grow_xasan_R1 528%positive "((0(0(1041292 1041596 1414360 524856 1031544 1387168 1388196))(4#77(1 0)))(((524856((1(0 1041504))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 11))(9(1 10))(10(1 44))(11(1 34))(12#8)(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 34))(19#6)(20#8)(21#7)(22(1 44))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#77#9#12#13#14#16#17#20#23#24#26#29#31#32#36#38#40#42#44#46#48#50#52#9#12#53#55#57#58#59#60#61#62#63#64#65#66#67#68#70#71#72#73#74#75#76))(1 524856)))()())"%pstring.
