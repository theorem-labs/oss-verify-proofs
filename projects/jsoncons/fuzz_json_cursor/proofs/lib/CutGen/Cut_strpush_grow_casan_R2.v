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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strpush_grow_casan_T Cut_strpush_grow_casan_R0 Cut_strpush_grow_casan_R1.
Definition dict_Cut_strpush_grow_casan_R2 : CCD.pt := CCD.mk_table 1101%positive "((2 0(1 2)(0 -64))(4 0(0 4)(1 32))(2 0#2(0 -2))(2 6#3(0 3))(4 0(0 8)#4)(2 0#5(0 8))(4 0(0 2)(1 32))(2 0#7(0 -1))(3 1359872 1392640)((0 0)1427896)(0 2147450880)(0#10 8#11)((1 44)0)(2#13#8 0)(5(0 99)1 4611686018427387904)(5(1 44)4096 140737479966719)(4(1 44)16)(9#13#6)(6#13#6)((0 0)2147446784)(0 17592186048512)(7#20#21#13#6)((0 0)1359872)(0 32768)(7#23#24#13#6)(7#10(0 8)#13#6)((1 10)0)(7#13#6#27(0 24))((1 2)-4368)(0 4368)(7#13#6#29#30)((1 34)0)(7#13#6#32#7)(5(0 100)1 4611686018427387904)(2 0#7(0 1))(6 0 0 1#35)(2 9#36(0 1))(5#37 1 1)((1 2)-64)(0#39 8(1 22))((1 2)-56)(0#41 8(1 21))((1 2)-48)(0#43 8(1 20))((1 2)-40)(0#45 8(1 19))((1 2)-32)(0#47 8(1 18))((1 2)-24)(0#49 8(1 9))((1 2)-16)(0#51 8(1 8))((1 2)-8)(0#53 8(1 1))(0#27 8#35)((1 10)8)(0#56 8#8)((1 10)16)(0#58 8(1 34))(5(1 32)12 33554432)(5(1 11)0 255)(2#32#8 0)(9#32#7)(6#32#7)(5(1 34)4096 140737488355328)(4(1 34)16)(9#27(0 24))(6#27(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(0 4304)(9#29#71)(6#29#30)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#29#30#27(0 24))(7#29#30#32#7)(7#27(0 24)#32#7)(5(0 98)1 4611686018427387904))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strpush_grow_casan_R2 383%positive "(985232((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 11)(1 10)(1 44)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 34)#6#8#7(1 44)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#9#12#14#15#9#12#16#17#18#19#22#25#26#28#31#33#34#38#40#42#44#46#48#50#52#54#9#12#55#57#59#60#61#62#63#64#65#66#67#68#69#70#72#73#74#75#76#77#78)72(((1 2)-4368#30)((1 10)0(0 24))((1 44)0#6))()(0 98))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strpush_grow_casan_R2 23%positive "(((1 44)#6)((1 34)#7))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_strpush_grow_casan_R2 535%positive "((0(0(985020 985324 1358140 519788 975272 1330948 1331976))(4#79(1 0)))(((975272((1(0 985252))(2#1)(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 11))(9(1 10))(10(1 34))(11#7)(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 34))(19#6)(20#8)(21#7)(22(1 44))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()(#79#9#12#14#15#9#12#16#17#18#19#22#25#26#28#31#33#34#38#40#42#44#46#48#50#52#54#9#12#55#57#59#60#61#62#63#64#65#66#67#68#69#70#72#73#74#75#76#77#78))(1 975272)))()())"%pstring.
