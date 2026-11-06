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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_sdtor_xasan_T Cut_sdtor_xasan_R0 Cut_sdtor_xasan_R1.
Definition dict_Cut_sdtor_xasan_R2 : CCD.pt := CCD.mk_table 1028%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 88))(3 1417216 1449984)((0 0)1482488)(0 2147450880)(0#4 8#5)(5(0 11)1 4611686018427387904)((1 10)88)(0 1435320)(0#8 8#9)((1 2)-40)(0#11 8(1 19))((1 2)-32)(0#13 8(1 18))((1 2)-24)(0#15 8(1 9))((1 2)-16)(0#17 8(1 8))((1 2)-8)(0#19 8(1 1))((1 10)24)(0 1435416)(0#21 8#22)((1 10)8)(0 1419928)(0#24 8#25)(5(0 12)1 4611686018427387904)((1 10)32)(0 6934032)(0#28 8#29)((1 10)264)(0#31 8(1 32))((1 10)272)(0 16384)(0#33 8#34)((1 10)136)(0#36 8#29)((1 10)144)(0#38 8(0 0))((1 10)152)(0#40 8(0 0))((1 10)160)(0#42 8(0 0))((1 10)176)(0#44 8(0 0))((1 10)200)(0#46 8(0 0))((1 10)0)(9#48(0 8))((1 10)16)(9#50(0 8))(6#48(0 592))(5(1 10)7077888 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#55 2147450880)(1#56(0 74))((0 0)2147446784)(0 17592186048512)(7#58#59#48(0 592))(5(1 32)4096 140737479966720)(4(1 32)16)((1 2)-4224)(0 4184)(9#63#64)(0 4224)(6#63#66)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(7#63#66#48(0 592))((1 32)0)(7#63#66#71#34)(7#48(0 592)#71#34)(7#58#59#71#34)(5(0 10)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_sdtor_xasan_R2 356%positive "(1061848((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)#2(0 0)(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#3#6#7#10#12#14#16#18#20#23#26#3#6#27#3#6#30#32#35#37#39#41#43#45#47#49#51#52#53#54#57#60#61#62#65#67#68#69#70#72#73#74)72(((1 2)-4224#66)((1 10)0(0 592)))()(0 10))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_sdtor_xasan_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xasan_R2 507%positive "((0(0(730848 1031544 531904 1387168 1388196))(4#75(1 0)))(((531904((1(0 1061856))(2#1)(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8#2)(9(0 0))(10(0 0))(11(1 61))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()(#75#3#6#7#10#12#14#16#18#20#23#26#3#6#27#3#6#30#32#35#37#39#41#43#45#47#49#51#52#53#54#57#60#61#62#65#67#68#69#70#72#73#74))(1 531904)))()())"%pstring.
