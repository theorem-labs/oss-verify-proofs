(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xboth_T Cut_vec_reserve_xboth_R0.
Definition dict_Cut_vec_reserve_xboth_R1 : CCD.pt := CCD.mk_table 948%positive "((2 0(1 2)(0 -32))(2 0(1 2)(0 -56))(0 2147450880)(3 1459384 1463120)((0 0)1497016)(0#5 8#3)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#9(0 66))((0 0)2147446784)(0 17592186048512)(7#11#12#9(0 66))(2 6(1 44)(0 3))(#14 2147450880)(2 0(1 11)(0 7))(2 6#16(0 3))(2 6#2(0 3))(#18 2147450880)(7#15#17#19(0 5))(5(0 16)1 4611686018427387904)((1 2)-24)(0#22 8(1 10))((1 2)-32)((1 2)-120)(0#25 8(1 21))((1 2)-112)(0#27 8(1 20))((1 2)-104)(0#29 8(1 19))((1 2)-96)(0#31 8(1 18))((1 2)-88)(0#33 8(1 9))((1 2)-80)(0#35 8(1 10))((1 2)-72)((1 2)-16)(0#38 8(1 8))((1 2)-8)(0#40 8(1 1))((1 10)0)(0#42 8(0 0))((1 10)8)(0#44 8(0 0))((1 10)16)(0#46 8(0 0))(6#42(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#51 2147450880)(1#52(0 3))(7#11#12#42(0 24))(5(1 11)66 66)((1 2)-8192)((1 2)-64)(0 8192)(6#56#58)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#19(0 5))(7#56#58#42(0 24))(7#52(0 3)#19(0 5))(5(0 15)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xboth_R1 420%positive "(856896((1 0)(1 40)(2 0(1 2)(0 -128))(1 3)(1 4)(1 41)(1 42)(1 43)#1(0 66)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#2(0 0)(2 0(2 6#1(0 3))#3)#3(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#4#6#7#8(9#9(0 66))#10#13#20#21#23(0#24 8(0 0))#26#28#30#32#34#36(0#37 8(0 856300))#39#41#4#6#43#45#47#48#49#50#53#54#55(9#56(0 8072))(9#57(0 32))#59#60#61#62#63#64)56(((1 2)-8192#58)((1 10)0(0 24)))()(0 15))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xboth_R1 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xboth_R1 712%positive "((0(0(856176 856332 1429232 732972 527120 857884 1402040 1403068))(4#65(1 0)))(((732972((1(0 857180))(2(2 0(1 2)(0 -144)))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8#2)(9(1 10))(10(1 10))(11(0 1497016))(12(0 1))(13(0 0))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21#3)(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#65(0((1 2)-144)8(1 24))(0((1 2)-136)8(1 23))(0((1 2)-128)8(1 22))#26#28#30#32#34#36(0#37 8(0 856312))(0#24 8(2 0(1 44)(0 66)))(0((1 2)-48)8(1 44))(0((1 2)-40)8(1 44))(0((1 2)-56)8(1 44))#4#6#7#8#10#13#20#21#23#39#41#4#6#43#45#47#48#49#50#53#54#55(9#56(0 8048))(9#57(0 8))#59#60#61#62#63#64))(1 732972)))()())"%pstring.
