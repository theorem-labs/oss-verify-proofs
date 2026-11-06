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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_dtor_xasan_T Cut_vec_dtor_xasan_R0.
Definition dict_Cut_vec_dtor_xasan_R1 : CCD.pt := CCD.mk_table 1064%positive "((2 0(1 2)(0 -32))(0 2147450880)(2 6(1 10)(0 3))(2 0#3#2)(3 1444792 1448528)((0 0)1482488)(0#6 8#2)(5(0 8)1 4611686018427387904)((1 32)8)(0#9 8(1 33))((1 2)-32)(0#11 8(1 18))((1 2)-24)(0#13 8(1 9))((1 2)-16)(0#15 8(1 8))((1 2)-8)(0#17 8(1 1))((1 10)0)(0#19 8(1 32))(5(1 10)1048576 140737488355320)(4(1 10)8)(#3 2147450880)(1#23(0 1))((0 0)2147446784)(0 17592186048512)(7#25#26#19(0 8))((1 32)0)(0#28 8(1 33))((1 32)16)(2 0(1 33)(1 35))(0#30 8#31)(6#28(0 24))(5(1 32)1048576 140737488354816)(4(1 32)8)(2 6(1 32)(0 3))(#36 2147450880)(1#37(0 3))(7#25#26#28(0 24))(5(1 33)17594333495296 140737479966720)(4(1 33)16)(5(1 35)1 4096)(4 0(0 -1)(1 34))(2 0#43(1 35))(5#44 0 4096)(5(1 34)0 4096)((1 2)-4192)(0 4160)(9#47#48)(0 4192)(6#47#50)(5(1 2)140735332487264 140737488355328)(4(1 2)16)(7#47#50#28(0 24))(7#47#50#19(0 8))(7#19(0 8)#28(0 24))((1 33)0)(7#47#50#57(1 35))(7#28(0 24)#57(1 35))(7#19(0 8)#57(1 35))(2 6(1 33)(0 3))(#61 2147450880)(2 0(1 35)(0 7))(2 6#63(0 3))(7#37(0 3)#62#64)(7#23(0 1)#62#64)(7#28(0 24)#62#64)(7#19(0 8)#62#64)(5(0 7)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xasan_R1 345%positive "(730352((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)#2(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#4(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#5#7#8#10#12#14#16#18#20#21#22#24#27#29#32#33#34#35#38#39#40#41#42#45#46#49#51#52#53#54#55#56#58#59#60#65#66#67#68)56(((1 2)-4192#50)((1 32)0(0 24)))()(0 7))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xasan_R1 17%positive "(((1 33)(1 35)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xasan_R1 513%positive "((0(0(730236 730472 1031544 730684 730524 1387168 1388196))(4#69(1 0)))(((730524((1(0 730368))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9#2)(10(1 32))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18#4)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#69#5#7#8#10#12#14#16#18#20#21#22#24#27#29#32#33#34#35#38#39#40#41#42#45#46#49#51#52#53#54#55#56#58#59#60#65#66#67#68))(1 730524)))()())"%pstring.
