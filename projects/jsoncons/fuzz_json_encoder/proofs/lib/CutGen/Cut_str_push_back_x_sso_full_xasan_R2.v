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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_push_back_x_sso_full_xasan_T Cut_str_push_back_x_sso_full_xasan_R0 Cut_str_push_back_x_sso_full_xasan_R1.
Definition dict_Cut_str_push_back_x_sso_full_xasan_R2 : CCD.pt := CCD.mk_table 717%positive "((3 1417216 1449984)((0 0)1482488)(0 2147450880)(0#2 8#3)((1 44)0)(2#5(0 22)0)(5(0 99)1 4611686018427387904)(5(1 44)4096 140737479966719)(4(1 44)16)(6#5(0 48))((0 0)2147446784)(0 17592186048512)(7#11#12#5(0 48))((0 0)1417216)(0 32768)(7#14#15#5(0 48))(7#2(0 8)#5(0 48))((1 10)0)(7#5(0 48)#18(0 24))((1 2)-4368)(0 4368)(7#5(0 48)#20#21)(5(0 100)1 4611686018427387904)((1 2)-64)(0#24 8(1 22))((1 2)-56)(0#26 8(1 21))((1 2)-48)(0#28 8(1 20))((1 2)-40)(0#30 8(1 19))((1 2)-32)(0#32 8(1 18))((1 2)-24)(0#34 8(1 9))((1 2)-16)(0#36 8(1 8))((1 2)-8)(0#38 8(1 1))(5(1 11)0 255)(6#18(0 24))(5(1 10)7077888 140737488351232)(4(1 10)8)(0 4304)(9#20#44)(6#20#21)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#20#21#18(0 24)))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_sso_full_xasan_R2 429%positive "(1041504((1 0)(1 56)(2 0(1 2)(0 -64))(1 3)(1 4)(1 57)(1 58)(1 59)(1 11)(1 10)(1 44)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(2 0(1 10)(0 1))(0 48)(0 22)(0 23)(1 44)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#1#4#6#7#1#4#8#9(9#5(0 48))#10#13#16#17#19#22#23#25#27#29#31#33#35#37#39#1#4(0#18 1(0 44))#40(2((1 10)1)(0 22)0)(9#18(0 24))#41#42#43#45#46#47#48#49)72(((1 2)-4368#21)((1 10)0(0 24))((1 44)0(0 48)))()(0 98))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_sso_full_xasan_R2 17%positive "(((1 44)(0 48)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_sso_full_xasan_R2 624%positive "((0(0(1041292 1041596 1414360 524856 1031544 1387168 1388196))(1 0))(((1041596((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(2 0(1 44)(0 22)))(11(0 23))(12(1 62))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()((0((1 44)23)1(0 0))(0((1 44)22)1(1 11))(0((1 10)8)8(0 23))(0((1 10)16)8(1 44))(0#18 8(0 49))#1#4#6#7#1#4#8#9(9#5(0 22))(9((1 44)24)(0 24))#10#13#16#17#19#22#23#25#27#29#31#33#35#37#39#1#4#40#41#42#43#45#46#47#48#49))(1 1041596)))()())"%pstring.
