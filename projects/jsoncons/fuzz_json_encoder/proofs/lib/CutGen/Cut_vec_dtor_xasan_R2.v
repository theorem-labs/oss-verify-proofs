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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_dtor_xasan_T Cut_vec_dtor_xasan_R0 Cut_vec_dtor_xasan_R1.
Definition dict_Cut_vec_dtor_xasan_R2 : CCD.pt := CCD.mk_table 1159%positive "((0 2147450880)(2 6(1 10)(0 3))(3 1444792 1448528)((0 0)1482488)(0#4 8#1)(5(0 7)1 4611686018427387904)(5(0 8)1 4611686018427387904)((1 32)8)(0#8 8(1 33))((1 2)-32)(0#10 8(1 18))((1 2)-24)(0#12 8(1 9))((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))((1 10)0)(0#18 8(1 32))(5(1 10)1048576 140737488355320)(4(1 10)8)(#2 2147450880)(1#22(0 1))((0 0)2147446784)(0 17592186048512)(7#24#25#18(0 8))((1 32)0)(0#27 8(1 33))((1 32)16)(2 0(1 33)(1 35))(0#29 8#30)(6#27(0 24))(5(1 32)1048576 140737488354816)(4(1 32)8)(2 6(1 32)(0 3))(#35 2147450880)(1#36(0 3))(7#24#25#27(0 24))(5(1 33)17594333495296 140737479966720)(4(1 33)16)(5(1 35)1 4096)(4 0(0 -1)(1 34))(2 0#42(1 35))(5#43 0 4096)(5(1 34)0 4096)((1 2)-4192)(0 4160)(9#46#47)(0 4192)(6#46#49)(5(1 2)140735332487264 140737488355328)(4(1 2)16)(7#46#49#27(0 24))(7#46#49#18(0 8))(7#18(0 8)#27(0 24))((1 33)0)(7#46#49#56(1 35))(7#27(0 24)#56(1 35))(7#18(0 8)#56(1 35))(2 6(1 33)(0 3))(#60 2147450880)(2 0(1 35)(0 7))(2 6#62(0 3))(7#36(0 3)#61#63)(7#22(0 1)#61#63)(7#27(0 24)#61#63)(7#18(0 8)#61#63)(#3#5#6#3#5#7#9#11#13#15#17#19#20#21#23#26#28#31#32#33#34#37#38#39#40#41#44#45#48#50#51#52#53#54#55#57#58#59#64#65#66#67))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xasan_R2 255%positive "(730368((1 0)(1 56)(2 0(1 2)(0 -32))(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)#1(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(2 0#2#1)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))#68 72(((1 2)-4192#49)((1 32)0(0 24)))()(0 6))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xasan_R2 17%positive "(((1 33)(1 35)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xasan_R2 396%positive "((0(0(730236 730472 1031544 730684 730524 1387168 1388196))(1 0))(((1031544((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(1 33))(11(1 35))(12(0 0))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()#68)(1 1031544)))()())"%pstring.
