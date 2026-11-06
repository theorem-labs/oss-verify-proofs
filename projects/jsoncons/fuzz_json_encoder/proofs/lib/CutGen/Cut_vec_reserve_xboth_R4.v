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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xboth_T Cut_vec_reserve_xboth_R0 Cut_vec_reserve_xboth_R1 Cut_vec_reserve_xboth_R2 Cut_vec_reserve_xboth_R3.
Definition dict_Cut_vec_reserve_xboth_R4 : CCD.pt := CCD.mk_table 969%positive "((3 1459384 1463120)((0 0)1497016)(0 2147450880)(0#2 8#3)(5(0 13)1 4611686018427387904)((1 2)-56)(0#6 8(0 0))((1 2)-32)(0#8 8(0 0))((1 10)16)(2 0(1 44)(0 66))(0#10 8#11)((1 2)-40)(0#13 8(0 0))((1 10)8)(0#15 8(1 44))((1 2)-48)(0#17 8(0 0))((1 10)0)(0#19 8(1 44))(5(0 14)1 4611686018427387904)(5(0 15)1 4611686018427387904)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#25(0 66))((0 0)2147446784)(0 17592186048512)(7#27#28#25(0 66))(2 6(1 44)(0 3))(#30 2147450880)(2 0(1 11)(0 7))(2 6#32(0 3))(2 0(1 2)(0 -56))(2 6#34(0 3))(#35 2147450880)(7#31#33#36(0 5))(5(0 16)1 4611686018427387904)((1 2)-24)(0#39 8(1 10))((1 2)-16)(0#41 8(1 8))((1 2)-8)(0#43 8(1 1))(6#19(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(7#27#28#19(0 24))(5(1 11)66 66)((1 2)-8192)(0 8048)(9#50#51)((1 2)-64)(9#53(0 8))(0 8192)(6#50#55)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#36(0 5))(7#50#55#19(0 24))(2 6(1 10)(0 3))(#61 2147450880)(7#62(0 3)#36(0 5))(2 0(1 2)(0 -24)))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xboth_R4 356%positive "(856312((1 0)(1 88)(2 0(1 2)(0 -64))(1 3)(1 4)(1 89)(1 90)(1 91)(1 10)(1 9)(1 92)(1 93)(1 94)(1 95)(1 96)(1 97)(1 98)(1 99)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 100)(1 101)(1 102)(1 103))(#1#4#5#7#9#12#14#16#18#20#21#22#23#24#26#29#37#38#40#42#44#45#46#47#48#49#52#54#56#57#58#59#60#63)104(((1 2)-8192#55)((1 10)0(0 24)))()(0 12))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xboth_R4 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints4 : list (nat * CC.subst) := hints3.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xboth_R4 548%positive "((0(0(856176 856332 1429232 732972 527120 857884 1402040 1403068))(1 0))(((856332((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 89))(6(1 90))(7(1 91))(8(1 8))(9(1 9))(10#34)(11#64)(12(0 0))(13#3)(14(2 6#64(0 3)))(15(2 0(2 6(2 0(1 2)(0 -40))(0 3))#3))(16(0 0))(17(0 0))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 100))(29(1 101))(30(1 102))(31(1 103)))()((0((1 2)-72)8(0 856320))#1#4#5#7#9#12#14#16#18#20#21#22#23#24#26#29#37#38#40#42#44#45#46#47#48#49#52#54#56#57#58#59#60#63))(1 856332)))()())"%pstring.
