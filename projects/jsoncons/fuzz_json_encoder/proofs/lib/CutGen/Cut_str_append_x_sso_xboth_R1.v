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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_str_append_x_sso_xboth_T Cut_str_append_x_sso_xboth_R0.
Definition dict_Cut_str_append_x_sso_xboth_R1 : CCD.pt := CCD.mk_table 563%positive "((2 0(1 10)(1 32))(2 0#1(0 1))(3 1433600 1466368)((0 0)1497016)(0 2147450880)(0#4 8#5)(#2 0)(2#7(1 12)1)(5(0 100)1 4611686018427387904)((1 2)-40)(0#10 8(1 19))((1 2)-32)(0#12 8(1 18))((1 2)-24)(0#14 8(1 9))((1 2)-16)(0#16 8(1 8))((1 2)-8)(0#18 8(1 1))((1 10)0)(4 0(0 2)(1 32))(5(1 32)0 22)(5(1 33)0 72057594037927935)(5(1 12)1 22)(2 0(1 12)(1 32))(5#25 1 22)((1 10)1)(2#27(1 32)0)(6#20(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)((1 2)-4368)(0 4328)(9#32#33)(0 4368)(6#32#35)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#32#35#20(0 24))(2 0(1 10)#25))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_append_x_sso_xboth_R1 351%positive "(1055600((1 0)(1 40)(2 0(1 2)(0 -48))(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 12)#2(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 32)(2 0(1 10)(0 1))(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#3#6#8#9#11#13#15#17#19#3#6(0#20 1#21)#22#23#24#26#28(9#20(0 24))#29#30#31#34#36#37#38#39)56(((1 2)-4368#35)((1 10)0(0 24)))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_append_x_sso_xboth_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_append_x_sso_xboth_R1 566%positive "((0(0(1055420 1055668 527112 1402040 1403068))(1 0))(((1055668((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 8))(9(1 9))(10(1 10))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()((0(#40 1)1(0 0))(0#20 1(2 0(4 0(0 2)(1 12))#21))#3#6#8#9#11#13#15#17#19#3#6#22#23#24#26#28(9#27#25)(9(#40 2)(2 0(2 0(4 0(0 -1)(1 12))(4 0(0 -1)(1 32)))(0 22)))#29#30#31#34#36#37#38#39))(1 1055668)))()())"%pstring.
