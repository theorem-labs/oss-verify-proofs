(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vec_reserve_cboth_T Cut_vec_reserve_cboth_R0 Cut_vec_reserve_cboth_R1 Cut_vec_reserve_cboth_R2.
Definition dict_Cut_vec_reserve_cboth_R3 : CCD.pt := CCD.mk_table 1157%positive "((2 0(1 2)(0 -56))(2 0(1 10)(0 8))(2 0(1 2)(0 -48))(0 2147450880)(2 6(1 10)(0 3))(3 1393824 1397544)((0 0)1432824)(0#7 8#4)(5(0 14)1 4611686018427387904)(5(0 15)1 4611686018427387904)((1 2)-144)(0#11 8(1 24))((1 2)-136)(0#13 8(1 23))((1 2)-128)(0#15 8(1 22))((1 2)-120)(0#17 8(1 21))((1 2)-112)(0#19 8(1 20))((1 2)-104)(0#21 8(1 19))((1 2)-96)(0#23 8(1 18))((1 2)-88)(0#25 8(1 9))((1 2)-80)(0#27 8(1 10))((1 2)-72)(0 829812)(0#29 8#30)((1 2)-32)(2 0(1 44)(0 66))((1 2)-48)((1 2)-40)((1 2)-56)(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#39(0 66))((0 0)2147446784)(0 17592186048512)(7#41#42#39(0 66))(2 6(1 44)(0 3))(#44 2147450880)(2 0(1 11)(0 7))(2 6#46(0 3))(2 6#1(0 3))(#48 2147450880)(7#45#47#49(0 5))(5(0 16)1 4611686018427387904)((1 2)-24)(0#52 8(1 10))((1 2)-16)(0#54 8(1 8))((1 2)-8)(0#56 8(1 1))((1 10)0)((1 10)8)((1 10)16)(6#58(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(#5 2147450880)(1#64(0 3))(7#41#42#58(0 24))(5(1 11)66 66)((1 2)-8192)(0 8048)(9#68#69)((1 2)-64)(9#71(0 8))(0 8192)(6#68#73)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#49(0 5))(7#68#73#58(0 24))(7#64(0 3)#49(0 5))(5(0 13)1 4611686018427387904))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_cboth_R3 481%positive "(809612((1 0)(1 72)(2 0(1 2)(0 -144))(1 3)(1 4)(1 73)(1 74)(1 75)#1(1 10)(1 44)(1 77)(1 78)(1 79)(1 80)(1 81)(1 82)(1 83)#2#3(1 44)#4(2 0(2 6#2(0 3))#4)(2 0(2 6#3(0 3))#4)(2 0#5#4)(1 25)(1 26)(1 27)(1 84)(1 85)(1 86)(1 87))(#6#8#9#6#8#10#12#14#16#18#20#22#24#26#28#31(0#32 8#33)(0#34 8(1 44))(0#35 8(1 44))(0#36 8(1 44))#6#8#37#38#40#43#50#51#53#55#57#6#8(0#58 8(0 0))(0#59 8(0 0))(0#60 8(0 0))#61#62#63#65#66#67#70#72#74#75#76#77#78#79)88(((1 2)-8192#73)((1 10)0(0 24)))()(0 13))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_cboth_R3 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_cboth_R3 614%positive "((0(0(829676 829832 1363704 727788 520756 810224 1336512 1337540))(4#80(1 0)))(((810224((1#30)(2(2 0(1 2)(0 -64)))(3(1 3))(4(1 4))(5(1 73))(6(1 74))(7(1 75))(8(1 10))(9(1 9))(10(1 10))(11(0 0))(12(0 0))(13(1 79))(14(1 80))(15(1 81))(16(1 82))(17(1 83))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 84))(29(1 85))(30(1 86))(31(1 87)))()(#80(0#36 8(0 0))(0#32 8(0 0))(0#60 8#33)(0#35 8(0 0))(0#59 8(1 44))(0#34 8(0 0))(0#58 8(1 44))#9#10#12#14#16#18#20#22#24#26#28#31#37#38#40#43#50#51#53#55#57#61#62#63#65#66#67#70#72#74#75#76#77#78#79))(1 810224)))()())"%pstring.
