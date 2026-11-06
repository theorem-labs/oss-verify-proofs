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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vec_reserve_cboth_T Cut_vec_reserve_cboth_R0 Cut_vec_reserve_cboth_R1.
Definition dict_Cut_vec_reserve_cboth_R2 : CCD.pt := CCD.mk_table 1239%positive "((0 -144)(2 0(1 2)#1)(2 0(1 2)(0 -56))(0 2147450880)(3 1393824 1397544)((0 0)1432824)(0#6 8#4)(5(0 15)1 4611686018427387904)((1 2)-144)(0#9 8(1 24))((1 2)-136)(0#11 8(1 23))((1 2)-128)(0#13 8(1 22))((1 2)-120)(0#15 8(1 21))((1 2)-112)(0#17 8(1 20))((1 2)-104)(0#19 8(1 19))((1 2)-96)(0#21 8(1 18))((1 2)-88)(0#23 8(1 9))((1 2)-80)(0#25 8(1 10))((1 2)-72)(0 829812)(0#27 8#28)((1 2)-32)(2 0(1 44)(0 66))(0#30 8#31)((1 2)-48)(0#33 8(1 44))((1 2)-40)(0#35 8(1 44))((1 2)-56)(0#37 8(1 44))(5(1 44)17594333495296 140737479966719)(4(1 44)16)((1 44)0)(6#41(0 66))((0 0)2147446784)(0 17592186048512)(7#43#44#41(0 66))(2 6(1 44)(0 3))(#46 2147450880)(2 0(1 11)(0 7))(2 6#48(0 3))(2 6#3(0 3))(#50 2147450880)(7#47#49#51(0 5))(5(0 16)1 4611686018427387904)((1 2)-24)(0#54 8(1 10))((1 2)-16)(0#56 8(1 8))((1 2)-8)(0#58 8(1 1))((1 10)0)(0#60 8(0 0))((1 10)8)(0#62 8(0 0))((1 10)16)(0#64 8(0 0))(6#60(0 24))(5(1 10)1048576 140737488354816)(4(1 10)8)(2 6(1 10)(0 3))(#69 2147450880)(1#70(0 3))(7#43#44#60(0 24))(5(1 11)66 66)((1 2)-8192)(0 8048)(9#74#75)((1 2)-64)(9#77(0 8))(0 8192)(6#74#79)(5(1 2)140735332491264 140737488355328)(4(1 2)16)(1#51(0 5))(7#74#79#60(0 24))(7#70(0 3)#51(0 5))(5(0 14)1 4611686018427387904)(2 0(1 10)(0 8))(2 0(1 2)(0 -48)))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_cboth_R2 366%positive "(809492((1 0)(1 56)#2(1 3)(1 4)(1 57)(1 58)(1 59)#3(1 10)(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 18)(1 19)(1 20)#4(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(#5#7#8#10#12#14#16#18#20#22#24#26#29#32#34#36#38#5#7#39#40#42#45#52#53#55#57#59#5#7#61#63#65#66#67#68#71#72#73#76#78#80#81#82#83#84#85)72(((1 2)-8192#79)((1 10)0(0 24)))()(0 14))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_cboth_R2 17%positive "(((1 44)(0 66)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_cboth_R2 561%positive "((0(0(829676 829832 1363704 727788 520756 810224 1336512 1337540))(4#86(1 0)))(((520756((1(0 809612))(2#2)(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8#3)(9(1 10))(10(1 44))(11(0 0))(12(0 0))(13(0 0))(14(0 1))(15(0 0))(16(1 66))(17(1 67))(18#87)(19#88)(20(1 44))(21#4)(22(2 0(2 6#87(0 3))#4))(23(2 0(2 6#88(0 3))#4))(24(2 0#69#4))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()(#86#5#7#8#10#12#14#16#18#20#22#24#26#29#32#34#36#38#5#7#39#40#42#45#52#53#55#57#59#5#7#61#63#65#66#67#68#71#72#73#76#78#80#81#82#83#84#85))(1 520756)))()())"%pstring.
