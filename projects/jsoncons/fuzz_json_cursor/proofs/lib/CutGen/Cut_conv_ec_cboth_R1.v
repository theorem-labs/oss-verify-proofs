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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_conv_ec_cboth_T Cut_conv_ec_cboth_R0.
Definition dict_Cut_conv_ec_cboth_R1 : CCD.pt := CCD.mk_table 519%positive "((2 0(1 2)(0 -32))(0 2147450880)(3 1393824 1397544)((0 0)1432824)(0#4 8#2)(5(0 20)1 4611686018427387904)((1 2)-32)(0#7 8(1 18))((1 2)-24)(0#9 8(1 9))((1 2)-16)(0#11 8(1 8))((1 2)-8)(0#13 8(1 1))((1 10)0)(9#15(0 16))(6#15(0 16))(5(1 10)7028736 140737479966704)(4(1 10)8)(2 6(1 10)(0 3))(#20 2147450880)(1#21(0 2))((0 0)2147446784)(0 17592186048512)(7#23#24#15(0 16))(5(1 11)1 31)((1 2)-1024)(9#27(0 992))(0 1024)(6#27#29)(5(1 2)140735332484096 140737488355328)(4(1 2)16)(7#27#29#15(0 16))(5(0 19)1 4611686018427387904))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_conv_ec_cboth_R1 292%positive "(729632((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)(1 10)(1 11)(0 1)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#3#5#6#8#10#12#14#3#5#16#17#18#19#22#25#26#28#30#31#32#33)48(((1 2)-1024#29)((1 10)0(0 16)))()(0 19))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_conv_ec_cboth_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_cboth_R1 480%positive "((0(0(729476 729476 729616 863640 436716 863720 1336512 1337540))(4#34(1 0)))(((436716((1(0 729668))(2#1)(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 10))(9(1 11))(10(0 986684))(11(0 1412176))(12(0 1401640))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#34#3#5#6#8#10#12#14#3#5#16#17#18#19#22#25#26#28#30#31#32#33))(1 436716)))()())"%pstring.
