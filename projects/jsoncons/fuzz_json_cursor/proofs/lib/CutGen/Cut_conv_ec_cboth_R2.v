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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_conv_ec_cboth_T Cut_conv_ec_cboth_R0 Cut_conv_ec_cboth_R1.
Definition dict_Cut_conv_ec_cboth_R2 : CCD.pt := CCD.mk_table 550%positive "((2 0(1 2)(0 -32))(0 2147450880)(3 1393824 1397544)((0 0)1432824)(0#4 8#2)(5(0 19)1 4611686018427387904)(5(0 20)1 4611686018427387904)((1 2)-32)(0#8 8(1 18))((1 2)-24)(0#10 8(1 9))((1 2)-16)(0#12 8(1 8))((1 2)-8)(0#14 8(1 1))((1 10)0)(9#16(0 16))(6#16(0 16))(5(1 10)7028736 140737479966704)(4(1 10)8)(2 6(1 10)(0 3))(#21 2147450880)(1#22(0 2))((0 0)2147446784)(0 17592186048512)(7#24#25#16(0 16))(5(1 11)1 31)((1 2)-1024)(9#28(0 992))(0 1024)(6#28#30)(5(1 2)140735332484096 140737488355328)(4(1 2)16)(7#28#30#16(0 16))(5(0 18)1 4611686018427387904))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_conv_ec_cboth_R2 298%positive "(729668((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(0 0)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)#2(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#5#6#3#5#7#9#11#13#15#3#5#17#18#19#20#23#26#27#29#31#32#33#34)64(((1 2)-1024#30)((1 10)0(0 16)))()(0 18))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_conv_ec_cboth_R2 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_cboth_R2 477%positive "((0(0(729476 729476 729616 863640 436716 863720 1336512 1337540))(4#35(1 0)))(((863720((1(0 729680))(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 10))(9(1 11))(10(0 6882176))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18#2)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#35#3#5#6#3#5#7#9#11#13#15#3#5#17#18#19#20#23#26#27#29#31#32#33#34))(1 863720)))()())"%pstring.
