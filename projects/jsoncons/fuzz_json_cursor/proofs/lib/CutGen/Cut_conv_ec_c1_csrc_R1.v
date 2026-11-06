(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_conv_ec_c1_csrc_T Cut_conv_ec_c1_csrc_R0.
Definition dict_Cut_conv_ec_c1_csrc_R1 : CCD.pt := CCD.mk_table 748%positive "((2 0(1 2)(0 -32))((0 0)864160)(0#2 1(0 0))((0 0)864161)(0#4 1(0 2))(5(0 10)1 4611686018427387904)((1 2)-24)(0#7 8(1 9))((1 2)-16)(0#9 8(1 8))((1 2)-8)(0#11 8(1 1))(6#2(0 2))((0 0)1001976)(0#14 1(0 0))((0 0)1001980)(0#16 4(0 0))((0 0)1001984)(0#18 4(0 2))((0 0)1001992)(0 1002000)(0#20 8#21)((0 0)1002000)(0#23 8(0 0))((0 0)1002008)(0 676696)(0#25 8#26)((0 0)1002264)(0 234372)(0#28 8#29)((0 0)1002016)(0 398928)(0#31 8#32)((0 0)1002272)(0 797784)(0#34 8#35)(6#14(0 544))((1 10)0)(9#38(0 16))(6#38(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)((1 2)-256)(9#43(0 232))(6#43(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 793640)(7#43(0 256)#38(0 16))((0 0)65536)(0 942080)(7#38(0 16)#50#51)(5(0 9)1 4611686018427387904))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_conv_ec_c1_csrc_R1 360%positive "(238076((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)(1 10)(1 11)(0 1)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#3#5#6#8#10#12#13#15#17#19#22#24#27#30#33#36#37#39#40#41#42#44#45#46#47#48#49#52)48(((1 2)-256(0 256))((1 10)0(0 16))((0 0)864160(0 2))((0 0)1001976(0 544)))()(0 9))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_conv_ec_c1_csrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_c1_csrc_R1 489%positive "((0(0(237976 238060 275884 275964 676300 744000 745408))(4#53(1 0)))(((676300((1(0 238112))(2#1)(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 10))(9(1 11))(10#32)(11(0 797776))(12(0 797736))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#53#3#5#6#8#10#12#13#15#17#19#22#24#27#30#33#36#37#39#40#41#42#44#45#46#47#48#49#52))(1 676300)))()())"%pstring.
