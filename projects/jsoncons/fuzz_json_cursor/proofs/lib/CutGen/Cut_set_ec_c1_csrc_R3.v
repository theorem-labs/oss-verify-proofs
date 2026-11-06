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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_set_ec_c1_csrc_T Cut_set_ec_c1_csrc_R0 Cut_set_ec_c1_csrc_R1 Cut_set_ec_c1_csrc_R2.
Definition dict_Cut_set_ec_c1_csrc_R3 : CCD.pt := CCD.mk_table 807%positive "(((0 0)864168)(0#1 1(0 1))((0 0)864169)(0#3 1(0 1))(5(0 8)1 4611686018427387904)((0 0)1001976)(0#6 1(0 0))((0 0)1001980)(0#8 4(0 0))((0 0)1001984)(0#10 4(0 3))((0 0)1001992)(0 1002000)(0#12 8#13)((0 0)1002000)(0#15 8(0 0))((0 0)1002008)(0 676696)(0#17 8#18)((0 0)1002264)(0 234372)(0#20 8#21)((0 0)1002016)(0 398928)(0#23 8#24)((0 0)1002272)(0 797776)(0#26 8#27)((0 0)1002024)(0#29 8#24)((0 0)1002280)(0 797784)(0#31 8#32)(5(0 9)1 4611686018427387904)(5(0 10)1 4611686018427387904)((1 2)-24)(0#36 8(1 9))((1 2)-16)(0#38 8(1 8))((1 2)-8)(0#40 8(1 1))(6#1(0 2))(6#6(0 544))((1 10)0)(6#44(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)((1 2)-256)(9#48(0 232))(6#48(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 793640)(7#48(0 256)#44(0 16))((0 0)65536)(0 942080)(7#44(0 16)#55#56))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_set_ec_c1_csrc_R3 396%positive "(244212((1 0)(1 64)(2 0(1 2)(0 -32))(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)(1 11)(1 68)(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#2#4#5#7#9#11#14#16#19#22#25#28#30#33#34#35#37#39#41#42#43(9#44(0 16))#45#46#47#49#50#51#52#53#54#57)80(((1 2)-256(0 256))((1 10)0(0 16))((0 0)864168(0 2))((0 0)1001976(0 544)))()(0 7))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_set_ec_c1_csrc_R3 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec_c1_csrc_R3 509%positive "((0(0(244064 244148 275884 275964 676300 744000 745408))(1 0))(((244148((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 8))(9(1 9))(10(1 10))(11(1 69))(12(1 70))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()((0((1 10)8)8#32)(0#44 8(1 11))#2#4#5#7#9#11#14#16#19#22#25#28#30#33#34#35#37#39#41#42#43#45#46#47#49#50#51#52#53#54#57))(1 244148)))()())"%pstring.
