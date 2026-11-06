(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm8CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import StrtodAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strtod_casan_T Cut_strtod_casan_R0 Cut_strtod_casan_R1.
Definition dict_Cut_strtod_casan_R2 : CCDD.pt := CCDD.mk_table 872%positive "((0 1152921504606846975)(5#1 1 4611686018427387904)((1 11)0)(0#3 8(1 34))((1 2)-264)(0#5 8(1 34))(0 1152921504606846976)(5#7 1 4611686018427387904)((1 2)-88)(0 18446744073709551615)(0#9 8#10)((1 2)-72)(0#12 8(0 0))((1 2)-80)(0#14 8(0 0))((1 2)-256)(0#16 8#10)((1 2)-184)(0#18 8(1 10))((1 2)-40)(0#20 8(1 32))((1 2)-32)(0#22 8(1 18))((1 2)-24)(0#24 8(1 9))((1 2)-16)(0#26 8(1 8))((1 2)-8)(0#28 8(1 1))(5(1 2)140735332492016 140737488355328)(4(1 2)16)((1 2)-8944)(0 8944)(6#32#33)(0 8680)(9#32#35)((1 2)-248)(9#37(0 64))((1 2)-176)(9#39(0 88))((1 2)-64)(9#41(0 24))((0 0)7015056)(0#43 8(1 32))(5(1 10)4096 140737488355328)(5(1 33)1 67108864)(6#3(0 8))(7#3(0 8)#32#33)(5(1 11)32 140737488355320)(7#3(0 8)#43(0 8))((1 4)-164)(7#3(0 8)#51(0 4))(7#51(0 4)#32#33)(5(1 4)6883920 6883921)(#2#4#6#8#11#13#15#17#19#21#23#25#27#29#30#31#34#36#38#40#42#44#45#46#47#48#49#50#52#53#54))"%pstring.

Definition t2 : CC.cutpoint := CCDD.dec_cp_t dict_Cut_strtod_casan_R2 296%positive "(1327656((1 0)(1 51)(2 0(1 2)(0 -272))(1 3)(1 4)(1 52)(1 53)(1 54)(1 11)(1 10)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 62)(0 7015056)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 63)(1 64)(1 65)(1 66))#55 67(((1 2)-8944#33)((1 11)0(0 8))((1 4)-164(0 4)))()(0 1152921504606846974))"%pstring.
Definition BL2 : CAD.blocks := Eval vm_compute in CCDD.dec_bl_t dict_Cut_strtod_casan_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CAD.pout := CCDD.dec_pout_t dict_Cut_strtod_casan_R2 393%positive "((0(0(1327532 1327688 1310100 1278920 1330948 1331976))(1 0))(((1327688((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 52))(6(1 53))(7(1 54))(8(1 8))(9(1 9))(10(1 32))(11(1 32))(12(1 57))(13(1 58))(14(1 59))(15(1 60))(16(1 61))(17(1 62))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 63))(29(1 64))(30(1 65))(31(1 66)))()#55)(1 1327688)))()())"%pstring.
