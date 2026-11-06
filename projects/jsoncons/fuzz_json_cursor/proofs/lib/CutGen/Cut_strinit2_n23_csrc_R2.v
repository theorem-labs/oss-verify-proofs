(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strinit2_n23_csrc_T Cut_strinit2_n23_csrc_R0 Cut_strinit2_n23_csrc_R1.
Definition dict_Cut_strinit2_n23_csrc_R2 : CCD.pt := CCD.mk_table 845%positive "(((1 36)0)(2#1(0 23)1)(9#1(0 23))(0 1048575)(5#4 1 4611686018427387904)((1 10)16)(0#6 8(1 36))((1 10)8)(0#8 8(0 23))((1 10)0)(0#10 8(0 27))(5(1 36)4096 140737488355328)(4(1 36)16)((1 36)23)(6#1(0 26))((0 0)65536)(0 942080)(7#1(0 26)#16#17)((1 2)-8288)(0 8288)(7#1(0 26)#19#20)((1 11)0)(7#1(0 26)#22(0 23))(7#1(0 26)#10(0 24))(0 8224)(9#19#25)(0 1048576)(5#27 1 4611686018427387904)((1 2)-64)(0#29 8(0 23))((1 2)-56)(0 270456)(0#31 8#32)((1 2)-48)(0#34 8(1 20))((1 2)-40)(0#36 8(1 19))((1 2)-32)(0#38 8(1 18))((1 2)-24)(0#40 8(1 9))((1 2)-16)(0#42 8(1 8))((1 2)-8)(0#44 8(1 1))(6#10(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#29(0 0))(6#19#20)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#19#20#10(0 24))(2#22(0 23)1)(9#22(0 23))(5(1 11)4096 140737488355328)(7#19#20#22(0 23))(7#10(0 24)#22(0 23))(5(0 3)0 4611686018427387904))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit2_n23_csrc_R2 392%positive "(270492((1 0)(1 48)(2 0(1 2)(0 -48))(1 3)(1 4)(1 49)(1 50)(1 51)(0 23)(1 11)(1 36)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 10)(1 36)(0 27)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#2#3#5#7#9#11#12#13(9#14(0 3))#15#18#21#23#24#26#28#30#33#35#37#39#41#43#45#46#47#48#49#50#51#52#53#54#55#56#57#58#59)64(((1 2)-8288#20)((1 10)0(0 24))((1 36)0(0 26)))()(0 1048574))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit2_n23_csrc_R2 17%positive "(((1 36)(0 26)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_strinit2_n23_csrc_R2 521%positive "((0(0(270352 270528 684944 745028 744000 745408))(1 0))(((270528((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(1 36))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0#14 1(0 0))#2#3#5#7#9#11#12#13(9((1 36)24)(0 2))#15#18#21#23#24#26#28#30#33#35#37#39#41#43#45#46#47#48#49#50#51#52#53#54#55#56#57#58#59))(1 270528)))()())"%pstring.
