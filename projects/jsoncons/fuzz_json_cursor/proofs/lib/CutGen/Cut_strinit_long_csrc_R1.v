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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strinit_long_csrc_T Cut_strinit_long_csrc_R0.
Definition dict_Cut_strinit_long_csrc_R1 : CCD.pt := CCD.mk_table 851%positive "((2 6(1 12)(0 3))(4 0(0 8)#1)(2 0#2(0 8))(5(1 36)4096 140737488355328)(4(1 36)16)((1 36)0)(9#6#3)(6#6#3)((0 0)65536)(0 942080)(7#6#3#9#10)((1 2)-8288)(0 8288)(7#6#3#12#13)((1 11)0)(7#6#3#15(1 12))((1 10)0)(7#6#3#17(0 24))(0 8224)(9#12#19)(0 1048576)(5#21 1 4611686018427387904)((1 2)-64)(0#23 8(1 12))((1 2)-56)(0 235132)(0#25 8#26)((1 2)-48)(0#28 8(1 20))((1 2)-40)(0#30 8(1 19))((1 2)-32)(0#32 8(1 18))((1 2)-24)(0#34 8(1 9))((1 2)-16)(0#36 8(1 8))((1 2)-8)(0#38 8(1 1))(6#17(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#23(0 0))(6#12#13)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#12#13#17(0 24))(2#15(1 12)1)(9#15(1 12))(5(1 11)4096 140737488355328)(7#12#13#15(1 12))(7#17(0 24)#15(1 12))(5(1 12)24 67108864)(0 1048575)(5#54 1 4611686018427387904)(2 0#2(0 9))(4 0(0 -1)(1 12))(2 0#57#2)(2 0#58(0 8))(5#59 0 4611686018427387904))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_long_csrc_R1 359%positive "(764308((1 0)(1 32)(2 0(1 2)(0 -64))(1 3)(1 4)(1 33)(1 34)(1 35)#3(1 11)(1 36)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 10)(1 19)#3(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#4#5#7#8#11#14#16#18#20#22#24#27#29#31#33#35#37#39(9#17(0 24))#40#41#42#43#44#45#46#47#48#49#50#51#52#53)48(((1 2)-8288#13)((1 10)0(0 24))((1 36)0#3))()#54)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_long_csrc_R1 13%positive "(((1 36)#3))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_long_csrc_R1 566%positive "((0(0(235028 235204 684944 745028 744000 745408))(16 0(4#55(1 0))))(((745028((1(0 235168))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 12))(9(1 11))(10(1 36))(11(1 11))(12(1 12))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 10))(19(1 36))(20#56)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#55#60(0((1 10)16)8(1 36))(0((1 10)8)8(1 12))(0#17 8#56)#4#5#7#8#11#14#16#18#20#22#24#27#29#31#33#35#37#39#40#41#42#43#44#45#46#47#48#49#50#51#52#53))(1 745028)))((0#60))())"%pstring.
