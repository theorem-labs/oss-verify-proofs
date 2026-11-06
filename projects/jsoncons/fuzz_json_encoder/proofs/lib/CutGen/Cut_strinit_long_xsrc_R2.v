(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strinit_long_xsrc_T Cut_strinit_long_xsrc_R0 Cut_strinit_long_xsrc_R1.
Definition dict_Cut_strinit_long_xsrc_R2 : CCD.pt := CCD.mk_table 952%positive "((2 6(1 12)(0 3))(4 0(0 8)#1)(2 0#2(0 9))((1 36)0)(2#4(1 12)1)(9#4(1 12))(0 1048575)(5#7 1 4611686018427387904)((1 10)16)(0#9 8(1 36))((1 10)8)(0#11 8(1 12))((1 10)0)(0#13 8#3)(5(1 36)4096 140737488355328)(4(1 36)16)(2 0(1 12)(1 36))(#17 0)(4 0(0 -1)(1 12))(2 0#19#2)(2 0#20(0 8))(2 0#2(0 8))(6#4#22)((0 0)65536)(0 962560)(7#4#22#24#25)((1 2)-8288)(0 8288)(7#4#22#27#28)((1 11)0)(7#4#22#30(1 12))(7#4#22#13(0 24))(0 8224)(9#27#33)(0 1048576)(5#35 1 4611686018427387904)((1 2)-64)(0#37 8(1 12))((1 2)-56)(0 237520)(0#39 8#40)((1 2)-48)(0#42 8(1 20))((1 2)-40)(0#44 8(1 19))((1 2)-32)(0#46 8(1 18))((1 2)-24)(0#48 8(1 9))((1 2)-16)(0#50 8(1 8))((1 2)-8)(0#52 8(1 1))(6#13(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#37(0 0))(6#27#28)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#27#28#13(0 24))(2#30(1 12)1)(9#30(1 12))(5(1 11)4096 140737488355328)(7#27#28#30(1 12))(7#13(0 24)#30(1 12))(5(1 12)24 67108864)(5#21 0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_long_xsrc_R2 388%positive "(237556((1 0)(1 48)(2 0(1 2)(0 -48))(1 3)(1 4)(1 49)(1 50)(1 51)(1 12)(1 11)(1 36)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 10)(1 36)#3(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#5#6#8#10#12#14#15#16(9#18#21)#23#26#29#31#32#34#36#38#41#43#45#47#49#51#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67#68)64(((1 2)-8288#28)((1 10)0(0 24))((1 36)0#22))()(0 1048574))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_long_xsrc_R2 14%positive "(((1 36)#22))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_long_xsrc_R2 531%positive "((0(0(237416 237592 704428 764512 763484 764892))(1 0))(((237592((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(1 36))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0#18 1(0 0))#5#6#8#10#12#14#15#16(9(#17 1)(2 0#20(0 7)))#23#26#29#31#32#34#36#38#41#43#45#47#49#51#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67#68))(1 237592)))()())"%pstring.
