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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_reserve_xsrc_T Cut_vec_reserve_xsrc_R0.
Definition dict_Cut_vec_reserve_xsrc_R1 : CCD.pt := CCD.mk_table 677%positive "((5(1 36)4096 140737488355328)(4(1 36)16)((1 36)0)(9#3(0 66))(6#3(0 66))((0 0)65536)(0 962560)(7#3(0 66)#6#7)((1 2)-8304)(0 8304)(7#3(0 66)#9#10)((1 10)0)(7#3(0 66)#12(0 24))(0 8224)(9#9#14)(0 1048576)(5#16 1 4611686018427387904)((1 2)-80)(0#18 8(0 0))((1 2)-72)(0 277852)(0#20 8#21)((1 2)-64)(0#23 8(1 22))((1 2)-56)(0#25 8(1 21))((1 2)-48)(0#27 8(1 20))((1 2)-40)(0#29 8(1 19))((1 2)-32)(0#31 8(1 18))((1 2)-24)(0#33 8(1 9))((1 2)-16)(0#35 8(1 8))((1 2)-8)(0#37 8(1 1))((1 10)8)((1 10)16)(6#12(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(9#18(0 0))(6#9#10)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#9#10#12(0 24))(277772 277976 704428 763484 764892)(0#49))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_reserve_xsrc_R1 388%positive "(783792((1 0)(1 32)(2 0(1 2)(0 -80))(1 3)(1 4)(1 33)(1 34)(1 35)(0 66)(0 0)(1 36)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 10)(0 66)(0 0)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#1#2#4#5#8#11#13#15#17#19#22#24#26#28#30#32#34#36#38(0#12 8(0 0))(0#39 8(0 0))(0#40 8(0 0))#41#42#43#44#45#46#47#48)48(((1 2)-8304#10)((1 10)0(0 24))((1 36)0(0 66)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_reserve_xsrc_R1 17%positive "(((1 36)(0 66)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vec_reserve_xsrc_R1 472%positive "((0#50(0#50(1 0)))(((277976((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10(1 36))(11(0 0))(12(0 0))(13(1 36))(14(0 0))(15(0 0))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()((0#40 8(2 0(1 36)(0 66)))(0#39 8(1 36))(0#12 8(1 36))#1#2#4#5#8#11#13#15#17#19#22#24#26#28#30#32#34#36#38#41#42#43#44#45#46#47#48))(1 277976)))()())"%pstring.
