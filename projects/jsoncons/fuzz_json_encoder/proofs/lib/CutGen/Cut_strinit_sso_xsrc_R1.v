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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strinit_sso_xsrc_T Cut_strinit_sso_xsrc_R0.
Definition dict_Cut_strinit_sso_xsrc_R1 : CCD.pt := CCD.mk_table 629%positive "((2 0(1 10)(0 1))((1 10)1)(2#2(1 12)1)(9#2(1 12))(0 1048576)(5#5 1 4611686018427387904)((1 10)0)(4 0(0 2)(1 12))(0#7 1#8)((1 2)-48)(0#10 8(1 20))((1 2)-40)(0#12 8(1 19))((1 2)-32)(0#14 8(1 18))((1 2)-24)(0#16 8(1 9))((1 2)-16)(0#18 8(1 8))((1 2)-8)(0#20 8(1 1))(2 0(1 10)(1 12))(#22 1)(4 0(0 -1)(1 12))(2 0#24(0 23))(6#7(0 24))(5(1 10)1099511627776 140737488355328)(4(1 10)8)((1 2)-8288)(0 8240)(9#29#30)(0 8288)(6#29#32)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#29#32#7(0 24))((1 11)0)(2#37(1 12)1)(9#37(1 12))(5(1 11)4096 140737488355328)(7#29#32#37(1 12))(7#7(0 24)#37(1 12))(5(1 12)1 22)(5#25 0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strinit_sso_xsrc_R1 332%positive "(237556((1 0)(1 32)(2 0(1 2)(0 -48))(1 3)(1 4)(1 33)(1 34)(1 35)(1 12)(1 11)#1(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 10)#1(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#3#4#6#9#11#13#15#17#19#21(9#23#25)#26#27#28#31#33#34#35#36#38#39#40#41#42#43#44)48(((1 2)-8288#32)((1 10)0(0 24)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strinit_sso_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_sso_xsrc_R1 488%positive "((0(0(237416 237592 704428 764512 763484 764892))(1 0))(((237592((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10#1)(11(1 37))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()((0#23 1(0 0))#3#4#6#9#11#13#15#17#19#21(9(#22 2)(2 0#24(0 22)))#26#27#28#31#33#34#35#36#38#39#40#41#42#43#44))(1 237592)))()())"%pstring.
