(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_append_x_sso_xsrc_T_u5 Cut_str_append_x_sso_xsrc_R0_u5.
Definition dict_Cut_str_append_x_sso_xsrc_R1 : CCD.pt := CCD.mk_table 645%positive "((2 0(1 10)(1 32))(#1 1)(9#2(1 12))(0 1048576)(5#4 1 4611686018427387904)((1 2)-40)(0#6 8(1 19))((1 2)-32)(0#8 8(1 18))((1 2)-24)(0#10 8(1 9))((1 2)-16)(0#12 8(1 8))((1 2)-8)(0#14 8(1 1))((1 10)0)(4 0(0 2)(1 32))(5(1 32)0 22)(5(1 33)0 72057594037927935)(5(1 12)1 22)(2 0(1 12)(1 32))(5#21 1 22)(5(1 11)4096 140737488355328)(2 0(1 11)(1 12))(5#24 4096 140737488355328)(2 0(1 10)#21)(#26 1)(4 0(0 -1)(1 12))(4 0(0 -1)(1 32))(2 0#28#29)(6#16(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)((1 2)-8384)(0 8344)(9#34#35)(0 8384)(6#34#37)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#34#37#16(0 24))((1 11)0)(7#34#37#42(1 12))(7#16(0 24)#42(1 12)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_append_x_sso_xsrc_R1 394%positive "(436468((1 0)(1 48)(2 0(1 2)(0 -48))(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 12)(2 0#1(0 1))(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 32)(2 0(1 10)(0 1))(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#5#7#9#11#13#15(0#16 1#17)#18#19#20#22#23#25(9#16(2 0(1 32)(0 1)))(9#27(2 0#30(0 23)))#31#32#33#36#38#39#40#41#43#44)64(((1 2)-8384#37)((1 10)0(0 24)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_append_x_sso_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_append_x_sso_xsrc_R1 529%positive "((0(0(436288 436536 779340 778312 779720))(1 0))(((436536((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(1 10))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0#27 1(0 0))(0#16 1(2 0(4 0(0 2)(1 12))#17))#3#5#7#9#11#13#15#18#19#20#22#23#25(9((1 10)1)(1 32))(9(#26 2)(2 0#30(0 22)))#31#32#33#36#38#39#40#41#43#44))(1 436536)))()())"%pstring.
