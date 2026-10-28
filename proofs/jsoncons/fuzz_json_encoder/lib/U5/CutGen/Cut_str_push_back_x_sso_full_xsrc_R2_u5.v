(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_x_sso_full_xsrc_T_u5 Cut_str_push_back_x_sso_full_xsrc_R0_u5 Cut_str_push_back_x_sso_full_xsrc_R1_u5.
Definition dict_Cut_str_push_back_x_sso_full_xsrc_R2 : CCD.pt := CCD.mk_table 652%positive "(((1 48)0)(2#1(0 22)0)(9#1(0 22))(0 1048575)(5#4 1 4611686018427387904)(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)22)(6#1(0 48))((0 0)65536)(0 974848)(7#1(0 48)#10#11)((1 2)-8304)(0 8304)(7#1(0 48)#13#14)((1 10)0)(7#1(0 48)#16(0 24))(0 1048576)(5#18 1 4611686018427387904)((1 2)-64)(0#20 8(1 22))((1 2)-56)(0#22 8(1 21))((1 2)-48)(0#24 8(1 20))((1 2)-40)(0#26 8(1 19))((1 2)-32)(0#28 8(1 18))((1 2)-24)(0#30 8(1 9))((1 2)-16)(0#32 8(1 8))((1 2)-8)(0#34 8(1 1))(5(1 11)0 255)(6#16(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(0 8240)(9#13#40)(6#13#14)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#13#14#16(0 24))(5(0 26)0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_sso_full_xsrc_R2 419%positive "(437084((1 0)(1 65)(2 0(1 2)(0 -64))(1 3)(1 4)(1 66)(1 67)(1 68)(1 11)(1 10)(1 48)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(2 0(1 10)(0 1))(0 48)(0 22)(0 23)(1 48)(1 23)(1 24)(1 25)(1 26)(1 27)(1 77)(1 78)(1 79)(1 80))(#2#3#5#6#7(9#8(0 26))#9#12#15#17#19#21#23#25#27#29#31#33#35(0#16 1(0 44))#36(2((1 10)1)(0 22)0)(9#16(0 24))#37#38#39#41#42#43#44#45#46)81(((1 2)-8304#14)((1 10)0(0 24))((1 48)0(0 48)))()(0 1048574))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_sso_full_xsrc_R2 17%positive "(((1 48)(0 48)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_sso_full_xsrc_R2 584%positive "((0(0(436872 437176 798592 718776 779340 778312 779720))(1 0))(((437176((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 66))(6(1 67))(7(1 68))(8(1 8))(9(1 9))(10(2 0(1 48)(0 22)))(11(0 23))(12(1 71))(13(1 72))(14(1 73))(15(1 74))(16(1 75))(17(1 76))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 77))(29(1 78))(30(1 79))(31(1 80)))()((0((1 48)23)1(0 0))(0#8 1(1 11))(0((1 10)8)8(0 23))(0((1 10)16)8(1 48))(0#16 8(0 49))#2#3#5#6#7(9((1 48)24)(0 24))#9#12#15#17#19#21#23#25#27#29#31#33#35#36#37#38#39#41#42#43#44#45#46))(1 437176)))()())"%pstring.
