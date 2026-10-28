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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_x_sso_full_xsrc_T_u5 Cut_str_push_back_x_sso_full_xsrc_R0_u5.
Definition dict_Cut_str_push_back_x_sso_full_xsrc_R1 : CCD.pt := CCD.mk_table 710%positive "((2 0(1 2)(0 -64))(2 0(1 10)(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)0)(9#5(0 48))(6#5(0 48))((0 0)65536)(0 974848)(7#5(0 48)#8#9)((1 2)-8304)(0 8304)(7#5(0 48)#11#12)((1 10)0)(7#5(0 48)#14(0 24))(0 1048576)(5#16 1 4611686018427387904)((1 2)-64)(0#18 8(1 22))((1 2)-56)(0#20 8(1 21))((1 2)-48)(0#22 8(1 20))((1 2)-40)(0#24 8(1 19))((1 2)-32)(0#26 8(1 18))((1 2)-24)(0#28 8(1 9))((1 2)-16)(0#30 8(1 8))((1 2)-8)(0#32 8(1 1))(0#14 1(0 44))(5(1 11)0 255)((1 10)1)(2#36(0 22)0)(9#14(0 24))(6#14(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(0 8240)(9#11#42)(6#11#12)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#11#12#14(0 24))(0 1048575)(5#48 1 4611686018427387904)(5(0 26)0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_sso_full_xsrc_R1 328%positive "(437068((1 0)(1 49)#1(1 3)(1 4)(1 50)(1 51)(1 52)(1 11)(1 10)(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)#2(0 48)(0 22)(0 23)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#3#4#6#7#10#13#15#17#19#21#23#25#27#29#31#33#34#35#37#38#39#40#41#43#44#45#46#47)65(((1 2)-8304#12)((1 10)0(0 24))((1 48)0(0 48)))()#48)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_sso_full_xsrc_R1 17%positive "(((1 48)(0 48)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_sso_full_xsrc_R1 491%positive "((0(0(436872 437176 798592 718776 779340 778312 779720))(16 0(4#49(1 0))))(((779340((1(0 437084))(2#1)(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 11))(9(1 10))(10(1 48))(11#2)(12(0 22))(13(1 56))(14(1 57))(15(1 58))(16(1 59))(17(1 60))(18#2)(19(0 48))(20(0 22))(21(0 23))(22(1 48))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()(#49#50#3#4#6#7#10#13#15#17#19#21#23#25#27#29#31#33#34#35#37#38#39#40#41#43#44#45#46#47))(1 779340)))((0#50))())"%pstring.
