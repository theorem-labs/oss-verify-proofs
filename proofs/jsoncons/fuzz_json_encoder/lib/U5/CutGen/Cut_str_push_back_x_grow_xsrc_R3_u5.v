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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_x_grow_xsrc_T_u5 Cut_str_push_back_x_grow_xsrc_R0_u5 Cut_str_push_back_x_grow_xsrc_R1_u5 Cut_str_push_back_x_grow_xsrc_R2_u5.
Definition dict_Cut_str_push_back_x_grow_xsrc_R3 : CCD.pt := CCD.mk_table 1053%positive "((4 0(0 4)(1 32))(2 0#1(0 -2))(2 6#2(0 3))(4 0(0 8)#3)(2 0#4(0 8))(4 0(0 2)(1 32))(2 0#6(0 -1))((1 2)-8288)(0 8224)(9#8#9)(0 1048574)(5#11 1 4611686018427387904)((1 48)0)(2#13#7 0)(9#13#7)(0 1048575)(5#16 1 4611686018427387904)(5(1 48)4096 140737488355328)(4(1 48)16)(2 0#6(1 48))(#20 -1)(4 0(0 -2)(1 32))(2 0#22#4)(2 0#23(0 9))(6#13#5)((0 0)65536)(0 974848)(7#13#5#26#27)((1 2)-8304)(0 8304)(7#13#5#29#30)((1 10)0)(7#13#5#32(0 24))((1 34)0)(7#13#5#34#6)(0 1048576)(5#36 1 4611686018427387904)(2 0#6(0 1))(6 0 0 1#38)(2 9#39(0 1))(5#40 1 1)((1 2)-64)(0#42 8(1 22))((1 2)-56)(0#44 8(1 21))((1 2)-48)(0#46 8(1 20))((1 2)-40)(0#48 8(1 19))((1 2)-32)(0#50 8(1 18))((1 2)-24)(0#52 8(1 9))((1 2)-16)(0#54 8(1 8))((1 2)-8)(0#56 8(1 1))((1 10)8)((1 10)16)(5(1 32)12 70368744177664)(5(1 11)0 255)(5(1 34)4096 140737488355328)(4(1 34)16)(6#32(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(9#29(0 16))(9#42(0 0))(6#29#30)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#29#30#32(0 24))(7#29#30#34#6)(7#32(0 24)#34#6)(5#24 0 4611686018427387904)(0 8240)(9#29#76))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_grow_xsrc_R3 432%positive "(437104((1 0)(1 81)(2 0(1 2)(0 -64))(1 3)(1 4)(1 82)(1 83)(1 84)(1 11)(1 10)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)(1 34)#5#7#6(1 48)(1 23)(1 24)(1 25)(1 26)(1 27)(1 93)(1 94)(1 95)(1 96))(#10#12#14#15#17#18#19(9#21#24)#25#28#31#33#35#37#41#43#45#47#49#51#53#55#57(0#32 8#38)(0#58 8#7)(0#59 8(1 34))#60#61#62#63(9#32(0 24))#64#65#66#67#68#69#70#71#72#73#74#75#77)97(((1 2)-8304#30)((1 10)0(0 24))((1 48)0#5))()(0 1048573))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_grow_xsrc_R3 13%positive "(((1 48)#5))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_grow_xsrc_R3 609%positive "((0(0(436872 437176 798592 718776 779340 778312 779720))(1 0))(((437176((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 82))(6(1 83))(7(1 84))(8(1 8))(9(1 9))(10(2 0#20(0 -1)))(11#6)(12(1 87))(13(1 88))(14(1 89))(15(1 90))(16(1 91))(17(1 92))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 93))(29(1 94))(30(1 95))(31(1 96)))()((0(#20 0)1(0 0))(0#21 1(1 11))(0#58 8#6)(0#59 8(1 48))(0#32 8(2 0#4(0 9)))#10#12#14#15#17#18#19(9(#20 1)(2 0#23(0 7)))#25#28#31#33#35#37#41#43#45#47#49#51#53#55#57#60#61#62#63#64#65#66#67#68#69#70#71#72#73#74#75#77))(1 437176)))()())"%pstring.
