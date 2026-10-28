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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_x_grow_xsrc_T_u5 Cut_str_push_back_x_grow_xsrc_R0_u5.
Definition dict_Cut_str_push_back_x_grow_xsrc_R1 : CCD.pt := CCD.mk_table 1023%positive "((2 0(1 2)(0 -64))(4 0(0 4)(1 32))(2 0#2(0 -2))(2 6#3(0 3))(4 0(0 8)#4)(2 0#5(0 8))(4 0(0 2)(1 32))(2 0#7(0 -1))(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)0)(9#11#6)(6#11#6)((0 0)65536)(0 974848)(7#11#6#14#15)((1 2)-8304)(0 8304)(7#11#6#17#18)((1 10)0)(7#11#6#20(0 24))((1 34)0)(7#11#6#22#7)(0 1048576)(5#24 1 4611686018427387904)(2 0#7(0 1))(6 0 0 1#26)(2 9#27(0 1))(5#28 1 1)((1 2)-64)(0#30 8(1 22))((1 2)-56)(0#32 8(1 21))((1 2)-48)(0#34 8(1 20))((1 2)-40)(0#36 8(1 19))((1 2)-32)(0#38 8(1 18))((1 2)-24)(0#40 8(1 9))((1 2)-16)(0#42 8(1 8))((1 2)-8)(0#44 8(1 1))(0#20 8#26)((1 10)8)(0#47 8#8)((1 10)16)(0#49 8(1 34))(5(1 32)12 70368744177664)(5(1 11)0 255)(2#22#8 0)(9#22#7)(6#22#7)(5(1 34)4096 140737488355328)(4(1 34)16)(9#20(0 24))(6#20(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(0 8240)(9#17#62)(6#17#18)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#17#18#20(0 24))(7#17#18#22#7)(7#20(0 24)#22#7)(0 1048575)(5#70 1 4611686018427387904)(4 0(0 -2)(1 32))(2 0#72#5)(2 0#73(0 9))(5#74 0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_x_grow_xsrc_R1 363%positive "(437068((1 0)(1 49)#1(1 3)(1 4)(1 50)(1 51)(1 52)(1 11)(1 10)(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 34)#6#8#7(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#9#10#12#13#16#19#21#23#25#29#31#33#35#37#39#41#43#45#46#48#50#51#52#53#54#55#56#57#58#59#60#61#63#64#65#66#67#68#69)65(((1 2)-8304#18)((1 10)0(0 24))((1 34)0#7)((1 48)0#6))()#70)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_x_grow_xsrc_R1 23%positive "(((1 48)#6)((1 34)#7))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_x_grow_xsrc_R1 519%positive "((0(0(436872 437176 798592 718776 779340 778312 779720))(16 0(4#71(1 0))))(((779340((1(0 437084))(2#1)(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 11))(9(1 10))(10(1 48))(11(1 34))(12#8)(13(1 56))(14(1 57))(15(1 58))(16(1 59))(17(1 60))(18(1 34))(19#6)(20#8)(21#7)(22(1 48))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()(#71#75#9#10#12#13#16#19#21#23#25#29#31#33#35#37#39#41#43#45#46#48#50#51#52#53#54#55#56#57#58#59#60#61#63#64#65#66#67#68#69))(1 779340)))((0#75))())"%pstring.
