(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_push_back_grow_xsrc_T_u5 Cut_str_push_back_grow_xsrc_R0_u5.
Definition dict_Cut_str_push_back_grow_xsrc_R1 : CCD.pt := CCD.mk_table 1066%positive "((4 0(0 4)(1 32))(2 0#1(0 -2))(2 6#2(0 3))(4 0(0 8)#3)(2 0#4(0 8))(4 0(0 2)(1 32))(2 0#6(0 -1))(5(1 52)4096 140737488355328)(4(1 52)16)((1 52)0)(9#10#5)(6#10#5)((0 0)65536)(0 974848)(7#10#5#13#14)((1 2)-8304)(0 8304)(7#10#5#16#17)((1 10)0)(7#10#5#19(0 24))((1 34)0)(7#10#5#21#6)(0 8224)(9#16#23)(0 1048576)(5#25 1 4611686018427387904)((1 2)-80)(0#27 8(1 11))((1 2)-72)(0 437068)(0#29 8#30)(2 0#6(0 1))(6 0 0 1#32)(2 9#33(0 1))(5#34 1 1)((1 2)-64)(0#36 8(1 22))((1 2)-56)(0#38 8(1 21))((1 2)-48)(0#40 8(1 20))((1 2)-40)(0#42 8(1 19))((1 2)-32)(0#44 8(1 18))((1 2)-24)(0#46 8(1 9))((1 2)-16)(0#48 8(1 8))((1 2)-8)(0#50 8(1 1))(0#19 8#32)((1 10)8)(0#53 8#7)((1 10)16)(0#55 8(1 34))(5(1 32)12 33554432)(5(1 11)0 255)(2#21#7 0)(9#21#6)(6#21#6)(5(1 34)4096 140737488355328)(4(1 34)16)(9#19(0 24))(6#19(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(9#27(0 0))(6#16#17)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#16#17#19(0 24))(7#16#17#21#6)(7#19(0 24)#21#6)(0 1048575)(5#75 1 4611686018427387904)(4 0(0 -2)(1 32))(2 0#77#4)(2 0#78(0 9))(5#79 0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_str_push_back_grow_xsrc_R1 382%positive "(798620((1 0)(1 48)(2 0(1 2)(0 -80))(1 3)(1 4)(1 49)(1 50)(1 51)#5(1 10)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 34)#5#7#6(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#8#9#11#12#15#18#20#22#24#26#28#31#35#37#39#41#43#45#47#49#51#52#54#56#57#58#59#60#61#62#63#64#65#66#67#68#69#70#71#72#73#74)64(((1 2)-8304#17)((1 10)0(0 24))((1 34)0#6)((1 52)0#5))()#75)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_str_push_back_grow_xsrc_R1 23%positive "(((1 52)#5)((1 34)#6))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_str_push_back_grow_xsrc_R1 542%positive "((0(0(436872 437176 719096 718776 779340 778312 779720))(16 0(4#76(1 0))))(((779340((1(0 437084))(2(2 0(1 2)(0 -64)))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 11))(9(1 10))(10(1 52))(11(1 34))(12#7)(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 34))(19#5)(20#7)(21#6)(22(1 52))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#76#80#8#9#11#12#15#18#20#22#24#26#28#31#35#37#39#41#43#45#47#49#51#52#54#56#57#58#59#60#61#62#63#64#65#66#67#68#69#70#71#72#73#74))(1 779340)))((0#80))())"%pstring.
