(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_set_ec_ls1_xsrc_T_u5 Cut_set_ec_ls1_xsrc_R0_u5 Cut_set_ec_ls1_xsrc_R1_u5.
Definition dict_Cut_set_ec_ls1_xsrc_R2 : CCD.pt := CCD.mk_table 776%positive "((2 0(1 2)(0 -32))((0 0)1036376)(0#2 1(0 0))((0 0)1036380)(0#4 4(0 0))((0 0)1036384)(0#6 4(0 2))((0 0)1036392)(0 1036400)(0#8 8#9)((0 0)1036400)(0#11 8(0 0))((0 0)1036408)(0 710848)(0#13 8#14)((0 0)1036664)(0 239000)(0#16 8#17)((0 0)1036416)(0 433132)(0#19 8#20)((0 0)1036672)(0 832120)(0#22 8#23)(5(0 9)1 4611686018427387904)((0 0)898496)(0#26 1(0 0))((0 0)898497)(0#28 1(0 2))(5(0 10)1 4611686018427387904)((1 2)-24)(0#31 8(1 9))((1 2)-16)(0#33 8(1 8))((1 2)-8)(0#35 8(1 1))(6#26(0 2))(6#2(0 544))((1 10)0)(9#39(0 16))(6#39(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)((1 2)-256)(9#44(0 232))(6#44(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 827984)(7#44(0 256)#39(0 16))((0 0)65536)(0 974848)(7#39(0 16)#51#52)(5(0 8)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_set_ec_ls1_xsrc_R2 364%positive "(285084((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(0 0)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#5#7#10#12#15#18#21#24#25#27#29#30#32#34#36#37#38#40#41#42#43#45#46#47#48#49#50#53)64(((1 2)-256(0 256))((1 10)0(0 16))((0 0)898496(0 2))((0 0)1036376(0 544)))()(0 8))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_set_ec_ls1_xsrc_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec_ls1_xsrc_R2 492%positive "((0(0(284948 285032 310088 310168 710452 778312 779720))(4#54(1 0)))(((310168((1(0 285096))(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 10))(9(1 11))(10(0 898496))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#54#3#5#7#10#12#15#18#21#24#25#27#29#30#32#34#36#37#38#40#41#42#43#45#46#47#48#49#50#53))(1 310168)))()())"%pstring.
