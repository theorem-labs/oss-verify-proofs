(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_conv_ec_c1_csrc_T_u Cut_conv_ec_c1_csrc_R0_u Cut_conv_ec_c1_csrc_R1_u.
Definition dict_Cut_conv_ec_c1_csrc_R2 : CCD.pt := CCD.mk_table 836%positive "((2 0(1 2)(0 -32))((0 0)1009736)(0#2 1(0 0))((0 0)1009740)(0#4 4(0 0))((0 0)1009744)(0#6 4(0 3))((0 0)1009752)(0 1009760)(0#8 8#9)((0 0)1009760)(0#11 8(0 0))((0 0)1009768)(0 684300)(0#13 8#14)((0 0)1010024)(0 235124)(0#16 8#17)((0 0)1009776)(0 406532)(0#19 8#20)((0 0)1010032)(0 805544)(0#22 8#23)((0 0)1009784)(0#25 8#20)((0 0)1010040)(0 805536)(0#27 8#28)(5(0 9)1 4611686018427387904)((0 0)871920)(0#31 1(0 0))((0 0)871921)(0#33 1(0 2))(5(0 10)1 4611686018427387904)((1 2)-24)(0#36 8(1 9))((1 2)-16)(0#38 8(1 8))((1 2)-8)(0#40 8(1 1))(6#31(0 2))(6#2(0 544))((1 10)0)(9#44(0 16))(6#44(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)((1 2)-256)(9#49(0 232))(6#49(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 801400)(7#49(0 256)#44(0 16))((0 0)65536)(0 950272)(7#44(0 16)#56#57)(5(0 8)1 4611686018427387904))"%pstring.

Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_conv_ec_c1_csrc_R2 370%positive "(239060((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(0 0)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#5#7#10#12#15#18#21#24#26#29#30#32#34#35#37#39#41#42#43#45#46#47#48#50#51#52#53#54#55#58)64(((1 2)-256(0 256))((1 10)0(0 16))((0 0)871920(0 2))((0 0)1009736(0 544)))()(0 8))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_conv_ec_c1_csrc_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_conv_ec_c1_csrc_R2 498%positive "((0(0(238924 239008 283488 283568 683904 751764 753172))(4#59(1 0)))(((283568((1(0 239072))(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 10))(9(1 11))(10(0 871920))(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#59#3#5#7#10#12#15#18#21#24#26#29#30#32#34#35#37#39#41#42#43#45#46#47#48#50#51#52#53#54#55#58))(1 283568)))()())"%pstring.
