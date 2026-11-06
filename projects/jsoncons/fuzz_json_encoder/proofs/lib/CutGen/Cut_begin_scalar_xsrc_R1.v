(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_begin_scalar_xsrc_T Cut_begin_scalar_xsrc_R0.
Definition dict_Cut_begin_scalar_xsrc_R1 : CCD.pt := CCD.mk_table 1053%positive "((0 1048576)(5#1 1 4611686018427387904)(2 0(1 36)(0 -1))(5#3 0 18446744073709551614)(5(1 36)1 18446744073709551615)(2 1(1 36)(0 0))(2 4#6(0 1))(5#7 0 0)((1 2)-16)(0#9 8(1 8))((1 2)-8)(0#11 8(1 1))((1 10)8)(0#13 8(1 32))((1 10)264)(0#15 8(1 34))((1 10)272)(4 0(0 32)(1 33))(2 0#18(1 34))(0#17 8#19)((1 10)296)((1 10)320)(0 83527)(0#22 8#23)((1 10)328)(0#25 8(0 2))(#19 -32)(0#27 4(1 38))(#19 -28)(0#29 1(0 0))(#19 -27)(0#31 1(1 39))(#19 -8)(0#33 8(1 36))(#19 -26)(5(1 40)0 1)(6#35(0 1))(5(1 33)1 1024)(4 0(0 -32)(1 33))(2 0#39(1 35))(5#40 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)(5(1 37)0 18446744073709551615)(6#21(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-8592)(0 8576)(9#52#53)(0 8592)(6#52#55)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#52#55#59(0 408))((1 32)0)(7#52#55#61(0 24))(7#59(0 408)#61(0 24))((1 34)0)(7#52#55#64(1 35))(7#59(0 408)#64(1 35))(7#61(0 24)#64(1 35))(0 1048575)(5#68 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_begin_scalar_xsrc_R1 407%positive "(252176((1 0)(1 48)(2 0(1 2)(0 -16))(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 9)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#2#4#5#8#10#12#14#16#20(0#21 8(1 37))#24#26#28#30#32#34(0#35 1(1 40))#36#37#38#41#42#43#44#45#46#47#48#49#50#51#54#56#57#58#60#62#63#65#66#67)64(((1 2)-8592#55)((1 10)296(0 8))(#19 -26(0 1)))()#68)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_begin_scalar_xsrc_R1 17%positive "(((1 34)(1 35)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_begin_scalar_xsrc_R1 541%positive "((0(0(252124 252264 421620 251692 763484 764892))(4#69(1 0)))(((251692((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(1 10))(11(0 1))(12(0 2))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#69(0#35 1(0 1))(0#21 8(2 0(1 37)(0 2)))#2#4#5#8#10#12#14#16#20#24#26#28#30#32#34#36#37#38#41#42#43#44#45#46#47#48#49#50#51#54#56#57#58#60#62#63#65#66#67))(1 251692)))()())"%pstring.
