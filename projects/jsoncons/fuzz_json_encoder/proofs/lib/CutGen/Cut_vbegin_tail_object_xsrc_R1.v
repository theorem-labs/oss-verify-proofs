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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbegin_tail_object_xsrc_T Cut_vbegin_tail_object_xsrc_R0.
Definition dict_Cut_vbegin_tail_object_xsrc_R1 : CCD.pt := CCD.mk_table 711%positive "((0 1048576)(5#1 1 4611686018427387904)((1 8)288)(4 0(0 4)(1 33))(2 0#4(0 4))(0#3 4#5)((1 8)272)(0#7 8(1 18))((1 8)8)(0#9 8(1 32))((1 8)36)(0#11 1(0 4))(5(1 33)0 1023)(6#3(0 4))(6#7(0 8))((1 8)296)(5(1 34)0 18446744073709551615)(6#16(0 8))((1 8)336)(0 83539)(0#19 8#20)((1 8)344)(0#22 8(0 1))((1 2)88)(0#24 8(1 40))((1 2)80)(0#26 8(1 41))((1 2)72)(0#28 8(1 42))((1 2)64)(0#30 8(1 43))((1 2)56)(0#32 8(1 44))((1 2)48)(0#34 8(1 45))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-8496)(0 8496)(9#40#41)(6#40#41)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8592)((1 8)0)(7#40#46#47(0 408))((1 32)0)(7#40#46#49(0 24))(7#47(0 408)#49(0 24))(3 65536 813152))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbegin_tail_object_xsrc_R1 377%positive "(244680((1 0)(1 48)(1 2)(1 3)(1 4)(1 49)(1 50)(1 51)(1 8)(1 9)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#2#6#8#10#12#13#14#15(0#16 8(1 34))#17#18#21#23#25#27#29#31#33#35#36#37#38#39#42#43#44#45#48#50#51#52)64(((1 2)-8496#41)((1 8)272(0 8))((1 8)288(0 4))((1 8)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbegin_tail_object_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vbegin_tail_object_xsrc_R1 500%positive "((0(0(244644 244728 421620 763484 764892))(1 0))(((244728((1(1 40))(2(2 0(1 2)(0 96)))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 41))(9(1 42))(10(0 1))(11(0 1))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 43))(19(1 44))(20(1 45))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0#16 8(2 0(1 34)(0 1)))#2#6#8#10#12#13#14#15#17#18#21#23#25#27#29#31#33#35#36#37#38#39#42#43#44#45#48#50#51#52))(1 244728)))()())"%pstring.
