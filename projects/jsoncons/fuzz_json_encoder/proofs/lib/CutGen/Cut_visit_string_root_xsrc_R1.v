(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums EncSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_string_root_xsrc_T Cut_visit_string_root_xsrc_R0.
Definition dict_Cut_visit_string_root_xsrc_R1 : CCD.pt := CCD.mk_table 808%positive "((0 1048576)(5#1 1 4611686018427387904)((1 2)-48)(0#3 8(1 20))((1 2)-40)(0#5 8(1 19))((1 2)-32)(0#7 8(1 18))((1 2)-24)(0#9 8(1 9))((1 2)-16)(0#11 8(1 8))((1 2)-8)(0#13 8(1 1))((1 10)8)(0#15 8(1 32))(5(1 37)0 18446744073709551615)((1 10)296)(6#18(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10576)(9#24#25)(0 10624)(6#24#27)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#24#27#31(0 408))((1 32)0)(7#24#27#33(0 24))(7#31(0 408)#33(0 24))(3 65536 813152)((1 10)264)(0#37 8(1 34))((1 10)272)(0#39 8(1 34))(5(1 12)0 255)(5(1 11)1099511627776 140737488355328)(4(1 11)8)((1 11)0)(7#24#27#44(0 16))(7#31(0 408)#44(0 16))(7#33(0 24)#44(0 16))(#2#4#6#8#10#12#14#16#17#19#20#21#22#23#26#28#29#30#32#34#35#36#38#40#41#42#43#45#46#47))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_string_root_xsrc_R1 264%positive "(247584((1 0)(1 48)(2 0(1 2)(0 -48))(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 14)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 13)(1 12)(1 11)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))#48 64(((1 2)-10624#27)((1 10)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_string_root_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_string_root_xsrc_R1 426%positive "((0(0(247440 247640 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(1 0))(((247640((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(0 1))(11(1 34))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()#48)(1 247640)))()())"%pstring.
