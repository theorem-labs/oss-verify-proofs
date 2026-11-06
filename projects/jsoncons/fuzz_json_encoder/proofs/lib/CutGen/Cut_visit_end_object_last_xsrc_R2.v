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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_end_object_last_xsrc_T Cut_visit_end_object_last_xsrc_R0 Cut_visit_end_object_last_xsrc_R1.
Definition dict_Cut_visit_end_object_last_xsrc_R2 : CCD.pt := CCD.mk_table 1231%positive "((0 1048575)(5#1 1 4611686018427387904)((1 10)272)(4 0(0 32)(1 33))(2 0#4(1 34))(2 0#5(0 -32))(0#3 8#6)(0 1048576)(5#8 1 4611686018427387904)(2 0(1 40)(0 -1))(5#10 0 0)(5(1 40)1 1)(2 1(1 40)(0 0))(2 4#13(0 1))(5#14 0 0)((1 10)288)(0#16 4(0 0))((1 10)400)(0#18 4(0 0))((1 2)-24)(0#20 8(1 9))((1 2)-16)(0#22 8(1 8))((1 2)-8)(0#24 8(1 1))((1 10)8)(0#26 8(1 32))((1 10)36)(0#28 1(0 4))(6#16(0 4))(6#18(0 4))(6#3(0 8))(5(1 37)0 18446744073709551615)((1 10)296)(6#34(0 8))((1 10)352)(0 83540)(0#36 8#37)((1 10)360)(0#39 8(0 1))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10576)(9#45#46)((1 2)-48)(9#48(0 24))(0 10624)(6#45#50)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#45#50#54(0 408))((1 32)0)(7#45#50#56(0 24))(7#54(0 408)#56(0 24))(3 65536 813152)((1 10)264)(0#60 8(1 34))(#5 -32)(0#62 4(1 38))(5(1 38)0 1)(#5 -28)(0#65 1(0 0))(#5 -27)(0#67 1(1 39))(#5 -26)(0#69 1(1 40))(5(1 40)0 1)(#5 -8)(0#72 8(1 36))(9#62(0 32))(4 0(0 -32)(1 33))(2 0#75(1 35))(5#76 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#45#50#82(1 35))(7#54(0 408)#82(1 35))(7#56(0 24)#82(1 35))(5(1 33)1 1)(2 0(1 80)(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_end_object_last_xsrc_R2 459%positive "(244904((1 0)(1 64)(2 0(1 2)(0 -48))(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)(1 9)(1 68)(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#2#7#9#11#12#15#17#19#21#23#25#27#29#30#31#32#33#35#38#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#68#70#71#73#74#77#78#79#80#81#83#84#85#86)80(((1 2)-10624#50)((1 10)272(0 8))((1 10)288(0 4))((1 10)296(0 8))((1 10)400(0 4)))()(0 1048574))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_end_object_last_xsrc_R2 17%positive "(((1 34)(1 35)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_end_object_last_xsrc_R2 541%positive "((0(0(244800 244964 421620 251692 763484 764892))(1 0))(((244964((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 8))(9(1 9))(10(0 1))(11#87)(12(1 80))(13(1 34))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()((0#34 8#87)#2#7#9#11#12#15#17#19#21#23#25#27#29#30#31#32#33#35#38#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#68#70#71#73#74#77#78#79#80#81#83#84#85#86))(1 244964)))()())"%pstring.
