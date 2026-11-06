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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_uint64_nested_xsrc_T Cut_visit_uint64_nested_xsrc_R0 Cut_visit_uint64_nested_xsrc_R1.
Definition dict_Cut_visit_uint64_nested_xsrc_R2 : CCD.pt := CCD.mk_table 1031%positive "((5(1 64)0 1125899906842624)(0 1048575)(5#2 1 4611686018427387904)(4 0(0 32)(1 33))(2 0#4(1 34))(#5 -32)(0#6 4(1 38))(#5 -28)(0#8 1(0 0))(#5 -26)(0#10 1(0 1))(#5 -8)(6#12(0 8))(0 1048576)(5#14 1 4611686018427387904)(4 0(0 -1)(1 38))(2 0#16(0 2))(5#17 1 1)(5(1 38)1 1)(2 1(1 38)(0 1))(2 4#20(0 1))(5#21 1 1)((1 2)-24)(0#23 8(1 9))((1 2)-16)(0#25 8(1 8))((1 2)-8)(0#27 8(1 1))((1 10)8)(0#29 8(1 32))(5(1 37)0 18446744073709551615)((1 10)296)(6#32(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#38#39)((1 2)-32)(9#41(0 8))(0 10624)(6#38#43)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#38#43#47(0 408))((1 32)0)(7#38#43#49(0 24))(7#47(0 408)#49(0 24))((1 10)264)(0#52 8(1 34))((1 10)272)(0#54 8#5)(5(1 38)0 1)(5(1 40)0 1)(5(1 33)1 1024)(4 0(0 -32)(1 33))(2 0#59(1 35))(5#60 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#38#43#66(1 35))(7#47(0 408)#66(1 35))(7#49(0 24)#66(1 35)))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_uint64_nested_xsrc_R2 434%positive "(242320((1 0)(1 65)(2 0(1 2)(0 -32))(1 3)(1 4)(1 66)(1 67)(1 68)(1 10)(1 11)(1 64)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 77)(1 78)(1 79)(1 80))(#1#3#7#9#11(0#12 8(1 36))#13(9#6(0 32))#15#18#19#22#24#26#28#30#31#33#34#35#36#37#40#42#44#45#46#48#50#51(3 65536 813152)#53#55#56#57#58#61#62#63#64#65#67#68#69)81(((1 2)-10624#43)((1 10)296(0 8))(#5 -8(0 8)))()(0 1048574))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_uint64_nested_xsrc_R2 17%positive "(((1 34)(1 35)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_uint64_nested_xsrc_R2 600%positive "((0(0(242212 242376 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(1 0))(((242376((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 66))(6(1 67))(7(1 68))(8(1 8))(9(1 9))(10(0 1))(11#5)(12(1 81))(13(1 34))(14(1 73))(15(1 74))(16(1 75))(17(1 76))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 77))(29(1 78))(30(1 79))(31(1 80)))()((0#12 8(2 0(1 36)(0 1)))(0#32 8(2 0(1 64)(1 81)))#1#3#7#9#11#13(9#6(0 24))#15#18#19#22#24#26#28#30#31#33#34#35#36#37#40#42#44#45#46#48#50#51#53#55#56#57#58#61#62#63#64#65#67#68#69))(1 242376)))()())"%pstring.
