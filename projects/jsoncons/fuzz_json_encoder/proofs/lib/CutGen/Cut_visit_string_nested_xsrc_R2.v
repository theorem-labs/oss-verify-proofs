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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_string_nested_xsrc_T Cut_visit_string_nested_xsrc_R0 Cut_visit_string_nested_xsrc_R1.
Definition dict_Cut_visit_string_nested_xsrc_R2 : CCD.pt := CCD.mk_table 1202%positive "((4 0(0 32)(1 33))(2 0#1(1 34))(#2 -32)(0#3 4(1 38))(#2 -28)(0#5 1(0 0))(#2 -8)(6#7(0 8))(0 1048575)(5#9 1 4611686018427387904)(0 1048576)(5#11 1 4611686018427387904)(4 0(0 -1)(1 38))(2 0#13(0 2))(5#14 1 1)(5(1 38)1 1)(2 1(1 38)(0 1))(2 4#17(0 1))(5#18 1 1)((1 2)-48)(0#20 8(1 20))((1 2)-40)(0#22 8(1 19))((1 2)-32)(0#24 8(1 18))((1 2)-24)(0#26 8(1 9))((1 2)-16)(0#28 8(1 8))((1 2)-8)(0#30 8(1 1))((1 10)8)(0#32 8(1 32))(5(1 37)0 18446744073709551615)((1 10)296)(6#35(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10576)(9#41#42)(0 10624)(6#41#44)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#41#44#48(0 408))((1 32)0)(7#41#44#50(0 24))(7#48(0 408)#50(0 24))((1 10)264)(0#53 8(1 34))((1 10)272)(0#55 8#2)(5(1 38)0 1)(5(1 40)0 1)(5(1 33)1 1024)(4 0(0 -32)(1 33))(2 0#60(1 35))(5#61 0 32768)(5(1 35)32 32768)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 36)0 18446744073709551615)((1 34)0)(7#41#44#67(1 35))(7#48(0 408)#67(1 35))(7#50(0 24)#67(1 35))((1 11)0)(7#71(0 16)#67(1 35))(5(1 12)0 255)(5(1 11)1099511627776 140737488355328)(4(1 11)8)(7#41#44#71(0 16))(7#48(0 408)#71(0 16))(7#50(0 24)#71(0 16))(2 0(1 36)(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_string_nested_xsrc_R2 455%positive "(247584((1 0)(1 64)(2 0(1 2)(0 -48))(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)(1 14)(1 68)(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 13)(1 12)(1 11)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#4#6(0#7 8(1 36))#8(9#3(0 32))#10#12#15#16#19#21#23#25#27#29#31#33#34#36#37#38#39#40#43#45#46#47#49#51#52(3 65536 813152)#54#56#57#58#59#62#63#64#65#66#68#69#70#72#73#74#75#76#77#78)80(((1 2)-10624#44)((1 10)296(0 8))(#2 -8(0 8)))()(0 1048574))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_string_nested_xsrc_R2 17%positive "(((1 34)(1 35)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_string_nested_xsrc_R2 584%positive "((0(0(247440 247640 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(1 0))(((247640((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 8))(9(1 9))(10(0 1))(11#79)(12(1 70))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()((0#7 8#79)#4#6#8(9#3(0 24))#10#12#15#16#19#21#23#25#27#29#31#33#34#36#37#38#39#40#43#45#46#47#49#51#52#54#56#57#58#59#62#63#64#65#66#68#69#70#72#73#74#75#76#77#78))(1 247640)))()())"%pstring.
