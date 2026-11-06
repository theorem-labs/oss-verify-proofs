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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_bool_root_xsrc_T Cut_visit_bool_root_xsrc_R0 Cut_visit_bool_root_xsrc_R1.
Definition dict_Cut_visit_bool_root_xsrc_R2 : CCD.pt := CCD.mk_table 1611%positive "((2 0(1 2)(0 -32))(0 66317)(5(1 69)5 5)((0 0)883736)(0#4 1(0 1))((0 0)883737)(0#6 1(0 1))((0 0)883720)(0#8 8#2)((0 0)883728)(0#10 8(0 5))(0 1048575)(5#12 1 4611686018427387904)(5(1 53)5 5)(0 1048576)(5#15 1 4611686018427387904)(4 0(0 -1)(1 11))(2 0#17(0 1))(5#18 1 1)(5(1 11)0 0)(2 1(1 11)(0 0))(2 4#21(0 1))(5#22 1 1)((1 2)-24)(0#24 8(1 9))((1 2)-16)(0#26 8(1 8))((1 2)-8)(0#28 8(1 1))((1 10)8)(0#30 8(1 32))((1 10)296)(0#32 8(1 37))(5(1 37)0 18446744073709551615)(6#32(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#40#41)((1 2)-32)(9#43(0 8))(0 10624)(6#40#45)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#40#45#49(0 408))((1 32)0)(7#40#45#51(0 24))(7#49(0 408)#51(0 24))(3 65536 813152)((1 10)264)(0#55 8(1 34))((1 10)272)(0#57 8(1 34))(5(1 11)0 1)((0 0)883696)(7#40#45#60(0 18))(7#49(0 408)#60(0 18))(7#51(0 24)#60(0 18))(7#40#45#8(0 18))(7#49(0 408)#8(0 18))(7#51(0 24)#8(0 18))((1 2)-10624#45)((1 10)296(0 8))(#67#68)(0 1048574)(247212 247436 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#71)(5#70 1 4611686018427387904)(4#73(1 0))(0#72#74)(2#1)(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 10))(10(1 32))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79))(1 421620)(0 72237)(5(1 69)4 4)((0 0)883712)(0#106 1(0 1))((0 0)883713)(0#108 1(0 1))(0#60 8#104)((0 0)883704)(0#111 8(0 4))(5(1 53)4 4)(2 0(1 11)(0 -1))(5#114 0 0)(5(1 11)1 1)(5#22 0 0))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R2 316%positive "(247360((1 0)(1 64)#1(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)#2#2(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#3#5#7#9#11#13#14#16#19#20#23#25#27#29#31#33#34#35#36#37#38#39#42#44#46#47#48#50#52#53#54#56#58#59#61#62#63#64#65#66)80#69()#70)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R2 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R2 268%positive "(#75(((421620((1(0 247376))#76#77#78#79#80#81#82(9#2)#83(11#2)(12(0 5))#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102)()(#73#3#5#7#9#11#13#14#16#19#20#23#25#27#29#31#33#34#35#36#37#38#39#42#44#46#47#48#50#52#53#54#56#58#59#61#62#63#64#65#66))#103))()())"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R2 333%positive "(247324((1 0)(1 64)#1(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)#104#104(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#105#107#109#110#112#13#113#16#115#116#117#25#27#29#31#33#34#35#36#37#38#39#42#44#46#47#48#50#52#53#54#56#58#59#61#62#63#64#65#66)80#69()#70)"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R2 285%positive "(#75(((421620((1(0 247340))#76#77#78#79#80#81#82(9#104)#83(11#104)(12(0 4))#84#85#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102)()(#73#105#107#109#110#112#13#113#16#115#116#117#25#27#29#31#33#34#35#36#37#38#39#42#44#46#47#48#50#52#53#54#56#58#59#61#62#63#64#65#66))#103))()())"%pstring.
