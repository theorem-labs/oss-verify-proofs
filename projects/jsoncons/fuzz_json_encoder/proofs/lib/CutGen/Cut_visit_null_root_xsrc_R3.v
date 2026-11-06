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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xsrc_T Cut_visit_null_root_xsrc_R0 Cut_visit_null_root_xsrc_R1 Cut_visit_null_root_xsrc_R2.
Definition dict_Cut_visit_null_root_xsrc_R3 : CCD.pt := CCD.mk_table 882%positive "((2 0(1 2)(0 -32))(0 69610)(0 1048574)(5#3 1 4611686018427387904)(5(1 69)4 4)((0 0)883688)(0#6 1(0 1))((0 0)883689)(0#8 1(0 1))((0 0)883672)(0#10 8#2)((0 0)883680)(0#12 8(0 4))(0 1048575)(5#14 1 4611686018427387904)(5(1 53)4 4)(0 1048576)(5#17 1 4611686018427387904)((1 2)-24)(0#19 8(1 9))((1 2)-16)(0#21 8(1 8))((1 2)-8)(0#23 8(1 1))((1 10)8)(0#25 8(1 32))((1 10)296)(0#27 8(1 37))(5(1 37)0 18446744073709551615)(6#27(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#35#36)((1 2)-32)(9#38(0 8))(0 10624)(6#35#40)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#35#40#44(0 408))((1 32)0)(7#35#40#46(0 24))(7#44(0 408)#46(0 24))(3 65536 813152)((1 10)264)(0#50 8(1 34))((1 10)272)(0#52 8(1 34))(7#35#40#10(0 18))(7#44(0 408)#10(0 18))(7#46(0 24)#10(0 18))(0 1048573)(5#57 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xsrc_R3 333%positive "(247148((1 0)(1 80)#1(1 3)(1 4)(1 81)(1 82)(1 83)(1 10)#2(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 92)(1 93)(1 94)(1 95))(#4#5#7#9#11#13#15#16#18#20#22#24#26#28#29#30#31#32#33#34#37#39#41#42#43#45#47#48#49#51#53#54#55#56)96(((1 2)-10624#40)((1 10)296(0 8)))()#57)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xsrc_R3 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xsrc_R3 533%positive "((0(0(247028 247208 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(4#58(1 0)))(((253336((1(0 247152))(2#1)(3(1 3))(4(1 4))(5(1 81))(6(1 82))(7(1 83))(8(1 10))(9#2)(10(1 84))(11(1 85))(12(1 86))(13(1 87))(14(1 88))(15(1 89))(16(1 90))(17(1 91))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 92))(29(1 93))(30(1 94))(31(1 95)))()(#58#4#5#7#9#11#13#15#16#18#20#22#24#26#28#29#30#31#32#33#34#37#39#41#42#43#45#47#48#49#51#53#54#55#56))(1 253336)))()())"%pstring.
