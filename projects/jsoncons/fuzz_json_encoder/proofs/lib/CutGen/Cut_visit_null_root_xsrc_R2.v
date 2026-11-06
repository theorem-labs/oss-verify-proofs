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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xsrc_T Cut_visit_null_root_xsrc_R0 Cut_visit_null_root_xsrc_R1.
Definition dict_Cut_visit_null_root_xsrc_R2 : CCD.pt := CCD.mk_table 840%positive "((2 0(1 2)(0 -32))(0 69610)(5(1 69)4 4)((0 0)883688)(0#4 1(0 1))((0 0)883689)(0#6 1(0 1))((0 0)883672)(0#8 8#2)((0 0)883680)(0#10 8(0 4))(0 1048575)(5#12 1 4611686018427387904)(5(1 53)4 4)(0 1048576)(5#15 1 4611686018427387904)((1 2)-24)(0#17 8(1 9))((1 2)-16)(0#19 8(1 8))((1 2)-8)(0#21 8(1 1))((1 10)8)(0#23 8(1 32))((1 10)296)(0#25 8(1 37))(5(1 37)0 18446744073709551615)(6#25(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#33#34)((1 2)-32)(9#36(0 8))(0 10624)(6#33#38)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#33#38#42(0 408))((1 32)0)(7#33#38#44(0 24))(7#42(0 408)#44(0 24))(3 65536 813152)((1 10)264)(0#48 8(1 34))((1 10)272)(0#50 8(1 34))(7#33#38#8(0 18))(7#42(0 408)#8(0 18))(7#44(0 24)#8(0 18))(0 1048574)(5#55 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xsrc_R2 326%positive "(247132((1 0)(1 64)#1(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)#2#2(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#3#5#7#9#11#13#14#16#18#20#22#24#26#27#28#29#30#31#32#35#37#39#40#41#43#45#46#47#49#51#52#53#54)80(((1 2)-10624#38)((1 10)296(0 8)))()#55)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xsrc_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xsrc_R2 525%positive "((0(0(247028 247208 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(4#56(1 0)))(((421620((1(0 247148))(2#1)(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8(1 10))(9#2)(10(1 32))(11#2)(12(0 4))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()(#56#3#5#7#9#11#13#14#16#18#20#22#24#26#27#28#29#30#31#32#35#37#39#40#41#43#45#46#47#49#51#52#53#54))(1 421620)))()())"%pstring.
