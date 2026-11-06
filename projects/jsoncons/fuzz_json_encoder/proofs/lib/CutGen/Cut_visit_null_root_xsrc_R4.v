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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xsrc_T Cut_visit_null_root_xsrc_R0 Cut_visit_null_root_xsrc_R1 Cut_visit_null_root_xsrc_R2 Cut_visit_null_root_xsrc_R3.
Definition dict_Cut_visit_null_root_xsrc_R4 : CCD.pt := CCD.mk_table 878%positive "((0 69610)(5(1 101)4 4)((0 0)883688)(0#3 1(0 1))((0 0)883689)(0#5 1(0 1))((0 0)883672)(0#7 8#1)((0 0)883680)(0#9 8(0 4))(0 1048573)(5#11 1 4611686018427387904)(0 1048574)(5#13 1 4611686018427387904)(5(1 69)4 4)(0 1048575)(5#16 1 4611686018427387904)(5(1 53)4 4)(0 1048576)(5#19 1 4611686018427387904)((1 2)-24)(0#21 8(1 9))((1 2)-16)(0#23 8(1 8))((1 2)-8)(0#25 8(1 1))((1 10)8)(0#27 8(1 32))((1 10)296)(5(1 37)0 18446744073709551615)(6#29(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#36#37)((1 2)-32)(9#39(0 8))(0 10624)(6#36#41)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#36#41#45(0 408))((1 32)0)(7#36#41#47(0 24))(7#45(0 408)#47(0 24))(3 65536 813152)((1 10)264)(0#51 8(1 34))((1 10)272)(0#53 8(1 34))(7#36#41#7(0 18))(7#45(0 408)#7(0 18))(7#47(0 24)#7(0 18))(2 0(1 37)(1 101)))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xsrc_R4 381%positive "(247152((1 0)(1 96)(2 0(1 2)(0 -32))(1 3)(1 4)(1 97)(1 98)(1 99)(1 10)#1#1(1 101)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 108)(1 109)(1 110)(1 111))(#2#4#6#8#10#12#14#15#17#18#20#22#24#26#28(0#29 8(1 37))#30#31#32#33#34#35#38#40#42#43#44#46#48#49#50#52#54#55#56#57)112(((1 2)-10624#41)((1 10)296(0 8)))()(0 1048572))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xsrc_R4 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints3.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xsrc_R4 542%positive "((0(0(247028 247208 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892))(1 0))(((247208((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 97))(6(1 98))(7(1 99))(8(1 8))(9(1 9))(10(0 1))(11#58)(12(1 37))(13(1 34))(14(1 104))(15(1 105))(16(1 106))(17(1 107))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 108))(29(1 109))(30(1 110))(31(1 111)))()((0#29 8#58)#2#4#6#8#10#12#14#15#17#18#20#22#24#26#28#30#31#32#33#34#35#38#40#42#43#44#46#48#49#50#52#54#55#56#57))(1 247208)))()())"%pstring.
