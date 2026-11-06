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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_aa_grow1_xsrc_T Cut_vbm_aa_grow1_xsrc_R0 Cut_vbm_aa_grow1_xsrc_R1 Cut_vbm_aa_grow1_xsrc_R2.
Definition dict_Cut_vbm_aa_grow1_xsrc_R3 : CCD.pt := CCD.mk_table 1445%positive "((2 0(1 48)(0 64))(2 0(1 35)(0 1))((1 2)-8224)(0 8224)(9#3#4)(0 1048574)(5#6 1 4611686018427387904)((1 2)32)(2 0(1 32)(0 32))(0#8 8#9)((1 2)24)(0#11 8(1 32))((1 2)16)(0#13 8(1 32))((1 2)8)(0#15 8(1 32))((1 8)280)(0#17 8#1)((1 8)272)(0#19 8#1)((1 8)264)(0#21 8(1 48))((1 48)0)(2#23(0 32)0)(9#23(0 32))(0 1048575)(5#26 1 4611686018427387904)((1 48)56)(0#28 8(0 0))((1 48)48)(0#30 8#2)((1 48)40)(0#32 8(1 35))((1 48)38)(0#34 1(0 0))((1 48)37)(0#36 1(0 0))((1 48)36)(0#38 1(0 0))((1 48)32)(0#40 4(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)(9#40(0 0))((1 48)39)(9#45(0 1))(6#23(0 64))((0 0)65536)(0 962560)(7#23(0 64)#48#49)((1 2)-8256)(0 8256)(7#23(0 64)#51#52)((1 8)0)(7#23(0 64)#54(0 264))((1 8)288)(7#23(0 64)#56(0 120))(7#23(0 64)#21(0 24))(7#23(0 64)#15(0 40))((1 32)0)(7#23(0 64)#60(0 32))(0 1048576)(5#62 1 4611686018427387904)((1 2)40)(2 0(1 8)(0 264))(0#64 8#65)(6#21(0 24))((1 8)296)(0#68 8(1 35))(5(1 35)0 18446744073709551615)((1 8)376)(0#71 8(0 1))((1 8)28)(0#73 1(0 0))((1 8)30)(0#75 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(9#51(0 32))(6#51#52)(6#15(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#51#84#54(0 408))(5(1 32)4096 140737488355328)(4(1 32)16)(7#51#84#60(0 32))(7#54(0 408)#60(0 32))(5(0 32)0 4611686018427387904)(0 8240)(9#51#91)(#5#7#10#12#14#16#18#20#22#24#25#27#29#31#33#35#37#39#41#42#43#44#46#47#50#53#55#57#58#59#61#63#66#67#69#70#72#74#76#77#78#79#80#81#82#83#85#86#87#88#89#90#92))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_aa_grow1_xsrc_R3 267%positive "(246500((1 0)(1 81)(1 2)(1 3)(1 4)(1 82)(1 83)(1 84)(1 8)(1 48)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)#1#2#1(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 93)(1 94)(1 95)(1 96))#93 97(((1 2)-8256#52)((1 2)8(0 40))((1 8)264(0 24))((1 48)0(0 64)))()(0 1048573))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_aa_grow1_xsrc_R3 17%positive "(((1 48)(0 64)))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_aa_grow1_xsrc_R3 326%positive "((1 0)(((246500((1(1 81))(2(1 2))(3(1 3))(4(1 4))(5(1 82))(6(1 83))(7(1 84))(8(1 8))(9(1 48))(10(1 85))(11(1 86))(12(1 87))(13(1 88))(14(1 89))(15(1 90))(16(1 91))(17(1 92))(18#1)(19#2)(20#1)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 93))(29(1 94))(30(1 95))(31(1 96)))()#93)(1 246500)))()())"%pstring.
