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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_aa_grow2_xsrc_T Cut_vbm_aa_grow2_xsrc_R0 Cut_vbm_aa_grow2_xsrc_R1 Cut_vbm_aa_grow2_xsrc_R2.
Definition dict_Cut_vbm_aa_grow2_xsrc_R3 : CCD.pt := CCD.mk_table 1580%positive "((4 0(0 32)(1 33))(2 0#1(1 48))(2 0#2(0 32))(2 0(1 35)(0 1))(2 7#1(0 4))(4 0(0 32)#5)(2 0(1 48)#6)((1 2)-8224)(0 8224)(9#8#9)(0 1048574)(5#11 1 4611686018427387904)((1 2)32)(2 0(1 32)#1)(0#13 8#14)((1 2)24)(0#16 8(1 32))((1 2)16)(0#18 8(1 32))((1 2)8)(0#20 8(1 32))((1 8)280)(0#22 8#7)((1 8)272)(0#24 8#3)((1 8)264)(0#26 8(1 48))((1 48)0)(2#28#1 0)(9#28#1)(0 1048575)(5#31 1 4611686018427387904)(#2 24)(0#33 8(0 0))(#2 16)(0#35 8#4)(#2 8)(0#37 8(1 35))(#2 6)(0#39 1(0 0))(#2 5)(0#41 1(0 0))(#2 4)(0#43 1(0 0))(#2 0)(0#45 4(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)(9#45(0 0))(#2 7)(9#50(0 1))(#2 32)(4 0(0 -32)(1 33))(2 0#53#6)(2 0#54(0 -32))(9#52#55)(6#28#6)((0 0)65536)(0 962560)(7#28#6#58#59)((1 2)-8256)(0 8256)(7#28#6#61#62)((1 8)0)(7#28#6#64(0 264))((1 8)288)(7#28#6#66(0 120))(7#28#6#26(0 24))(7#28#6#20(0 40))((1 32)0)(7#28#6#70#1)(0 1048576)(5#72 1 4611686018427387904)((1 2)40)(2 0(1 8)(0 264))(0#74 8#75)(6#26(0 24))((1 8)296)(0#78 8(1 35))(5(1 35)0 18446744073709551615)((1 8)376)(0#81 8(0 1))((1 8)28)(0#83 1(0 0))((1 8)30)(0#85 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(9#61(0 32))(6#61#62)(6#20(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#61#94#64(0 408))(5(1 33)2 512)(2 7#1(0 5))(2 1#5#97)(5#98 2 512)(2 1#5(1 33))(5#100 2 512)(5(1 32)4096 140737488355328)(4(1 32)16)(7#61#94#70#1)(7#64(0 408)#70#1)(5#54 0 4611686018427387904)(0 8240)(9#61#107)(#10#12#15#17#19#21#23#25#27#29#30#32#34#36#38#40#42#44#46#47#48#49#51#56#57#60#63#65#67#68#69#71#73#76#77#79#80#82#84#86#87#88#89#90#91#92#93#95#96#99#101#102#103#104#105#106#108))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_aa_grow2_xsrc_R3 264%positive "(246500((1 0)(1 81)(1 2)(1 3)(1 4)(1 82)(1 83)(1 84)(1 8)(1 48)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)(1 92)#3#4#7(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 93)(1 94)(1 95)(1 96))#109 97(((1 2)-8256#62)((1 2)8(0 40))((1 8)264(0 24))((1 48)0#6))()(0 1048573))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_aa_grow2_xsrc_R3 13%positive "(((1 48)#6))"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_aa_grow2_xsrc_R3 327%positive "((1 0)(((246500((1(1 81))(2(1 2))(3(1 3))(4(1 4))(5(1 82))(6(1 83))(7(1 84))(8(1 8))(9(1 48))(10(1 85))(11(1 86))(12(1 87))(13(1 88))(14(1 89))(15(1 90))(16(1 91))(17(1 92))(18#3)(19#4)(20#7)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 93))(29(1 94))(30(1 95))(31(1 96)))()#109)(1 246500)))()())"%pstring.
