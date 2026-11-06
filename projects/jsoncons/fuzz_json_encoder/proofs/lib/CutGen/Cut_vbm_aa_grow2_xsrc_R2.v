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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_aa_grow2_xsrc_T Cut_vbm_aa_grow2_xsrc_R0 Cut_vbm_aa_grow2_xsrc_R1.
Definition dict_Cut_vbm_aa_grow2_xsrc_R2 : CCD.pt := CCD.mk_table 1315%positive "((4 0(0 32)(1 33))(2 0#1(1 48))(2 0#2(0 32))(2 0(1 35)(0 1))(2 7#1(0 4))(4 0(0 32)#5)(2 0(1 48)#6)((1 48)0)(2#8#1 0)(9#8#1)(0 1048575)(5#11 1 4611686018427387904)(#2 24)(0#13 8(0 0))(#2 16)(0#15 8#4)(#2 8)(0#17 8(1 35))(#2 6)(0#19 1(0 0))(#2 5)(0#21 1(0 0))(#2 4)(0#23 1(0 0))(#2 0)(0#25 4(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)(9#25(0 0))(#2 7)(9#30(0 1))(#2 32)(4 0(0 -32)(1 33))(2 0#33#6)(2 0#34(0 -32))(9#32#35)(6#8#6)((0 0)65536)(0 962560)(7#8#6#38#39)((1 2)-8256)(0 8256)(7#8#6#41#42)((1 8)0)(7#8#6#44(0 264))((1 8)288)(7#8#6#46(0 120))((1 8)264)(7#8#6#48(0 24))((1 2)8)(7#8#6#50(0 40))((1 32)0)(7#8#6#52#1)(0 1048576)(5#54 1 4611686018427387904)((1 2)-16)(0#56 8(1 8))((1 2)-8)(0 246148)(0#58 8#59)((1 2)40)(2 0(1 8)(0 264))(0#61 8#62)((1 8)272)(2 0(1 32)#1)((1 8)280)(6#48(0 24))((1 8)296)(0#68 8(1 35))(5(1 35)0 18446744073709551615)((1 8)376)(0#71 8(0 1))((1 8)28)(0#73 1(0 0))((1 8)30)(0#75 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(0 8240)(9#41#79)(6#41#42)(6#50(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#41#85#44(0 408))(5(1 33)2 512)(2 7#1(0 5))(2 1#5#88)(5#89 2 512)(2 1#5(1 33))(5#91 2 512)(9#52#1)(6#52#1)(5(1 32)4096 140737488355328)(4(1 32)16)(7#41#85#52#1)(7#44(0 408)#52#1)(2#52#1 0)(5#34 0 4611686018427387904)(0 1048574)(5#101 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_aa_grow2_xsrc_R2 469%positive "(246456((1 0)(1 65)(1 2)(1 3)(1 4)(1 66)(1 67)(1 68)(1 8)(1 48)(1 48)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)#3#4#7(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 77)(1 78)(1 79)(1 80))(#9#10#12#14#16#18#20#22#24#26#27#28#29#31#36#37#40#43#45#47#49#51#53#55#57#60#63(0#48 8(1 32))(0#64 8#65)(0#66 8#65)#67#69#70#72#74#76#77#78#80#81(9#50(0 32))#82#83#84#86#87#90#92#93#94#95#96#97#98#99#100)81(((1 2)-8256#42)((1 2)8(0 40))((1 8)264(0 24))((1 32)0#1)((1 48)0#6))()#101)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_aa_grow2_xsrc_R2 23%positive "(((1 48)#6)((1 32)#1))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_aa_grow2_xsrc_R2 650%positive "((0(0(245568 246500 783764 763484 704108 763484 764892))(4#102(1 0)))(((704108((1(0 246500))(2(1 2))(3(1 3))(4(1 4))(5(1 66))(6(1 67))(7(1 68))(8(1 8))(9(1 48))(10(1 32))(11#1)(12(1 32))(13(1 72))(14(1 73))(15(1 74))(16(1 75))(17(1 76))(18#3)(19#4)(20#7)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 77))(29(1 78))(30(1 79))(31(1 80)))()(#102(0((1 2)32)8#65)(0((1 2)24)8(1 32))(0((1 2)16)8(1 32))(0#50 8(1 32))(0#66 8#7)(0#64 8#3)(0#48 8(1 48))#9#10#12#14#16#18#20#22#24#26#27#28#29#31#36#37#40#43#45#47#49#51#53#55#57#60#63#67#69#70#72#74#76#77#78#80#81#82#83#84#86#87#90#92#93#94#95#96#97#98#99#100))(1 704108)))()())"%pstring.
