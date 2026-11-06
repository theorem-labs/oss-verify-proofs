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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_aa_grow1_xsrc_T Cut_vbm_aa_grow1_xsrc_R0 Cut_vbm_aa_grow1_xsrc_R1.
Definition dict_Cut_vbm_aa_grow1_xsrc_R2 : CCD.pt := CCD.mk_table 1214%positive "((2 0(1 48)(0 64))(2 0(1 35)(0 1))((1 48)0)(2#3(0 32)0)(9#3(0 32))(0 1048575)(5#6 1 4611686018427387904)((1 48)56)(0#8 8(0 0))((1 48)48)(0#10 8#2)((1 48)40)(0#12 8(1 35))((1 48)38)(0#14 1(0 0))((1 48)37)(0#16 1(0 0))((1 48)36)(0#18 1(0 0))((1 48)32)(0#20 4(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)(9#20(0 0))((1 48)39)(9#25(0 1))(6#3(0 64))((0 0)65536)(0 962560)(7#3(0 64)#28#29)((1 2)-8256)(0 8256)(7#3(0 64)#31#32)((1 8)0)(7#3(0 64)#34(0 264))((1 8)288)(7#3(0 64)#36(0 120))((1 8)264)(7#3(0 64)#38(0 24))((1 2)8)(7#3(0 64)#40(0 40))((1 32)0)(7#3(0 64)#42(0 32))(0 1048576)(5#44 1 4611686018427387904)((1 2)-16)(0#46 8(1 8))((1 2)-8)(0 246148)(0#48 8#49)((1 2)40)(2 0(1 8)(0 264))(0#51 8#52)((1 8)272)(2 0(1 32)(0 32))((1 8)280)(6#38(0 24))((1 8)296)(0#58 8(1 35))(5(1 35)0 18446744073709551615)((1 8)376)(0#61 8(0 1))((1 8)28)(0#63 1(0 0))((1 8)30)(0#65 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(0 8240)(9#31#69)(6#31#32)(6#40(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#31#75#34(0 408))(9#42(0 32))(6#42(0 32))(5(1 32)4096 140737488355328)(4(1 32)16)(7#31#75#42(0 32))(7#34(0 408)#42(0 32))(2#42(0 32)0)(5(0 32)0 4611686018427387904)(0 1048574)(5#85 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_aa_grow1_xsrc_R2 460%positive "(246456((1 0)(1 65)(1 2)(1 3)(1 4)(1 66)(1 67)(1 68)(1 8)(1 48)(1 48)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)#1#2#1(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 77)(1 78)(1 79)(1 80))(#4#5#7#9#11#13#15#17#19#21#22#23#24#26#27#30#33#35#37#39#41#43#45#47#50#53(0#38 8(1 32))(0#54 8#55)(0#56 8#55)#57#59#60#62#64#66#67#68#70#71(9#40(0 32))#72#73#74#76#77#78#79#80#81#82#83#84)81(((1 2)-8256#32)((1 2)8(0 40))((1 8)264(0 24))((1 32)0(0 32))((1 48)0(0 64)))()#85)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_aa_grow1_xsrc_R2 31%positive "(((1 48)(0 64))((1 32)(0 32)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_aa_grow1_xsrc_R2 636%positive "((0(0(245568 246500 783764 763484 704108 763484 764892))(4#86(1 0)))(((704108((1(0 246500))(2(1 2))(3(1 3))(4(1 4))(5(1 66))(6(1 67))(7(1 68))(8(1 8))(9(1 48))(10(1 32))(11(0 32))(12(1 32))(13(1 72))(14(1 73))(15(1 74))(16(1 75))(17(1 76))(18#1)(19#2)(20#1)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 77))(29(1 78))(30(1 79))(31(1 80)))()(#86(0((1 2)32)8#55)(0((1 2)24)8(1 32))(0((1 2)16)8(1 32))(0#40 8(1 32))(0#56 8#1)(0#54 8#1)(0#38 8(1 48))#4#5#7#9#11#13#15#17#19#21#22#23#24#26#27#30#33#35#37#39#41#43#45#47#50#53#57#59#60#62#64#66#67#68#70#71#72#73#74#76#77#78#79#80#81#82#83#84))(1 704108)))()())"%pstring.
