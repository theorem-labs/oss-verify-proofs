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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_ao_grow1_xsrc_T Cut_vbm_ao_grow1_xsrc_R0.
Definition dict_Cut_vbm_ao_grow1_xsrc_R1 : CCD.pt := CCD.mk_table 1008%positive "((2 0(1 8)(0 264))(2 0(1 35)(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)0)(6#5(0 64))((0 0)65536)(0 962560)(7#5(0 64)#7#8)((1 2)-8256)(0 8256)(7#5(0 64)#10#11)((1 8)0)(7#5(0 64)#13(0 264))((1 8)288)(7#5(0 64)#15(0 120))((1 8)264)(7#5(0 64)#17(0 24))((1 2)8)(7#5(0 64)#19(0 40))((1 32)0)(7#5(0 64)#21(0 32))(0 1048576)(5#23 1 4611686018427387904)((1 2)-16)(0#25 8(1 8))((1 2)-8)(0 246380)(0#27 8#28)((1 2)40)(0#30 8#1)(0#17 8(1 32))((1 8)272)(2 0(1 32)(0 32))(0#33 8#34)((1 8)280)(0#36 8#34)(6#17(0 24))((1 8)296)(0#39 8(1 35))(5(1 35)0 18446744073709551615)((1 8)376)(0#42 8(0 1))((1 8)28)(0#44 1(0 0))((1 8)30)(0#46 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(0 8240)(9#10#50)(6#10#11)(9#19(0 32))(6#19(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#10#57#13(0 408))(9#21(0 32))(6#21(0 32))(5(1 32)4096 140737488355328)(4(1 32)16)(7#10#57#21(0 32))(7#13(0 408)#21(0 32))(2#21(0 32)0)(0 1048575)(5#66 1 4611686018427387904)(2 0(1 48)(0 64))(5(0 32)0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_ao_grow1_xsrc_R1 411%positive "(274376((1 0)(1 49)(2 0(1 2)(0 -16))(1 3)(1 4)(1 50)(1 51)(1 52)(0 2)#1(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)#2(0 0)(0 32)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#3#4(9#5(0 64))#6#9#12#14#16#18#20#22#24#26#29#31#32#35#37#38#40#41#43#45#47#48#49#51#52#53#54#55#56#58#59#60#61#62#63#64#65)65(((1 2)-8256#11)((1 2)8(0 40))((1 8)264(0 24))((1 32)0(0 32))((1 48)0(0 64)))()#66)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_ao_grow1_xsrc_R1 31%positive "(((1 48)(0 64))((1 32)(0 32)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_ao_grow1_xsrc_R1 684%positive "((0(0(245392 246500 783764 763484 704108 763484 764892))(16 0(4#67(1 0))))(((763484((1(0 246456))(2(1 2))(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 48))(10(1 48))(11(1 32))(12(0 32))(13#34)(14(1 35))(15(1 58))(16(1 59))(17(1 60))(18#68)(19(0 0))(20#68)(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()(#67#69(0((1 48)56)8(0 0))(0((1 48)48)8#2)(0((1 48)40)8(1 35))(0((1 48)38)1(0 0))(0((1 48)37)1(0 1))(0((1 48)36)1(0 0))(0((1 48)32)4(0 1))#3#4(9#5(0 32))(9((1 48)39)(0 1))#6#9#12#14#16#18#20#22#24#26#29#31#32#35#37#38#40#41#43#45#47#48#49#51#52#53#54#55#56#58#59#60#61#62#63#64#65))(1 763484)))((0#69))())"%pstring.
