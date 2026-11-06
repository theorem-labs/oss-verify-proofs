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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_or_grow0_xsrc_T Cut_vbm_or_grow0_xsrc_R0.
Definition dict_Cut_vbm_or_grow0_xsrc_R1 : CCD.pt := CCD.mk_table 782%positive "((2 0(1 8)(0 264))(2 0(1 35)(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)0)(6#5(0 32))((0 0)65536)(0 962560)(7#5(0 32)#7#8)((1 2)-8256)(0 8256)(7#5(0 32)#10#11)((1 8)0)(7#5(0 32)#13(0 264))((1 8)288)(7#5(0 32)#15(0 120))((1 8)264)(7#5(0 32)#17(0 24))((1 2)8)(7#5(0 32)#19(0 40))(0 1048576)(5#21 1 4611686018427387904)((1 2)-16)(0#23 8(1 8))((1 2)-8)(0 244532)(0#25 8#26)((1 2)40)(0#28 8#1)((1 8)272)((1 8)280)(6#17(0 24))((1 8)296)(0#33 8(1 35))(5(1 35)0 18446744073709551615)((1 8)344)(0#36 8(0 1))((1 8)28)(0#38 1(0 0))((1 8)30)(0#40 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(0 8240)(9#10#44)(6#10#11)(6#19(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#10#50#13(0 408))(5(1 32)0 0)(244144 244644 783764 763484 764892)(0#53)(2 0(1 48)(0 32)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_or_grow0_xsrc_R1 425%positive "(274376((1 0)(1 49)(2 0(1 2)(0 -16))(1 3)(1 4)(1 50)(1 51)(1 52)(0 1)#1(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)#2(0 0)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#3#4(9#5(0 32))#6#9#12#14#16#18#20#22#24#27#29(0#17 8(1 32))(0#30 8(1 32))(0#31 8(1 32))#32#34#35#37#39#41#42#43#45#46(9#19(0 32))#47#48#49#51#52)65(((1 2)-8256#11)((1 2)8(0 40))((1 8)264(0 24))((1 48)0(0 32)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_or_grow0_xsrc_R1 17%positive "(((1 48)(0 32)))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_or_grow0_xsrc_R1 672%positive "((0#54(0#54(1 0)))(((244644((1(0 244644))(2(1 2))(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 48))(10(2 0(1 2)(0 8)))(11(0 0))(12(0 0))(13(1 48))(14(0 0))(15(0 0))(16(1 59))(17(1 60))(18#55)(19#55)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()((0((1 2)32)8(0 0))(0((1 2)24)8(0 0))(0((1 2)16)8(0 0))(0#19 8(0 0))(0#31 8#55)(0#30 8#55)(0#17 8(1 48))(0((1 48)24)8(0 0))(0((1 48)16)8#2)(0((1 48)8)8(1 35))(0((1 48)6)1(0 0))(0((1 48)5)1(0 0))(0((1 48)4)1(0 0))(0#5 4(0 0))#3#4(9((1 48)7)(0 1))#6#9#12#14#16#18#20#22#24#27#29#32#34#35#37#39#41#42#43#45#46#47#48#49#51#52))(1 244644)))()())"%pstring.
