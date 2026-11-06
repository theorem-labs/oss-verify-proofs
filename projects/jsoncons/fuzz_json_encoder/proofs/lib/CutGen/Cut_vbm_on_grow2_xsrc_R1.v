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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vbm_on_grow2_xsrc_T Cut_vbm_on_grow2_xsrc_R0.
Definition dict_Cut_vbm_on_grow2_xsrc_R1 : CCD.pt := CCD.mk_table 1088%positive "((4 0(0 32)(1 33))(2 7#1(0 4))(2 0(1 8)(0 264))(2 0(1 35)(0 1))(5(1 48)4096 140737488355328)(4(1 48)16)((1 48)0)(4 0(0 32)#2)(6#7#8)((0 0)65536)(0 962560)(7#7#8#10#11)((1 2)-8256)(0 8256)(7#7#8#13#14)((1 8)0)(7#7#8#16(0 264))((1 8)288)(7#7#8#18(0 120))((1 8)264)(7#7#8#20(0 24))((1 2)8)(7#7#8#22(0 40))((1 32)0)(7#7#8#24#1)(0 1048576)(5#26 1 4611686018427387904)((1 2)-16)(0#28 8(1 8))((1 2)-8)(0 244384)(0#30 8#31)((1 2)40)(0#33 8#3)(0#20 8(1 32))((1 8)272)(2 0(1 32)#1)(0#36 8#37)((1 8)280)(0#39 8#37)(6#20(0 24))((1 8)296)(0#42 8(1 35))(5(1 35)0 18446744073709551615)((1 8)344)(0#45 8(0 1))((1 8)28)(0#47 1(0 0))((1 8)30)(0#49 1(0 0))(5(1 8)1099511627776 140737488355328)(4(1 8)8)(0 8240)(9#13#53)(6#13#14)(9#22(0 32))(6#22(0 40))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(0 8304)(7#13#60#16(0 408))(5(1 33)2 512)(2 7#1(0 5))(2 1#2#63)(5#64 2 512)(2 1#2(1 33))(5#66 2 512)(9#24#1)(6#24#1)(5(1 32)4096 140737488355328)(4(1 32)16)(7#13#60#24#1)(7#16(0 408)#24#1)(2#24#1 0)(0 1048575)(5#75 1 4611686018427387904)(2 0#1(1 48))(4 0(0 -32)(1 33))(2 0#78#8)(5#79 0 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vbm_on_grow2_xsrc_R1 402%positive "(274376((1 0)(1 49)(2 0(1 2)(0 -16))(1 3)(1 4)(1 50)(1 51)(1 52)#2#3(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(0 0)#4#1(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#5#6(9#7#8)#9#12#15#17#19#21#23#25#27#29#32#34#35#38#40#41#43#44#46#48#50#51#52#54#55#56#57#58#59#61#62#65#67#68#69#70#71#72#73#74)65(((1 2)-8256#14)((1 2)8(0 40))((1 8)264(0 24))((1 32)0#1)((1 48)0#8))()#75)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vbm_on_grow2_xsrc_R1 23%positive "(((1 48)#8)((1 32)#1))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_vbm_on_grow2_xsrc_R1 711%positive "((0(0(244256 244644 783764 763484 704108 763484 764892))(16 0(4#76(1 0))))(((763484((1(0 244456))(2(1 2))(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 48))(10(1 48))(11(1 32))(12#1)(13(1 56))(14(1 57))(15(1 58))(16(1 59))(17(1 60))(18(2 0#77(0 32)))(19#4)(20(2 0(1 48)#8))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()(#76#80(0(#77 24)8(0 0))(0(#77 16)8#4)(0(#77 8)8(1 35))(0(#77 6)1(0 0))(0(#77 5)1(0 0))(0(#77 4)1(0 0))(0(#77 0)4(0 0))#5#6(9#7#1)(9(#77 7)(0 1))(9(#77 32)(2 0#79(0 -32)))#9#12#15#17#19#21#23#25#27#29#32#34#35#38#40#41#43#44#46#48#50#51#52#54#55#56#57#58#59#61#62#65#67#68#69#70#71#72#73#74))(1 763484)))((0#80))())"%pstring.
