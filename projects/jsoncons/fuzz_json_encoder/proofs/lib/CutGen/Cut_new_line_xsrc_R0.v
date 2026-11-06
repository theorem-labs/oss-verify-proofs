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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_new_line_xsrc_T.
Definition dict_Cut_new_line_xsrc_R0 : CCD.pt := CCD.mk_table 908%positive "((251692 251952 251996 421620 422204 763484 764892)(0#1)(0 1048576)(5#3 1 4611686018427387904)(2 0(1 2)(0 -80))(2#5)(3(1 3))(4(1 4))(8(1 10))(2 0(1 2)(0 -47))(10(1 32))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(0 2562)((1 2)-24)(0#23 8(1 9))((1 2)-16)(0#25 8(1 8))((1 2)-8)(0#27 8(1 1))((1 10)8)(0#29 8(1 32))((1 10)48)(0#31 8#22)((1 10)56)(0#33 8(0 0))((1 10)64)(0#35 8(0 0))((1 10)248)(0#37 1(0 32))((1 10)288)(4 0(0 4)(1 33))(0#39 4#40)(5(1 33)0 1024)((1 10)296)(9#43(0 8))(6#43(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-8576)(0 8496)(9#50#51)(0 8576)(6#50#53)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#50#53#57(0 408))((1 32)0)(7#50#53#59(0 24))(7#57(0 408)#59(0 24))((1 2)-80)(4 0(0 4)(1 48))(2 0#63(0 2))(5#64 1 4611686018427387904)(4 0(0 -1)(1 48))(2 0#40#66))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_new_line_xsrc_R0 431%positive "((0#2(4#4(1 0)))(((421620((1(0 251884))#6#7#8(5(1 5))(6(1 6))(7(1 7))#9(9#10)#11(11#10)(12(0 1))(13(0 0))(14(1 14))(15(1 15))(16(1 16))(17(1 17))#12#13#14#15#16#17#18#19#20#21(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#4(0((1 2)-56)8(0 0))(0((1 2)-64)8(0 0))(0((1 2)-72)8#22)(0((1 2)-32)8(0 0))(0((1 2)-40)8(0 0))(0((1 2)-48)8#22)#24#26#28#30#32#34#36#38#41#42#44#45#46#47#48#49#52#54#55#56#58#60#61(9#62(0 8))))(1 421620)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_new_line_xsrc_R0 360%positive "((0#2(4#65(1 0)))(((422204((1(0 251964))#6#7#8(5(1 50))(6(1 51))(7(1 52))#9(9#67)#11(11(0 32))(12(1 55))(13(1 56))(14(1 57))(15(1 58))(16(1 59))(17(1 60))#12#13#14#15#16#17#18#19#20#21(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()(#65#30#32#34#36#38#41#42#44#45#46#47#48#49#52#54#55#56#58#60#61#28#26#24(9#62(0 56))(5(1 48)1 4096)(5#67 0 4096)))(1 422204)))()())"%pstring.
