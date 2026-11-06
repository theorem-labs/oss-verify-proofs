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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T.
Definition dict_Cut_df_xsrc_R0 : CCD.pt := CCD.mk_table 806%positive "((273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892)(0#1)(0 1048576)(5#3 1 4611686018427387904)(0 -160)(2 0(1 2)#5)(2#6)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 11))(15(1 15))(16(1 16))(17(1 17))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-48)((1 2)-40)(0#31 8(1 19))((1 2)-32)(0#33 8(1 18))((1 2)-24)(0#35 8(1 9))((1 2)-16)(0#37 8(1 8))((1 2)-8)(0#39 8(1 1))((1 11)0)(0#41 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#47#48)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#47#48#41(0 8))((1 32)0)(7#47#48#53(0 24))(7#41(0 8)#53(0 24))(0 524288)(5#56 1 4611686018427387904))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R0 294%positive "((0#2(0(3 1)(0#2(4#4(1 0)))))(((273868((1(1 1))#7#8#9#10#11#12#13(9(1 9))(10(1 10))(11(1 11))(12(1 12))(13(1 13))(14(1 14))#14#15#16(18(1 18))#17#18#19#20#21#22#23#24#25#26#27#28#29)()(#4(0#30 8(1 48))#32#34#36#38#40#42#43#44#45#46#49#50#51#52#54#55(9#47(0 9152))(9#31(0 0))))(1 273868)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R0 312%positive "((0#2(4#57(1 0)))(((719568((1(0 273964))#7#8#9#10#11#12#13(9(1 10))(10(2 0(1 2)(0 -148)))(11(0 100))(12(0 77440))(13(0 15))(14(1 48))#14#15#16(18(1 48))#17#18#19#20#21#22#23#24#25#26#27#28#29)()(#57#42#43#44#45#46#49#50#51#52#54#55(9#47(0 9040))(9((1 2)-160)(0 112))#40#38#36#34#32(9#30(0 8))))(1 719568)))()())"%pstring.
