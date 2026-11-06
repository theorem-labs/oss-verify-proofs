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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fi_u64_xsrc_T.
Definition dict_Cut_fi_u64_xsrc_R0 : CCD.pt := CCD.mk_table 1053%positive "((252368 252392 252436 422204 252392 763484 764892)(0#1)(2 0(1 33)(0 -1))(5#3 0 19)(5(0 1)1 20)(4 0(0 -4)(1 33))(0 1048576)(2 0#6#7)(5#8 1 4611686018427387904)(5#7 0 4611686018427387904)(4 0(0 4)(1 33))(5#11 0 4611686018427387904)(0 -320)(2 0(1 2)#13)(2#14)(3(1 3))(4(1 4))(5(1 51))(6(1 52))(7(1 53))(8(1 11))(9(1 33))(12(1 56))(13(1 57))(14(1 58))(15(1 59))(16(1 60))(17(1 61))(0 -295)(2 0(1 2)#29)(18#30)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 62))(29(1 63))(30(1 64))(31(1 65))((1 11)0)(0#44 8(1 32))(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 33)1 20)((1 2)-8816)(0 8816)(6#50#51)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#50#51#44(0 8))((1 32)0)(7#50#51#56(0 24))(7#44(0 8)#56(0 24))((1 2)-8)(0#59 8(1 1))((1 2)-16)(0#61 8(1 8))((1 2)-24)(0#63 8(1 9))((1 2)-32)(0#65 8(1 18))((1 2)-40)(0#67 8(1 19))((1 2)-320)(9#69(0 25))((1 2)-295)(9#71(0 255))(0 8496)(9#50#73)(4 0(0 4)(1 48))(2 0#75(0 4))(5#76 1 4611686018427387904)(2 0(1 2)(1 48))(#78 -295))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_fi_u64_xsrc_R0 447%positive "((0#2(4#4(4#5(4#9(4#10(4#12(1 0)))))))(((252392((1(1 1))#15#16#17#18#19#20#21#22(10(0 255))(11(1 55))#23#24#25#26#27#28#31(19(2 0(2 0(1 2)(1 33))(0 -296)))#32#33#34#35#36#37#38#39#40#41#42#43)()(#45#46#47#48#49#52#53#54#55#57#58#60#62#64#66#68#70#72#74#4#5#9#10#12))(0 1((48#3)(65(1 65))(64(1 64))(63(1 63))(62(1 62))(61(1 61))(60(1 60))(59(1 59))(58(1 58))(57(1 57))(56(1 56))(55(1 55))(54(0 255))(53(1 53))(52(1 52))(51(1 51))(50(1 1))))))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_fi_u64_xsrc_R0 328%positive "((16 0(0#2(4#77(1 0))))(((422204((1(0 252404))#15#16#17#18#19#20#21#22(10(1 32))(11(1 66))#23#24#25#26#27#28#31(19(2 0#78#29))#32#33#34#35#36#37#38#39#40#41#42#43)()(#77(0#79 1(1 66))(5(1 66)0 255)#45#46#47#48#49#52#53#54#55#57#58#60#62#64#66#68#70#72#74(5(1 48)0 19)(5(2 0(1 33)(4 0(0 -1)(1 48)))1 20)))(1 422204)))((9#79))())"%pstring.
