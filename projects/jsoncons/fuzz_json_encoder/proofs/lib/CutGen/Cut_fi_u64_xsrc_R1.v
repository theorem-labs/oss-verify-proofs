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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_fi_u64_xsrc_T Cut_fi_u64_xsrc_R0.
Definition dict_Cut_fi_u64_xsrc_R1 : CCD.pt := CCD.mk_table 1112%positive "((0 -320)(2 0(1 2)#1)(0 -295)(2 0(1 2)#3)(2 0(1 2)(1 48))(4 0(0 4)(1 48))(2 0#6(0 4))(5#7 1 4611686018427387904)(#5 -295)(0#9 1(1 66))(5(1 66)0 255)((1 11)0)(0#12 8(1 32))(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 33)1 20)((1 2)-8816)(0 8816)(6#18#19)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#18#19#12(0 8))((1 32)0)(7#18#19#24(0 24))(7#12(0 8)#24(0 24))((1 2)-8)(0#27 8(1 1))((1 2)-16)(0#29 8(1 8))((1 2)-24)(0#31 8(1 9))((1 2)-32)(0#33 8(1 18))((1 2)-40)(0#35 8(1 19))((1 2)-320)(9#37(0 25))((1 2)-295)(9#39(0 255))(0 8496)(9#18#41)(5(1 48)0 19)(4 0(0 -1)(1 48))(2 0(1 33)#44)(5#45 1 20)(2 0#6(0 3))(252368 252392 252436 422204 252392 763484 764892)(0#48)(5(0 3)1 4611686018427387904)(5#47 0 4611686018427387904)(5#6 0 4611686018427387904)(3(1 3))(4(1 4))(5(1 68))(6(1 69))(7(1 70))(11(1 72))(12(1 73))(13(1 74))(14(1 75))(15(1 76))(16(1 77))(17(1 78))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 79))(29(1 80))(30(1 81))(31(1 82))(0 -296)(2 0#5#77)(2 4#78#4)(2 0(1 48)(0 -1))(5#80 0 19)(2 0#45(0 1))(5#82 1 20))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_fi_u64_xsrc_R1 292%positive "(252404((1 0)(1 67)#2(1 3)(1 4)(1 68)(1 69)(1 70)(1 11)(1 33)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 78)#4(2 0#5#3)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 79)(1 80)(1 81)(1 82))(#8#10#11#13#14#15#16#17#20#21#22#23#25#26#28#30#32#34#36#38#40#42#43#46)83(((1 2)-8816#19))()#47)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_fi_u64_xsrc_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_fi_u64_xsrc_R1 825%positive "((0#49(3(16 0(0#49(1 0)))(16 1(0#49(16 2(16 3(4#50(4#51(4#52(1 1))))))))))(((252436((1(1 1))(2(1 2))#53#54#55#56#57(8(1 8))(9(1 9))(10(1 33))#58#59#60#61#62#63#64(18(1 18))(19(1 19))#65#66#67#68#69#70#71#72#73#74#75#76)()((5(2 0#44(0 1))1 139637976727553)(5#79 1 1)#8#10#11#13#14#15#16#17#20#21#22#23#25#26#28#30#32#34#36#38#40#42#43#46))(1 252436))((252392((1(1 67))(2#2)#53#54#55#56#57(8(1 11))(9(1 33))(10(1 71))#58#59#60#61#62#63#64(18#4)(19#78)#65#66#67#68#69#70#71#72#73#74#75#76)()(#13#14#15#16#17#20#21#22#23#25#26#28#30#32#34#36#38#40#42#81#83#50#51#52(5#80 0 139637976727570)(5#79 0 0)#8#10#11#43#46))(0 1((48#80)(65(1 82))(64(1 81))(63(1 80))(62(1 79))(61(1 78))(60(1 77))(59(1 76))(58(1 75))(57(1 74))(56(1 73))(55(1 72))(54(1 71))(53(1 70))(52(1 69))(51(1 68))(50(1 67))))))((1#78#4 1)(1#4#78 0)(0#81)(0#83))())"%pstring.
