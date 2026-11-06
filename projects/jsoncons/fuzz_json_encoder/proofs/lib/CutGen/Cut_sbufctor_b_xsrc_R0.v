(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_sbufctor_b_xsrc_T.
Definition dict_Cut_sbufctor_b_xsrc_R0 : CCD.pt := CCD.mk_table 1017%positive "((239956 239996 763484 764892)(0#1)(1(1 64))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 65))(9(1 66))(10(0 0))(6 0 0 1(1 71))(2 9#13(0 1))(11#14)(2 6#13(0 1))(2 0(1 40)#16)(2 0#17(0 65))(13(0 8))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 67))(19(1 68))(20(1 69))(21(1 70))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 40)88)((1 40)32)((1 40)24)(2 0(1 40)(0 65))((1 40)16)(2 1#14(0 0))(2 4#43(0 1))((1 2)-96)(0#45 8(1 50))((1 2)-88)(0#47 8(1 41))((1 2)-80)(0#49 8(1 40))((1 2)-72)(0 239964)(0#51 8#52)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 2)-8)(0#56 8(1 64))((1 2)-16)(0#58 8(1 65))((1 2)-24)(0#60 8(1 66))((1 2)-32)(0#62 8(1 67))((1 2)-40)(0#64 8(1 68))((1 2)-48)(0#66 8(1 69))((1 2)-56)(0#68 8(1 70))(6#45(0 32))(5(1 40)1099511627776 140737488355328)((1 40)64)(0#72 8(1 71))((1 40)72)(0#74 8(1 72))((1 40)80)(0#76 8(1 73))((1 40)96)(0#78 4(0 8))(6#42(0 24))(6#38(0 8))((1 40)0)(7#45(0 96)#82(0 104))(1 239996)(2 0(1 72)(1 73)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_sbufctor_b_xsrc_R0 649%positive "((0#2(3(16 0(0#2(1 0)))(11 71 1 18446744073709551615(16 1(0#2(1 1))))))(((239996(#3#4#5#6#7#8#9#10#11#12#15(12#18)#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37)()((0#38 8#18)(0#39 8#18)(0#40 8#41)(0#42 8#41)(5(2 0(4 0(0 -1)#14)(0 1))1 1)(5#44 1 1)#46#48#50#53#54#55#57#59#61#63#65#67#69#70#71#73#75#77#79#80#81#83))#84)((239996(#3#4#5#6#7#8#9#10#11#12#15(12#85)#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37)()((0#38 8#85)(0#39 8#85)(0#40 8(1 73))(0#42 8(1 73))(5(2 0#14(0 -1))0 0)(5(1 71)1 18446744073709551615)(5#44 0 0)#46#48#50#53#54#55#57#59#61#63#65#67#69#70#71#73#75#77#79#80#81#83))#84))((1#43(0 1)1)(1(0 1)#43 0))())"%pstring.
