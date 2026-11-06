(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm10CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_hnb_s2s_csrc_T.
Definition dict_Cut_hnb_s2s_csrc_R0 : CCD.pt := CCD.mk_table 943%positive "((234656 268092 392920 236980 574064 234916 744000 745408)(0#1)(0 -1024)(2 0(1 2)#3)(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(6 1 0 4(1 69))(2 1#31(0 0))(2 4#32(0 1))(6 0 0 1(1 68))(2 9#34(0 1))(4 0(0 -1)#35)(2 0#36(0 1))(5#37 1 1)(2 1#35(0 0))(2 4#39(0 1))(5#40 1 1)(6 0 0 1(1 67))(4 0(0 -1)#42)(2 0#43(0 1))(5#44 1 1)(2 1#42(0 0))(2 4#46(0 1))(5#47 1 1)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 2)-460)(0#51 1(1 67))((1 2)-352)(0#53 1(1 68))((1 2)-336)(0#55 4(1 69))((1 2)-992)(6#57(0 8))((1 2)-344)(6#59(0 8))(0 234736)(1#61)(0 -672)(2 0(1 2)#63)(10#64)(0 768720)(11#66)(12(1 44))(13(1 45))(#62#5#6#7#8#9#10#11#12#65#67#68#69#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30)(0 768936)(0#59 8#71)(0#57 8#66)(1 236980))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_hnb_s2s_csrc_R0 802%positive "((0#2(3(16 0(0#2(3(16 1(0#2(3(0#2(1 0))(11 69 1 18446744073709551615(0#2(1 1))))))(11 68 1 18446744073709551615(16 2(0#2(1 2)))))))(11 67 1 18446744073709551615(16 3(0#2(1 3))))))(((268092((1(0 234624))#5#6#7#8#9#10#11#12(10(2 0(1 2)(0 -1016)))(11(1 40))(12(0 0))(13(2 0(1 2)(0 -336)))#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30)()((5#33 1 1)#38#41#45#48#49#50#52#54#56(9#57(0 8))#58(9#59(0 8))#60))(1 268092))((236980#70()(#72#73(5(1 69)1 18446744073709551615)(5#33 0 0)#38#41#45#48#49#50#52#54#56#58#60))#74)((236980#70()(#72#73(5(2 0#35(0 -1))0 0)(5(1 68)1 18446744073709551615)(5#40 0 0)#45#48#49#50#52#54#56#58#60))#74)((236980#70()(#72#73(5(2 0#42(0 -1))0 254)(5(1 67)1 18446744073709551615)(5#47 0 0)#49#50#52#54#56#58#60))#74))((1#46(0 1)1)(1#39(0 1)1)(1(0 1)#39 0)(1(0 1)#46 0))())"%pstring.
