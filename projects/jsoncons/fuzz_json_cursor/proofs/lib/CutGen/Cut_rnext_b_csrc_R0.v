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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_rnext_b_csrc_T.
Definition dict_Cut_rnext_b_csrc_R0 : CCD.pt := CCD.mk_table 858%positive "((240536 240728 240772 243864 245028 244064 240768 744000 745408)(0#1)(0#2(1 0))(2 0(1 2)(0 -80))(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(2 1(1 65)(1 64))(2 4#32(0 1))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 41)4096 140737488355328)((1 41)512)(0#37 8(1 64))((1 41)520)(0#39 8(1 65))(1(1 64))(2(1 2))(8(1 65))(9(1 66))(18(1 67))(19(1 68))(20(1 69))(21(1 70))(22(1 71))(23(1 72))((1 2)-8)(0#51 8(1 64))((1 2)-16)(0#53 8(1 65))((1 2)-24)(0#55 8(1 66))((1 2)-32)(0#57 8(1 67))((1 2)-40)(0#59 8(1 68))((1 2)-48)(0#61 8(1 69))((1 2)-56)(0#63 8(1 70))((1 2)-64)(0#65 8(1 71))((1 2)-72)(0#67 8(1 72))(#34#35#52#54#56#58#60#62#64#66#68))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_rnext_b_csrc_R0 375%positive "((0#2(3#3(0#2(1 1))))(((243864((1(0 240560))#5#6#7#8#9#10#11#12(10(1 52))(11(1 40))#13#14#15#16#17#18#19#20#21#22#23(23(1 55))#24#25#26#27#28#29#30#31)()((5#33 1 1)#34#35#36#38#40))(1 243864))((245028((1(0 240656))#5#6#7#8#9#10#11#12(10(1 51))(11(1 50))(12(1 40))#14#15#16#17#18#19#20#21#22#23(23(0 1))#24#25#26#27#28#29#30#31)()((5#33 0 0)#34#35#36#38#40))(1 245028)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_rnext_b_csrc_R0 141%positive "(#3(((240768(#41#42#6#7#8#9#10#43#44(10(1 42))(11(1 43))#13#14#15#16#17#18#45#46#47#48#49#50#24#25#26#27#28#29#30#31)()#69)(1 240768)))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_rnext_b_csrc_R0 140%positive "(#3(((244064(#41#42#6#7#8#9#10#43#44(10(1 40))(11(0 1))#13#14#15#16#17#18#45#46#47#48#49#50#24#25#26#27#28#29#30#31)()#69)(1 244064)))()())"%pstring.
