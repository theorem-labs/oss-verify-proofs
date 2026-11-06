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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getstr_bool_csrc_T.
Definition dict_Cut_getstr_bool_csrc_R0 : CCD.pt := CCD.mk_table 952%positive "((268092 268596 270352 275692 268808 269100 269520 237976 268760 268364 268536 268620 268632 268680 744000 745408)(0#1)(0#2(1 0))(0 268596)(1#4)(2 0(1 2)(0 -48))(2#6)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 42))(9(1 43))(10(1 42))(2 0(1 2)(0 -25))(12#16)(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(6 0 0 1(1 65))(2 1#37(0 0))(2 4#38(0 1))((1 2)-25)(0#40 1(1 44))((1 2)-24)(0#42 8(1 41))((1 2)-16)(0#44 8(1 40))((1 2)-8)(0#46 8(1 33))(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 2)-48)(9#50(0 23))(6#50(0 48))(5(1 42)1099511627776 140737488355328)((1 42)0)(9#54(0 24))(6#54(0 24))(5(1 43)4096 140737488355328)((1 43)0)(0#58 8(0 8))((1 43)8)(9#60(0 16))((1 43)24)(0#62 8(1 65))((1 43)32)(0#64 8(1 66))(3 65536 793640)(7#50(0 48)#54(0 24))(7#50(0 48)#58(0 40))(7#58(0 40)#54(0 24))(1 275692))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_bool_csrc_R0 555%positive "((0#2(3(16 0#3)(11 65 1 18446744073709551615(16 1(0#2(1 1))))))(((275692(#5#7#8#9#10#11#12#13#14#15(11(0 66375))#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36)()((5(2 0(4 0(0 -1)#37)(0 1))1 1)(5#39 1 1)#41#43#45#47#48#49#51#52#53#55#56#57#59#61#63#65#66#67#68#69))#70)((275692(#5#7#8#9#10#11#12#13#14#15(11(0 72770))#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36)()((5(2 0#37(0 -1))0 254)(5(1 65)1 18446744073709551615)(5#39 0 0)#41#43#45#47#48#49#51#52#53#55#56#57#59#61#63#65#66#67#68#69))#70))((1#38(0 1)1)(1(0 1)#38 0))())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_bool_csrc_R0 213%positive "(#3(((268680((1(1 64))(2(1 2))#8#9#10#11#12(8(1 65))(9(1 66))#15(11(1 43))(12(1 44))#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36)()(#48#49(0#46 8(1 64))(0#44 8(1 65))(0#42 8(1 66))))(1 268680)))()())"%pstring.
