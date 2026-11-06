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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getstr_key_csrc_T.
Definition dict_Cut_getstr_key_csrc_R0 : CCD.pt := CCD.mk_table 470%positive "((268092 268404 270352 275692 268808 269100 269520 237976 268760 268364 268536 268620 268632 268680 744000 745408)(0#1)(0#2(1 0))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(10(1 42))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 2)-24)((1 2)-16)((1 2)-8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 2)-48)((1 42)0)((1 43)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_key_csrc_R0 531%positive "(#3(((270352((1(0 268404))(2(2 0(1 2)(0 -48)))#4#5#6#7#8(8(1 42))(9(1 43))#9(11(1 65))(12(1 66))(13(2 0(1 2)(0 -25)))#10#11#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27)()((0((1 2)-25)1(1 44))(0#28 8(1 41))(0#29 8(1 40))(0#30 8(1 33))#31#32(9#33(0 23))(6#33(0 48))(5(1 42)1099511627776 140737488355328)(9#34(0 24))(6#34(0 24))(5(1 43)4096 140737488355328)(0#35 8(0 4097))(9((1 43)8)(0 16))(0((1 43)24)8(1 65))(0((1 43)32)8(1 66))(3 65536 793640)(7#33(0 48)#34(0 24))(7#33(0 48)#35(0 40))(7#35(0 40)#34(0 24))))(1 270352)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_getstr_key_csrc_R0 216%positive "(#3(((268680((1(1 64))(2(1 2))#4#5#6#7#8(8(1 65))(9(1 66))#9(11(1 43))(12(1 44))(13(1 45))#10#11#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27)()(#31#32(0#30 8(1 64))(0#29 8(1 65))(0#28 8(1 66))))(1 268680)))()())"%pstring.
