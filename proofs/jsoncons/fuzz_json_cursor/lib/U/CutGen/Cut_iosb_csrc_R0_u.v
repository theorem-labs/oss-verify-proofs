(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_iosb_csrc_T_u.
Definition dict_Cut_iosb_csrc_R0 : CCD.pt := CCD.mk_table 559%positive "((432192 430872 430880 430888 430896 581668 692228 751764 753172)(0#1)(0#2(1 0))(2 0(1 2)(0 -48))(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(0 791600)(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 42)0)((1 2)-40)((1 2)-32)((1 2)-24)((1 2)-16)((1 2)-8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 2)-48)(8(1 40))(9(1 41))(10(0 0))(11(1 43))(5(1 40)1099511627776 140737488355328)(1 692228))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_iosb_csrc_R0 392%positive "(#3(((581668((1(0 430872))#5#6#7#8#9#10(8(1 42))(9(0 0))(10(2 0(1 42)(0 48)))(11#11)#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#32 8#11)(0#33 8(1 51))(0#34 8(1 50))(0#35 8(1 41))(0#36 8(1 40))(0#37 8(1 33))#38#39(9#40(0 8))(6#40(0 48))(5(1 42)1099511627776 140737488355328)(0((1 42)48)8(0 874048))(0((1 42)72)8(0 0))(6#32(0 8))(7#40(0 48)#32(0 152))))(1 581668)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_iosb_csrc_R0 156%positive "(#3(((692228((1(0 430880))#5#6#7#8#9#10#41#42#43#44#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#38#39#45(0((1 40)56)8(0 0))))#46))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_iosb_csrc_R0 156%positive "(#3(((692228((1(0 430888))#5#6#7#8#9#10#41#42#43#44#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#38#39#45(0((1 40)64)8(0 0))))#46))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_iosb_csrc_R0 156%positive "(#3(((692228((1(0 430896))#5#6#7#8#9#10#41#42#43#44#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#38#39#45(0((1 40)88)8(0 0))))#46))()())"%pstring.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_iosb_csrc_R0 255%positive "(#3(((692228((1(1 64))(2(1 2))#6#7#8#9#10(8(1 65))(9(1 66))#43#44#12#13#14#15#16#17(18(1 67))(19(1 68))#20#21#22#23#24#25#26#27#28#29#30#31)()(#38#39#45(0((1 40)112)8(0 0))(0#37 8(1 64))(0#36 8(1 65))(0#35 8(1 66))(0#34 8(1 67))(0#33 8(1 68))))#46))()())"%pstring.
