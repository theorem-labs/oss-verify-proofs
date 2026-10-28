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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_guard_csrc_T_u.
Definition dict_Cut_guard_csrc_R0 : CCD.pt := CCD.mk_table 437%positive "((283488 283568 283544 283584 751764 753172)(0#1)(0#2(1 0))(1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 42)1)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 42)0 4611686018427387904)((1 42)0)(6#36(0 2)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_guard_csrc_R0 199%positive "(#3(((283544(#4#5#6#7#8#9#10#11#12(10(0 1))(11(0 18446744073709551615))(12(0 2))#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#32 1(0 2))#33#34#35(0#36 1(0 0))#37))(1 283544)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_guard_csrc_R0 182%positive "(#3(((283584(#4#5#6#7#8#9#10#11#12(10(1 42))(11(0 1))(12(1 44))#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#32 1(0 1))(0#36 1(0 1))#33#34#35#37))(1 283584)))()())"%pstring.
