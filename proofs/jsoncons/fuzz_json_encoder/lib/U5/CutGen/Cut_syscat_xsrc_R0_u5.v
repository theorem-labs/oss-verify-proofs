(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_syscat_xsrc_T_u5.
Definition dict_Cut_syscat_xsrc_R0 : CCD.pt := CCD.mk_table 434%positive "((454008 454008 454032 778312 779720)(0#1)(0#2(1 0))(1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(0 832176)(10#13)(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(5(1 2)1099511627776 140737488355328)(4(1 2)16)((0 0)899136)(0#36 1(0 1))(1 454032)((1 2)-16))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_xsrc_R0 140%positive "(#3(((454032(#4#5#6#7#8#9#10#11#12#14(11(1 43))(12(1 44))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()(#34#35#37))#38))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_xsrc_R0 213%positive "(#3(((454032(#4#5#6#7#8#9#10#11#12#14(11(0 1))(12(0 2))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()((0((0 0)899137)1(0 1))#37(0((1 2)-8)8(1 33))#34#35(9#39(0 8))(6#39(0 16))(6#36(0 2))))#38))()())"%pstring.
