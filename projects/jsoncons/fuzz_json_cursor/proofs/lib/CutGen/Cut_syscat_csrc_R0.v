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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_syscat_csrc_T.
Definition dict_Cut_syscat_csrc_R0 : CCD.pt := CCD.mk_table 434%positive "((419856 419856 419880 744000 745408)(0#1)(0#2(1 0))(1(1 33))(2(1 2))(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(0 797840)(10#13)(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(5(1 2)1099511627776 140737488355328)(4(1 2)16)((0 0)864736)(0#36 1(0 1))(1 419880)((1 2)-16))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_csrc_R0 140%positive "(#3(((419880(#4#5#6#7#8#9#10#11#12#14(11(1 43))(12(1 44))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()(#34#35#37))#38))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_csrc_R0 213%positive "(#3(((419880(#4#5#6#7#8#9#10#11#12#14(11(0 1))(12(0 2))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()((0((0 0)864737)1(0 1))#37(0((1 2)-8)8(1 33))#34#35(9#39(0 8))(6#39(0 16))(6#36(0 2))))#38))()())"%pstring.
