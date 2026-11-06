(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_syscat_xasan_T.
Definition dict_Cut_syscat_xasan_R0 : CCD.pt := CCD.mk_table 450%positive "((1058428 1058428 1058452 1387168 1388196)(0#1)(0#2(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(0 1463216)(10#13)(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-128)(6#34(0 128))(5(1 2)140735332483200 140737488355328)(4(1 2)16)((0 0)6932480)(0#38 1(0 1))(1 1058452))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_xasan_R0 157%positive "(#3(((1058452(#4#5#6#7#8#9#10#11#12#14(11(1 11))(12(1 12))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()((9#34(0 128))#35#36#37#39))#40))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_syscat_xasan_R0 207%positive "(#3(((1058452(#4#5#6#7#8#9#10#11#12#14(11(0 1))(12(0 2))#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33)()((0((0 0)6932481)1(0 1))#39(0((1 2)-8)8(1 1))(9#34(0 120))#35#36#37(6#38(0 2))))#40))()())"%pstring.
