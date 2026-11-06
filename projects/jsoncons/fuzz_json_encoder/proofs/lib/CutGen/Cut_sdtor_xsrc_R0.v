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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_sdtor_xsrc_T.
Definition dict_Cut_sdtor_xsrc_R0 : CCD.pt := CCD.mk_table 509%positive "((238960 239000 239056 239076 412456 593548 444820 444072 763484 764892)(0#1)(0#2(1 0))(2 0(1 2)(0 -32))(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(9(1 41))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 2)-32)((1 2)-24)((1 2)-16)((1 2)-8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(8(1 40))(0 803432)(0 788352)((1 40)24)((1 40)8)((1 40)88))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xsrc_R0 366%positive "(#3(((412456((1(0 239000))#5#6#7#8#9#10(8(1 42))#11(10(1 64))(11(1 65))#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#32 8(1 50))(0#33 8(1 41))(0#34 8(1 40))(0#35 8(1 33))#36#37(6#32(0 32))(5(1 42)1099511627776 140737488355328)(0((1 42)264)8(1 64))(5(1 64)4096 140737488355328)(0((1 42)272)8(1 65))(7#32(0 32)((1 42)0)(0 592))))(1 412456)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xsrc_R0 328%positive "(#3(((593548((1(0 239056))#5#6#7#8#9#10#38(9(2 0(1 40)(0 8)))(10(2 0(1 40)(0 32)))(11#39)(12#40)#13#14#15#16#17(18(2 0(1 40)(0 88)))#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#41 8#39)(0#42 8(0 788312))(0#43 8#40)#36#37(5(1 40)1099511627776 140737488355328)(3 65536 813152)(6#42(0 8))(6#41(0 8))(6#43(0 8))))(1 593548)))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xsrc_R0 159%positive "(#3(((444820((1(0 239076))#5#6#7#8#9#10#38#11(10(1 41))(11(0 788376))#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#36#37))(1 444820)))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_xsrc_R0 232%positive "(#3(((444072((1(1 64))(2(1 2))#6#7#8#9#10(8(1 65))(9(1 66))(10(1 50))(11(1 43))#12#13#14#15#16#17(18(1 67))#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#36#37(0#35 8(1 64))(0#34 8(1 65))(0#33 8(1 66))(0#32 8(1 67))))(1 444072)))()())"%pstring.
