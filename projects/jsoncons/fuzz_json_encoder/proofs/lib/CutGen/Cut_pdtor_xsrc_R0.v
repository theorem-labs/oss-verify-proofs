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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_pdtor_xsrc_T.
Definition dict_Cut_pdtor_xsrc_R0 : CCD.pt := CCD.mk_table 715%positive "((238612 238664 238676 238692 412456 238676 238692 238816 763484 764892)(0#1)(0#2(1 0))(2 0(1 2)(0 -16))(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(9(1 41))(12(1 44))(13(1 45))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))((1 42)256)((1 42)0)((1 2)-16)((1 2)-8)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(1 412456)(1(1 33))(8(1 40))(2 9(1 64)(0 1))(10#41)(11(1 43))(#39#5#6#7#8#9#10#40#11#42#43#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)(2 1#41(0 0))(2 4#45(0 1))(5(1 40)1099511627776 140737488355328)((1 40)224)(0#48 1(1 64))(5(1 64)0 255)(0 789696))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_xsrc_R0 401%positive "(#3(((412456((1(0 238664))#5#6#7#8#9#10(8(1 42))#11(10(1 64))(11(2 0(4 0(0 -1)(1 64))(1 65)))#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()((0#32 8(1 64))(0#33 8(0 788192))(0#34 8(1 40))(0#35 8(1 33))#36#37(6#34(0 16))(5(1 42)1099511627776 140737488355328)(0((1 42)248)8(1 64))(5(1 64)4096 140737488355328)(0((1 42)264)8(1 65))(6#33(0 8))(6#32(0 8))(7#34(0 16)#33(0 272))))#38))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_xsrc_R0 274%positive "((0#2(3(11 64 0 254(16 0#3))(11 64 1 255(16 1(0#2(1 1))))))(((238692#44()((5(2 0(4 0(0 -1)#41)(0 1))1 1)(5(1 64)0 254)(5#46 1 1)#36#37#47#49#50))(1 238692))((238676#44()((5(2 0#41(0 -1))0 0)(5(1 64)1 255)(5#46 0 0)#36#37#47#49#50))(1 238676)))((1#45(0 1)1)(1(0 1)#45 0))())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_xsrc_R0 206%positive "(#3(((412456((1(0 238692))#5#6#7#8#9#10#40#11(10(1 65))(11(4 0(0 2)(2 6(1 64)(0 1))))#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#36#37#47(0#48 8(1 64))(0((1 40)240)8(1 65))))#38))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_xsrc_R0 323%positive "(#3(((238816((1(1 64))(2(1 2))#6#7#8#9#10(8(1 65))#11(10(0 0))(11(0 276404))(12#51)#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31)()(#36#37(0#35 8(1 64))(0#34 8(1 65))#47(0((1 40)128)8(2 0(1 40)(0 96)))(0((1 40)96)8#51)(3 65536 813152)(0((1 40)72)1(0 0))(0((1 40)48)1(0 0))(0((1 40)24)1(0 0))))(1 238816)))()())"%pstring.
