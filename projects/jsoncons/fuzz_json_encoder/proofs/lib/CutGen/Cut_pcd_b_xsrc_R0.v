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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_pcd_b_xsrc_T.
Definition dict_Cut_pcd_b_xsrc_R0 : CCD.pt := CCD.mk_table 1010%positive "((295284 295304 274112 295412 763484 764892)(0#1)(0 295384)(1#3)(2 0(1 2)(0 -64))(2#5)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(10(1 40))(11(0 4))(12(1 41))(0 276416)(13#17)(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(0 32))(19(0 4))(0 4294977024)(20#25)(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(#4#6#7#8#9#10#11#12#13#14#15#16#18#19#20#21#22#23#24#26#27#28#29#30#31#32#33#34#35#36#37)((1 41)211)(0#39 1(0 0))((1 2)-52)(0#41 4(0 4))(2 4(0 32)(1 64))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 41)1099511627776 140737488355328)(5(1 44)4096 140737488355328)((1 44)0)(0#48 1(1 64))(5(1 64)0 255)((1 41)128)(2 0(1 41)(0 96))(0#51 8#52)((1 41)96)(0 789696)(0#54 8#55)(3 65536 813152)(6#39(0 1))(6#41(0 4))((1 2)-64)((1 41)0)(7#60(0 64)#61(0 272))(7#60(0 64)#48(0 1))(7#61(0 272)#48(0 1))(1 274112)(2 6#25(1 64))(2 9#66(0 1))(2 1#67(0 0))(2 4#68(0 1))(4 0(0 -1)(1 64))(2 0#70(0 32))(5#71 0 32)(5(1 64)0 32)(5#43 0 0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_pcd_b_xsrc_R0 679%positive "((0#2(3(11 64 32 255(11 64 33 255(16 0(0#2(1 0)))))(11 64 0 32(16 1(0#2(3(16 2(0#2(1 1)))(16 3(0#2(1 2)))))))))(((274112#38()(#40#42(5(2 0(1 64)(0 -32))1 223)(5(1 64)33 255)(5(1 64)32 255)(5#43 1 1)#44#45#46#47#49#50#53#56#57#58#59#62#63#64))#65)((274112#38()(#40#42(5(2 0(4 0(0 -1)#67)(0 1))1 1)(5#69 1 1)#72#73#74#44#45#46#47#49#50#53#56#57#58#59#62#63#64))#65)((295304((1(1 33))#6#7#8#9#10#11#12#13(10(1 42))(11#67)(12(1 44))(13(1 45))#19#20#21#22#23#24#26#27#28#29#30#31#32#33#34#35#36#37)()((5(2 0#67(0 -1))0 0)(5#69 0 0)#72#73#74#44#45#46#47#49#50#53#56#57(0#39 1(1 65))#58(9#41(0 4))#59#62#63#64))(1 295304)))((1(0 32)(1 64)1)(1(1 64)(0 32)0)(1#68(0 1)1)(1(0 1)#68 0))())"%pstring.
