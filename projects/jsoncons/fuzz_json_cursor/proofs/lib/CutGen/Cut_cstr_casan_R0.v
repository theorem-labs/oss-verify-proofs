(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_cstr_casan_T.
Definition dict_Cut_cstr_casan_R0 : CCD.pt := CCD.mk_table 1024%positive "((857780 857780 857780 858072 435532 521552 1330948 1331976)(0#1)(5(0 24)1 4611686018427387904)(4#3(1 0))(0#2#4)(0 857840)(1#6)(2 0(1 2)(0 -64))(2#8)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(0 155456)(9(1 9))(0 1427896)(11#17)(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 10))(19(1 19))(20(1 20))(0 2147450880)(21#28)(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-56)(0#40 8(1 21))((1 2)-48)(0#42 8(1 20))((1 2)-40)(0#44 8(1 19))((1 2)-32)(0#46 8(1 18))((1 2)-24)(0#48 8(1 9))((1 2)-16)(0#50 8(1 8))((1 2)-8)(0#52 8(1 1))(3 1359872 1392640)((0 0)1427896)(0#55 8#28)((1 10)0)(9#57(0 24))(6#57(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#62 2147450880)(1#63(0 3))((0 0)2147446784)(0 17592186048512)(7#65#66#57(0 24))((1 2)-4176)(0 4120)(9#68#69)(0 4176)(6#68#71)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#68#71#57(0 24))(#3#41#43#45#47#49#51#53#54#56#58#59#60#61#64#67#70#72#73#74#75)(1 435532)(0 155392)(0 155424))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R0 129%positive "(#5(((435532(#7#9#10#11#12#13#14(8#15)#16(10#15)#18#19#20#21#22#23#24#25#26#27#29#30#31#32#33#34#35#36#37#38#39)()#76)#77))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R0 129%positive "(#5(((435532(#7#9#10#11#12#13#14(8#78)#16(10#78)#18#19#20#21#22#23#24#25#26#27#29#30#31#32#33#34#35#36#37#38#39)()#76)#77))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_cstr_casan_R0 129%positive "(#5(((435532(#7#9#10#11#12#13#14(8#79)#16(10#79)#18#19#20#21#22#23#24#25#26#27#29#30#31#32#33#34#35#36#37#38#39)()#76)#77))()())"%pstring.
