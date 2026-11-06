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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_strinit_casan_T.
Definition dict_Cut_strinit_casan_R0 : CCD.pt := CCD.mk_table 1143%positive "((719088 719088 719088 719088 719372 1358140 521552 1330948 1331976)(0#1)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(2 0(1 10)(0 1))(10#8)(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(19(1 19))(20(1 20))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 10)1)((1 10)0)((1 2)-56)(0#29 8(1 21))((1 2)-48)(0#31 8(1 20))((1 2)-40)(0#33 8(1 19))((1 2)-32)(0#35 8(1 18))((1 2)-24)(0#37 8(1 9))((1 2)-16)(0#39 8(1 8))((1 2)-8)(0#41 8(1 1))(3 1359872 1392640)((0 0)1427896)(0 2147450880)(0#44 8#45)(6#28(0 24))(5(1 10)7024640 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#50 2147450880)(1#51(0 3))(2 0(1 10)(0 8))(2 6#53(0 3))(#54 2147450880)(1#55(0 1))(2 0(1 10)(0 16))(2 6#57(0 3))(#58 2147450880)(1#59(0 1))((0 0)2147446784)(0 17592186048512)(7#61#62#28(0 24))((1 2)-4176)(0 4120)(9#64#65)(0 4176)(6#64#67)(5(1 2)140735332487248 140737488355328)(4(1 2)16)(7#64#67#28(0 24))(5(0 24)1 4611686018427387904)(4#72(1 0))(0#2#73)(2 0(1 2)(0 -64))(2#75)(9(1 11))(18(1 10))(21#45)(0 719224)(1#80)(0 18446744073709551608)(11#82)(12(1 12))(9#28(0 24))(1 1358140)(2 6(1 12)(0 3))(4 0(0 8)#87)(2 0#88(0 8)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_casan_R0 317%positive "((0#2(1 0))(((719372((1(1 1))(2(1 2))#3#4#5#6#7(8(1 8))(9(1 9))#9(11(0 0))(12(0 0))#10#11#12#13#14(18(1 18))#15#16(21(1 21))#17#18#19#20#21#22#23#24#25#26)()((0#27 1(0 0))(0#28 1(0 0))#30#32#34#36#38#40#42#43#46(9((1 10)2)(0 22))#47#48#49#52#56#60#63#66#68#69#70#71(1((2 6#8(0 3))2147450880)(0 1))))(1 719372)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_casan_R0 330%positive "(#74(((521552((1(0 719316))#76#3#4#5#6#7(8(1 32))#77#9(11(1 11))(12(1 32))#10#11#12#13#14#78(19#8)#16#79#17#18#19#20#21#22#23#24#25#26)()(#72(0#28 1(4 0(0 2)(1 32)))#30#32#34#36#38#40#42#43#46(9#27(0 23))#47#48#49#52#56#60#63#66#68#69#70#71(5(1 32)1 22)(1((2 6(2 0(2 0(1 10)(1 32))(0 1))(0 3))2147450880)(0 1))))(1 521552)))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_casan_R0 223%positive "(#74(((1358140(#81#76#3#4#5#6#7(8(0 23))#77(10(0 26))#83#84#10#11#12#13#14#78#15(20(0 26))#79#17#18#19#20#21#22#23#24#25#26)()(#72#30#32#34#36#38#40#42#43#46#85#47#48#49#52#56#60#63#66#68#69#70#71(5(1 12)23 23)))#86))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_strinit_casan_R0 223%positive "(#74(((1358140(#81#76#3#4#5#6#7(8(1 12))#77(10#89)#83#84#10#11#12#13#14#78#15(20#89)#79#17#18#19#20#21#22#23#24#25#26)()(#72#30#32#34#36#38#40#42#43#46#85#47#48#49#52#56#60#63#66#68#69#70#71(5(1 12)24 67108863)))#86))()())"%pstring.
