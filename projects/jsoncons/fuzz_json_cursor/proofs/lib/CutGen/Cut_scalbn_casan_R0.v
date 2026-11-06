(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm8CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodecD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_scalbn_casan_T.
Definition dict_Cut_scalbn_casan_R0 : CCDD.pt := CCDD.mk_table 747%positive "((1284120 1284244 1284268 1284140 1284164 1284196 1284220 1284260 1284264 1284120 1284144 1284168 1284192 1284216 1284240 1284264 1330948 1331976)(0#1)(0 1984)(5#3 1 4611686018427387904)(0 1099511627776)(5#5 0 4611686018427387904)(0 1099511625792)(5#7 0 4611686018427387904)(5#5 1 4611686018427387904)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 10))(0 18446744073709550593)(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(5(1 2)140735332483072 140737488355328)(4(1 2)16)(3 65536 1392640)(0 1024)(2 3(1 10)#44)(5#7 1 4611686018427387904)(0 4607182418800017408))"%pstring.
Definition o0 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_casan_R0 791%positive "((0#2(3(0#2(3(0#2(4#4(4#6(4#8(1 0)))))(0#2(0(4 1)(0#2(4#9(1 1)))))))(11 10 1024 18446744073709551615(0#2(0(4 1)(0#2(4#9(1 2))))))))(((1284244(#10#11#12#13#14#15#16#17#18#19(11#20)#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()(#41#42#43#4#6#8))(0 1((46(1 31))(45(1 30))(44(1 29))(43(1 28))(42(1 17))(41(1 16))(40(1 15))(39(1 14))(38(1 13))(37(1 12))(36#20)(35(1 10))(34(1 7))(33(1 6))(32(1 5)))))((1284196(#10#11#12#13#14#15#16#17#18#19(11(0 18446744073709549624))#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()(#9(5(2 3#20(1 10))0 0)(5#45 1 1)#41#42#43))(1 1284196))((1284140(#10#11#12#13#14#15#16#17#18#19(11(0 2047))#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()(#9(5(1 10)1024 18446744073709551615)(5#45 0 0)#41#42#43))(1 1284140)))()())"%pstring.
Definition o1 : CAD.pout := CCDD.dec_pout_t dict_Cut_scalbn_casan_R0 290%positive "((0#2(4#46(1 0)))(((1284260(#10#11#12#13(5(1 32))(6(1 33))(7(1 34))#17#18(10(2 0(4 0(0 4503599627370496)(1 35))#47))(11#47)(12(1 37))(13(1 38))(14(1 39))(15(1 40))(16(1 41))(17(1 42))#27#28#29#30#31#32#33#34#35#36(28(1 43))(29(1 44))(30(1 45))(31(1 46)))()(#46#41#42#43))(1 1284260)))()())"%pstring.
