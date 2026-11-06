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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_fpclassifyl_casan_T.
Definition dict_Cut_fpclassifyl_casan_R0 : CCDD.pt := CCDD.mk_table 628%positive "((1279408 1279452 1279464 1279472 1279408 1279432 1279456 1330948 1331976)(0#1)(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(0 65536)(4 0#12(1 11))(2 6#13(0 16))(2 8#14(1 10))(2 4#15(0 1))(11#14)(4 0(0 2)(1 11))(2 6#18(0 49))(12#19)(0 32767)(13#21)(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(2 1#19#21)(2 4#41(0 1))(5(1 2)140735332483072 140737488355328)(4(1 2)16)(2 1#19(0 0))(2 4#45(0 1))(5(1 11)0 18446744073709551613)(5(1 11)0 18446744073709551614)(5#42 0 0))"%pstring.
Definition o0 : CAD.pout := CCDD.dec_pout_t dict_Cut_fpclassifyl_casan_R0 918%positive "((0#2(3(11 11 2 18446744073709551615(11 11 3 18446744073709551615(0#2(0#2(1 0)))))(11 11 0 18446744073709551614(11 11 0 18446744073709551613(0#2(3(11 11 0 18446744073709551612(11 11 0 18446744073709551611(0#2(1 1))))(11 11 2 18446744073709551613(11 11 3 18446744073709551613(0#2(1 2))))))))))(((1279464(#3#4#5#6#7#8#9#10#11(10#16)#17#20#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()((5(1 11)3 18446744073709551615)(5(1 11)2 18446744073709551615)(5#42 1 1)#43#44))(1 1279464))((1279452(#3#4#5#6#7#8#9#10#11(10(2 5#16(0 3)))#17#20#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()((5(1 11)0 18446744073709551611)(5(1 11)0 18446744073709551612)(5#46 1 1)#47#48#49#43#44))(1 1279452))((1279472(#3#4#5#6#7#8#9#10#11(10(0 4))#17#20#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38#39#40)()((5(1 11)3 18446744073709551613)(5(1 11)2 18446744073709551613)(5#46 0 0)#47#48#49#43#44))(1 1279472)))()())"%pstring.
