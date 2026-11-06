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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_pdtor_casan_T Cut_pdtor_casan_R0.
Definition dict_Cut_pdtor_casan_R1 : CCD.pt := CCD.mk_table 1200%positive "((2 0(1 2)(0 -32))(0 2147450880)(3 1359872 1392640)((0 0)1427896)(0#4 8#2)(5(0 10)1 4611686018427387904)((1 2)-32)(2 0(1 10)(0 248))(0#7 8#8)((1 10)0)(0 1363968)(0#10 8#11)((1 2)-24)(0#13 8(1 9))((1 2)-16)(0#15 8(1 8))((1 2)-8)(0#17 8(1 1))((1 10)24)(0#19 1(0 0))((1 10)48)(0#21 1(0 0))((1 10)72)(0#23 1(0 0))((1 10)96)(0 1364920)(0#25 8#26)((1 10)128)(2 0(1 10)(0 96))(0#28 8#29)((1 10)224)(0#31 8(1 36))((1 10)240)(0#33 8(1 35))(6 0 0 1(1 36))(2 9#35(0 1))(5#36 1 1)(5(1 36)265 140737488355328)((1 10)8)(9#39(0 16))((1 10)232)(9#41(0 8))(6#10(0 272))(5(1 10)1048576 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#46 2147450880)(1#47(0 34))((0 0)2147446784)(0 17592186048512)(7#49#50#10(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(5(1 33)0 4096)(4 0(0 -1)(1 33))(2 0#56(1 34))(5#57 0 4096)(5(1 35)4096 140737479966720)(4(1 35)16)((1 2)-4272)(0 4240)(9#61#62)(0 4272)(6#61#64)(5(1 2)140735332487344 140737488355328)(4(1 2)16)(2 6#1(0 3))(#68 2147450880)(1#69(0 1))(7#61#64#10(0 272))((1 32)0)(7#61#64#72(1 34))(7#10(0 272)#72(1 34))((1 35)0)(2 0(1 36)(0 -1))(7#61#64#75#76)(7#10(0 272)#75#76)(7#72(1 34)#75#76)(7#49#50#72(1 34))(7#49#50#75#76)(5(0 9)1 4611686018427387904))"%pstring.

Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pdtor_casan_R1 364%positive "(725272((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)#2(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#3#5#6#9#12#14#16#18#20#22#24#27#30#32#34#37#38#40#42#43#44#45#48#51#52#53#54#55#58#59#60#63#65#66#67#70#71#73#74#77#78#79#80#81)56(((1 2)-4272#64)((1 10)0(0 272)))()(0 9))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pdtor_casan_R1 14%positive "(((1 35)#76))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_casan_R1 542%positive "((0(0(725196 725688 726216 975272 1330948 1331976))(4#82(1 0)))(((975272((1(0 725348))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 10))(9#2)(10(1 35))(11(4 0(0 2)(2 6(1 36)(0 1))))(12(1 36))(13(0 0))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#82#3#5#6#9#12#14#16#18#20#22#24#27#30#32#34#37#38#40#42#43#44#45#48#51#52#53#54#55#58#59#60#63#65#66#67#70#71#73#74#77#78#79#80#81))(1 975272)))()())"%pstring.
