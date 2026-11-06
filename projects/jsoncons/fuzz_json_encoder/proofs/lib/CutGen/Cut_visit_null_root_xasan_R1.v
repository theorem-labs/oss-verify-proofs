(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xasan_T Cut_visit_null_root_xasan_R0.
Definition dict_Cut_visit_null_root_xasan_R1 : CCD.pt := CCD.mk_table 1307%positive "((2 0(1 2)(0 -80))(2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 154272)(2 0(1 10)(0 296))(2 0(1 10)(0 8))(0 2147450880)(2 6#2(0 3))(2 0#8#7)(2 6#3(0 3))(2 0#10#7)(5(1 53)4 4)((0 0)6931864)(0#13 1(0 1))((0 0)6931865)(0#15 1(0 1))((0 0)6931848)(0#17 8#4)((0 0)6931856)(0#19 8(0 4))(3 1444792 1448528)((0 0)1482488)(0#22 8#7)(0 1048576)(5#24 1 4611686018427387904)((1 2)-80)(0#26 8(1 24))((1 2)-72)(0#28 8(1 23))((1 2)-64)(0#30 8(1 22))((1 2)-56)(0#32 8(1 21))((1 2)-48)(0#34 8(1 20))((1 2)-40)(0#36 8(1 19))((1 2)-32)(0#38 8(1 18))((1 2)-24)(0#40 8(1 9))((1 2)-16)(0#42 8(1 8))((1 2)-8)(0#44 8(1 1))(3 65536 1449984)((1 10)8)(0#47 8(1 32))((1 10)40)(0#49 8(0 120))((1 10)296)(0#51 8(1 37))(5(1 37)0 18446744073709551615)(6#51(0 8))(5(1 10)7077888 140737479966312)(4(1 10)8)(2 6(1 10)(0 3))(#57 2147450880)(1#58(0 51))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#60#61#62(0 408))(5(1 32)7077888 140737479966696)(4(1 32)8)(2 6(1 32)(0 3))(#66 2147450880)(1#67(0 3))((1 32)0)(7#60#61#69(0 24))((1 2)-13824)(0 13744)(9#71#72)(0 13824)(6#71#74)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#60#61#71#74)(7#71#74#62(0 408))(7#71#74#69(0 24))(7#62(0 408)#69(0 24))((1 10)264)(0#82 8(1 34))((1 10)272)(0#84 8(1 34))(7#71#74#17(0 18))(7#62(0 408)#17(0 18))(7#69(0 24)#17(0 18))(0 1048575)(5#89 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xasan_R1 349%positive "(751616((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)#2#3#4(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)#5(1 10)#6(1 21)#7#9#11(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#12#14#16#18#20#21#23#25#27#29#31#33#35#37#39#41#43#45#21#23#46#48#50#52#53#54#55#56#59#63#64#65#68#70#73#75#76#77#78#79#80#81#83#85#86#87#88)64(((1 2)-13824#74)((1 10)296(0 8)))()#89)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xasan_R1 548%positive "((0(0(751316 751796 765616 1040708 770528 832876 832992 766156 767788 769828 1387168 1388196))(4#90(1 0)))(((770528((1(0 751624))(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8#2)(9#3)(10#4)(11(1 53))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18#5)(19(1 10))(20#6)(21#4)(22#7)(23#9)(24#11)(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()(#90#12#14#16#18#20#21#23#25#27#29#31#33#35#37#39#41#43#45#21#23#46#48#50#52#53#54#55#56#59#63#64#65#68#70#73#75#76#77#78#79#80#81#83#85#86#87#88))(1 770528)))()())"%pstring.
