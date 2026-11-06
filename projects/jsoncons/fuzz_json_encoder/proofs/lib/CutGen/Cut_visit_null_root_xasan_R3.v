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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xasan_T Cut_visit_null_root_xasan_R0 Cut_visit_null_root_xasan_R1 Cut_visit_null_root_xasan_R2.
Definition dict_Cut_visit_null_root_xasan_R3 : CCD.pt := CCD.mk_table 1397%positive "((2 0(1 2)(0 -80))(2 0(1 10)(0 264))(2 0(1 10)(0 272))(2 0(1 10)(0 296))(2 0(1 10)(0 8))(0 154272)(0 2147450880)(2 6#2(0 3))(2 0#8#7)(2 6#3(0 3))(2 0#10#7)(3 1444792 1448528)((0 0)1482488)(0#13 8#7)(0 1048574)(5#15 1 4611686018427387904)(5(1 69)4 4)((0 0)6931864)(0#18 1(0 1))((0 0)6931865)(0#20 1(0 1))((0 0)6931848)(0#22 8#6)((0 0)6931856)(0#24 8(0 4))(0 1048575)(5#26 1 4611686018427387904)(5(1 53)4 4)(0 1048576)(5#29 1 4611686018427387904)((1 2)-80)(0#31 8(1 24))((1 2)-72)(0#33 8(1 23))((1 2)-64)(0#35 8(1 22))((1 2)-56)(0#37 8(1 21))((1 2)-48)(0#39 8(1 20))((1 2)-40)(0#41 8(1 19))((1 2)-32)(0#43 8(1 18))((1 2)-24)(0#45 8(1 9))((1 2)-16)(0#47 8(1 8))((1 2)-8)(0#49 8(1 1))(3 65536 1449984)((1 10)8)(0#52 8(1 32))((1 10)40)(0#54 8(0 120))((1 10)296)(0#56 8(1 37))(5(1 37)0 18446744073709551615)(6#56(0 8))(5(1 10)7077888 140737479966312)(4(1 10)8)(2 6(1 10)(0 3))(#62 2147450880)(1#63(0 51))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#65#66#67(0 408))(5(1 32)7077888 140737479966696)(4(1 32)8)(2 6(1 32)(0 3))(#71 2147450880)(1#72(0 3))((1 32)0)(7#65#66#74(0 24))((1 2)-13824)(0 13744)(9#76#77)(0 13824)(6#76#79)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#65#66#76#79)(7#76#79#67(0 408))(7#76#79#74(0 24))(7#67(0 408)#74(0 24))((1 10)264)(0#87 8(1 34))((1 10)272)(0#89 8(1 34))(7#76#79#22(0 18))(7#67(0 408)#22(0 18))(7#74(0 24)#22(0 18))(0 1048573)(5#94 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xasan_R3 370%positive "(751656((1 0)(1 80)#1(1 3)(1 4)(1 81)(1 82)(1 83)#2#3(1 84)(1 85)(1 86)(1 87)(1 88)(1 89)(1 90)(1 91)#4(1 10)#5#6#7#9#11(1 25)(1 26)(1 27)(1 92)(1 93)(1 94)(1 95))(#12#14#16#17#19#21#23#25#12#14#27#28#12#14#30#32#34#36#38#40#42#44#46#48#50#12#14#51#53#55#57#58#59#60#61#64#68#69#70#73#75#78#80#81#82#83#84#85#86#88#90#91#92#93)96(((1 2)-13824#79)((1 10)296(0 8)))()#94)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xasan_R3 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xasan_R3 573%positive "((0(0(751316 751796 765616 1040708 770528 832876 832992 766156 767788 769828 1387168 1388196))(4#95(1 0)))(((770528((1(0 751660))(2#1)(3(1 3))(4(1 4))(5(1 81))(6(1 82))(7(1 83))(8#2)(9#3)(10(1 84))(11(1 85))(12(1 86))(13(1 87))(14(1 88))(15(1 89))(16(1 90))(17(1 91))(18#4)(19(1 10))(20#5)(21#6)(22#7)(23#9)(24#11)(25(1 25))(26(1 26))(27(1 27))(28(1 92))(29(1 93))(30(1 94))(31(1 95)))()(#95#12#14#16#17#19#21#23#25#12#14#27#28#12#14#30#32#34#36#38#40#42#44#46#48#50#12#14#51#53#55#57#58#59#60#61#64#68#69#70#73#75#78#80#81#82#83#84#85#86#88#90#91#92#93))(1 770528)))()())"%pstring.
