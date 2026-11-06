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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_null_root_xasan_T Cut_visit_null_root_xasan_R0 Cut_visit_null_root_xasan_R1.
Definition dict_Cut_visit_null_root_xasan_R2 : CCD.pt := CCD.mk_table 1358%positive "((2 0(1 2)(0 -80))(2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 154272)(2 0(1 10)(0 296))(2 0(1 10)(0 8))(0 2147450880)(2 6#2(0 3))(2 0#8#7)(2 6#3(0 3))(2 0#10#7)(5(1 69)4 4)((0 0)6931864)(0#13 1(0 1))((0 0)6931865)(0#15 1(0 1))((0 0)6931848)(0#17 8#4)((0 0)6931856)(0#19 8(0 4))(3 1444792 1448528)((0 0)1482488)(0#22 8#7)(0 1048575)(5#24 1 4611686018427387904)(5(1 53)4 4)(0 1048576)(5#27 1 4611686018427387904)((1 2)-80)(0#29 8(1 24))((1 2)-72)(0#31 8(1 23))((1 2)-64)(0#33 8(1 22))((1 2)-56)(0#35 8(1 21))((1 2)-48)(0#37 8(1 20))((1 2)-40)(0#39 8(1 19))((1 2)-32)(0#41 8(1 18))((1 2)-24)(0#43 8(1 9))((1 2)-16)(0#45 8(1 8))((1 2)-8)(0#47 8(1 1))(3 65536 1449984)((1 10)8)(0#50 8(1 32))((1 10)40)(0#52 8(0 120))((1 10)296)(0#54 8(1 37))(5(1 37)0 18446744073709551615)(6#54(0 8))(5(1 10)7077888 140737479966312)(4(1 10)8)(2 6(1 10)(0 3))(#60 2147450880)(1#61(0 51))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#63#64#65(0 408))(5(1 32)7077888 140737479966696)(4(1 32)8)(2 6(1 32)(0 3))(#69 2147450880)(1#70(0 3))((1 32)0)(7#63#64#72(0 24))((1 2)-13824)(0 13744)(9#74#75)(0 13824)(6#74#77)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#63#64#74#77)(7#74#77#65(0 408))(7#74#77#72(0 24))(7#65(0 408)#72(0 24))((1 10)264)(0#85 8(1 34))((1 10)272)(0#87 8(1 34))(7#74#77#17(0 18))(7#65(0 408)#17(0 18))(7#72(0 24)#17(0 18))(0 1048574)(5#92 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_null_root_xasan_R2 357%positive "(751624((1 0)(1 64)#1(1 3)(1 4)(1 65)(1 66)(1 67)#2#3#4(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)#5(1 10)#6#4#7#9#11(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#12#14#16#18#20#21#23#25#26#21#23#28#30#32#34#36#38#40#42#44#46#48#21#23#49#51#53#55#56#57#58#59#62#66#67#68#71#73#76#78#79#80#81#82#83#84#86#88#89#90#91)80(((1 2)-13824#77)((1 10)296(0 8)))()#92)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_null_root_xasan_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_null_root_xasan_R2 561%positive "((0(0(751316 751796 765616 1040708 770528 832876 832992 766156 767788 769828 1387168 1388196))(4#93(1 0)))(((1040708((1(0 751656))(2#1)(3(1 3))(4(1 4))(5(1 65))(6(1 66))(7(1 67))(8#2)(9#3)(10(1 32))(11#4)(12(0 4))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18#5)(19(1 10))(20#6)(21#4)(22#7)(23#9)(24#11)(25(1 25))(26(1 26))(27(1 27))(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()(#93#12#14#16#18#20#21#23#25#26#21#23#28#30#32#34#36#38#40#42#44#46#48#21#23#49#51#53#55#56#57#58#59#62#66#67#68#71#73#76#78#79#80#81#82#83#84#86#88#89#90#91))(1 1040708)))()())"%pstring.
