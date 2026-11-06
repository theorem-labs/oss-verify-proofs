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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_string_root_xasan_T Cut_visit_string_root_xasan_R0.
Definition dict_Cut_visit_string_root_xasan_R1 : CCD.pt := CCD.mk_table 1342%positive "((2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 2147450880)(3 1444792 1448528)((0 0)1482488)(0#5 8#3)(0 1048576)(5#7 1 4611686018427387904)((1 2)-88)(0#9 8(1 25))((1 2)-80)(0#11 8(1 24))((1 2)-72)(0#13 8(1 23))((1 2)-64)(0#15 8(1 22))((1 2)-56)(0#17 8(1 21))((1 2)-48)(0#19 8(1 20))((1 2)-40)(0#21 8(1 19))((1 2)-32)(0#23 8(1 18))((1 2)-24)(0#25 8(1 9))((1 2)-16)(0#27 8(1 8))((1 2)-8)(0#29 8(1 1))(3 65536 1449984)((1 10)8)(0#32 8(1 32))((1 10)40)(0#34 8(0 120))(5(1 37)0 18446744073709551615)((1 10)296)(6#37(0 8))(5(1 10)7077888 140737479966312)(4(1 10)8)(2 6(1 10)(0 3))(#41 2147450880)(1#42(0 51))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#44#45#46(0 408))(5(1 32)7077888 140737479966696)(4(1 32)8)(2 6(1 32)(0 3))(#50 2147450880)(1#51(0 3))((1 32)0)(7#44#45#53(0 24))((1 2)-13824)(0 13728)(9#55#56)((1 2)-96)(9#58(0 8))(0 13824)(6#55#60)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#44#45#55#60)(7#55#60#46(0 408))(7#55#60#53(0 24))(7#46(0 408)#53(0 24))((1 10)264)(0#68 8(1 34))((1 10)272)(0#70 8(1 34))(5(1 12)0 255)(5(1 11)7077888 140737479966704)(4(1 11)8)(2 6(1 11)(0 3))(#75 2147450880)(1#76(0 2))((1 11)0)(7#44#45#78(0 16))(7#55#60#78(0 16))(7#46(0 408)#78(0 16))(7#53(0 24)#78(0 16))(#4#6#8#10#12#14#16#18#20#22#24#26#28#30#4#6#31#33#35#36#38#39#40#43#47#48#49#52#54#57#59#61#62#63#64#65#66#67#69#71#72#73#74#77#79#80#81#82))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_string_root_xasan_R1 278%positive "(752920((1 0)(1 48)(2 0(1 2)(0 -96))(1 3)(1 4)(1 49)(1 50)(1 51)#1#2(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 14)(1 13)(1 12)(1 10)(1 11)#3(2 0(2 6#1(0 3))#3)(2 0(2 6#2(0 3))#3)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))#83 64(((1 2)-13824#60)((1 10)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_string_root_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_string_root_xasan_R1 429%positive "((0(0(752584 753032 765616 1040708 770528 832876 832992 766156 767788 769828 1387168 1388196))(1 0))(((753032((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10(0 1))(11(1 34))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()#83)(1 753032)))()())"%pstring.
