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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_int64_root_xasan_T Cut_visit_int64_root_xasan_R0.
Definition dict_Cut_visit_int64_root_xasan_R1 : CCD.pt := CCD.mk_table 994%positive "((2 0(1 10)(0 264))(2 0(1 10)(0 272))(0 2147450880)(5(1 48)0 1125899906842624)(3 1444792 1448528)((0 0)1482488)(0#6 8#3)(0 1048576)(5#8 1 4611686018427387904)((1 2)-72)(0#10 8(1 23))((1 2)-64)(0#12 8(1 22))((1 2)-56)(0#14 8(1 21))((1 2)-48)(0#16 8(1 20))((1 2)-40)(0#18 8(1 19))((1 2)-32)(0#20 8(1 18))((1 2)-24)(0#22 8(1 9))((1 2)-16)(0#24 8(1 8))((1 2)-8)(0#26 8(1 1))(3 65536 1449984)((1 10)8)(0#29 8(1 32))((1 10)40)(0#31 8(0 120))((1 10)296)(5(1 37)0 18446744073709551615)(6#33(0 8))(5(1 10)7077888 140737479966312)(4(1 10)8)(2 6(1 10)(0 3))(#38 2147450880)(1#39(0 51))((0 0)2147446784)(0 17592186048512)((1 10)0)(7#41#42#43(0 408))(5(1 32)7077888 140737479966696)(4(1 32)8)(2 6(1 32)(0 3))(#47 2147450880)(1#48(0 3))((1 32)0)(7#41#42#50(0 24))((1 2)-13824)(0 13744)(9#52#53)((1 2)-80)(9#55(0 8))(0 13824)(6#52#57)(5(1 2)140735332496896 140737488355328)(4(1 2)32)(7#41#42#52#57)(7#52#57#43(0 408))(7#52#57#50(0 24))(7#43(0 408)#50(0 24))((1 10)264)(0#65 8(1 34))((1 10)272)(0#67 8(1 34)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_int64_root_xasan_R1 413%positive "(739732((1 0)(1 49)(2 0(1 2)(0 -80))(1 3)(1 4)(1 50)(1 51)(1 52)#1#2(1 48)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(2 0(1 10)(0 296))(1 10)(1 11)#3(2 0(2 6#1(0 3))#3)(2 0(2 6#2(0 3))#3)(1 24)(1 25)(1 26)(1 27)(1 61)(1 62)(1 63)(1 64))(#4#5#7#9#11#13#15#17#19#21#23#25#27#5#7#28#30#32(0#33 8(1 37))#34#35#36#37#40#44#45#46#49#51#54#56#58#59#60#61#62#63#64#66#68)65(((1 2)-13824#57)((1 10)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_int64_root_xasan_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_visit_int64_root_xasan_R1 564%positive "((0(0(739428 739864 765616 1040708 770528 832876 832992 766156 767788 769828 1387168 1388196))(1 0))(((739864((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 50))(6(1 51))(7(1 52))(8(1 8))(9(1 9))(10(0 1))(11(1 34))(12(1 55))(13(1 56))(14(1 57))(15(1 58))(16(1 59))(17(1 60))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 61))(29(1 62))(30(1 63))(31(1 64)))()((0#33 8(2 0(1 37)(1 48)))#4#5#7#9#11#13#15#17#19#21#23#25#27#5#7#28#30#32#34#35#36#37#40#44#45#46#49#51#54#56#58#59#60#61#62#63#64#66#68))(1 739864)))()())"%pstring.
