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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_db_xasan_T Cut_db_xasan_R0 Cut_db_xasan_R1.
Definition dict_Cut_db_xasan_R2 : CCD.pt := CCD.mk_table 1423%positive "((4 0(0 -1)(1 48))(2 0(1 11)#1)(2 0(1 10)#2)(2 0#3(0 1))(2 6(1 13)(0 3))(0 2147450880)(2 0(1 10)(1 11))(3 1444792 1448528)((0 0)1482488)(0#9 8#6)(4 0(0 64)(1 48))(2 0#11(0 3))(5#12 1 4611686018427387904)(2 0(1 49)(0 -1))(5#14 0 0)(5(1 49)1 1)(2 1(1 49)(0 0))(2 4#17(0 1))(5#18 0 0)(2 0#1(0 1))(5#20 0 140737472888824)(2 4#4#7)(5#22 0 0)(5#3 7077888 140737479966712)(5#4 6946817 140737479966713)(2 0#11(0 4))(5#26 1 4611686018427387904)((1 13)0)(0#28 8(1 32))(5(1 11)1 25)(5(1 12)0 255)((1 10)0)(9#32(1 11))(5(1 10)7077888 140737479966688)(4(1 10)8)(2 6(1 10)(0 3))(#36 2147450880)(1#37(0 4))((0 0)2147446784)(0 17592186048512)(7#39#40#32(0 32))(5(1 13)7077888 140737488355320)(4(1 13)8)(#5 2147450880)(1#44(0 1))(7#39#40#28(0 8))(5(1 32)7077888 140737479966696)(4(1 32)8)((1 32)0)(7#39#40#49(0 24))((1 2)-4480)(0 4368)(9#51#52)(0 4480)(6#51#54)(5(1 2)140735332487552 140737488355328)(4(1 2)16)(7#39#40#51#54)(7#51#54#32(0 32))(7#51#54#28(0 8))(7#51#54#49(0 24))(7#32(0 32)#49(0 24))(7#28(0 8)#49(0 24))(7#32(0 32)#28(0 8))((1 2)-8)(0#65 8(1 1))((1 2)-16)(0#67 8(1 8))((1 2)-24)(0#69 8(1 9))((1 2)-32)(0#71 8(1 18))((1 2)-40)(0#73 8(1 19))((1 2)-48)(0#75 8(1 20))((1 2)-56)(0#77 8(1 21))((1 2)-64)(0#79 8(1 22))((1 2)-72)(0#81 8(1 23))((1 2)-80)(0#83 8(1 24))((1 2)-88)(0#85 8(1 25))((1 2)-96)(0#87 8(1 26))((1 2)-104)(0#89 8(1 27))(5(1 48)1 25)(5#2 0 24)(5(1 49)0 1)(5(1 66)0 255)(2 0#11(0 2))(5#95 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_db_xasan_R2 398%positive "(815632((1 0)(1 84)(2 0(1 2)(0 -112))(1 3)(1 4)(1 85)(1 86)(1 87)(1 13)(1 12)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 94)(1 95)#4#4(2 0#5#6)#7(1 49)(0 10)(0 68)#6(0 43)(0 101)(1 96)(1 97)(1 98)(1 99))(#8#10#13#15#16#19#21#23#24#25#8#10#27#8#10#29#30#31#33#34#35#38#41#42#43#45#46#47#48#50#53#55#56#57#58#59#60#61#62#63#64#66#68#70#72#74#76#78#80#82#84#86#88#90#91#92#93#94)100(((1 2)-4480#54))()#95)"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_db_xasan_R2 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints6.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_db_xasan_R2 631%positive "((0(0(815348 815468 815484 815504 815764 815476 1041292 815476 815468 815484 815504 815484 1387168 1388196))(16 0(1 0)))(((1041292((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 85))(6(1 86))(7(1 87))(8(1 8))(9(1 9))(10(1 32))(11(0 48))(12(1 90))(13(1 91))(14(1 92))(15(1 93))(16(1 94))(17(1 95))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 96))(29(1 97))(30(1 98))(31(1 99)))()(#96#8#10#13#15#16#19#21#23#24#25#8#10#27#8#10#29#30#31#33#34#35#38#41#42#43#45#46#47#48#50#53#55#56#57#58#59#60#61#62#63#64#66#68#70#72#74#76#78#80#82#84#86#88#90#91#92#93#94))(1 1041292)))((0#96))())"%pstring.
