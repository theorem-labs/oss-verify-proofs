(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_vec_dtor_xboth_T Cut_vec_dtor_xboth_R0 Cut_vec_dtor_xboth_R1.
Definition dict_Cut_vec_dtor_xboth_R2 : CCD.pt := CCD.mk_table 2267%positive "((2 0(1 2)(0 -32))(0 2147450880)(2 6(1 10)(0 3))(2 0#3#2)((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)#2(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)#4(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))(3 1459384 1463120)((0 0)1497016)(0#7 8#2)(5(0 7)1 4611686018427387904)(5(0 8)1 4611686018427387904)((1 32)8)(0#11 8(1 33))(2 0(1 34)(0 1))(5#13 1 1)(5(1 34)0 0)(2 0(1 33)(1 34))(2 1(1 33)#16)(2 4#17(0 1))(5#18 1 1)((1 2)-32)(0#20 8(1 18))((1 2)-24)(0#22 8(1 9))((1 2)-16)(0#24 8(1 8))((1 2)-8)(0#26 8(1 1))((1 10)0)(0#28 8(1 32))(5(1 10)1048576 140737488355320)(4(1 10)8)(#3 2147450880)(1#32(0 1))((0 0)2147446784)(0 17592186048512)(7#34#35#28(0 8))((1 32)0)(0#37 8(1 33))((1 32)16)(2 0(1 33)(1 35))(0#39 8#40)(6#37(0 24))(5(1 32)1048576 140737488354816)(4(1 32)8)(2 6(1 32)(0 3))(#45 2147450880)(1#46(0 3))(7#34#35#37(0 24))(5(1 33)17594333495296 140737479966720)(4(1 33)16)(5(1 35)1 4096)(4 0(0 -1)(1 34))(2 0#52(1 35))(5#53 0 4096)(5(1 34)0 4096)((1 2)-4192)(0 4152)(9#56#57)(0 4192)(6#56#59)(5(1 2)140735332487264 140737488355328)(4(1 2)16)(7#56#59#37(0 24))(7#56#59#28(0 8))(7#28(0 8)#37(0 24))((1 33)0)(7#56#59#66(1 35))(7#37(0 24)#66(1 35))(7#28(0 8)#66(1 35))(2 6(1 33)(0 3))(#70 2147450880)(2 0(1 35)(0 7))(2 6#72(0 3))(7#46(0 3)#71#73)(7#32(0 1)#71#73)(7#37(0 24)#71#73)(7#28(0 8)#71#73)(#6#8#9#6#8#10#12#14#15#19#21#23#25#27#29#30#31#33#36#38#41#42#43#44#47#48#49#50#51#54#55#58#60#61#62#63#64#65#67#68#69#74#75#76#77)((1 2)-4192#59)((1 32)0(0 24))(#79#80)((1 33)(1 35))(732544 732784 1046256 733160 732972 1402040 1403068)(0#83)(0#84(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10(1 33))(11(1 35))(12(0 0))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71))(#86#87#88#89#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110#111#112#113#114#115#116)(1 1046256)(5#52 18446744073709547520 18446744073709551615)(2 0#52(0 -1))(5#120 0 18446744073709551614)(5(1 34)1 4096)(5#18 0 0)(#6#8#9#6#8#10#12#119#119#121#122#123#21#23#25#27#29#30#31#33#36#38#41#42#43#44#47#48#49#50#51#54#55#58#60#61#62#63#64#65#67#68#69#74#75#76#77))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xboth_R2 27%positive "(732668#5#78 72#81()(0 6))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xboth_R2 6%positive "(#82)"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xboth_R2 36%positive "(#85(((1046256#117()#78)#118))()())"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_vec_dtor_xboth_R2 28%positive "(732668#5#124 72#81()(0 6))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_vec_dtor_xboth_R2 6%positive "(#82)"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_vec_dtor_xboth_R2 37%positive "(#85(((1046256#117()#124)#118))()())"%pstring.
