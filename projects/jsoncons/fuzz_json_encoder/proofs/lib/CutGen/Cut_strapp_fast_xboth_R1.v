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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_strapp_fast_xboth_T Cut_strapp_fast_xboth_R0.
Definition dict_Cut_strapp_fast_xboth_R1 : CCD.pt := CCD.mk_table 1169%positive "((2 0(1 33)(1 34))(3 1433600 1466368)((0 0)1497016)(0 2147450880)(0#3 8#4)(#1 0)(2#6(1 12)1)(5(0 100)1 4611686018427387904)(4 0(0 -1)(1 12))(4 0(0 2)(1 32))(4 0(0 -1)(1 33))(2 0#10#11)(2 0#9#12)(2 0#13(0 -1))(5#14 0 140737488355326)(2 0#12(0 -1))(2 4#16(1 12))(5#17 0 0)(5(1 12)1 67108863)(5(1 33)0 67108862)(5#12 2 140737488355328)(5#16 1 140737488355327)(2 0#10(0 1))(6 0 0 1#23)(2 9#24(0 1))(5#25 1 1)((1 2)-40)(0#27 8(1 19))((1 2)-32)(0#29 8(1 18))((1 2)-24)(0#31 8(1 9))((1 2)-16)(0#33 8(1 8))((1 2)-8)(0#35 8(1 1))((1 10)0)(0#37 8#23)((1 10)8)((1 10)16)(0#40 8(1 34))(5(1 32)12 70368744177664)(5(1 33)0 67108864)((1 34)0)(2#44(1 33)0)(6#44#10)(5(1 34)4096 140737488355328)(4(1 34)16)(5#16 0 140737488355328)(6#37(0 24))(5(1 10)7094272 140737488351232)(4(1 10)8)((1 2)-4368)(0 4328)(9#53#54)(0 4368)(6#53#56)(5(1 2)140735332487440 140737488355328)(4(1 2)16)(7#53#56#37(0 24))(7#53#56#44#10)(7#37(0 24)#44#10)(5(1 12)1 67108864)(2 0(1 12)(1 33))(5#64 1 67108863)((1 11)0)(2#66(1 12)1)(9#66(1 12))(5(1 11)4096 140737488355328)(2 0(1 11)(1 12))(5#70 4096 140737488355328)(7#53#56#66(1 12))(7#37(0 24)#66(1 12))(7#44#10#66(1 12))(5#14 0 140737488355328)(2 0(1 12)#1))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_strapp_fast_xboth_R1 434%positive "(1055600((1 0)(1 40)(2 0(1 2)(0 -48))(1 3)(1 4)(1 41)(1 42)(1 43)(1 10)(1 12)#1(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 33)(1 34)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#2#5#7#8#15#18#19#20#21#22#26#28#30#32#34#36#2#5#38(0#39 8(1 33))#41#42#43#45(9#44#10)#46#47#48#49(9#37(0 24))#50#51#52#55#57#58#59#60#61#62#63#65#67#68#69#71#72#73#74#75)56(((1 2)-4368#56)((1 10)0(0 24))((1 34)0#10))()(0 99))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_strapp_fast_xboth_R1 14%positive "(((1 34)#10))"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_strapp_fast_xboth_R1 581%positive "((0(0(1055420 1055668 527112 1402040 1403068))(1 0))(((1055668((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 8))(9(1 9))(10(1 10))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()((0(#76 0)1(0 0))(0#39 8#64)#7#8#15#18#19#20#21#22#26#28#30#32#34#36#38#41#42#43#45(9#44#64)(9(#76 1)#14)#46#47#48#49(9#37(0 8))(9#40(0 8))#50#51#52#55#57#58#59#60#61#62#63#65#67#68#69#71#72#73#74#75))(1 1055668)))()())"%pstring.
