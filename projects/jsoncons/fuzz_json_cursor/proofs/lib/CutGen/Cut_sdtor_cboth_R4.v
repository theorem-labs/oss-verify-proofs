(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_sdtor_cboth_T Cut_sdtor_cboth_R0 Cut_sdtor_cboth_R1 Cut_sdtor_cboth_R2 Cut_sdtor_cboth_R3.
Definition dict_Cut_sdtor_cboth_R4 : CCD.pt := CCD.mk_table 1052%positive "((3 1368064 1400832)((0 0)1432824)(0 2147450880)(0#2 8#3)(5(0 9)1 4611686018427387904)(5(0 10)1 4611686018427387904)(5(0 11)1 4611686018427387904)((1 10)88)(0 1384352)(0#8 8#9)((1 2)-40)(0#11 8(1 19))((1 2)-32)(0#13 8(1 18))((1 2)-24)(0#15 8(1 9))((1 2)-16)(0#17 8(1 8))((1 2)-8)(0#19 8(1 1))((1 10)24)(0 1384448)(0#21 8#22)((1 10)8)(0 1369640)(0#24 8#25)(5(0 12)1 4611686018427387904)((1 10)32)(0 6884304)(0#28 8#29)((1 10)264)(0#31 8(1 32))((1 10)272)(0 16384)(0#33 8#34)((1 10)136)(0#36 8#29)((1 10)144)(0#38 8(0 0))((1 10)152)(0#40 8(0 0))((1 10)160)(0#42 8(0 0))((1 10)176)(0#44 8(0 0))((1 10)200)(0#46 8(0 0))((1 10)0)(9#48(0 8))((1 10)16)(9#50(0 8))(6#48(0 592))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#55 2147450880)(1#56(0 74))((0 0)2147446784)(0 17592186048512)(7#58#59#48(0 592))(5(1 32)4096 140737479966720)(4(1 32)16)((1 2)-4224)(0 4184)(9#63#64)(0 4224)(6#63#66)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(7#63#66#48(0 592))((1 32)0)(7#63#66#71#34)(7#48(0 592)#71#34)(7#58#59#71#34)(5(0 8)1 4611686018427387904))"%pstring.

Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_sdtor_cboth_R4 402%positive "(1011048((1 0)(1 88)(2 0(1 2)(0 -48))(1 3)(1 4)(1 89)(1 90)(1 91)(2 0(1 10)(0 88))(0 0)(1 92)(1 93)(1 94)(1 95)(1 96)(1 97)(1 98)(1 99)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 100)(1 101)(1 102)(1 103))(#1#4#5#1#4#6#1#4#7#10#12#14#16#18#20#23#26#1#4#27#1#4#30#32#35#37#39#41#43#45#47#49#51#52#53#54#57#60#61#62#65#67#68#69#70#72#73#74)104(((1 2)-4224#66)((1 10)0(0 592)))()(0 8))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_sdtor_cboth_R4 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints3.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_cboth_R4 522%positive "((0(0(728272 980676 527796 1336512 1337540))(4#75(1 0)))(((527796((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 89))(6(1 90))(7(1 91))(8(1 8))(9(1 9))(10(0 0))(11(1 93))(12(1 94))(13(1 95))(14(1 96))(15(1 97))(16(1 98))(17(1 99))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 100))(29(1 101))(30(1 102))(31(1 103)))()(#75#1#4#5#1#4#6#1#4#7#10#12#14#16#18#20#23#26#1#4#27#1#4#30#32#35#37#39#41#43#45#47#49#51#52#53#54#57#60#61#62#65#67#68#69#70#72#73#74))(1 527796)))()())"%pstring.
