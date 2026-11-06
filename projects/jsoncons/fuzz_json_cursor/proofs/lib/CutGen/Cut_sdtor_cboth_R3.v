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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_sdtor_cboth_T Cut_sdtor_cboth_R0 Cut_sdtor_cboth_R1 Cut_sdtor_cboth_R2.
Definition dict_Cut_sdtor_cboth_R3 : CCD.pt := CCD.mk_table 1058%positive "((2 0(1 2)(0 -48))(2 0(1 10)(0 88))(3 1368064 1400832)((0 0)1432824)(0 2147450880)(0#4 8#5)(5(0 10)1 4611686018427387904)(5(0 11)1 4611686018427387904)((1 10)88)(0 1384352)(0#9 8#10)((1 2)-40)(0#12 8(1 19))((1 2)-32)(0#14 8(1 18))((1 2)-24)(0#16 8(1 9))((1 2)-16)(0#18 8(1 8))((1 2)-8)(0#20 8(1 1))((1 10)24)(0 1384448)(0#22 8#23)((1 10)8)(0 1369640)(0#25 8#26)(5(0 12)1 4611686018427387904)((1 10)32)(0 6884304)(0#29 8#30)((1 10)264)(0#32 8(1 32))((1 10)272)(0 16384)(0#34 8#35)((1 10)136)(0#37 8#30)((1 10)144)(0#39 8(0 0))((1 10)152)(0#41 8(0 0))((1 10)160)(0#43 8(0 0))((1 10)176)(0#45 8(0 0))((1 10)200)(0#47 8(0 0))((1 10)0)(9#49(0 8))((1 10)16)(9#51(0 8))(6#49(0 592))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#56 2147450880)(1#57(0 74))((0 0)2147446784)(0 17592186048512)(7#59#60#49(0 592))(5(1 32)4096 140737479966720)(4(1 32)16)((1 2)-4224)(0 4184)(9#64#65)(0 4224)(6#64#67)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(7#64#67#49(0 592))((1 32)0)(7#64#67#72#35)(7#49(0 592)#72#35)(7#59#60#72#35)(5(0 9)1 4611686018427387904))"%pstring.

Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_sdtor_cboth_R3 361%positive "(1011040((1 0)(1 72)#1(1 3)(1 4)(1 73)(1 74)(1 75)#2(0 0)(1 76)(1 77)(1 78)(1 79)(1 80)(1 81)(1 82)(1 83)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 84)(1 85)(1 86)(1 87))(#3#6#7#3#6#8#11#13#15#17#19#21#24#27#3#6#28#3#6#31#33#36#38#40#42#44#46#48#50#52#53#54#55#58#61#62#63#66#68#69#70#71#73#74#75)88(((1 2)-4224#67)((1 10)0(0 592)))()(0 9))"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_sdtor_cboth_R3 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints2.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_sdtor_cboth_R3 512%positive "((0(0(728272 980676 527796 1336512 1337540))(4#76(1 0)))(((527796((1(0 1011048))(2#1)(3(1 3))(4(1 4))(5(1 73))(6(1 74))(7(1 75))(8#2)(9(0 0))(10(0 0))(11(1 77))(12(1 78))(13(1 79))(14(1 80))(15(1 81))(16(1 82))(17(1 83))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 84))(29(1 85))(30(1 86))(31(1 87)))()(#76#3#6#7#3#6#8#11#13#15#17#19#21#24#27#3#6#28#3#6#31#33#36#38#40#42#44#46#48#50#52#53#54#55#58#61#62#63#66#68#69#70#71#73#74#75))(1 527796)))()())"%pstring.
