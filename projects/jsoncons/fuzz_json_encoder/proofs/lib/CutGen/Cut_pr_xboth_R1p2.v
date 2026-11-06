(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncSumsA5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_pr_xboth_T Cut_pr_xboth_R0p0 Cut_pr_xboth_R0p1 Cut_pr_xboth_R0p2.
Definition dict_Cut_pr_xboth_R1p2 : CCD.pt := CCD.mk_table 1230%positive "((2 0(1 2)(0 -48))(0 5243)(0 281474976710656)(4 0#3(1 68))(2 6#4(0 50))(4 0#2#5)(2 6#6(0 17))(2 6(1 15)(0 3))(0 2147450880)(2 0#8#9)(3 1459384 1463120)((0 0)1497016)(0#12 8#9)(4 0(0 64)(1 70))(2 0#14(0 40))(5#15 1 4611686018427387904)(0 -100)(2 0(1 68)#17)(5#18 0 243)(5(1 68)100 343)(2 4(1 68)(0 100))(5#21 0 0)(2 0(1 68)(0 -10))(5#23 0 333)(5(1 68)10 343)(2 3(1 68)(0 10))(5#26 0 0)(5(1 68)5 343)(5(1 69)3 24)(5(1 70)0 1048576)((1 15)0)(0#31 8(1 32))(5(1 11)1 21)((1 10)0)(9#34(1 11))(5(1 10)7094272 140737479966688)(4(1 10)8)(2 6(1 10)(0 3))(#38 2147450880)(1#39(0 4))((0 0)2147446784)(0 17592186048512)(7#41#42#34(0 32))(5(1 15)7094272 140737488355320)(4(1 15)8)(#8 2147450880)(1#46(0 1))(7#41#42#31(0 8))(5(1 32)7094272 140737479966696)(4(1 32)8)((1 32)0)(7#41#42#51(0 24))((1 2)-4512)(0 4512)(6#53#54)(5(1 2)140735332487584 140737488355328)(4(1 2)16)(7#41#42#53#54)(7#53#54#34(0 32))(7#53#54#31(0 8))(7#53#54#51(0 24))(7#34(0 32)#51(0 24))(7#31(0 8)#51(0 24))(7#34(0 32)#31(0 8))(0 4400)(9#53#65)((1 2)-8)(0#67 8(1 1))((1 2)-16)(0#69 8(1 8))((1 2)-24)(0#71 8(1 9))((1 2)-32)(0#73 8(1 18))((1 2)-40)(0#75 8(1 19))(2 0#14(0 39))(4 0#17#7)(2 0(1 68)#78)(2 9#79(0 255))(4 0(0 205)#80)(2 6#81(0 11))(5#77 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t36 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pr_xboth_R1p2 347%positive "(837688((1 0)(1 73)#1(1 3)(1 4)(1 74)(1 75)(1 76)(1 15)(1 68)(1 77)(1 78)(1 79)(1 80)(1 81)(1 82)(1 83)(1 84)#7#10(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 85)(1 86)(1 87)(1 88))(#11#13#16#19#20#22#24#25#27#28#29#30#11#13#32#33#35#36#37#40#43#44#45#47#48#49#50#52#55#56#57#58#59#60#61#62#63#64#66#68#70#72#74#76)89(((1 2)-4512#54))()#77)"%pstring.
Definition BL36 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pr_xboth_R1p2 3%positive "()"%pstring.
Definition hints36 : list (nat * CC.subst) := hints19.
Definition o36 : CA.pout := CCD.dec_pout_t dict_Cut_pr_xboth_R1p2 762%positive "((0(0(833108 833108 833108 833108 833108 833240 833300 833488 833376 833436 833968 834012 833756 833812 833872 834316 834360 834316 834360 837468 834116 833292 833428 834004 833864 834352 1056004 833300 833436 834012 833872 834360 834180 834256 1402040 1403068))(16 0(1 0)))(((1056004((1(0 837748))(2#1)(3(1 3))(4(1 4))(5(1 74))(6(1 75))(7(1 76))(8(1 15))(9#79)(10(1 32))(11(2 0(2 9#82(0 -49))(0 48)))(12(0 205))(13(1 80))(14(1 81))(15(1 82))(16(1 83))(17(1 84))(18#82)(19#10)(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 85))(29(1 86))(30(1 87))(31(1 88)))()(#83#11#13#16#19#20#22#24#25#27#28#29#30#11#13#32#33#35#36#37#40#43#44#45#47#48#49#50#52#55#56#57#58#59#60#61#62#63#64#66#68#70#72#74#76))(1 1056004)))((0#83))())"%pstring.
