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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_convert_xboth_T Cut_convert_xboth_R0 Cut_convert_xboth_R1 Cut_convert_xboth_R2 Cut_convert_xboth_R3.
Definition dict_Cut_convert_xboth_R4 : CCD.pt := CCD.mk_table 2459%positive "((0 -128)(2 0(1 2)#1)(2 0(1 10)(0 4))(0 18446744073709385119)(6 1 0 4(1 32))(3 6#5(0 6))(2 9#6(0 63))(2 0#7#1)(2 9#5(0 63))(2 0#9#1)(0 2147450880)(0 166496)((1 0)(1 96)#2(1 3)(1 4)(1 97)(1 98)(1 99)#3(0 0)(1 100)(1 101)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(1 12)#4#3(0 0)#8#3#10#11#10#12(1 108)(1 109)(1 110)(1 111))(3 1459384 1463120)((0 0)1497016)(0#15 8#11)(5(0 97)1 4611686018427387904)(5(0 98)1 4611686018427387904)(5(0 99)1 4611686018427387904)(5(0 100)1 4611686018427387904)(5(1 32)134 4294967295)(5(1 32)133 4294967295)(3 6#5(0 16))(2 4(0 16)#23)(5#24 0 0)(5(1 32)132 4294967295)(5(1 32)131 4294967295)(2 1#23(0 0))(2 4#28(0 1))(5#29 0 0)(5(1 32)130 4294967295)(5(1 32)129 4294967295)(3 6#5(0 11))(2 1#33(0 0))(2 4#34(0 1))(5#35 0 0)(5(1 32)128 4294967295)(2 4#5(0 128))(5#38 0 0)(0 2048)(2 6#5(0 11))(4 0#40#41)(0 55296)(2 1#42#43)(2 4#44(0 1))(5#45 0 0)((1 2)-128)(0 65533)(0#47 8#48)((1 2)-112)(0#50 8#43)((1 2)-120)(0#52 8(0 0))((1 2)-104)(0#54 8(1 27))((1 2)-96)(0#56 8(1 26))((1 2)-88)(0#58 8(1 25))((1 2)-80)(0#60 8(1 24))((1 2)-72)(0#62 8(1 23))((1 2)-64)(0#64 8(1 22))((1 2)-56)(0#66 8(1 21))((1 2)-48)(0#68 8(1 20))((1 2)-40)(0#70 8(1 19))((1 2)-32)(0#72 8(1 18))((1 2)-24)(0#74 8(1 9))((1 2)-16)(0#76 8(1 8))((1 2)-8)(0#78 8(1 1))(5(1 32)0 4294967295)(5(1 10)7094272 140737479966716)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#82#83#84(0 4))(5(1 12)7094272 140737479966696)(4(1 12)8)(3 166400 166656)((1 2)-4496)(0 4368)(9#89#90)(0 4496)(6#89#92)(5(1 2)140735332487568 140737488355328)(4(1 2)16)(7#89#92#84(0 4))((1 12)0)(7#89#92#97(0 24))(4(1 10)8)(#14#16#17#14#16#18#14#16#19#14#16#20#21#22#25#26#27#30#31#32#36#37#39#46#49#51#53#55#57#59#61#63#65#67#69#71#73#75#77#79#14#16#80#81#85#86#87#88#91#93#94#95#96#98#99)((1 2)-4496#92)(#101)((1 94)(1 95))(923544 923544 924188 1056004 1402040 1403068)(0#104)(0#105(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 97))(6(1 98))(7(1 99))(8(1 8))(9(1 9))(10#3)(11(0 0))(12(1 102))(13(1 103))(14(1 104))(15(1 105))(16(1 106))(17(1 107))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 108))(29(1 109))(30(1 110))(31(1 111))(#107#108#109#110#111#112#113#114#115#116#117#118#119#120#121#122#123#124#125#126#127#128#129#130#131#132#133#134#135#136#137)(1 924188)(4(1 10)4)(#14#16#17#14#16#18#14#16#19#14#16#20#21#22#25#26#27#30#31#32#36#37#39#46#49#51#53#55#57#59#61#63#65#67#69#71#73#75#77#79#14#16#80#81#85#86#87#88#91#93#94#95#96#98#140))"%pstring.
(* [comment removed for export] *)
Definition t26 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R4 32%positive "(924056#13#100 112#102()(0 96))"%pstring.
Definition BL26 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R4 7%positive "(#103)"%pstring.
Definition hints26 : list (nat * CC.subst) := hints22.
Definition o26 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R4 37%positive "(#106(((924188#138()#100)#139))()())"%pstring.
(* [comment removed for export] *)
Definition t27 : CC.cutpoint := CCD.dec_cp_t dict_Cut_convert_xboth_R4 32%positive "(924056#13#141 112#102()(0 96))"%pstring.
Definition BL27 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_convert_xboth_R4 7%positive "(#103)"%pstring.
Definition hints27 : list (nat * CC.subst) := hints25.
Definition o27 : CA.pout := CCD.dec_pout_t dict_Cut_convert_xboth_R4 37%positive "(#106(((924188#138()#141)#139))()())"%pstring.
