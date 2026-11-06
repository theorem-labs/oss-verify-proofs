(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums EncSums2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_double_root_xsrc_T Cut_visit_double_root_xsrc_R0 Cut_visit_double_root_xsrc_R1.
Definition dict_Cut_visit_double_root_xsrc_R2 : CCD.pt := CCD.mk_table 1330%positive "((2 0(1 2)(0 -96))(0 1048575)(5#2 1 4611686018427387904)(0 1048576)(5#4 1 4611686018427387904)((1 2)-48)(0#6 8(1 48))((1 2)-40)(0#8 8(1 19))((1 2)-32)(0#10 8(1 18))((1 2)-24)(0#12 8(1 9))((1 2)-16)(0#14 8(1 8))((1 2)-8)(0#16 8(1 1))((1 10)8)(0#18 8(1 32))((1 10)16)(0 788528)(0#20 8#21)((1 10)88)(0#23 2(1 41))(5(1 41)0 65535)((1 10)296)(0#26 8(1 37))(5(1 37)0 18446744073709551615)(6#26(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10528)(9#34#35)((1 2)-96)(9#37(0 48))(9#8(0 0))(0 10624)(6#34#40)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#34#40#44(0 408))((1 32)0)(7#34#40#46(0 24))(7#44(0 408)#46(0 24))(3 65536 813152)((1 10)264)(0#50 8(1 34))((1 10)272)(0#52 8(1 34))((0 0)883672)(7#34#40#54(0 18))(7#44(0 408)#54(0 18))(7#46(0 24)#54(0 18))(0 1048574)(242548 243296 242884 242736 242816 243056 243476 243596 252124 421620 253336 254004 242596 242664 242676 242712 242784 763484 764892)(0#59)(5#58 1 4611686018427387904)(1(1 1))(2#1)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 13))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 12))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(2 9(1 49)(0 897))(2 1#91(0 0))(2 4#92(0 1)))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_double_root_xsrc_R2 333%positive "(242668((1 0)(1 1)#1(1 3)(1 4)(1 5)(1 6)(1 7)(1 10)(1 13)(1 49)(1 34)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 12)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#3#5#7#9#11#13#15#17#19#22#24#25#27#28#29#30#31#32#33#36#38#39#41#42#43#45#47#48#49#51#53#55#56#57)50(((1 2)-10624#40)((1 10)296(0 8)))()#58)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_double_root_xsrc_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_visit_double_root_xsrc_R2 709%positive "((0#60(3(16 0(0#60(4#61(1 0))))(11 49 1 18446744073709551615(16 1(0#60(4#61(1 1)))))))(((242784(#62#63#64#65#66#67#68#69#70(10(2 0(1 10)(0 252)))(11(2 0(1 10)(0 8)))#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90)()(#61(5(2 0(4 0(0 -1)#91)(0 1))1 1)(5#93 1 1)#3#5#7#9#11#13#15#17#19#22#24#25#27#28#29#30#31#32#33#36#38#39#41#42#43#45#47#48#49#51#53#55#56#57))(1 242784))((242676(#62#63#64#65#66#67#68#69#70(10#91)(11(1 34))#71#72#73#74#75#76#77#78#79#80#81#82#83#84#85#86#87#88#89#90)()(#61(5(2 0#91(0 -1))0 896)(5(1 49)1 18446744073709551615)(5#93 0 0)#3#5#7#9#11#13#15#17#19#22#24#25#27#28#29#30#31#32#33#36#38#39#41#42#43#45#47#48#49#51#53#55#56#57))(1 242676)))((1#92(0 1)1)(1(0 1)#92 0))())"%pstring.
