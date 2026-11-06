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
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_bool_root_xsrc_T Cut_visit_bool_root_xsrc_R0 Cut_visit_bool_root_xsrc_R1 Cut_visit_bool_root_xsrc_R2 Cut_visit_bool_root_xsrc_R3.
Definition dict_Cut_visit_bool_root_xsrc_R4 : CCD.pt := CCD.mk_table 1855%positive "((2 0(1 2)(0 -32))(0 66317)(5(1 101)5 5)((0 0)883736)(0#4 1(0 1))((0 0)883737)(0#6 1(0 1))((0 0)883720)(0#8 8#2)((0 0)883728)(0#10 8(0 5))(0 1048573)(5#12 1 4611686018427387904)(0 1048574)(5#14 1 4611686018427387904)(5(1 69)5 5)(0 1048575)(5#17 1 4611686018427387904)(5(1 53)5 5)(0 1048576)(5#20 1 4611686018427387904)(4 0(0 -1)(1 11))(2 0#22(0 1))(5#23 1 1)(5(1 11)0 0)(2 1(1 11)(0 0))(2 4#26(0 1))(5#27 1 1)((1 2)-24)(0#29 8(1 9))((1 2)-16)(0#31 8(1 8))((1 2)-8)(0#33 8(1 1))((1 10)8)(0#35 8(1 32))((1 10)296)(0#37 8(1 37))(5(1 37)0 18446744073709551615)(6#37(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#45#46)((1 2)-32)(9#48(0 8))(0 10624)(6#45#50)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#45#50#54(0 408))((1 32)0)(7#45#50#56(0 24))(7#54(0 408)#56(0 24))(3 65536 813152)((1 10)264)(0#60 8(1 34))((1 10)272)(0#62 8(1 34))(5(1 11)0 1)((0 0)883696)(7#45#50#65(0 18))(7#54(0 408)#65(0 18))(7#56(0 24)#65(0 18))(7#45#50#8(0 18))(7#54(0 408)#8(0 18))(7#56(0 24)#8(0 18))((1 2)-10624#50)((1 10)296(0 8))(#72#73)(0 1048572)(247212 247436 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#76)(0#77(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 97))(6(1 98))(7(1 99))(8(1 8))(9(1 9))(10(0 1))(2 0(1 37)(1 101))(11#89)(12(1 37))(13(1 34))(14(1 104))(15(1 105))(16(1 106))(17(1 107))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 108))(29(1 109))(30(1 110))(31(1 111))(#79#80#81#82#83#84#85#86#87#88#90#91#92#93#94#95#96#97#98#99#100#101#102#103#104#105#106#107#108#109#110)(0#37 8#89)(1 247436)(0 72237)(5(1 101)4 4)((0 0)883712)(0#116 1(0 1))((0 0)883713)(0#118 1(0 1))(0#65 8#114)((0 0)883704)(0#121 8(0 4))(5(1 69)4 4)(5(1 53)4 4)(2 0(1 11)(0 -1))(5#125 0 0)(5(1 11)1 1)(5#27 0 0))"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R4 337%positive "(247380((1 0)(1 96)#1(1 3)(1 4)(1 97)(1 98)(1 99)(1 10)#2#2(1 101)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 108)(1 109)(1 110)(1 111))(#3#5#7#9#11#13#15#16#18#19#21#24#25#28#30#32#34#36#38#39#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#67#68#69#70#71)112#74()#75)"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R4 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints5.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R4 160%positive "(#78(((247436#111()(#112#3#5#7#9#11#13#15#16#18#19#21#24#25#28#30#32#34#36#39#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#67#68#69#70#71))#113))()())"%pstring.
(* [comment removed for export] *)
Definition t8 : CC.cutpoint := CCD.dec_cp_t dict_Cut_visit_bool_root_xsrc_R4 355%positive "(247344((1 0)(1 96)#1(1 3)(1 4)(1 97)(1 98)(1 99)(1 10)#114#114(1 101)(1 102)(1 103)(1 104)(1 105)(1 106)(1 107)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 108)(1 109)(1 110)(1 111))(#115#117#119#120#122#13#15#123#18#124#21#126#127#128#30#32#34#36#38#39#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#67#68#69#70#71)112#74()#75)"%pstring.
Definition BL8 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_visit_bool_root_xsrc_R4 3%positive "()"%pstring.
Definition hints8 : list (nat * CC.subst) := hints6.
Definition o8 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R4 174%positive "(#78(((247436#111()(#112#115#117#119#120#122#13#15#123#18#124#21#126#127#128#30#32#34#36#39#40#41#42#43#44#47#49#51#52#53#55#57#58#59#61#63#64#66#67#68#69#70#71))#113))()())"%pstring.
