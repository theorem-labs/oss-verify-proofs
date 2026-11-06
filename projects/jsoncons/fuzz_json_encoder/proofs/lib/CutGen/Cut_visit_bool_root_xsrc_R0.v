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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_visit_bool_root_xsrc_T.
Definition dict_Cut_visit_bool_root_xsrc_R0 : CCD.pt := CCD.mk_table 1134%positive "((247212 247436 252124 421620 253336 274788 274904 252268 252560 253060 763484 764892)(0#1)(0 1048576)(5#3 1 4611686018427387904)(2 0(1 2)(0 -32))(2#5)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(1 34))(11(1 11))(12(1 34))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(2 1(1 11)(0 0))(2 4#36(0 1))((1 2)-24)(0#38 8(1 9))((1 2)-16)(0#40 8(1 8))((1 2)-8)(0#42 8(1 1))((1 10)8)(0#44 8(1 32))((1 10)296)(0#46 8(1 37))(5(1 37)0 18446744073709551615)(6#46(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-10624)(0 10592)(9#54#55)((1 2)-32)(9#57(0 8))(0 10624)(6#54#59)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#54#59#63(0 408))((1 32)0)(7#54#59#65(0 24))(7#63(0 408)#65(0 24))(3 65536 813152)((1 10)264)(0#69 8(1 34))((1 10)272)(0#71 8(1 34))(5(1 11)0 1)((0 0)883696)(7#54#59#74(0 18))(7#63(0 408)#74(0 18))(7#65(0 24)#74(0 18))((0 0)883720)(7#54#59#78(0 18))(7#63(0 408)#78(0 18))(7#65(0 24)#78(0 18)))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_visit_bool_root_xsrc_R0 634%positive "((0#2(3(11 11 0 0(16 0(0#2(4#4(1 0)))))(11 11 1 1(16 1(0#2(4#4(1 1)))))))(((274904((1(0 247352))#6#7#8#9#10#11#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()(#4(5(2 0(4 0(0 -1)(1 11))(0 1))1 1)(5(1 11)0 0)(5#37 1 1)#39#41#43#45#47#48#49#50#51#52#53#56#58#60#61#62#64#66#67#68#70#72#73#75#76#77#79#80#81))(1 274904))((274788((1(0 247316))#6#7#8#9#10#11#12#13#14#15#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()(#4(5(2 0(1 11)(0 -1))0 0)(5(1 11)1 1)(5#37 0 0)#39#41#43#45#47#48#49#50#51#52#53#56#58#60#61#62#64#66#67#68#70#72#73#75#76#77#79#80#81))(1 274788)))((1#36(0 1)1)(1(0 1)#36 0))())"%pstring.
