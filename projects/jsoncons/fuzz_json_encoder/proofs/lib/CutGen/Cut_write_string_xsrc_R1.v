(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEnc Require Import EncSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_write_string_xsrc_T Cut_write_string_xsrc_R0.
Definition dict_Cut_write_string_xsrc_R1 : CCD.pt := CCD.mk_table 1368%positive "((2 0(1 2)(0 -32))(0 1048576)(5#2 1 4611686018427387904)(4 0(0 -1)(1 12))(2 0#4(0 2))(5#5 1 1)(5(1 12)1 1)(5(1 12)1 255)(2 1(1 12)(0 1))(2 4#9(0 1))(5#10 1 1)((1 2)-32)(0#12 8(1 18))((1 2)-24)(0#14 8(1 9))((1 2)-16)(0#16 8(1 8))((1 2)-8)(0#18 8(1 1))((1 10)8)(0#20 8(1 32))((1 10)24)(4 0(0 16)(1 36))(0#22 1#23)(5(1 36)0 15)((1 10)27)(0#26 1(0 0))((1 10)296)(0#28 8(1 35))((1 11)0)(0#30 8(1 33))((1 11)8)(0#32 8(1 34))(5(1 12)0 255)(5(1 34)0 140737488355328)(5(1 35)0 18446744073709551615)(6#28(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 11)1099511627776 140737488355328)(4(1 11)8)((1 2)-8704)(0 8672)(9#44#45)(0 8704)(6#44#47)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#44#47#51(0 408))((1 32)0)(7#44#47#53(0 24))(7#51(0 408)#53(0 24))(7#44#47#30(0 16))(7#51(0 408)#30(0 16))(7#53(0 24)#30(0 16))((1 2)-8704#47)((1 10)296(0 8))(#59#60)(0 1048575)(253060 253196 421620 422204 255860 254836 763484 764892)(0#63)(5#62 1 4611686018427387904)(4#65(1 0))(0#64#66)(2#1)(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 10))(9(1 11))(15(1 57))(16(1 58))(17(1 59))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(2 0(1 10)(0 8))(2 1(1 12)(0 3))(2 4#93(0 1))(5#94 0 0)(2 1(1 12)(0 2))(2 4#96(0 1))(5#97 0 0)(5#10 0 0))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R1 312%positive "(253128((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#6#7#8#11#13#15#17#19#21#24#25#27#29#31#33#34#35#36#37#38#39#40#41#42#43#46#48#49#50#52#54#55#56#57#58)64#61()#62)"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R1 290%positive "(#67(((421620((1(0 253144))#68#69#70#71#72#73#74#75(10(1 32))(11(1 33))(12(1 34))(13(1 55))(14(1 56))#76#77#78(18(1 18))#79#80#81#82#83#84#85#86#87#88#89#90#91)()(#65#3#6#7#8#11#13#15#17#19#21#24#25#27#29#31#33#34#35#36#37#38#39#40#41#42#43#46#48#49#50#52#54#55#56#57#58))(1 421620)))()())"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R1 309%positive "(253272((1 0)(1 48)#1(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)#92(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#3#95#98#99#13#15#17#19#21#24#25#27#29#31#33#34#35#36#37#38#39#40#41#42#43#46#48#49#50#52#54#55#56#57#58)64#61()#62)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R1 282%positive "(#67(((255860((1(0 253304))#68#69#70#71#72#73#74#75(10(1 33))(11(1 34))(12(0 0))(13(0 0))(14#92)#76#77#78(18#92)#79#80#81#82#83#84#85#86#87#88#89#90#91)()(#65#3#95#98#99#13#15#17#19#21#24#25#27#29#31#33#34#35#36#37#38#39#40#41#42#43#46#48#49#50#52#54#55#56#57#58))(1 255860)))()())"%pstring.
