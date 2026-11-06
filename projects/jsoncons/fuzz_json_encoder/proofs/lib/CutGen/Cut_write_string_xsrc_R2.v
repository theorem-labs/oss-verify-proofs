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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_write_string_xsrc_T Cut_write_string_xsrc_R0 Cut_write_string_xsrc_R1.
Definition dict_Cut_write_string_xsrc_R2 : CCD.pt := CCD.mk_table 1358%positive "((2 0(1 2)(0 -32))(0 1048575)(5#2 1 4611686018427387904)(0 1048576)(5#4 1 4611686018427387904)(4 0(0 -1)(1 12))(2 0#6(0 2))(5#7 1 1)(5(1 12)1 1)(5(1 12)1 255)(2 1(1 12)(0 1))(2 4#11(0 1))(5#12 1 1)((1 2)-32)(0#14 8(1 18))((1 2)-24)(0#16 8(1 9))((1 2)-16)(0#18 8(1 8))((1 2)-8)(0#20 8(1 1))((1 10)8)(0#22 8(1 32))((1 10)24)(4 0(0 16)(1 36))(0#24 1#25)(5(1 36)0 15)((1 10)27)(0#28 1(0 0))((1 10)296)(0#30 8(1 35))((1 11)0)(0#32 8(1 33))((1 11)8)(0#34 8(1 34))(5(1 12)0 255)(5(1 34)0 140737488355328)(5(1 35)0 18446744073709551615)(6#30(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 11)1099511627776 140737488355328)(4(1 11)8)((1 2)-8704)(0 8672)(9#46#47)(0 8704)(6#46#49)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#46#49#53(0 408))((1 32)0)(7#46#49#55(0 24))(7#53(0 408)#55(0 24))(7#46#49#32(0 16))(7#53(0 408)#32(0 16))(7#55(0 24)#32(0 16))((1 2)-8704#49)((1 10)296(0 8))(#61#62)(0 1048574)(253060 253196 421620 422204 255860 254836 763484 764892)(0#65)(5#64 1 4611686018427387904)(4#67(1 0))(0#66#68)(2#1)(3(1 3))(4(1 4))(8(1 10))(10(1 32))(11(0 34))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(1 422204)(2 0(1 10)(0 8))(5(1 64)0 1125899906842624)(2 1(1 12)(0 3))(2 4#88(0 1))(5#89 0 0)(2 1(1 12)(0 2))(2 4#91(0 1))(5#92 0 0)(5#12 0 0))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R2 315%positive "(253144((1 0)(1 64)#1(1 3)(1 4)(1 65)(1 66)(1 67)(1 10)(1 11)(1 68)(1 69)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 76)(1 77)(1 78)(1 79))(#3#5#8#9#10#13#15#17#19#21#23#26#27#29#31#33#35#36#37#38#39#40#41#42#43#44#45#48#50#51#52#54#56#57#58#59#60)80#63()#64)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R2 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R2 345%positive "(#69(((422204((1(0 253156))#70#71#72(5(1 65))(6(1 66))(7(1 67))#73(9(1 11))#74#75(12(1 70))(13(1 71))(14(1 72))(15(1 73))(16(1 74))(17(1 75))(18(1 18))#76#77#78#79#80#81#82#83#84(28(1 76))(29(1 77))(30(1 78))(31(1 79)))()(#67#3#5#8#9#10#13#15#17#19#21#23#26#27#29#31#33#35#36#37#38#39#40#41#42#43#44#45#48#50#51#52#54#56#57#58#59#60))#85))()())"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_string_xsrc_R2 314%positive "(253304((1 0)(1 65)#1(1 3)(1 4)(1 66)(1 67)(1 68)(1 10)(1 11)(1 64)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)#86(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 77)(1 78)(1 79)(1 80))(#87#3#5#90#93#94#15#17#19#21#23#26#27#29#31#33#35#36#37#38#39#40#41#42#43#44#45#48#50#51#52#54#56#57#58#59#60)81#63()#64)"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_string_xsrc_R2 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints2.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_write_string_xsrc_R2 344%positive "(#69(((422204((1(0 253324))#70#71#72(5(1 66))(6(1 67))(7(1 68))#73(9(1 64))#74#75(12(1 32))(13(1 72))(14(1 73))(15(1 74))(16(1 75))(17(1 76))(18#86)#76#77#78#79#80#81#82#83#84(28(1 77))(29(1 78))(30(1 79))(31(1 80)))()(#67#87#3#5#90#93#94#15#17#19#21#23#26#27#29#31#33#35#36#37#38#39#40#41#42#43#44#45#48#50#51#52#54#56#57#58#59#60))#85))()())"%pstring.
