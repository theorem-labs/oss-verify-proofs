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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_db_xsrc_T Cut_db_xsrc_R0 Cut_db_xsrc_R1.
Definition dict_Cut_db_xsrc_R2 : CCD.pt := CCD.mk_table 1145%positive "((4 0(0 -1)(1 48))(2 0(1 11)#1)(2 0(1 10)#2)(2 0#3(0 1))(2 0(1 10)(1 11))(4 0(0 4)(1 48))(5#6 1 4611686018427387904)(2 0(1 49)(0 -1))(5#8 0 0)(5(1 49)1 1)(2 1(1 49)(0 0))(2 4#11(0 1))(5#12 0 0)(2 0#1(0 1))(5#14 0 139637976727650)(2 4#4#5)(5#16 0 0)(5#3 1099511627776 140737488355426)(5#4 1099511627777 140737488355427)(2 0#6(0 1))(5#20 1 4611686018427387904)((1 13)0)(0#22 8(1 32))(5(1 11)1 99)(5(1 12)0 255)((1 10)0)(9#26(1 11))(5(1 10)1099511627776 140737488355328)(5(1 13)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-8592)(0 8496)(9#32#33)(0 8592)(6#32#35)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#32#35#26(1 11))(7#32#35#22(0 8))((1 32)0)(7#32#35#41(0 24))(7#26(1 11)#41(0 24))(7#22(0 8)#41(0 24))(7#26(1 11)#22(0 8))((1 2)-8)(0#46 8(1 1))((1 2)-16)(0#48 8(1 8))((1 2)-24)(0#50 8(1 9))((1 2)-32)(0#52 8(1 18))((1 2)-40)(0#54 8(1 19))((1 2)-48)(0#56 8(1 20))((1 2)-56)(0#58 8(1 21))((1 2)-64)(0#60 8(1 22))((1 2)-72)(0#62 8(1 23))((1 2)-80)(0#64 8(1 24))((1 2)-88)(0#66 8(1 25))((1 2)-96)(0#68 8(1 26))(5(1 48)1 99)(5#2 0 98)(5(1 49)0 1)(5(1 66)0 255)(2 0#6(0 -1))(5#74 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_db_xsrc_R2 358%positive "(269548((1 0)(1 84)(2 0(1 2)(0 -96))(1 3)(1 4)(1 85)(1 86)(1 87)(1 13)(1 12)(1 88)(1 89)(1 90)(1 91)(1 92)(1 93)(1 94)(1 95)#4#5(0 10)(1 49)(0 68)(0 43)(0 45)(0 101)(0 69)(1 27)(1 96)(1 97)(1 98)(1 99))(#7#9#10#13#15#17#18#19#21#23#24#25#27#28#29#30#31#34#36#37#38#39#40#42#43#44#45#47#49#51#53#55#57#59#61#63#65#67#69#70#71#72#73)100(((1 2)-8592#35))()#74)"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_db_xsrc_R2 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints5.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_db_xsrc_R2 540%positive "((0(0(269344 269444 269456 269664 422204 269444 763484 764892))(16 0(1 0)))(((422204((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 85))(6(1 86))(7(1 87))(8(1 8))(9(1 9))(10(1 32))(11(0 48))(12(1 90))(13(1 91))(14(1 92))(15(1 93))(16(1 94))(17(1 95))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 96))(29(1 97))(30(1 98))(31(1 99)))()(#75#7#9#10#13#15#17#18#19#21#23#24#25#27#28#29#30#31#34#36#37#38#39#40#42#43#44#45#47#49#51#53#55#57#59#61#63#65#67#69#70#71#72#73))(1 422204)))((0#75))())"%pstring.
