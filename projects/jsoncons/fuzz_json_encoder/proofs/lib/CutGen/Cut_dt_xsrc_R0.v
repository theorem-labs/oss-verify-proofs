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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmFloatX Require Import FxSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_dt_xsrc_T.
Definition dict_Cut_dt_xsrc_R0 : CCD.pt := CCD.mk_table 964%positive "((273660 273732 273732 273808 422204 270980 273836 273736 273812 763484 764892)(0#1)(0 1048576)(5#3 1 4611686018427387904)(4#4(1 0))(0#2#5)(0 -144)(2 0(1 2)#7)(2#8)(3(1 3))(4(1 4))(5(1 51))(6(1 52))(7(1 53))(8(1 11))(12(1 56))(13(1 57))(14(1 58))(15(1 59))(16(1 60))(17(1 61))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 62))(29(1 63))(30(1 64))(31(1 65))((1 11)0)(0#36 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9344)(0 9344)(6#42#43)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#42#43#36(0 8))((1 32)0)(7#42#43#48(0 24))(7#36(0 8)#48(0 24))(0 9200)(9#42#51)((1 2)-144)((1 2)-8)(0#54 8(1 1))((1 2)-16)(0#56 8(1 8))((1 2)-24)(0#58 8(1 9))((1 2)-32)(9#60(0 8))(1(1 50))(9(1 10))(11(1 55))(9#53(0 104))((1 2)-40)(0#66 4(1 34))((1 2)-36)(0#68 4(1 33))(5(1 33)1 21)(#4#37#38#39#40#41#44#45#46#47#49#50#52#65#67#69#55#57#59#61#70))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R0 221%positive "(#6(((422204((1(0 273672))#9#10#11#12#13#14#15(9(1 9))(10(1 32))(11(0 48))#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()(#4#37#38#39#40#41#44#45#46#47#49#50#52(9#53(0 112))#55#57#59#61))(1 422204)))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R0 136%positive "(#6(((273736(#62#9#10#11#12#13#14#15#63(10(0 1))#64#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()#71)(1 273736)))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R0 136%positive "(#6(((273812(#62#9#10#11#12#13#14#15#63(10(0 0))#64#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()#71)(1 273812)))()())"%pstring.
