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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_dt_xsrc_T Cut_dt_xsrc_R0.
Definition dict_Cut_dt_xsrc_R1 : CCD.pt := CCD.mk_table 1071%positive "((0 -144)(2 0(1 2)#1)(0 1048576)(5#3 1 4611686018427387904)((1 11)0)(0#5 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9344)(0 9344)(6#11#12)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#11#12#5(0 8))((1 32)0)(7#11#12#17(0 24))(7#5(0 8)#17(0 24))(0 9200)(9#11#20)((1 2)-144)(9#22(0 112))((1 2)-8)(0#24 8(1 1))((1 2)-16)(0#26 8(1 8))((1 2)-24)(0#28 8(1 9))((1 2)-32)(9#30(0 8))((1 2)-9344#12)(#32)(0 1048575)(273660 273732 273732 273808 422204 270980 273836 273736 273812 763484 764892)(0#35)(5#34 1 4611686018427387904)(4#37(1 0))(0#36#38)(2#2)(3(1 3))(4(1 4))(8(1 11))(10(1 32))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(1 422204)(9#22(0 104))((1 2)-40)(0#57 4(1 34))((1 2)-36)(0#59 4(1 33))(5(1 33)1 21)(#4#6#7#8#9#10#13#14#15#16#18#19#21#56#58#60#25#27#29#31#61)(5(1 51))(6(1 52))(7(1 53))(9(1 10))(13(1 57))(14(1 58))(15(1 59))(16(1 60))(17(1 61))(28(1 62))(29(1 63))(30(1 64))(31(1 65))(2 3(1 66)(0 0))(5(1 66)0 18446744073709551613))"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R1 256%positive "(273672((1 0)(1 66)#2(1 3)(1 4)(1 67)(1 68)(1 69)(1 11)(1 9)(1 70)(1 71)(1 72)(1 73)(1 74)(1 75)(1 76)(1 77)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 78)(1 79)(1 80)(1 81))(#4#6#7#8#9#10#13#14#15#16#18#19#21#23#25#27#29#31)82#33()#34)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints0.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R1 286%positive "(#39(((422204((1(0 273684))#40#41#42(5(1 67))(6(1 68))(7(1 69))#43(9(1 9))#44(11(0 46))(12(1 72))(13(1 73))(14(1 74))(15(1 75))(16(1 76))(17(1 77))#45#46#47#48#49#50#51#52#53#54(28(1 78))(29(1 79))(30(1 80))(31(1 81)))()(#37#4#6#7#8#9#10#13#14#15#16#18#19#21#23#25#27#29#31))#55))()())"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R1 210%positive "(273740((1 0)(1 50)#2(1 3)(1 4)(1 51)(1 52)(1 53)(1 11)(1 10)(1 66)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 62)(1 63)(1 64)(1 65))#62 67#33()#34)"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints1.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R1 823%positive "((3(11 66 1 18446744073709551615(11 66 2 18446744073709551615(16 0#39)))(11 66 0 18446744073709551614(11 66 0 18446744073709551613(16 1(0#36(4#37(1 1)))))))(((422204((1(0 273756))#40#41#42#63#64#65#43#66#44(11(0 45))(12(1 56))#67#68#69#70#71#45#46#47#48#49#50#51#52#53#54#72#73#74#75)()(#37(5(4 0(0 -1)(1 66))1 18446744073709551614)(5(1 66)2 18446744073709551615)(5(1 66)1 18446744073709551615)(5#76 1 1)#4#6#7#8#9#10#13#14#15#16#18#19#21#56#58#60#25#27#29#31#61))#55)((270980((1(0 273784))#40#41#42#63#64#65#43#66(10(2 0(1 2)(0 -140)))(11(1 33))(12(6 1 0 4(1 34)))(13(0 18446744073709551612))(14(0 17))(15(1 11))#70#71#45#46#47#48#49#50#51#52#53#54#72#73#74#75)()(#37#77#77(5(1 66)0 18446744073709551614)(5#76 0 0)#4#6#7#8#9#10#13#14#15#16#18#19#21#56#58#60#25#27#29#31#61))(1 270980)))((5(1 66)(0 0)1)(5(0 0)(1 66)0))())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_dt_xsrc_R1 209%positive "(273816((1 0)(1 50)#2(1 3)(1 4)(1 51)(1 52)(1 53)(1 11)(1 10)(0 0)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 62)(1 63)(1 64)(1 65))#62 66#33()#34)"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_dt_xsrc_R1 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints2.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_dt_xsrc_R1 222%positive "(#39(((273836((1(0 273832))#40#41#42#63#64#65#43#66(10(1 10))(11(1 11))(12(0 0))#67#68#69#70#71#45#46#47#48#49#50#51#52#53#54#72#73#74#75)()(#37#4#6#7#8#9#10#13#14#15#16#18#19#21#56#58#60#25#27#29#31#61))(1 273836)))()())"%pstring.
