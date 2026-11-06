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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_df_xsrc_T Cut_df_xsrc_R0.
Definition dict_Cut_df_xsrc_R1 : CCD.pt := CCD.mk_table 788%positive "((0 -160)(2 0(1 2)#1)(0 1048576)(5#3 1 4611686018427387904)((1 2)-48)(0#5 8(1 48))((1 2)-40)(0#7 8(1 19))((1 2)-32)(0#9 8(1 18))((1 2)-24)(0#11 8(1 9))((1 2)-16)(0#13 8(1 8))((1 2)-8)(0#15 8(1 1))((1 11)0)(0#17 8(1 32))(5(1 10)0 255)(5(1 11)1099511627776 140737488355328)(5(1 32)1099511627776 140737488355328)(4(1 32)8)((1 2)-9200)(0 9200)(6#23#24)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#23#24#17(0 8))((1 32)0)(7#23#24#29(0 24))(7#17(0 8)#29(0 24))(0 9152)(9#23#32)(9#7(0 0))(0 1048575)(5#35 1 4611686018427387904)(2#2)(3(1 3))(4(1 4))(8(1 11))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(5(1 55)1 25)((1 2)-148)(9#50(0 100))(0 524288)(5#52 1 4611686018427387904)(0 9040)(9#23#54)((1 2)-160)(9#5(0 8))(0 524287)(5#58 1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R1 274%positive "(273872((1 0)(1 1)#2(1 3)(1 4)(1 5)(1 6)(1 7)(1 11)(1 9)(1 10)(1 11)(1 12)(1 13)(1 14)(1 15)(1 16)(1 17)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 28)(1 29)(1 30)(1 31))(#4#6#8#10#12#14#16#18#19#20#21#22#25#26#27#28#30#31#33#34)49(((1 2)-9200#24))()#35)"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R1 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints0.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R1 322%positive "((4#36(1 0))(((273872((1(1 1))#37#38#39(5(1 5))(6(1 6))(7(1 7))#40(9(1 9))(10(1 10))(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 19))#41#42#43#44#45#46#47#48(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#36#4#6#8#10#12#14#16#18#19#20#21#22#25#26#27#28#30#31#33#34))(1 273872)))()())"%pstring.
(* [comment removed for export] *)
Definition t3 : CC.cutpoint := CCD.dec_cp_t dict_Cut_df_xsrc_R1 298%positive "(273964((1 0)(1 51)#2(1 3)(1 4)(1 52)(1 53)(1 54)(1 11)(1 10)(1 55)(1 56)(1 57)(1 58)(1 59)(1 60)(1 61)(1 62)(1 48)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 63)(1 64)(1 65)(1 66))(#49#51#53#18#19#20#21#22#25#26#27#28#30#31#55(9#56(0 112))#16#14#12#10#8#57)67(((1 2)-160(0 8)))()#58)"%pstring.
Definition BL3 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_df_xsrc_R1 3%positive "()"%pstring.
Definition hints3 : list (nat * CC.subst) := hints1.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_df_xsrc_R1 483%positive "((0(0(273836 273940 274036 422204 719568 273320 269344 273868 273872 273924 273932 274044 763484 764892))(4#59(1 0)))(((273320((1(0 273992))#37#38#39(5(1 52))(6(1 53))(7(1 54))#40(9(1 10))(10(2 0(1 2)(0 -148)))(11(1 55))(12#2)(13(1 58))(14(1 59))(15(1 60))(16(1 61))(17(1 62))(18(1 48))(19(1 55))#41#42#43#44#45#46#47#48(28(1 63))(29(1 64))(30(1 65))(31(1 66)))()(#59(0#56 8(0 0))#49#51#53#18#19#20#21#22#25#26#27#28#30#31#55(9((1 2)-152)(0 104))#16#14#12#10#8#57))(1 273320)))()())"%pstring.
