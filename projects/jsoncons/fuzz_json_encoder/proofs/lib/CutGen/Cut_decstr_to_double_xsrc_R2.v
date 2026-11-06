(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_decstr_to_double_xsrc_T Cut_decstr_to_double_xsrc_R0 Cut_decstr_to_double_xsrc_R1.
Definition dict_Cut_decstr_to_double_xsrc_R2 : CCD.pt := CCD.mk_table 679%positive "((2 0(1 10)(1 11))(5(0 9)1 4611686018427387904)((1 12)0)(0#3 8(1 48))((1 2)-56)(0#5 8#1)(5(0 10)1 4611686018427387904)((1 2)-48)(0#8 8(1 20))((1 2)-40)(0#10 8(1 19))((1 2)-32)(0#12 8(1 18))((1 2)-24)(0#14 8(1 9))((1 2)-16)(0#16 8(1 8))((1 2)-8)(0#18 8(1 1))(5(1 11)0 67108864)(5(1 10)4096 140737488355328)((1 2)-9040)(0 8984)(9#22#23)(0 9040)(6#22#25)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 12)8)(9#29(0 0))(6#3(0 8))(5(1 12)1099511627776 140737488355328)((0 0)890236)(6#33(0 4))(3 65536 813152)(7#22#25#3(0 8))((1 10)0)(2 0(1 11)(0 1))(7#22#25#37#38)(7#33(0 4)#37#38)(5#1 4096 140737488355328)(#2#4#6#7#9#11#13#15#17#19#20#21#24#26#27#28#30#31#32#34#35#36#39#40#41))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_decstr_to_double_xsrc_R2 265%positive "(273392((1 0)(1 32)(2 0(1 2)(0 -80))(1 3)(1 4)(1 33)(1 34)(1 35)(1 12)(1 10)(1 49)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)#1(1 11)#1(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))#42 50(((1 2)-9040#25)((1 12)0(0 8))((0 0)890236(0 4)))()(0 8))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_decstr_to_double_xsrc_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_decstr_to_double_xsrc_R2 425%positive "((0(0(273320 273440 760068 273388 763484 764892))(1 0))(((273440((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 8))(9(1 9))(10#1)(11(2 9(2 0(2 4(2 9(1 49)(0 129))(0 1))(0 -1))(0 34)))(12(1 38))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()#42)(1 273440)))()())"%pstring.
