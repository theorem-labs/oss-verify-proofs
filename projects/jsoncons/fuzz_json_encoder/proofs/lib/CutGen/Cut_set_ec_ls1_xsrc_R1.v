(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallSums.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_set_ec_ls1_xsrc_T Cut_set_ec_ls1_xsrc_R0.
Definition dict_Cut_set_ec_ls1_xsrc_R1 : CCD.pt := CCD.mk_table 678%positive "((2 0(1 2)(0 -32))((0 0)883664)(0#2 1(0 0))((0 0)883665)(0#4 1(0 2))(5(0 10)1 4611686018427387904)((1 2)-24)(0#7 8(1 9))((1 2)-16)(0#9 8(1 8))((1 2)-8)(0#11 8(1 1))(6#2(0 2))((0 0)1021544)(0#14 1(0 0))((0 0)1021548)(0#16 4(0 0))((0 0)1021552)(0#18 4(0 1))((0 0)1021560)(0 1021568)(0#20 8#21)((0 0)1021568)(0#23 8(0 0))((0 0)1021576)(0 696180)(0#25 8#26)((0 0)1021832)(0 236824)(0#28 8#29)(6#14(0 544))((1 10)0)(9#32(0 16))(6#32(0 16))(5(1 10)1099511627776 140737488355328)(5(1 11)1 31)((1 2)-256)(9#37(0 232))(6#37(0 256))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(3 65536 813152)(7#37(0 256)#32(0 16))((0 0)65536)(0 962560)(7#32(0 16)#44#45)(5(0 9)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_set_ec_ls1_xsrc_R1 354%positive "(274212((1 0)(1 32)#1(1 3)(1 4)(1 33)(1 34)(1 35)(1 10)(1 11)(0 1)(1 37)(1 38)(1 39)(1 40)(1 41)(1 42)(1 43)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 44)(1 45)(1 46)(1 47))(#3#5#6#8#10#12#13#15#17#19#22#24#27#30#31#33#34#35#36#38#39#40#41#42#43#46)48(((1 2)-256(0 256))((1 10)0(0 16))((0 0)883664(0 2))((0 0)1021544(0 544)))()(0 9))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_set_ec_ls1_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_set_ec_ls1_xsrc_R1 490%positive "((0(0(274112 274196 295420 295500 695784 763484 764892))(4#47(1 0)))(((695784((1(0 274248))(2#1)(3(1 3))(4(1 4))(5(1 33))(6(1 34))(7(1 35))(8(1 10))(9(1 11))(10(0 418464))(11(0 817288))(12(0 817248))(13(1 39))(14(1 40))(15(1 41))(16(1 42))(17(1 43))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 44))(29(1 45))(30(1 46))(31(1 47)))()(#47#3#5#6#8#10#12#13#15#17#19#22#24#27#30#31#33#34#35#36#38#39#40#41#42#43#46))(1 695784)))()())"%pstring.
