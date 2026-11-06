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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_write_bignum_xsrc_T Cut_write_bignum_xsrc_R0.
Definition dict_Cut_write_bignum_xsrc_R1 : CCD.pt := CCD.mk_table 716%positive "((0 1048576)(5#1 1 4611686018427387904)((1 2)-32)(0#3 8(1 18))((1 2)-24)(0#5 8(1 9))((1 2)-16)(0#7 8(1 8))((1 2)-8)(0#9 8(1 1))((1 10)8)(0#11 8(1 32))((1 10)27)(0#13 1(0 0))((1 10)296)((1 11)0)(0#16 8(1 33))((1 11)8)(0#18 8(1 34))(5(1 34)0 140737488355328)(5(1 35)0 18446744073709551615)(6#15(0 8))(5(1 10)1099511627776 140737488355328)(4(1 10)8)(5(1 32)1099511627776 140737488355328)(4(1 32)8)(5(1 11)1099511627776 140737488355328)(4(1 11)8)((1 2)-8672)(0 8496)(9#29#30)((1 2)-176)(9#32(0 144))(0 8672)(6#29#34)(5(1 2)1099511627776 140737488355328)(4(1 2)16)((1 10)0)(7#29#34#38(0 408))((1 32)0)(7#29#34#40(0 24))(7#38(0 408)#40(0 24))(7#29#34#16(0 16))(7#38(0 408)#16(0 16))(7#40(0 24)#16(0 16))(2 0(1 34)(1 35)))"%pstring.
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CCD.dec_cp_t dict_Cut_write_bignum_xsrc_R1 359%positive "(254904((1 0)(1 48)(2 0(1 2)(0 -176))(1 3)(1 4)(1 49)(1 50)(1 51)(1 10)(1 11)(1 52)(1 53)(1 54)(1 55)(1 56)(1 57)(1 58)(1 59)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 60)(1 61)(1 62)(1 63))(#2#4#6#8#10#12#14(0#15 8(1 35))#17#19#20#21#22#23#24#25#26#27#28#31#33#35#36#37#39#41#42#43#44#45)64(((1 2)-8672#34)((1 10)296(0 8)))()(0 1048575))"%pstring.
Definition BL1 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_write_bignum_xsrc_R1 3%positive "()"%pstring.
Definition hints1 : list (nat * CC.subst) := hints0.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_write_bignum_xsrc_R1 468%positive "((0(0(254836 255616 421620 763484 764892))(1 0))(((255616((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 49))(6(1 50))(7(1 51))(8(1 8))(9(1 9))(10#46)(11(1 35))(12(1 54))(13(1 55))(14(1 56))(15(1 57))(16(1 58))(17(1 59))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 60))(29(1 61))(30(1 62))(31(1 63)))()((0#15 8#46)#2#4#6#8#10#12#14#17#19#20#21#22#23#24#25#26#27#28#31#33#35#36#37#39#41#42#43#44#45))(1 255616)))()())"%pstring.
