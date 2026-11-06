(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_annotate_xboth_T Cut_annotate_xboth_R0.
Definition dict_Cut_annotate_xboth_R1 : CCD.pt := CCD.mk_table 1304%positive "((2 0(1 2)(0 -16))((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)(1 8)(1 9)(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(5(0 8)1 4611686018427387904)((1 2)-16)(0#4 8(1 8))((1 2)-8)(0#6 8(1 1))(3 1459384 1463120)((0 0)1497016)(0 2147450880)(0#9 8#10)(5(1 10)1048576 140737488355304)(4(1 10)8)((0 0)2147446784)(0 17592186048512)((1 10)0)(7#14#15#16(0 24))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#21(1 34))(5#22 0 4096)(5(1 33)0 4096)((1 2)-4128)(0 4104)(9#25#26)(0 4128)(6#25#28)(5(1 2)140735332487200 140737488355328)(4(1 2)16)(7#25#28#16(0 24))(5(1 11)0 4096)(#3#5#7#8#11#12#13#17#18#19#20#23#24#27#29#30#31#32#33)((1 2)-4128#28)(#35)(859068 733160 857884 732972 859196 733284 858012 733116 542968 1402040 1403068)(0#37)(0#38(1 0))(1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8(1 8))(9(1 9))(10(1 44))(11(1 45))(12(1 46))(13(1 47))(14(1 48))(15(1 49))(16(1 50))(17(1 51))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55))(#40#41#42#43#44#45#46#47#48#49#50#51#52#53#54#55#56#57#58#59#60#61#62#63#64#65#66#67#68#69#70)(#3#5#7#8#11#12#13#17#18#19#20#23#24#27#29#30#31#32))"%pstring.
(* [comment removed for export] *)
Definition t4 : CC.cutpoint := CCD.dec_cp_t dict_Cut_annotate_xboth_R1 27%positive "(859184#2#34 56#36()(0 7))"%pstring.
Definition BL4 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_annotate_xboth_R1 3%positive "()"%pstring.
Definition hints4 : list (nat * CC.subst) := hints0.
Definition o4 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_xboth_R1 40%positive "(#39(((859196#71()#34)(1 859196)))()())"%pstring.
(* [comment removed for export] *)
Definition t5 : CC.cutpoint := CCD.dec_cp_t dict_Cut_annotate_xboth_R1 27%positive "(733272#2#34 56#36()(0 7))"%pstring.
Definition BL5 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_annotate_xboth_R1 3%positive "()"%pstring.
Definition hints5 : list (nat * CC.subst) := hints1.
Definition o5 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_xboth_R1 40%positive "(#39(((733284#71()#34)(1 733284)))()())"%pstring.
(* [comment removed for export] *)
Definition t6 : CC.cutpoint := CCD.dec_cp_t dict_Cut_annotate_xboth_R1 27%positive "(858000#2#34 56#36()(0 7))"%pstring.
Definition BL6 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_annotate_xboth_R1 3%positive "()"%pstring.
Definition hints6 : list (nat * CC.subst) := hints2.
Definition o6 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_xboth_R1 40%positive "(#39(((858012#71()#34)(1 858012)))()())"%pstring.
(* [comment removed for export] *)
Definition t7 : CC.cutpoint := CCD.dec_cp_t dict_Cut_annotate_xboth_R1 27%positive "(733104#2#72 56#36()(0 7))"%pstring.
Definition BL7 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_annotate_xboth_R1 3%positive "()"%pstring.
Definition hints7 : list (nat * CC.subst) := hints3.
Definition o7 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_xboth_R1 40%positive "(#39(((733116#71()#72)(1 733116)))()())"%pstring.
