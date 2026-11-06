(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm4PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm4CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_enc_dtor_xasan_T Cut_enc_dtor_xasan_R0.
Definition dict_Cut_enc_dtor_xasan_R1 : CCD.pt := CCD.mk_table 1383%positive "((2 0(1 2)(0 -80))(2 0(1 2)(0 -24))(0 2147450880)(2 6#2(0 3))(2 0#4#3)(3 1417216 1449984)((0 0)1482488)(0#7 8#3)(5(0 20)1 4611686018427387904)((1 2)-80)(0#10 8#2)((1 2)-72)((1 10)272)(0#13 8(1 32))((1 2)-64)(0#15 8(1 18))((1 2)-56)(0#17 8(1 9))((1 2)-48)(0#19 8(1 10))((1 2)-40)(0 728756)(0#21 8#22)((1 2)-24)(2 0(1 10)(0 264))(0#24 8#25)((1 2)-16)(0#27 8(1 8))((1 2)-8)(0#29 8(1 1))((1 10)48)(0#31 1(0 2))((1 10)96)(0#33 1(0 0))((1 10)120)(0#35 1(0 0))((1 10)144)(0#37 1(0 0))((1 10)168)(0#39 1(0 0))((1 10)192)(0#41 1(0 0))((1 10)216)(0#43 1(0 0))((1 10)264)(0#45 8(1 32))((1 10)280)(2 0(1 32)(1 34))(0#47 8#48)(5(1 32)4096 140737479966720)(4(1 32)16)(5(1 34)32 32768)(5(1 33)0 32768)(4 0(0 -1)(1 33))(2 0#54(1 34))(5#55 0 32768)(2 9(1 33)(0 31))(5#57 0 0)(2 9(1 34)(0 31))(5#59 0 0)((1 2)-4224)(0 4224)((1 32)0)(7#61#62#63(1 34))((1 10)0)(7#65(0 408)#63(1 34))((0 0)2147446784)(0 17592186048512)(7#67#68#63(1 34))(2 6(1 10)(0 3))(#70 2147450880)(2 6(1 32)(0 3))(#72 2147450880)(2 0(1 34)(0 7))(2 6#74(0 3))(7#71(0 51)#73#75)(#4 2147450880)(7#77(0 1)#73#75)(7#65(0 408)#73#75)(7#61#62#73#75)(9#65(0 272))(9#47(0 128))(6#65(0 408))(5(1 10)7077888 140737479966312)(4(1 10)8)(1#71(0 51))(7#67#68#65(0 408))(0 4144)(9#61#88)((1 2)-32)(9#90(0 8))(6#61#62)(5(1 2)140735332487296 140737488355328)(4(1 2)16)(1#77(0 1))(7#61#62#65(0 408))(7#71(0 51)#77(0 1))(5(0 19)1 4611686018427387904))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_enc_dtor_xasan_R1 398%positive "(763412((1 0)(1 40)#1(1 3)(1 4)(1 41)(1 42)(1 43)#2#3(1 44)(1 45)(1 46)(1 47)(1 48)(1 49)(1 50)(1 51)#5(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 52)(1 53)(1 54)(1 55))(#6#8#9#11(0#12 8(0 762964))#14#16#18#20#23#26#28#30#6#8#32#34#36#38#40#42#44#46#49#50#51#52#53#56#58#60#64#66#69#76#78#79#80#81#82#83#84#85#86#87#89#91#92#93#94#95#96#97)56(((1 2)-4224#62)((1 10)0(0 408)))()(0 19))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_enc_dtor_xasan_R1 17%positive "(((1 32)(1 34)))"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_enc_dtor_xasan_R1 580%positive "((0(0(728724 728724 728792 540712 1031544 1387168 1388196))(4#98(1 0)))(((540712((1(0 763244))(2#1)(3(1 3))(4(1 4))(5(1 41))(6(1 42))(7(1 43))(8#2)(9#3)(10(1 32))(11#48)(12(1 32))(13#48)(14(2 6(2 0(1 10)(0 272))(0 3)))(15(1 49))(16(1 50))(17(1 51))(18#5)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 52))(29(1 53))(30(1 54))(31(1 55)))()(#98#11(0#12 8(0 762980))#6#8#9#14#16#18#20#23#26#28#30#6#8#32#34#36#38#40#42#44#46#49#50#51#52#53#56#58#60#64#66#69#76#78#79#80#81#82#83#84#85#86#87#89#91#92#93#94#95#96#97))(1 540712)))()())"%pstring.
