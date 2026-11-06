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
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_pdtor_xboth_T Cut_pdtor_xboth_R0 Cut_pdtor_xboth_R1.
Definition dict_Cut_pdtor_xboth_R2 : CCD.pt := CCD.mk_table 1387%positive "((2 0(1 2)(0 -32))(0 2147450880)(3 1433600 1466368)((0 0)1497016)(0#4 8#2)((0 0)2147630408)(0#6 1(0 0))(5(0 9)1 4611686018427387904)(5(0 10)1 4611686018427387904)((1 2)-32)(2 0(1 10)(0 248))(0#10 8#11)((1 10)0)(0 1434688)(0#13 8#14)((1 2)-24)(0#16 8(1 9))((1 2)-16)(0#18 8(1 8))((1 2)-8)(0#20 8(1 1))((1 10)24)(0#22 1(0 0))((1 10)48)(0#24 1(0 0))((1 10)72)(0#26 1(0 0))((1 10)96)(0 1436192)(0#28 8#29)((1 10)128)(2 0(1 10)(0 96))(0#31 8#32)((1 10)224)(0#34 8(1 36))((1 10)240)(0#36 8(1 35))(6 0 0 1(1 36))(2 9#38(0 1))(5#39 1 1)(5(1 36)265 140737488355328)((1 10)8)(9#42(0 16))((1 10)232)(9#44(0 8))(6#13(0 272))(5(1 10)1048576 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#49 2147450880)(1#50(0 34))((0 0)2147446784)(0 17592186048512)(7#52#53#13(0 272))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(5(1 33)0 4096)(4 0(0 -1)(1 33))(2 0#59(1 34))(5#60 0 4096)(5(1 35)4096 140737479966720)(4(1 35)16)((1 2)-4272)(0 4240)(9#64#65)(0 4272)(6#64#67)(5(1 2)140735332487344 140737488355328)(4(1 2)16)(2 6#1(0 3))(#71 2147450880)(1#72(0 1))(7#64#67#13(0 272))((1 32)0)(7#64#67#75(1 34))(7#13(0 272)#75(1 34))((1 35)0)(2 0(1 36)(0 -1))(7#64#67#78#79)(7#13(0 272)#78#79)(7#75(1 34)#78#79)(7#52#53#75(1 34))(7#52#53#78#79)(#3#5#7#8#3#5#9#12#15#17#19#21#23#25#27#30#33#35#37#40#41#43#45#46#47#48#51#54#55#56#57#58#61#62#63#66#68#69#70#73#74#76#77#80#81#82#83#84)(2 0(1 10)(0 24)))"%pstring.
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CCD.dec_cp_t dict_Cut_pdtor_xboth_R2 238%positive "(731664((1 0)(1 56)#1(1 3)(1 4)(1 57)(1 58)(1 59)(1 10)#2(1 60)(1 61)(1 62)(1 63)(1 64)(1 65)(1 66)(1 67)(1 18)(1 19)(1 20)(1 21)(1 22)(1 23)(1 24)(1 25)(1 26)(1 27)(1 68)(1 69)(1 70)(1 71))#85 72(((1 2)-4272#67)((1 10)0(0 272)))()(0 8))"%pstring.
Definition BL2 : CA.blocks := Eval vm_compute in CCD.dec_bl_t dict_Cut_pdtor_xboth_R2 3%positive "()"%pstring.
Definition hints2 : list (nat * CC.subst) := hints1.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_pdtor_xboth_R2 398%positive "((0(0(731512 732012 732544 1046256 1402040 1403068))(1 0))(((732012((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 57))(6(1 58))(7(1 59))(8(1 8))(9(1 9))(10#86)(11(0 0))(12(2 0(2 6#86(0 3))#2))(13(1 63))(14(1 64))(15(1 65))(16(1 66))(17(1 67))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 68))(29(1 69))(30(1 70))(31(1 71)))()#85)(1 732012)))()())"%pstring.
