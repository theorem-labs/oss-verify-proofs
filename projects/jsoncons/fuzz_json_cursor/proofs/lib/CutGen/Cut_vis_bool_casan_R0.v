(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_vis_bool_casan_T.
Definition dict_Cut_vis_bool_casan_R0 : CCD.pt := CCD.mk_table 55%positive "((0 2147450880)((1 10)8)((1 10)0)((1 2)-2624)(0 2624))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_vis_bool_casan_R0 798%positive "((0(0(830164 830320 1330948 1331976))(1 0))(((830320((1(1 1))(2(1 2))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(0 1))(11(2 0(1 10)(0 40)))(12(2 0(1 10)(0 32)))(13(0 0))(14#1)(15(0 0))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((0((1 10)40)8(0 0))(0((1 10)32)1(1 11))(0((1 10)24)8(0 0))(0((1 10)16)1(1 12))(0#2 8(0 8))(0((1 2)-8)8(1 1))(3 1388760 1392480)(0((0 0)1427896)8#1)(9((1 10)17)(0 7))(9((1 10)33)(0 7))(6#2(0 40))(5(1 10)7024640 140737479966672)(4(1 10)8)(1((2 6(1 10)(0 3))2147450880)(0 6))(7((0 0)2147446784)(0 17592186048512)#3(0 48))(9#4(0 2616))(6#4#5)(5(1 2)140735332485696 140737488355328)(4(1 2)16)(7#4#5#3(0 48))(5(1 11)0 1)))(1 830320)))()())"%pstring.
