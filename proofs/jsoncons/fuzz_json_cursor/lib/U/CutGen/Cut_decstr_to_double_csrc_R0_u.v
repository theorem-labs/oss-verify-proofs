(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallSums2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Import Cut_decstr_to_double_csrc_T_u.
Definition o0 : CA.pout := CCD.dec_pout 1136%positive "((0(0(259304 259456 748348 259400 751764 753172))(4(5(0 10)1 4611686018427387904)(1 0)))(((748348((1(0 259388))(2(2 0(1 2)(0 -96)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 12))(9(1 10))(10(1 10))(11(2 0(1 2)(0 -64)))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(18(1 18))(19(1 11))(20(2 0(1 10)(1 11)))(21(0 1))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()((5(0 10)1 4611686018427387904)(0((1 2)-64)8(0 0))(0((1 2)-56)8(1 21))(0((1 2)-48)8(1 20))(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(5(1 11)0 67108864)(5(1 10)4096 140737488355328)(2((1 10)0)(1 11)0)(0((2 0(1 10)(1 11))0)1(0 0))(9((1 10)0)(2 0(1 11)(0 1)))(9((1 2)-9040)(0 8976))(6((1 2)-9040)(0 9040))(5(1 2)1099511627776 140737488355328)(4(1 2)16)(9((1 12)0)(0 8))(6((1 12)0)(0 8))(5(1 12)1099511627776 140737488355328)(6((0 0)878428)(0 4))(3 65536 801400)(7((1 2)-9040)(0 9040)((1 12)0)(0 8))(7((1 2)-9040)(0 9040)((1 10)0)(2 0(1 11)(0 1)))(7((0 0)878428)(0 4)((1 10)0)(2 0(1 11)(0 1)))(5(2 0(1 10)(1 11))4096 140737488355328)))(1 748348)))()())"%pstring.
