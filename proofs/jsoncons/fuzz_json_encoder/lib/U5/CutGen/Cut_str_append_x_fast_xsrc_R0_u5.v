(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_str_append_x_fast_xsrc_T_u5.
Definition dict_Cut_str_append_x_fast_xsrc_R0 : CCD.pt := CCD.mk_table 369%positive "((436288 436536 779340 778312 779720)(0#1)(0 1048576)(5#3 1 4611686018427387904)(4 0(0 -1)(1 12))(4 0(0 2)(1 32))(4 0(0 -1)(1 33))(2 0#6#7)(2 0#5#8)(2 0#9(0 -1))(2 0#8(0 -1))(5(1 12)1 140737488351232)(5(1 33)0 140737488355326)(5#8 2 140737488355328)(5#11 1 140737488355327)(2 0#6(0 1))(6 0 0 1#16)(2 9#17(0 1))(5#18 1 1)((1 10)0)((1 34)0)((1 2)-8384)(0 8384)((1 11)0))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_str_append_x_fast_xsrc_R0 1248%positive "((0#2(16 0(0#2(16 1(16 2(16 3(16 4(3(11 12 2 140737488351232(16 5(16 6(2(1 48)0(1 0)(1 0)))))(16 7(0#2(4#4(1 0))))))))))))(((779340((1(0 436468))(2(2 0(1 2)(0 -48)))(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 12))(10(2 0(1 33)(1 34)))(11(1 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 11))(18(1 33))(19(1 34))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31)))()(#4(5#10 0 140737488355326)(5(2 4#11(1 12))0 0)#12#13#14#15#19(0((1 2)-40)8(1 19))(0((1 2)-32)8(1 18))(0((1 2)-24)8(1 9))(0((1 2)-16)8(1 8))(0((1 2)-8)8(1 1))(0#20 8#16)(0((1 10)8)8(1 33))(0((1 10)16)8(1 34))(5(1 32)24 70368744177664)(5(1 33)0 140737488355328)(5#11 0 140737488355328)(5(1 12)1 140737488355328)(5#10 0 140737488355328)(9#21#6)(6#21#6)(5(1 34)4096 140737488355328)(4(1 34)16)(5(1 11)4096 140737488355328)(5(2 0(1 11)(1 12))4096 140737488355328)(9#20(0 24))(6#20(0 24))(5(1 10)4096 140737488355328)(4(1 10)8)(9#22(0 8344))(6#22#23)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(7#22#23#20(0 24))(7#22#23#24(1 12))(7#20(0 24)#24(1 12))(7#22#23#21#6)(7#20(0 24)#21#6)(7#21#6#24(1 12))))(1 779340)))((0#19)(0#15)(0#14)(0#13)(0#12)(1#11(1 12)1)(3((0 -1)(4 -1)))(1(1 12)#11 0))())"%pstring.
