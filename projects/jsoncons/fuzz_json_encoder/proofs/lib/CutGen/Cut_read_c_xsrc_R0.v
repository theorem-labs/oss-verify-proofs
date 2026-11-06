(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm6CutKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import Cut_read_c_xsrc_T.
Definition dict_Cut_read_c_xsrc_R0 : CCD.pt := CCD.mk_table 797%positive "((279080 278504 278644 278988 278800 279120 763484 764892)(0#1)(1(1 33))(2 0(1 2)(0 -32))(2#4)(3(1 35))(4(1 36))(5(1 37))(6(1 38))(7(1 39))(8(1 40))(9(1 41))(10(1 42))(11(1 43))(2 9(1 65)(0 2))(12#15)(13(0 120))(14(1 46))(15(1 47))(16(1 48))(17(1 49))(18(1 50))(19(1 51))(20(1 52))(21(1 53))(22(1 54))(23(1 55))(24(1 56))(25(1 57))(26(1 58))(27(1 59))(28(1 60))(29(1 61))(30(1 62))(31(1 63))(#3#5#6#7#8#9#10#11#12#13#14#16#17#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)(2 1#15(0 0))(2 4#37(0 1))(2 1(1 42)(1 43))(2 4#39(0 1))(5#40 1 1)(5(1 2)1099511627776 140737488355328)(4(1 2)16)(5(1 40)4096 140737488355328)((1 40)288)(0#45 8(0 0))((1 40)240)(0#47 8(1 64))((1 64)0)(0 803800)(0#49 8#50)((1 64)152)(0#52 1(1 65))(3 65536 813152)(5(1 64)4096 140737488355328)(5(1 65)0 255)(1 278988))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_read_c_xsrc_R0 457%positive "((3(0#2(3(16 0(0#2(1 0)))(11 65 1 255(16 1(0#2(1 1))))))(0#2(1 2)))(((278988#36()((5(2 0(4 0(0 -1)#15)(0 1))1 1)(5#38 1 1)#41#42#43#44#46#48#51#53#54#55#56))#57)((279120#36()((5(2 0#15(0 -1))0 1)(5(1 65)1 255)(5#38 0 0)#41#42#43#44#46#48#51#53#54#55#56))(1 279120))((278988(#3#5#6#7#8#9#10#11#12#13#14(12(1 44))(13(1 45))#18#19#20#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35)()((5#40 0 0)#42#43#44#46#48#51#53#54#55#56))#57))((1#37(0 1)1)(1(0 1)#37 0))())"%pstring.
