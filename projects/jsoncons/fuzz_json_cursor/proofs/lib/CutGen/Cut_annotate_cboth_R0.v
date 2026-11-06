(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Corelib Require Import PrimString.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCodec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_annotate_cboth_T.
Definition dict_Cut_annotate_cboth_R0 : CCD.pt := CCD.mk_table 1082%positive "((808928 727976 810224 727788 809056 728100 810352 727932 536604 1336512 1337540)(0#1)(5(0 8)1 4611686018427387904)(4#3(1 0))(0#2#4)(0 809044)(2 0(1 2)(0 -16))(2#7)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 8))(9(1 9))(10(1 32))(2 0(1 32)(1 34))(11#17)(2 0(1 32)(1 33))(12#19)(14(0 1))(15(0 0))(16(1 16))(17(1 17))(18(1 18))(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))((1 2)-24)((1 2)-16)(0#40 8(1 8))((1 2)-8)(0#42 8(1 1))(3 1393824 1397544)((0 0)1432824)(0 2147450880)(0#45 8#46)((1 10)0)(0#48 8(1 32))((1 10)16)(0#50 8#17)(5(1 10)1048576 140737488355304)(4(1 10)8)(2 6(1 10)(0 3))(#54 2147450880)(1#55(0 3))((0 0)2147446784)(0 17592186048512)(7#57#58#48(0 24))(5(1 32)17594333495296 140737479966720)(4(1 32)16)(5(1 34)1 4096)(4 0(0 -1)(1 33))(2 0#63(1 34))(5#64 0 4096)(5(1 33)0 4096)((1 2)-4128)(0 4104)(9#67#68)(0 4128)(6#67#70)(5(1 2)140735332487200 140737488355328)(4(1 2)16)(7#67#70#48(0 24))((1 10)8)(0#75 8#19)(5(1 11)0 4096)(1 536604)(0 728088)(2 0(1 11)(1 32))(0 810340)(0 727920))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_cboth_R0 216%positive "(#5(((536604((1#6)#8#9#10#11#12#13#14#15#16#18#20(13(2 0(1 11)#19))#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38)()(#3(0#39 8#6)#41#43#44#47#49#51#52#53#56#59#60#61#62#65#66#69#71#72#73#74#76#77))#78))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_cboth_R0 238%positive "(#5(((536604((1#79)#8#9#10#11#12#13#14#15#16#18(12#80)(13#19)#21#22(16(2 6(2 0(1 10)(0 8))(0 3)))#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38)()(#3(0#39 8#79)#41#43#44#47#49#51#52#53#56#59#60#61#62#65#66#69#71#72#73#74#76#77))#78))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_cboth_R0 208%positive "(#5(((536604((1#81)#8#9#10#11#12#13#14#15#16#18(12#17)(13#80)#21#22#23#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38)()(#3(0#39 8#81)#41#43#44#47#49#51#52#53#56#59#60#61#62#65#66#69#71#72#73#74#77))#78))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_annotate_cboth_R0 232%positive "(#5(((536604((1#82)#8#9#10#11#12#13#14#15#16#18#20(13#17)#21#22(16(2 6(2 0(1 10)(0 16))(0 3)))#24#25#26#27#28#29#30#31#32#33#34#35#36#37#38)()(#3(0#39 8#82)#41#43#44#47#49#51#52#53#56#59#60#61#62#65#66#69#71#72#73#74#76))#78))()())"%pstring.
