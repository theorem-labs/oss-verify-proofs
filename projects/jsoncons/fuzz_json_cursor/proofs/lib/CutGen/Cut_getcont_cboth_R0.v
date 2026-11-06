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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_getcont_cboth_T.
Definition dict_Cut_getcont_cboth_R0 : CCD.pt := CCD.mk_table 1398%positive "((841728 841728 841728 841728 842596 849628 846852 842188 521936 729476 863168 843204 844828 1336512 1337540)(0#1)(5(0 24)1 4611686018427387904)(4#3(1 0))(0#2#4)(0 842464)(1#6)(2 0(1 2)(0 -48))(2#8)(3(1 3))(4(1 4))(5(1 5))(6(1 6))(7(1 7))(8(1 10))(9(1 11))(10(1 13))(11(0 11))(12(1 12))(13(1 13))(14(1 14))(15(1 15))(16(1 16))(17(1 17))(0 2147450880)(18#25)(19(1 19))(20(1 20))(21(1 21))(22(1 22))(23(1 23))(24(1 24))(25(1 25))(26(1 26))(27(1 27))(28(1 28))(29(1 29))(30(1 30))(31(1 31))(#7#9#10#11#12#13#14#15#16#17#18#19#20#21#22#23#24#26#27#28#29#30#31#32#33#34#35#36#37#38#39)((1 2)-33)(0#41 1(1 12))((1 2)-32)(0#43 8(1 18))((1 2)-24)(0#45 8(1 9))((1 2)-16)(0#47 8(1 8))((1 2)-8)(0#49 8(1 1))(3 1368064 1400832)((0 0)1432824)(0#52 8#25)((1 10)0)(9#54(0 24))(6#54(0 24))(5(1 10)7028736 140737488351232)(4(1 10)8)(2 6(1 10)(0 3))(#59 2147450880)(1#60(0 3))((0 0)2147446784)(0 17592186048512)(7#62#63#54(0 24))((1 11)0)(9#65(0 40))(5(1 11)7028736 140737488351232)(4(1 11)8)(2 6(1 11)(0 3))(#69 2147450880)(1#70(0 5))(7#62#63#65(0 40))((1 13)0)(9#73(0 16))(6#73(0 16))(5(1 13)7028736 140737488351232)(4(1 13)8)(2 6(1 13)(0 3))(#78 2147450880)(1#79(0 2))(7#62#63#73(0 16))((1 2)-14384)(0 14351)(9#82#83)(0 14384)(6#82#85)(5(1 2)140735332497456 140737488355328)(4(1 2)32)(7#82#85#54(0 24))(7#82#85#65(0 40))(7#82#85#73(0 16))(7#54(0 24)#65(0 40))(7#54(0 24)#73(0 16))(7#65(0 40)#73(0 16))(1 729476))"%pstring.
Definition o0 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R0 150%positive "(#5(((729476#40()(#3#42#44#46#48#50#51#53#55#56#57#58#61#64#66#67#68#71#72#74#75#76#77#80#81#84#86#87#88#89#90#91#92#93#94(0#65 8(0 256))))#95))()())"%pstring.
Definition o1 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R0 150%positive "(#5(((729476#40()(#3#42#44#46#48#50#51#53#55#56#57#58#61#64#66#67#68#71#72#74#75#76#77#80#81#84#86#87#88#89#90#91#92#93#94(0#65 8(0 512))))#95))()())"%pstring.
Definition o2 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R0 151%positive "(#5(((729476#40()(#3#42#44#46#48#50#51#53#55#56#57#58#61#64#66#67#68#71#72#74#75#76#77#80#81#84#86#87#88#89#90#91#92#93#94(0#65 8(0 1024))))#95))()())"%pstring.
Definition o3 : CA.pout := CCD.dec_pout_t dict_Cut_getcont_cboth_R0 151%positive "(#5(((729476#40()(#3#42#44#46#48#50#51#53#55#56#57#58#61#64#66#67#68#71#72#74#75#76#77#80#81#84#86#87#88#89#90#91#92#93#94(0#65 8(0 2048))))#95))()())"%pstring.
