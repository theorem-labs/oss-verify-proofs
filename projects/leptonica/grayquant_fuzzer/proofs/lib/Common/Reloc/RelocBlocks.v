(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import Reloc.

(* [comment removed for export] *)
Abbreviation B_ABS0 := 8%positive (only parsing).
Abbreviation dABS0 := (rl_delta 8%positive).
(* [comment removed for export] *)
Abbreviation B_ABSGP := 8%positive (only parsing).
Abbreviation dABSGP := (rl_delta 8%positive).
(* [comment removed for export] *)
Abbreviation B_F_13084 := 1000%positive (only parsing).
Abbreviation dF_13084 := (rl_delta 1000%positive).
(* [comment removed for export] *)
Abbreviation B_F_130a0 := 1001%positive (only parsing).
Abbreviation dF_130a0 := (rl_delta 1001%positive).
(* [comment removed for export] *)
Abbreviation B_F_130cc := 1002%positive (only parsing).
Abbreviation dF_130cc := (rl_delta 1002%positive).
(* [comment removed for export] *)
Abbreviation B_F_13140 := 1003%positive (only parsing).
Abbreviation dF_13140 := (rl_delta 1003%positive).
(* [comment removed for export] *)
Abbreviation B_F_131d0 := 1004%positive (only parsing).
Abbreviation dF_131d0 := (rl_delta 1004%positive).
(* [comment removed for export] *)
Abbreviation B_F_13494 := 1005%positive (only parsing).
Abbreviation dF_13494 := (rl_delta 1005%positive).
(* [comment removed for export] *)
Abbreviation B_F_13498 := 1006%positive (only parsing).
Abbreviation dF_13498 := (rl_delta 1006%positive).
(* [comment removed for export] *)
Abbreviation B_F_134a0 := 1007%positive (only parsing).
Abbreviation dF_134a0 := (rl_delta 1007%positive).
(* [comment removed for export] *)
Abbreviation B_F_135ac := 1008%positive (only parsing).
Abbreviation dF_135ac := (rl_delta 1008%positive).
(* [comment removed for export] *)
Abbreviation B_F_1365c := 1009%positive (only parsing).
Abbreviation dF_1365c := (rl_delta 1009%positive).
(* [comment removed for export] *)
Abbreviation B_F_13660 := 1010%positive (only parsing).
Abbreviation dF_13660 := (rl_delta 1010%positive).
(* [comment removed for export] *)
Abbreviation B_F_13694 := 1011%positive (only parsing).
Abbreviation dF_13694 := (rl_delta 1011%positive).
(* [comment removed for export] *)
Abbreviation B_F_13730 := 1012%positive (only parsing).
Abbreviation dF_13730 := (rl_delta 1012%positive).
(* [comment removed for export] *)
Abbreviation B_F_13764 := 1013%positive (only parsing).
Abbreviation dF_13764 := (rl_delta 1013%positive).
(* [comment removed for export] *)
Abbreviation B_F_1377c := 1014%positive (only parsing).
Abbreviation dF_1377c := (rl_delta 1014%positive).
(* [comment removed for export] *)
Abbreviation B_F_14d1c := 1015%positive (only parsing).
Abbreviation dF_14d1c := (rl_delta 1015%positive).
(* [comment removed for export] *)
Abbreviation B_F_1516c := 1016%positive (only parsing).
Abbreviation dF_1516c := (rl_delta 1016%positive).
(* [comment removed for export] *)
Abbreviation B_F_15170 := 1017%positive (only parsing).
Abbreviation dF_15170 := (rl_delta 1017%positive).
(* [comment removed for export] *)
Abbreviation B_F_1539c := 1018%positive (only parsing).
Abbreviation dF_1539c := (rl_delta 1018%positive).
(* [comment removed for export] *)
Abbreviation B_F_153e8 := 1019%positive (only parsing).
Abbreviation dF_153e8 := (rl_delta 1019%positive).
(* [comment removed for export] *)
Abbreviation B_F_15448 := 1020%positive (only parsing).
Abbreviation dF_15448 := (rl_delta 1020%positive).
(* [comment removed for export] *)
Abbreviation B_F_15490 := 1021%positive (only parsing).
Abbreviation dF_15490 := (rl_delta 1021%positive).
(* [comment removed for export] *)
Abbreviation B_F_1574c := 1022%positive (only parsing).
Abbreviation dF_1574c := (rl_delta 1022%positive).
(* [comment removed for export] *)
Abbreviation B_F_15758 := 1023%positive (only parsing).
Abbreviation dF_15758 := (rl_delta 1023%positive).
(* [comment removed for export] *)
Abbreviation B_F_15794 := 1024%positive (only parsing).
Abbreviation dF_15794 := (rl_delta 1024%positive).
(* [comment removed for export] *)
Abbreviation B_F_157b0 := 1025%positive (only parsing).
Abbreviation dF_157b0 := (rl_delta 1025%positive).
(* [comment removed for export] *)
Abbreviation B_F_157b4 := 1026%positive (only parsing).
Abbreviation dF_157b4 := (rl_delta 1026%positive).
(* [comment removed for export] *)
Abbreviation B_F_15800 := 1027%positive (only parsing).
Abbreviation dF_15800 := (rl_delta 1027%positive).
(* [comment removed for export] *)
Abbreviation B_F_15874 := 1028%positive (only parsing).
Abbreviation dF_15874 := (rl_delta 1028%positive).
(* [comment removed for export] *)
Abbreviation B_F_15958 := 1029%positive (only parsing).
Abbreviation dF_15958 := (rl_delta 1029%positive).
(* [comment removed for export] *)
Abbreviation B_F_159b8 := 1030%positive (only parsing).
Abbreviation dF_159b8 := (rl_delta 1030%positive).
(* [comment removed for export] *)
Abbreviation B_F_159c0 := 1031%positive (only parsing).
Abbreviation dF_159c0 := (rl_delta 1031%positive).
(* [comment removed for export] *)
Abbreviation B_F_159f8 := 1032%positive (only parsing).
Abbreviation dF_159f8 := (rl_delta 1032%positive).
(* [comment removed for export] *)
Abbreviation B_F_159fc := 1033%positive (only parsing).
Abbreviation dF_159fc := (rl_delta 1033%positive).
(* [comment removed for export] *)
Abbreviation B_F_15a00 := 1034%positive (only parsing).
Abbreviation dF_15a00 := (rl_delta 1034%positive).
(* [comment removed for export] *)
Abbreviation B_F_15b38 := 1035%positive (only parsing).
Abbreviation dF_15b38 := (rl_delta 1035%positive).
(* [comment removed for export] *)
Abbreviation B_F_15b3c := 1036%positive (only parsing).
Abbreviation dF_15b3c := (rl_delta 1036%positive).
(* [comment removed for export] *)
Abbreviation B_F_15b40 := 1037%positive (only parsing).
Abbreviation dF_15b40 := (rl_delta 1037%positive).
(* [comment removed for export] *)
Abbreviation B_F_15d0c := 1038%positive (only parsing).
Abbreviation dF_15d0c := (rl_delta 1038%positive).
(* [comment removed for export] *)
Abbreviation B_F_15e1c := 1039%positive (only parsing).
Abbreviation dF_15e1c := (rl_delta 1039%positive).
(* [comment removed for export] *)
Abbreviation B_F_161f4 := 1040%positive (only parsing).
Abbreviation dF_161f4 := (rl_delta 1040%positive).
(* [comment removed for export] *)
Abbreviation B_F_164cc := 1041%positive (only parsing).
Abbreviation dF_164cc := (rl_delta 1041%positive).
(* [comment removed for export] *)
Abbreviation B_F_1683c := 1042%positive (only parsing).
Abbreviation dF_1683c := (rl_delta 1042%positive).
(* [comment removed for export] *)
Abbreviation B_F_170e0 := 1043%positive (only parsing).
Abbreviation dF_170e0 := (rl_delta 1043%positive).
(* [comment removed for export] *)
Abbreviation B_F_17230 := 1044%positive (only parsing).
Abbreviation dF_17230 := (rl_delta 1044%positive).
(* [comment removed for export] *)
Abbreviation B_F_173a8 := 1045%positive (only parsing).
Abbreviation dF_173a8 := (rl_delta 1045%positive).
(* [comment removed for export] *)
Abbreviation B_F_17440 := 1046%positive (only parsing).
Abbreviation dF_17440 := (rl_delta 1046%positive).
(* [comment removed for export] *)
Abbreviation B_F_17444 := 1047%positive (only parsing).
Abbreviation dF_17444 := (rl_delta 1047%positive).
(* [comment removed for export] *)
Abbreviation B_F_17530 := 1048%positive (only parsing).
Abbreviation dF_17530 := (rl_delta 1048%positive).
(* [comment removed for export] *)
Abbreviation B_F_17578 := 1049%positive (only parsing).
Abbreviation dF_17578 := (rl_delta 1049%positive).
(* [comment removed for export] *)
Abbreviation B_F_175c0 := 1050%positive (only parsing).
Abbreviation dF_175c0 := (rl_delta 1050%positive).
(* [comment removed for export] *)
Abbreviation B_F_176bc := 1051%positive (only parsing).
Abbreviation dF_176bc := (rl_delta 1051%positive).
(* [comment removed for export] *)
Abbreviation B_F_1771c := 1052%positive (only parsing).
Abbreviation dF_1771c := (rl_delta 1052%positive).
(* [comment removed for export] *)
Abbreviation B_F_178c0 := 1053%positive (only parsing).
Abbreviation dF_178c0 := (rl_delta 1053%positive).
(* [comment removed for export] *)
Abbreviation B_F_17a50 := 1054%positive (only parsing).
Abbreviation dF_17a50 := (rl_delta 1054%positive).
(* [comment removed for export] *)
Abbreviation B_F_17a58 := 1055%positive (only parsing).
Abbreviation dF_17a58 := (rl_delta 1055%positive).
(* [comment removed for export] *)
Abbreviation B_F_17a5c := 1056%positive (only parsing).
Abbreviation dF_17a5c := (rl_delta 1056%positive).
(* [comment removed for export] *)
Abbreviation B_F_17a88 := 1057%positive (only parsing).
Abbreviation dF_17a88 := (rl_delta 1057%positive).
(* [comment removed for export] *)
Abbreviation B_F_17aec := 1058%positive (only parsing).
Abbreviation dF_17aec := (rl_delta 1058%positive).
(* [comment removed for export] *)
Abbreviation B_F_17b40 := 1059%positive (only parsing).
Abbreviation dF_17b40 := (rl_delta 1059%positive).
(* [comment removed for export] *)
Abbreviation B_F_17b9c := 1060%positive (only parsing).
Abbreviation dF_17b9c := (rl_delta 1060%positive).
(* [comment removed for export] *)
Abbreviation B_F_17cd4 := 1061%positive (only parsing).
Abbreviation dF_17cd4 := (rl_delta 1061%positive).
(* [comment removed for export] *)
Abbreviation B_F_17d8c := 1062%positive (only parsing).
Abbreviation dF_17d8c := (rl_delta 1062%positive).
(* [comment removed for export] *)
Abbreviation B_F_17dbc := 1063%positive (only parsing).
Abbreviation dF_17dbc := (rl_delta 1063%positive).
(* [comment removed for export] *)
Abbreviation B_F_17f6c := 1064%positive (only parsing).
Abbreviation dF_17f6c := (rl_delta 1064%positive).
(* [comment removed for export] *)
Abbreviation B_F_18d9c := 1065%positive (only parsing).
Abbreviation dF_18d9c := (rl_delta 1065%positive).
(* [comment removed for export] *)
Abbreviation B_F_18ed0 := 1066%positive (only parsing).
Abbreviation dF_18ed0 := (rl_delta 1066%positive).
(* [comment removed for export] *)
Abbreviation B_F_18fa4 := 1067%positive (only parsing).
Abbreviation dF_18fa4 := (rl_delta 1067%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a66c := 1068%positive (only parsing).
Abbreviation dF_1a66c := (rl_delta 1068%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a690 := 1069%positive (only parsing).
Abbreviation dF_1a690 := (rl_delta 1069%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a7bc := 1070%positive (only parsing).
Abbreviation dF_1a7bc := (rl_delta 1070%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a94c := 1071%positive (only parsing).
Abbreviation dF_1a94c := (rl_delta 1071%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a954 := 1072%positive (only parsing).
Abbreviation dF_1a954 := (rl_delta 1072%positive).
(* [comment removed for export] *)
Abbreviation B_F_1a998 := 1073%positive (only parsing).
Abbreviation dF_1a998 := (rl_delta 1073%positive).
(* [comment removed for export] *)
Abbreviation B_F_1aa70 := 1074%positive (only parsing).
Abbreviation dF_1aa70 := (rl_delta 1074%positive).
(* [comment removed for export] *)
Abbreviation B_F_1ab38 := 1075%positive (only parsing).
Abbreviation dF_1ab38 := (rl_delta 1075%positive).
(* [comment removed for export] *)
Abbreviation B_F_1b238 := 1076%positive (only parsing).
Abbreviation dF_1b238 := (rl_delta 1076%positive).
(* [comment removed for export] *)
Abbreviation B_F_1b340 := 1077%positive (only parsing).
Abbreviation dF_1b340 := (rl_delta 1077%positive).
(* [comment removed for export] *)
Abbreviation B_F_1b350 := 1078%positive (only parsing).
Abbreviation dF_1b350 := (rl_delta 1078%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bb1c := 1079%positive (only parsing).
Abbreviation dF_1bb1c := (rl_delta 1079%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bb4c := 1080%positive (only parsing).
Abbreviation dF_1bb4c := (rl_delta 1080%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bb58 := 1081%positive (only parsing).
Abbreviation dF_1bb58 := (rl_delta 1081%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bbec := 1082%positive (only parsing).
Abbreviation dF_1bbec := (rl_delta 1082%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bcd8 := 1083%positive (only parsing).
Abbreviation dF_1bcd8 := (rl_delta 1083%positive).
(* [comment removed for export] *)
Abbreviation B_F_1bd80 := 1084%positive (only parsing).
Abbreviation dF_1bd80 := (rl_delta 1084%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c684 := 1085%positive (only parsing).
Abbreviation dF_1c684 := (rl_delta 1085%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c6a0 := 1086%positive (only parsing).
Abbreviation dF_1c6a0 := (rl_delta 1086%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c740 := 1087%positive (only parsing).
Abbreviation dF_1c740 := (rl_delta 1087%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c80c := 1088%positive (only parsing).
Abbreviation dF_1c80c := (rl_delta 1088%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c8e8 := 1089%positive (only parsing).
Abbreviation dF_1c8e8 := (rl_delta 1089%positive).
(* [comment removed for export] *)
Abbreviation B_F_1c9b4 := 1090%positive (only parsing).
Abbreviation dF_1c9b4 := (rl_delta 1090%positive).
(* [comment removed for export] *)
Abbreviation B_F_1cdb8 := 1091%positive (only parsing).
Abbreviation dF_1cdb8 := (rl_delta 1091%positive).
(* [comment removed for export] *)
Abbreviation B_F_1ceb0 := 1092%positive (only parsing).
Abbreviation dF_1ceb0 := (rl_delta 1092%positive).
(* [comment removed for export] *)
Abbreviation B_F_1cf40 := 1093%positive (only parsing).
Abbreviation dF_1cf40 := (rl_delta 1093%positive).
(* [comment removed for export] *)
Abbreviation B_F_1cf84 := 1094%positive (only parsing).
Abbreviation dF_1cf84 := (rl_delta 1094%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d20c := 1095%positive (only parsing).
Abbreviation dF_1d20c := (rl_delta 1095%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d280 := 1096%positive (only parsing).
Abbreviation dF_1d280 := (rl_delta 1096%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d2a4 := 1097%positive (only parsing).
Abbreviation dF_1d2a4 := (rl_delta 1097%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d2a8 := 1098%positive (only parsing).
Abbreviation dF_1d2a8 := (rl_delta 1098%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d2b4 := 1099%positive (only parsing).
Abbreviation dF_1d2b4 := (rl_delta 1099%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d308 := 1100%positive (only parsing).
Abbreviation dF_1d308 := (rl_delta 1100%positive).
(* [comment removed for export] *)
Abbreviation B_F_1d314 := 1101%positive (only parsing).
Abbreviation dF_1d314 := (rl_delta 1101%positive).
(* [comment removed for export] *)
Abbreviation B_E_LLVMFuzzerTestOneInput := 3000%positive (only parsing).
Abbreviation dE_LLVMFuzzerTestOneInput := (rl_delta 3000%positive).
(* [comment removed for export] *)
Abbreviation B_E_pixDeserializeFromMemory := 3001%positive (only parsing).
Abbreviation dE_pixDeserializeFromMemory := (rl_delta 3001%positive).
(* [comment removed for export] *)
Abbreviation B_S_102e7 := 4000%positive (only parsing).
Abbreviation dS_102e7 := (rl_delta 4000%positive).
(* [comment removed for export] *)
Abbreviation B_S_103fc := 4001%positive (only parsing).
Abbreviation dS_103fc := (rl_delta 4001%positive).
(* [comment removed for export] *)
Abbreviation B_S_10445 := 4002%positive (only parsing).
Abbreviation dS_10445 := (rl_delta 4002%positive).
(* [comment removed for export] *)
Abbreviation B_S_10459 := 4003%positive (only parsing).
Abbreviation dS_10459 := (rl_delta 4003%positive).
(* [comment removed for export] *)
Abbreviation B_S_1045d := 4004%positive (only parsing).
Abbreviation dS_1045d := (rl_delta 4004%positive).
(* [comment removed for export] *)
Abbreviation B_S_1045e := 4005%positive (only parsing).
Abbreviation dS_1045e := (rl_delta 4005%positive).
(* [comment removed for export] *)
Abbreviation B_S_10492 := 4006%positive (only parsing).
Abbreviation dS_10492 := (rl_delta 4006%positive).
(* [comment removed for export] *)
Abbreviation B_S_104a3 := 4007%positive (only parsing).
Abbreviation dS_104a3 := (rl_delta 4007%positive).
(* [comment removed for export] *)
Abbreviation B_S_10563 := 4008%positive (only parsing).
Abbreviation dS_10563 := (rl_delta 4008%positive).
(* [comment removed for export] *)
Abbreviation B_S_106e4 := 4009%positive (only parsing).
Abbreviation dS_106e4 := (rl_delta 4009%positive).
(* [comment removed for export] *)
Abbreviation B_S_106e8 := 4010%positive (only parsing).
Abbreviation dS_106e8 := (rl_delta 4010%positive).
(* [comment removed for export] *)
Abbreviation B_S_108b7 := 4011%positive (only parsing).
Abbreviation dS_108b7 := (rl_delta 4011%positive).
(* [comment removed for export] *)
Abbreviation B_S_108cc := 4012%positive (only parsing).
Abbreviation dS_108cc := (rl_delta 4012%positive).
(* [comment removed for export] *)
Abbreviation B_S_1097c := 4013%positive (only parsing).
Abbreviation dS_1097c := (rl_delta 4013%positive).
(* [comment removed for export] *)
Abbreviation B_S_109b4 := 4014%positive (only parsing).
Abbreviation dS_109b4 := (rl_delta 4014%positive).
(* [comment removed for export] *)
Abbreviation B_S_109eb := 4015%positive (only parsing).
Abbreviation dS_109eb := (rl_delta 4015%positive).
(* [comment removed for export] *)
Abbreviation B_S_10a13 := 4016%positive (only parsing).
Abbreviation dS_10a13 := (rl_delta 4016%positive).
(* [comment removed for export] *)
Abbreviation B_S_10a6d := 4017%positive (only parsing).
Abbreviation dS_10a6d := (rl_delta 4017%positive).
(* [comment removed for export] *)
Abbreviation B_S_10a77 := 4018%positive (only parsing).
Abbreviation dS_10a77 := (rl_delta 4018%positive).
(* [comment removed for export] *)
Abbreviation B_A_10b04 := 5000%positive (only parsing).
Abbreviation dA_10b04 := (rl_delta 5000%positive).
(* [comment removed for export] *)
Abbreviation B_A_113b4 := 5001%positive (only parsing).
Abbreviation dA_113b4 := (rl_delta 5001%positive).
(* [comment removed for export] *)
Abbreviation B_A_1144f := 5002%positive (only parsing).
Abbreviation dA_1144f := (rl_delta 5002%positive).
(* [comment removed for export] *)
Abbreviation B_A_11458 := 5003%positive (only parsing).
Abbreviation dA_11458 := (rl_delta 5003%positive).
(* [comment removed for export] *)
Abbreviation B_A_11460 := 5004%positive (only parsing).
Abbreviation dA_11460 := (rl_delta 5004%positive).
(* [comment removed for export] *)
Abbreviation B_A_11468 := 5005%positive (only parsing).
Abbreviation dA_11468 := (rl_delta 5005%positive).
(* [comment removed for export] *)
Abbreviation B_A_11480 := 5006%positive (only parsing).
Abbreviation dA_11480 := (rl_delta 5006%positive).
(* [comment removed for export] *)
Abbreviation B_A_114a0 := 5007%positive (only parsing).
Abbreviation dA_114a0 := (rl_delta 5007%positive).
(* [comment removed for export] *)
Abbreviation B_A_114a8 := 5008%positive (only parsing).
Abbreviation dA_114a8 := (rl_delta 5008%positive).
(* [comment removed for export] *)
Abbreviation B_A_117c0 := 5009%positive (only parsing).
Abbreviation dA_117c0 := (rl_delta 5009%positive).
(* [comment removed for export] *)
Abbreviation B_A_117d0 := 5010%positive (only parsing).
Abbreviation dA_117d0 := (rl_delta 5010%positive).
(* [comment removed for export] *)
Abbreviation B_A_11968 := 5011%positive (only parsing).
Abbreviation dA_11968 := (rl_delta 5011%positive).
(* [comment removed for export] *)
Abbreviation B_A_1e368 := 5012%positive (only parsing).
Abbreviation dA_1e368 := (rl_delta 5012%positive).
(* [comment removed for export] *)
Abbreviation B_A_1f3f8 := 5013%positive (only parsing).
Abbreviation dA_1f3f8 := (rl_delta 5013%positive).
(* [comment removed for export] *)
Abbreviation B_A_1f630 := 5015%positive (only parsing).
Abbreviation dA_1f630 := (rl_delta 5015%positive).
(* [comment removed for export] *)
Abbreviation B_A_1e348 := 5016%positive (only parsing).
Abbreviation dA_1e348 := (rl_delta 5016%positive).
(* [comment removed for export] *)
Abbreviation B_A_10a80 := 5018%positive (only parsing).
Abbreviation dA_10a80 := (rl_delta 5018%positive).
(* [comment removed for export] *)
Abbreviation B_A_1f440 := 5019%positive (only parsing).
Abbreviation dA_1f440 := (rl_delta 5019%positive).
(* [comment removed for export] *)
Abbreviation B_A_113d4 := 5020%positive (only parsing).
Abbreviation dA_113d4 := (rl_delta 5020%positive).
(* [comment removed for export] *)
Abbreviation B_A_11470 := 5021%positive (only parsing).
Abbreviation dA_11470 := (rl_delta 5021%positive).
(* [comment removed for export] *)
Abbreviation B_A_11478 := 5022%positive (only parsing).
Abbreviation dA_11478 := (rl_delta 5022%positive).
(* [comment removed for export] *)
Abbreviation B_A_11488 := 5023%positive (only parsing).
Abbreviation dA_11488 := (rl_delta 5023%positive).
(* [comment removed for export] *)
Abbreviation B_A_11490 := 5024%positive (only parsing).
Abbreviation dA_11490 := (rl_delta 5024%positive).
(* [comment removed for export] *)
Abbreviation B_A_11498 := 5025%positive (only parsing).
Abbreviation dA_11498 := (rl_delta 5025%positive).
(* [comment removed for export] *)
Abbreviation B_A_1e3a0 := 5026%positive (only parsing).
Abbreviation dA_1e3a0 := (rl_delta 5026%positive).
(* [comment removed for export] *)
Abbreviation B_A_1e3b8 := 5027%positive (only parsing).
Abbreviation dA_1e3b8 := (rl_delta 5027%positive).
(* [comment removed for export] *)
Abbreviation B_A_1f430 := 5028%positive (only parsing).
Abbreviation dA_1f430 := (rl_delta 5028%positive).
(* [comment removed for export] *)
Abbreviation B_A_2f6b0 := 5029%positive (only parsing).
Abbreviation dA_2f6b0 := (rl_delta 5029%positive).
Abbreviation B_A_2f6b0s := 5036%positive (only parsing).
Abbreviation dA_2f6b0s := (rl_delta 5036%positive).
Abbreviation B_A_2f6b8 := 5037%positive (only parsing).
Abbreviation dA_2f6b8 := (rl_delta 5037%positive).
(* [comment removed for export] *)
Abbreviation B_A_2f840 := 5030%positive (only parsing).
Abbreviation dA_2f840 := (rl_delta 5030%positive).
(* [comment removed for export] *)
Abbreviation B_A_2f848 := 5031%positive (only parsing).
Abbreviation dA_2f848 := (rl_delta 5031%positive).
(* [comment removed for export] *)
Abbreviation B_A_2fc88 := 5032%positive (only parsing).
Abbreviation dA_2fc88 := (rl_delta 5032%positive).
(* [comment removed for export] *)
Abbreviation B_A_2fcb0 := 5033%positive (only parsing).
Abbreviation dA_2fcb0 := (rl_delta 5033%positive).

(* [comment removed for export] *)
Abbreviation B_ABS := 8%positive (only parsing).
Abbreviation dABS := (rl_delta 8%positive) (only parsing).
Abbreviation B_EHFRAME := 5011%positive (only parsing).
Abbreviation dEHFRAME := (rl_delta 5011%positive) (only parsing).
Abbreviation B_T_14d1c := 1015%positive (only parsing).
Abbreviation dT_14d1c := (rl_delta 1015%positive) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation B_A_1e3a0s := 5034%positive (only parsing).
Abbreviation dA_1e3a0s := (rl_delta 5034%positive).
(* [comment removed for export] *)
Abbreviation B_F_foeR23 := 1900%positive (only parsing).
Abbreviation dF_foeR23 := (rl_delta 1900%positive).
