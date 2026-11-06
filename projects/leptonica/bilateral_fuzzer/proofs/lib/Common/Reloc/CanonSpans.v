(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocImg RelocSpan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_CanonSpans () := "I69OSSVerify5KrLib6Common5Reloc8RelocImg9RelocData00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib6Common5Reloc:CanonSpans:RelocSpans00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib6Common5Reloc9RelocSpan;xblk_apartbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00c69OSSVerify5KrLib6Common5Reloc:CanonSpans;rl_spans_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonSpans<rl_orders_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonSpans:rl_hull_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan:xblk_apartC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith6Zorder9Zle_0_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C69OSSVerify5KrLib6Common5Reloc5Reloc4rl_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib6Common5Reloc5Reloc5Reloc00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00c69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_spansC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5Reloc:CanonSpans;canon_orderC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib6Common5Reloc9RelocSpan9hull_factC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg:rl_data_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc9rl_img_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common5Reloc9RelocSpan9span_findC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common5Reloc9RelocSpan9span_factC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc9RelocSpan5cspan00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9RelocSpan:order_factC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.

Definition canon_spans : list cspan := [
  mkSpan 1000%positive SK_RO 0x13084 0x130a0 4; mkSpan 1001%positive SK_RO 0x130a0 0x130cc 4; mkSpan 1002%positive SK_RO 0x130cc 0x13140 4;
  mkSpan 1003%positive SK_RO 0x13140 0x131d0 4; mkSpan 1004%positive SK_RO 0x131d0 0x13494 4; mkSpan 1005%positive SK_RO 0x13494 0x13498 4;
  mkSpan 1006%positive SK_RO 0x13498 0x134a0 4; mkSpan 1008%positive SK_RO 0x135ac 0x135f4 4; mkSpan 1009%positive SK_RO 0x1365c 0x13660 4;
  mkSpan 1010%positive SK_RO 0x13660 0x13694 4; mkSpan 1011%positive SK_RO 0x13694 0x13730 4; mkSpan 1012%positive SK_RO 0x13730 0x13764 4;
  mkSpan 1013%positive SK_RO 0x13764 0x1377c 4; mkSpan 1014%positive SK_RO 0x1377c 0x13794 4; mkSpan 1015%positive SK_RO 0x14d1c 0x14d20 4;
  mkSpan 1016%positive SK_RO 0x1516c 0x15170 4; mkSpan 1017%positive SK_RO 0x15170 0x1539c 4; mkSpan 1018%positive SK_RO 0x1539c 0x153e8 4;
  mkSpan 1019%positive SK_RO 0x153e8 0x15448 4; mkSpan 1020%positive SK_RO 0x15448 0x15490 4; mkSpan 1021%positive SK_RO 0x15490 0x15740 4;
  mkSpan 1022%positive SK_RO 0x1574c 0x15758 4; mkSpan 1023%positive SK_RO 0x15758 0x15794 4; mkSpan 1024%positive SK_RO 0x15794 0x157b0 4;
  mkSpan 1025%positive SK_RO 0x157b0 0x157b4 4; mkSpan 1026%positive SK_RO 0x157b4 0x15800 4; mkSpan 1027%positive SK_RO 0x15800 0x15874 4;
  mkSpan 1028%positive SK_RO 0x15874 0x15958 4; mkSpan 1029%positive SK_RO 0x15958 0x159b8 4; mkSpan 1030%positive SK_RO 0x159b8 0x159c0 4;
  mkSpan 1031%positive SK_RO 0x159c0 0x159f8 4; mkSpan 1032%positive SK_RO 0x159f8 0x159fc 4; mkSpan 1033%positive SK_RO 0x159fc 0x15a00 4;
  mkSpan 1034%positive SK_RO 0x15a00 0x15b38 4; mkSpan 1035%positive SK_RO 0x15b38 0x15b3c 4; mkSpan 1036%positive SK_RO 0x15b3c 0x15b40 4;
  mkSpan 1037%positive SK_RO 0x15b40 0x15d0c 4; mkSpan 1038%positive SK_RO 0x15d0c 0x15e1c 4; mkSpan 1039%positive SK_RO 0x15e1c 0x161f4 4;
  mkSpan 1040%positive SK_RO 0x161f4 0x164cc 4; mkSpan 1041%positive SK_RO 0x164cc 0x1683c 4; mkSpan 1042%positive SK_RO 0x1683c 0x170e0 4;
  mkSpan 1043%positive SK_RO 0x170e0 0x17230 4; mkSpan 1044%positive SK_RO 0x17230 0x173a8 4; mkSpan 1045%positive SK_RO 0x173a8 0x17440 4;
  mkSpan 1046%positive SK_RO 0x17440 0x17444 4; mkSpan 1047%positive SK_RO 0x17444 0x17530 4; mkSpan 1048%positive SK_RO 0x17530 0x17578 4;
  mkSpan 1049%positive SK_RO 0x17578 0x175c0 4; mkSpan 1050%positive SK_RO 0x175c0 0x176bc 4; mkSpan 1051%positive SK_RO 0x176bc 0x1771c 4;
  mkSpan 1052%positive SK_RO 0x1771c 0x178c0 4; mkSpan 1053%positive SK_RO 0x178c0 0x17a50 4; mkSpan 1054%positive SK_RO 0x17a50 0x17a58 4;
  mkSpan 1055%positive SK_RO 0x17a58 0x17a5c 4; mkSpan 1056%positive SK_RO 0x17a5c 0x17a88 4; mkSpan 1057%positive SK_RO 0x17a88 0x17aec 4;
  mkSpan 1058%positive SK_RO 0x17aec 0x17b40 4; mkSpan 1059%positive SK_RO 0x17b40 0x17b9c 4; mkSpan 1060%positive SK_RO 0x17b9c 0x17cd4 4;
  mkSpan 1061%positive SK_RO 0x17cd4 0x17d8c 4; mkSpan 1062%positive SK_RO 0x17d8c 0x17dbc 4; mkSpan 1063%positive SK_RO 0x17dbc 0x17f6c 4;
  mkSpan 1064%positive SK_RO 0x17f6c 0x18d9c 4; mkSpan 1065%positive SK_RO 0x18d9c 0x18ed0 4; mkSpan 1066%positive SK_RO 0x18ed0 0x18fa4 4;
  mkSpan 1067%positive SK_RO 0x18fa4 0x1a66c 4; mkSpan 1068%positive SK_RO 0x1a66c 0x1a690 4; mkSpan 1069%positive SK_RO 0x1a690 0x1a7bc 4;
  mkSpan 1070%positive SK_RO 0x1a7bc 0x1a94c 4; mkSpan 1071%positive SK_RO 0x1a94c 0x1a954 4; mkSpan 1072%positive SK_RO 0x1a954 0x1a998 4;
  mkSpan 1073%positive SK_RO 0x1a998 0x1aa70 4; mkSpan 1074%positive SK_RO 0x1aa70 0x1ab38 4; mkSpan 1075%positive SK_RO 0x1ab38 0x1b238 4;
  mkSpan 1076%positive SK_RO 0x1b238 0x1b340 4; mkSpan 1077%positive SK_RO 0x1b340 0x1b350 4; mkSpan 1078%positive SK_RO 0x1b350 0x1bb1c 4;
  mkSpan 1079%positive SK_RO 0x1bb1c 0x1bb4c 4; mkSpan 1080%positive SK_RO 0x1bb4c 0x1bb58 4; mkSpan 1081%positive SK_RO 0x1bb58 0x1bbec 4;
  mkSpan 1082%positive SK_RO 0x1bbec 0x1bcd8 4; mkSpan 1083%positive SK_RO 0x1bcd8 0x1bd80 4; mkSpan 1084%positive SK_RO 0x1bd80 0x1c684 4;
  mkSpan 1085%positive SK_RO 0x1c684 0x1c6a0 4; mkSpan 1086%positive SK_RO 0x1c6a0 0x1c740 4; mkSpan 1087%positive SK_RO 0x1c740 0x1c80c 4;
  mkSpan 1088%positive SK_RO 0x1c80c 0x1c8e8 4; mkSpan 1089%positive SK_RO 0x1c8e8 0x1c9b4 4; mkSpan 1090%positive SK_RO 0x1c9b4 0x1cdb8 4;
  mkSpan 1091%positive SK_RO 0x1cdb8 0x1ceb0 4; mkSpan 1092%positive SK_RO 0x1ceb0 0x1cf40 4; mkSpan 1093%positive SK_RO 0x1cf40 0x1cf84 4;
  mkSpan 1094%positive SK_RO 0x1cf84 0x1d20c 4; mkSpan 1095%positive SK_RO 0x1d20c 0x1d280 4; mkSpan 1096%positive SK_RO 0x1d280 0x1d2a4 4;
  mkSpan 1097%positive SK_RO 0x1d2a4 0x1d2a8 4; mkSpan 1098%positive SK_RO 0x1d2a8 0x1d2b4 4; mkSpan 1099%positive SK_RO 0x1d2b4 0x1d308 4;
  mkSpan 1100%positive SK_RO 0x1d308 0x1d314 4; mkSpan 1101%positive SK_RO 0x1d314 0x1d348 4; mkSpan 4000%positive SK_RO 0x102e7 0x102f1 1;
  mkSpan 4001%positive SK_RO 0x103fc 0x1040f 1; mkSpan 4002%positive SK_RO 0x10445 0x10459 1; mkSpan 4003%positive SK_RO 0x10459 0x1045d 1;
  mkSpan 4004%positive SK_RO 0x1045d 0x1045e 1; mkSpan 4005%positive SK_RO 0x1045e 0x10460 1; mkSpan 4006%positive SK_RO 0x10492 0x104a3 1;
  mkSpan 4007%positive SK_RO 0x104a3 0x104c3 1; mkSpan 4008%positive SK_RO 0x10563 0x10567 1; mkSpan 4009%positive SK_RO 0x106e4 0x106e8 1;
  mkSpan 4010%positive SK_RO 0x106e8 0x10709 1; mkSpan 4011%positive SK_RO 0x108b7 0x108cc 1; mkSpan 4012%positive SK_RO 0x108cc 0x108e3 1;
  mkSpan 4013%positive SK_RO 0x1097c 0x10980 1; mkSpan 4014%positive SK_RO 0x109b4 0x109b8 1; mkSpan 4015%positive SK_RO 0x109eb 0x10a0b 1;
  mkSpan 4016%positive SK_RO 0x10a13 0x10a24 1; mkSpan 4017%positive SK_RO 0x10a6d 0x10a77 1; mkSpan 4018%positive SK_RO 0x10a77 0x10a7e 1;
  mkSpan 5000%positive SK_RO 0x10b04 0x113b4 2; mkSpan 5001%positive SK_RO 0x113b4 0x113d4 4; mkSpan 5002%positive SK_RO 0x1144f 0x11454 1;
  mkSpan 5003%positive SK_RO 0x11458 0x11460 4; mkSpan 5004%positive SK_RO 0x11460 0x11468 4; mkSpan 5005%positive SK_RO 0x11468 0x11470 4;
  mkSpan 5006%positive SK_RO 0x11480 0x11488 4; mkSpan 5007%positive SK_RO 0x114a0 0x114a8 4; mkSpan 5008%positive SK_RO 0x114a8 0x117c0 4;
  mkSpan 5009%positive SK_RO 0x117c0 0x117d0 4; mkSpan 5010%positive SK_RO 0x117d0 0x117dc 4; mkSpan 5011%positive SK_RO 0x11968 0x12084 4;
  mkSpan 5012%positive SK_RELRO 0x1e368 0x1e3a0 8; mkSpan 5013%positive SK_DATA 0x1f3f8 0x1f430 8; mkSpan 5015%positive SK_DATA 0x1f630 0x2f6b0 8;
  mkSpan 5016%positive SK_RELRO 0x1e348 0x1e360 8; mkSpan 5018%positive SK_RO 0x10a80 0x10b04 4; mkSpan 5019%positive SK_DATA 0x1f440 0x1f624 8;
  mkSpan 5020%positive SK_RO 0x113d4 0x1144f 2; mkSpan 5021%positive SK_RO 0x11470 0x11478 4; mkSpan 5022%positive SK_RO 0x11478 0x11480 4;
  mkSpan 5023%positive SK_RO 0x11488 0x11490 4; mkSpan 5024%positive SK_RO 0x11490 0x11498 4; mkSpan 5025%positive SK_RO 0x11498 0x114a0 4;
  mkSpan 5026%positive SK_RELRO 0x1e3a0 0x1e3b0 8; mkSpan 5027%positive SK_RELRO 0x1e3b8 0x1e3f8 8; mkSpan 5028%positive SK_DATA 0x1f430 0x1f440 8;
  mkSpan 5029%positive SK_DATA 0x2f6f0 0x2f840 8; mkSpan 5036%positive SK_DATA 0x2f6b0 0x2f6b8 8; mkSpan 5037%positive SK_DATA 0x2f6b8 0x2f6f0 8; mkSpan 5030%positive SK_DATA 0x2f840 0x2f844 8; mkSpan 5031%positive SK_DATA 0x2f848 0x2fc88 8;
  mkSpan 5032%positive SK_DATA 0x2fc88 0x2fcb0 8; mkSpan 5033%positive SK_DATA 0x2fcb0 0x300b0 8; mkSpan 5034%positive SK_RELRO 0x1e360 0x1e368 8;
  mkSpan 5035%positive SK_RELRO 0x1e3b0 0x1e3b8 8].

(* [comment removed for export] *)
Definition canon_order : list (positive * positive) := [(5013%positive, 5028%positive); (5013%positive, 5019%positive); (5013%positive, 5015%positive); (5013%positive, 5036%positive); (5013%positive, 5029%positive); (5013%positive, 5037%positive); (5013%positive, 5030%positive); (5013%positive, 5031%positive); (5013%positive, 5032%positive); (5013%positive, 5033%positive); (5028%positive, 5019%positive); (5028%positive, 5015%positive); (5028%positive, 5036%positive); (5028%positive, 5029%positive); (5028%positive, 5037%positive); (5028%positive, 5030%positive); (5028%positive, 5031%positive); (5028%positive, 5032%positive); (5028%positive, 5033%positive); (5019%positive, 5015%positive); (5019%positive, 5036%positive); (5019%positive, 5029%positive); (5019%positive, 5037%positive); (5019%positive, 5030%positive); (5019%positive, 5031%positive); (5019%positive, 5032%positive); (5019%positive, 5033%positive); (5015%positive, 5036%positive); (5015%positive, 5029%positive); (5015%positive, 5037%positive); (5015%positive, 5030%positive); (5015%positive, 5031%positive); (5015%positive, 5032%positive); (5015%positive, 5033%positive); (5036%positive, 5029%positive); (5036%positive, 5037%positive); (5036%positive, 5030%positive); (5036%positive, 5031%positive); (5036%positive, 5032%positive); (5036%positive, 5033%positive); (5029%positive, 5037%positive); (5029%positive, 5030%positive); (5029%positive, 5031%positive); (5029%positive, 5032%positive); (5029%positive, 5033%positive); (5037%positive, 5030%positive); (5037%positive, 5031%positive); (5037%positive, 5032%positive); (5037%positive, 5033%positive); (5030%positive, 5031%positive); (5030%positive, 5032%positive); (5030%positive, 5033%positive); (5031%positive, 5032%positive); (5031%positive, 5033%positive); (5032%positive, 5033%positive); (5016%positive, 5034%positive); (5016%positive, 5012%positive); (5016%positive, 5026%positive); (5016%positive, 5035%positive); (5016%positive, 5027%positive); (5034%positive, 5012%positive); (5034%positive, 5026%positive); (5034%positive, 5035%positive); (5034%positive, 5027%positive); (5012%positive, 5026%positive); (5012%positive, 5035%positive); (5012%positive, 5027%positive); (5026%positive, 5035%positive); (5026%positive, 5027%positive); (5035%positive, 5027%positive)].

Class RelocSpans (RL : Reloc) (RD : RelocData RL) := {
  rl_hull_ok : hull_okb = true;
  rl_spans_ok : spans_check canon_spans = true;
  rl_orders_ok : orders_check canon_spans canon_order = true }.

(* [comment removed for export] *)
Lemma rdn_wbytes_out_xblk : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} segs bs m b1 b2 ca cb (n : nat),
  xblk_apartb canon_spans canon_order b1 b2 ca n cb (length bs) = true ->
  rdn segs (wbytes m (rl (rl_delta b2) cb) bs) (rl (rl_delta b1) ca) n = rdn segs m (rl (rl_delta b1) ca) n.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonSpans ()) [] "h04__x1h14__x2h24__x3h32H0h47__arithh56__sat6h66__sat7h74cstrh82Hah94__ffh:6__sat8h;6__sat9h<8__varmaph=5__with>1zh?5cstr0h@4__x4hA4__x5hB4__x6hC2A1hD2A2hE2A3hF2A4hG2A5hH2E1hI2E2hJ1HhK2RDhL2RLhM3RSPhN1ahO2b1hP2b2hQ2bshR2cahS2cbhT1mhU1nhV4segsp;1p;2p;8p;3p;>p;4p;7p;6p;9g0000j1zTg0016j2yTg002?j1STg002_j1=Tg003Dj1TTg003bj1^Tg004Ej1[Tg004gj25Tg005Gj8eTg006Nj3<Tg006hj3dTg0080j3cTg0099j3bTg00:@l>xTg00;Fj1RTg00;dj1FTg00<Ij2\Tg00<fj22Tg00=Bj3LTg00><j4:Tg00?4j17Tg00?Tj26Tg00@Tj1YTg00A5j1JTg00AZj2XTg00BBj2ITg00B^j3VTg00CBj1QTg00Caj2PTg00DJj3UTg00E3j2wTg00E_j1vTg00F?j3uTg00F_j2HTg00G=j1sTg00G[j1rTg00HFj2_Tg00Hij2BTg00ILj1qTg00Inj3GTg00JQj3]Tg00K4j4WTg00K_j7oTg00LCj2nTg00Lej2mTg00M?j2lTg00Mkj3kTg00NJj4jTg00O<j24Tg00OYR0j2OTg00P4j3ZTg00Q0j2DTg00Qjj2ETg00RTj1iTg00S2j7hTg00SVj6MTg00T4l9gTg00U6j2`Tg00UPj4tTg00Unj7aTg00VRj8fTf2R1f1R2f0R3'6'4p=1g00W6R4/23p=0%73,42p=3f3R5/211223'`p=91O23,O1p=C1212/O3p=N1612/D3p=81412/23p=?1523#7p=@1212/`3p=Kg00WTR6P1P2P3Ctp=AP1g00X2R7g00XQR8P8g00Y1R9P6P2g00YQP3CWg00Z8R:Fap=;P2P7P8P8P9P3P:Fap=pP5P7P8P8P9P1P2P3Gfp=>g00ZX%z31y23g00[W#Sg00\VR:#=R;#=R<#=R=#T#^R>#SR?%==#=#=R=#TR@#^%[>[g00];RAg00]`g00^?RBg00^_RCg00_gRDf4REP5P1P3P2f6RF,5>Geg00`oRG3<f;RHf:RIPCPDf9RD9dHIAcHIDAbHIDf5RCPEP5P2P1f7RJ,5>RKP3M>xA15HCRL#013L2RM%R;RN%F:RO#F#F#FRP#RRQ'\RR'2A11HERS#013SKRK/2RPMPSPKPLC93C3CP0f<RL=1EFRK#013K1RSA15LCRM#0f8RT,5>,3MRU/2RPSPMPUPKC93C7NR%[?R?PIf=RK?8FE=LTDA8KJCRUP5C:PIPTPUP5C:3<P3f>RU=1FT#0f?RM=1JDRS/3CRVA1FMTRW#015>H,3WRX/2RPVPWPXPSC93C7NRP0f@RS=1TIRX/3FRW/2RA1JSDRV#015>L,3VRY/2RPWPVPYPXC93CPUfARX?8IT=LLKA8XHDRYPJC:PUPLPYPJC:5<?P3fBRY=1IL%7T;?RfCRT=1ILRV#015>M,3VRW/2RA1HTKRZ/3DPVPWPZC93CP0fDRZ=1HKRW#015>S,3WRVA1LZUR[/3IPWPVP[C97NRPYfER[?8UL=LSXA8[MKRLPHC:PYPSPLPHC:5<?P3fFRH=1KM#0fGRL=1USRV15>T'3RWA1MLXR\/3KPVPWP\C97NRP0fHR0=1MXR\15>Z'3RW/2RA1S0YRV/3UP\PWPVC9PHfIRV?8YS=LZ[A8VTXRWPMC:PHPZPWPMC:5<?P3fJR?=1XT1@>H;?RfKRM=1T[RT/3XA1YMZRX1@>L=?XT3KfLRX/6HRT%YY%7Y#015>VRW#J%7W#0R\%R=R=,XNRU1I4NR]%0=1\N=R^,I4[[R_%0NR`g00aORaAVN=2UW8R=%0^\a^8`Rb1XNQRc%0Q1I4R[\]R]AVNQ2VaX8`RQ%0R\a^8`R`g00akRag00bWRd#Q#QRe#Q,P61P6e1P6d5U65U6g00c6'w%vaRd3uRe%SaRa1H611H65Rf7A2Rg%s6Rh%r6Ri1_64Rj1B6ORk5;i%q8RlPi1B6:1B6;5G6R:=G6kRk1_6NRN%TP5]6RP5;iRmPlPiA;ij:RnPlPiP7P8P8P9PnP6P:g00cbA]6N@RNCW,piFoC>RnC>C>1ni9RoP3P11mBG1l31=<BGdAk642CjR4b9b<b=X06X16X26%011421RG/45RB/2R1415#0145ERp#01Ip^'O[[[^06^16^26RqP3%7VRrfSRsfMRt'6RuPMPFPSPZO6b4b5b6b:b;b7b37ZZ1DTZ,E@14ZT5<616tHRT%YWP\%JZ%7Z#0PUP_P=PbPcP]PQP`PePa%i6Re?A1f?A2ePhPi%=O,B6RO9;ijPlPiAG6:O=;iPPlPnC>C>PoP4b9b<b=X06X16X26PqP3fP,@>fT/6tPMPFPDPKO6b4b5b6b:b;b7b37ZZ1DTZ,E@14ZT5<6PMP?PVfNRT/6LRK/D[RD16T0Rq/DHRnPZP614HqRq%7[RZ,43RPfORj?80H,E@R01@>MRH=?033KX>6P614[KRKA1LjVRV/4ZP3143HRHPVC9X>615>?RV#JRL%7V#0RV%J[R[%0ZRZPcP]PQP`PdPa1H6E1H6F7A11H6C?A5e7A2PhPiPiP7P8P8P91B6<%F;,B65G6R;9;ikAG6;O=;i:FhR:PlP:C>PoP4b9b<b=X06X16X26X@6XA6XB61432R:/41R1A?pC:7Kp14ECRCA?CFG5KB[^06^16^26^@6^A6^B6P31@>j16sXP?PrPuPMPJO7b4b5b6b?b71E@DRDP3EM1E@nRnP2EMP6Pq12P^X>6PLPVP[PZPUP_P=PbPcP]PQP`PdPaPgPhPiPmPlA;ikNC>PoP4b9b<b=X06X16X26R4121R12B^[^06^16^26RBP3%7MfURM/6jPtPYO4b4b5b6b:b;b?b7PnP2EMP6PK12H^X>6PLPVP[PZPUP_P=PbPcP]PQP`P4PBP3fQ,@>16MTPXPIO4b4b5b6b:b;b?b7PDP3EMM9gbIbHWGWFP2P3O2n2001000000121000000W3WEP2P3O2n2001000000121000000W3WDP2P3O2n2001000000121000000W3WCP2P3O2n2001000000121000000bNWJWUXS6XR6XPAWOWTWQWVWMWKWLo"). Qed.

(* [comment removed for export] *)
Lemma rl_hull : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD},
  2^16 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo /\ rl_data_lo <= rl_img_hi /\ rl_img_hi <= 2^31.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonSpans ()) [] "h01Hh11Ah21Bh31Ch41Dh51Eh62RDh72RLh83RSPh92_Hh:1ap;1p;2p;3p;4g0000j1CTg0016j2BTg0099j3ATg00dIj3@Tg002_j1<Tg00;Fj1;Tg00<Ij2=Tg00eNj15Tg00fOj14Tg00gOj23Tg00hTj12Tg00;dj1:Tg00<fj20Tg00OYR0j27Tg00iUj49Tg00j0j2?Tg006Nj3>Tf3R1f2R2'0g00WTR3f1R4f0R5'?g00W6R63>'7p=8f4R7/011024/75'7p=11?45=>36p=6g00ZX%C51B45AA2459@24g00\VR6#<R3#;R8%<3#<R3#<#;'=R9%52R:P:%42R:P:1324R:P:%22R:P:%:6#:#:#:#;,=8R8P:%;3R3C8D1D1P0%51R:,09P:%41R:P:1312R2P2%21R2P2P81623D1D1P9%57R2P2%47R2P21371R1P1%27R71078D1D1P5f5R7#5,09f6R1#5%41R2P21317R2P2%21R2P2P81623D1D1P0f7R2#5%42R:'0P:1321R1P1%22R1P1P8P1P3C8D1P9f8R1#5R:P:%41R:P:1312R2P2%21R11018D1D1P5f9R1#5%41'0f:R2#41321R:P:%22R:P:P8P:P3C8D1P0f;R:#413:2R2'0P2%2:R2P2P81623D1P9f<R2#5R6P6%42R6P6132:R:P:%22R:10:8D1D1P5f=R:#413:2'0f>R2/3:%22R6P6P81663D1P0f?R6/32%26R2'0P2P8P2P3C8P9f@R2#5R;P;%42R;P;1326R6P6%22R61068D1D1P5fAR6/32%26'0fB#2R2P8P2P3C8P0fCR0#2R2/081623P9fDR2#5R;P;%42R;P;1320R0P0%22R21028D1D1P5fE#2/08fFR2#2/63fGR3#5R0,09%43R9,00R01332R2,09R9%23R3,02R21038R3'7R8'7R;'7P6P0P;P:P9P8P1P2P3P7P4C9C9C9C9W9W5P4P5O2n2001000000120000000W0W4P4P5O2n2001000000121000000W0W3P4P5O2n2001000000121000000W0W2P4P5O2n2001000000121000000W0W1P4P5O2n2001000000121000000b:W8W6W7o"). Qed.
Lemma rl_hull_al : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD}, rl_img_hi mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonSpans ()) [] "h01Hh11Fh22RDh32RLh43RSPh52_Hh63_H0h73_H1h83_H2h93_H3h:1ap;1p;2p;3g0000j1BTg0016j2ATg0099j3@Tg00dIj3?Tg002_j1:Tg00;Fj19Tg00<Ij2<Tg00eNj16Tg00fOj15Tg00gOj23Tg00hTj10Tg00;dj18Tg00<fj21Tg00j0j2>Tg006Nj3=Tg00OYR0j2;Tf3R1f2R2'1g00WTR3f1R4f0R5'>g00W6R63=';p=7f4R7/111124/;5';p=41>45==36p=2g00ZX%B51A45A@2459?24g00\VR6#:R3#9R8%:3#:R3#:#9'<R9%62R:P:%52R:P:1324R:P:%02R:P:%86#8#8#8#9,<8R8P:%93R3C7D4D4P0%61R:,19P:%51R:P:1312R2P2%01R1P1P81213D4D4%07/23P5f5R7#6,19f6R9#6%59R1P11397R7P7%09R7P7P81273D4D4P0f7R7#6%57R1'1P11379R9P9%07R7P7P8P7P3C7D4f8#0/23P5f9R7#6%57'1f:R9#51397R7P7%09R7P7P8P7P3C7D4P0f;R7#51379R9'1P9%07R7P7P81273D4f<R7#0/23P5f=R9#51397'1f>R7/39%07R9P9P81293D4P0f?R9/37%09R9'1P9P8P9P3C7f@R9#0/23P5fAR7/39%07'1fB#0R7P8P7P3C7P0fC#0R0/181203fD#0/23P5fE#0/18fF#0/23P5W1W9P4P5O2n2001000000120000000W0W8P4P5O2n2001000000120000000W0W7P4P5O2n2001000000121000000W0W6P4P5O2n2001000000121000000W0W5P4P5O2n2001000000121000000b:W4W2W3o"). Qed.

Lemma rl_span : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} b s, span_find canon_spans b = Some s -> span_P s.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonSpans ()) [] "h01Hh12RDh22RLh33RSPh41bh51sp;1p;2p;3p;7g0000j17Tg0016j26Tg004Ej10Tg00jPj21Tg00kUj25Tg006Nj32Tg006hj33Tg00l7j74Tg00ZXf0R0#7f1R1/60g00];g00m<R2%02g00^_R3/11152032f5R2f4R4P3f39324f2P1P0F4W0W5W4W3W1W2o"). Qed.

(* [comment removed for export] *)
Definition span_mark (b : positive) : Prop := True.
Ltac rl_span_of b :=
  lazymatch goal with
  | _ : span_mark b |- _ => fail
  | _ =>
      let r := eval vm_compute in (span_find canon_spans b) in
      lazymatch r with
      | Some ?s =>
          let P := eval cbv [span_P sp_blk sp_kind sp_lo sp_hi sp_al] in (span_P s) in
          lazymatch P with
          | ?R /\ _ =>
              let h := fresh "Hspan" in let m := fresh "Hspanm" in
              pose proof (proj1 (rl_span b s (@eq_refl _ (Some s)) : P) : R) as h; pose proof (I : span_mark b) as m
          end
      | None => fail
      end
  end.
(* [comment removed for export] *)
Ltac rl_span_al b :=
  let r := eval vm_compute in (span_find canon_spans b) in
  lazymatch r with
  | Some ?s =>
      let P := eval cbv [span_P sp_blk sp_kind sp_lo sp_hi sp_al] in (span_P s) in
      lazymatch P with
      | _ /\ ?A =>
          let h := fresh "Hspanal" in pose proof (proj2 (rl_span b s (@eq_refl _ (Some s)) : P) : A) as h
      end
  end.

(* [comment removed for export] *)
Ltac rl_hull_ctx :=
  lazymatch goal with
  | _ : 2^16 <= rl_img_lo /\ _ |- _ => idtac
  | _ => let h := fresh "Hhull" in pose proof rl_hull as h
  end.
Ltac rl_spans_ctx :=
  rl_hull_ctx;
  repeat match goal with
         | |- context [@rl_delta _ ?b] => rl_span_of b
         | H : context [@rl_delta _ ?b] |- _ => rl_span_of b
         end.

(* [comment removed for export] *)
Lemma rl_order : forall {RL : Reloc} {RD : RelocData RL} {RSP : RelocSpans RL RD} b1 b2 s1 s2,
  pair_inb canon_order b1 b2 = true -> span_find canon_spans b1 = Some s1 -> span_find canon_spans b2 = Some s2 ->
  sp_hi s1 + rl_delta b1 <= sp_lo s2 + rl_delta b2.
Proof.
ltac2:(KReplay.run1 (kr_t_CanonSpans ()) [] "h02RDh12RLh23RSPh32b1h42b2h52s1h62s2p;1p;2p;3p;8g0000j13Tg0016j22Tg0080j30Tg00n?j81Tg00ZXf0R0#3f1R1/20g00];R2g00m<R3f6R4g00^_g00_gf5f4504f3f2P1P0G1X63W5X42W3W2W0W1o"). Qed.
Ltac rl_order_of b1 b2 :=
  let r1 := eval vm_compute in (span_find canon_spans b1) in
  let r2 := eval vm_compute in (span_find canon_spans b2) in
  lazymatch r1 with
  | Some ?s1 =>
      lazymatch r2 with
      | Some ?s2 =>
          let P := eval cbv [sp_blk sp_kind sp_lo sp_hi sp_al] in (sp_hi s1 + rl_delta b1 <= sp_lo s2 + rl_delta b2) in
          let h := fresh "Hord" in
          pose proof (rl_order b1 b2 s1 s2 (@eq_refl bool true) (@eq_refl _ (Some s1)) (@eq_refl _ (Some s2)) : P) as h
      end
  end.
Ltac rl_data_chain :=
  rl_order_of 5013%positive 5028%positive;
  rl_order_of 5028%positive 5019%positive;
  rl_order_of 5019%positive 5015%positive;
  rl_order_of 5015%positive 5036%positive;
  rl_order_of 5036%positive 5029%positive;
  rl_order_of 5029%positive 5037%positive;
  rl_order_of 5037%positive 5030%positive;
  rl_order_of 5030%positive 5031%positive;
  rl_order_of 5031%positive 5032%positive;
  rl_order_of 5032%positive 5033%positive.
Ltac rl_relro_chain :=
  rl_order_of 5016%positive 5034%positive;
  rl_order_of 5034%positive 5012%positive;
  rl_order_of 5012%positive 5026%positive;
  rl_order_of 5026%positive 5035%positive;
  rl_order_of 5035%positive 5027%positive.
(* [comment removed for export] *)
Ltac rl_ndata l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | cons (@rl_delta _ ?b) ?t =>
      let n := rl_ndata t in
      lazymatch b with
      | 5013%positive => constr:(S n)
      | 5028%positive => constr:(S n)
      | 5019%positive => constr:(S n)
      | 5015%positive => constr:(S n)
      | 5029%positive => constr:(S n)
      | 5036%positive => constr:(S n)
      | 5037%positive => constr:(S n)
      | 5030%positive => constr:(S n)
      | 5031%positive => constr:(S n)
      | 5032%positive => constr:(S n)
      | 5033%positive => constr:(S n)
      | _ => n
      end
  | cons _ ?t => rl_ndata t
  end.
Ltac rl_nrelro l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | cons (@rl_delta _ ?b) ?t =>
      let n := rl_nrelro t in
      lazymatch b with
      | 5016%positive => constr:(S n)
      | 5034%positive => constr:(S n)
      | 5012%positive => constr:(S n)
      | 5026%positive => constr:(S n)
      | 5035%positive => constr:(S n)
      | 5027%positive => constr:(S n)
      | _ => n
      end
  | cons _ ?t => rl_nrelro t
  end.
Ltac rl_chains l :=
  (let n := rl_ndata l in lazymatch n with S (S _) => try rl_data_chain | _ => idtac end);
  (let n := rl_nrelro l in lazymatch n with S (S _) => try rl_relro_chain | _ => idtac end).

(* [comment removed for export] *)
Ltac rl_spans_data :=
  rl_hull_ctx;
  try rl_span_of 5000%positive;
  try rl_span_of 5001%positive;
  try rl_span_of 5002%positive;
  try rl_span_of 5003%positive;
  try rl_span_of 5004%positive;
  try rl_span_of 5005%positive;
  try rl_span_of 5006%positive;
  try rl_span_of 5007%positive;
  try rl_span_of 5008%positive;
  try rl_span_of 5009%positive;
  try rl_span_of 5010%positive;
  try rl_span_of 5011%positive;
  try rl_span_of 5012%positive;
  try rl_span_of 5013%positive;
  try rl_span_of 5015%positive;
  try rl_span_of 5016%positive;
  try rl_span_of 5018%positive;
  try rl_span_of 5019%positive;
  try rl_span_of 5020%positive;
  try rl_span_of 5021%positive;
  try rl_span_of 5022%positive;
  try rl_span_of 5023%positive;
  try rl_span_of 5024%positive;
  try rl_span_of 5025%positive;
  try rl_span_of 5026%positive;
  try rl_span_of 5027%positive;
  try rl_span_of 5028%positive;
  try rl_span_of 5029%positive;
  try rl_span_of 5036%positive;
  try rl_span_of 5037%positive;
  try rl_span_of 5030%positive;
  try rl_span_of 5031%positive;
  try rl_span_of 5032%positive;
  try rl_span_of 5033%positive;
  try rl_span_of 5034%positive;
  try rl_span_of 5035%positive.
