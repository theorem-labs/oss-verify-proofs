(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx QhAd QVbl QQLG QQRC Q91D QCa8 QkTt Qy8Z Q8l1 QROt QZxv Q5m9 QXfH.
From Ltac2 Require Ltac2 Constr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QhAd.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import QQRC.Mq0.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQRC.
Import QkTt.Mq0.
Import QkTt.Mq1.
Import QVbl.Mq2.
Import QVbl.Mq1.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import Q91D.Mq4.
Import Qy8Z.Mq0.
Import QQRC.Mq3.
Import Q8l1.Mq3.
Import QROt.Mq2.
Import QQRC.Mq1.
Import QZxv.Mql.
Import QQRC.Mq2.
Import Q8l1.Mq0.
Import Q5m9.Mq1.
Import QXfH.

Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Import Ltac2.Ltac2 Ltac2.Constr.
Set Default Proof Mode "Classic".
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition floatscan_code (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z) : list Z :=
[0x81010113; 0x7e113423; 0x7e813023; 0x7c913c23; 0x7d213823; 0x7d313423; 0x7d413023; 0x7b513c23; 0x7b613823; 0x7b713423; 0x7b813023; 0x79913c23; 0x79a13823; 0x79b13423; 0x78813027; 0x000016b7; 0x40d10133; 0x00013023; 0x80010113; 0xf1010113; 0x00060b93; 0x00050a93; w_22; w_23; 0x000a3503; 0x00002637; 0x00c10633; 0x06a63423; 0x02058a63; 0x00200513; 0x00a58c63; 0x00100c13; 0x258592e3; 0xbce00b13; 0x03500913; 0x0240006f; 0x07100913; 0x00100c13; 0xffffc537; 0xf9250b1b; 0x0100006f; 0x00000c13; 0xf6b00b13; 0x01800913; 0x00500413; 0x02000493; 0x0140006f; 0x000a8513; 0xd59ff0ef; 0xff750593; 0x0285f263; 0x008ab503; 0x0b8ab583; 0xfeb504e3; 0x00150593; 0x00bab423; 0x00054503; 0xff750593; 0xfe85e2e3; 0xfe9500e3; 0x02d00593; 0x00b50663; 0x02b00593; 0x06b51063; 0x008ab583; 0x0b8ab603; 0xfd350513; 0x00a03533; 0xfff50513; 0x00156493; 0x08c58263; 0x00158513; 0x00aab423; 0x0005c503; 0xfdf57593; 0x04900613; 0x02c59e63; 0x008ab503; 0x0b8ab583; 0x10b50e63; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x04e00593; 0x10b50c63; 0x1410006f; 0x00100493; 0xfdf57593; 0x04900613; 0xfcc586e3; 0x04e00613; 0x04c59263; 0x008ab503; 0x0b8ab583; 0x16b50063; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x04100593; 0x10b512e3; 0x1580006f; 0x000a8513; 0xc79ff0ef; 0xfdf57593; 0x04900613; 0xf8c584e3; 0xfbdff06f; 0x03000593; 0x0cb51e63; 0x008ab503; 0x0b8ab583; 0x20b50663; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x05800593; 0x20b51463; 0x000a3503; 0x000025b7; 0x00b105b3; 0x0685b583; 0x00b50463; 0x4900106f; 0x000a8513; 0x00090593; 0x000b0613; 0x00048693; 0x000b8713; 0x000027b7; 0x8f07879b; 0x00f10133; 0x7e813083; 0x7e013403; 0x7d813483; 0x7d013903; 0x7c813983; 0x7c013a03; 0x7b813a83; 0x7b013b03; 0x7a813b83; 0x7a013c03; 0x79813c83; 0x79013d03; 0x78813d83; 0x78013407; 0x7f010113; 0x4340106f; 0x000a8513; 0xbbdff0ef; 0xfdf57513; 0x04e00593; 0x02b518e3; 0x008ab503; 0x0b8ab583; 0x0ab50263; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x04600593; 0x00b516e3; 0x09c0006f; 0x41600d33; 0x412d05b3; 0x00b13423; 0x00050413; 0x00000513; w_170; 0x00a13823; 0x02e00613; 0x00b13c23; 0x0cc41c63; 0x00000993; 0x008ab503; 0x0b8ab583; 0x2ab50c63; 0x00150593; 0x00bab423; 0x00054503; 0x2b00006f; 0x000a8513; 0xb39ff0ef; 0xfdf57513; 0x04100593; 0x7ab51663; 0x008ab503; 0x0b8ab583; 0x12b50663; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x04e00593; 0x78b51463; 0x1240006f; 0x000a8513; 0xafdff0ef; 0xfdf57513; 0x04600593; 0x76b51863; 0x008ab503; 0x0b8ab583; 0x1ab50c63; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57413; 0x04900513; 0x1aa41a63; 0x008ab503; 0x0b8ab583; 0x1ab50863; 0x00150593; 0x00bab423; 0x00054503; 0xfdf57513; 0x04e00593; 0x1ab51663; 0x008ab503; 0x0b8ab583; 0x4cb50263; 0x00150593; 0x00bab423; 0x00054503; 0x4bc0006f; 0x00040513; 0x05713023; 0x03613423; 0x04913423; 0x03213c23; 0x05413c23; 0x00000c93; 0x00000993; 0x00000a13; 0x03a13823; 0x03813023; 0x06012423; 0x02e00b93; 0xfd04059b; 0x27741863; 0x2dc0006f; 0x000a8513; 0xa45ff0ef; 0xfdf57513; 0x05800593; 0xe0b500e3; 0x0c0ab503; 0x008ab403; 0x00054663; 0xfff40413; 0x008ab423; 0x41600d33; 0x00000513; w_256; 0x00a13823; 0x0b8ab503; 0x00b13c23; 0x10a40a63; 0x00140513; 0x00aab423; 0x00044503; 0x10c0006f; 0x000a8513; 0x9f1ff0ef; 0xfdf57513; 0x04e00593; 0x66b51263; 0x008ab503; 0x0b8ab583; 0x3cb50863; 0x00150593; 0x00bab423; 0x00054503; 0x02800593; 0x3cb51663; 0x00100413; 0x00a00493; 0x01a00913; 0x05f00993; 0x0080006f; 0x00140413; 0x008ab503; 0x0b8ab583; 0x00b50e63; 0x00150593; 0x00bab423; 0x00054503; 0xfd05059b; 0x0095fc63; 0xfddff06f; 0x000a8513; 0x981ff0ef; 0xfd05059b; 0xfc95e6e3; 0xfbf5059b; 0xfd25e2e3; 0xfd3500e3; 0xf9f5059b; 0xfb25ece3; 0x02900593; 0x36b50c63; 0x0c0ab503; 0x00054863; 0x008ab583; 0xfff58593; 0x00bab423; 0x5c0b8c63; 0x34040e63; 0x34054c63; 0x008ab503; 0x40850533; 0x3480006f; 0x000a8513; 0x929ff0ef; 0xfdf57413; 0x04900513; 0xe4a40ae3; 0xffd00513; 0x54c0006f; 0x000a8513; 0x90dff0ef; 0xfdf57513; 0x04e00593; 0xe4b50ee3; 0xffc00513; 0x52c0006f; 0x000a8513; 0x8f1ff0ef; 0x412d09b3; 0x03000413; 0x00850a63; 0x02c0006f; 0x000a8513; 0x8d9ff0ef; 0x02851063; 0x008ab503; 0x0b8ab583; 0xfeb506e3; 0x00150593; 0x00bab423; 0x00054503; 0xfe8504e3; 0x01313423; 0x02e00593; 0x08b51a63; 0x00100993; 0x008ab503; 0x0b8ab583; 0xd4b518e3; 0x000a8513; 0x895ff0ef; 0x05713023; 0x03613423; 0x03213c23; 0x05413c23; 0x03000413; 0x04913423; 0x00000c93; 0x00850c63; 0x0380006f; 0x000a8513; 0x869ff0ef; 0xfffc8c93; 0x02851263; 0x008ab503; 0x0b8ab583; 0xfeb504e3; 0x00150593; 0x00bab423; 0x00054503; 0xfffc8c93; 0xfe8502e3; 0x00100993; 0x00100a13; 0x03a13823; 0x03813023; 0x06012423; 0x02e00b93; 0xfd05059b; 0x05751063; 0x0ac0006f; 0x05713023; 0x03613423; 0x04913423; 0x03213c23; 0x05413c23; 0x00000c93; 0x00000a13; 0x00100993; 0x03a13823; 0x03813023; 0x06012423; 0x02e00b93; 0xfd05059b; 0x07750a63; 0x00900613; 0x06b67663; 0x00000493; 0x06013023; 0x00000c13; 0x00000d13; 0x00048b93; 0x000a0463; 0x000c8b93; 0x14098e63; 0xfdf57593; 0x04500613; 0x14c59863; 0x000a8513; 0x04013403; 0x00040593; 0x728010ef; 0xfff00593; 0x03f59593; 0x1eb51c63; 0x14040e63; 0x0c0ab503; 0x1e054463; 0x00000513; 0x008ab583; 0xfff58593; 0x00bab423; 0x1d80006f; 0x00000d13; 0x00000c13; 0x06013023; 0x00000493; 0xfd250613; 0x000026b7; 0x06810913; 0x00a00b13; 0x7fc00d93; 0x03000413; 0x00004737; 0x00163613; 0xff06869b; 0x00d90933; 0x7dc70693; 0x04d13823; 0x0200006f; 0x000a8513; 0xf28ff0ef; 0xfd05059b; 0xfd250613; 0x00163613; 0x01750463; 0xf565f6e3; 0x00167613; 0x00060a63; 0x0e0a1663; 0x00100a13; 0x00048c93; 0x0700006f; 0x00148493; 0x058dc863; 0x00850463; 0x06913023; 0x002c1613; 0x06810693; 0x00c68633; 0x000d0a63; 0x00062583; 0x036585b3; 0x00b50533; 0xfd050593; 0x00b62023; 0x001d0d1b; 0xff7d0513; 0x00153513; 0x00ac0c3b; 0xfff5051b; 0x01a57d33; 0x00100993; 0x01c0006f; 0x00850c63; 0x00092503; 0x00156513; 0x00a92023; 0x05013503; 0x06a13023; 0x008ab503; 0x0b8ab583; 0xf4b50ce3; 0x00150593; 0x00bab423; 0x00054503; 0xfd05059b; 0xfd250613; 0x00163613; 0xf5751ae3; 0xf55ff06f; 0x0019b593; 0x00054c63; 0x0c0ab503; 0x00054863; 0x008ab503; 0xfff50513; 0x00aab423; 0x0a058663; w_502; 0x01600593; 0x00b52023; 0x000a8513; 0x00000593; 0xdf4ff0ef; 0x00000513; w_509; 0x1780006f; 0x0019b593; 0x000c8b93; 0x0c0ab503; 0xfc0550e3; 0xfc9ff06f; 0x000a8513; 0xe04ff0ef; 0x02800593; 0xc2b50ee3; 0x0c0ab503; 0x00054863; 0x008ab503; 0xfff50513; 0x00aab423; 0x7fc00537; 0xf0050553; 0x2540006f; 0x000a8513; 0xdd4ff0ef; 0xfdf57513; 0x04900593; 0x02b51063; 0x008ab503; 0x0b8ab583; 0x16b50063; 0x00150593; 0x00bab423; 0x00054503; 0x1580006f; 0xffb00513; 0x1d80006f; 0x00000513; 0x01750bb3; 0x06812a83; 0x080a8a63; 0x00900513; 0x04954663; 0x049b9463; 0x03813503; 0x00aad53b; 0x00153513; 0x02013583; 0x00a5e533; 0x02050863; 0x04813503; w_556; 0x00050413; 0x00058493; 0x000a8513; w_560; 0x00050613; 0x00058693; 0x00040513; 0x00048593; 0x0980006f; 0x03013503; 0x0015551b; 0x05755863; w_569; 0x02200593; 0x00b52023; 0x04813503; w_573; 0x07fff637; 0x02461613; 0xfff60413; 0xfff00613; 0x00040693; w_579; 0xfff00613; 0x0540006f; 0x04813503; 0xd20507d3; 0xf2000753; 0x12e7f553; w_586; 0x0440006f; 0x02813503; 0xf1e50513; 0x04abd263; w_591; 0x02200593; 0x00b52023; 0x04813503; w_595; 0x00100413; 0x03041413; 0x00000613; 0x00040693; w_600; 0x00000613; 0x00040693; w_603; 0x05813603; 0x00063603; 0x1580006f; 0x060d0c63; 0x00800513; 0x06013683; 0x03a54663; 0x002c1513; 0x06810593; 0x00a58533; 0x00052583; 0xff7d0d13; 0x00a00613; 0x001d0d1b; 0x02c585b3; 0xfe0d1ce3; 0x00b52023; 0x001c0c1b; 0x0400006f; 0x000a8513; 0xc58ff0ef; 0xfdf57513; 0x05400593; 0x02b51063; 0x008ab503; 0x0b8ab583; 0x04b50e63; 0x00150593; 0x00bab423; 0x00054503; 0x0540006f; 0xffa00513; 0x05c0006f; 0x06013683; 0x0006851b; 0x00800593; 0x1ca5c463; 0x01100593; 0x1d75c063; 0x000b859b; 0x1aa5cc63; 0x00900513; 0x10ab9a63; 0x04813503; w_648; 0x00050413; 0x06812503; 0x00058493; 0xe91ff06f; 0x000a8513; 0xbe0ff0ef; 0xfdf57513; 0x05900593; 0x02b50e63; 0xff900513; 0x040b8663; 0x0c0ab583; 0x0205c663; 0x008ab583; 0xfff58593; 0x00bab423; 0x000b8e63; 0x04900593; 0x00b41a63; 0x008ab583; 0x00a58533; 0x00350513; 0x00aab423; 0xd004f7d3; 0x7f800537; 0xf0050753; 0x10e7f553; w_676; 0x0380006f; 0x0c0ab503; 0x00054863; 0x008ab503; 0xfff50513; 0x00aab423; w_683; 0x01600593; 0x00b52023; 0x000a8513; 0x00000593; 0xb20ff0ef; 0x00000513; w_690; 0x000a3603; 0x000026b7; 0x00d106b3; 0x0686b683; 0x3ad614e3; 0x00002637; 0x8f06061b; 0x00c10133; 0x7e813083; 0x7e013403; 0x7d813483; 0x7d013903; 0x7c813983; 0x7c013a03; 0x7b813a83; 0x7b013b03; 0x7a813b83; 0x7a013c03; 0x79813c83; 0x79013d03; 0x78813d83; 0x78013407; 0x7f010113; 0x00008067; 0x00800913; 0x07794863; 0x04813503; w_718; 0x00050413; 0x06812503; 0x00058493; w_722; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_727; 0x00050413; 0x4179053b; w_730; 0x02051513; 0x01e55513; w_733; 0x00a60533; 0x00052503; 0x00058493; w_737; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_742; 0xdd5ff06f; 0x001b9513; 0x03813583; 0x417585bb; 0x06812a83; 0x40a5853b; 0x01b5051b; 0x01e00593; 0x26a5cae3; 0x00aad53b; 0x260506e3; 0x00000593; 0x020c1513; 0xfff00713; 0x002c1613; 0x06810693; 0x00d60633; 0x02075693; 0x00d56533; 0x001c0693; 0xffc60613; 0x00150513; 0x02071713; 0x00062783; 0x00158593; 0x00e50533; 0xfff68693; 0xffc60613; 0xfe0786e3; 0x40bc063b; 0x38e395b7; 0xe395859b; 0x02bb85b3; 0x03f5d713; 0x4215d593; 0x00e585b3; 0x00359713; 0x40bb85bb; 0x40e585bb; 0x0016091b; 0x0c058463; 0x43fbd713; 0x00977713; 0x00e585bb; 0x0c068063; 0x00000693; 0x00000713; 0x00000993; 0x00800793; w_792; 0x3b9ad8b7; 0x00160293; 0x40b787b3; w_796; 0x00279793; 0x00f807b3; 0x0007a783; 0xa0088893; 0x02029293; 0x0202d813; 0x02f8c8bb; 0x06810293; 0x02c0006f; 0x02f383b3; 0x00e03733; 0x00168693; 0x4073033b; 0xfff70393; 0x0313073b; 0xff73f313; 0x006b8bb3; 0x00428293; 0x02d80663; 0x0002a303; 0x02f353bb; 0x00e38e3b; 0x0136c733; 0x01c76733; 0x01c2a023; 0xfc0710e3; 0x00198993; 0x7ff9f993; 0xfb5ff06f; 0x02070663; 0x0026091b; 0x41e55513; 0x06810613; 0x00a60533; 0x00e52023; 0x0140006f; 0x00000993; 0x0140006f; 0x00000993; 0x00000913; 0x40bb8bbb; 0x009b8b93; 0x00000a93; 0x06810513; 0x02400593; 0x3b9ad737; w_843; 0xa017061b; w_845; 0xa007071b; 0x009e77b7; 0x4d07879b; 0x00299893; 0x011508b3; 0x000b829b; 0x0100006f; 0xfe3a8a9b; 0x00030913; 0x0a081663; 0x00b2c863; 0x10b29663; 0x0008a803; 0x1107e263; 0x00000813; 0x7ff90e93; 0x00c0006f; 0xfff38e93; 0xfd338ae3; 0x7ffef393; 0x00239e13; 0x01c50e33; 0x000e6303; 0x01d31313; 0x01030eb3; 0x00090313; 0x02cee463; 0x009ed813; 0x02d83833; 0x00b85813; 0x02e80f33; 0x41ee8eb3; 0x01de2023; 0x00038f13; 0x000e9c63; 0x0180006f; 0x00000813; 0x01de2023; 0x00038f13; 0x000e8463; 0x00030f13; 0xfff30e13; 0x0133ceb3; 0x7ffe7e13; 0x01c3cfb3; 0x01f03fb3; 0x001ebe93; 0x01dfeeb3; 0x00030913; 0xf80e90e3; 0x000f0913; 0xf79ff06f; 0xfff98993; 0x7ff9f993; 0x02699863; 0x002e1893; 0x7fe30293; 0x011508b3; 0x7ff2f293; 0x00229293; 0x005502b3; 0x0008a883; 0x0002a303; 0x011368b3; 0x0112a023; 0x0080006f; 0x00030e13; 0x009b8b93; 0x00299893; 0x011508b3; 0x0108a023; 0x000e0913; 0xeedff06f; 0x00291913; 0x06810513; 0x01250533; 0x00652023; 0x00040913; 0x7ff97513; 0x06810813; 0x00190593; 0x00290613; 0x00390693; 0xfff90713; 0x00251793; 0x7ff5f413; 0x7ff67513; 0x7ff6f593; 0x7ff77693; 0x00f80633; 0x00241493; 0x00251713; 0x00259793; 0x00269893; 0x009806b3; 0x00e80733; 0x00f807b3; 0x01180833; 0x7ff9f893; 0x01289a63; 0x000b889b; 0x02400293; 0x0a589a63; 0x1fc0006f; 0x00289893; 0x06810293; 0x011288b3; 0x0008ab03; 0x009e78b7; 0x4d18889b; 0x011b7a63; 0x000b889b; 0x02400293; 0x08589463; 0x2040006f; 0x091b1063; 0x00198893; 0x7ff8f893; 0xff2882e3; 0x00289893; 0x011288b3; 0x0008a883; 0x2abda2b7; 0xd572829b; 0xfc58e6e3; 0x04589c63; 0x00298893; 0x7ff8f893; 0xfb288ee3; 0x00289893; 0x06810293; 0x011288b3; 0x0008a883; 0x0f5272b7; 0x0802829b; 0xfa58e0e3; 0x02589663; 0x00398893; 0x7ff8f893; 0xf92888e3; 0x00289893; 0x06810293; 0x011288b3; 0x0008a883; 0x273f02b7; 0xfff2829b; 0xf712fae3; 0x000b889b; 0x02d00293; 0x0112c663; 0x00100293; 0x0080006f; 0x00900293; 0x09298e63; 0x00000313; 0x01528abb; 0xfff00893; 0x3b9ad3b7; 0x005898bb; 0xa0038393; 0xfff8c893; 0x0053d3bb; 0x00098e13; 0x0280006f; 0x011efeb3; 0x00603f33; 0x001e0e13; 0x027e833b; 0xffff0f13; 0xff7f7e93; 0x7ffe7e13; 0x01db8bb3; 0x032e0c63; 0x002e1e93; 0x06810f13; 0x01df0f33; 0x000f2e83; 0x005edfbb; 0x006f8fbb; 0x013e4333; 0x01f36333; 0x01ff2023; 0xfa031ce3; 0x00198993; 0x7ff9f993; 0xfadff06f; 0xea0300e3; 0xe3341ce3; 0x00082883; 0x0018e893; 0x01182023; 0xe8dff06f; 0x02d00813; 0x01184663; 0x00100813; 0x0080006f; 0x00900813; 0x01528abb; 0x00b9529b; 0x02400313; 0x009e73b7; 0x2abdae37; 0x0f527eb7; 0x273f0f37; 0x4d13839b; 0xd57e0e1b; 0x080e8e9b; 0xffff0f1b; 0x00c0006f; 0x04688863; 0x010a8abb; 0xfe028ce3; 0x00062b03; 0x007b7663; 0xfe6898e3; 0x06c0006f; 0xfe7b14e3; 0xff240ae3; 0x0006af83; 0xffcfe6e3; 0xfdcf9ce3; 0xff2502e3; 0x00072f83; 0xfddfeee3; 0xfddf94e3; 0xfd258ae3; 0x0007af83; 0xfdff76e3; 0xfb9ff06f; 0x00090993; 0x00000513; w_1077; 0x00050b93; 0x00058c13; 0x06810513; 0x00291913; 0x00a484b3; 0xfe04ae23; 0x01250533; 0x00052b03; 0x00040913; 0x0180006f; 0x00090993; 0x00000513; w_1090; 0x00050b93; 0x00058c13; 0x000b0513; w_1094; 0x00050c93; 0x00058d13; 0x00402537; 0xcdd50513; 0x00c51513; 0xd6550b13; 0x01cb1b13; 0x00000513; 0x000b0593; 0x000b8613; 0x000c0693; w_1106; 0x000c8613; 0x000d0693; w_1109; 0x00050b93; 0x00058c13; 0x00198513; 0x7ff57513; 0x00298413; 0x01251c63; 0x7ff47913; 0x00291593; 0x06810613; 0x00c585b3; 0xfe05ae23; 0x00251513; 0x06810493; 0x00a48533; 0x00052503; w_1125; 0x00050c93; 0x00058d13; 0x00000513; 0x000b0593; 0x000b8613; 0x000c0693; w_1132; 0x000c8613; 0x000d0693; w_1135; 0x00050b93; 0x00058c13; 0x7ff47513; 0x00398413; 0x01251a63; 0x7ff47913; 0x00291593; 0x009585b3; 0xfe05ae23; 0x00251513; 0x00a48533; 0x00052503; w_1148; 0x00050c93; 0x00058d13; 0x00402537; 0xcdd50513; 0x00c51513; 0xd6550b13; 0x01cb1b13; 0x00000513; 0x000b0593; 0x000b8613; 0x000c0693; w_1160; 0x000c8613; 0x000d0693; w_1163; 0x00050b93; 0x00058c13; 0x7ff47513; 0x00498493; 0x01251c63; 0x7ff4f913; 0x00291593; 0x06810613; 0x00c585b3; 0xfe05ae23; 0x00251513; 0x06810593; 0x00a58533; 0x00052503; w_1178; 0x00050c93; 0x00058d13; 0x00000513; 0x000b0593; 0x000b8613; 0x000c0693; w_1185; 0x000c8613; 0x000d0693; w_1188; 0x00050b13; 0x00058b93; 0x04813503; w_1192; 0x00050613; 0x00058693; 0x000b0513; 0x000b8593; w_1197; 0x00050b13; 0x071a8413; 0x02813503; 0x40a40cbb; 0x00058a13; 0x03813d83; 0x01bcc663; 0x000d8d13; 0x0100006f; 0x01902533; 0x40a00533; 0x01957d33; 0x03b13c23; 0x07000513; 0x09a56863; 0x00100513; 0xd2050453; 0x0e100513; 0x41a5053b; 0x22840553; w_1218; w_1219; 0x000b0613; 0x000a0693; w_1222; 0x00050b93; 0x00058c13; 0x07100513; 0x41a5053b; 0x22840553; w_1228; w_1229; 0x00050613; 0x00058693; 0x000b0513; 0x000a0593; w_1234; 0x00050613; 0x00058693; 0x000b0513; 0x000a0593; 0x00c13823; 0x00d13c23; w_1241; 0x000b8613; 0x000c0693; w_1244; 0x00050b13; 0x00058a13; 0x00c0006f; 0x01013b83; 0x01813c03; 0x7ff4f513; 0x01251a63; 0x00813983; 0x01013903; 0x01813483; 0x1140006f; 0x00251513; 0x06810593; 0x00a58533; 0x00052503; 0x1dcd65b7; 0x4ff5861b; 0x01813483; 0x02a66063; 0x04051263; 0x00598993; 0x7ff9f513; 0x03251c63; 0x00813983; 0x01013903; 0x0800006f; 0x5005859b; 0x02b51863; 0x00598993; 0x7ff9f513; 0x04813583; 0xd20587d3; 0x03251a63; w_1278; w_1279; 0x0300006f; w_1281; w_1282; 0x00c0006f; w_1284; w_1285; 0x04813503; 0xd2050753; 0x12e7f553; 0x0100006f; w_1290; w_1291; 0x12f77553; 0x00813983; w_1294; 0x00050613; 0x00058693; 0x01013503; 0x00048593; w_1299; 0x00050913; 0x00058493; 0x000d051b; 0x06f00593; 0x04a5e863; 0x00100513; w_1306; 0x00050613; 0x00058693; 0x00090513; 0x00048593; w_1311; 0x00000613; 0x00000693; w_1314; 0x02051263; 0x03fff6b7; 0x02469693; 0x00090513; 0x00048593; 0x00000613; w_1321; 0x00050913; 0x00058493; 0x000b0513; 0x000a0593; 0x00090613; 0x00048d93; 0x00048693; w_1329; 0x000b8613; 0x000c0693; w_1332; 0x00050493; 0x02141413; 0x02145413; 0xffe98513; 0x00058a13; 0x08855a63; 0x00048513; 0x000a0593; w_1341; 0x00050b13; 0x00058b93; 0x00200513; w_1345; 0x03f8f6b7; 0x02469693; 0x00000613; w_1349; 0x00050613; 0x00058693; 0x000b0513; 0x000b8593; w_1354; 0x00090b13; 0x04054a63; 0x03813503; 0x00aca533; 0x000d0d1b; 0x019d45b3; 0x00b03433; 0x00857433; w_1363; w_1364; w_1365; 0x00050613; 0x00058693; 0x00048513; 0x000a0593; w_1370; 0x00050493; 0x00058a13; 0x001a8a9b; 0x0140006f; 0x05813903; 0x0440006f; 0x03813503; 0x00aca433; 0x06ea851b; 0x05813903; 0x00a9da63; w_1382; 0x02200593; 0x00b52023; 0x0200006f; 0x00040e63; 0x000b0513; 0x000d8593; 0x00000613; 0x00000693; w_1391; 0xfc051ce3; 0x00093503; 0x000025b7; 0x00b105b3; 0x0685b583; 0x0ab51863; 0x00048513; 0x000a0593; 0x000a8613; 0x000026b7; 0x8f06869b; 0x00d10133; 0x7e813083; 0x7e013403; 0x7d813483; 0x7d013903; 0x7c813983; 0x7c013a03; 0x7b813a83; 0x7b013b03; 0x7a813b83; 0x7a013c03; 0x79813c83; 0x79013d03; 0x78813d83; 0x78013407; 0x7f010113; w_1419; 0x04813503; w_1421; 0x00050413; 0x00058493; 0x000a8513; w_1425; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_1430; 0x00050413; 0xff6b8b9b; w_1433; 0x002b9b93; w_1435; 0x01750533; 0x00052503; 0x00058493; w_1439; 0xa44ff06f; w_1441; 0xf5010113; 0x0a113423; 0x0a813023; 0x08913c23; 0x09213823; 0x09313423; 0x09413023; 0x07513c23; 0x07613823; 0x07713423; 0x07813023; 0x05913c23; 0x05a13823; 0x05b13423; 0x04813027; 0x00070a13; 0x02d13423; 0x00c13c23; 0x00058413; 0x00050c13; 0x00000513; w_1463; 0x00050993; 0x00058b93; 0x00100513; w_1467; 0x02a13c23; 0x008c3503; 0x0b8c3603; 0x00058d93; 0x04c50a63; 0x00150593; 0x00bc3423; 0x00054503; 0x00813023; 0x02e00593; 0x04b50863; 0x00000493; 0x00000413; 0x03000593; 0x00000913; 0x10b51e63; 0x008c3503; 0x0b8c3583; 0x04b50e63; 0x00150593; 0x00bc3423; 0x00054503; 0x03000413; 0x06850463; 0x0800006f; 0x000c0513; 0xec0fe0ef; 0x00813023; 0x02e00593; 0xfab51ce3; 0x00000413; 0x008c3503; 0x0b8c3583; 0x06b50a63; 0x00150593; 0x00bc3423; 0x00054503; 0x00000913; 0x03000493; 0x08950463; 0x06c0006f; 0x000c0513; 0xe80fe0ef; 0x03000413; 0x00850a63; 0x02c0006f; 0x000c0513; 0xe6cfe0ef; 0x02851063; 0x008c3503; 0x0b8c3583; 0xfeb506e3; 0x00150593; 0x00bc3423; 0x00054503; 0xfe8504e3; 0x02e00593; 0x06b51463; 0x00100413; 0x008c3503; 0x0b8c3583; 0xf8b51ae3; 0x000c0513; 0xe2cfe0ef; 0x00000913; 0x03000493; 0x00950e63; 0x00100493; 0x0480006f; 0x000c0513; 0xe10fe0ef; 0xfff90913; 0x02951263; 0x008c3503; 0x0b8c3583; 0xfeb504e3; 0x00150593; 0x00bc3423; 0x00054503; 0xfff90913; 0xfe9502e3; 0x00100493; 0x00c0006f; 0x00000493; 0x00000913; 0x00100413; 0x03413023; 0x00000a93; 0x02013823; 0x00000a13; 0x00a00c93; 0x03900d13; 0x02e00b13; 0x01313823; 0x01713423; 0xfd05059b; 0x00050613; 0x1395fa63; 0x0340006f; 0x03651863; 0x12049e63; 0x00100493; 0x000a0913; 0x008c3503; 0x0b8c3583; 0x0eb51e63; 0x000c0513; 0xd7cfe0ef; 0xfd05059b; 0x00050613; 0x1195f063; 0x00ad5463; 0xfa96059b; 0x00700513; 0x01454863; 0x004a9a93; 0x01558abb; 0x0b80006f; 0x01d00513; 0x07456863; 0x00058513; w_1589; 0x000b8d13; 0x00098b93; 0x00050993; 0x00058413; 0x01000513; w_1595; 0x00050613; 0x00058693; 0x03813503; 0x000d8593; w_1600; 0x00050613; 0x00058d93; 0x00098513; 0x00040593; 0x02c13c23; 0x000d8693; w_1607; 0x000b8613; 0x000d0693; 0x03900d13; w_1611; 0x00050993; 0x00058b93; 0x0440006f; 0x04058063; 0x03013503; 0x02051c63; w_1618; w_1619; w_1620; 0x03813603; 0x000d8693; w_1623; 0x00098613; 0x000b8693; w_1626; 0x00050993; 0x00058b93; 0x00100513; 0x02a13823; 0x001a0a13; 0x00100413; 0x008c3503; 0x0b8c3583; 0xf0b506e3; 0x00150593; 0x00bc3423; 0x00054503; 0xfd05059b; 0x00050613; 0xf195e4e3; 0x02056613; 0xed6508e3; 0xf9f6069b; 0x00500713; 0xecd772e3; 0x06040a63; 0x000a0413; 0x00048463; 0x00090413; 0x00700593; 0x0145ca63; 0xff8a0a13; 0x001a0a13; 0x004a9a9b; 0xfe0a1ce3; 0xfdf57513; 0x05000593; 0x02b51263; 0x000c0513; 0x02013483; 0x00048593; 0x3a4000ef; 0xfff00593; 0x03f59593; 0x02b51063; 0x1c048e63; 0x0c0c3503; 0x04054863; 0x00000513; 0x008c3583; 0xfff58593; 0x00bc3423; 0x040a9263; 0x0e00006f; 0x0c0c3503; 0x0c054263; 0x008c3503; 0xfff50593; 0x00bc3423; 0x02013583; 0x0a058c63; 0xffe50593; 0x00bc3423; 0x0a048c63; 0xffd50513; 0x00ac3423; 0x0ac0006f; 0x00000513; 0x0a0a8263; 0x00241413; 0x00a40533; 0xfe050c13; 0x01813403; 0x4080053b; 0x03855c63; w_1697; 0x02200593; 0x00b52023; 0x02813503; w_1701; 0x07fff637; 0x02461613; 0xfff60413; 0xfff00613; 0x00040693; w_1707; 0xfff00613; 0x0380006f; 0xf1e4051b; 0x0aac5263; w_1712; 0x02200593; 0x00b52023; 0x02813503; w_1716; 0x00100413; 0x03041413; 0x00000613; 0x00040693; w_1721; 0x00000613; 0x00040693; w_1724; 0x02c0006f; 0x02013503; 0x00051863; 0x000c0513; 0x00000593; 0xad8fe0ef; 0x02813503; 0xd20507d3; 0xf2000753; 0x12e7f553; w_1735; 0x0a813083; 0x0a013403; 0x09813483; 0x09013903; 0x08813983; 0x08013a03; 0x07813a83; 0x07013b03; 0x06813b83; 0x06013c03; 0x05813c83; 0x05013d03; 0x04813d83; 0x04013407; 0x0b010113; 0x00008067; 0x0a0ac063; w_1753; w_1754; 0x00013903; 0x0480006f; 0x001aea93; 0x00100513; w_1759; 0x00050613; 0x00058693; 0x00098513; 0x000b8593; w_1764; 0x00050613; 0x00058693; 0x00098513; 0x000b8593; w_1769; 0x00050993; 0x00058b93; 0xfffc0c13; 0x040ac863; 0x22840553; w_1775; 0x00050613; 0x00058693; 0x00098513; 0x000b8593; w_1780; 0x001a9a9b; 0xf8055ee3; 0x00098613; 0x000b8693; 0xfb9ff06f; 0x000c0513; 0x00000593; 0x9f0fe0ef; 0x00000513; w_1790; 0xf25ff06f; 0x00013903; 0x02000513; 0x4085053b; 0x00ac05b3; 0x0125da63; 0x00ac053b; 0x00a025b3; 0x40b005b3; 0x00a5f933; 0x07000513; 0x09256863; 0x00100513; 0xd2050553; 0x09000513; 0x4125053b; 0x0009091b; w_1808; w_1809; 0x00050413; 0x00058493; 0x02813503; w_1813; 0x00050613; 0x00058693; 0x00040513; 0x00048593; w_1818; 0x00a13823; 0x01f00513; 0x00b13423; 0x05256063; 0x00098513; 0x000b8593; 0x00000613; 0x00000693; w_1827; 0x001af593; 0x02059263; 0x00a03533; 0x00050e63; 0x001aea93; 0x00000513; w_1834; 0x00050b13; 0x00058b93; 0x0080006f; 0x00098b13; 0x02813503; w_1840; 0x00050413; 0x00058993; 0x000a8513; w_1844; 0x00050613; 0x00058693; 0x00040513; 0x00098593; w_1849; 0x01013483; 0x00048613; 0x00813903; 0x00090693; w_1854; 0x00050a13; 0x00058a93; 0x00040513; 0x00098593; 0x000b0613; 0x000b8693; w_1861; 0x000a0613; 0x000a8693; w_1864; 0x00048613; 0x00090693; w_1867; 0x00050413; 0x00058493; 0x00000613; 0x00000693; w_1872; 0x00051863; w_1874; 0x02200593; 0x00b52023; 0x000c061b; 0x00040513; 0x00048593; 0x0a813083; 0x0a013403; 0x09813483; 0x09013903; 0x08813983; 0x08013a03; 0x07813a83; 0x07013b03; 0x06813b83; 0x06013c03; 0x05813c83; 0x05013d03; 0x04813d83; 0x04013407; 0x0b010113; w_1895]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Definition extendsftf2_code : list Z :=
[0xe00505d3; 0x0175d51b; 0x02959613; 0x0ff57693; 0x02965613; 0x02068a63; 0x0ff00513; 0x0ea69e63; 0x00000513; 0x01961613; 0x000086b7; 0xfff68693; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x0e060c63; 0x00165693; 0x00d666b3; 0x0026d713; 0x00e6e6b3; 0x0046d713; 0x00e6e6b3; 0x02969713; 0x03175793; 0x00f6e6b3; 0x555557b7; 0x5557879b; 0x03975713; 0x00e6e6b3; 0xfff6c693; 0x0016d713; 0x00f77733; 0x333337b7; 0x3337879b; 0x40e686b3; 0x00f6f733; 0x0026d693; 0x00f6f6b3; 0x00d706b3; 0x0046d713; 0x00e686b3; 0x0f0f1737; 0xf0f70713; 0x00e6f6b3; 0x01010737; 0x10170713; 0x02e686b3; 0x00004737; 0xf8070713; 0x0186d69b; 0x40d70733; 0x01168693; 0x00d61633; 0x0006a693; 0xfff68693; 0x00c6f633; 0x00100793; 0x00970693; 0x03079793; 0x00f64633; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x00000513; 0x00004737; 0xf8070713; 0x00e686b3; 0x01961613; 0x01f5d593; 0x03f59593; 0x03069693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067; 0x01f5d593; 0x03f59593; 0x03001693; 0x00b6e5b3; 0x00c5e5b3; 0x00008067]%Z.

Ltac2 rec zt_plain_arith' (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
| _ => false
end.
Ltac2 rec zt_codomain (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ b => zt_codomain b
| Constr.Unsafe.LetIn _ _ b => zt_codomain b
| Constr.Unsafe.Cast c _ _ => zt_codomain c
| _ => t
end.
Ltac2 rec zt_head (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f _ => zt_head f
| Constr.Unsafe.Cast c _ _ => zt_head c
| _ => t
end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
let h := zt_head (zt_codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
| _ => false
end.
Ltac2 zt_is_local' (id : ident) : bool :=
match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if zt_plain_arith' ty then None
else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof.
intros a m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
pose proof (Z.sub_land_same_l m a) as E. rewrite (Z.land_comm a m).
assert (0 <= Z.land m (Z.lnot a))%Z by (apply Z.land_nonneg; left; exact Hm). lia.
Qed.

Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof.
intros ws i t Hw Ht. unfold sx32. f_equal. unfold wval in Hw. rewrite swrap32_eq.
pose proof (bv_unsigned_in_range 64 (wnth ws i)) as R.
rewrite <- Hw. rewrite <- Hw in Ht. Z.div_mod_to_equations. lia.
Qed.

Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. intros. unfold zx32, wval. reflexivity. Qed.

Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof.
intros t sh Ht Hsh. rewrite (Z.mod_small sh 32) by lia.
replace (bv_wrap 32 t) with t by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
assert (0 <= Z.shiftr t sh <= t)%Z.
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ sh)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia). nia. }
apply swrap32_small. lia.
Qed.

Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Definition FS_DEPTH : Z := 8656.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 : Z).
Variables (joff_1419 : bv 21).
Variables (got_ssp RATP STRING_READ ssp_guard : Z).
Variables (e_errno_loc e_extenddftf2 e_fpclassifyl e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 : Z).
Hypothesis CODE : code_at segs base (floatscan_code w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 7584.
Hypothesis D_1419 : decode_any (Z_to_bv 32 w_1419) = Some (Jal 0 joff_1419, 4%Z).
Hypothesis E_1419 : is_ecall (Z_to_bv 32 w_1419) = false.
Hypothesis LINK_1419 : gw_anch (base + 5676 + bv_signed joff_1419)%Z (e_extendsftf2 + 1132)%Z.
Hypothesis CODE_e_errno_loc : code_at segs e_errno_loc errno_loc_code.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_got_ssp_RERRNO : gw_le (got_ssp + 8) (RATP + -164).
Hypothesis LAY_RATP_ssp_guard : gw_le (RATP + 8) ssp_guard.

Local Definition gw_tbl_0 := tt.

Definition getf2_post : ltac:(gw_rebind_ty (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QVbl.Mq1.getf2_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QVbl.Mq1.getf2_post segs) getf2_post gw_tbl_0).
Definition scalbn_post : ltac:(gw_rebind_ty (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq4.scalbn_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q91D.Mq4.scalbn_post segs) scalbn_post gw_tbl_1).
Definition SCALBNL := (e_extendsftf2 + 1132)%Z.
Local Definition gw_tbl_3 := (gw_ent (@QQRC.Mq2.SCALBNL e_extendsftf2) SCALBNL gw_tbl_2).
Definition COPYSIGNL := (e_extendsftf2 + 348)%Z.
Local Definition gw_tbl_4 := (gw_ent (@QQRC.Mq2.COPYSIGNL e_extendsftf2) COPYSIGNL gw_tbl_3).
Definition FABSL := (e_extendsftf2 + 1120)%Z.
Local Definition gw_tbl_5 := (gw_ent (@QQRC.Mq2.FABSL e_extendsftf2) FABSL gw_tbl_4).
Definition leafq_post : ltac:(gw_rebind_ty (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QQRC.Mq2.leafq_post segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@QQRC.Mq2.leafq_post segs) leafq_post gw_tbl_5).
Definition scalbnl_post : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_post segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QQRC.Mq2.scalbnl_post segs) scalbnl_post gw_tbl_6).
Definition scalbnl_stmt : ltac:(gw_rebind_ty (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@QQRC.Mq2.scalbnl_stmt segs e_extendsftf2) scalbnl_stmt gw_tbl_7).
Definition extenddftf2_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.extenddftf2_post segs) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Qy8Z.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@Q8l1.Mq0.extenddftf2_post segs) extenddftf2_post (gw_ent (@QQRC.Mq2.extenddftf2_post segs) extenddftf2_post gw_tbl_8))).
Definition divtf3_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Qy8Z.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@Q8l1.Mq0.divtf3_stmt segs e_divtf3) divtf3_stmt (gw_ent (@QQRC.Mq2.divtf3_stmt segs e_divtf3) divtf3_stmt gw_tbl_9))).
Definition leaf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf2_post segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Qy8Z.Mq0.leaf2_post segs) leaf2_post (gw_ent (@Q8l1.Mq0.leaf2_post segs) leaf2_post (gw_ent (@QQRC.Mq2.leaf2_post segs) leaf2_post gw_tbl_10))).
Definition leaf1_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.leaf1_post segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Qy8Z.Mq0.leaf1_post segs) leaf1_post (gw_ent (@Q8l1.Mq0.leaf1_post segs) leaf1_post gw_tbl_11)).
Definition call2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.call2_post segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Qy8Z.Mq0.call2_post segs) call2_post (gw_ent (@Q8l1.Mq0.call2_post segs) call2_post (gw_ent (@QQRC.Mq2.call2_post segs) call2_post gw_tbl_12))).
Definition FMODL := (e_extendsftf2 + 388)%Z.
Local Definition gw_tbl_14 := (gw_ent (@Q8l1.Mq0.FMODL e_extendsftf2) FMODL gw_tbl_13).
Definition rfmodl_post : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_post segs) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@Q8l1.Mq0.rfmodl_post segs) rfmodl_post gw_tbl_14).
Definition rfmodl_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@Q8l1.Mq0.rfmodl_stmt segs e_extendsftf2) rfmodl_stmt gw_tbl_15).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@Q5m9.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mql.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_16)))).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_17)).
Local Definition gw_tbl_18 := (gw_ent (@Q5m9.Mq1.ssJ STRING_READ) ssJ (gw_ent (@QZxv.Mql.ssJ STRING_READ) ssJ (gw_ent (@QROt.Mq2.ssJ STRING_READ) ssJ (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_17)))).
Definition RFJ : ltac:(gw_rebind_ty (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QZxv.Mql.RFJ STRING_READ) constr:(gw_tbl_18)).
Local Definition gw_tbl_19 := (gw_ent (@Q5m9.Mq1.RFJ STRING_READ) RFJ (gw_ent (@QZxv.Mql.RFJ STRING_READ) RFJ gw_tbl_18)).
Definition fixunstfsi_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fixunstfsi_post segs) constr:(gw_tbl_19)).
Local Definition gw_tbl_20 := (gw_ent (@Qy8Z.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@Q8l1.Mq0.fixunstfsi_post segs) fixunstfsi_post (gw_ent (@QQRC.Mq2.fixunstfsi_post segs) fixunstfsi_post gw_tbl_19))).
Definition floatsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatsitf_post segs) constr:(gw_tbl_20)).
Local Definition gw_tbl_21 := (gw_ent (@Qy8Z.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@Q8l1.Mq0.floatsitf_post segs) floatsitf_post (gw_ent (@QQRC.Mq2.floatsitf_post segs) floatsitf_post gw_tbl_20))).
Definition floatunsitf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.floatunsitf_post segs) constr:(gw_tbl_21)).
Local Definition gw_tbl_22 := (gw_ent (@Qy8Z.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@Q8l1.Mq0.floatunsitf_post segs) floatunsitf_post (gw_ent (@QQRC.Mq2.floatunsitf_post segs) floatunsitf_post gw_tbl_21))).
Definition addtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.addtf3_post segs) constr:(gw_tbl_22)).
Local Definition gw_tbl_23 := (gw_ent (@Qy8Z.Mq0.addtf3_post segs) addtf3_post (gw_ent (@Q8l1.Mq0.addtf3_post segs) addtf3_post (gw_ent (@QQRC.Mq2.addtf3_post segs) addtf3_post gw_tbl_22))).
Definition multf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_post segs) constr:(gw_tbl_23)).
Local Definition gw_tbl_24 := (gw_ent (@Qy8Z.Mq0.multf3_post segs) multf3_post (gw_ent (@Q8l1.Mq0.multf3_post segs) multf3_post (gw_ent (@QQRC.Mq2.multf3_post segs) multf3_post gw_tbl_23))).
Definition multf3_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.multf3_stmt segs e_multf3) constr:(gw_tbl_24)).
Local Definition gw_tbl_25 := (gw_ent (@Qy8Z.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@Q8l1.Mq0.multf3_stmt segs e_multf3) multf3_stmt (gw_ent (@QQRC.Mq2.multf3_stmt segs e_multf3) multf3_stmt gw_tbl_24))).
Definition divtf3_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_25)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.divtf3_post segs) constr:(gw_tbl_25)).
Local Definition gw_tbl_26 := (gw_ent (@Qy8Z.Mq0.divtf3_post segs) divtf3_post (gw_ent (@Q8l1.Mq0.divtf3_post segs) divtf3_post (gw_ent (@QQRC.Mq2.divtf3_post segs) divtf3_post gw_tbl_25))).
Definition letf2_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_26)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.letf2_post segs) constr:(gw_tbl_26)).
Local Definition gw_tbl_27 := (gw_ent (@Qy8Z.Mq0.letf2_post segs) letf2_post (gw_ent (@Q8l1.Mq0.letf2_post segs) letf2_post (gw_ent (@QQRC.Mq2.letf2_post segs) letf2_post gw_tbl_26))).
Definition frexpl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_27)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.frexpl_post segs) constr:(gw_tbl_27)).
Local Definition gw_tbl_28 := (gw_ent (@Qy8Z.Mq0.frexpl_post segs) frexpl_post (gw_ent (@Q8l1.Mq0.frexpl_post segs) frexpl_post (gw_ent (@QQRC.Mq2.frexpl_post segs) frexpl_post gw_tbl_27))).
Definition signbitl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_28)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.signbitl_post segs) constr:(gw_tbl_28)).
Local Definition gw_tbl_29 := (gw_ent (@Qy8Z.Mq0.signbitl_post segs) signbitl_post (gw_ent (@Q8l1.Mq0.signbitl_post segs) signbitl_post (gw_ent (@QQRC.Mq2.signbitl_post segs) signbitl_post gw_tbl_28))).
Definition fpclassifyl_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.fpclassifyl_post segs) constr:(gw_tbl_29)).
Local Definition gw_tbl_30 := (gw_ent (@Qy8Z.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@Q8l1.Mq0.fpclassifyl_post segs) fpclassifyl_post (gw_ent (@QQRC.Mq2.fpclassifyl_post segs) fpclassifyl_post gw_tbl_29))).
Definition calla_post : ltac:(gw_rebind_ty (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)) := ltac:(gw_rebind_tm (@Qy8Z.Mq0.calla_post segs) constr:(gw_tbl_30)).
Local Definition gw_tbl_31 := (gw_ent (@Qy8Z.Mq0.calla_post segs) calla_post gw_tbl_30).

Hypothesis divtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQRC.divtf3_spec segs e_divtf3) 9%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).

Hypothesis getf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq1.getf2_spec segs e_getf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).  Arguments getf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.

Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).  Arguments extenddftf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.

Hypothesis scalbn_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq4.gw_all) (@Q91D.Mq4.scalbn_spec) e_scalbn)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).  Arguments scalbn_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.

Hypothesis fabsl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.fabsl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).  Arguments fabsl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis copysignl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.copysignl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).  Arguments copysignl_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope _%_Z_scope.
Hypothesis scalbnl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQRC.Mq2.gw_all) (@QQRC.Mq2.scalbnl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).

Hypothesis rfmodl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq0.gw_all) (@Q8l1.Mq0.rfmodl_spec) e_extendsftf2)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_31))) in exact T).
Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs e_letf2) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QVbl.Mq2.letf2_post segs) letf2_post in exact T).  Arguments letf2_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments floatsitf_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope _%_Z_scope.
Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (@QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).  Arguments addtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis subtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QkTt.Mq1.subtf3_spec segs e_subtf3) 4%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).  Arguments subtf3_spec _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _%_bv_scope _ _%_bv_scope _%_function_scope.
Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (@QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (@QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (@QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (@QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (@QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (@QCa8.multf3_post segs) multf3_post in let T := gw_subst T (@QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (@QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (@QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (@QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (@QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (@QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (@QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).
Notation rfj := G.T_rfj.rfj.

Definition letf2_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.letf2_callv) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.letf2_callv)).
Definition floatsitf_callv : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callv) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callv)).
Definition floatsitf_callp : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.floatsitf_callp) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.floatsitf_callp)).
Definition multf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.multf3_callq) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.multf3_callq)).
Definition divtf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.divtf3_callq) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.divtf3_callq)).
Definition addtf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.addtf3_callq) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.addtf3_callq)).
Definition subtf3_callq : ltac:(gw_ctx_fold_ty (@Qy8Z.Mq0.subtf3_callq) constr:(gw_tbl_31)) := ltac:(gw_ctx_fold_tm (@Qy8Z.Mq0.subtf3_callq)).

Notation F_divtf3_main__divtf3_spec := divtf3_spec (only parsing).

#[using="got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_fpclassifyl e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1419 E_1419 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard divtf3_spec getf2_spec extenddftf2_spec scalbn_spec fabsl_spec copysignl_spec scalbnl_spec rfmodl_spec letf2_spec floatsitf_spec addtf3_spec subtf3_spec multf3_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1419 got_ssp RATP STRING_READ ssp_guard e_errno_loc e_extenddftf2 e_fpclassifyl e_letf2 e_getf2 e_multf3 e_floatsitf e_scalbn e_subtf3 e_addtf3 e_divtf3 e_extendsftf2 CODE BASE4 BASER D_1419 E_1419 LINK_1419 CODE_e_errno_loc RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard divtf3_spec getf2_spec extenddftf2_spec scalbn_spec fabsl_spec copysignl_spec scalbnl_spec rfmodl_spec letf2_spec floatsitf_spec addtf3_spec subtf3_spec multf3_spec.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section DivW.
Local Open Scope Z_scope.
#[using="Type"] Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
intros v i Hv Hi. unfold v_divw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
rewrite (swrap32_small v), (swrap32_small i) by lia. rewrite Z.quot_div_nonneg by lia.
assert (0 <= v / i <= v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|]; nia]).
apply swrap32_small. lia.
Qed.
#[using="Type"] Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof.
intros j Hj.
assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
match goal with |- context [znth p10s ?j] => let v := eval vm_compute in (znth p10s j) in change (znth p10s j) with v end; (split; [lia | reflexivity]).
Qed.
End DivW.

Definition RERRNO : Z := (RATP + -164)%Z.
Definition ERRNO_LOC : Z := (e_errno_loc + 0x0).

#[using="CODE_e_errno_loc"] Lemma errno_loc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
evt segs (fun ms' => exists m', ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m')
(MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ERRNO_LOC) fc None m (seg_rom segs)).
Proof. clear - CODE_e_errno_loc segs RATP.
intros until m. intros MI. gw_expose RATP; unfold ERRNO_LOC, RERRNO.
zs. zs. zs.
apply evt_done. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI].
Qed.

Section CallE.
Local Open Scope Z_scope.
Definition DS : divtf3_stmt := F_divtf3_main__divtf3_spec.
#[using="multf3_spec"] Lemma mul_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk segs m (q - 80) q -> mem_inv segs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_multf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - multf3_spec segs e_multf3. intros until Y. intros ST MI Hq -> -> -> ->. apply multf3_callq; assumption. Qed.
#[using="divtf3_spec"] Lemma div_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk segs m (q - 112) q -> mem_inv segs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_divtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - divtf3_spec segs e_divtf3. intros until Y. intros ST MI Hq -> -> -> ->. apply (divtf3_callq DS); assumption. Qed.
#[using="addtf3_spec"] Lemma add_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk segs m (q - 48) q -> mem_inv segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_addtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - addtf3_spec segs e_addtf3. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply addtf3_callq; assumption. Qed.
#[using="subtf3_spec"] Lemma sub_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk segs m (q - 48) q -> mem_inv segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_subtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - subtf3_spec segs e_subtf3. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply subtf3_callq; assumption. Qed.
#[using="letf2_spec"] Lemma letf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_letf2 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - letf2_spec segs e_letf2. intros until Y. intros MI -> -> -> ->. apply letf2_callv; assumption. Qed.
#[using="getf2_spec"] Lemma getf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_ge X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_getf2 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - getf2_spec segs e_getf2.
intros until Y. intros MI -> -> -> ->. eapply evt_mono. { eapply getf2_spec. exact MI. }
intros ms' P. unfold getf2_post in P. unfold leaf1_post. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite Q9Ay.f128_ge_canon in P. exact P.
Qed.

#[using="scalbn_spec"] Lemma scalbn_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv segs m -> frm0 fc -> (-2^31 <= n < 2^31)%Z ->
evt segs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
(bvmap_set 10 (scalbn_model (reg_get F 10) n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ frm0 fc')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_scalbn + 0x0)) fc None m (seg_rom segs)).
Proof. clear - scalbn_spec segs e_scalbn.
intros until n. intros MI FRM Hn. eapply evt_mono. { eapply scalbn_spec; [exact MI | exact FRM | | exact Hn]. apply signed_of_Z; lia. }
intros ms' P. unfold scalbn_post in P. exact P.
Qed.
#[using="fabsl_spec"] Lemma fabsl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah X : Z),
mem_inv segs m -> al = lo64 X -> ah = hi64 X ->
evt segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom segs)).
Proof. clear - fabsl_spec segs. intros until X. intros MI -> ->. apply fabsl_spec; assumption. Qed.
#[using="copysignl_spec"] Lemma copysignl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv segs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt segs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom segs)).
Proof. clear - copysignl_spec segs. intros until Y. intros MI -> -> -> ->. apply copysignl_spec; assumption. Qed.

#[using="rfmodl_spec"] Lemma fmodl_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q lo al ah bl bh X Y r : Z),
stk segs m lo q -> mem_inv segs m -> (lo <= q - 192) -> (4288 <= q < 2^63) ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
m_fmodl X Y = Some r ->
evt segs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 192, q)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo q /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k))
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom segs)).
Proof. clear - rfmodl_spec segs.
intros until r. intros ST MI Hlo Hq -> -> -> -> HMr.
destruct (stk_split _ _ _ (q - 192) _ ST ltac:(lia)) as [ST1 ST2].
eapply evt_mono. { eapply (rfmodl_spec ra q); unfold RFMODL_DEPTH; eauto; lia. }
intros ms' P. unfold rfmodl_post, RFMODL_DEPTH in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & MU & WM & MI' & ST' & FOK).
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [|exact FOK].
eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ].
Qed.
End CallE.
Definition FLOATSCAN : Z := (base + 0x0).

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Definition ctx_all : unit :=
let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
Fp, T, p, J, txt, pre, post, canary, pok, fuelc, f0, kmin0, c0, fR, yR) in tt.

Definition Wfs : list (Z * Z) := [(q - FS_DEPTH, q); (Fp, Fp + 232); (RERRNO, RERRNO + 4)]%Z.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).
Definition zero0 : Z := f128_of_i32 0.

Definition FokR (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.

Definition Fok (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 8%Z -> bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. intros k _ _ _ _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set : forall F' (r : bv 5) v, Fok F' -> (bv_unsigned r = 8 \/ bv_unsigned r = 10 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15)%Z -> Fok (bvmap_set r v F').
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros F' r v H Hr k H8 H10 H14 H15. rewrite reg_get_set_other. { apply H; assumption. }
intros E. rewrite <- E in *. lia.
Qed.
#[using="Type"] Lemma Fok_trans10 : forall F1 F2, Fok F1 -> (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. intros F1 F2 H1 H2 k H8 H10 H14 H15. rewrite H2 by exact H10. apply H1; assumption. Qed.

Definition fs_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' k' c' (ev' : word),
ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch Wfs m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - FS_DEPTH) q
/\ rw_cells segs m' Fp (rf_cells T p true fR J)
/\ RFJ' k' c' fR /\ (0 <= k')%Z
/\ bytes_at segs m' T (zbytes txt)
/\ ssp_cells m' canary
/\ rw_cells segs m' RERRNO [C4 ev']
/\ FokR F' /\ frm0 fc'.

Definition hi_cells : list cell :=
[C8 canary; C8 (reg_get F 8); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv segs m /\ munch Wfs m0 m /\ wmono segs m0 m
/\ rw_cells segs m (q + -120) hi_cells
/\ stk segs m (q - FS_DEPTH) (q + -8416)
/\ bytes_at segs m T (zbytes txt)
/\ rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary].
#[using="Type"] Lemma zbytes_len : length (zbytes txt) = length txt.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. unfold zbytes. apply length_map. Qed.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold Wfs, FS_DEPTH, RERRNO in MU; unfold hi_cells in FRhi;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH in ST;
gw_expose got_ssp; gw_expose ssp_guard; unfold FS_DEPTH, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Definition framL (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word) (m : word -> option byte) : Prop :=
rw_cells segs m (q + -8416) [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; CB 8 b96]
/\ rw_cells segs m RERRNO [C4 ev].
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.

#[using="Type"] Lemma rw_cells_C8_CB8 : forall m A pre (v : word) post,
rw_cells segs m A (pre ++ C8 v :: post) <-> rw_cells segs m A (pre ++ CB 8 (le8 v) :: post).
Proof. clear - segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - segs. intros m A pre v post. unfold rw_cells, cells_at.
rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
rewrite length_le8. tauto.
Qed.
#[using="Type"] Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
#[using="Type"] Lemma cb8_c8_in : forall m A pre post bs, rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. clear - segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - segs. intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Definition xrel (ws : list word) (x : list Z) (P : Z -> Prop) : Prop :=
length ws = 2048%nat /\ length x = 2048%nat /\ forall i, (0 <= i < 2048)%Z -> P i -> znth x i = wval ws i.

Notation POST := (fs_post m0).

#[using="BYT"] Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
Proof. clear - BYT ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros i Hi. pose proof (proj1 (Forall_forall _ _) BYT (znth txt i) (Qy5Y.znth_In' txt i Hi)) as R. exact R.
Qed.
#[using="Hnum"] Lemma numch_nz : forall i, (0 <= i < p)%Z -> (43 <= znth txt i <= 101)%Z.
Proof. clear - Hnum ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros i Hi. pose proof (Hnum i Hi) as E. unfold is_numch in E.
repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]);
try (apply Z.eqb_eq in E; lia). apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

#[using="pre"] Lemma frame_release : forall m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws,
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr segs m XA ws -> length ws = 2048%nat ->
stk segs m (q - FS_DEPTH) q.
Proof. clear - pre segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; try gw_hide SE_T; try gw_hide SPLO; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SPT; try gw_hide SG1; try gw_hide SG2; try gw_hide SG3; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until ws. intros FI FL XW LW. dest_finv FI. dest_framL FL.
apply u8arr_of_u32arr in XW. apply rw_cells_of_u8arr in XW. rewrite u32s_length, LW in XW.
release_frame LOW ST (q + -8312)%Z.
release_frame XW ST (q + -120)%Z.
release_frame FRhi ST q.
unfold FS_DEPTH. exact ST.
Qed.

#[using="RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard pre Hp SE_T SPF SPT SG1 SG3"] Lemma post_tail : forall m m' K F' fc' k c ev,
finv m -> rw_cells segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> rw_cells segs m RERRNO [C4 ev] ->
FokR F' -> frm0 fc' -> (0 <= K <= FS_DEPTH)%Z ->
munch [(q - K, q)]%Z m m' -> wmono segs m m' -> mem_inv segs m' ->
stk segs m' (q - FS_DEPTH) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom segs)).
Proof. clear - RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard pre Hp SE_T SPF SPT SG1 SG3 segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until ev. intros FI FC RJ Hk ERR FOK FRM' HK MU2 WM2 MI2 ST2. intros. dest_finv FI. unfold FS_DEPTH in HK, SPLO, SPT, SG1. unfold RERRNO in *.
gw_expose got_ssp; gw_expose ssp_guard.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
gw_expose got_ssp; gw_expose ssp_guard; unfold fs_post, Wfs, FS_DEPTH, RERRNO, ssp_cells. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET34 : forall m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr segs m XA ws -> length ws = 2048%nat ->
rw_cells segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) canary x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xad0)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 segs base ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. pose proof (lo64_range r). pose proof (hi64_range r).
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK.
subst r. apply evt_done. eapply (post_tail _ _ 0%Z); try eassumption.
- intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- apply munch_refl.
- apply wmono_refl.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET1 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ssp_guard) b96 ev m -> u32arr segs m XA ws -> length ws = 2048%nat ->
rw_cells segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x970)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. pose proof FL as FL0. dest_framL FL. gw_expose ssp_guard.
zs. zs. zs.
eapply L_RET34; eassumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET30 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr segs m XA ws -> length ws = 2048%nat ->
rw_cells segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xacc)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 CODE RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard Hp SE_T SPF SPT SG1 SG3 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPLO SPF2 SG2 Q1 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; try gw_hide SPLO; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. gw_expose ssp_guard.
zs.
eapply L_RET34; eassumption.
Qed.

#[using="w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1419 e_extendsftf2 CODE D_1419 E_1419 LINK_1419 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard scalbnl_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_SCL : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (Y e2 : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr segs m XA ws -> length ws = 2048%nat ->
rw_cells segs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x15c4)) fct None m (seg_rom segs)).
Proof. clear - w_22 w_23 w_170 w_256 w_502 w_509 w_556 w_560 w_569 w_573 w_579 w_586 w_591 w_595 w_600 w_603 w_648 w_676 w_683 w_690 w_718 w_722 w_727 w_730 w_733 w_737 w_742 w_792 w_796 w_843 w_845 w_1077 w_1090 w_1094 w_1106 w_1109 w_1125 w_1132 w_1135 w_1148 w_1160 w_1163 w_1178 w_1185 w_1188 w_1192 w_1197 w_1218 w_1219 w_1222 w_1228 w_1229 w_1234 w_1241 w_1244 w_1278 w_1279 w_1281 w_1282 w_1284 w_1285 w_1290 w_1291 w_1294 w_1299 w_1306 w_1311 w_1314 w_1321 w_1329 w_1332 w_1341 w_1345 w_1349 w_1354 w_1363 w_1364 w_1365 w_1370 w_1382 w_1391 w_1419 w_1421 w_1425 w_1430 w_1433 w_1435 w_1439 w_1441 w_1463 w_1467 w_1589 w_1595 w_1600 w_1607 w_1611 w_1618 w_1619 w_1620 w_1623 w_1626 w_1697 w_1701 w_1707 w_1712 w_1716 w_1721 w_1724 w_1735 w_1753 w_1754 w_1759 w_1764 w_1769 w_1775 w_1780 w_1790 w_1808 w_1809 w_1813 w_1818 w_1827 w_1834 w_1840 w_1844 w_1849 w_1854 w_1861 w_1864 w_1867 w_1872 w_1874 w_1895 joff_1419 e_extendsftf2 CODE D_1419 E_1419 LINK_1419 RNG_got_ssp RNG_ssp_guard LAY_got_ssp_RERRNO LAY_RATP_ssp_guard scalbnl_spec Hp SE_T SPLO SPF SPT SG1 SG3 Q1 segs base ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hnul Hnum HP30 T0 T1 SEP SPF2 SG2 FRM. first [clear HM | gw_hide HM | idtac]; try gw_hide Hpok; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; try gw_hide SEP; first [clear SPF2 | gw_hide SPF2 | idtac]; try gw_hide SG2; first [clear FRM | gw_hide FRM | idtac].
intros until e2. intros _ FI FL XW LW FC RJ Hk FOK FRM' He2 Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. gw_expose ssp_guard.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof (gw_unhyp scalbnl_spec) as SS. unfold scalbnl_stmt in SS.
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. eapply (post_tail m m' 112%Z); try eassumption.
- intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- unfold FS_DEPTH. eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST3 | lia ].
Qed.

#[using="Type"] Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. destruct a, b; reflexivity. Qed.
#[using="Type"] Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. destruct c; reflexivity. Qed.

Definition hide (P : Prop) := P.

#[using="Type"] Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. rewrite (Z.add_comm c (Z.land a _)), swrap32_landW. f_equal. lia. Qed.

Definition hide2 (P : Prop) := P.

Definition dfinv (m : word -> option byte) (j0 : list byte) (w16 w24 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 18396) (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr segs m XA ws /\ length ws = 2048%nat /\ rw_cells segs m Fp (rf_cells T p true f J).

Definition dfinvG (m : word -> option byte) (j0 : list byte) (w16 w24 w80 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr segs m XA ws /\ length ws = 2048%nat /\ rw_cells segs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma dfinvG_dfinv : forall m j0 w16 w24 b96 ev ws sign f,
dfinvG m j0 w16 w24 (Z_to_bv 64 18396) b96 ev ws sign f = dfinv m j0 w16 w24 b96 ev ws sign f.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.

Definition inring (a z i : Z) : Prop := ((i - a) mod 2048 < (z - a) mod 2048)%Z.
#[using="Type"] Lemma land2047 : forall v, Z.land v 2047 = (v mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. change 2047%Z with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma landW_mod2048 : forall v, ((Z.land v 18446744073709551615) mod 2048 = v mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. rewrite land_W64. apply Z.mod_mod_divide. exists (2^53)%Z. reflexivity. Qed.

#[using="Type"] Lemma inring_plus : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> (d <= (z - a) mod 2048)%Z -> Z.land (a + d) 2047 <> z ->
inring a z (Z.land (a + d) 2047) /\ (d + 1 <= (z - a) mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear.
intros a z d Hz Hd Hle Hne. rewrite land2047 in *. unfold inring.
rewrite Zminus_mod_idemp_l. replace (a + d - a)%Z with d by lia. rewrite (Z.mod_small d 2048) by lia.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)).
assert ((z - a) mod 2048 <> d)%Z; [|lia].
intros Ed. apply Hne. rewrite <- (Z.mod_small z 2048) by lia.
rewrite <- Ed. rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_hit : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> Z.land (a + d) 2047 = z -> ((z - a) mod 2048 = d)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear.
intros a z d Hz Hd E. rewrite land2047 in E. rewrite <- E. rewrite Zminus_mod_idemp_l.
replace (a + d - a)%Z with d by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma inring_grow : forall a z i, (0 <= z)%Z -> ((z - a) mod 2048 < 2047)%Z ->
inring a (z + 1) i <-> (inring a z i \/ (i - a) mod 2048 = (z - a) mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear.
intros a z i Hz Hlt. unfold inring.
replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)). pose proof (Z.mod_pos_bound (i - a) 2048 ltac:(lia)).
rewrite (Z.mod_small ((z - a) mod 2048 + 1)) by lia. lia.
Qed.
#[using="Type"] Lemma mod_eq_idx : forall a z i, (0 <= z < 2048)%Z -> (0 <= i < 2048)%Z -> ((i - a) mod 2048 = (z - a) mod 2048)%Z -> i = z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear.
intros a z i Hz Hi E.
rewrite <- (Z.mod_small i 2048), <- (Z.mod_small z 2048) by lia.
transitivity (((i - a) mod 2048 + a) mod 2048)%Z. { rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite E. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_mod : forall a z i, inring a (z mod 2048) i <-> inring a z i.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. unfold inring. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
#[using="Type"] Lemma xrel_iff : forall ws x (P Q : Z -> Prop), (forall i, (0 <= i < 2048)%Z -> Q i -> P i) -> xrel ws x P -> xrel ws x Q.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros ws x P Q HPQ (L1 & L2 & R). split; [exact L1|]. split; [exact L2|]. intros i Hi Hq. apply R; [exact Hi | apply HPQ; [exact Hi | exact Hq]]. Qed.

Definition zone (h w : bool) (a z : Z) (i : Z) : Prop := inring a z i \/ (h = true /\ (z <= i)%Z) \/ (w = true /\ (a <= i)%Z).
#[using="Type"] Lemma zone_in : forall h w a z i, inring a z i -> zone h w a z i.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. left. assumption. Qed.
#[using="Type"] Lemma xrel_window : forall ws x h w a z, xrel ws x (zone h w a z) -> xrel ws x (inring a z).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros until z. apply xrel_iff. intros i _ Hi. left. exact Hi. Qed.

Definition X31 (x : list Z) : Prop := forall i, (0 <= znth x i < 2^31)%Z.

Definition S_F3 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
fin_K3 1024 Y FR BI e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x14b0)) fct None m (seg_rom segs)).

#[using="Type"] Lemma f128_ge_range : forall a b, (-1 <= f128_ge a b <= 1)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros a b. unfold f128_ge.
repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
all: try (unfold nez64, b2z; destruct (negb _); cbn; lia).
Qed.

#[using="extenddftf2_spec"] Lemma extenddftf2_callF : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (D : Z),
mem_inv segs m -> bv_unsigned (reg_get F' 10) = D ->
evt segs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_d D) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 (e_extenddftf2 + 0x0)) fc' None m (seg_rom segs)).
Proof. clear - extenddftf2_spec segs e_extenddftf2 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - extenddftf2_spec segs e_extenddftf2. intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite HD in P. exact P.
Qed.

Definition S_F2 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K2 sign 1024 a z x 4 bits' Y FR BI e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1388)) fct None m (seg_rom segs)).

#[using="floatsitf_spec"] Lemma floatsitf_callsg : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (sg : Z),
mem_inv segs m -> (sg = 1 \/ sg = -1)%Z ->
evt segs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_i32 sg) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 sg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 (e_floatsitf + 0x0)) fc' None m (seg_rom segs)).
Proof. clear - floatsitf_spec segs e_floatsitf ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - floatsitf_spec segs e_floatsitf. intros until sg. intros MI [-> | ->].
- apply floatsitf_callp; [exact MI | lia].
- replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
apply floatsitf_callv; [exact MI | lia | rewrite sext32_eq; reflexivity].
Qed.

Definition S_F1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y e2 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K1 53 (-1074) sign 1024 zero0 a z x 4 Y e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x129c)) fct None m (seg_rom segs)).

#[using="Type"] Lemma lxor_sign_small : forall e, (-2^62 <= e < 2^62)%Z ->
Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 = (e + 2^63)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros e He. rewrite land_W64. change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma clamp0_idiom : forall v, (-2^62 <= v < 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land v 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land v 18446744073709551615) = (if v <? 0 then 0 else v)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros v Hv. rewrite lxor_sign_small by lia.
destruct (Z.ltb_spec 9223372036854775808 (v + 2^63)); destruct (Z.ltb_spec v 0); try lia; cbn [Z.b2z].
- change (Z.land (0 - 1) 18446744073709551615)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite land_W64, Z.mod_mod by lia. apply Z.mod_small. lia.
- change (Z.land (0 - 0) 18446744073709551615)%Z with 0%Z. apply Z.land_0_l.
- assert (E : v = 0%Z) by lia. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma cb44_merge : forall m A pre (bs : list byte) (w : word),
rw_cells segs m A (pre ++ [CB 4 bs; C4 w]) -> rw_cells segs m A (pre ++ [CB 8 (bs ++ le4 w)]).
Proof. clear - segs ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear - segs. intros m A pre bs w [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [|exact I]. cbn -[le4]. rewrite length_app, H2, length_le4. reflexivity.
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite <- app_assoc, app_nil_r in *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Definition C1E9HI : Z := 0x401cdcd650000000.

Definition ainv (ws : list word) (x : list Z) (h w : bool) (a z i : Z) : Prop :=
xrel ws x (zone h w a z) /\ X31 x /\ (0 <= z < 2048)%Z /\ (h = false -> z + (4 - i) <= 2052)%Z /\ (i <= (z - a) mod 2048)%Z /\ (w = false -> a <= 60)%Z.

Definition S_A69C : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 3 ->
df_asm_loop f a (mkAS 3 Y z x) = Some sres -> (2 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1238)) fct None m (seg_rom segs)).

Definition S_A62C : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 2 ->
df_asm_loop f a (mkAS 2 Y z x) = Some sres -> (3 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) (Z_to_bv 64 XA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x11c8)) fct None m (seg_rom segs)).

Definition S_A5C4 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 ->
df_asm_loop f a (mkAS 1 Y z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1160)) fct None m (seg_rom segs)).

Definition fin_K0 (sign a z : Z) (x : list Z) (e2 : Z) : option Z := df_final a z x e2 53 (-1074) sign 1024 zero0 zero0.

Definition S_A568 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 xa : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a <> z -> xa = znth x a ->
fin_K0 sign a z x e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 xa) x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1104)) fct None m (seg_rom segs)).

Definition S_A534 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 S1 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a = z -> S1 = (4 * ((z + 1) mod 2048))%Z ->
fin_K0 sign a z x e2 = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 ((z + 1) mod 2048)) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x10d0)) fct None m (seg_rom segs)).

Definition SN324 (fo : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xec0)) fct None m (seg_rom segs)).
Definition S_N324 : Prop := forall fo, SN324 fo.

Definition S_N2D4 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xe70)) fct None m (seg_rom segs)).

Definition up_K (sign rp a z e2 : Z) (x : list Z) : option Z :=
match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
| None => None
| Some s' => fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s')
end.
Definition MAGIC : Z := 19342813113834067.

Definition S_U1A8 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd44)) fct None m (seg_rom segs)).

#[using="Type"] Lemma df_dn_loop_step : forall n s, df_dn_loop (S n) s = match df_dn_body s with None => None | Some (inl s') => df_dn_loop n s' | Some (inr s') => Some s' end.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_dni_loop_step : forall n a z x i, df_dni_loop (S n) a z x i =
if (i <? LD_B1B_DIG)%Z then match df_dni_body a z x i with inl i' => df_dni_loop n a z x i' | inr i' => Some i' end else Some i.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_dnk_loop_step : forall n z sh s, df_dnk_loop (S n) z sh s = if negb (dk_k s =? z)%Z then df_dnk_loop n z sh (df_dnk_body z sh s) else Some s.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma dn_carry_bound : forall sh tmp, (sh = 1 \/ sh = 9)%Z -> (0 <= tmp <= 2^sh - 1)%Z -> (0 <= Z.shiftr 1000000000 sh * tmp < 2^30)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros sh tmp [-> | ->] H; [change (Z.shiftr 1000000000 1) with 500000000%Z | change (Z.shiftr 1000000000 9) with 1953125%Z]; cbn in H; lia. Qed.
#[using="Type"] Lemma shr_half : forall t sh, (0 <= t)%Z -> (1 <= sh)%Z -> (0 <= Z.shiftr t sh <= t / 2)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros t sh Ht Hsh. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_compat_l; [lia|]. split; [lia|]. change 2%Z with (2^1)%Z at 1. apply Z.pow_le_mono_r; lia.
Qed.
#[using="Type"] Lemma lor_lxor_zero : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z ->
Z.lor (Z.lxor k a) v = 0%Z <-> (k = a /\ v = 0%Z).
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros k a v Hk Ha Hv. split.
- intros H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2]. split; [|exact H2]. apply Z.lxor_eq_0_iff. exact H1.
- intros [-> ->]. rewrite Z.lxor_nilpotent. reflexivity.
Qed.
#[using="Type"] Lemma lor_lxor_nonneg : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z -> (0 <= Z.lor (Z.lxor k a) v)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. apply Z.lor_nonneg. split; [apply Z.lxor_nonneg; lia | lia]. Qed.
#[using="Type"] Lemma rp_upd : forall rp (c : bool),
Z_to_bv 64 (rp + Z.land (Z.land (Z.b2z c + -1) 18446744073709551615) 18446744073709551607) = Z_to_bv 64 (if c then rp else rp - 9)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros rp [|].
- change (Z.land (Z.land (Z.b2z true + -1) 18446744073709551615) 18446744073709551607) with 0%Z. rewrite Z.add_0_r. reflexivity.
- change (Z.land (Z.land (Z.b2z false + -1) 18446744073709551615) 18446744073709551607) with 18446744073709551607%Z.
apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma dn_az_none : forall fo rp z e2 x i0, (0 <= z < 2048)%Z -> rp <> 36%Z -> df_dn_loop fo (mkDS rp z z e2 x i0) = None.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. induction fo as [|fo IH]; intros rp z e2 x i0 Hz Hrp; [reflexivity|].
rewrite df_dn_loop_step. unfold df_dn_body. cbn [ds_a ds_z ds_x ds_rp ds_e2].
change (df_dni_loop 6 z z x 0) with (if (0 <? LD_B1B_DIG)%Z then match df_dni_body z z x 0 with inl i' => df_dni_loop 5 z z x i' | inr i' => Some i' end else Some 0%Z).
change (0 <? LD_B1B_DIG)%Z with true. unfold df_dni_body. rewrite Z.add_0_r. change MASK with 2047%Z. rewrite land2047, Z.mod_small, Z.eqb_refl by lia. cbn [orb].
change LD_B1B_DIG with 4%Z. change (4 =? 4)%Z with true. replace (rp =? 9 * 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
cbv zeta. unfold FUEL_RING. rewrite df_dnk_loop_step. cbn [dk_k]. rewrite Z.eqb_refl. cbn [negb nz Z.eqb].
apply IH; assumption.
Qed.

Definition S_NK : Prop := forall (fi : nat) m (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x20 x22 x24 x25 x26 x27 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a i rp z sh e2 B : Z) (s1 : st_dnk),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> ((k - a) mod 2048 <= (z - a) mod 2048)%Z -> k <> z ->
(0 <= carry < 2^30)%Z -> (sh = 1 \/ sh = 9)%Z -> (B + 9 * Z.of_nat fi <= rp <= 560)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^27 <= B)%Z -> (-2^21 <= e2 <= 2^21)%Z ->
df_dnk_loop fi z sh (mkDK k carry a i rp x) = Some s1 ->
(forall m' ws' b96' (x17' x28' x29' x30' x31' : word) (w' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' (dk_x s1) (zone h w' (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> (B <= dk_rp s1 <= 560)%Z -> (w' = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> dk_k s1 = z ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17'
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 (base + 0x1020)) fct None m' (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 carry) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xfec)) fct None m (seg_rom segs)).

Definition S_N484 : Prop := forall (fo : nat), SN324 fo ->
forall (s1 : st_dnk) m (x1 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (h w : bool) (rp z e2 Z0 S1 A6 sh : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws (dk_x s1) (zone h w (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> dk_k s1 = z -> (sh = 1 \/ sh = 9)%Z ->
(0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (rp - 18450 <= dk_rp s1 <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
(let 'mkDK _ carry a1 i rp1 xx := s1 in
let '(z', x') := if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx) in
df_dn_loop fo (mkDS rp1 a1 z' (e2 + sh) x' i) = Some s') ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 (e2 + sh)) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1020)) fct None m (seg_rom segs)).

Definition S_N3E8 : Prop := forall (fo : nat), SN324 fo ->
forall (iq : Z) m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z -> a <> z ->
match
match df_dnk_loop FUEL_RING z (if 45 <? rp then 9%Z else 1%Z) (mkDK a 0 a iq rp x) with
| Some (mkDK _ carry a1 i rp1 xx) =>
let '(z', x') := (if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx)) in
Some (inl (mkDS rp1 a1 z' (e2 + (if 45 <? rp then 9%Z else 1%Z)) x' i))
| None => None
end
with
| Some (inl s'') => df_dn_loop fo s''
| Some (inr s'') => Some s''
| None => None
end = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xf84)) fct None m (seg_rom segs)).

#[using="Type"] Lemma df_up_loop_step : forall n s, df_up_loop (S n) s = if df_up_cond s then match df_up_body s with None => None | Some s' => df_up_loop n s' end else Some s.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_upk_loop_step : forall n a s, df_upk_loop (S n) a s = match df_upk_body a s with inl s' => df_upk_loop n a s' | inr s' => Some s' end.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma mod_add2047 : forall u, ((u + 2047) mod 2048 = (u - 1) mod 2048)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros u. rewrite <- (Z.mod_add (u - 1) 1 2048) by lia. f_equal. lia. Qed.

#[using="Type"] Lemma magic_div_1e9 : forall tmp, (0 <= tmp < 2^61)%Z ->
(Z.shiftr ((Z.shiftr tmp 9 * MAGIC) / 2^64) 11 = tmp / 1000000000)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros tmp Ht. unfold MAGIC. rewrite !Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by lia. change (2^64 * 2^11)%Z with (2^75)%Z.
replace (tmp / 1000000000)%Z with ((tmp / 2^9) / 1953125)%Z by (rewrite Z.div_div by lia; f_equal).
set (u := (tmp / 2^9)%Z). assert (Hu : (0 <= u < 2^52)%Z) by (subst u; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody u. clear Ht tmp. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma magic_div_1e9_reg : forall tmp, (0 <= tmp < 2^61)%Z ->
Z.shiftr (Z.land (Z.shiftr (Z.shiftr tmp 9 * Z.land MAGIC 18446744073709551615) 64) 18446744073709551615) 11 = (tmp / 1000000000)%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac].
clear. intros tmp Ht. change (Z.land MAGIC 18446744073709551615) with MAGIC.
assert (R1 : (0 <= Z.shiftr tmp 9 < 2^52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (R2 : (0 <= Z.shiftr (Z.shiftr tmp 9 * MAGIC) 64 < 2^64)%Z).
{ unfold MAGIC. rewrite (Z.shiftr_div_pow2 _ 64) by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. nia. }
rewrite land_W64, (Z.mod_small _ _ R2). rewrite (Z.shiftr_div_pow2 _ 64) by lia. apply magic_div_1e9. exact Ht.
Qed.
#[using="Type"] Lemma u32_id : forall v, (0 <= v < 2^32)%Z -> u32 v = v.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. unfold u32. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma inring_front : forall a z i, (0 <= a < 2048)%Z -> (0 <= i < 2048)%Z -> (0 <= z < 2048)%Z ->
inring ((a - 1) mod 2048) z i -> i <> ((a - 1) mod 2048)%Z -> z <> ((a - 1) mod 2048)%Z -> inring a z i.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros a z i Ha Hi Hz H Hne Hzne. unfold inring in *. Z.div_mod_to_equations. nia. Qed.

Definition S_UK : Prop := forall (n : nat) m (x1 x5 x6 x8 x9 x11 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a z : Z) (s1 : st_upk),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> inring a z k ->
(0 <= carry < 2^31)%Z ->
df_upk_loop n a (mkUK k carry z x) = Some s1 ->
(forall m' ws' (x7' x18' x29' x30' x31' : word) (h' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (uk_x s1) (zone h' w a (uk_z s1)) -> X31 (uk_x s1) ->
uk_k s1 = a -> (0 <= uk_carry s1 < 2^31)%Z -> (0 <= uk_z s1 < 2048)%Z -> (h' = false -> h = false /\ uk_z s1 <= z)%Z -> a <> uk_z s1 ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 (uk_z s1)) x7' x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 (uk_carry s1)) x17
x18' (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 ((uk_z s1 - 1) mod 2048)) x29' x30' x31')
Ft (Z_to_bv 64 (base + 0xd54)) fct None m' (seg_rom segs))) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd88)) fct None m (seg_rom segs)).

Definition SU1C4 (fo : nat) : Prop := forall m (x1 x6 x7 x8 x9 x16 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt segs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xd60)) fct None m (seg_rom segs)).
Definition S_U1C4 : Prop := forall fo, SU1C4 fo.

Definition S_T : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (-2^15 <= rp <= 537)%Z ->
dfK_tz 53 (-1074) sign fR rp kz x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xbc8)) fct None m (seg_rom segs)).

Definition S_DD0 : Prop := forall m (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x96c)) fct None m (seg_rom segs)).

Definition S_DD24 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X u : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(0 <= u < 2^31)%Z -> yR = f128_mul X (f128_of_u32 u) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8c0)) fct None m (seg_rom segs)).

Definition S_M : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp lnz kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= rp <= 537)%Z ->
dfK_mid 53 (-1074) sign fR rp lnz kz x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x9f8)) fct None m (seg_rom segs)).

Definition digz (k j : Z) (i : Z) : Prop := (i < k)%Z \/ i = 0%Z \/ (i = k /\ j <> 0%Z).

Definition S_P : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign k c (x : list Z) (lrp lnz j kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= lrp <= 537)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) ->
dfK_pad 53 (-1074) sign fR lrp lnz j kz x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x97c)) fct None m (seg_rom segs)).

Definition S_R : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign k c (x : list Z) (lrp dc lnz j kz : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> (0 <= dc < 2^31)%Z -> (0 <= lnz < 2^31)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) -> (-2^62 <= lrp < 2^62)%Z ->
(znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
dfK_rng 53 (-1074) sign fR lrp dc lnz j kz x = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x880)) fct None m (seg_rom segs)).

Definition dig_facts (ws : list word) (x : list Z) (j kz dc lnz : Z) : Prop :=
xrel ws x (digz kz j) /\ X31 x /\
(0 <= j <= 8)%Z /\ (0 <= kz <= 2045)%Z /\ (0 <= dc < 2^31)%Z /\ (0 <= lnz < 2^31)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\
(j <> 0%Z -> znth x kz < 10 ^ j)%Z /\ (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\ (kz = 2045%Z -> j = 0%Z).

Definition S_C38 : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (0 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0) else dfK_rng 53 (-1074) sign f lrp dc lnz j kz x) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x7d4)) fct None m (seg_rom segs)).

Definition S_C2C : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> sh_shlim_neg f = false ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 (sh_unget f), f128_of_i32 0) else dfK_rng 53 (-1074) sign (sh_unget f) lrp dc lnz j kz x) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x7c8)) fct None m (seg_rom segs)).

Definition S_E : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (- 2^31 <= lrp < 2^31)%Z ->
dfK_exp fuelc 53 (-1074) sign pok (mkDL f c j kz lrp dc lnz gotdig gotrad x) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x650)) fct None m (seg_rom segs)).

Definition digI (ws : list word) (x : list Z) (f : shfile) (c j k lrp dc lnz gotdig gotrad : Z) : Prop :=
xrel ws x (digz k j) /\ X31 x /\ (0 <= j <= 8)%Z /\ (0 <= k)%Z /\ (9 * k + j <= dc)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (c <> (-1)%Z -> dc + 1 <= sh_rpos f)%Z /\
(0 <= lnz <= dc)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\ (j <> 0%Z -> znth x k < 10 ^ j)%Z /\ (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\
(- 2^31 <= lrp < 2^31)%Z /\ (0 <= gotdig <= 1)%Z /\ (0 <= gotrad <= 1)%Z /\
(k <= 2045)%Z /\ (k = 2045%Z -> j = 0%Z).

Definition SDn (n : nat) : Prop := forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
digI ws x f c j k lrp dc lnz gotdig gotrad ->
(isdigitc c || (c =? 46))%Z = true ->
df_dig_loop n (mkDL f c j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) (Z_to_bv 64 (Z.b2z (c =? 46)%Z)) x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x708)) fct None m (seg_rom segs)).
Definition S_D : Prop := forall n, SDn n.

Definition winv (m : word -> option byte) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word)
(ws : list word) (f : shfile) : Prop :=
finv m /\ framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m
/\ u32arr segs m XA ws /\ length ws = 2048%nat /\ rw_cells segs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma winv_dfinvG : forall m j0 w16 w24 w80 b96 ev ws sign f,
winv m j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f
= dfinvG m j0 w16 w24 w80 b96 ev ws sign f.
Proof. clear - ssp_guard ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.

Definition X0 : list Z := zupd (zrepeat 0 KMAX) 0 0.

Definition fch (c : Z) : Prop := is_numch c = true \/ c = 0%Z \/ c = (-1)%Z.

Definition S_B0C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
(isdigitc c || (c =? 46))%Z = true ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x6a8)) fct None m (seg_rom segs)).

Definition S_A9C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x638)) fct None m (seg_rom segs)).

Definition S_A44 : Prop := forall m (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig : Z),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> c <> 48%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig 1 X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x5e0)) fct None m (seg_rom segs)).

#[using="Type"] Lemma df_dig_loop_step : forall n s, df_dig_loop (S n) s = if df_dig_cond s then match df_dig_body s with inl s' => df_dig_loop n s' | inr s' => Some s' end else Some s.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. reflexivity. Qed.
#[using="Type"] Lemma df_rz_loop_step : forall n g l c f, df_rz_loop (S n) (g, l, c, f) =
(if c =? 48 then df_rz_loop n (1, l - 1, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. cbn [df_rz_loop df_rz_body]. destruct (sh_getc f). reflexivity. Qed.
#[using="Type"] Lemma df_lz_loop_step : forall n g c f, df_lz_loop (S n) (g, c, f) =
(if c =? 48 then df_lz_loop n (1, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f))%Z.
Proof. clear - ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR HM Hpok ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM. first [clear HM | gw_hide HM | idtac]; first [clear Hpok | gw_hide Hpok | idtac]; first [clear ST0 | gw_hide ST0 | idtac]; first [clear BYT | gw_hide BYT | idtac]; first [clear Hp | gw_hide Hp | idtac]; first [clear Hnul | gw_hide Hnul | idtac]; first [clear Hnum | gw_hide Hnum | idtac]; first [clear HP30 | gw_hide HP30 | idtac]; first [clear T0 | gw_hide T0 | idtac]; first [clear T1 | gw_hide T1 | idtac]; first [clear SEP | gw_hide SEP | idtac]; first [clear SE_T | gw_hide SE_T | idtac]; first [clear SPLO | gw_hide SPLO | idtac]; first [clear SPF | gw_hide SPF | idtac]; first [clear SPF2 | gw_hide SPF2 | idtac]; first [clear SPT | gw_hide SPT | idtac]; first [clear SG1 | gw_hide SG1 | idtac]; first [clear SG2 | gw_hide SG2 | idtac]; first [clear SG3 | gw_hide SG3 | idtac]; first [clear Q1 | gw_hide Q1 | idtac]; first [clear FRM | gw_hide FRM | idtac]. clear. intros. cbn [df_lz_loop df_lz_body]. destruct (sh_getc f). reflexivity. Qed.

Definition SRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (lrp g : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(1 - sh_rpos f <= lrp <= 0)%Z ->
df_rz_loop n (g, lrp, 48, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x5bc)) fct None m (seg_rom segs)).
Definition S_RZ : Prop := forall n, SRZn n.

Definition S_9EC : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (gotdig : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= gotdig <= 1)%Z ->
df_rz_loop fuelc (gotdig, 0, c, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 gotdig) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x588)) fct None m (seg_rom segs)).

Definition S_A64 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 1 0 X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x600)) fct None m (seg_rom segs)).

Definition S_7F4 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 0 0 X0) = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x390)) fct None m (seg_rom segs)).

Definition S_9C8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
dfK_rz fuelc 53 (-1074) sign pok 1 c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x564)) fct None m (seg_rom segs)).

Definition SLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (g : Z) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (g, 48, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x548)) fct None m (seg_rom segs)).
Definition S_LZ : Prop := forall n, SLZn n.

Definition S_990 : Prop := forall (n : nat) m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
df_lz_loop n (1, c, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x52c)) fct None m (seg_rom segs)).

Definition S_848 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
decfloat fuelc (sh_unget f) 48 53 (-1074) sign pok = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x3e4)) fct None m (seg_rom segs)).

Definition S_6F8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
decfloat fuelc f c 53 (-1074) sign pok = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x294)) fct None m (seg_rom segs)).

Definition FS_tail (sign c : Z) (f : shfile) : option (shfile * Z) :=
if (c =? 48)%Z then
let '(c2, f2) := sh_getc f in
if (Z.lor c2 32 =? 120)%Z then None else decfloat fuelc (sh_unget f2) 48 53 (-1074) sign pok
else decfloat fuelc f c 53 (-1074) sign pok.

Definition S_618 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail sign c f = Some (fR, yR) ->
evt segs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1b4)) fct None m (seg_rom segs)).
End Floatscan.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 QqdR QYTG G.T_shp G.T_pe Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Qfw3_c1.Mq1.
Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import Q91D.Mq3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Qbz7.
Import Q8l1.Mq1.
Import Q5m9.Mq0.
Import QROt.Mq1.
Import Q8l1.Mq4.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition vfprintf_code (w_10 w_11 w_30 w_54 w_93 w_107 : Z) : list Z :=
[0xe9010113; 0x16113423; 0x16813023; 0x14913c23; 0x15213823; 0x15313423; 0x15413023; 0x13513c23; 0x00058493; 0x00050413; w_10; w_11; 0x00093503; 0x12a13823; 0x00c13423; 0x12013423; 0x10013423; 0x10013823; 0x10013c23; 0x12013023; 0x00c13023; 0x00010613; 0x06010693; 0x10810713; 0x00000513; 0x14c000ef; 0x00054e63; 0x08c42503; 0x00054e63; 0x00040513; w_30; 0x00153993; 0x0100006f; 0xfff00513; 0x0f40006f; 0x00100993; 0x00042a83; 0x06043503; 0xfdfaf593; 0x00b42023; 0x00050a63; 0x02043503; 0x00000a13; 0x04051263; 0x0240006f; 0x05843a03; 0x01010513; 0x02043023; 0x02043423; 0x02043c23; 0x04a43c23; 0x05000513; 0x06a43023; 0x00040513; w_54; 0x00050a63; 0xfff00493; 0x020afa93; 0x020a1663; 0x0600006f; 0x00010613; 0x06010693; 0x10810713; 0x00040513; 0x00048593; 0x0ac000ef; 0x00050493; 0x020afa93; 0x020a0e63; 0x04843683; 0x00040513; 0x00000593; 0x00000613; 0x000680e7; 0x02843503; 0x02043023; 0x02043423; 0x02043c23; 0x05443c23; 0x00a03533; 0xfff5051b; 0x009564b3; 0x06043023; 0x00042503; 0x02057593; 0x01556633; 0x0015b513; 0xfff5051b; 0x00956533; 0x00c42023; 0x00099a63; 0x00050493; 0x00040513; w_93; 0x00048513; 0x00093583; 0x13013603; 0x02c59463; 0x16813083; 0x16013403; 0x15813483; 0x15013903; 0x14813983; 0x14013a03; 0x13813a83; 0x17010113; 0x00008067; w_107]%Z.

Definition towrite_code : list Z :=
[0x08852603; 0x00056583; 0xfff60693; 0x00c6e633; 0x0085f693; 0x08c52423; 0x02069663; 0x05853603; 0x06053683; 0x02c53c23; 0x00d606b3; 0x00053423; 0x00053823; 0x02d53023; 0x02c53423; 0x00000513; 0x00008067; 0x0205e593; 0x00b52023; 0xfff00513; 0x00008067]%Z.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_10 w_11 w_30 w_54 w_93 w_107 : Z).
Variables (hi_10 : bv 20).
Variables (lo_11 : bv 12).
Variables (joff_54 : bv 21).
Variables (got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_194bc e_194c8 e_197bc e_fwritex e_towrite e_sn_write e_memcpy e_memset e_2596c : Z).
Hypothesis CODE : code_at segs base (vfprintf_code w_10 w_11 w_30 w_54 w_93 w_107).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 432.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 10 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Load SZ8 true 18 10 lo_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_54 : decode_any (Z_to_bv 32 w_54) = Some (Jal 1 joff_54, 4%Z).
Hypothesis E_54 : is_ecall (Z_to_bv 32 w_54) = false.
Hypothesis ANCH_11 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_11)%Z got_ssp.
Hypothesis LINK_54 : gw_anch (base + 216 + bv_signed joff_54)%Z (e_towrite + 0)%Z.
Hypothesis CODE_e_towrite : code_at segs e_towrite towrite_code.
Hypothesis RNG_STATIC_SPLIT : gw_br STATIC_SPLIT 8.
Hypothesis LAY_lo_STATIC_SPLIT : gw_le 65536 STATIC_SPLIT.
Hypothesis AL_STATIC_SPLIT : gw_al STATIC_SPLIT 8.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis LAY_lo_got_ssp : gw_le 65536 got_ssp.
Hypothesis AL_got_ssp : gw_al got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis LAY_lo_ssp_guard : gw_le 65536 ssp_guard.
Hypothesis AL_ssp_guard : gw_al ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis AL_GLOBALS_TOP : gw_al GLOBALS_TOP 8.
Hypothesis LAY_STATIC_SPLIT_got_ssp : gw_le (STATIC_SPLIT + 8) got_ssp.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis AL_e_sn_write_b4 : gw_b4 e_sn_write.
Hypothesis RNG_e_sn_write_code : gw_br e_sn_write 220.

Local Definition gw_tbl_0 := tt.

Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@QZxv.Mqi.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqh.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq7.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqg.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqf.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqe.arg_ok segs) arg_ok (gw_ent (@QZxv.Mqj.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq9.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq8.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq5.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq4.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq0.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq2.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq3.arg_ok segs) arg_ok (gw_ent (@QEN3.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq1.arg_ok segs) arg_ok (gw_ent (@QZxv.Mq0.arg_ok segs) arg_ok (gw_ent (@QK0e.arg_ok segs) arg_ok (gw_ent (@QEN3.arg_ok segs) arg_ok (gw_ent (@Q5m9.Mq0.arg_ok segs) arg_ok (gw_ent (@QROt.Mq0.arg_ok segs) arg_ok (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_0)))))))))))))))))))))).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QZxv.Mqi.args_ok segs) args_ok (gw_ent (@QZxv.Mqh.args_ok segs) args_ok (gw_ent (@QEN3.Mq7.args_ok segs) args_ok (gw_ent (@QZxv.Mqg.args_ok segs) args_ok (gw_ent (@QZxv.Mqf.args_ok segs) args_ok (gw_ent (@QZxv.Mqe.args_ok segs) args_ok (gw_ent (@QZxv.Mqj.args_ok segs) args_ok (gw_ent (@QZxv.Mq9.args_ok segs) args_ok (gw_ent (@QZxv.Mq8.args_ok segs) args_ok (gw_ent (@QEN3.Mq5.args_ok segs) args_ok (gw_ent (@QEN3.Mq4.args_ok segs) args_ok (gw_ent (@QEN3.Mq0.args_ok segs) args_ok (gw_ent (@QZxv.Mq2.args_ok segs) args_ok (gw_ent (@QZxv.Mq3.args_ok segs) args_ok (gw_ent (@QEN3.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq1.args_ok segs) args_ok (gw_ent (@QZxv.Mq0.args_ok segs) args_ok (gw_ent (@QK0e.args_ok segs) args_ok (gw_ent (@QEN3.args_ok segs) args_ok (gw_ent (@Q5m9.Mq0.args_ok segs) args_ok (gw_ent (@QROt.Mq0.args_ok segs) args_ok (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_1)))))))))))))))))))))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@QZxv.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqc.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqk.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqb.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqd.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqi.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqh.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq7.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqg.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqf.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqe.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqj.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq9.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq5.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq4.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq8.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QK0e.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QZxv.Mqa.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QEN3.Mq6.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q5m9.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@QROt.Mq0.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_2))))))))))))))))))))))))))))))))))))).
Definition printf_core_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q5m9.Mq0.printf_core_post segs got_ssp ssp_guard) printf_core_post (gw_ent (@Q8l1.Mq1.printf_core_post segs got_ssp ssp_guard) printf_core_post gw_tbl_3)).
#[global] Arguments printf_core_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F AP%_Z_scope lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QZxv.Mqi.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqh.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq7.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqg.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqf.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqe.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mqj.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq9.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq8.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq5.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq4.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq2.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq3.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QZxv.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QK0e.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QEN3.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QROt.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q5m9.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@QROt.Mq0.fpcall_post segs got_ssp ssp_guard) fpcall_post (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_4))))))))))))))))))))))).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt := ltac:(let t := constr:(ltac:(gw_rebind (@Q8l1.Mq1.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_5))) in let t := gw_fold_pcs t base (432)%Z [0]%Z in exact t).
Local Definition gw_tbl_6 := (gw_ent (@QZxv.Mqi.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqh.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq7.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqg.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqf.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqe.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mqj.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq9.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq8.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq5.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq4.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq0.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq2.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq3.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.Mq1.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq1.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QZxv.Mq0.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QK0e.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QEN3.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QROt.Mq1.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q5m9.Mq0.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@QROt.Mq0.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt (gw_ent (@Q8l1.Mq1.fpcall_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_5))))))))))))))))))))))).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@QZxv.Mq6.va_area segs) va_area (gw_ent (@QZxv.Mq5.va_area segs) va_area (gw_ent (@QZxv.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqc.va_area segs) va_area (gw_ent (@QEN3.Mq3.va_area segs) va_area (gw_ent (@QZxv.Mqk.va_area segs) va_area (gw_ent (@QZxv.Mqb.va_area segs) va_area (gw_ent (@QZxv.Mqd.va_area segs) va_area (gw_ent (@QZxv.Mq4.va_area segs) va_area (gw_ent (@QZxv.Mqi.va_area segs) va_area (gw_ent (@QZxv.Mqh.va_area segs) va_area (gw_ent (@QEN3.Mq7.va_area segs) va_area (gw_ent (@QZxv.Mqg.va_area segs) va_area (gw_ent (@QZxv.Mqf.va_area segs) va_area (gw_ent (@QZxv.Mqe.va_area segs) va_area (gw_ent (@QZxv.Mqj.va_area segs) va_area (gw_ent (@QZxv.Mq9.va_area segs) va_area (gw_ent (@QZxv.Mq8.va_area segs) va_area (gw_ent (@QEN3.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq5.va_area segs) va_area (gw_ent (@QEN3.Mq4.va_area segs) va_area (gw_ent (@QEN3.Mq0.va_area segs) va_area (gw_ent (@QZxv.Mq2.va_area segs) va_area (gw_ent (@QEN3.Mq8.va_area segs) va_area (gw_ent (@QZxv.Mq3.va_area segs) va_area (gw_ent (@QEN3.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq1.va_area segs) va_area (gw_ent (@QZxv.Mq0.va_area segs) va_area (gw_ent (@QK0e.va_area segs) va_area (gw_ent (@QEN3.va_area segs) va_area (gw_ent (@QZxv.Mqa.va_area segs) va_area (gw_ent (@QEN3.Mq6.va_area segs) va_area (gw_ent (@QROt.Mq1.va_area segs) va_area (gw_ent (@Q5m9.Mq0.va_area segs) va_area (gw_ent (@QROt.Mq0.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_6))))))))))))))))))))))))))))))))))))).
Definition printf_core_stmt := ltac:(let t := constr:(ltac:(gw_rebind (@Q8l1.Mq1.printf_core_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_7))) in let t := gw_fold_pcs t base (432)%Z [0]%Z in exact t).
Local Definition gw_tbl_8 := (gw_ent (@Q5m9.Mq0.printf_core_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core_stmt (gw_ent (@Q8l1.Mq1.printf_core_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core_stmt gw_tbl_7)).
#[global] Arguments printf_core_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope OUTFP%_function_scope.
Definition printf_core1_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q5m9.Mq0.printf_core1_post segs got_ssp ssp_guard) printf_core1_post (gw_ent (@Q8l1.Mq1.printf_core1_post segs got_ssp ssp_guard) printf_core1_post gw_tbl_8)).
Definition printf_core1_stmt := ltac:(let t := constr:(ltac:(gw_rebind (@Q8l1.Mq1.printf_core1_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) constr:(gw_tbl_9))) in let t := gw_fold_pcs t base (432)%Z [0]%Z in exact t).
Local Definition gw_tbl_10 := (gw_ent (@Q5m9.Mq0.printf_core1_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core1_stmt (gw_ent (@Q8l1.Mq1.printf_core1_stmt segs (base + 432)%Z got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) printf_core1_stmt gw_tbl_9)).
Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@QZxv.Mq6.wfile segs) wfile (gw_ent (@QZxv.Mq5.wfile segs) wfile (gw_ent (@QZxv.Mq7.wfile segs) wfile (gw_ent (@QZxv.Mqc.wfile segs) wfile (gw_ent (@QEN3.Mq3.wfile segs) wfile (gw_ent (@QZxv.Mqk.wfile segs) wfile (gw_ent (@QZxv.Mqb.wfile segs) wfile (gw_ent (@QZxv.Mqd.wfile segs) wfile (gw_ent (@QZxv.Mq4.wfile segs) wfile (gw_ent (@QZxv.Mqi.wfile segs) wfile (gw_ent (@QZxv.Mqh.wfile segs) wfile (gw_ent (@QEN3.Mq7.wfile segs) wfile (gw_ent (@QZxv.Mqg.wfile segs) wfile (gw_ent (@QZxv.Mqf.wfile segs) wfile (gw_ent (@QZxv.Mqe.wfile segs) wfile (gw_ent (@QZxv.Mqj.wfile segs) wfile (gw_ent (@QZxv.Mq9.wfile segs) wfile (gw_ent (@QZxv.Mq8.wfile segs) wfile (gw_ent (@QEN3.Mq2.wfile segs) wfile (gw_ent (@QEN3.Mq5.wfile segs) wfile (gw_ent (@QEN3.Mq4.wfile segs) wfile (gw_ent (@QEN3.Mq0.wfile segs) wfile (gw_ent (@QZxv.Mq2.wfile segs) wfile (gw_ent (@QEN3.Mq8.wfile segs) wfile (gw_ent (@QZxv.Mq3.wfile segs) wfile (gw_ent (@QEN3.Mq1.wfile segs) wfile (gw_ent (@QZxv.Mq1.wfile segs) wfile (gw_ent (@QZxv.Mq0.wfile segs) wfile (gw_ent (@QK0e.wfile segs) wfile (gw_ent (@QEN3.wfile segs) wfile (gw_ent (@QZxv.Mqa.wfile segs) wfile (gw_ent (@QEN3.Mq6.wfile segs) wfile (gw_ent (@QROt.Mq1.wfile segs) wfile (gw_ent (@Q5m9.Mq0.wfile segs) wfile (gw_ent (@QROt.Mq0.wfile segs) wfile (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_10)))))))))))))))))))))))))))))))))))))).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@QZxv.Mq6.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq5.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq7.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqc.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqk.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqb.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqd.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq4.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqi.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqh.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq7.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqg.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqf.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqe.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqj.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq9.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq8.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq2.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq5.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq4.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq2.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq8.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq1.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq1.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QK0e.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QZxv.Mqa.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QEN3.Mq6.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QROt.Mq1.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q5m9.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@QROt.Mq0.sink_frame_stmt segs) sink_frame_stmt (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_11)))))))))))))))))))))))))))))))))))).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@QZxv.Mq6.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq5.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq7.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqc.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqk.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqb.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqd.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq4.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqi.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqh.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq7.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqg.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqf.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqe.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqj.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq9.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq8.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq2.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq5.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq4.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq2.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq8.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq1.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq1.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QK0e.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QZxv.Mqa.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QEN3.Mq6.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QROt.Mq1.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q5m9.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@QROt.Mq0.sink_flags_stmt segs) sink_flags_stmt (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_12)))))))))))))))))))))))))))))))))))).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_13)).
Local Definition gw_tbl_14 := (gw_ent (@QZxv.Mq6.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq5.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq7.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqc.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqk.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqb.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqd.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq4.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqi.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqh.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq7.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqg.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqf.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqe.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqj.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq9.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq8.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq2.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq5.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq4.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq2.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq8.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq1.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq1.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QK0e.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QZxv.Mqa.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QEN3.Mq6.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QROt.Mq1.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q5m9.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@QROt.Mq0.out_post segs got_ssp ssp_guard) out_post (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_13)))))))))))))))))))))))))))))))))))).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_14)).
Local Definition gw_tbl_15 := (gw_ent (@QZxv.Mq6.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq5.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq7.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqc.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqk.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqb.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqd.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq4.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqi.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqh.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq7.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqg.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqf.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqe.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqj.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq9.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq8.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq2.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq5.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq4.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq2.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq8.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QK0e.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QZxv.Mqa.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QEN3.Mq6.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QROt.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q5m9.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@QROt.Mq0.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_14)))))))))))))))))))))))))))))))))))).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition SINK_sn : ltac:(gw_rebind_ty (@Q8l1.Mq1.SINK_sn segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.SINK_sn segs) constr:(gw_tbl_15)).
Local Definition gw_tbl_16 := (gw_ent (@QROt.Mq1.SINK_sn segs) SINK_sn (gw_ent (@Q8l1.Mq1.SINK_sn segs) SINK_sn gw_tbl_15)).
Definition sn_write_post : ltac:(gw_rebind_ty (@Q8l1.Mq4.sn_write_post segs) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q8l1.Mq4.sn_write_post segs) constr:(gw_tbl_16)).
Local Definition gw_tbl_17 := (gw_ent (@Q8l1.Mq4.sn_write_post segs) sn_write_post gw_tbl_16).

Hypothesis printf_core_proof : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq0.gw_all) (@Q5m9.Mq0.printf_core_proof) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0; 176; 204; 212; 228; 236; 280; 296; 328; 332; 408; 444; 480; 552; 628; 784; 920; 980; 1096; 1224; 1284; 1304; 1320; 1340; 1352; 1432; 1504; 1744; 1800; 1864; 1888; 1928; 2204; 2220; 2276; 2300; 2324; 2380; 2468; 2596; 2624; 2760; 2892; 2920; 3204; 3548]%Z in exact T).
Hypothesis printf_core1_proof : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q5m9.Mq0.gw_all) (@Q5m9.Mq0.printf_core1_proof) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0; 176; 204; 212; 228; 236; 280; 296; 328; 332; 408; 444; 480; 552; 628; 784; 920; 980; 1096; 1224; 1284; 1304; 1320; 1340; 1352; 1432; 1504; 1744; 1800; 1864; 1888; 1928; 2204; 2220; 2276; 2300; 2324; 2380; 2468; 2596; 2624; 2760; 2892; 2920; 3204; 3548]%Z in exact T).

Hypothesis sn_sink_frame : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq1.gw_all) (@QROt.Mq1.sn_sink_frame) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0]%Z in exact T).
Hypothesis sn_sink_flags : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq1.gw_all) (@QROt.Mq1.sn_sink_flags) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0]%Z in exact T).
Hypothesis sn_topok : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq1.gw_all) (@QROt.Mq1.sn_topok) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0]%Z in exact T).
Hypothesis sn_out : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq1.gw_all) (@QROt.Mq1.sn_out) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0]%Z in exact T).
Hypothesis sn_fpcall : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QROt.Mq1.gw_all) (@QROt.Mq1.sn_fpcall) (base + 432)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in let T := gw_fold_pcs T base (432)%Z [0]%Z in exact T).

Hypothesis rw_CB_length : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq4.gw_all) (@Q8l1.Mq4.rw_CB_length) e_sn_write)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in exact T).
Hypothesis sn_write_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq4.gw_all) (@Q8l1.Mq4.sn_write_spec) e_sn_write)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_17))) in exact T).
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac unstash := unfold hide in *.
Notation mem := (word -> option byte).
Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
end.

Ltac fix_litstore :=
match goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
| _ => idtac
end.

Notation parg := G.T_printf.parg.

#[using="got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_towrite e_sn_write e_memcpy e_memset e_2596c CODE BASE4 BASER D_10 E_10 D_11 E_11 D_54 E_54 ANCH_11 LINK_54 CODE_e_towrite RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP AL_e_sn_write_b4 RNG_e_sn_write_code printf_core_proof printf_core1_proof sn_sink_frame sn_sink_flags sn_topok sn_out sn_fpcall rw_CB_length sn_write_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_10 w_11 w_30 w_54 w_93 w_107 hi_10 lo_11 joff_54 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_194bc e_194c8 e_197bc e_fwritex e_towrite e_sn_write e_memcpy e_memset e_2596c CODE BASE4 BASER D_10 E_10 D_11 E_11 D_54 E_54 ANCH_11 LINK_54 CODE_e_towrite RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT AL_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp AL_got_ssp RNG_ssp_guard LAY_lo_ssp_guard AL_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP AL_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP AL_e_sn_write_b4 RNG_e_sn_write_code printf_core_proof printf_core1_proof sn_sink_frame sn_sink_flags sn_topok sn_out sn_fpcall rw_CB_length sn_write_spec.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs_ m a bs ::= transport_chunks_fast segs_ m a bs.
Local Ltac footprint_after_store segs_ m a bs ::= footprint_after_store_fast segs_ m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs_ m m' MU WM ::= transport_after_call_fast segs_ m m' MU WM.
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
(try g_ret_pc) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells segs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv segs m ->
evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_towrite + 0x0)) fc None m (seg_rom segs)).

#[using="CODE_e_towrite"] Theorem towrite_g_proof : towrite_g_stmt.
Proof. clear - CODE_e_towrite.
unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
unfold gfile_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

#[using="Type"] Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d|li|lu]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
split; [|repeat (split; [first [assumption | lia]|]); exact D4].
eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
#[using="Type"] Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

#[using="Type"] Lemma rw_cells_unmerge : forall m A pre mid post,
rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
rw_cells segs m A (pre ++ mid ++ post).
Proof. clear - segs.
intros m A pre mid post [[Hwf Hb] Hw] WF.
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
split; [split|].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

#[using="Type"] Lemma rwc_eq : forall m A A' cs, rw_cells segs m A cs -> A = A' -> rw_cells segs m A' cs.
Proof. clear - segs. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

#[using="Type"] Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells segs m B [CB 0 []].
Proof. clear - segs.
intros m B H0 H1. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase (e_sn_write + 0x0) 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
[C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition VF_FRAME : Z := 368.

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk segs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells segs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ rw_cells segs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells segs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
rw_cells segs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells segs m (Fp + 148) (snfile_rest CK) ->
rw_cells segs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
rw_cells segs m D [CB dn junkd] ->
bytes_at segs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo_c1.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
stk segs m lo q -> (lo <= q - VF_FRAME - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv segs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
(q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D \/ (STATIC_SPLIT <= D /\ D + Z.of_nat dn <= got_ssp) \/ (got_ssp + 8 <= D /\ D + Z.of_nat dn <= ssp_guard) \/ (ssp_guard + 8 <= D /\ D + Z.of_nat dn <= GLOBALS_TOP)) ->
evt segs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).

#[using="w_10 w_11 w_30 w_54 w_93 w_107 hi_10 lo_11 joff_54 e_fwritex e_towrite CODE BASE4 BASER D_10 E_10 D_11 E_11 D_54 E_54 ANCH_11 LINK_54 CODE_e_towrite RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP AL_e_sn_write_b4 RNG_e_sn_write_code printf_core_proof printf_core1_proof sn_sink_frame sn_sink_flags sn_topok sn_out sn_fpcall rw_CB_length sn_write_spec"] Theorem vfprintf_sn_proof : vfprintf_sn_stmt.
Proof. clear - w_10 w_11 w_30 w_54 w_93 w_107 hi_10 lo_11 joff_54 e_fwritex e_towrite CODE BASE4 BASER D_10 E_10 D_11 E_11 D_54 E_54 ANCH_11 LINK_54 CODE_e_towrite RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP AL_e_sn_write_b4 RNG_e_sn_write_code printf_core_proof printf_core1_proof sn_sink_frame sn_sink_flags sn_topok sn_out sn_fpcall rw_CB_length sn_write_spec.
unfold vfprintf_sn_stmt. intros until o. cbv zeta.
intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 GD. gw_expose got_ssp; gw_expose ssp_guard.
gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold VF_FRAME, PC_DEPTH in *.
pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
destruct SSP as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard. idtac. idtac.
pose proof (wmono_refl segs m) as WM.
unfold snfile_head, gfile_cells in FH. unfold snfile_rest in FR.
carve_frame 368%nat ST.

pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
stash FH. stash FR. stash CKC. stash DST. stash BY. stash VAA.
do 12 zs. do 14 zs.
unstash.
lazymatch type of MUp with munch ?Wp ?ma ?mb =>
transport_after_call segs ma mb MUp WM;
assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z ma mb)
by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp]);
assert (MU1 : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp])
end.
clear MUp.

pose proof (gw_unhyp printf_core1_proof) as PC1. unfold printf_core1_stmt in PC1.
eapply evt_cut.
{ eapply PC1; rewrite ?unsigned_lit by lia; gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold PC_DEPTH, zlength;
[ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
| gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MUc & WMc & MIc & STc & SSPc).
rewrite !unsigned_lit in MUc, STc by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m' MUc WMc; clear MUc WMc; try clear MI end.
fix_ret.
clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard. idtac. idtac.

zs. if_lit. zs. zs. if_lit. zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in *. zs. zs. zs. zs. if_lit.
do 10 zs.
pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size csize Nat.add] in FB.

pose proof towrite_g_proof as TW. unfold towrite_g_stmt in TW.
eapply evt_cut.
{ eapply (TW _ _ _ _ _ _ _ _ _ (Z_to_bv 64 Fp)) with (flags := Z_to_bv 64 0) (rpos := 0) (rend := 0) (close := 0) (wend := 0) (wpos := 0) (wbase := 0)
(writefn := (e_sn_write + 0x0)) (seekfn := 0) (buf := bv_unsigned sp + -352) (bufsize := 80) (fd := 0) (mode := Z_to_bv 64 0) (lock := Z_to_bv 64 4294967295) (lbf := 4294967295);
rewrite ?unsigned_lit by lia; [ unfold gfile_cells; exact FH | reflexivity | lia | lia | lia | assumption ]. }
cbv beta. intros ms' P. clear TW.
destruct P as (x5' & x6' & x7' & c1 & c2 & c3 & c4 & c5 & c6 & c7 & x28' & x29' & x30' & x31' & mode' & m'' & -> & MUc & WMc & MIt & FH').
rewrite !unsigned_lit in MUc, FH' by lia. clear FH.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
fix_ret.
zs. if_lit. do 6 zs.

set (B := bv_unsigned sp + -352) in *.
unfold gfile_cells in FH'.
apply (rw_cells_merge segs _ _ [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in FH'.
apply (rw_cells_split_CB segs _ _ [] _ _ _ [1; 31]%nat) in FH'; [|reflexivity].
apply (rw_cells_merge segs _ _ [_; _; _; _]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 (e_sn_write + 0x0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)]) in FH'.
cbn [app mk_CB_cells cells_size csize Nat.add] in FH'.
match type of FH' with rw_cells _ _ _ (CB 1 ?b1 :: CB 31 ?b31 :: _ :: _ :: CB 96 ?b96 :: _) =>
let v1 := eval vm_compute in b1 in change b1 with v1 in FH'; set (j1 := b31) in FH'; set (j2 := b96) in FH' end.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
apply (rw_cells_split_CB segs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).

assert (SNK : SINK_sn Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368) m'' []).
{ exists jb. split; [|split; [exact FR | split; [reflexivity | split; [unfold zlength, SN_CAP; rewrite LJB; reflexivity | unfold SN_CAP; split; [lia | split; lia]]]]].
unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB. rewrite !Z.add_0_r.
split; [unfold FILE_cells; exact FH'|].
split. { apply (proj2 (rw_cells_app segs _ _ [CB 0 []] [CB 80 jb])). split; [apply rw_cells_CB0; lia|]. cbn [cells_size csize Nat.add]. rewrite Z.add_0_r. exact BUFc. }
split; [reflexivity|]. split; [vm_compute; discriminate|]. lia. }

assert (PCALL : forall Q ms, implM segs (printf_model OUT_sn OUTFP_sn fmt args) [] Q ms -> evt segs (Q r o) ms).
{ intros Q ms H. unfold implM in H. rewrite MODEL in H. exact H. }
pose proof (printf_core_proof (list Z) Fp B 80 _ _ OUT_sn OUTFP_sn
(sn_sink_frame Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_sink_flags Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
(sn_topok (bv_unsigned sp + -368))
(sn_out Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))) as PC2.
unfold printf_core_stmt in PC2.
eapply evt_cut.
{ apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); rewrite ?unsigned_lit by lia; gw_expose GLOBALS_TOP; gw_expose STATIC_SPLIT; unfold PC_DEPTH, TOPOK_sn, zlength;
[ exact SNK | exact BY | exact HF | reflexivity | exact APC | exact VAA | lia | | | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | lia | lia | lia
| gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells; split; [exact SSP1 | exact SSP2] | assumption | exact FRM | lia | lia | lia | lia | lia | lia | lia ].
-  cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia |].
exact MU1.
-
eapply Forall_impl; [|exact FPF]. intros [[[[y w] p] fl] t] FF. apply sn_fpcall. exact FF. }
cbv beta. intros ms' P. clear PC2 PCALL MODEL FPF AOK HF BY VAA P1.
unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (y5 & y6 & y7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & apv & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SNK3 & SSP3 & APC3 & Hr).
unfold INT_MAX in Hr.
unfold SR in MUc. cbn [app] in MUc.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
fix_ret.

destruct SNK3 as (junk3 & WF3 & FR3 & FRL3 & LEN3 & SEPB3 & T13 & T23).
destruct WF3 as (FC3 & BUF3 & FL3 & LBF3 & B03 & BHI3 & SEPfb3).
pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength, SN_CAP in LEN3.
unfold FILE_cells in FC3. subst j2.

lazymatch type of FC3 with rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; CB 96 _; ?c6] =>
pose proof (rw_cells_unmerge mm Fp [c1; c2; c3; c4]
[C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 (e_sn_write + 0x0)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)] [c6]) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
subst j1.
apply (rw_cells_merge segs _ _ [] [CB 1 _; CB 31 _]) in FC3. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC3.
match type of FC3 with rw_cells _ _ _ (CB 32 ?b :: _) => let v := eval vm_compute in b in change b with v in FC3 end.
lazymatch type of FC3 with rw_cells _ ?mm _ (CB 32 _ :: ?rest) =>
pose proof (rw_cells_unmerge mm Fp [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) as UM end.
cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
lazymatch type of UM with rw_cells _ _ _ (CB 32 ?b :: _) -> _ => let v := eval vm_compute in b in change b with v in UM end.
specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
zs. zs. zs. brf Kb; [exfalso; lia|].
zs. zs. zs. zs. zs.

apply (proj1 (rw_cells_app segs _ _ [_; _; _; _; _; _] _)) in FC3. destruct FC3 as [F0 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FC3. destruct FC3 as [F40 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FC3. destruct FC3 as [F48 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FC3. destruct FC3 as [F56 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app segs _ _ [_; _; _] _)) in FC3. destruct FC3 as [F64 FC3]. cbn [cells_size csize Nat.add app] in FC3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FC3. destruct FC3 as [F88 F96]. cbn [cells_size csize Nat.add app] in F96.
replace (Fp + Z.of_nat 40)%Z with (Fp + 40)%Z in F40 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8)%Z with (Fp + 48)%Z in F48 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 56)%Z in F56 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 64)%Z in F64 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24)%Z with (Fp + 88)%Z in F88 by lia.
replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8)%Z with (Fp + 96)%Z in F96 by lia.
unfold snfile_rest in FR3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FR3. destruct FR3 as [F148 FR3]. cbn [cells_size csize Nat.add app] in FR3.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in FR3. destruct FR3 as [F152 F160]. cbn [cells_size csize Nat.add app] in F160.
replace (Fp + 148 + Z.of_nat 4)%Z with (Fp + 152)%Z in F152 by lia.
replace (Fp + 148 + Z.of_nat 4 + Z.of_nat 8)%Z with (Fp + 160)%Z in F160 by lia.
pose proof (rw_cells_bytes_at' _ _ _ _ BUF3) as SRC3. cbn [cells_bytes cbytes app] in SRC3. rewrite app_nil_r in SRC3.
apply bytes_at_app in SRC3. destruct SRC3 as [SRC3 _].
replace (Z_to_bv 64 (B + Z.of_nat (length o))) with (Z_to_bv 64 (B + zlength o)) in F40 by reflexivity.
clear MU1. clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. gw_expose got_ssp; gw_expose ssp_guard.
change segs with segs in SSP1, SSP2, BUF3.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 64) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
replace (ret_pc (Z_to_bv 64 e_sn_write)) with (Z_to_bv 64 (e_sn_write + 0)%Z) by (rewrite <- (ret_pc_base e_sn_write 220 0 AL_e_sn_write_b4 RNG_e_sn_write_code eq_refl); rewrite Z.add_0_r; reflexivity).
eapply evt_cut.
{ eapply (gw_unhyp sn_write_spec) with (o := o) (B := B) (n := n) (D := D) (CK := CK) (dn := dn) (bufp := B) (Fp := Fp) (junk := junkd);
rewrite ?unsigned_lit by lia; unfold zlength;
[ reflexivity | reflexivity | exact F40 | exact F56 | exact F88 | exact F152 | | exact SRC3 | | exact ROOM | lia | lia | lia | exact ST4b | lia | assumption
| lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ].
all: lazymatch goal with |- rw_cells _ _ ?a _ => match goal with H : rw_cells _ _ a _ |- _ => exact H end end. }
cbv beta. intros ms' P.
unfold sn_write_post in P. rewrite !unsigned_lit in P by lia.
destruct P as (z5 & z6 & z7 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z28 & z29 & z30 & z31 & m4 & -> & MUc & WMc & MI4 & ST4b' & CK4 & DST4 & F40' & F56' & SRC4).
rewrite ?unsigned_lit in ST4b' by lia.
lazymatch type of MUc with munch _ ?mm _ => transport_after_call segs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
fix_ret.

zs. zs. zs. zs. zs.
zs. replace (0 <? B)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
zs. zs. rewrite ?Z.lor_0_l. zs.
zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. zs. zs. zs. zs. rewrite ?Z.lor_0_l. zs. zs. if_lit.
zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear - Kc w_10 w_11 w_30 w_54 w_93 w_107 hi_10 lo_11 joff_54 e_fwritex e_towrite CODE BASE4 BASER D_10 E_10 D_11 E_11 D_54 E_54 ANCH_11 LINK_54 CODE_e_towrite RNG_STATIC_SPLIT LAY_lo_STATIC_SPLIT RNG_got_ssp LAY_lo_got_ssp RNG_ssp_guard LAY_lo_ssp_guard RNG_GLOBALS_TOP LAY_STATIC_SPLIT_got_ssp LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP AL_e_sn_write_b4 RNG_e_sn_write_code printf_core_proof printf_core1_proof sn_sink_frame sn_sink_flags sn_topok sn_out sn_fpcall rw_CB_length sn_write_spec. apply Kc. reflexivity. }
do 9 zs.
try rewrite (land_M64_id r) by lia.

match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z [C8 apv] |- _ => rename H into APC4 end.
match goal with H : rw_cells _ ?mm B _ |- _ => rename H into BUF4 end.
match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 64)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 64)%Z _ |- _ =>
pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
release_frame APC4 ST5 (bv_unsigned sp + -360)%Z.
release_frame AP2 ST5 B.
release_frame BUF4 ST5 (bv_unsigned sp + -272)%Z.
release_frame FRv ST5 (bv_unsigned sp).
lazymatch goal with F0 : rw_cells _ ?mm Fp _, F40 : rw_cells _ ?mm (Fp + 40)%Z _, F48 : rw_cells _ ?mm (Fp + 48)%Z _, F56 : rw_cells _ ?mm (Fp + 56)%Z _,
F64 : rw_cells _ ?mm (Fp + 64)%Z _, F88 : rw_cells _ ?mm (Fp + 88)%Z _, F96 : rw_cells _ ?mm (Fp + 96)%Z _,
F148 : rw_cells _ ?mm (Fp + 148)%Z _, F152 : rw_cells _ ?mm (Fp + 152)%Z _, F160 : rw_cells _ ?mm (Fp + 160)%Z _ |- _ =>
assert (FALL : rw_cells segs mm Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (e_sn_write + 0x0)); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 bufp)]
++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode'; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)]
++ [C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 CK)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
[ apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F0|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F40|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F48|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F56|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F64|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F88|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F96|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F148|];
apply (proj2 (rw_cells_app segs _ _ _ _)); split; [piece F152|];
piece F160
| ] end.
destruct (rw_cells_forget _ _ _ _ FALL) as [fjunk FJ]. cbn [cells_size csize Nat.add app] in FJ.
apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
split; [exact ST5|].
split; [split; [exact SSP1 | exact SSP2]|].
split; [exact DST4|]. split; [exact CK4|]. exact FJ.
Qed.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import QlEo_c1.Mq0.
Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import Q91D.Mq2.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Q8l1.Mq1.
Import Q5m9.Mq0.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation PA_i := G.T_printf.PA_i.
Local Notation d_p := G.T_printf.d_p.
Local Notation d_t := G.T_printf.d_t.
Local Notation d_ty := G.T_printf.d_ty.

Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
m s = QlEo_c1.Mq0.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = QlEo_c1.Mq0.Ret (Ok (tt, o ++ bs)).
Proof.
intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma OUTFP_sn_eq : forall y w p fl t o o1 r, fmt_fp o y w p fl t = Some (o1, r) -> zlength o1 <= SN_CAP ->
OUTFP_sn y w p fl t o = QlEo_c1.Mq0.Ret (Ok (r, o1)).
Proof.
intros y w p fl t o o1 r E H. unfold OUTFP_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
rewrite E. replace (zlength o1 <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
m s = QlEo_c1.Mq0.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
mpad OUT_sn c w l fl o = QlEo_c1.Mq0.Ret (Ok (tt, o ++ concat ps)).
Proof.
intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
- inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
- destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
apply OUT_sn_eq. exact H.
Qed.

Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
inversion T; subst. clear T.
repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
destruct a as [s|i|u|dd|li|lu].
- destruct (negb (d_ty d =? T_PTR)); [discriminate|].
destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
eapply conv_tail_sn; eassumption.
- destruct (negb (d_ty d =? T_INT)); [discriminate|].
destruct (d_t d =? 99); [eapply conv_tail_sn; eassumption|].
destruct (INTMAX_MAX <? i mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_UINT)); [discriminate|].
destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
- discriminate.
- destruct (negb (d_ty d =? T_LONG)); [discriminate|].
destruct (INTMAX_MAX <? li mod 2 ^ 64);
[|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
eapply conv_int_sn; eassumption.
- destruct (negb (d_ty d =? T_ULONG) || negb (d_t d =? 117))%bool; [discriminate|].
eapply conv_int_sn; eassumption.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
printf_loop OUT_sn OUTFP_sn fuel s args cnt o = QlEo_c1.Mq0.Ret (Ok (r, o ++ concat ps)).
Proof.
induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
cbn [printf_pieces_loop] in P. cbn [printf_loop].
destruct s as [|c s1]; [discriminate|].
destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
pose proof (zlength_nonneg o) as Ho.
destruct (0 <? zlength lit).
- destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
- destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo_c1.Mq0.Ret (Ok (r, concat ps)).
Proof.
intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof.
intros x Hx. destruct (Z_lt_le_dec x 10).
- rewrite dec_digits_small by lia. rewrite Z.div_small, Z.mod_small, dec_digits_0 by lia. reflexivity.
- apply dec_digits_step. lia.
Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. intros x Hx. rewrite dec_digits_step1 by lia. rewrite length_app. cbn. lia. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof.
induction n as [|n IH]; intros x Hx H64.
- cbn in Hx. replace x with 0 by lia. rewrite dec_digits_0. cbn. lia.
- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite dec_digits_0; cbn; lia|].
rewrite dec_digits_step1 by lia. rewrite length_app. cbn [length].
specialize (IH (x / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)). lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Lemma zsub_snoc : forall l i n, 0 <= i -> 0 <= n -> i + n + 1 <= zlength l ->
zsub l i (n + 1) = zsub l i n ++ [znth l (i + n)].
Proof.
intros l i n Hi Hn H. unfold zsub, zlength in *.
replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
rewrite firstn_S_snoc by (rewrite length_skipn; lia). rewrite nth_skipn.
unfold znth. destruct (Z.ltb_spec0 (i + n) 0); [lia|].
replace (Z.to_nat (i + n)) with (Z.to_nat i + Z.to_nat n)%nat by lia. reflexivity.
Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. intros. reflexivity. Qed.

Lemma fmt_u_loop_dec : forall (n : nat) fuel y s b,
(n < fuel)%nat -> 0 <= y < 10 ^ Z.of_nat n -> y < 2^64 -> Z.of_nat n <= s -> s <= zlength b ->
exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - zlength (dec_digits y), b')
/\ length b' = length b
/\ zsub b' (s - zlength (dec_digits y)) (zlength (dec_digits y)) = dec_digits y
/\ (forall i, ~ (s - zlength (dec_digits y) <= i < s) -> znth b' i = znth b i).
Proof.
induction n as [|n IH]; intros fuel y s b Hf Hy Hy64 Hs Hb.
- cbn in Hy. destruct fuel as [|fuel]; [lia|]. exists b. cbn [fmt_u_loop].
replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
replace y with 0 by lia. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
- destruct fuel as [|fuel]; [lia|].
destruct (Z.eq_dec y 0) as [->|NZ].
+ exists b. cbn [fmt_u_loop Z.eqb negb]. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
+ cbn [fmt_u_loop]. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
unfold fmt_u_loop_body at 1.
rewrite Nat2Z.inj_succ in Hy, Hs. rewrite Z.pow_succ_r in Hy by lia.
destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10)) ltac:(lia)
ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)
ltac:(lia) ltac:(rewrite zlength_zupd; lia))
as (b' & E & LEN & SUB & OUT).
pose proof (dec_digits_step1 y ltac:(lia)) as DD.
assert (LD : zlength (dec_digits y) = zlength (dec_digits (y / 10)) + 1) by (rewrite DD, zlength_app; reflexivity).
pose proof (zlength_nonneg (dec_digits (y / 10))) as L0.
pose proof (dec_digits_len_bound n (y / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)) as L20.
unfold zlength in *.
exists b'. split; [rewrite E; f_equal; f_equal; f_equal; lia|].
split; [rewrite LEN; apply zupd_length|].
split.
* rewrite LD. replace (s - (Z.of_nat (length (dec_digits (y / 10))) + 1)) with (s - 1 - Z.of_nat (length (dec_digits (y / 10)))) by lia.
rewrite zsub_snoc by (unfold zlength; rewrite ?LEN, ?zupd_length; lia).
rewrite SUB. replace (s - 1 - Z.of_nat (length (dec_digits (y / 10))) + Z.of_nat (length (dec_digits (y / 10)))) with (s - 1) by lia.
rewrite OUT by lia. rewrite znth_zupd_eq by (unfold zlength; lia). rewrite DD. unfold CHR_0. reflexivity.
* intros i Hi. rewrite OUT by lia. apply znth_zupd_neq. lia.
Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_u_dec : forall x, 0 <= x < 2^64 ->
exists b', fmt_u x (zrepeat 0 24) 24 = Some (24 - zlength (dec_digits x), b')
/\ zlength b' = 24 /\ zsub b' (24 - zlength (dec_digits x)) (zlength (dec_digits x)) = dec_digits x.
Proof.
intros x Hx. unfold fmt_u. change FMT_U_FUEL with 21%nat.
destruct (fmt_u_loop_dec 20 21 x 24 (zrepeat 0 24) ltac:(lia) ltac:(pose proof pow10_20; lia) ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia) ltac:(change (zlength (zrepeat 0 24)) with 24; lia))
as (b' & E & LEN & SUB & _).
exists b'. rewrite E. split; [reflexivity|]. split; [unfold zlength; rewrite LEN; reflexivity| exact SUB].
Qed.

Ltac zb1 :=
match goal with
| |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
| |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
| |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
end; cbn [andb orb negb]; cbv beta iota.

Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. reflexivity. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. reflexivity. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. reflexivity. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

Lemma tail_pieces_d : forall prefix body, zlength prefix <= 1 -> 1 <= zlength body <= 20 ->
tail_pieces 0 0 0 (Z.max (-1) (zlength body + 0)) prefix body = Some ([prefix; body], zlength prefix + zlength body).
Proof.
intros prefix body Hp Hb. pose proof (zlength_nonneg prefix). unfold tail_pieces. cbv zeta.
replace (Z.max (Z.max (-1) (zlength body + 0)) (zlength body)) with (zlength body) by lia.
replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
unfold INT_MAX. zb1. zb1.
unfold pad_pieces. fl0. zb1. zb1. reflexivity.
Qed.

Lemma printf_pieces_d_pos : forall x, 1 <= x < 2^31 ->
printf_pieces FMT_d [PA_i x] = Some ([[]; []; dec_digits x], zlength (dec_digits x)).
Proof.
intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1.
unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x).
zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma printf_pieces_d_neg : forall x, -2^31 <= x < 0 ->
printf_pieces FMT_d [PA_i x] = Some ([[]; [45]; dec_digits (- x)], 1 + zlength (dec_digits (- x))).
Proof.
intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
unfold INTMAX_MAX. zb1.
replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)).
zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma fmt_d_pos : forall x, 1 <= x < 2^31 -> fmt_d x = Some (dec_digits x, zlength (dec_digits x)).
Proof.
intros x Hx. unfold fmt_d. cbv zeta. unfold u64. rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1. fl0.
destruct (fmt_u_dec x ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x). unfold zlength in *.
repeat zb1.
replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits x))) + 0)) with (Z.of_nat (length (dec_digits x))) by lia.
unfold INT_MAX. repeat zb1.
rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 0) with (@nil Z). cbn [app]. rewrite app_nil_r.
replace (24 - (24 - Z.of_nat (length (dec_digits x)))) with (Z.of_nat (length (dec_digits x))) by lia.
rewrite SUB. repeat f_equal; lia.
Qed.

Lemma fmt_d_neg : forall x, -2^31 <= x < 0 -> fmt_d x = Some (45 :: dec_digits (- x), 1 + zlength (dec_digits (- x))).
Proof.
intros x Hx. unfold fmt_d. cbv zeta. unfold u64.
replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
unfold INTMAX_MAX. zb1.
replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
destruct (fmt_u_dec (- x) ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)). unfold zlength in *.
repeat zb1.
replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits (- x)))) + 0)) with (Z.of_nat (length (dec_digits (- x)))) by lia.
unfold INT_MAX. repeat zb1.
rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 1) with [45]. cbn [app]. rewrite app_nil_r.
replace (24 - (24 - Z.of_nat (length (dec_digits (- x))))) with (Z.of_nat (length (dec_digits (- x)))) by lia.
rewrite SUB. repeat f_equal; lia.
Qed.

Theorem printf_sn_d : forall i o r, -2^31 <= i < 2^31 -> fmt_d i = Some (o, r) ->
printf_model OUT_sn OUTFP_sn FMT_d [PA_i i] [] = QlEo_c1.Mq0.Ret (Ok (r, o)).
Proof.
intros i o r Hi E.
destruct (Z.eq_dec i 0) as [->|NZ].
{ vm_compute in E. inversion E; subst. vm_compute. reflexivity. }
pose proof (dec_digits_length (Z.abs i)) as L.
destruct (Z_lt_le_dec i 0).
- rewrite fmt_d_neg in E by lia. inversion E; subst. rewrite Z.abs_neq in L by lia.
rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_neg i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
unfold zlength, SN_CAP. cbn [length]. lia.
- rewrite fmt_d_pos in E by lia. inversion E; subst. rewrite Z.abs_eq in L by lia.
rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_pos i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
unfold zlength, SN_CAP. lia.
Qed.

Ltac lhs_cbvg1 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d conv OUT_sn OUTFP_sn mbind mret] in l in change l with l' end.
Ltac lhs_cbvg2 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d OUT_sn OUTFP_sn mbind mret munr Z.ltb Z.leb orb Z.sub Z.add] in l in change l with l' end.

Section G.

Local Definition gw_tbl_0 := tt.

#[using="Type"] Lemma gw_all : True. Proof. exact I. Qed.

End G.
End Mq2.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QTyG QM7w QNAo Q8QT QDXD Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QTyG.Mq0 QM7w QNAo.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq4.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0)))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq4.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_1)))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mq4.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_2))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_3))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_4))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_7))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_8))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_9))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_13))))))).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).
Definition rfresh_image : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rfresh_image) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rfresh_image)).

Definition rauxv_ok_pres : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq1.rauxv_ok_pres) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq1.rauxv_ok_pres)).

Notation RISTF := (@ISTF_g ref_reserved).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rgmf_of_facts st LB sc g :
RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof. clear - st LB sc g.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
constructor.
- gw_exact MSL.
- gw_exact AVr.
- gw_exact FRr.
- gw_exact MW.
- gw_exact SC48.
- gw_exact GSC.
- exists b, (mkGhdr (Some g) ai). split; [gw_exact Hmem|]. split; [gw_exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
+ intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
exact (X Hmem Hgh S0).
+ intros o Ho. exact (GU b _ o Hgh Ho).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
- destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
exists n, p. split; reflexivity.
Qed.

#[using="Type"] Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof. clear - st LB sc.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| gw_exact GSC]. eapply rgmf_of_facts; [gw_exact F| gw_exact LM| gw_exact GSC| gw_exact SC].
- intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply rgmf_of_facts; [gw_exact F| gw_exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| gw_exact SC]|].
split; [gw_exact SCn|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply rgmf_of_facts; [gw_exact F| gw_exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| gw_exact SC]|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

#[using="segs RATP RGOT_SSP ref_reserved LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER"] Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ gw_RTEXT_LO <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= gw_RTEXT_LO \/ RDATA_LO <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= RDATA_LO \/ gw_RDATA2_LO <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= gw_RDATA2_LO \/ RIMG_HI <= r_base r).
Proof. clear - segs RATP RGOT_SSP ref_reserved LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rid r st0. gw_expose_win. first [clear st0 | gw_hide st0 | idtac].
intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. unfold alloc_ceiling in *. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER"] Lemma rmalloc_fp_cases_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER stE mE lo sp a RATP st0. gw_expose_fam RATP. first [clear st0 | gw_hide st0 | idtac].
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; gw_exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. gw_expose_fam RATP. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER"] Lemma rmalloc_fp_image_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
0x10000 <= a < RIMG_HI -> (RATP + 131968) <= a < (RATP + 132896) \/ (RATP + -164) <= a < (RATP + -164 + 4).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER RATP RIMG_HI stE mE lo sp a st0. gw_expose_fam RATP. try gw_hide st0.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. gw_exact H.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); gw_exact RS1)). lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER"] Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER stE mE lo sp m1 m' B RATP st0. gw_expose_fam RATP. first [clear st0 | gw_hide st0 | idtac].
intros MRE AUX PE CLO SB. eapply rauxv_ok_pres; [gw_exact AUX| gw_exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH). unfold alloc_ceiling in *. lia.
- intros a Ha Hfp. gw_expose_fam RATP.
destruct (rmalloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; gw_expose_fam RATP; lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER"] Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells segs m1 A cs ->
sp <= A -> alloc_ceiling <= A -> rw_cells segs m' A cs.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved st m MR ER segs stE mE lo sp m1 m' A cs st0. first [clear st0 | gw_hide st0 | idtac].
intros MRE PE H HA HC. eapply rpres_except_rw_cells; [gw_exact PE| gw_exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End RC__1.

End G.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mqa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QROt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QROt.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxv.Mqo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5m9.Mq8.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Let ralloc_slot_entry := (base + 0)%Z.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mq4.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Q8l1.Mq8.rpres_except segs) (@rpres_except) gw_tbl_0)))))))))).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_1)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_2 := (gw_ent (@QQRC.Mq4.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) (gw_ent (@Q8l1.Mq8.rimplT segs RC__) (@rimplT) gw_tbl_1))))).
Definition rta_frame : ltac:(gw_rebind_ty (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QROt.Mq3.rta_frame RC__) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QZxv.Mqo.rta_frame RC__) (@rta_frame) (gw_ent (@QROt.Mq3.rta_frame RC__) (@rta_frame) gw_tbl_2)).
Definition rt1_regs : ltac:(gw_rebind_ty (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QZxv.Mqo.rt1_regs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q5m9.Mq8.rt1_regs RATP) (@rt1_regs) (gw_ent (@QZxv.Mqo.rt1_regs RATP) (@rt1_regs) gw_tbl_3)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q5m9.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QZxv.Mqo.rarea_rep segs) (@rarea_rep) (gw_ent (@QROt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_4)))))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q5m9.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QZxv.Mqo.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QROt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_5)))))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q5m9.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QZxv.Mqo.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QROt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_6)))))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q5m9.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QZxv.Mqo.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QROt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_7)))))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q5m9.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QZxv.Mqo.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QROt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_8)))))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q5m9.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QZxv.Mqo.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QROt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_9)))))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q5m9.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QZxv.Mqo.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QROt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_10)))))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q5m9.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QZxv.Mqo.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QROt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_11)))))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q5m9.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QZxv.Mqo.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QROt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_12)))))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q5m9.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QZxv.Mqo.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QROt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_13)))))))))))))))))).
Hypothesis rdbi_range : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdbi_range) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rdebruijn_read : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdebruijn_read) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis mul_srliw27_sxv : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq8.gw_all) (@Q8l1.Mq8.mul_srliw27_sxv) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524; 664; 676; 696; 708; 712; 768; 784; 804; 816; 876]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_undef : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_undef) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_undef)).
#[global] Arguments rimplT_undef {R}%_type_scope o w k%_function_scope s Q%_function_scope ms.
Definition rimplT_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_evt)).
#[global] Arguments rimplT_evt {R}%_type_scope o t s Q%_function_scope P%_function_scope ms _ _%_function_scope.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rgroup_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rgroup_bounds) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rgroup_bounds)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Definition rfin_walk : ltac:(gw_ctx_fold_ty2 (@QROt.Mq3.rfin_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QROt.Mq3.rfin_walk)).

Definition ras_entry_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.ras_entry_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.ras_entry_walk)).
Definition rt1_fin_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rt1_fin_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rt1_fin_walk)).
Definition rt1_deq_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rt1_deq_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rt1_deq_walk)).
Definition rt1_next_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rt1_next_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rt1_next_walk)).
Definition rdeq_self_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rdeq_self_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rdeq_self_walk)).
Definition rdeq_other_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rdeq_other_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rdeq_other_walk)).
Definition rm_act_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rm_act_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rm_act_walk)).
Definition rm_skip_walk : ltac:(gw_ctx_fold_ty2 (@QZxv.Mqo.rm_skip_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QZxv.Mqo.rm_skip_walk)).

Definition ravz_pre_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq8.ravz_pre_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq8.ravz_pre_walk)).
Definition ravz_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq8.ravz_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq8.ravz_walk)).
Definition ract_skip_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq8.ract_skip_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq8.ract_skip_walk)).
Definition ract_next_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq8.ract_next_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq8.ract_next_walk)).
Definition ract_span_walk : ltac:(gw_ctx_fold_ty2 (@Q5m9.Mq8.ract_span_walk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q5m9.Mq8.ract_span_walk)).

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ ralloc_slot_entry rdbi_range rdebruijn_read mul_srliw27_sxv"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ (RATP + 131968) <= a < (RATP + 132896)
\/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

#[using="Type"] Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. clear - st lo sp a. intros; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_ctx st lo sp a : (RATP + 131968) <= a < (RATP + 132896) -> rta_fp st lo sp a. Proof. clear - RATP st lo sp a. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. clear - st lo sp a q RATP. gw_expose_fam RATP. intros; do 2 right; left. exists q; auto. Qed.
#[using="Type"] Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. clear - st lo sp a b gh RATP. gw_expose_fam RATP. intros; do 3 right. exists b, gh; auto. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).

Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv segs m' -> stk segs m' lo spv ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)).

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry CLO LO HK1"] Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
rmrep stX mZ -> mem_inv segs mZ -> rw_cells segs mZ (spv + -144) (FRM junk) -> stk segs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_fin stX g3 msk K) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 (base + 0x1a0)) fc None mZ (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry CLO LO HK1 segs base RATP R K bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc TAF SC spv RR FRM. gw_expose_fam RATP. first [clear FRM | gw_hide FRM | idtac]; try gw_hide RR; try gw_hide spv; first [clear SC | gw_hide SC | idtac]; first [clear TAF | gw_hide TAF | idtac]; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; try gw_hide lo; try gw_hide sc; try gw_hide m; try gw_hide st; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds st m g3) as GB0.
pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
unfold ta_fin. riprefixT. unfold RR, rt1_regs.
eapply evt_mono.
{ eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| gw_exact FRZ| gw_exact STZ| unfold spv; lia| gw_exact MIZ].
rewrite unsigned_lit by lia. symmetry; gw_exact ECONC. }
cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
eapply rpres_except_trans; [gw_exact PEZ|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
- intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1"] Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
(pc = (base + 0x11c) \/ pc = (base + 0x128)) ->
ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
rmrep stZ mZ -> mem_inv segs mZ -> rw_cells segs mZ (spv + -144) (FRM junk) -> stk segs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_avz K bail stZ g3) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1 segs base RATP R K bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc spv RR FRM. gw_expose_fam RATP. try gw_hide FRM; try gw_hide RR; try gw_hide spv; try gw_hide fc; try gw_hide F; try gw_hide t6; try gw_hide t5; try gw_hide t4; try gw_hide t3; try gw_hide s11; try gw_hide s10; try gw_hide s9; try gw_hide s8; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; try gw_hide s3; first [clear s2 | gw_hide s2 | idtac]; try gw_hide a1; try gw_hide s1; first [clear s0 | gw_hide s0 | idtac]; try gw_hide t2; try gw_hide tp; try gw_hide gp; first [clear sp | gw_hide sp | idtac]; try gw_hide ra; try gw_hide lo; try gw_hide sc; first [clear m | gw_hide m | idtac]; try gw_hide st; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; try gw_hide o; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
unfold ta_avz, activate_group.
destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
rewrite EM, Hmem. cbn [default].
replace (group_active_idx stZ b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
apply Z.eqb_neq in MZ.
rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; gw_exact Hmem).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; gw_exact ECONC).

unfold RR.
eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x128)) fc None mZ (seg_rom segs))).
{ destruct PC as [-> | ->].
- eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [gw_exact HG| gw_exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
- apply evt_done. eexists. reflexivity. }
intros ms0 [a1x ->].
riprefixT. eapply evt_mono.
{ eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| gw_exact SC| gw_exact HG| gw_exact MIZ].
intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
assert (TR4 : ta_rel sc st st4).
{ eapply ta_rel_trans; [gw_exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
- repeat split; reflexivity.
- cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; gw_exact Hb.
- cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (Z.ldiff_nonneg f act). lia. }
assert (TR5 : ta_rel sc st st5).
{ eapply ta_rel_trans; [gw_exact TR4|]. unfold st5. apply ta_rel_decay.
pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
assert (FR5 : rw_cells segs m5 (spv + -144) (FRM junk)).
{ eapply rw_cells_transport; [gw_exact FRZ| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia. }
assert (ST5 : stk segs m5 lo (spv + -144)).
{ eapply stk_transport_disjoint; [gw_exact STZ| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia. }
eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
[gw_exact TR5| | gw_exact GM| | | gw_exact MR5| gw_exact MI5| gw_exact FR5| gw_exact ST5|].
- unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. gw_exact HA.
- unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
- pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
- eapply rpres_except_trans; [gw_exact PEZ|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
+ intros x Hx. apply rta_fp_ctx. gw_expose_fam RATP. lia.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 hi_311 lo_116 lo_313 CODE D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1"] Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
msk = m_freed (get_meta_rec stY g2) ->
(forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
m_next (get_meta_rec stY g2) <> None ->
rmrep stY mY -> mem_inv segs mY -> rw_cells segs mY (spv + -144) (FRM junk) -> stk segs mY lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mY ->
rimplT o (ta_act sc K bail stY g2 msk) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 (base + 0xf4)) fc None mY (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 hi_311 lo_116 lo_313 CODE D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1 segs base RATP R K bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc spv RR FRM. gw_expose_fam RATP. first [clear FRM | gw_hide FRM | idtac]; try gw_hide RR; try gw_hide spv; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; try gw_hide lo; try gw_hide sc; first [clear m | gw_hide m | idtac]; try gw_hide st; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; gw_exact Hmem).
assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; gw_exact RFY).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; gw_exact ECONC).
unfold ta_act. rewrite EMb. cbn [default].
replace (group_active_idx stY b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
unfold RR.
destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
-
apply Z.eqb_eq in ZR.
destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
+
apply aptr_eqb_eq in EQ. subst mn.
destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
*
assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
{ destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; gw_exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
assert (MZ : msk = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
assert (IL : i <= m_last_idx (get_meta_rec st g2)).
{ pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
{ rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
rewrite ZR, Z.bits_0 in TB2. discriminate. }

cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
*
destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
apply Z.eqb_eq in AV0.
assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [gw_exact ZR| gw_exact GNY| gw_exact MWY| gw_exact SCY| | rewrite GM1; gw_exact GMg| gw_exact AV0| gw_exact MIY].
intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. gw_exact Ho'. }
cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
cbv zeta iota beta.
match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
assert (TRG : ta_rel sc st stG).
{ eapply ta_rel_trans; [gw_exact TR|]. apply ta_rel_set_gai.
- apply land31_range.
- intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
rewrite (tr_conc _ _ _ g2 TR).
eapply (ravz_block (base + 0x128) stG g2 m5); [right; reflexivity| gw_exact TRG| | gw_exact GM| gw_exact MR5| gw_exact MI5| | |].
-- unfold stG. rewrite active_set_gai. gw_exact HA.
-- eapply rw_cells_transport; [gw_exact FRY| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply stk_transport_disjoint; [gw_exact STY| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply rpres_except_trans; [gw_exact PEY|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
+
assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
pose proof (GN mn eq_refl) as GMn.
destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [gw_exact ZR| gw_exact GNY| gw_exact NE| gw_exact MSn| gw_exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [gw_exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ravz_block (base + 0x11c) (set_active sc (Some mn) stY) mn m5); [left; reflexivity| gw_exact TRN| | gw_exact GMn| gw_exact MR5| gw_exact MI5| | |].
-- rewrite active_set_active, Z.eqb_refl. reflexivity.
-- eapply rw_cells_transport; [gw_exact FRY| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
-- eapply stk_transport_disjoint; [gw_exact STY| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
-- eapply rpres_except_trans; [gw_exact PEY|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. gw_expose_fam RATP. lia.
-
apply Z.eqb_neq in ZR.
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [gw_exact ZR| gw_exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
eapply (ravz_block (base + 0x11c) stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 hi_311 lo_116 lo_313 CODE D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1"] Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
rmrep stX mX -> mem_inv segs mX -> rw_cells segs mX (spv + -144) (FRM junk) -> stk segs mX lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mX ->
rimplT o (ta_m sc K bail stX g1) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 (base + 0xc8)) fc None mX (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 hi_311 lo_116 lo_313 CODE D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1 segs base RATP R K bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc spv RR FRM. gw_expose_fam RATP. first [clear FRM | gw_hide FRM | idtac]; try gw_hide RR; try gw_hide spv; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; first [clear lo | gw_hide lo | idtac]; try gw_hide sc; first [clear m | gw_hide m | idtac]; try gw_hide st; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; first [clear bail | gw_hide bail | idtac]; first [clear K | gw_hide K | idtac].
intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
unfold ta_m, RR.
set (f := m_freed (get_meta_rec stX g1)).
destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
-
pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
rewrite GN1.
destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [gw_exact FSK| gw_exact GN1| gw_exact MSn| gw_exact RFn| gw_exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [gw_exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ reflexivity.
+ intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
+ rewrite rec_set_active, GN2. discriminate.
+ eapply rw_cells_transport; [gw_exact FRX| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
+ eapply stk_transport_disjoint; [gw_exact STX| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
+ eapply rpres_except_trans; [gw_exact PEX|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. gw_expose_fam RATP. lia.
-
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [gw_exact FSK| gw_exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
eapply (ract_block stX g1 f mX); try eassumption.
+ reflexivity.
+ intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
+ rewrite GN1. discriminate.
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_311 lo_15 lo_19 lo_116 lo_313 CODE D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_15 ANCH_19 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1"] Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
a0 = Z_to_bv 64 sc ->
rmrep st m -> mem_inv segs m -> stk segs m lo spv ->
(forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m' -> mem_inv segs m' -> rw_cells segs m' (spv + -144) (FRM junk) -> stk segs m' lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 (base + 0x1e0)) fc None m' (seg_rom segs))) ->
rimplT o (try_avail sc st K bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_14 hi_18 hi_114 hi_311 lo_15 lo_19 lo_116 lo_313 CODE D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_311 E_311 D_313 E_313 ANCH_15 ANCH_19 ANCH_116 ANCH_313 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv ralloc_slot_entry TAF SC CLO LO HK1 segs base RATP R K bail o s Q st m sc lo ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc spv RR FRM. gw_expose_fam RATP. first [clear FRM | gw_hide FRM | idtac]; first [clear RR | gw_hide RR | idtac]; try gw_hide spv; first [clear fc | gw_hide fc | idtac]; first [clear F | gw_hide F | idtac]; first [clear t6 | gw_hide t6 | idtac]; first [clear t5 | gw_hide t5 | idtac]; first [clear t4 | gw_hide t4 | idtac]; first [clear t3 | gw_hide t3 | idtac]; first [clear s11 | gw_hide s11 | idtac]; first [clear s10 | gw_hide s10 | idtac]; first [clear s9 | gw_hide s9 | idtac]; first [clear s8 | gw_hide s8 | idtac]; first [clear s7 | gw_hide s7 | idtac]; first [clear s6 | gw_hide s6 | idtac]; first [clear s5 | gw_hide s5 | idtac]; first [clear s4 | gw_hide s4 | idtac]; first [clear s3 | gw_hide s3 | idtac]; first [clear s2 | gw_hide s2 | idtac]; first [clear a1 | gw_hide a1 | idtac]; first [clear s1 | gw_hide s1 | idtac]; first [clear s0 | gw_hide s0 | idtac]; first [clear t2 | gw_hide t2 | idtac]; first [clear tp | gw_hide tp | idtac]; first [clear gp | gw_hide gp | idtac]; first [clear sp | gw_hide sp | idtac]; first [clear ra | gw_hide ra | idtac]; try gw_hide lo; try gw_hide sc; try gw_hide m; try gw_hide st; first [clear Q | gw_hide Q | idtac]; first [clear s | gw_hide s | idtac]; first [clear o | gw_hide o | idtac]; try gw_hide bail; try gw_hide K.
intros until a7. intros A0 MR MI ST HK0.
assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
riprefixT. eapply evt_mono.
{ eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [gw_exact A0| gw_exact ST| gw_exact LO| gw_exact MI]. }
cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
{ eapply rpres_except_of_munch_cov; [gw_exact MU1| gw_exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
clear MU1 WM1.
rewrite (try_avail_eq sc K bail st).
destruct (active st sc) as [g|] eqn:HA.
2:{
eapply (HK0 st m1); [| apply ta_rel_refl| gw_exact HA| gw_exact MR1| gw_exact MI1| gw_exact FR1| gw_exact ST1| gw_exact PE1].
unfold ta_fail, try_avail. rewrite HA. reflexivity. }
destruct (taf_head _ _ TAF g HA) as [GM GSC].
pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
unfold pw. cbn [oconc]. unfold wz.
destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
2:{
apply Z.eqb_neq in AV.
riprefixT. eapply evt_mono.
{ eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [gw_exact AV| gw_exact MI1]. }
cbv beta. intros ms' ->.
eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| gw_exact HA| gw_exact GM| reflexivity| lia| gw_exact MR1| gw_exact MI1| gw_exact FR1| gw_exact ST1| gw_exact PE1]. }
apply Z.eqb_eq in AV.
destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
-
apply Z.eqb_eq in FZ.
riprefixT. eapply evt_mono.
{ eapply (rt1_deq_walk st m1 g sc MR1 MSg); [gw_exact AV| gw_exact FZ| gw_exact MI1]. }
cbv beta. intros ms' ->.
destruct (decide (nx = g)) as [->|NEn].
+
rewrite (dequeue_self_eq sc g st GN).
replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
cbn [Z.eqb].
riprefixT. eapply evt_mono.
{ eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [gw_exact GN| gw_exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
eapply (HK0 _ m2).
* unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
rewrite (dequeue_self_eq sc g st GN).
change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by first [reflexivity | (cbn; lia)]. apply ta_rel_put_links.
* change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* gw_exact MR2.
* gw_exact MI2.
* eapply rw_cells_transport; [gw_exact FR1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
* eapply stk_transport_disjoint; [gw_exact ST1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
* eapply rpres_except_trans; [gw_exact PE1|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; gw_expose_fam RATP; lia| eapply rta_fp_meta; [gw_exact MSg| lia]].
+
assert (NEp : pv <> g).
{ intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
assert (HA1 : active st1 sc = Some nx).
{ unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
rewrite HA1.
pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
riprefixT. eapply evt_mono.
{ eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [gw_exact GN| gw_exact GP| gw_exact NEn| gw_exact NEp| gw_exact MSn| gw_exact MSp| gw_exact MI1]. }
cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
assert (TR1 : ta_rel sc st st1).
{ unfold st1.
lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
lazymatch sC with set_active _ _ ?sB =>
lazymatch sB with put_meta _ _ ?sA =>
apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
end end end.
rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; gw_exact E).
rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; gw_exact E). reflexivity. }

assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
{ intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by gw_exact Hq. rewrite rec_set_active.
rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
- apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
- rewrite get_meta_rec_put. reflexivity. }
eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [gw_exact TR1| gw_exact HA1| | split; [gw_exact GMn| gw_exact NEn] | gw_exact MR2| gw_exact MI2| | |].
* intros q [GMq NEq]. split; [gw_exact GMq|]. rewrite (REC1 q NEq).
destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
destruct (aptr_eqb q nx) eqn:E1.
-- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
destruct (aptr_eqb nx pv) eqn:E2.
++ exists nx. cbn. split; [reflexivity|]. split; [gw_exact GMn| gw_exact NEn].
++ exists qn. split; [gw_exact QN|]. split; [gw_exact GMqn|]. intros ->.
rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
-- destruct (aptr_eqb q pv) eqn:E2.
++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [gw_exact GMn| gw_exact NEn].
++ exists qn. split; [gw_exact QN|]. split; [gw_exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
* eapply rw_cells_transport; [gw_exact FR1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
* eapply stk_transport_disjoint; [gw_exact ST1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
* eapply rpres_except_trans; [gw_exact PE1|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
[apply rta_fp_ctx; gw_expose_fam RATP; lia| eapply rta_fp_meta; [gw_exact MSg| lia]| eapply rta_fp_meta; [gw_exact MSp| lia]| eapply rta_fp_meta; [gw_exact MSn| lia]].
-
apply Z.eqb_neq in FZ. rewrite GN.
riprefixT. eapply evt_mono.
{ eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [gw_exact AV| gw_exact FZ| gw_exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | gw_exact GMn| gw_exact MR2| gw_exact MI2| | |].
+ apply ta_rel_set_active.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ intros q GMq. split; [gw_exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
exists qn. split; [gw_exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
+ eapply rw_cells_transport; [gw_exact FR1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
+ eapply stk_transport_disjoint; [gw_exact ST1| gw_exact MU| gw_exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; (gw_expose_fam RATP; unfold alloc_ceiling in *); lia.
+ eapply rpres_except_trans; [gw_exact PE1|]. eapply rpres_except_of_munch_cov; [gw_exact MU| gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. gw_expose_fam RATP. lia.
Qed.
End PHASE.

End RC__1.

End G.
