(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6Iq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzQg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzQg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPUx.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4l4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzHs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDgQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwbh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwbh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGbx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGbx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QB5o.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QB5o. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4WT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4WT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjqb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGEX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGEX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFHW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFHW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfbZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfbZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJ2O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJ2O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHhK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHhK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL4p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL4p. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QP89.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QP89. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJ9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxDK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxDK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoo0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qoo0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnKY.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnKY. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqYW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqYW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3qs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3qs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTgq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTgq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNt7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNt7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUNy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUNy.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCqH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCqH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmCU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmCU.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x59ad8%Z.
Definition w_22 := 0x0000a517%Z.
Definition w_23 := 0x35853a03%Z.
Definition w_170 := 0xea5fc0ef%Z.
Definition w_256 := 0xd4dfc0ef%Z.
Definition w_502 := 0xb29f40ef%Z.
Definition w_509 := 0x959fc0ef%Z.
Definition w_556 := 0x89dfc0ef%Z.
Definition w_560 := 0xad8fd0ef%Z.
Definition w_569 := 0xa1df40ef%Z.
Definition w_573 := 0x859fc0ef%Z.
Definition w_579 := 0x940fc0ef%Z.
Definition w_586 := 0xcedfb0ef%Z.
Definition w_591 := 0x9c5f40ef%Z.
Definition w_595 := 0x801fc0ef%Z.
Definition w_600 := 0x8ecfc0ef%Z.
Definition w_603 := 0x8e0fc0ef%Z.
Definition w_648 := 0xf2cfc0ef%Z.
Definition w_676 := 0x580010ef%Z.
Definition w_683 := 0x855f40ef%Z.
Definition w_690 := 0xe84fc0ef%Z.
Definition w_718 := 0xe14fc0ef%Z.
Definition w_722 := 0x850fd0ef%Z.
Definition w_727 := 0xef1fb0ef%Z.
Definition w_730 := 0xfffbc617%Z.
Definition w_733 := 0xe9860613%Z.
Definition w_737 := 0xdc8fc0ef%Z.
Definition w_742 := 0x994fd0ef%Z.
Definition w_792 := 0xfffbc817%Z.
Definition w_796 := 0xda080813%Z.
Definition w_843 := 0xfffb9697%Z.
Definition w_845 := 0xc5c6b683%Z.
Definition w_1077 := 0x878fc0ef%Z.
Definition w_1090 := 0x844fc0ef%Z.
Definition w_1094 := 0xa81fc0ef%Z.
Definition w_1106 := 0x905fb0ef%Z.
Definition w_1109 := 0x9a8fc0ef%Z.
Definition w_1125 := 0xa05fc0ef%Z.
Definition w_1132 := 0x89dfb0ef%Z.
Definition w_1135 := 0x940fc0ef%Z.
Definition w_1148 := 0x9a9fc0ef%Z.
Definition w_1160 := 0x82dfb0ef%Z.
Definition w_1163 := 0x8d0fc0ef%Z.
Definition w_1178 := 0x931fc0ef%Z.
Definition w_1185 := 0xfc8fb0ef%Z.
Definition w_1188 := 0x86cfc0ef%Z.
Definition w_1192 := 0xeadfb0ef%Z.
Definition w_1197 := 0xf98fb0ef%Z.
Definition w_1218 := 0xf4dfb0ef%Z.
Definition w_1219 := 0xb08fb0ef%Z.
Definition w_1222 := 0x655000ef%Z.
Definition w_1228 := 0xf25fb0ef%Z.
Definition w_1229 := 0xae0fb0ef%Z.
Definition w_1234 := 0x64d000ef%Z.
Definition w_1241 := 0xf89fb0ef%Z.
Definition w_1244 := 0xf8dfb0ef%Z.
Definition w_1278 := 0xfffb8517%Z.
Definition w_1279 := 0x54853707%Z.
Definition w_1281 := 0xfffb8517%Z.
Definition w_1282 := 0x54c53787%Z.
Definition w_1284 := 0xfffb8517%Z.
Definition w_1285 := 0x52053787%Z.
Definition w_1290 := 0xfffb8517%Z.
Definition w_1291 := 0x50853707%Z.
Definition w_1294 := 0x9dcfb0ef%Z.
Definition w_1299 := 0xeb1fb0ef%Z.
Definition w_1306 := 0xce5fb0ef%Z.
Definition w_1311 := 0x519000ef%Z.
Definition w_1314 := 0xc40fb0ef%Z.
Definition w_1321 := 0xe59fb0ef%Z.
Definition w_1329 := 0xe39fb0ef%Z.
Definition w_1332 := 0xe1dfb0ef%Z.
Definition w_1341 := 0x77d000ef%Z.
Definition w_1345 := 0xc49fb0ef%Z.
Definition w_1349 := 0x819fc0ef%Z.
Definition w_1354 := 0xc68fb0ef%Z.
Definition w_1363 := 0xfffb8517%Z.
Definition w_1364 := 0x3f453507%Z.
Definition w_1365 := 0x8c0fb0ef%Z.
Definition w_1370 := 0xce4fb0ef%Z.
Definition w_1382 := 0xd69f30ef%Z.
Definition w_1391 := 0xb0cfb0ef%Z.
Definition w_1419 := 0x6510006f%Z.
Definition w_1421 := 0xb19fb0ef%Z.
Definition w_1425 := 0xd54fc0ef%Z.
Definition w_1430 := 0xbf4fb0ef%Z.
Definition w_1433 := 0xfffbb517%Z.
Definition w_1435 := 0x39c50513%Z.
Definition w_1439 := 0xad1fb0ef%Z.
Definition w_1441 := 0x940f40ef%Z.
Definition w_1463 := 0xa71fb0ef%Z.
Definition w_1467 := 0xa61fb0ef%Z.
Definition w_1589 := 0x879fb0ef%Z.
Definition w_1595 := 0x861fb0ef%Z.
Definition w_1600 := 0xc2cfc0ef%Z.
Definition w_1607 := 0x930fb0ef%Z.
Definition w_1611 := 0x9d1fb0ef%Z.
Definition w_1618 := 0xfffb8517%Z.
Definition w_1619 := 0xff853507%Z.
Definition w_1620 := 0xcc5fa0ef%Z.
Definition w_1623 := 0x8f0fb0ef%Z.
Definition w_1626 := 0x995fb0ef%Z.
Definition w_1697 := 0x87df30ef%Z.
Definition w_1701 := 0xeb8fb0ef%Z.
Definition w_1707 := 0xfa1fa0ef%Z.
Definition w_1712 := 0x841f30ef%Z.
Definition w_1716 := 0xe7cfb0ef%Z.
Definition w_1721 := 0xf69fa0ef%Z.
Definition w_1724 := 0xf5dfa0ef%Z.
Definition w_1735 := 0xaf9fa0ef%Z.
Definition w_1753 := 0xfffb8517%Z.
Definition w_1754 := 0xddc53407%Z.
Definition w_1759 := 0xdd0fb0ef%Z.
Definition w_1764 := 0xf5cfb0ef%Z.
Definition w_1769 := 0xf58fb0ef%Z.
Definition w_1775 := 0xa59fa0ef%Z.
Definition w_1780 := 0xdc1fa0ef%Z.
Definition w_1790 := 0xd54fb0ef%Z.
Definition w_1808 := 0xe14fb0ef%Z.
Definition w_1809 := 0x9d1fa0ef%Z.
Definition w_1813 := 0xcf8fb0ef%Z.
Definition w_1818 := 0x504000ef%Z.
Definition w_1827 := 0xc3dfa0ef%Z.
Definition w_1834 := 0xca4fb0ef%Z.
Definition w_1840 := 0xc8cfb0ef%Z.
Definition w_1844 := 0xec9fb0ef%Z.
Definition w_1849 := 0xd69fa0ef%Z.
Definition w_1854 := 0xe04fb0ef%Z.
Definition w_1861 := 0xd39fa0ef%Z.
Definition w_1864 := 0xddcfb0ef%Z.
Definition w_1867 := 0xdc0fb0ef%Z.
Definition w_1872 := 0xb89fa0ef%Z.
Definition w_1874 := 0xdb8f30ef%Z.
Definition w_1895 := 0x6e00006f%Z.
Definition hi_22 := (Z_to_bv 20 10).
Definition hi_730 := (Z_to_bv 20 1048508).
Definition hi_792 := (Z_to_bv 20 1048508).
Definition hi_843 := (Z_to_bv 20 1048505).
Definition hi_1278 := (Z_to_bv 20 1048504).
Definition hi_1281 := (Z_to_bv 20 1048504).
Definition hi_1284 := (Z_to_bv 20 1048504).
Definition hi_1290 := (Z_to_bv 20 1048504).
Definition hi_1363 := (Z_to_bv 20 1048504).
Definition hi_1433 := (Z_to_bv 20 1048507).
Definition hi_1618 := (Z_to_bv 20 1048504).
Definition hi_1753 := (Z_to_bv 20 1048504).
Definition lo_23 := (Z_to_bv 12 856).
Definition lo_733 := (Z_to_bv 12 3736).
Definition lo_796 := (Z_to_bv 12 3488).
Definition lo_845 := (Z_to_bv 12 3164).
Definition lo_1279 := (Z_to_bv 12 1352).
Definition lo_1282 := (Z_to_bv 12 1356).
Definition lo_1285 := (Z_to_bv 12 1312).
Definition lo_1291 := (Z_to_bv 12 1288).
Definition lo_1364 := (Z_to_bv 12 1012).
Definition lo_1435 := (Z_to_bv 12 924).
Definition lo_1619 := (Z_to_bv 12 4088).
Definition lo_1754 := (Z_to_bv 12 3548).
Definition joff_170 := (Z_to_bv 21 2084516).
Definition joff_256 := (Z_to_bv 21 2084172).
Definition joff_502 := (Z_to_bv 21 2050856).
Definition joff_509 := (Z_to_bv 21 2083160).
Definition joff_556 := (Z_to_bv 21 2082972).
Definition joff_560 := (Z_to_bv 21 2085592).
Definition joff_569 := (Z_to_bv 21 2050588).
Definition joff_573 := (Z_to_bv 21 2082904).
Definition joff_579 := (Z_to_bv 21 2081088).
Definition joff_586 := (Z_to_bv 21 2079980).
Definition joff_591 := (Z_to_bv 21 2050500).
Definition joff_595 := (Z_to_bv 21 2082816).
Definition joff_600 := (Z_to_bv 21 2081004).
Definition joff_603 := (Z_to_bv 21 2080992).
Definition joff_648 := (Z_to_bv 21 2082604).
Definition joff_676 := (Z_to_bv 21 5504).
Definition joff_683 := (Z_to_bv 21 2050132).
Definition joff_690 := (Z_to_bv 21 2082436).
Definition joff_718 := (Z_to_bv 21 2082324).
Definition joff_722 := (Z_to_bv 21 2084944).
Definition joff_727 := (Z_to_bv 21 2080496).
Definition joff_737 := (Z_to_bv 21 2082248).
Definition joff_742 := (Z_to_bv 21 2085268).
Definition joff_1077 := (Z_to_bv 21 2080888).
Definition joff_1090 := (Z_to_bv 21 2080836).
Definition joff_1094 := (Z_to_bv 21 2083456).
Definition joff_1106 := (Z_to_bv 21 2078980).
Definition joff_1109 := (Z_to_bv 21 2081192).
Definition joff_1125 := (Z_to_bv 21 2083332).
Definition joff_1132 := (Z_to_bv 21 2078876).
Definition joff_1135 := (Z_to_bv 21 2081088).
Definition joff_1148 := (Z_to_bv 21 2083240).
Definition joff_1160 := (Z_to_bv 21 2078764).
Definition joff_1163 := (Z_to_bv 21 2080976).
Definition joff_1178 := (Z_to_bv 21 2083120).
Definition joff_1185 := (Z_to_bv 21 2078664).
Definition joff_1188 := (Z_to_bv 21 2080876).
Definition joff_1192 := (Z_to_bv 21 2080428).
Definition joff_1197 := (Z_to_bv 21 2078616).
Definition joff_1218 := (Z_to_bv 21 2080588).
Definition joff_1219 := (Z_to_bv 21 2077448).
Definition joff_1222 := (Z_to_bv 21 3668).
Definition joff_1228 := (Z_to_bv 21 2080548).
Definition joff_1229 := (Z_to_bv 21 2077408).
Definition joff_1234 := (Z_to_bv 21 3660).
Definition joff_1241 := (Z_to_bv 21 2080648).
Definition joff_1244 := (Z_to_bv 21 2080652).
Definition joff_1294 := (Z_to_bv 21 2077148).
Definition joff_1299 := (Z_to_bv 21 2080432).
Definition joff_1306 := (Z_to_bv 21 2079972).
Definition joff_1311 := (Z_to_bv 21 3352).
Definition joff_1314 := (Z_to_bv 21 2077760).
Definition joff_1321 := (Z_to_bv 21 2080344).
Definition joff_1329 := (Z_to_bv 21 2080312).
Definition joff_1332 := (Z_to_bv 21 2080284).
Definition joff_1341 := (Z_to_bv 21 3964).
Definition joff_1345 := (Z_to_bv 21 2079816).
Definition joff_1349 := (Z_to_bv 21 2082840).
Definition joff_1354 := (Z_to_bv 21 2077800).
Definition joff_1365 := (Z_to_bv 21 2076864).
Definition joff_1370 := (Z_to_bv 21 2077924).
Definition joff_1382 := (Z_to_bv 21 2047336).
Definition joff_1391 := (Z_to_bv 21 2077452).
Definition joff_1419 := (Z_to_bv 21 3664).
Definition joff_1421 := (Z_to_bv 21 2079512).
Definition joff_1425 := (Z_to_bv 21 2082132).
Definition joff_1430 := (Z_to_bv 21 2077684).
Definition joff_1439 := (Z_to_bv 21 2079440).
Definition joff_1441 := (Z_to_bv 21 2048320).
Definition joff_1463 := (Z_to_bv 21 2079344).
Definition joff_1467 := (Z_to_bv 21 2079328).
Definition joff_1589 := (Z_to_bv 21 2078840).
Definition joff_1595 := (Z_to_bv 21 2078816).
Definition joff_1600 := (Z_to_bv 21 2081836).
Definition joff_1607 := (Z_to_bv 21 2076976).
Definition joff_1611 := (Z_to_bv 21 2079184).
Definition joff_1620 := (Z_to_bv 21 2075844).
Definition joff_1623 := (Z_to_bv 21 2076912).
Definition joff_1626 := (Z_to_bv 21 2079124).
Definition joff_1697 := (Z_to_bv 21 2046076).
Definition joff_1701 := (Z_to_bv 21 2078392).
Definition joff_1707 := (Z_to_bv 21 2076576).
Definition joff_1712 := (Z_to_bv 21 2046016).
Definition joff_1716 := (Z_to_bv 21 2078332).
Definition joff_1721 := (Z_to_bv 21 2076520).
Definition joff_1724 := (Z_to_bv 21 2076508).
Definition joff_1735 := (Z_to_bv 21 2075384).
Definition joff_1759 := (Z_to_bv 21 2078160).
Definition joff_1764 := (Z_to_bv 21 2078556).
Definition joff_1769 := (Z_to_bv 21 2078552).
Definition joff_1775 := (Z_to_bv 21 2075224).
Definition joff_1780 := (Z_to_bv 21 2076096).
Definition joff_1790 := (Z_to_bv 21 2078036).
Definition joff_1808 := (Z_to_bv 21 2078228).
Definition joff_1809 := (Z_to_bv 21 2075088).
Definition joff_1813 := (Z_to_bv 21 2077944).
Definition joff_1818 := (Z_to_bv 21 1284).
Definition joff_1827 := (Z_to_bv 21 2075708).
Definition joff_1834 := (Z_to_bv 21 2077860).
Definition joff_1840 := (Z_to_bv 21 2077836).
Definition joff_1844 := (Z_to_bv 21 2080456).
Definition joff_1849 := (Z_to_bv 21 2076008).
Definition joff_1854 := (Z_to_bv 21 2078212).
Definition joff_1861 := (Z_to_bv 21 2075960).
Definition joff_1864 := (Z_to_bv 21 2078172).
Definition joff_1867 := (Z_to_bv 21 2078144).
Definition joff_1872 := (Z_to_bv 21 2075528).
Definition joff_1874 := (Z_to_bv 21 2045368).
Definition joff_1895 := (Z_to_bv 21 1760).
Definition G_10778 := 0x13408%Z.
Definition G_10788 := 0x13418%Z.
Definition G_10798 := 0x13428%Z.
Definition G_107c0 := 0x13460%Z.
Definition G_116a8 := 0x164d8%Z.
Definition got_ssp := got_ssp.
Definition RATP := RATP.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_errno_loc := 0x4edd8%Z.
Definition e_197bc := 0x4f29c%Z.
Definition e_extenddftf2 := 0x560ec%Z.
Definition e_fpclassifyl := 0x56284%Z.
Definition e_letf2 := 0x563a0%Z.
Definition e_getf2 := 0x56468%Z.
Definition e_multf3 := 0x56524%Z.
Definition e_floatsitf := 0x56c24%Z.
Definition e_scalbn := 0x56d2c%Z.
Definition e_subtf3 := 0x56dc4%Z.
Definition e_addtf3 := 0x56dd4%Z.
Definition e_floatunsitf := 0x57670%Z.
Definition e_divtf3 := 0x57804%Z.
Definition e_extendsftf2 := 0x5bae8%Z.
Lemma CODE : CodeAt.code_at rsegs 0x59ad8 (QzQg.Mq0.floatscan_code 0x0000a517%Z 0x35853a03%Z 0xea5fc0ef%Z 0xd4dfc0ef%Z 0xb29f40ef%Z 0x959fc0ef%Z 0x89dfc0ef%Z 0xad8fd0ef%Z 0xa1df40ef%Z 0x859fc0ef%Z 0x940fc0ef%Z 0xcedfb0ef%Z 0x9c5f40ef%Z 0x801fc0ef%Z 0x8ecfc0ef%Z 0x8e0fc0ef%Z 0xf2cfc0ef%Z 0x580010ef%Z 0x855f40ef%Z 0xe84fc0ef%Z 0xe14fc0ef%Z 0x850fd0ef%Z 0xef1fb0ef%Z 0xfffbc617%Z 0xe9860613%Z 0xdc8fc0ef%Z 0x994fd0ef%Z 0xfffbc817%Z 0xda080813%Z 0xfffb9697%Z 0xc5c6b683%Z 0x878fc0ef%Z 0x844fc0ef%Z 0xa81fc0ef%Z 0x905fb0ef%Z 0x9a8fc0ef%Z 0xa05fc0ef%Z 0x89dfb0ef%Z 0x940fc0ef%Z 0x9a9fc0ef%Z 0x82dfb0ef%Z 0x8d0fc0ef%Z 0x931fc0ef%Z 0xfc8fb0ef%Z 0x86cfc0ef%Z 0xeadfb0ef%Z 0xf98fb0ef%Z 0xf4dfb0ef%Z 0xb08fb0ef%Z 0x655000ef%Z 0xf25fb0ef%Z 0xae0fb0ef%Z 0x64d000ef%Z 0xf89fb0ef%Z 0xf8dfb0ef%Z 0xfffb8517%Z 0x54853707%Z 0xfffb8517%Z 0x54c53787%Z 0xfffb8517%Z 0x52053787%Z 0xfffb8517%Z 0x50853707%Z 0x9dcfb0ef%Z 0xeb1fb0ef%Z 0xce5fb0ef%Z 0x519000ef%Z 0xc40fb0ef%Z 0xe59fb0ef%Z 0xe39fb0ef%Z 0xe1dfb0ef%Z 0x77d000ef%Z 0xc49fb0ef%Z 0x819fc0ef%Z 0xc68fb0ef%Z 0xfffb8517%Z 0x3f453507%Z 0x8c0fb0ef%Z 0xce4fb0ef%Z 0xd69f30ef%Z 0xb0cfb0ef%Z 0x6510006f%Z 0xb19fb0ef%Z 0xd54fc0ef%Z 0xbf4fb0ef%Z 0xfffbb517%Z 0x39c50513%Z 0xad1fb0ef%Z 0x940f40ef%Z 0xa71fb0ef%Z 0xa61fb0ef%Z 0x879fb0ef%Z 0x861fb0ef%Z 0xc2cfc0ef%Z 0x930fb0ef%Z 0x9d1fb0ef%Z 0xfffb8517%Z 0xff853507%Z 0xcc5fa0ef%Z 0x8f0fb0ef%Z 0x995fb0ef%Z 0x87df30ef%Z 0xeb8fb0ef%Z 0xfa1fa0ef%Z 0x841f30ef%Z 0xe7cfb0ef%Z 0xf69fa0ef%Z 0xf5dfa0ef%Z 0xaf9fa0ef%Z 0xfffb8517%Z 0xddc53407%Z 0xdd0fb0ef%Z 0xf5cfb0ef%Z 0xf58fb0ef%Z 0xa59fa0ef%Z 0xdc1fa0ef%Z 0xd54fb0ef%Z 0xe14fb0ef%Z 0x9d1fa0ef%Z 0xcf8fb0ef%Z 0x504000ef%Z 0xc3dfa0ef%Z 0xca4fb0ef%Z 0xc8cfb0ef%Z 0xec9fb0ef%Z 0xd69fa0ef%Z 0xe04fb0ef%Z 0xd39fa0ef%Z 0xddcfb0ef%Z 0xdc0fb0ef%Z 0xb89fa0ef%Z 0xdb8f30ef%Z 0x6e00006f%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x59ad8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x59ad8 /\ 0x59ad8 + 7584 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_e_errno_loc : CodeAt.code_at rsegs e_errno_loc QzQg.Mq0.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_extendsftf2 : CodeAt.code_at rsegs e_extendsftf2 QzQg.Mq0.extendsftf2_code.  Proof. StepGen.code_at_vm. Qed.
Definition RFI_rpos := @RFI_rpos.
Definition rf_getc_fast := @rf_getc_fast.
Definition rf_getc_fast_lt := @rf_getc_fast_lt.
Definition rf_getc_slow := @rf_getc_slow.
Definition RFI_getc := @RFI_getc.
Definition shgetc_callJ := @shgetc_callJ.
End GwI.

Local Strategy 1000 [FUEL_RING FUEL_SCALE df_dnk_loop df_dn_loop df_dni_loop df_upk_loop df_up_loop df_tz_loop df_al_loop df_pad_loop df_asm_loop df_dig_loop df_rz_loop df_lz_loop].

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

Local Ltac lia ::= first [ zify_prune_fast; intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs; Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
| zify_prune_fast; Zify.zify; xlia zchecker
| Zify.zify; xlia zchecker ].

Local Ltac solve_load_base ::=
match goal with
| |- context [ov_read_bytes ?segs ?m ?a ?n] =>
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| H : ro_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
end
| HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
cbv delta [wa] in HR;
first [ rewrite HR
| replace (ov_read_bytes segs m a n) with (Some bs)
by (rewrite <- HR; f_equal; word_eq_tac) ]
end
end;
load_post.
Local Ltac solve_store ::=
match goal with
| |- context [store_ok ?segs ?m ?a ?n] =>
rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
let E := addr_expr a in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff E A in
lazymatch k with Zneg _ => fail | _ => idtac end;
let kn := eval vm_compute in (Z.to_nat k) in
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
cbv beta iota;
match goal with
| |- context [write_to_mem m a ?bs] =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
end
end
| HS : store_ok segs m ?a' n = true |- _ =>
cbv delta [wa] in HS;
first [ rewrite HS
| replace (store_ok segs m a n) with true
by (rewrite <- HS; f_equal; word_eq_tac);
try replace (write_to_mem m a) with (write_to_mem m a')
by (f_equal; word_eq_tac) ];
cbv beta iota
end
end.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation RFJ' := (RFJ T txt p true J).

Local Notation ctx_all := (@QmCU.ctx_all ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).
Local Notation Fok_refl := (@QmCU.Fok_refl F).
Local Notation Fok_set := (@QmCU.Fok_set F).
Local Notation fs_post := (@QmCU.fs_post ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F Fp T p J txt canary fR yR).
Local Notation zbytes_len := (@QmCU.zbytes_len txt).
Local Notation winv := (@QmCU.winv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F m0 Fp T p J txt canary).
Local Notation FS_tail := (@QmCU.FS_tail pok fuelc).
Local Notation S_618 := (@QmCU.S_618 ra q gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary pok fuelc f0 kmin0 c0 fR yR).

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.
Notation POST := (fs_post m0).

Hypothesis HS_618 : S_618.

#[using="Type"] Lemma getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_stdio) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_stdio)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq3.ssp_cells) (@QxDK.ssp_cells) (Q6nq.gwt_def (@Q6Iq.Mq2.ssp_cells) (@QxDK.ssp_cells) (Q6nq.gwt_def (@QQRC.Mq3.rf_cells) (@QxDK.rf_cells) (Q6nq.gwt_def (@QzQg.Mq0.fs_post) (@QmCU.fs_post) (Q6nq.gwt_def (@Q6Iq.Mq2.fs_post) (@QmCU.fs_post) (Q6nq.gwt_def (@QzQg.Mq0.fch) (@QmCU.fch) (Q6nq.gwt_def (@QzQg.Mq0.ctx_all) (@QmCU.ctx_all) (Q6nq.gwt_def (@QZxv.Mql.RFJ) (@Q3qs.RFJ) (Q6nq.gwt_def (@Q6Iq.Mq2.RFJ) (@Q3qs.RFJ) (Q6nq.gwt_def (@QzQg.Mq0.RERRNO) (@QmCU.RERRNO) (Q6nq.gwt_def (@Q6Iq.Mq2.RERRNO) (@QmCU.RERRNO) (Q6nq.gwt_def (@QzQg.Mq0.FS_DEPTH) (@QmCU.FS_DEPTH) (Q6nq.gwt_def (@QzQg.Mq0.FLOATSCAN) (@QmCU.FLOATSCAN) (Q6nq.gwt_def (@Q6Iq.Mq2.FLOATSCAN) (@QmCU.FLOATSCAN) Q6nq.gwt_nil)))))))))))))).
#[using="Type"] Lemma getc_rpos2 : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq2.getc_rpos2) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_rpos2) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_rpos2)]. Qed.

#[using="Hnul Hnum"] Lemma getc_fch : forall kmin c f, RFJ' kmin c f -> c <> 0%Z -> fch (fst (sh_getc f)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_fch) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.getc_fch)]. Qed.
Definition fch_ok (c : Z) : bool :=
(negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 73) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 78) &&
negb (Z.land (Z.land c 18446744073709551615) 18446744073709551583 =? 88) &&
negb (Z.land c 18446744073709551583 =? 73) && negb (Z.land c 18446744073709551583 =? 78) && negb (Z.land c 18446744073709551583 =? 88) &&
negb (Z.lor c 32 =? 105) && negb (Z.lor c 32 =? 110) && negb (Z.lor c 32 =? 120) &&
negb (m_isspace c) && negb (c =? 32) && (5 <=? (c + -9) mod 2 ^ 64))%Z.
Lemma gw_eq_fch_ok : @fch_ok = ltac:(GwInst.gw_term (@Q6Iq.Mq2.fch_ok) (@fch_ok)). Proof. unfold fch_ok, Q6Iq.Mq2.fch_ok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_fch_ok : gw_eqs.
#[using="Type"] Lemma forallb_range : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq2.forallb_range) [[@gw_eq_fch_ok__3; @gw_eq_fch_ok__2; @gw_eq_fch_ok]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.forallb_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.forallb_range)]. Qed.
#[using="Type"] Lemma numch_range : forall c, is_numch c = true -> (0 <= c < 256)%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_is_numch__3; @gw_eq_is_numch__2; @gw_eq_is_numch]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.numch_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.numch_range)]. Qed.
#[using="Type"] Lemma fch_ok_true : forall c, fch c -> fch_ok c = true.
Proof. rewrite ?gw_eq_fch_ok; ltac2:(GwEq.gw_rw [[@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_ok_true) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_ok_true)]. Qed.
#[using="Type"] Lemma fch_facts : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq2.fch_facts) [[@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]; [@gw_eq_fch_ok__3; @gw_eq_fch_ok__2; @gw_eq_fch_ok]] '([73; 78; 88; 105; 110; 120; 18446744073709551583; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) (Q6nq.gwt_unf (@M64) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_facts) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_facts)]. Qed.
#[using="Type"] Lemma fch_range : forall c, fch c -> (-1 <= c < 256)%Z.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_range) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.fch_range)]. Qed.

#[using="Type"] Lemma floatscan_front : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq2.floatscan_front) [[@gw_eq_fch_ok__3; @gw_eq_fch_ok__2; @gw_eq_fch_ok]] '([(-1074); 105; 110; 120]%Z : list Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.floatscan_front) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.floatscan_front)]. Qed.

#[using="Hp SE_T SPF SPT SG1 SG3 FRM HS_618"] Lemma L_5D0 : forall m3 (x1' x5' x6' x7' x8' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (av sg c : Z) (f : shfile) (kmin : Z),
let _ := ctx_all in
winv m3 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> (sg = 1 \/ sg = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= av < 2^64)%Z -> av <> 78%Z ->
FS_tail sg c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 sg) (Z_to_bv 64 c) (Z_to_bv 64 av) x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 614624) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 0x59c44) fc None m3 (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FS_tail__3; @gw_eq_FS_tail__2; @gw_eq_FS_tail]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_fs_post__3; @gw_eq_fs_post__2; @gw_eq_fs_post]; [@gw_eq_winv__3; @gw_eq_winv__2; @gw_eq_winv]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_5D0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_5D0)]. Qed.

#[using="ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_564 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
let _ := ctx_all in
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> (c1 = 43%Z \/ c1 = 45%Z) ->
FS_tail (1 - 2 * b2z (c1 =? 45))%Z (fst (sh_getc f1)) (snd (sh_getc f1)) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 614624) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 0x59bd8) fc None m2 (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FS_tail__3; @gw_eq_FS_tail__2; @gw_eq_FS_tail]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_fs_post__3; @gw_eq_fs_post__2; @gw_eq_fs_post]; [@gw_eq_winv__3; @gw_eq_winv__2; @gw_eq_winv]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_564) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_564)]. Qed.

#[using="ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_554 : forall m2 (x1' x5' x6' x7' x8' x11' x12' x13' x14' x15' x16' x17' x19' x25' x26' x27' x28' x29' x30' x31' : word)
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws (c1 : Z) (f1 : shfile) (k1 : Z),
let _ := ctx_all in
winv m2 j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f1 ->
RFJ' k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 -> fch c1 -> (c1 <> (-1)%Z -> 1 <= sh_rpos f1)%Z ->
(forall sg c2 f2,
(if ((c1 =? 43) || (c1 =? 45))%Z then ((1 - 2 * b2z (c1 =? 45))%Z, fst (sh_getc f1), snd (sh_getc f1)) else (1%Z, c1, f1)) = (sg, c2, f2) ->
FS_tail sg c2 f2 = Some (fR, yR)) ->
evt rsegs POST
(MS (mkR x1' SPv gp TPv x5' x6' x7' x8' (Z_to_bv 64 32) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
(Z_to_bv 64 53) x19' (Z_to_bv 64 614624) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25' x26' x27' x28' x29' x30' x31')
F (Z_to_bv 64 0x59bc8) fc None m2 (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FS_tail__3; @gw_eq_FS_tail__2; @gw_eq_FS_tail]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_fch__3; @gw_eq_fch__2; @gw_eq_fch]; [@gw_eq_fs_post__3; @gw_eq_fs_post__2; @gw_eq_fs_post]; [@gw_eq_winv__3; @gw_eq_winv__2; @gw_eq_winv]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_554) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_554)]. Qed.

#[using="HM ST0 BYT Hp Hnul Hnum HP30 T0 T1 SEP SE_T SPLO SPF SPF2 SPT SG1 SG2 SG3 Q1 FRM HS_618"] Lemma L_ENTRY : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq2.L_ENTRY) [[@gw_eq_FLOATSCAN__3; @gw_eq_FLOATSCAN__2; @gw_eq_FLOATSCAN]; [@gw_eq_FS_DEPTH__3; @gw_eq_FS_DEPTH__2; @gw_eq_FS_DEPTH]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_fs_post__3; @gw_eq_fs_post__2; @gw_eq_fs_post]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_fch_ok__3; @gw_eq_fch_ok__2; @gw_eq_fch_ok]] '(@nil Z) '(Q6nq.gwt_zc RERRNO (Q6nq.gwt_zc RATP (Q6nq.gwt_zc FS_DEPTH (Q6nq.gwt_zc FLOATSCAN (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_FLOATSCAN__3; @gw_eq_FLOATSCAN__2; @gw_eq_FLOATSCAN]; [@gw_eq_FS_DEPTH__3; @gw_eq_FS_DEPTH__2; @gw_eq_FS_DEPTH]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_RERRNO__3; @gw_eq_RERRNO__2; @gw_eq_RERRNO]; [@gw_eq_RFJ__3; @gw_eq_RFJ__2; @gw_eq_RFJ]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_fs_post__3; @gw_eq_fs_post__2; @gw_eq_fs_post]; [@gw_eq_rf_cells__3; @gw_eq_rf_cells__2; @gw_eq_rf_cells]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_ENTRY) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq2.L_ENTRY)]. Qed.

End Floatscan.
Lemma gw_eq_fch_ok__2 : @fch_ok = ltac:(GwInst.gw_term (@Q6Iq.Mq2.fch_ok) (@fch_ok)). Proof. unfold fch_ok, Q6Iq.Mq2.fch_ok; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_fch_ok__2 : gw_eqs.
