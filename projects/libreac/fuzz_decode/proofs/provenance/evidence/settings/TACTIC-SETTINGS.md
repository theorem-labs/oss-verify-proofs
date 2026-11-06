# Tactic-level settings of fuzz_decode (recorded once, stream lead rule 1i-ter)

A tactic-level setting (an `Ltac ... ::=` redefinition, an Opaque / Transparent / Strategy hint, a Hint, zify or
lia flag) changes proof search, not what the kernel checks. Per rule 1i-ter it is recorded here once; it is not
made Local and not rebuilt. A kernel-level setting is never accepted: this run found none.

- Tree: `proofs/libreac/fuzz_decode/lib` at commit `3f64815aead2`, every `.v` file of the lib (2673 files).
- Tool: `global_settings.py` v10, sha256 `439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242` (release `global_settings-439f8e3bd463`; its self-test and 20
  real-file controls ran first and passed). Command: `global_settings.py WT <every lib .v file>`; exit code 0.
- `SUMMARY: 2673 files read of 2673 given; ESCAPES 1229; PLAIN 4735; UNMEASURED 4; KERNEL 0; levels TACTIC 5154, OPTION 814; HINTS 227 (report only, tactic-level)`
- Paths below are relative to `proofs/libreac/fuzz_decode/lib`.

## ESCAPES, by setting

| setting | level | rows | files |
|---|---|---|---|
| `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` | TACTIC | 1100 | 453 |
| `Ltac numconst ::=` | TACTIC | 92 | 92 |
| `Ltac drv_anch ::=` | TACTIC | 6 | 6 |
| `#[global] Set Default Proof Mode .` | OPTION | 4 | 4 |
| `Global Opaque` | TACTIC | 2 | 2 |
| `Ltac Lia.lia ::=` | TACTIC | 2 | 2 |
| `Ltac Lia.nia ::=` | TACTIC | 2 | 2 |
| `#[global] Unset Lia Cache.` | TACTIC | 1 | 1 |
| `#[global] Unset Nia Cache.` | TACTIC | 1 | 1 |
| `#[global] Unset Nra Cache.` | TACTIC | 1 | 1 |
| `Ltac Corelib.Init.Tauto.tauto ::=` | TACTIC | 1 | 1 |
| `Ltac YM03.lf_lia_orig ::=` | TACTIC | 1 | 1 |
| `Ltac Z.euclidean_division_equations_cleanup ::=` | TACTIC | 1 | 1 |
| `Ltac Zify.zify_internal_to_euclidean_division_equations ::=` | TACTIC | 1 | 1 |
| `Ltac Zify.zify_pre_hook ::=` | TACTIC | 1 | 1 |
| `Ltac exec_pre i ::=` | TACTIC | 1 | 1 |
| `Ltac is_concrete_map R ::=` | TACTIC | 1 | 1 |
| `Ltac lia ::=` | TACTIC | 1 | 1 |
| `Ltac map_cbv_get ::=` | TACTIC | 1 | 1 |
| `Ltac map_cbv_set ::=` | TACTIC | 1 | 1 |
| `Ltac mem_after_store ::=` | TACTIC | 1 | 1 |
| `Ltac mem_after_store_opt ::=` | TACTIC | 1 | 1 |
| `Ltac post_step i ::=` | TACTIC | 1 | 1 |
| `Ltac sim_destruct e ::=` | TACTIC | 1 | 1 |
| `Ltac sim_hook ::=` | TACTIC | 1 | 1 |
| `Ltac solve_load ::=` | TACTIC | 1 | 1 |
| `Ltac stdpp.bitvector.definitions.solve_BvWf ::=` | TACTIC | 1 | 1 |
| `Ltac transport_chunks segs m a bs ::=` | TACTIC | 1 | 1 |

## ESCAPES, every row (file: lines)

### `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` (TACTIC)

- A/AB14.v: 15, 140
- A/AB15.v: 15, 264
- A/AB16.v: 16, 295
- A/AB17.v: 17, 66, 350
- A/AB18.v: 17, 288, 379
- A/AB1a.v: 17, 202, 238
- A/AB1b.v: 17, 203, 239
- A/AB1c.v: 17, 197, 233
- A/AB1d.v: 17, 316
- A/AB1f.v: 18, 436
- A/AD1d.v: 23
- A/AD1e.v: 23
- A/AD1f.v: 24
- A/AD1g.v: 22
- A/AD1z.v: 21
- A/AD23.v: 21
- A/AD25.v: 18
- A/AD2k.v: 25
- A/AE20.v: 14, 530
- A/AE2q.v: 27
- A/AE2r.v: 27
- A/AE2s.v: 29
- A/AE2t.v: 29
- A/AE2u.v: 29
- A/AE2v.v: 29
- A/AE2w.v: 29
- A/AE2x.v: 28
- A/AE2z.v: 29
- A/AE30.v: 27
- A/AE31.v: 27
- A/AE32.v: 28
- A/AE33.v: 28
- A/AE35.v: 30
- A/AE6k.v: 27
- A/AE6l.v: 27
- A/AE6m.v: 27
- A/AE6n.v: 27
- A/AE6o.v: 27
- A/AE6p.v: 27
- A/AE6q.v: 27
- A/AE6r.v: 27
- A/AE6s.v: 27
- A/AE6t.v: 27
- A/AE6u.v: 27
- A/AE6v.v: 27
- A/AE6w.v: 28
- A/AE6x.v: 29
- A/AE6y.v: 28
- A/AE6z.v: 28
- A/AE70.v: 28
- A/AE71.v: 27
- A/AE72.v: 27
- A/AE73.v: 27
- A/AE74.v: 28
- A/AE75.v: 27
- A/AE76.v: 27
- A/AE77.v: 27
- A/AE78.v: 28
- A/AE79.v: 27
- A/AE7a.v: 27
- A/AE7b.v: 27
- A/AE7c.v: 28
- A/AE7d.v: 28
- A/AE7e.v: 28
- A/AF0n.v: 17
- A/AF0o.v: 17, 118
- A/AFes.v: 29
- A/AFf4.v: 23
- A/AFf5.v: 29
- A/AFf6.v: 33
- A/AFf7.v: 33
- A/AFf8.v: 30
- A/AFf9.v: 33
- A/AFfa.v: 29
- A/AFfb.v: 27
- A/AFfc.v: 32
- A/AFfd.v: 29
- A/AFfe.v: 33
- A/AFfs.v: 24
- A/AFg4.v: 30
- A/AFg8.v: 30
- A/AFg9.v: 34
- A/AFgy.v: 47
- A/AFgz.v: 47
- A/AFh2.v: 35
- A/AFh3.v: 29
- A/AFh7.v: 47
- A/AFhd.v: 18
- A/AFhe.v: 29
- A/AFhf.v: 20
- A/AFhg.v: 29
- A/AFhi.v: 29
- A/AFhj.v: 29
- A/AFhk.v: 29
- A/AFhl.v: 30
- A/Prog/YC1i.v: 28
- A/Prog/YC4b.v: 24
- A/Rt/StackMalloc0.v: 28
- A/Rt/StackMalloc0Tbl.v: 25
- B/YA02.v: 18
- B/YA03.v: 20, 174, 177, 198, 200, 248, 260
- B/YA07.v: 25
- B/YA08.v: 23, 311, 314, 824, 825, 1133, 1139, 1302, 1304
- B/YA09.v: 24, 268, 271, 278, 279, 286, 287, 1368, 1370, 1459, 1461, 1463, 1465, 1645, 1646, 2041, 2043, 2123, 2129, 2162, 2163, 2202, 2204, 2213, 2215, 2225, 2227, 2250, 2253, 2290, 2292, 2380, 2381, 2400, 2407, 2730, 2735, 2745, 2746, 2757, 2758, 2800, 2805, 2815, 2816, 2827, 2828, 2873, 2875, 2877, 2879, 3339, 3341
- B/YA0a.v: 21
- B/YA0b.v: 19
- B/YA0d.v: 15
- B/YA0e.v: 21, 26, 27, 36, 244, 246, 253, 256, 287, 299, 882, 883, 1058, 1063, 1090, 1095, 1102, 1104, 1108, 1110, 1125, 1126, 1150, 1155, 1168, 1170, 1175, 1176, 1266, 1271, 1296, 1301, 1308, 1310, 1314, 1316, 1331, 1332, 1356, 1361, 1374, 1376, 1381, 1382, 1444, 1446, 1460, 1462, 1476, 1479, 1482, 1497, 1767, 1771, 1789, 1800, 2197, 2199, 2208, 2211, 2267, 2273, 2766, 2770, 3393, 3398, 3471, 3473, 3518, 3519, 3743, 3758
- B/YA0f.v: 22, 263, 267, 1023, 1025, 1243, 1245, 1513, 1518, 1528, 1529, 1597, 1598, 1602, 1603, 1609, 1610, 1614, 1615, 1651, 1655, 1666, 1667, 1715, 1716, 1717, 1718, 1726, 1727, 1751, 1752, 1753, 1754, 1877, 1878, 1882, 1883, 1889, 1890, 1894, 1895, 1904, 1905, 1938, 1942, 1953, 1954, 2002, 2003, 2004, 2005, 2013, 2014, 2038, 2039, 2040, 2041
- B/YA0j.v: 77, 94, 101, 105, 107
- B/YB14.v: 14, 139
- B/YB15.v: 14, 263
- B/YB16.v: 14, 293
- B/YB17.v: 16, 65, 349
- B/YB18.v: 16, 287, 378
- B/YB1a.v: 16, 201, 237
- B/YB1b.v: 16, 202, 238
- B/YB1c.v: 16, 196, 232
- B/YB1d.v: 16, 315
- B/YB1f.v: 17, 435
- B/YD1d.v: 21
- B/YD1e.v: 22
- B/YD1f.v: 23
- B/YD1g.v: 22
- B/YD1z.v: 22
- B/YD23.v: 22
- B/YD25.v: 20
- B/YD2k.v: 23
- B/YE20.v: 13, 529
- B/YE2q.v: 27
- B/YE2r.v: 27
- B/YE2s.v: 28
- B/YE2t.v: 28
- B/YE2u.v: 28
- B/YE2v.v: 28
- B/YE2w.v: 28
- B/YE2x.v: 28
- B/YE2z.v: 28
- B/YE30.v: 27
- B/YE31.v: 27
- B/YE32.v: 27
- B/YE33.v: 27
- B/YE35.v: 28
- B/YE6k.v: 27
- B/YE6l.v: 27
- B/YE6m.v: 27
- B/YE6n.v: 27
- B/YE6o.v: 27
- B/YE6p.v: 27
- B/YE6q.v: 27
- B/YE6r.v: 27
- B/YE6s.v: 27
- B/YE6t.v: 27
- B/YE6u.v: 27
- B/YE6v.v: 27
- B/YE6w.v: 27
- B/YE6x.v: 28
- B/YE6y.v: 27
- B/YE6z.v: 27
- B/YE70.v: 27
- B/YE71.v: 27
- B/YE72.v: 27
- B/YE73.v: 27
- B/YE74.v: 27
- B/YE75.v: 27
- B/YE76.v: 27
- B/YE77.v: 27
- B/YE78.v: 27
- B/YE79.v: 27
- B/YE7a.v: 27
- B/YE7b.v: 27
- B/YE7c.v: 27
- B/YE7d.v: 28
- B/YE7e.v: 27
- B/YF0n.v: 16
- B/YF0o.v: 16, 117
- B/YFes.v: 25
- B/YFf4.v: 20
- B/YFf5.v: 27
- B/YFf6.v: 30
- B/YFf7.v: 30
- B/YFf8.v: 28
- B/YFf9.v: 30
- B/YFfa.v: 27
- B/YFfb.v: 25
- B/YFfc.v: 29
- B/YFfd.v: 27
- B/YFfe.v: 30
- B/YFfs.v: 22
- B/YFg4.v: 26
- B/YFg8.v: 26
- B/YFg9.v: 31
- B/YFgy.v: 45
- B/YFgz.v: 45
- B/YFh2.v: 33
- B/YFh3.v: 27
- B/YFh7.v: 45
- B/YFhd.v: 17
- B/YFhe.v: 27
- B/YFhf.v: 19
- B/YFhg.v: 25
- B/YFhi.v: 27
- B/YFhj.v: 27
- B/YFhk.v: 27
- B/YFhl.v: 26
- Reusable/YA02.v: 19
- Reusable/YA03.v: 21, 175, 178, 199, 201, 249, 261
- Reusable/YA07.v: 26
- Reusable/YA08.v: 24, 312, 315, 825, 826, 1134, 1140, 1303, 1305
- Reusable/YA09.v: 25, 269, 272, 279, 280, 287, 288, 1369, 1371, 1460, 1462, 1464, 1466, 1646, 1647, 2042, 2044, 2124, 2130, 2163, 2164, 2203, 2205, 2214, 2216, 2226, 2228, 2251, 2254, 2291, 2293, 2381, 2382, 2401, 2408, 2731, 2736, 2746, 2747, 2758, 2759, 2801, 2806, 2816, 2817, 2828, 2829, 2874, 2876, 2878, 2880, 3340, 3342
- Reusable/YA0a.v: 22
- Reusable/YA0b.v: 20
- Reusable/YA0d.v: 16
- Reusable/YA0e.v: 22, 27, 28, 37, 245, 247, 254, 257, 288, 300, 883, 884, 1059, 1064, 1091, 1096, 1103, 1105, 1109, 1111, 1126, 1127, 1151, 1156, 1169, 1171, 1176, 1177, 1267, 1272, 1297, 1302, 1309, 1311, 1315, 1317, 1332, 1333, 1357, 1362, 1375, 1377, 1382, 1383, 1445, 1447, 1461, 1463, 1477, 1480, 1483, 1498, 1768, 1772, 1790, 1801, 2198, 2200, 2209, 2212, 2268, 2274, 2767, 2771, 3394, 3399, 3472, 3474, 3519, 3520, 3744, 3759
- Reusable/YA0f.v: 23, 264, 268, 1024, 1026, 1244, 1246, 1514, 1519, 1529, 1530, 1598, 1599, 1603, 1604, 1610, 1611, 1615, 1616, 1652, 1656, 1667, 1668, 1716, 1717, 1718, 1719, 1727, 1728, 1752, 1753, 1754, 1755, 1878, 1879, 1883, 1884, 1890, 1891, 1895, 1896, 1905, 1906, 1939, 1943, 1954, 1955, 2003, 2004, 2005, 2006, 2014, 2015, 2039, 2040, 2041, 2042
- Reusable/YA0j.v: 78, 95, 102, 106, 108
- Reusable/YE08.v: 14, 311
- Reusable/YF0v.v: 16
- Reusable/YFk4.v: 340, 349
- Reusable/YI0s.v: 177
- Reusable/YI67.v: 20
- Reusable/YK0a.v: 339, 348
- Reusable/YK0b.v: 18
- Reusable/YL0l.v: 20
- Reusable/YL0l_cfw.v: 18
- Reusable/YL0o.v: 19
- Reusable/YL0o_cfw.v: 16
- Reusable/YL0s.v: 19
- Reusable/YL10.v: 21, 207
- Reusable/YL10_cfw.v: 19, 176
- Reusable/YL10_cfwi.v: 19, 176
- Reusable/YL11.v: 21, 398
- Reusable/YL11_cfw.v: 20, 331
- Reusable/YL11_cfwi.v: 20, 331
- Reusable/YL12.v: 21, 207
- Reusable/YL12_cfw.v: 19, 176
- Reusable/YL12_cfwi.v: 19, 176
- Reusable/YL13.v: 21, 255
- Reusable/YL13_cfw.v: 19, 215
- Reusable/YL13_cfwi.v: 19, 215
- Reusable/YL14.v: 21, 301
- Reusable/YL14_cfw.v: 19, 252
- Reusable/YL14_cfwi.v: 19, 252
- Reusable/YL15.v: 21, 347
- Reusable/YL15_cfw.v: 19, 289
- Reusable/YL15_cfwi.v: 19, 289
- Reusable/YL16.v: 21, 398
- Reusable/YL16_cfw.v: 20, 331
- Reusable/YL16_cfwi.v: 20, 331
- Reusable/YL17.v: 21, 452
- Reusable/YL17_cfw.v: 20, 376
- Reusable/YL17_cfwi.v: 20, 376
- Reusable/YL18.v: 21, 503
- Reusable/YL18_cfw.v: 20, 418
- Reusable/YL18_cfwi.v: 20, 418
- Reusable/YL19.v: 21, 554
- Reusable/YL19_cfw.v: 20, 460
- Reusable/YL19_cfwi.v: 20, 460
- Reusable/YN04.v: 19, 770
- Reusable/YN06.v: 24, 1087
- Reusable/YN06_cf.v: 25, 1088
- Reusable/YN0a.v: 23, 327
- Reusable/YN0a_cf.v: 24, 328
- Reusable/YN0c.v: 29, 795
- Reusable/YN0c_cf.v: 30, 796
- Reusable/YN0e.v: 27, 632
- Reusable/YN0e_cf.v: 28, 635
- Reusable/YN0h.v: 22, 407
- Reusable/YN0h_cf.v: 23, 408
- Reusable/YN0i.v: 28, 2688
- Reusable/YN0i_cf.v: 29, 2705
- Reusable/YN0k.v: 25, 1140
- Reusable/YN0k_cf.v: 26, 1141
- Reusable/YN0l.v: 25, 1234
- Reusable/YN0l_cf.v: 26, 1235
- Reusable/YN0m.v: 26, 763
- Reusable/YN0m_cf.v: 27, 764
- Reusable/YN0n.v: 26, 816
- Reusable/YN0n_cf.v: 27, 817
- Reusable/YN0o.v: 26, 662
- Reusable/YN0o_cf.v: 27, 663
- Reusable/YN0p.v: 25, 226
- Reusable/YN0p_cf.v: 26, 227
- Reusable/YN0q.v: 26, 206
- Reusable/YN0q_cf.v: 27, 207
- Reusable/YN0w.v: 25, 64
- Reusable/YN0w_cf.v: 26, 65
- Reusable/YN0x.v: 27, 352
- Reusable/YN0x_cf.v: 28, 353
- Reusable/YN0z.v: 26, 1036
- Reusable/YN0z_cf.v: 27, 1037
- Reusable/YN12.v: 27, 72
- Reusable/YN12_cf.v: 28, 73
- Reusable/YN13.v: 26, 795
- Reusable/YN13_cf.v: 27, 796
- Reusable/YN14.v: 26, 1059
- Reusable/YN14_cf.v: 27, 1060
- Reusable/YN15.v: 29, 400
- Reusable/YN15_cf.v: 30, 403
- Reusable/YN16.v: 28, 893
- Reusable/YN16_cf.v: 29, 894
- Reusable/YN17.v: 27, 230
- Reusable/YN17_cf.v: 28, 231
- Reusable/YN18.v: 27, 1063
- Reusable/YN18_cf.v: 28, 1064
- Reusable/YN19.v: 28, 1400
- Reusable/YN19_cf.v: 29, 1401
- Reusable/YN1a.v: 29, 1404
- Reusable/YN1a_cf.v: 30, 1405
- Reusable/YN1c.v: 17
- Reusable/YN1c_cf.v: 18
- Reusable/YN1d.v: 26, 792
- Reusable/YN1d_cf.v: 27, 793
- Reusable/YN1e.v: 29, 441
- Reusable/YN1e_cf.v: 30, 442
- Reusable/YN1f.v: 29, 2829
- Reusable/YN1f_cf.v: 30, 2830
- Reusable/YN1o.v: 17, 102
- Reusable/YN1p.v: 23, 301
- Reusable/YN1p_cf.v: 24, 302
- Reusable/YN1r.v: 24, 640
- Reusable/YN1r_cf.v: 25, 641
- Reusable/YN1s.v: 26, 360
- Reusable/YN1s_cf.v: 27, 361
- Reusable/YN1u.v: 26, 532
- Reusable/YN1u_cf.v: 27, 533
- Reusable/YN1w.v: 25, 695
- Reusable/YN1w_cf.v: 26, 696
- Reusable/YN2i.v: 18, 670
- Reusable/YN2j.v: 20, 351
- Reusable/YN2j_cf.v: 21, 352
- Reusable/YN2l.v: 20, 583
- Reusable/YN2l_cf.v: 21, 584
- Reusable/YN2m.v: 20, 964
- Reusable/YN2m_cf.v: 21, 965
- Reusable/YN2n.v: 19, 541
- Reusable/YN30.v: 18, 433
- Reusable/YN30_cf.v: 19, 434
- U/Reusable/YL0l.v: 20
- U/Reusable/YL0l_cfw.v: 18
- U/Reusable/YL0o.v: 19
- U/Reusable/YL0o_cfw.v: 16
- U/Reusable/YL0s.v: 19
- U/Reusable/YL10.v: 21, 207
- U/Reusable/YL10_cfw.v: 19, 176
- U/Reusable/YL10_cfwi.v: 19, 176
- U/Reusable/YL11.v: 21, 398
- U/Reusable/YL11_cfw.v: 20, 331
- U/Reusable/YL11_cfwi.v: 20, 331
- U/Reusable/YL12.v: 21, 207
- U/Reusable/YL12_cfw.v: 19, 176
- U/Reusable/YL12_cfwi.v: 19, 176
- U/Reusable/YL13.v: 21, 255
- U/Reusable/YL13_cfw.v: 19, 215
- U/Reusable/YL13_cfwi.v: 19, 215
- U/Reusable/YL14.v: 21, 301
- U/Reusable/YL14_cfw.v: 19, 252
- U/Reusable/YL14_cfwi.v: 19, 252
- U/Reusable/YL15.v: 21, 347
- U/Reusable/YL15_cfw.v: 19, 289
- U/Reusable/YL15_cfwi.v: 19, 289
- U/Reusable/YL16.v: 21, 398
- U/Reusable/YL16_cfw.v: 20, 331
- U/Reusable/YL16_cfwi.v: 20, 331
- U/Reusable/YL17.v: 21, 452
- U/Reusable/YL17_cfw.v: 20, 376
- U/Reusable/YL17_cfwi.v: 20, 376
- U/Reusable/YL18.v: 21, 503
- U/Reusable/YL18_cfw.v: 20, 418
- U/Reusable/YL18_cfwi.v: 20, 418
- U/Reusable/YL19.v: 21, 554
- U/Reusable/YL19_cfw.v: 20, 460
- U/Reusable/YL19_cfwi.v: 20, 460
- U/Reusable/YN04.v: 19, 770
- U/Reusable/YN06.v: 24, 1087
- U/Reusable/YN06_cf.v: 25, 1088
- U/Reusable/YN0a.v: 23, 327
- U/Reusable/YN0a_cf.v: 24, 328
- U/Reusable/YN0c.v: 29, 795
- U/Reusable/YN0c_cf.v: 30, 796
- U/Reusable/YN0e.v: 27, 632
- U/Reusable/YN0e_cf.v: 28, 635
- U/Reusable/YN0h.v: 22, 407
- U/Reusable/YN0h_cf.v: 23, 408
- U/Reusable/YN0i.v: 28, 2688
- U/Reusable/YN0i_cf.v: 29, 2705
- U/Reusable/YN0k.v: 25, 1140
- U/Reusable/YN0k_cf.v: 26, 1141
- U/Reusable/YN0l.v: 25, 1234
- U/Reusable/YN0l_cf.v: 26, 1235
- U/Reusable/YN0m.v: 26, 763
- U/Reusable/YN0m_cf.v: 27, 764
- U/Reusable/YN0n.v: 26, 816
- U/Reusable/YN0n_cf.v: 27, 817
- U/Reusable/YN0o.v: 26, 662
- U/Reusable/YN0o_cf.v: 27, 663
- U/Reusable/YN0p.v: 25, 226
- U/Reusable/YN0p_cf.v: 26, 227
- U/Reusable/YN0q.v: 26, 206
- U/Reusable/YN0q_cf.v: 27, 207
- U/Reusable/YN0w.v: 25, 64
- U/Reusable/YN0w_cf.v: 26, 65
- U/Reusable/YN0x.v: 27, 352
- U/Reusable/YN0x_cf.v: 28, 353
- U/Reusable/YN0z.v: 26, 1036
- U/Reusable/YN0z_cf.v: 27, 1037
- U/Reusable/YN12.v: 27, 72
- U/Reusable/YN12_cf.v: 28, 73
- U/Reusable/YN13.v: 26, 795
- U/Reusable/YN13_cf.v: 27, 796
- U/Reusable/YN14.v: 26, 1059
- U/Reusable/YN14_cf.v: 27, 1060
- U/Reusable/YN15.v: 29, 400
- U/Reusable/YN15_cf.v: 30, 403
- U/Reusable/YN16.v: 28, 893
- U/Reusable/YN16_cf.v: 29, 894
- U/Reusable/YN17.v: 27, 230
- U/Reusable/YN17_cf.v: 28, 231
- U/Reusable/YN18.v: 27, 1063
- U/Reusable/YN18_cf.v: 28, 1064
- U/Reusable/YN19.v: 28, 1400
- U/Reusable/YN19_cf.v: 29, 1401
- U/Reusable/YN1a.v: 29, 1404
- U/Reusable/YN1a_cf.v: 30, 1405
- U/Reusable/YN1c.v: 17
- U/Reusable/YN1c_cf.v: 18
- U/Reusable/YN1d.v: 26, 792
- U/Reusable/YN1d_cf.v: 27, 793
- U/Reusable/YN1e.v: 29, 441
- U/Reusable/YN1e_cf.v: 30, 442
- U/Reusable/YN1f.v: 29, 2829
- U/Reusable/YN1f_cf.v: 30, 2830
- U/Reusable/YN1o.v: 17, 102
- U/Reusable/YN1p.v: 23, 301
- U/Reusable/YN1p_cf.v: 24, 302
- U/Reusable/YN1r.v: 24, 640
- U/Reusable/YN1r_cf.v: 25, 641
- U/Reusable/YN1s.v: 26, 360
- U/Reusable/YN1s_cf.v: 27, 361
- U/Reusable/YN1u.v: 26, 532
- U/Reusable/YN1u_cf.v: 27, 533
- U/Reusable/YN1w.v: 25, 695
- U/Reusable/YN1w_cf.v: 26, 696
- U/Reusable/YN2i.v: 18, 670
- U/Reusable/YN2j.v: 20, 351
- U/Reusable/YN2j_cf.v: 21, 352
- U/Reusable/YN2l.v: 20, 583
- U/Reusable/YN2l_cf.v: 21, 584
- U/Reusable/YN2m.v: 20, 964
- U/Reusable/YN2m_cf.v: 21, 965
- U/Reusable/YN2n.v: 19, 541
- U/Reusable/YN30.v: 18, 433
- U/Reusable/YN30_cf.v: 19, 434

### `Ltac numconst ::=` (TACTIC)

- A/AFip.v: 162
- A/AFiq.v: 162
- A/AFir.v: 162
- A/AFis.v: 316
- A/AFit.v: 162
- A/AFiu.v: 162
- A/AFiv.v: 162
- A/AFiw.v: 162
- A/AFix.v: 162
- A/AFiy.v: 163
- A/AFiz.v: 162
- A/AFj0.v: 162
- A/AFj1.v: 163
- A/AFj2.v: 162
- A/AFj3.v: 161
- A/AFj4.v: 161
- A/AFj5.v: 161
- A/AFj6.v: 317
- A/AFj7.v: 161
- A/AFj8.v: 161
- A/AFj9.v: 161
- A/AFja.v: 161
- A/AFjb.v: 161
- A/AFjc.v: 162
- A/AFjd.v: 161
- A/AFje.v: 161
- A/AFjf.v: 162
- A/AFjg.v: 161
- A/AGc1.v: 136
- A/AGc2.v: 131
- A/AGip.v: 160
- A/AGiq.v: 160
- A/AGir.v: 160
- A/AGis.v: 317
- A/AGit.v: 158
- A/AGiu.v: 160
- A/AGiv.v: 158
- A/AGj2.v: 166
- A/AGj3.v: 159
- A/AGj4.v: 168
- A/AGj5.v: 159
- A/AGj6.v: 316
- A/AGj7.v: 157
- A/AGj8.v: 159
- A/AGj9.v: 157
- A/AGjg.v: 170
- B/AGc1.v: 137
- B/AGc2.v: 132
- B/AGip.v: 161
- B/AGiq.v: 161
- B/AGir.v: 161
- B/AGis.v: 318
- B/AGit.v: 159
- B/AGiu.v: 161
- B/AGiv.v: 159
- B/AGj2.v: 166
- B/AGj3.v: 160
- B/AGj4.v: 169
- B/AGj5.v: 160
- B/AGj6.v: 317
- B/AGj7.v: 158
- B/AGj8.v: 160
- B/AGj9.v: 158
- B/AGjg.v: 170
- B/YFip.v: 160
- B/YFiq.v: 160
- B/YFir.v: 160
- B/YFis.v: 314
- B/YFit.v: 160
- B/YFiu.v: 160
- B/YFiv.v: 160
- B/YFiw.v: 160
- B/YFix.v: 160
- B/YFiy.v: 161
- B/YFiz.v: 160
- B/YFj0.v: 160
- B/YFj1.v: 161
- B/YFj2.v: 160
- B/YFj3.v: 159
- B/YFj4.v: 159
- B/YFj5.v: 159
- B/YFj6.v: 315
- B/YFj7.v: 159
- B/YFj8.v: 159
- B/YFj9.v: 159
- B/YFja.v: 159
- B/YFjb.v: 159
- B/YFjc.v: 160
- B/YFjd.v: 159
- B/YFje.v: 159
- B/YFjf.v: 160
- B/YFjg.v: 159

### `Ltac drv_anch ::=` (TACTIC)

- Reusable/YL0l.v: 242
- Reusable/YL0s.v: 216
- Reusable/YL0u.v: 39
- U/Reusable/YL0l.v: 242
- U/Reusable/YL0s.v: 216
- U/Reusable/YL0u.v: 39

### `#[global] Set Default Proof Mode .` (OPTION)

- Lib/LiaSec.v: 9
- Lib/LiaTwx2.v: 10
- Lib/WeqGuard.v: 8
- Lib/Zifyk6b.v: 6

### `Global Opaque` (TACTIC)

- Reusable/YK0c.v: 668
- Reusable/YQ04.v: 62

### `Ltac Lia.lia ::=` (TACTIC)

- Reusable/YM03.v: 182
- Reusable/YM05.v: 63

### `Ltac Lia.nia ::=` (TACTIC)

- Reusable/YM03.v: 186
- Reusable/YM05.v: 68

### `#[global] Unset Lia Cache.` (TACTIC)

- Lib/LiaTwx2.v: 18

### `#[global] Unset Nia Cache.` (TACTIC)

- Lib/LiaTwx2.v: 19

### `#[global] Unset Nra Cache.` (TACTIC)

- Lib/LiaTwx2.v: 20

### `Ltac Corelib.Init.Tauto.tauto ::=` (TACTIC)

- Reusable/YM03.v: 200

### `Ltac YM03.lf_lia_orig ::=` (TACTIC)

- Reusable/YM04.v: 36

### `Ltac Z.euclidean_division_equations_cleanup ::=` (TACTIC)

- Lib/LiaTwx2.v: 109

### `Ltac Zify.zify_internal_to_euclidean_division_equations ::=` (TACTIC)

- Lib/LiaTwx2.v: 117

### `Ltac Zify.zify_pre_hook ::=` (TACTIC)

- Lib/Zifyk6b.v: 48

### `Ltac exec_pre i ::=` (TACTIC)

- Prog/RcBraidLib.v: 18

### `Ltac is_concrete_map R ::=` (TACTIC)

- Lib/Tac.v: 18

### `Ltac lia ::=` (TACTIC)

- Lib/LiaTwx2.v: 187

### `Ltac map_cbv_get ::=` (TACTIC)

- Lib/Tac.v: 24

### `Ltac map_cbv_set ::=` (TACTIC)

- Lib/Tac.v: 25

### `Ltac mem_after_store ::=` (TACTIC)

- Lib/Tac.v: 97

### `Ltac mem_after_store_opt ::=` (TACTIC)

- Lib/Tac.v: 147

### `Ltac post_step i ::=` (TACTIC)

- Prog/RcBraidLib.v: 48

### `Ltac sim_destruct e ::=` (TACTIC)

- Reusable/YQ03.v: 15

### `Ltac sim_hook ::=` (TACTIC)

- Reusable/YQ03.v: 226

### `Ltac solve_load ::=` (TACTIC)

- Lib/Tac.v: 48

### `Ltac stdpp.bitvector.definitions.solve_BvWf ::=` (TACTIC)

- Reusable/YM05.v: 131

### `Ltac transport_chunks segs m a bs ::=` (TACTIC)

- Lib/Tac.v: 52

## UNMEASURED (no locality the tool can decide)

- A/Prog/PaSym.v:179 OPTION `Arguments`
- Lib/Exec.v:136 OPTION `Arguments`
- Lib/ExecF.v:321 OPTION `Arguments`
- Reusable/YG0f.v:88 OPTION `Arguments`

## KERNEL

None (0 rows).
