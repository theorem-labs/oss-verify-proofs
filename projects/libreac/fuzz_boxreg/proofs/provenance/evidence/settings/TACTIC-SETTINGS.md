# Tactic-level settings of fuzz_boxreg (recorded once, stream lead rule 1i-ter)

A tactic-level setting (an `Ltac ... ::=` redefinition, an Opaque / Transparent / Strategy hint, a Hint, zify or
lia flag) changes proof search, not what the kernel checks. Per rule 1i-ter it is recorded here once; it is not
made Local and not rebuilt. A kernel-level setting is never accepted: this run found none.

- Tree: `proofs/libreac/fuzz_boxreg/lib` at commit `b2e59f3b3308`, every `.v` file of the lib (2895 files).
- Tool: `global_settings.py` v10, sha256 `439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242` (release `global_settings-439f8e3bd463`; its self-test and 20
  real-file controls ran first and passed). Command: `global_settings.py WT <every lib .v file>`; exit code 0.
- `SUMMARY: 2895 files read of 2895 given; ESCAPES 1139; PLAIN 5542; UNMEASURED 13; KERNEL 0; levels TACTIC 5977, OPTION 717; HINTS 246 (report only, tactic-level)`
- Paths below are relative to `proofs/libreac/fuzz_boxreg/lib`.

## ESCAPES, by setting

| setting | level | rows | files |
|---|---|---|---|
| `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` | TACTIC | 904 | 454 |
| `Ltac mseq ::=` | TACTIC | 72 | 70 |
| `Ltac numconst ::=` | TACTIC | 56 | 56 |
| `#[global] Set Default Proof Mode .` | OPTION | 9 | 9 |
| `Ltac drv_anch ::=` | TACTIC | 6 | 6 |
| `Ltac transport_chunks segs m a bs ::=` | TACTIC | 6 | 6 |
| `#[global] Unset Lia Cache.` | TACTIC | 4 | 4 |
| `#[global] Unset Nia Cache.` | TACTIC | 4 | 4 |
| `#[global] Unset Nra Cache.` | TACTIC | 4 | 4 |
| `Ltac Lia.nia ::=` | TACTIC | 4 | 4 |
| `Ltac Z.euclidean_division_equations_cleanup ::=` | TACTIC | 4 | 4 |
| `Ltac Zify.zify_internal_to_euclidean_division_equations ::=` | TACTIC | 4 | 4 |
| `Ltac is_concrete_map R ::=` | TACTIC | 4 | 4 |
| `Ltac lia ::=` | TACTIC | 4 | 4 |
| `Ltac map_cbv_get ::=` | TACTIC | 4 | 4 |
| `Ltac map_cbv_set ::=` | TACTIC | 4 | 4 |
| `Ltac mem_after_store ::=` | TACTIC | 4 | 4 |
| `Ltac mem_after_store_opt ::=` | TACTIC | 4 | 4 |
| `Ltac solve_load ::=` | TACTIC | 4 | 4 |
| `Ltac Zify.zify_pre_hook ::=` | TACTIC | 3 | 3 |
| `Ltac addr_diff E A ::=` | TACTIC | 3 | 3 |
| `Global Opaque` | TACTIC | 2 | 2 |
| `Ltac Lia.lia ::=` | TACTIC | 2 | 2 |
| `Ltac step_core segs R F pc fc rv m ro ::=` | TACTIC | 2 | 2 |
| `Ltac transport_after_call segs m m' MU WM ::=` | TACTIC | 2 | 2 |
| `Ltac zs_idioms ::=` | TACTIC | 2 | 1 |
| `Ltac zs_idioms_in H ::=` | TACTIC | 2 | 1 |
| `Ltac zstep ::=` | TACTIC | 2 | 2 |
| `Ltac Corelib.Init.Tauto.tauto ::=` | TACTIC | 1 | 1 |
| `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.simp_regs ::=` | TACTIC | 1 | 1 |
| `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n` | TACTIC | 1 | 1 |
| `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_fast ::=` | TACTIC | 1 | 1 |
| `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_with rp rpm vh ::=` | TACTIC | 1 | 1 |
| `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.zstep ::=` | TACTIC | 1 | 1 |
| `Ltac YM03.lf_lia_orig ::=` | TACTIC | 1 | 1 |
| `Ltac model_reg_tac n X mexpr ::=` | TACTIC | 1 | 1 |
| `Ltac sim_destruct e ::=` | TACTIC | 1 | 1 |
| `Ltac sim_hook ::=` | TACTIC | 1 | 1 |
| `Ltac stdpp.bitvector.definitions.solve_BvWf ::=` | TACTIC | 1 | 1 |
| `Ltac step ::=` | TACTIC | 1 | 1 |
| `Ltac zs_wrap e ::=` | TACTIC | 1 | 1 |
| `Ltac zs_wrap_in e H ::=` | TACTIC | 1 | 1 |

## ESCAPES, every row (file: lines)

### `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` (TACTIC)

- A/AB14.v: 14, 139
- A/AB15.v: 14, 263
- A/AB16.v: 15, 294
- A/AB17.v: 16, 65, 349
- A/AB18.v: 16, 287, 378
- A/AB1a.v: 16, 201, 237
- A/AB1b.v: 16, 202, 238
- A/AB1c.v: 16, 196, 232
- A/AB1d.v: 16, 315
- A/AB1f.v: 17, 435
- A/AD1d.v: 21
- A/AD1e.v: 22
- A/AD1f.v: 24
- A/AD1g.v: 22
- A/AD1z.v: 20
- A/AD23.v: 20
- A/AD25.v: 17
- A/AD2k.v: 42
- A/AE20.v: 13, 529
- A/AE2q.v: 26
- A/AE2r.v: 26
- A/AE2s.v: 28
- A/AE2t.v: 28
- A/AE2u.v: 28
- A/AE2v.v: 28
- A/AE2w.v: 28
- A/AE2x.v: 27
- A/AE2z.v: 28
- A/AE30.v: 26
- A/AE31.v: 26
- A/AE32.v: 26
- A/AE33.v: 26
- A/AE35.v: 28
- A/AE6k.v: 26
- A/AE6l.v: 26
- A/AE6m.v: 26
- A/AE6n.v: 26
- A/AE6o.v: 26
- A/AE6p.v: 26
- A/AE6q.v: 26
- A/AE6r.v: 26
- A/AE6s.v: 26
- A/AE6t.v: 26
- A/AE6u.v: 26
- A/AE6v.v: 26
- A/AE6w.v: 26
- A/AE6x.v: 28
- A/AE6y.v: 26
- A/AE6z.v: 26
- A/AE70.v: 26
- A/AE71.v: 26
- A/AE72.v: 26
- A/AE73.v: 26
- A/AE74.v: 26
- A/AE75.v: 26
- A/AE76.v: 26
- A/AE77.v: 26
- A/AE78.v: 26
- A/AE79.v: 26
- A/AE7a.v: 26
- A/AE7b.v: 26
- A/AE7c.v: 26
- A/AE7d.v: 27
- A/AE7e.v: 26
- A/AF0n.v: 16
- A/AF0o.v: 16, 117
- A/AFes.v: 28
- A/AFf4.v: 22
- A/AFf5.v: 28
- A/AFf6.v: 32
- A/AFf7.v: 32
- A/AFf8.v: 29
- A/AFf9.v: 32
- A/AFfa.v: 28
- A/AFfb.v: 26
- A/AFfc.v: 31
- A/AFfd.v: 28
- A/AFfe.v: 32
- A/AFfs.v: 23
- A/AFg4.v: 30
- A/AFg8.v: 29
- A/AFg9.v: 33
- A/AFgy.v: 46
- A/AFgz.v: 46
- A/AFh2.v: 34
- A/AFh3.v: 28
- A/AFh7.v: 46
- A/AFhd.v: 17
- A/AFhe.v: 28
- A/AFhf.v: 18
- A/AFhg.v: 28
- A/AFhi.v: 28
- A/AFhj.v: 28
- A/AFhk.v: 28
- A/AFhl.v: 28
- A/Prog/YC4b.v: 23
- A/Rt/FMsnprintfGwrc.v: 30
- A/Rt/FMsnprintfGwrcT.v: 36
- A/Rt/FMsnprintfMs32.v: 31
- A/Rt/FMsnprintfMs79.v: 30
- A/Rt/FMsnprintfMs7a.v: 30
- A/Rt/FMsnprintfMs7b.v: 30
- A/Rt/Memchr.v: 34
- A/Rt/MemchrChk.v: 27
- B/AB14.v: 14, 139
- B/AB15.v: 14, 263
- B/AB16.v: 15, 294
- B/AB17.v: 16, 65, 349
- B/AB18.v: 16, 287, 378
- B/AB1a.v: 16, 201, 237
- B/AB1b.v: 16, 202, 238
- B/AB1c.v: 16, 196, 232
- B/AB1d.v: 16, 315
- B/AB1f.v: 17, 435
- B/AD1d.v: 21
- B/AD1e.v: 22
- B/AD1f.v: 24
- B/AD1g.v: 22
- B/AD1z.v: 20
- B/AD23.v: 20
- B/AD25.v: 17
- B/AD2k.v: 42
- B/AE20.v: 13, 529
- B/AE2q.v: 26
- B/AE2r.v: 26
- B/AE2s.v: 28
- B/AE2t.v: 28
- B/AE2u.v: 28
- B/AE2v.v: 28
- B/AE2w.v: 28
- B/AE2x.v: 27
- B/AE2z.v: 28
- B/AE30.v: 26
- B/AE31.v: 26
- B/AE32.v: 26
- B/AE33.v: 26
- B/AE35.v: 28
- B/AE6k.v: 26
- B/AE6l.v: 26
- B/AE6m.v: 26
- B/AE6n.v: 26
- B/AE6o.v: 26
- B/AE6p.v: 26
- B/AE6q.v: 26
- B/AE6r.v: 26
- B/AE6s.v: 26
- B/AE6t.v: 26
- B/AE6u.v: 26
- B/AE6v.v: 26
- B/AE6w.v: 26
- B/AE6x.v: 28
- B/AE6y.v: 26
- B/AE6z.v: 26
- B/AE70.v: 26
- B/AE71.v: 26
- B/AE72.v: 26
- B/AE73.v: 26
- B/AE74.v: 26
- B/AE75.v: 26
- B/AE76.v: 26
- B/AE77.v: 26
- B/AE78.v: 26
- B/AE79.v: 26
- B/AE7a.v: 26
- B/AE7b.v: 26
- B/AE7c.v: 26
- B/AE7d.v: 27
- B/AE7e.v: 26
- B/AF0n.v: 16
- B/AF0o.v: 16, 117
- B/AFes.v: 28
- B/AFf4.v: 22
- B/AFf5.v: 28
- B/AFf6.v: 32
- B/AFf7.v: 32
- B/AFf8.v: 29
- B/AFf9.v: 32
- B/AFfa.v: 28
- B/AFfb.v: 26
- B/AFfc.v: 31
- B/AFfd.v: 28
- B/AFfe.v: 32
- B/AFfs.v: 23
- B/AFg4.v: 30
- B/AFg8.v: 29
- B/AFg9.v: 33
- B/AFgy.v: 46
- B/AFgz.v: 46
- B/AFh2.v: 34
- B/AFh3.v: 28
- B/AFh7.v: 46
- B/AFhd.v: 17
- B/AFhe.v: 28
- B/AFhf.v: 18
- B/AFhg.v: 28
- B/AFhi.v: 28
- B/AFhj.v: 28
- B/AFhk.v: 28
- B/AFhl.v: 28
- B/Rt/FMsnprintfGwrc.v: 30
- B/Rt/FMsnprintfGwrcT.v: 36
- B/Rt/FMsnprintfMs32.v: 31
- B/Rt/FMsnprintfMs79.v: 30
- B/Rt/FMsnprintfMs7a.v: 30
- B/Rt/FMsnprintfMs7b.v: 30
- B/Rt/Memchr.v: 34
- B/Rt/MemchrChk.v: 27
- Reusable/YA02.v: 18
- Reusable/YA03.v: 20, 174, 177, 198, 200, 248, 260
- Reusable/YA07.v: 25
- Reusable/YA08.v: 23, 311, 314, 824, 825, 1133, 1139, 1302, 1304
- Reusable/YA09.v: 24, 268, 271, 278, 279, 286, 287, 1368, 1370, 1459, 1461, 1463, 1465, 1645, 1646, 2041, 2043, 2123, 2129, 2162, 2163, 2202, 2204, 2213, 2215, 2225, 2227, 2250, 2253, 2290, 2292, 2380, 2381, 2400, 2407, 2730, 2735, 2745, 2746, 2757, 2758, 2800, 2805, 2815, 2816, 2827, 2828, 2873, 2875, 2877, 2879, 3339, 3341
- Reusable/YA0a.v: 21
- Reusable/YA0b.v: 19
- Reusable/YA0d.v: 15
- Reusable/YA0e.v: 21, 26, 27, 36, 244, 246, 253, 256, 287, 299, 882, 883, 1058, 1063, 1090, 1095, 1102, 1104, 1108, 1110, 1125, 1126, 1150, 1155, 1168, 1170, 1175, 1176, 1266, 1271, 1296, 1301, 1308, 1310, 1314, 1316, 1331, 1332, 1356, 1361, 1374, 1376, 1381, 1382, 1444, 1446, 1460, 1462, 1476, 1479, 1482, 1497, 1767, 1771, 1789, 1800, 2197, 2199, 2208, 2211, 2267, 2273, 2766, 2770, 3393, 3398, 3471, 3473, 3518, 3519, 3743, 3758
- Reusable/YA0f.v: 22, 263, 267, 1023, 1025, 1243, 1245, 1513, 1518, 1528, 1529, 1597, 1598, 1602, 1603, 1609, 1610, 1614, 1615, 1651, 1655, 1666, 1667, 1715, 1716, 1717, 1718, 1726, 1727, 1751, 1752, 1753, 1754, 1877, 1878, 1882, 1883, 1889, 1890, 1894, 1895, 1904, 1905, 1938, 1942, 1953, 1954, 2002, 2003, 2004, 2005, 2013, 2014, 2038, 2039, 2040, 2041
- Reusable/YA0j.v: 78, 95, 102, 106, 108
- Reusable/YE08.v: 13, 310
- Reusable/YFk4.v: 339, 348
- Reusable/YI0s.v: 176
- Reusable/YI67.v: 19
- Reusable/YK0a.v: 338, 347
- Reusable/YK0b.v: 17
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

### `Ltac mseq ::=` (TACTIC)

- CJ/RL/GX/G_printf_core.v: 367, 764
- CJ/RL/GX/G_printf_core_common.v: 2007
- CJ/RL/GX/G_printf_core_conv.v: 328
- CJ/RL/GX/G_printf_core_cvc.v: 311
- CJ/RL/GX/G_printf_core_cvd.v: 308
- CJ/RL/GX/G_printf_core_cvfp.v: 306
- CJ/RL/GX/G_printf_core_cvs.v: 311
- CJ/RL/GX/G_printf_core_cvu.v: 306
- CJ/RL/GX/G_printf_core_cvx.v: 319
- CJ/RL/GX/G_printf_core_dir.v: 307
- CJ/RL/GX/G_printf_core_dirs.v: 287
- CJ/RL/GX/G_printf_core_dloop.v: 307
- CJ/RL/GX/G_printf_core_end.v: 304
- CJ/RL/GX/G_printf_core_exit.v: 305
- CJ/RL/GX/G_printf_core_exit1.v: 304
- CJ/RL/GX/G_printf_core_flags.v: 305
- CJ/RL/GX/G_printf_core_fmtu.v: 304
- CJ/RL/GX/G_printf_core_fmtu2.v: 307
- CJ/RL/GX/G_printf_core_head.v: 315
- CJ/RL/GX/G_printf_core_intc.v: 307
- CJ/RL/GX/G_printf_core_intc2.v: 316
- CJ/RL/GX/G_printf_core_p1.v: 311
- CJ/RL/GX/G_printf_core_prec.v: 307
- CJ/RL/GX/G_printf_core_precs.v: 287
- CJ/RL/GX/G_printf_core_pro.v: 308
- CJ/RL/GX/G_printf_core_scan.v: 307
- CJ/RL/GX/G_printf_core_state.v: 305
- CJ/RL/GX/G_printf_core_t1.v: 306
- CJ/RL/GX/G_printf_core_t2.v: 306
- CJ/RL/GX/G_printf_core_t3.v: 306
- CJ/RL/GX/G_printf_core_t4.v: 304
- CJ/RL/GX/G_printf_core_t5.v: 306
- CJ/RL/GX/G_printf_core_t6.v: 310
- CJ/RL/GX/G_printf_core_tail.v: 310
- CJ/RL/GX/G_printf_core_xloop.v: 304
- CJ/RL/GXA/G_printf_core.v: 350, 734
- CJ/RL/GXA/G_printf_core_common.v: 1965
- CJ/RL/GXA/G_printf_core_conv.v: 312
- CJ/RL/GXA/G_printf_core_cvc.v: 299
- CJ/RL/GXA/G_printf_core_cvd.v: 296
- CJ/RL/GXA/G_printf_core_cvfp.v: 293
- CJ/RL/GXA/G_printf_core_cvs.v: 299
- CJ/RL/GXA/G_printf_core_cvu.v: 293
- CJ/RL/GXA/G_printf_core_cvx.v: 304
- CJ/RL/GXA/G_printf_core_dir.v: 294
- CJ/RL/GXA/G_printf_core_dirs.v: 296
- CJ/RL/GXA/G_printf_core_dloop.v: 294
- CJ/RL/GXA/G_printf_core_end.v: 292
- CJ/RL/GXA/G_printf_core_exit.v: 293
- CJ/RL/GXA/G_printf_core_exit1.v: 292
- CJ/RL/GXA/G_printf_core_flags.v: 293
- CJ/RL/GXA/G_printf_core_fmtu.v: 292
- CJ/RL/GXA/G_printf_core_fmtu2.v: 294
- CJ/RL/GXA/G_printf_core_head.v: 301
- CJ/RL/GXA/G_printf_core_intc.v: 294
- CJ/RL/GXA/G_printf_core_intc2.v: 301
- CJ/RL/GXA/G_printf_core_p1.v: 298
- CJ/RL/GXA/G_printf_core_prec.v: 294
- CJ/RL/GXA/G_printf_core_precs.v: 296
- CJ/RL/GXA/G_printf_core_pro.v: 296
- CJ/RL/GXA/G_printf_core_scan.v: 294
- CJ/RL/GXA/G_printf_core_state.v: 293
- CJ/RL/GXA/G_printf_core_t1.v: 293
- CJ/RL/GXA/G_printf_core_t2.v: 293
- CJ/RL/GXA/G_printf_core_t3.v: 293
- CJ/RL/GXA/G_printf_core_t4.v: 292
- CJ/RL/GXA/G_printf_core_t5.v: 293
- CJ/RL/GXA/G_printf_core_t6.v: 297
- CJ/RL/GXA/G_printf_core_tail.v: 297
- CJ/RL/GXA/G_printf_core_xloop.v: 292

### `Ltac numconst ::=` (TACTIC)

- A/AFip.v: 161
- A/AFiq.v: 161
- A/AFir.v: 161
- A/AFis.v: 315
- A/AFit.v: 161
- A/AFiu.v: 161
- A/AFiv.v: 161
- A/AFiw.v: 161
- A/AFix.v: 162
- A/AFiy.v: 161
- A/AFiz.v: 161
- A/AFj0.v: 161
- A/AFj1.v: 161
- A/AFj2.v: 161
- A/AFj3.v: 160
- A/AFj4.v: 160
- A/AFj5.v: 160
- A/AFj6.v: 316
- A/AFj7.v: 160
- A/AFj8.v: 160
- A/AFj9.v: 160
- A/AFja.v: 160
- A/AFjb.v: 161
- A/AFjc.v: 160
- A/AFjd.v: 160
- A/AFje.v: 160
- A/AFjf.v: 160
- A/AFjg.v: 160
- B/AFip.v: 161
- B/AFiq.v: 161
- B/AFir.v: 161
- B/AFis.v: 315
- B/AFit.v: 161
- B/AFiu.v: 161
- B/AFiv.v: 161
- B/AFiw.v: 161
- B/AFix.v: 162
- B/AFiy.v: 161
- B/AFiz.v: 161
- B/AFj0.v: 161
- B/AFj1.v: 161
- B/AFj2.v: 161
- B/AFj3.v: 160
- B/AFj4.v: 160
- B/AFj5.v: 160
- B/AFj6.v: 316
- B/AFj7.v: 160
- B/AFj8.v: 160
- B/AFj9.v: 160
- B/AFja.v: 160
- B/AFjb.v: 161
- B/AFjc.v: 160
- B/AFjd.v: 160
- B/AFje.v: 160
- B/AFjf.v: 160
- B/AFjg.v: 160

### `#[global] Set Default Proof Mode .` (OPTION)

- A/Bz/Lib/LiaTuning.v: 7
- B/Bz/Lib/LiaTuning.v: 7
- CJ/Lib/LiaTuning.v: 11
- CJ/Lib/StoreCache.v: 539
- CJ/P/F_sf_helpers2.v: 35
- Lib/LiaSec.v: 9
- Lib/LiaTwx2.v: 10
- Lib/WeqGuard.v: 8
- Lib/Zifyk6b.v: 6

### `Ltac drv_anch ::=` (TACTIC)

- Reusable/YL0l.v: 242
- Reusable/YL0s.v: 216
- Reusable/YL0u.v: 39
- U/Reusable/YL0l.v: 242
- U/Reusable/YL0s.v: 216
- U/Reusable/YL0u.v: 39

### `Ltac transport_chunks segs m a bs ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 49
- B/Bz/Lib/Tac.v: 49
- CJ/Lib/Tac.v: 759
- CJ/RL/GX/G_printf_core_common.v: 1395
- CJ/RL/GXA/G_printf_core_common.v: 1326
- Lib/Tac.v: 52

### `#[global] Unset Lia Cache.` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 16
- B/Bz/Lib/LiaTuning.v: 16
- CJ/Lib/LiaTuning.v: 18
- Lib/LiaTwx2.v: 18

### `#[global] Unset Nia Cache.` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 17
- B/Bz/Lib/LiaTuning.v: 17
- CJ/Lib/LiaTuning.v: 19
- Lib/LiaTwx2.v: 19

### `#[global] Unset Nra Cache.` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 18
- B/Bz/Lib/LiaTuning.v: 18
- CJ/Lib/LiaTuning.v: 20
- Lib/LiaTwx2.v: 20

### `Ltac Lia.nia ::=` (TACTIC)

- CJ/Lib/Ceil.v: 70
- CJ/Lib/LiaTuning.v: 397
- Reusable/YM03.v: 186
- Reusable/YM05.v: 68

### `Ltac Z.euclidean_division_equations_cleanup ::=` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 129
- B/Bz/Lib/LiaTuning.v: 129
- CJ/Lib/LiaTuning.v: 109
- Lib/LiaTwx2.v: 109

### `Ltac Zify.zify_internal_to_euclidean_division_equations ::=` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 137
- B/Bz/Lib/LiaTuning.v: 137
- CJ/Lib/LiaTuning.v: 117
- Lib/LiaTwx2.v: 117

### `Ltac is_concrete_map R ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 15
- B/Bz/Lib/Tac.v: 15
- CJ/Lib/Tac.v: 21
- Lib/Tac.v: 18

### `Ltac lia ::=` (TACTIC)

- A/Bz/Lib/LiaTuning.v: 221
- B/Bz/Lib/LiaTuning.v: 221
- CJ/Lib/LiaTuning.v: 343
- Lib/LiaTwx2.v: 187

### `Ltac map_cbv_get ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 21
- B/Bz/Lib/Tac.v: 21
- CJ/Lib/Tac.v: 27
- Lib/Tac.v: 24

### `Ltac map_cbv_set ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 22
- B/Bz/Lib/Tac.v: 22
- CJ/Lib/Tac.v: 30
- Lib/Tac.v: 25

### `Ltac mem_after_store ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 94
- B/Bz/Lib/Tac.v: 94
- CJ/Lib/Tac.v: 772
- Lib/Tac.v: 97

### `Ltac mem_after_store_opt ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 126
- B/Bz/Lib/Tac.v: 126
- CJ/Lib/Tac.v: 966
- Lib/Tac.v: 147

### `Ltac solve_load ::=` (TACTIC)

- A/Bz/Lib/Tac.v: 45
- B/Bz/Lib/Tac.v: 45
- CJ/Lib/Tac.v: 55
- Lib/Tac.v: 48

### `Ltac Zify.zify_pre_hook ::=` (TACTIC)

- CJ/Lib/Ceil.v: 64
- CJ/Lib/LiaTuning.v: 392
- Lib/Zifyk6b.v: 48

### `Ltac addr_diff E A ::=` (TACTIC)

- Prog/CF/LLVMFuzzerTestOneInput_seg.v: 32
- Prog/LLVMFuzzerTestOneInput_seg.v: 31
- U/Prog/LLVMFuzzerTestOneInput_seg.v: 31

### `Global Opaque` (TACTIC)

- Reusable/YK0c.v: 667
- Reusable/YQ04.v: 62

### `Ltac Lia.lia ::=` (TACTIC)

- Reusable/YM03.v: 182
- Reusable/YM05.v: 63

### `Ltac step_core segs R F pc fc rv m ro ::=` (TACTIC)

- A/Bz/Lib/StepFast.v: 2499
- B/Bz/Lib/StepFast.v: 2499

### `Ltac transport_after_call segs m m' MU WM ::=` (TACTIC)

- CJ/RL/GX/G_printf_core_common.v: 1422
- CJ/RL/GXA/G_printf_core_common.v: 1353

### `Ltac zs_idioms ::=` (TACTIC)

- CJ/Lib/SFModel.v: 32, 193

### `Ltac zs_idioms_in H ::=` (TACTIC)

- CJ/Lib/SFModel.v: 33, 194

### `Ltac zstep ::=` (TACTIC)

- A/Bz/Lib/StepFast.v: 2500
- B/Bz/Lib/StepFast.v: 2500

### `Ltac Corelib.Init.Tauto.tauto ::=` (TACTIC)

- Reusable/YM03.v: 200

### `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.simp_regs ::=` (TACTIC)

- CJ/Lib/RegFold.v: 208

### `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n` (TACTIC)

- CJ/Lib/JunkAbs.v: 50

### `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_fast ::=` (TACTIC)

- CJ/Lib/StepFast.v: 1198

### `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.step2_with rp rpm vh ::=` (TACTIC)

- CJ/Lib/StepFast.v: 1197

### `Ltac OssFuzzTheorems.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib.Step.zstep ::=` (TACTIC)

- CJ/Lib/StepFast.v: 1199

### `Ltac YM03.lf_lia_orig ::=` (TACTIC)

- Reusable/YM04.v: 36

### `Ltac model_reg_tac n X mexpr ::=` (TACTIC)

- CJ/P/F_f128_mul.v: 54

### `Ltac sim_destruct e ::=` (TACTIC)

- Reusable/YQ03.v: 15

### `Ltac sim_hook ::=` (TACTIC)

- Reusable/YQ03.v: 226

### `Ltac stdpp.bitvector.definitions.solve_BvWf ::=` (TACTIC)

- Reusable/YM05.v: 131

### `Ltac step ::=` (TACTIC)

- CJ/Lib/Step.v: 1405

### `Ltac zs_wrap e ::=` (TACTIC)

- CJ/Lib/SFModel.v: 30

### `Ltac zs_wrap_in e H ::=` (TACTIC)

- CJ/Lib/SFModel.v: 31

## UNMEASURED (no locality the tool can decide)

- A/Bz/Lib/Exec.v:65 OPTION `Arguments`
- A/Prog/PaSym.v:178 OPTION `Arguments`
- B/Bz/Lib/Exec.v:65 OPTION `Arguments`
- CJ/Lib/Ceil.v:22 OPTION `Arguments`
- CJ/Lib/Exec.v:68 OPTION `Arguments`
- CJ/P/SFW_add_split.v:17 TACTIC `Strategy`
- CJ/P/SFW_add_split.v:108 TACTIC `Strategy`
- CJ/P/SFW_add_split.v:154 TACTIC `Strategy`
- CJ/P/SFW_add_split.v:168 TACTIC `Strategy`
- CJ/P/SFW_add_split.v:179 TACTIC `Strategy`
- CJ/P/SFW_add_split.v:239 TACTIC `Strategy`
- Lib/Exec.v:136 OPTION `Arguments`
- Reusable/YG0f.v:88 OPTION `Arguments`

## KERNEL

None (0 rows).

## The four settings of the runtime memchr files

`A/Rt/Memchr.v:34`, `A/Rt/MemchrChk.v:27`, `B/Rt/Memchr.v:34` and `B/Rt/MemchrChk.v:27` each hold the file's only
setting of the flag, `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).` They are
recorded here like every other row; they are not made Local. Files that import them (from the Require lines):
`Memchr.v` imports `MemchrChk.v` (A and B); `A/Prog/BoxClose.v:41` and `B/Prog/BoxBClose.v:49` import `Memchr.v`;
with the files that reach them through those, 14 files: the two `Memchr.v`, `A/Prog/BoxClose.v`, `A/Prog/BoxSinkPin.v`,
`B/Prog/BoxBClose.v`, `B/Prog/BoxBSinkPin.v`, `Theorems.v` and the 7 `Proof.v` files. A test of the Local form (not
kept) gave ESCAPES 4 -> 0 over these four files with the same tool; its partial build compiled 2,650 files with 0
failures and stopped before it reached the 12 importers outside `Rt/`, so no importer is shown to rely on the flag.

## Reproducing

`mk_settings_record.py RUN_OUTPUT proofs/libreac/fuzz_boxreg/lib <commit> > TACTIC-SETTINGS.md`, where RUN_OUTPUT is
the stdout of global_settings.py v10 over every `.v` file of the lib at that commit.
