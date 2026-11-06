# GHUNKS-A, rec3: the G patches on the start-up layer cut around the hull

proves no function (kind: statement text)

This replaces ../GHUNKS-A.md sections 0, 4, 5, 6, 7 and 8 for the run on the cut start-up layer (the integration owner's decision of
02:03Z, path (a)). Section 3 of ../GHUNKS-A.md (the pcap-vs-grant hunk classification) still holds. Its AD1y rows
are now in the start-up layer, not in the core.

## Inputs (sha256, first 12)
- start-up layer: T3r's cut layer (../startup-layer.tsv; donor not released): A/AD2j.v f32f53f83a52 (54 regions), A/AD1y.v
  cd08f8cdb321, A/AF0m.v 5dfdd0e65356. These equal the files in LIB/A, checked with git show
  on the ref.
- run WORK=TCA/work-rec3 (port_core 83f5203d2a2f, 6 patches applied, 0 failed, run-rec3.log). Its
  stage-out A/ACfn AD1w AD1m AD1p AD1q AD1r are byte-equal to work-rec's. A/AD2f.v fcf336110c35 differs from work-rec's
  only in region counts (54-region list).
- twin fuzz_transport.asan 86efc3a80314 (asan_globals table ../src/asan_globals-86efc3a80314.tsv)

## Patch list (rec3/, applied after the run's 6 patches, in this order)
| patch | sha | hunks | content |
|---|---|---|---|
| g-ACfn.patch | 541e4c4696b9 | 4 | Require W_journalG; `Variable G`; post `ajournal_gx segs B G 0 []`; `tfib_lib_contract_x_all` takes G |
| g-AD1w.patch | ed41960ef097 | 2 | Require W_journalG; lib_site_x's call journal `ajournal_gx tfibsegs B DRV_G 0 []` |
| g-AD1m.patch | 58f8cadc9122 | 1 | LIBC at `DRV_G` |
| g-AD1p.patch | 2b55df460405 | 1 | LIBC at `AD2f.DRV_G` |
| g-AD1q.patch | c353e5cf6157 | 3 | Require TransportDriver; `Variable G`, `G_HULL : g_in_hull G`, LIBX at G; DRV_MAINX lifts LIBX to the hull |
| g-AD1r.patch | 258880fd6cad | 8 (20 edits) | Require TransportDrvG; journal_regions_kept / lib_reseat over memS + agreement; NG asserts; call site `drv_journal_of_gx`; L_mem_avoids_G |
| g-AD2f.patch | f9d48ede68ec | 3 | `DRV_G := [(DRV_G_LO, DRV_G_HI - DRV_G_LO)]`; the hull clip in IMG_L, IMG_LC, L_pieces (outermost); `L_mem_avoids_G` |

Dropped, as asked: g-AD2d, g-AD2e, g-AD1x and the IMG_L / IMG_LC / IMG_XL count rows. AD2f now defines only DRV_G.
DRV_G_LO, DRV_G_HI, region_avoids_G and region_avoids_G_sound are the start-up AD1y's (AD1y.v:25-26, :215-222), and
AD2f, AD1r and TransportDrvG Require AD1y.

Changes from the first version (work-rec), apart from the drops:
- g-AD1r: the four `drv_keep_set` selectors are pcap's text again (`right; right; right; right` stack, `right; left`
  stdout, `right; right; left` rodata). The kept set has pcap's DRVW disjunct again, because the cut AD1y's
  `DRVW_not_G` (AD1y.v:54) now holds.
- TransportDrvG.v (d94ee4caa8e6): `drv_keep_set` = pcap's five disjuncts (DRVW, STDOUT_MUT, in_ro_tfa, finv_img,
  CEIL_MIN <= a). `drv_keep_not_G` uses AD1y's `DRVW_not_G`; `drv_keep_not_inG` is kept as pcap has it. Requires AD1y.
- TransportDriver.v (c5e7bbb55e4f): Requires AD1y (g_in_hull names DRV_G_LO / DRV_G_HI). Otherwise unchanged.
- g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q: byte-identical to the first version.

## Dry-run results (rec3/check_gpatches.out)
`python3 tools/check_gpatches.py work-rec3/stage-out rec3 --before <the 6 ev83 patches in run83.sh order>`:
- the 6 run patches undone in reverse order (`patch -R -p0 -F0`): rc=0 each;
- reapplied in order zero-shadow-forallb, cell-lookup, ad1q-shape, imgtop-alias, dead-arm-ad1g, bss-zero-range
  (dry-run `-F0`, then for real): rc=0 each; the tree equals the stage-out text byte for byte (round trip exact);
- then g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q, g-AD1r, g-AD2f, each `--dry-run -F0` then for real: rc=0 each. Each
  patched file equals stage-g/A/<f>.v. g-AD1q applies on top of ad1q-shape (both touch AD1q.v);
- control: g-ACfn.patch with one context line altered gives rc=1 ("Hunk #1 FAILED at 14").
The only port_core pass that writes values after the --patch step is relations(). It wrote 0 in this run
("relation results recomputed 0"), and no slot was laid. So the stage-out text of the 7 files is the text port_core
patches.

## Measurement (rec3/measure_gcut.out)
`python3 tools/measure_gcut.py rec3/lib/A/AD2j.v work-rec3/stage-out/A/AD2f.v work-rec3/stage-out/A/AD1x.v
src/asan_globals-86efc3a80314.tsv rec3/lib/A/AD1y.v`:
- hull from asan_globals [0x5df080, 0x5f3190) equals AD1y's DRV_G_LO / DRV_G_HI;
- 54 regions, none meets the hull (R_A5a_1 ends at 0x5df080, R_A5a_2 starts at 0x5f31e0); clip_identity true;
- IMG_L / IMG_LC 56 with or without the hull clip; IMG_XL 57. These are the counts port_core wrote (`*_written ...
  stands`), so the counts stand and no row is needed;
- L_mem_avoids_G true; STDOUT, SOBUF, F_STDERR off the hull.
Control (rec3/measure_gcut-control.out): the same script on the uncut list (rec/lib, work-rec) gives clip_identity
false, 72 -> 55 and 73 -> 56, `DIFFERS`.

## AF0m zero-shadow rows (bss-zero-range.patch)
The new AF0m 5dfdd0e65356 Tfib_zero_shadow (25 rows) still holds both rows the patch names: `(0x5f31e0, 0x616000 -
0x5f31e0)` (A/AD1o.v bss_zero_shadow) and `(0xa9340, 0x5df0b8 - 0xa9340)` (A/AD25.v rs_zero_shadow). Tfib_zero_shadow
is the same list in both AF0m versions. The only AF0m change from the earlier start-up layer is in Tfib_owned_static:
one row (0x10338, 8) is added, with its const cell `z8 (ANum 0x10338) 0xf5f5f5f5f5f5f5f5`.

## Values
No value in the G patches changed. The hull is 0x5df080 / 0x5f3190 as before, now stated once in the start-up AD1y.
The count rows of ../g-values.tsv are void for this layer: the counts port_core writes stand.

## G units for TCB (replaces ../GHUNKS-A.md section 8)
| unit | pcap A anchor | transport A (rec3) |
|---|---|---|
| G1 contract takes G | Prog/PcapEntry.v:33, :61 | g-ACfn |
| G2 call journal at G | AD1w.v:13, :103 | g-AD1w (at DRV_G) |
| G3 LIBC at G | AD1m.v:34, AD1p.v:59 | g-AD1m, g-AD1p (at DRV_G) |
| G4 driver LIBX at G | PcapDriver.v:57 | g-AD1q + TransportDriver.v (lift G -> hull) |
| G5 hull bounds | AD1y.v:18-20 | start-up AD1y.v:25-26 (no core hunk); DRV_G list in g-AD2f |
| G6 bridge drv_journal_of_gx | PcapDrvG.v:36, :68 | TransportDrvG.v |
| G7 kept set + side condition | PcapDrvG.v:44-61 | TransportDrvG.v (same five disjuncts) |
| G8 driver-window split | AD1y.v:21, :40, :45-63 | start-up AD1y.v:27, :52-59 (no core hunk) |
| G9 region_avoids_G | AD1y.v:217-227 | start-up AD1y.v:215-222 (no core hunk) |
| G10 hull clip | AD2f.v:185-190, :216 | g-AD2f; changes no region, no count row |
| G11 L_mem_avoids_G | AD2f.v:323-327 | g-AD2f |
| G12 AD1r consumer | AD1r.v:160-162, 229-344, 669-698 | g-AD1r (tactics as pcap's) |

## Not verified
No build was run. A build must still confirm items 1 and 3 of ../GHUNKS-A.md section 9. Item 2 is moot now that the
clip changes no region: the vm_compute lemmas see the same lists.

## Re-run
```
python3 tools/make_gpatches.py <WORK>/stage-out <OUT>
python3 tools/check_gpatches.py <WORK>/stage-out <OUT> --before $(for p in zero-shadow-forallb cell-lookup ad1q-shape imgtop-alias dead-arm-ad1g bss-zero-range; do echo ev83/$p.patch; done)
python3 tools/measure_gcut.py <LIB>/A/AD2j.v <WORK>/stage-out/A/AD2f.v <WORK>/stage-out/A/AD1x.v src/asan_globals-86efc3a80314.tsv <LIB>/A/AD1y.v
```
Tools (sha256, first 12): make_gpatches.py c8ad86be0ebb, check_gpatches.py 273729a57008, measure_gcut.py 03c6c8e51444,
asan_globals.py 1ae1100fd0f9. The first version's tools are kept in ../tools/rec/ (9a009a6e36d5, d847a8a69751,
a244a0f52033).
