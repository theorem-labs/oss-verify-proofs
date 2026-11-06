# GHUNKS-A: the G hunks of libreac/fuzz_pcap's G-adapted driver files, taken into the libdiginet/fuzz_transport image-A core

proves no function (kind: statement text)

**Superseded for the cut start-up layer (T3r's cut layer, ../startup-layer.tsv; run work-rec3): see rec3/GHUNKS-A-rec3.md.** It replaces
sections 0 and 4-8 below. Section 3, the hunk classification, still holds.

Row TCA. The integration owner's decision of 01:50Z: G hunks only, as port_core `--patch` files on the core's own
donor text (fuzz_grant released lib, recipes 25e3d17bdb50); TransportDriver.v / TransportDrvG.v reduced to pcap's G
content; the slot's G parameter stays on the program side; values as rows. Image-B twin: row TCB (the image-B core's writer).

## 0. Result

- 10 patch files `g-*.patch`, not 6. Each one applies with `patch -p0 --dry-run -F0` to the run-of-record stage-out
  (`TCA/work-rec/stage-out`, provenance line removed). The planted control is refused (section 5).
  - A/AD1y.v has no patch. In this core it is a start-up layer file (T3r, `ev83/not-relocated-startup-layer.txt`),
    not port_core output. Its G content moves: the hull and `region_avoids_G` go to A/AD2f.v. The driver-window split
    is not taken (section 3, AD1y).
  - A/ACfn.v and A/AD1q.v need G hunks. pcap replaced these two files with program files (Prog/PcapEntry.v,
    PcapDriver.v). The grant core keeps them, so the G change lands on them.
  - A/AD2d.v, A/AD2e.v and A/AD1x.v need G hunks. In pcap the region cut leaves the lists unchanged: no region of
    pcap's start-up list meets its hull. In transport the T3r list holds the 18 globals as regions, so the cut removes
    17 regions, and every lemma that restates the cut lists or counts them has to change (section 4).
- Two new lib/A files: `TransportDrvG.v` and `TransportDriver.v` (section 7).
- Prerequisite: `lib/A/W_journalG.v` (Main's port of pcap's file). The core Requires it for `inG`, `ajournal_gx`,
  `ajournal_gx_inner` and `ajournal_gx_G_mono`. All of these are in pcap's Sections a and b (lines 1-508). Those lines
  use none of the 109 names that pcap's Pa* kit defines (PaTable, PaSym, PaRun, PaShadow, A/Prog/PaJournal;
  `src/pa-names.txt` against `src/wjg-ab-idents.txt`: empty intersection). Every Reusable module they Require is in
  the transport lib. So W_journalG.v cut to Sections a and b, without its Require lines 24, 30 and 31, can land with
  the core before the T1r merge. Section e (the run chain over ajournal_gx) needs the Pa* kit and can land after T1r,
  next to Section g in W_journal.v, as pcap does.
- No build was run in this lane. Section 9 lists what the first build must confirm.

## 1. Inputs (sha256, first 12)

| input | sha |
|---|---|
| donor (grant, recipes 25e3d17bdb50) A/AD1m AD1p AD1r AD1w AD1y AD2f `*.grant.v` | b9464cf53bef 4df731e70fa1 b812695149e0 3d31d672edf0 300ce30e9150 2a125309dcd9 |
| pcap (recipes 198234fa4d3) the same six `*.pcap.v` | 25a141b24062 560ac023744e 5bb9ff749248 9dbb509b244c 19df29583b38 9382f069a76d |
| pcap PcapDriver.v / PcapDrvG.v / W_journalG.v | 5950f499d1a8 / b9c11d7e400e / 4094c746f86a |
| stage-out (work-rec, = work83b) A/ACfn AD1w AD1m AD1p AD1q AD1r AD2f AD2d AD2e AD1x | 7abadaa10480 9b079df0c596 86c764a054b7 819a590a8082 382090c9bd14 452dbe19012e 8b62cf243df0 ce9876ce7cb8 88540dabc99c c287cea47173 |
| start-up layer rec/lib/A/AD2j.v (region list) / AD1y.v (T3r's earlier layer) | db4ad395250e / e1543cdbc213 |
| unstripped twin fuzz_transport.asan | 86efc3a80314 |

## 2. The G form, and why

- **The slot's G is a parameter of the program contract.** A/ACfn.v gets `Variable G : list (Z * Z)`. The post's
  journal becomes `ajournal_gx segs B G 0 [] ...`, and `tfib_lib_contract_x_all` takes `G` before `B`. This is pcap's
  Prog/PcapEntry.v:33 and :61 on the core's own contract file. The program side instantiates G with its harness
  globals (G_HARNESS: 18 payload ranges, Main's TransportG.v). The core names neither G_HARNESS nor any program file.
- **The driver's own statements fix G to a core-local hull.** A/AD2f.v defines `DRV_G_LO = 0x5df080`,
  `DRV_G_HI = 0x5f3190` and `DRV_G := [(DRV_G_LO, DRV_G_HI - DRV_G_LO)]`. These are measured from asan_globals of the
  twin and cut on the T3r region list (section 6). `lib_site_x` (A/AD1w.v) and LIBC (A/AD1m.v, A/AD1p.v) state the call
  at `DRV_G`.
- **The two meet in exactly one place: A/AD1q.v**, the driver statement (pcap's PcapDriver.v). It takes
  `Variable G`, `Hypothesis G_HULL : g_in_hull G` and `Hypothesis LIBX : tfib_lib_contract_x_all G B ...`, and lifts
  LIBX to the hull with `TransportDriver.tfib_lib_contract_x_all_hull` (W_journalG's ajournal_gx_G_mono).
- Why this form and not a G variable in every driver file:
  1. pcap's driver proof uses G only through "outside the hull" (PcapDrvG.v:36 `inG_harness_hull`, then every
     consumer in AD1r uses `~ (DRV_G_LO <= a < DRV_G_HI)`). Fixing the driver's G to the hull loses nothing.
  2. `lib_site_x`, `tfib_lib_site_x`, `tfib_loop_L` and `tfib_drv_main` keep their signatures. A G variable plus a
     hypothesis would have to be threaded through AD1w, AD1m, AD1p, AD1r Section g and TransportDrvG.
  3. The hypothesis the core needs is `g_in_hull G`, not `gx_ok G`. gx_ok is needed only by the slot's walks
     (W_journalG Section e, `paj_run_x ... G HG`). The hull itself cannot be the slot's G: the redzones between the
     globals are in Tfib_owned_static, so `gx_ok DRV_G` is false. The slot must use the 18 exact payload ranges, and
     the lift is what joins the two.
- What the program side owes the core (Main): `g_in_hull G_HARNESS` (18 ranges in [0x5df080, 0x5f3190), one lia per
  range). A/AD1q.v's `DRV_MAINX` and `tfib_srealizesX` now take `G G_HULL LIBX`.

## 3. Classified hunk table (A): every pcap-vs-grant hunk

Columns: grant lines (= stage-out lines without the provenance line) | pcap lines | class | content | transport A.
Classes: **G** = needed for the slot or driver to state ajournal_gx over G and to keep the driver's reads off G;
**pm** = pcap model (stdio source, sink head, entry/relro program files, output shape, pcap_img_end); **other** =
notice, module paths, renames, relocated values.

### AD1m (10 hunks: G 1, pm 7, other 2)
| # | grant | pcap | class | content | transport A |
|---|---|---|---|---|---|
| 1 | 4-5 | 4-5 | other | notice line, YZ00 path | none (donor notice block stays; hdrcheck) |
| 2 | 9 | 9-10 | pm | Require AgreePcap (output shape) | none |
| 3 | 11-17 | 12-19 | pm | drop AE2k/ACfn; PSource*, PcapRelro/PcapEntry/PcapEntryA, W_journal | none: AD1m names no G term (ajournal_gx reaches it through ACfn/AD1w) |
| 4 | 22 | 24-25 | pm | Context drops {LS}, adds explicit {SK} {PH} | none |
| 5 | 25 | 28 | other | GrantSyms -> PcapSyms | none |
| 6 | 29 | 31 del | pm | Variables RLO RHI dropped (PcapRelro fixes the window) | none |
| 7 | 31-32 | 33-34 | **G** (+pm) | LIBC at the contract with G (G_HARNESS); the rest is pm (SK, PCAP_RLO/RHI, A_LLVMF.., pcap_KS, RO_IN gone) | g-AD1m @32: `LIBC : tfib_lib_contract_x DRV_G B ...` (G part only) |
| 8 | 35 | 37 | pm | lib_site_x (LS:=ag_out_shape) | none |
| 9 | 52-54 | 54-57 | pm | pre: RO_IN or_intror, pcap_head, fd-names conjunct | none |
| 10 | 56 | 59 | pm | post destructuring order (fd-names) | none |

### AD1p (8 hunks: G 1, pm 5, other 2)
| # | grant | pcap | class | content | transport A |
|---|---|---|---|---|---|
| 1 | 4-5 | 4-5 | other | notice, path | none |
| 2 | 10-25 | 10-29 | pm | AgreePcap, YI16, PSourceK, PcapRelro/PcapEntry/PcapEntryA; drop ACfl/ACfn/AE2k | none (`AD2f.DRV_G` is qualified; no import) |
| 3 | 37 | 41-45 | pm | ag_out_shape instance; Context SK PH | none |
| 4 | 40 | 48 | other | PcapSyms | none |
| 5 | 47 | 55 | pm | drop RLO RHI | none |
| 6 | 49-50 | 57-59 | **G** (+pm) | LIBC with G_HARNESS (RO_IN gone: pm) | g-AD1p @50: `LIBC : tfib_lib_contract_x AD2f.DRV_G B ...` |
| 7 | 56 | 65 | pm | Let LIB args without RLO RHI RO_IN | none |
| 8 | 66-68 | 75-77 | other | fprintf format addresses | none |

### AD1w (12 hunks: G 2, pm 5, other 5)
| # | grant | pcap | class | content | transport A |
|---|---|---|---|---|---|
| 1 | 4-5 | 4-5 | other | notice, path | none |
| 2 | 9-13 | 9-16 | **G** (+pm) | Require W_journal (ajournal_gx); drop AE2k, add PcapEntry/PcapEntryA/PWalk (pm) | g-AD1w @+12: `Require Import W_journalG` |
| 3 | 15 | 18-19 | pm | PcapImgEnd YImgTop | none |
| 4 | 19 | +24 | pm | Context {SK} (transport resolves the AE2k instance) | none |
| 5 | 89 | +95 | other | HOOK comment (sink_path) | none |
| 6 | 97 | 103 | **G** | post journal `ajournal` -> `ajournal_gx tfibsegs B G_HARNESS 0 []` | g-AD1w @97: `ajournal_gx tfibsegs B DRV_G 0 [] ...` |
| 7 | 101 | 107-108 | pm | `ll_out l = PWalk.OUT pl`, HOOK comment | none |
| 8 | 123-125 | 130-132 | other | addresses | none |
| 9 | 159 | 166 | other | A_EXIT | none |
| 10 | 181 | 188 | other | PcapSyms | none |
| 11 | 195-196 | 202-203 | pm | pcap_img_end unfold | none |
| 12 | 202 | +210-211 | other | HOOK comment | none |

### AD1y (29 hunks: G 4, pm 21, other 4). Transport: start-up layer, no patch
| # | grant | pcap | class | content | transport A |
|---|---|---|---|---|---|
| 1 | 4-5 | 4-5 | other | notice, path | n/a |
| 2 | 9-13 | 9-14 | pm | PcapImgEnd YImgTop, paths | n/a |
| 3 | 17 | 18-21 | **G** | hull DRV_G_LO/HI (0x5d3f40/0x5d3f80) + DRV_IVS split around it | hull -> g-AD2f @+147 (values in g-values.tsv); split NOT taken (below) |
| 4-7 | 26, 28, 31, 33 | 30, 32, 35, 37 | pm | DRVW_rw / DRVW_lo at pcap_img_end (+ values) | n/a |
| 8 | 36 | 40 | **G** | DRVW_cases with five cases (follows the split) | NOT taken |
| 9 | +40 | 45-63 | **G** | DRV_IVS_not_G, DRVW_not_G, DRV_IVS_split_exact | NOT taken |
| 10 | 63 | 86 | other | PcapSyms | n/a |
| 11-12 | 65, 67 | 88, 90 | pm | in_img_rw at pcap_img_end | n/a |
| 13 | 70 | 93 | other | segment bound value | n/a |
| 14-16 | 131, 148, 150 | 154, 171, 173 | pm | pcap_img_end | n/a |
| 17 | 154-156 | 177-179 | other | segment bound values | n/a |
| 18-23 | 159, 164, 167, 173, 190, 192 | 182, 187, 190, 196, 213, 215 | pm | pcap_img_end (+ value 0x99000) | n/a |
| 24 | +193 | 217-227 | **G** | region_avoids_G + _sound | -> g-AD2f @+147 (moved; AD2f Requires AD1y for ext_avoids) |
| 25-29 | 255, 273, 285, 300, 356 | 289, 307, 319, 334, 390 | pm | pcap_img_end | n/a |

Why the split is not taken: T3r's AD1y.v:22 DRV_IVS (22 windows) lists each global's payload as its own driver
window. This follows from its region list, where R_A5a_2..R_A5a_18 are the globals with full write windows. So
"DRVW avoids the hull" is false in this core, and making it true would mean changing the start-up layer. The only
consumer of DRVW_not_G is the DRVW disjunct of PcapDrvG's drv_keep_set. Neither pcap's AD1r nor this core's AD1r uses
that disjunct (pcap uses only the STDOUT, ro and stack cases). TransportDrvG's kept set therefore has no DRVW
disjunct (section 7).

### AD2f (14 hunks: G 3, pm 1, other 10)
| # | grant | pcap | class | content | transport A |
|---|---|---|---|---|---|
| 1 | 4-5 | 4-33 | other | notice + ADAPTED comment | none (the hunk comments carry the reasons) |
| 2 | 9-14 | 37-47 | pm | ACfl -> PcapEntry/PcapEntryA (program: A_LLVMF.., G_HARNESS) | none (ACfl stays) |
| 3 | 23-29 | 56-62 | other | addresses | none |
| 4 | 146-147 | 179-180 | other | STDOUT/SOBUF values | none |
| 5 | 152-153 | 185-190 | **G** | IMG_L, IMG_LC clip the hull (outermost, after STDOUT, SOBUF) | g-AD2f @152-153 (+ counts @167, @169: 72 -> 55) |
| 6 | 155 | 192 | other | L_regs TP value | none |
| 7 | 179 | 216 | **G** | L_pieces clips the hull | g-AD2f @179 |
| 8 | 196-197 | 233-234 | other | IMG_B_eq counts on pcap's list | none (stage-out 43/44/66 already measured on T3r's) |
| 9-13 | 206, 231, 248, 251, 278 | 243, 268, 285, 288, 315 | other | addresses | none |
| 14 | +285 | 323-327 | **G** | L_mem_avoids_G (vm_compute) | g-AD2f @+285 |

### AD1r (41 hunks: G 21, pm 13, other 7)
| # | grant | pcap | class | content | transport A (g-AD1r @ line) |
|---|---|---|---|---|---|
| 1-4 | 4-5, 9-13, 16-17, 21-23 | same | other | notice, paths, addresses | none |
| 5 | 160 | 160-162 | **G** (+pm) | Require PcapDrvG; drop AE2k, add PSource*/PcapImgEnd (pm) | @160 `AE2k AD1u TransportDrvG` |
| 6 | +161 | 164 | pm | Context SK PH | none |
| 7, 8 | 172, 204 | 175, 207 | other | PcapSyms, in_ro_range values | none |
| 9, 10 | 210, 213 | 213, 216 | pm | spares_ro/stdout via pcap_head | none |
| 11 | 226-228 | 229-232 | **G** (+pm) | journal_regions_kept over memS + agreement premise; val_mem at as_ofl_head (pm) | @226-227 (+1 line) |
| 12 | 232 | 236 | **G** | premise `forallb region_avoids_G rs` | @232 |
| 13 | 236 | 240 | **G** | intros memS Hag HavG | @236 |
| 14 | 238 | 242-243 | **G** (+pm) | CV (alloc_ceiling bounds, beside the hull's lia); HKH (pm) | @238 (CV only) |
| 15 | +244 | 250 | **G** | HrG | @+244 |
| 16 | +248 | 255 | **G** | NG for the stack via drv_keep_not_G | @+248 (`right; right; right`: no DRVW disjunct) |
| 17 | 250 | 257 | **G** | rewrite <- Hag | @250 |
| 18 | 254 | 261 | pm | pcap_img_end | none |
| 19, 20 | 272, 275-276 | 279, 282-283 | pm | as_ofl_head | none |
| 21 | 278-279 | 285-288 | **G** (+pm) | NG via region_avoids_G_sound, rewrite <- Hag; fp_spares_off via pcap_head (pm) | @278 (3 lines; 279 kept) |
| 22 | 289 | 298 | pm | pcap_img_end | none |
| 23 | 291 | 300 | **G** | lib_reseat memS | @291 |
| 24 | 294-295 | 303-305 | **G** (+pm) | ajournal over memS + agreement premise; as_ofl_head (pm) | @294 (+1 line) |
| 25 | 300 | 310 | **G** | intros memS Hag | @300 |
| 26 | +301 | 312 | **G** | CV | @+301 |
| 27 | +323 | 335 | **G** | NG for the stack | @+323 (`right; right; right`) |
| 28 | 325 | 337 | **G** | rewrite <- Hag | @325 |
| 29 | 327-328 | 339-340 | pm | pcap_img_end | none |
| 30 | 330-331 | 342-344 | **G** | journal_regions_kept call: memS, Hag, L_mem_avoids_G | @330-331 (+comment) |
| 31-33 | 435, 456, 553 | 448, 469, 566 | pm | pcap_img_end | none |
| 34 | 656 | 669 | **G** | HJ -> HJG | @656 |
| 35 | +657 | 671-672 | **G** | `apply drv_journal_of_gx in HJG as (memS & HJ & Hag)` | @+657 |
| 36 | 665 | 680-682 | **G** | stdout kept: rewrite F3, Hag, drv_keep_not_G | @665 (`left`) |
| 37 | 667 | 684-686 | **G** (+pm) | rodata kept: rewrite F3, Hag, drv_keep_not_G; pcap_img_end unfold (pm) | @667 (`right; left`; plain lia) |
| 38 | 679 | 698 | **G** | lib_reseat call: memS, Hag | @679 |
| 39, 40 | 783, 858 | 802, 877 | pm | pcap_img_end | none |
| 41 | 1054 | 1073 | other | PcapSyms | none |

Counts by diff hunk here: AD1m 1, AD1p 1, AD1r 21, AD1w 2, AD1y 4, AD2f 3. The regex split had 1, 1, 10, 1, 6, 3. The
AD1r and AD1w differences are the many-line G runs and the W_journal import, read here hunk by hunk. For AD1y, the 21
pcap_img_end / value hunks are classed pm here. I did not read which 6 hunks the regex took.

### PcapDriver.v / PcapDrvG.v (new files in pcap)
- PcapDriver.v: G content = LIBX at pcap's program contract with G (:57, through PcapEntryA's G_HARNESS). Everything
  else is pm (pcap_drv_SK, ag_out_shape, MT/XM/XN fixed, pcap_KS) or AD1q's text, which this core keeps.
  -> TransportDriver.v (lift) + g-AD1q.
- PcapDrvG.v: everything is G except PcapImgEnd/PSource/Prog imports (pm). inG_harness_hull (:36) -> inG_DRV_G_hull
  (+ inG_DRV_G_of_hull for the lift); drv_keep_set (:44) without DRVW; FINV_IVS_not_G (:46); drv_keep_not_G (:49);
  drv_keep_not_inG (:60) dropped (no user in pcap or here); drv_journal_of_gx (:68) at DRV_G. -> TransportDrvG.v.

## 4. Transport-only G hunks (no pcap-vs-grant hunk)

| file | lines | what | why |
|---|---|---|---|
| A/ACfn.v | +16, 28, 51, 72-73 | Require W_journalG; `Variable G`; post `ajournal_gx segs B G 0 []`; `tfib_lib_contract_x_all` takes G | the slot contract's G parameter (pcap: Prog/PcapEntry.v:33, :61, a program file; this core keeps grant's ACfn) |
| A/AD1q.v | +21, 40, 68 | Require TransportDriver; `Variable G`, `G_HULL : g_in_hull G`, LIBX at G; DRV_MAINX lifts LIBX to the hull | pcap: PcapDriver.v:57 LIBX; this core keeps grant's AD1q |
| A/AD2f.v | +147 | DRV_G_LO/HI, DRV_G, region_avoids_G(+_sound) | pcap's AD1y hunks 3 and 24 (AD1y is the start-up layer here) |
| A/AD2f.v | 167, 169 | `length IMG_L = 55`, `length IMG_LC = 55` (were 72) | the cut removes 17 regions (pcap: unchanged, its cut changes no region) |
| A/AD2d.v | 32, 162 | L_pieces_unfold restates the clip with the hull; refines_B's IMG proof gets the third layer (flat_map_pieces_ok + clip_out_ok) | vm_compute equality with the new L_piecesC |
| A/AD2e.v | 65, 75, 78, 117, 124 | PM_tailCM, PM_tailL_unfold, PM_tailCM_unfold with the hull; refines_PM_tailL/CM third layer | concat PM_piecesCM = CM_mem (IMG_L is cut); unfold lemmas are vm_compute |
| A/AD1x.v | 26 | `length IMG_XL = 56` (was 73) | IMG_XL = clipX IMG_L |

## 5. Patch files and checks

Applied by port_core after the five existing patches (zero-shadow-forallb cell-lookup ad1q-shape imgtop-alias
dead-arm-ad1g), in this order: g-ACfn g-AD1w g-AD1m g-AD1p g-AD1q g-AD1r g-AD2f g-AD2d g-AD2e g-AD1x. Each patch has
the header form of ad1q-shape.patch (`--- A/<f>.v` / `+++ A/<f>.v`).

| patch | sha | hunks |
|---|---|---|
| g-ACfn.patch | 541e4c4696b9 | 4 |
| g-AD1w.patch | ed41960ef097 | 2 |
| g-AD1m.patch | 58f8cadc9122 | 1 |
| g-AD1p.patch | 2b55df460405 | 1 |
| g-AD1q.patch | c353e5cf6157 | 3 |
| g-AD1r.patch | f608c9daaac2 | 8 (20 edits) |
| g-AD2f.patch | 63f0e056cabf | 4 |
| g-AD2d.patch | f42403c14e4f | 2 |
| g-AD2e.patch | 70366e6cbea5 | 4 |
| g-AD1x.patch | 2bf084002fd5 | 1 |

Check (record `src/check_gpatches.out`): `python3 tools/check_gpatches.py TCA/work-rec/stage-out .`
copies stage-out/A without its provenance lines and runs `patch -p0 --dry-run -F0` for each patch: all 10 `rc=0`.
Control: g-AD1q.patch with one context line altered gives `rc=1` ("Hunk #1 FAILED at 19"). The same check on work83b's
stage-out also exits 0. The patched texts (`stage-g/A/*.v`) equal a real `patch -p0 -F0` application, byte for byte
(cmp, all 10).

Gate interplay at the run of record: check.tsv / gate.tsv explain A/AD2f.v 167, 169 and A/AD1x.v 26 as port_core's
region-count rows (donor 35 -> 72, 36 -> 73). After these patches the files say 55 and 56, so the gate lanes must
explain those lines with the rows of section 6.

## 6. Value rows (`g-values.tsv`)

```
file	donor-line	old	new	reason
A/AD2f.v	+147	0x5d3f40	0x5df080	DRV_G_LO (pcap A/AD1y.v:19): payload start of g_cfg, first of the 18 writable harness globals (asan_globals, twin 86efc3a80314)
A/AD2f.v	+147	0x5d3f80	0x5f3190	DRV_G_HI (pcap A/AD1y.v:20): payload end of OW = 0x5f3060 + 304; OW's redzone [0x5f3190, 0x5f31e0) meets no region, so 0x5f31e0 cuts the same
A/AD2f.v	167	72	55	length IMG_L: 70 IMG_REGIONS + 1 (STDOUT in R_A3) + 1 (SOBUF in R_A8) - 17 (R_A5a_2..R_A5a_18 in the hull); R_A5a_1 cut to [0x5df050, 0x5df080)
A/AD2f.v	169	72	55	length IMG_LC: same count
A/AD1x.v	26	73	56	length IMG_XL = clipX IMG_L: 55 + 1 (F_STDERR splits R_A3's lower piece)
```
How measured: `python3 tools/asan_globals.py <twin> > src/asan_globals-86efc3a80314.tsv` (40 descriptors; the 18 at
or above 0x5d0000 are exactly the task's list) and `python3 tools/measure_gcut.py rec/lib/A/AD2j.v src/AD2f.so.v
stage-out/A/AD1x.v src/asan_globals-86efc3a80314.tsv` (record `src/measure_gcut.out`; the stage-out AD2f.v with its
provenance line gives the same output). Control: the same script without the hull clip gives 72 (IMG_L) and 73
(IMG_XL), the values port_core wrote in the run of record. The script also shows that STDOUT, SOBUF and F_STDERR are
off the hull and that the clipped IMG_LC avoids the
hull (L_mem_avoids_G true). By reading rec/lib/A/AE23.v:51: the one ex_consts cell near the hull (0x5df054, the init
flag) is below 0x5df080, so it stays in R_A5a_1's kept piece.

## 7. The two new files (lib/A)

- `TransportDrvG.v` (ae57dacedcd3): pcap's Copyright/SPDX lines byte for byte, no notice line of ours. It holds
  inG_DRV_G_hull, inG_DRV_G_of_hull, drv_keep_set (STDOUT_MUT, in_ro_tfa, finv_img, stack; no DRVW),
  FINV_IVS_not_G, drv_keep_not_G and drv_journal_of_gx (at DRV_G). Requires W_journalG and the core's AB1v ACeg AD1u
  AD2f AD1w. No program file.
- `TransportDriver.v` (ef03dc37128d): the same header form. It holds g_in_hull, g_in_hull_DRV_G,
  tfib_lib_contract_x_hull (per float state) and tfib_lib_contract_x_all_hull. Requires W_journalG, ACfn, AD2f and
  TransportDrvG.

## 8. G hunks in units, for one-to-one comparison with TCB's B list

| unit | change | pcap A anchor | transport A anchor | note for B |
|---|---|---|---|---|
| G1 | contract takes G; post journal `ajournal_gx .. G 0 []` | Prog/PcapEntry.v:33, :61 | g-ACfn @+16, 28, 51, 72-73 | B's twin of ACfn |
| G2 | call-site journal at G | AD1w.v:13 (import), :103 | g-AD1w @+12, 97 (at DRV_G) | |
| G3 | LIBC at the contract with G | AD1m.v:34, AD1p.v:59 | g-AD1m @32, g-AD1p @50 (at DRV_G) | TCB's YD1m 30-32 / YD1p 48-49 |
| G4 | driver statement LIBX at G | PcapDriver.v:57 | g-AD1q @+21, 40, 68 + TransportDriver.v | |
| G5 | hull bounds | AD1y.v:18-20 | g-AD2f @+147 (0x5df080 / 0x5f3190) | B's hull from the B twin's asan_globals |
| G6 | bridge drv_journal_of_gx | PcapDrvG.v:36, :68 | TransportDrvG.v | |
| G7 | kept-set side condition | PcapDrvG.v:44-61 | TransportDrvG.v (no DRVW disjunct, no drv_keep_not_inG) | |
| G8 | driver-window split around the hull | AD1y.v:21, :40, :45-63 | NOT taken (T3r DRV_IVS lists the globals) | check B's start-up DRV_IVS the same way |
| G9 | region_avoids_G(+_sound) | AD1y.v:217-227 | g-AD2f @+147 (moved) | TCB's YD1y 200 |
| G10 | region cut IMG_L/IMG_LC/L_pieces | AD2f.v:185-190, :216 | g-AD2f @152-153, 179 + counts 167/169, g-AD2d, g-AD2e, g-AD1x | pcap's cut changes no region; in A it drops 17. B's count needs B's list |
| G11 | L_mem_avoids_G | AD2f.v:323-327 | g-AD2f @+285 | TCB's YD2f 301 |
| G12 | AD1r consumer (memS, Hag, NG, bridge call) | AD1r.v:160-162, 229-344, 669-698 | g-AD1r (8 hunks, 20 edits, section 3) | drv_keep_set indices differ if DRVW is dropped |

## 9. Not verified: what the first build must confirm

- Nothing here was compiled (W_journalG.v, TransportDrvG.v and TransportDriver.v are in no tree yet). In the order a
  failure is most likely:
  1. `eapply ajournal_gx_G_mono; [..|..]` (TransportDriver.v) and `apply ajournal_gx_inner in HJ` (TransportDrvG.v)
     assume these lemmas take no Section hypothesis (LAWS, segs_low) as an argument. pcap's PcapDrvG uses
     ajournal_gx_inner the same way.
  2. The vm_compute checks the cut changes: AD2f CM_mem_wf / fb_checks / CM_so_ok / L_pieces_eq / L_mem_avoids_G;
     AD1r rsFQ_eq / XM_sub_chk / calls_checks / L_mem0_shape; AD2e PM_pieces_eq; AD28 IMG_XL lemmas; AD1j
     ex_consts_chk. The exit walks AD27/AD28 run over IMG_XL, which now lacks the 17 global regions. They hold only
     if the exit path reads no harness global.
  3. `region_avoids_G_sound`'s lia and the NG lias in AD1r (the same tactics as pcap's, at transport literals).
- The core no longer has pcap's check that the driver's write windows avoid G (G8). No statement here needs it. If
  the slot needs the harness globals' contents at entry (pcap's contract does not), that is a program-side
  obligation.
- The alternative to the AD2d/AD2e/AD1x ripple is pcap's own method: regenerate T3r's start-up list without the
  globals (R_A5a cut around the hull, as pca-2 did). Then the AD2f clip changes no region, but every region count of
  the core moves through port_core's region-count rows (70 -> 53). This lane did not take it, because it changes the
  start-up layer, which is not part of this core.

## 10. Re-run (run of record on the final stage-out)

```
python3 tools/make_gpatches.py <WORK>/stage-out <OUT>     # refuses if any edited line moved
python3 tools/check_gpatches.py <WORK>/stage-out <OUT>    # 10 dry-runs + control
python3 tools/asan_globals.py <unstripped twin> > g.tsv && python3 tools/measure_gcut.py <LIB>/A/AD2j.v <WORK>/stage-out/A/AD2f.v <WORK>/stage-out/A/AD1x.v g.tsv
```
Tools (sha256, first 12): make_gpatches.py 9a009a6e36d5, check_gpatches.py d847a8a69751, asan_globals.py 1ae1100fd0f9,
measure_gcut.py a244a0f52033. make_gpatches.py writes only under OUT; check_gpatches.py only in a temporary directory
it removes; the other two print to stdout.
