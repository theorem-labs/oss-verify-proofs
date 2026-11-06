# Method of libdiginet/fuzz_transport's image-A core relocation: route, decisions and measurements

proves no function (kind: merge; relocation of libreac/fuzz_grant's released image-A core onto libdiginet
fuzz_transport.asan). This file gives the route and the run status, and records each decision with the measurement it
rests on; GATES.md gives every gate's result, MANIFEST.md the role of each file. Image A = fuzz_transport.asan (pin sha256
e89be137db17, names from its unstripped twin 86efc3a80314, whose PT_LOAD bytes equal the pin's except the ELF header and
the build-id note at 0x10028-0x102cb); image B = fuzz_transport.asan-ubsan (41113a03c82f); donor image = fuzz_grant.asan
(c2c7559b29bd, twin 57c26f993615). Every pin is the one projects/libdiginet/fuzz_transport/harness.yaml of this
tree states (plain bb20ce415827, ubsan af7b86991906, asan e89be137db17, asan-ubsan 41113a03c82f).

## Route and run status

The run of record is `run.sh` (this directory) on the run directory WORK, with:

    REL=<port_core 83f5203d2a2f release> DON=<fuzz_grant's released lib, normalised> PG=<fuzz_grant's images>
    P=<fuzz_transport's images> EV=<this directory> SYMS=<fuzz_grant.asan.syms.txt, sha256 b46268790c46>
    LIB=<the unit's lib, below> GRANTB=<B/YA09.v, B/YA0e.v of fuzz_grant's released lib, recipes 4f87de75d67>
    sh run.sh WORK

- REL: the port_core 83f5203d2a2f release (port_core.py, sha256 83f5203d2a2f; README.md, sha256 299fda276079; internal
  records); the copy the run used equals it file for file (20 of 20 sha256 equal). `versions.txt` (the run's own) lists port_core.py 83f5203d2a2f and the sha256 of every helper.
- DON: fuzz_grant's released lib at origin/ossv/recipes 25e3d17bdb50, normalised as fuzz_frame's and fuzz_decode's runs
  do (Reusable/* at the lib root, module text `...fuzz_grant.lib.Reusable` -> `...fuzz_grant.lib`).
- LIB: the lib the run read: the unit's lib on the new pin (with libdiginet/fuzz_transport lib/A/TransportShape.v, file
  sha256 caa68b81b1f5; donor not released) with the 19 start-up files of row T3r's cut layer (records/startup-layer.tsv: each
  file's sha256; donor not released), plus the composition kit (`add-kit.sh`, `kit-rec.tsv`) and Reusable/YImgTop.v taken
  by path. Each is below. Measured: the 19 start-up files of LIB equal records/startup-layer.tsv and this tree's lib (19 of 19);
  the 17 kit files of LIB equal kit-rec.tsv's written blobs (17 of 17).
- EV: this directory. run.sh passes 14 `--patch` files in this order: zero-shadow-forallb, cell-lookup, ad1q-shape,
  imgtop-alias, dead-arm-ad1g, bss-zero-range, then the 7 G patches g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q, g-AD1r,
  g-AD2f ("G patches" below), then afet-cost (a proof-script cost fix of A/AFet.v, "Patches" below). `run.sh` and
  `overrides.tsv` here differ from the files the run read in one comment line each, rewritten after the run (a branch
  name and an actor's name, now a file sha256 and the role it played): the run read run.sh sha256 be810dc6934d and
  overrides.tsv sha256 e796f27baba3 (the sha256 the records of the run cite); every line that is not a comment is
  byte-equal (measured).
- Status 3 with the expected rows (records/run-of-record.txt: the summary lines and every check.tsv FAIL row with its
  reason). port_core: `staged 492 files (112 kept from the target ...)`, `59 hand values from --override`, `patches
  applied 14, failed 0`, `region counts recomputed 50`; `run: hdrcheck: 492 files, 492 in form, 0 refused`;
  reusable-local.py: 53 + 72 redefinitions made Local, `code equals released lib/B/YA09.v with all Local: True` (and
  YA0e.v).
- required.tsv: 4 rows, each `require-unresolved` and each expected: the G patches make A/ACfn.v and A/AD1w.v Require
  A.W_journalG, A/AD1q.v Require A.TransportDriver and A/AD1r.v Require A.TransportDrvG, modules the unit writes itself
  and that LIB did not hold. This tree's lib holds all three: lib/A/W_journalG.v (file sha256 afd0c41a8ecd) and the two
  new files of the G work, lib/A/TransportDrvG.v and lib/A/TransportDriver.v (below).
- This tree's lib holds the run's 492 WORK/stage-out files byte for byte except lib/A/AB1w.v, from which 160 function-table
  cells that no file reads were removed after the run (records/TFIB-WHOLE-TABLE.md; measured: 491 equal, 1 differs), and
  Reusable/YImgTop.v, lib/A/W_journalG.v and the two new files. The core as the run wrote it (all 492 files equal) is
  the commit before that removal.

Earlier runs, each a DRY run, none cited as the record:

| run | port_core | inputs | LIB start-up layer | stage-out tree (sha256 of the sorted `sha256sum` list) |
|---|---|---|---|---|
| work2 | d9e0589898fd (not of record) | 5 patches, CZONE 0x800bac00 | T3 old-pin stand-in | 40642240e8e1 |
| work83b | 83f5203d2a2f | 5 patches, CZONE 0x800bac00 | T3 old-pin stand-in | 9cc9f95c5eb3 |
| work-rec | 83f5203d2a2f | the same as work83b | T3r, earlier (A/AF0m.v 390be0f43c79) | 9cc9f95c5eb3 (byte-equal to work83b) |
| work-rec2 | 83f5203d2a2f | 6 patches, CZONE 0x800b9c00 | T3r, earlier (A/AF0m.v 390be0f43c79) | 47644e6295ea (the interim core) |
| work-rec3 | 83f5203d2a2f | the same 6 patches | T3r cut (records/startup-layer.tsv) | the text the G patches were cut against (records/ghunks/GHUNKS-A-rec3.md) |
| work-rec4 | 83f5203d2a2f | 13 patches (the 6 + 7 G) | T3r cut (records/startup-layer.tsv) | a6263e40662d |
| work-rec5 (record) | 83f5203d2a2f | 14 patches (the 13 + afet-cost) | T3r cut (records/startup-layer.tsv) | 3df9dee2b44d |

work-rec5 differs from work-rec4 in one file, A/AFet.v (afet-cost.patch; measured: `diff -r` of the two stage-outs names
only it; overrides.tsv, required.tsv and versions.txt byte-equal; check.tsv adds the row `A/AFet.v 0 patched (--patch)`).
work-rec4 differs from work-rec2 in 14 files: the 7 G-patched files A/ACfn, AD1m, AD1p, AD1q, AD1r, AD1w, AD2f, and
A/AD1x, AD22, AD27, AD28, AD2d, AD2e, AD2h, whose region counts port_core recomputes on the cut layer's 54-region list
(A/AD2f.v carries both). The donor text WORK/stage is the same in every run (cb94de36d3c6). Why work-rec was not the
record: the whole-unit build of its core (cb, the unit's lib plus the 492 files, build VM log
build-20261031T011642Z) failed 3 targets, at A/AD1o.v:85, A/AD25.v:533 and A/AFju.v:663; "Values this unit states
otherwise than the donor" below gives each cause and its measurement. Why work-rec2 is not the record: the start-up
layer moved to T3r's cut layer and the G patches came in (the integration owner's decisions of 01:50Z and 02:03Z,
path (a)). Why work-rec4 is
not the record: A/AFet.vo took 7936 s and 43 GB, and the integration build (MEM=24g) killed it at 24 GB; afet-cost.patch
fixes the proof script (below).

## Donor

Row TCA names fuzz_grant's released image A (origin/ossv/recipes) as the donor, as libdiginet/fuzz_frame's image-A core
(its run.sh, sha256 437d65e84649; internal record) and libdiginet/fuzz_decode's image-A core record ("D9" below; its
METHOD.md, sha256 0fbec3bd18a7; internal record) use. The reasons are D9's: (1) libreac/fuzz_decode's
released lib/A is that same grant core relocated onto another image, so taking it would relocate a relocation; (2)
port_core's donor inputs are grant's (--old-elf fuzz_grant.asan, its symbol list b46268790c46, the AB1w tfib_entry guard
against --old-elf's e_entry); (3) fuzz_transport links grant's runtime set: the five runtime functions the row names
(MaybeReleaseToOS, VSNPrintf, Decorator::ShadowByte, SignalContext::Describe, __strftime_fmt_1) compared by cmpkit
86da41d3ef68 (strictcmp3 and jtcheck, records/STRICTCMP-RUNTIME.md) are the same code up to pc-relative displacements
and their tables, every `lui-in-section` row a number by its dataflow. This unit did not run the kit over every stepped
runtime function (D9 did); the five are the row's list.

## port_core 83f5203d2a2f and --src-rev

The row named d9e0589898fd, best available then. 83f5203d2a2f became OF RECORD at 22:0xZ (tools registry, `port_core
83f5203d2a2f OF RECORD, SUPERSEDES d9e0589898fd`), so the run of record uses it; the four compensating checks of the
d9e0589898fd registry entry still run on its output (records/compcheck.txt). port_core e0e94a04094b became of record at
02:4xZ (registry: `port_core e0e94a04094b OF RECORD, SUPERSEDES 83f5203d2a2f`; port_core.py, sha256 e0e94a04094b; internal
record), after this
run started; the run of record stays on 83f5203d2a2f, the version it started on. The DRY cross-check ran the port_core
the registry names in tools/pg-reloc-portcore/LATEST (LATEST, sha256 c47f7ef1a6e4, in the registry's README.md, sha256
44131f52b660; internal records; 07:59Z): e0e94a04094b. port_core d6572d099856 and 465c9cffd0b8 are released as tool
directories (port_core.py, sha256 d6572d099856 and 465c9cffd0b8; internal records) but not in the registry, so neither
ran. It ran ONCE on the run of record's inputs (run.sh with REL changed, 14 patches, 08:04Z-08:11Z;
records/e0e9-dry/E0E9-DRY.md): exit 3 as the record; 0 new FAIL rows (interval-delta, tot-bound,
hypothesis-decimal-moved, bound-name-mismatch: 0 each); 0 shadow-offset rows (no class of this tag); 0 NO-FILE /
override-not-found rows (overrides.tsv and required.tsv byte-equal to the record's); the 492 stage-out files differ only
in the provenance line's tool sha, 0 value cells. One FAIL row is the record's only (A/AFem.v:206 value-role-conflict,
which e0e94a04094b leaves out because an override row writes the value). An earlier run of the same tag on work-rec4's
inputs gave the same result.
`--src-rev 25e3d17bdb50`: 83f5203d2a2f's item 92 writes one registered provenance line per staged file, and only with
--src-rev: `(* Relocated from <donor file> at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport
(asan). *)`, directly under the donor's notice block, which stays byte for byte; no `Modified by` line. `hdrcheck.py`
checks exactly that on every staged file (the donor's notice block first, then the registered line, no other provenance
or `Modified by Theorem Labs` line): `492 files, 492 in form, 0 refused`. It takes the place of D9's hdrform.py, whose
month-dated `Modified by` form 83f5203d2a2f no longer writes.

## Start-up layer (row T3r, the cut layer)

The 19 lib/A start-up files are row T3r's cut layer (records/startup-layer.tsv, each file's sha256; donor not released): the
image-region list cut around the harness-globals hull. Measured: each of the 19 is byte-equal to its row there, in the
LIB the run read and in this tree's lib. Against T3r's earlier layer (the layer of work-rec and work-rec2; libdiginet/
fuzz_transport lib/A/AF0m.v, file sha256 390be0f43c79; donor not released) 11 of the 19 differ: A/AB01, AB05, AB12, ACej, AD1k, AD1y, AD2i, AD2j, AE23, AE3i, AF0m. What the core reads
from them:
- A/AD2j.v (f32f53f83a52): IMG_REGIONS has 54 regions, and none meets the hull [0x5df080, 0x5f3190): R_A5a_1 ends at
  0x5df080, R_A5a_2 starts at 0x5f31e0 (records/ghunks.txt, measure_gcut.py: `hull_meets 0`, `clip_identity true`).
  port_core recomputes the core's region counts on this list (`region counts recomputed 50`).
- A/AD1y.v (cd08f8cdb321): DRV_G_LO 0x5df080, DRV_G_HI 0x5f3190 (AD1y.v:25-26), the driver windows DRV_IVS (:27) with
  DRVW_not_G (:54), and region_avoids_G with region_avoids_G_sound (:215-222). The G patches use these names; no core
  file restates them.
- A/AF0m.v (5dfdd0e65356): the one change against the earlier layer's file is in Tfib_owned_static: the row (0x10338, 8)
  (AF0m.v:3115) with its constant cell `z8 (ANum 0x10338) 0xf5f5f5f5f5f5f5f5` (:545). Tfib_zero_shadow (:3105, 25 ranges)
  is the same list and still holds both pieces bss-zero-range.patch names.

`not-relocated-startup-layer.txt` passes the 19 to `--no-stage`, with Reusable/YI0a.v and YI17.v (cgif's shape files,
not in LIB): 21 entries, 0 staged; the run log names the 19 as kept. The dry runs work-rec and work-rec2 read T3r's
earlier layer (A/AF0m.v 390be0f43c79, A/AD2j.v db4ad395250e: 70 regions); work2 and work83b read row T3's old-pin
stand-in (libdiginet/fuzz_transport lib/A/AF0m.v, file sha256 3b58b624cb9e; donor not released).

## Trunk files the run needs

- The composition kit: the 17 files port_core expects in the trunk lib and the new-pin base lacks (A/RelimCut.v,
  Reusable/YK0j YK0t YK18 YK1e YK1g YM08 YM09 YQ00..YQ06 from fuzz_grant's released lib at 25e3d17bdb50;
  Reusable/HaltsKitB.v and YJ00.v from libreac/fuzz_decode's at bf7779f81ed7), written by `add-kit.sh` with one change
  per file, the module path. `kit-rec.tsv` is its table for the run of record: per file the donor path and commit, the
  donor blob, the written blob, the number of module paths changed; byte-equal to the dry runs' table. Measured: 17 of 17
  written blobs equal the files of the LIB the run read and of this tree's lib. The run
  reports `kit-file-staged 0`.
- lib/A/TransportShape.v (file sha256 caa68b81b1f5): transport_shape := ag_shape kept_shape and transport_plain_rz_stmt,
  libdiginet/fuzz_frame lib/A/FrameShape.v (file sha256 a947a413a58a; donor not released) with the names changed; the Require stays FrameSlotK (the
  unit's lib/FrameSlotK.v). `ad1q-shape.patch` makes A/AD1q.v take it. The run's FAIL row `forbidden-module
  Reusable/YI5c.v (import path: YI5c <- FrameSlotK <- TransportShape <- AD1q)` is D9's row with DecodeShape.
- Reusable/YImgTop.v, taken by path: libdiginet/fuzz_frame lib/Reusable/YImgTop.v (file sha256 598a5c3875fe; donor not
  released; libreac/fuzz_decode's released YImgTop.v over one image) with fuzz_frame's added notice line left out, the unit name changed, and the measured last loaded segment:
  fuzz_transport.asan's last PT_LOAD vaddr 0xa5d88, memsz 0x56f648, end 0x6153d0, so IMG_TOP_val 0x616000. Measured: after
  the name change it differs from fuzz_frame's in exactly those 3 lines; sha256 e4d179ca9a5a, this tree's file.
- lib/A/W_journalG.v (file sha256 afd0c41a8ecd): the G journal (inG, ajournal_gx, ajournal_gx_inner,
  ajournal_gx_G_mono), pcap's Sections a and b. g-ACfn and g-AD1w Require it; it is not part of this slice's run LIB, so
  required.tsv lists it (above).
- lib/A/TransportDrvG.v (d94ee4caa8e6) and lib/A/TransportDriver.v (c5e7bbb55e4f), the two new files of the G work
  ("G patches" below); g-AD1r and g-AD1q Require them.

## --generated entries and slots

No --generated entry is passed. port_core's default set (24 entries with their Y twins) are --no-stage start-up files or
Y files not in core-files-transport.txt, so the run applies 0 slots (`generated slots applied ...: 0: none`).
required.tsv holds the 4 require-unresolved rows of the G patches (above) and no value row. `core-files-transport.txt` is
the release's core-files.txt (sha256 384356fd372f) less YI0j.v and YO08.v, as fuzz_frame's and fuzz_decode's lists (623
of 625 lines).

## G patches (the harness globals)

The record of the G work is records/ghunks/GHUNKS-A-rec3.md (it replaces sections 0 and 4-8 of records/ghunks/GHUNKS-A.md;
section 3 there, the classification of every pcap-vs-grant hunk, still holds). The integration owner's decisions of 01:50Z
and 02:03Z (path (a)):
G hunks only, as port_core `--patch` files on the core's own donor text; the slot's G stays a parameter on the program
side; the hull is the cut start-up layer's.
- The G form. A/ACfn.v takes `Variable G` and states its post journal `ajournal_gx segs B G 0 []` (pcap's
  Prog/PcapEntry.v:33, :61 on the core's own contract file). The driver's own statements fix G to the hull DRV_G
  (A/AD2f.v `DRV_G := [(DRV_G_LO, DRV_G_HI - DRV_G_LO)]`, the bounds from start-up AD1y): lib_site_x (A/AD1w.v) and LIBC
  (A/AD1m.v, A/AD1p.v) state the call at DRV_G. The two meet in A/AD1q.v (pcap's PcapDriver.v), which takes `Variable G`,
  `G_HULL : g_in_hull G` and LIBX at G, and lifts LIBX to the hull with TransportDriver.v. A/AD1r.v's consumer reads the
  driver journal through TransportDrvG.v's drv_journal_of_gx, from a start memory that agrees with mem outside the hull.
  The program side owes `g_in_hull G_HARNESS` (18 payload ranges in [0x5df080, 0x5f3190)).
- The 7 patches (sha256 first 12): g-ACfn 541e4c4696b9 (4 hunks), g-AD1w ed41960ef097 (2), g-AD1m 58f8cadc9122 (1),
  g-AD1p 2b55df460405 (1), g-AD1q c353e5cf6157 (3), g-AD1r 258880fd6cad (8 hunks, 20 edits), g-AD2f f9d48ede68ec (3:
  DRV_G, the hull clip in IMG_L / IMG_LC / L_pieces (outermost), L_mem_avoids_G). g-AD2d, g-AD2e, g-AD1x and the IMG_L /
  IMG_LC / IMG_XL count rows of the first version are dropped: on the cut layer no region meets the hull, so the clip
  returns every region unchanged and the counts port_core writes stand (IMG_L / IMG_LC 56, IMG_XL 57, each `stands` in
  measure_gcut.py's output).
- No value row: the hull 0x5df080 / 0x5f3190 is the payload start of g_cfg and the payload end of OW (0x5f3060 + 304),
  the first and last of the 18 writable harness globals in the twin's asan_globals (40 descriptors; asan_globals.py),
  stated once in the start-up AD1y and equal to it (measure_gcut.py: `AD1y_DRV_G_LO ... equal`, `AD1y_DRV_G_HI ...
  equal`).
- The two new files: TransportDrvG.v (inG_DRV_G_hull, drv_keep_set = pcap's five disjuncts DRVW, STDOUT_MUT, in_ro_tfa,
  finv_img, CEIL_MIN <= a; drv_keep_not_G from AD1y's DRVW_not_G; drv_journal_of_gx at DRV_G) and TransportDriver.v
  (g_in_hull over DRV_G_LO / DRV_G_HI, tfib_lib_contract_x_all_hull, the lift). Both Require AD1y. global_settings v10
  reads both (records/settings-count.txt).
- Checks: gate ghunks (checks/ghunks-A.sh, records/ghunks.txt) on the run of record: the 7 G patches undo on WORK's
  stage-out and re-apply on the 6-patch text to exactly WORK's text (check_gpatches.py: each `rc=0`, `patched text vs
  stage-g: equal`, round trip `equal`); the hull and the counts measured again; two controls. The G work's own check on
  work-rec3 is records/ghunks/check_gpatches.out (its control: one context line altered, `Hunk #1 FAILED at 14`), its
  measurement records/ghunks/measure_gcut.out, and the control on the uncut list records/ghunks/measure_gcut-control.out
  (`clip_identity false`, 72 -> 55 and 73 -> 56: the counts that would change on T3r's earlier 70-region list).
- Not verified here: the build. GHUNKS-A.md section 9 items 1 and 3 (ajournal_gx_G_mono / ajournal_gx_inner take no
  Section hypothesis; region_avoids_G_sound's lia and the NG lias in A/AD1r.v) are for the whole-unit build to confirm.

## Values stated against the image (overrides.tsv)

59 rows in 19 groups; each group in overrides.tsv carries its measured reason. The values were measured by role with
measure_overrides.py (row TCA's preparation; measure_overrides.py, sha256 a96e0e4d5091; internal record), which gives
fuzz_frame's rows exactly on fuzz_frame.asan (its control). The run reports 37 rows `applied` and 22 `removed by --patch`:
the A/AD1o.v and A/AD25.v zero-shadow rows, whose lines bss-zero-range.patch then rewrites (the patch's removed lines
carry the override values). L4: `NO-FILE` rows in the run's overrides.tsv: 0.

| group (rows) | value and measurement |
|---|---|
| stdout buffer (9) | the 8 bytes at __stdout_FILE 0xa8738 + 88 (FILE.buf) hold 0x614200 (grant 0x5f81e0): A/AD1o.v:196, 248, 284, A/AE3m.v:34 STDOUT_BUFA; in decimal 6373888 at A/AD1j.v:113, 121 (2 occurrences), 134, A/AE3m.v:559, 1069. T3r's exit-driver control C7 reads the same value on e89be137db17 |
| stderr buffer (2) | __stderr_FILE 0xa8648 + 88 holds 0x6141f8 (grant 0x5f81d8): A/AD2f.v:147, A/AE2p.v:30 |
| stdin buffer (1) | __stdin_FILE 0xa8828 + 88 holds 0x614608 (grant 0x5f85e8): A/AD2f.v:147 |
| format windows (10) | [floor8(shadow(fmt)), floor8(shadow(fmt + len)) + 8) of 'cli: cannot open %s\n' 0x1d848, 'cli: read error on %s\n' 0x1d85d, 'cli: input >= %u bytes, refused\n' 0x1980a, 'usage: %s INPUT\n' 0x15897, '%d\n' 0x1481c: A/AE2t.v, AE2u.v, AE2v.v, AE2w.v:63, A/AE35.v:64 |
| BUFEND (1) | 6374912 = 0x614200 + 1024 (buf_size at FILE + 96): A/AE3m.v:1071 |
| TFIB_BSS (10) | 0xa9340 = __stop_asan_globals, the end of section asan_globals (grant 0xa1460): A/AD1o.v:80-99, A/AD25.v:528-545; 693056 in decimal |
| image end (7) | the last PT_LOAD [0xa5d88, +0x56f648) ends 0x6153d0, paged up 0x616000 (grant 0x5fa000); 6381568 in decimal |
| .bss + 0x20 (3) and quotients (3) | 0xa9360 = __do_init.__object + 16; 0xa9360 / 8 = 86636, 0xa9340 / 8 = 86632, (0x616000 - 0xa9340) / 8 = 711064 |
| tfib_at_rw_len (1) | 0x571000 = 0x616000 - 0xa5000, the last PT_LOAD's page range (grant 0x55c000): A/AB1w.v:599 |
| AD1g static_img_chk (1 row, 2 occurrences) | 0x10000, the first PT_LOAD's vaddr |
| CZONE (9) | 0x800b9c00, below |
| TOT_range (2) | 127008, below |

No row: R_A3 = [0xa8600, 0xa8940) = 832 bytes, grant's 832 by the same two roles (__stderr_FILE - 0x48 to
__start_asan_globals); A/AF0l.v (the class map is port_core's from fuzz_transport's own __asan_stack_malloc_*; run log:
`class map 1 (0=0x3d698, 1=0x3d80c, 2=0x3d99c, 4=0x3db38, 5=0x3dd04)`); tfib_rodata_hi, which 83f5203d2a2f's item 97 writes
as the section end 0x22b4c from the pin's section headers (.rodata [0x102e0, 0x22b4c)).

## Values this unit states otherwise than the donor

Three values are not the donor's quantity moved to this image. Each is derived from this unit's own definitions and
image, and the whole-unit build is the check for the first two.

1. CZONE 0x800b9c00 (A/AFhn.v:419, AFix.v:285 and 289, AFjb.v:284 and 288, AFju.v:576 and 586, AFkm.v:1305, AFkz.v:898,
   donor lines). The donor's 0x80050000 is a page-aligned bound, not the shadow of an object, and it is below this unit's
   highest constant shadow cell end 0x800b663c (records/czone.txt: the 40 asan_globals descriptors of the twin, highest OW
   0x5f3060, shadow end 0x800b663c; T3r's A/AF0m.v Tfib_const_shadow highest byte 0x800b663b), so port_core refuses it
   (czone-bound). The dry runs used 0x800bac00 = 0x7fff8000 + 0x616000 / 8, the shadow of the image top. The build of the
   work-rec core failed at A/AFju.v:663 (CZ_untouched, case 2). A debug build printed that goal
   (its log: removed from the shipped tree on 2026-11-04; internal record, in git history): `Ha : (2147450880 <= a < 2148248576)` (the CZONE window [0x7fff8000,
   0x800bac00)) and `SM1 : (2147446784 + 6381568 / 8 <= SMv)`, map_facts SM1 of A/AFjm.v:305, `kLowShadowBeg +
   TFIB_IMG_END / 8 <= SMv`, with kLowShadowBeg 0x7fff7000 (Reusable/YG0f.v:22). The goal needs a < SMv, and SM1 only
   gives SMv >= 0x7fff7000 + 0x616000 / 8 = 0x800b9c00; a bound of 0x800bac00 leaves the 4096 bytes [0x800b9c00,
   0x800bac00) where the map window can start. So CZONE is 0x800b9c00 = kLowShadowBeg + IMG_TOP / 8, the least start of
   the secondary map's shadow, and still above 0x800b663c. port_core's partner-left rows (the window start 0x7fff8000 is
   the shadow offset, kept) are expected.
2. The A/AD1o.v and A/AD25.v zero-shadow ranges (bss-zero-range.patch). The donor's lemmas take ONE zero-shadow range
   over the whole .bss after asan_globals, [TFIB_BSS, IMG_TOP). In this image the 18 instrumented harness globals cut
   T3r's A/AF0m.v Tfib_zero_shadow (line 3105, 25 ranges) into pieces, so no such range is in the list, and the build of
   the work-rec core failed at A/AD1o.v:85 and A/AD25.v:533 (`No applicable tactic`). Each lemma now takes the piece of
   Tfib_zero_shadow its consumer needs: A/AD1o.v bss_zero_shadow the range (0x5f31e0, 0x616000 - 0x5f31e0), which holds
   the stdout buffer 0x614200 (bound 0x5f3200 = 0x5f31e0 + 0x20 in place of .bss + 0x20; 0x5f3200 / 8 = 779840,
   0x5f31e0 / 8 = 779836, (0x616000 - 0x5f31e0) / 8 = 17860, 0x5f31e0 = 6238688); A/AD25.v rs_zero_shadow the range
   (0xa9340, 0x5df0b8 - 0xa9340), which holds the read window [0x5cf050, 0x5df050). Both ranges are AF0m.v:3105 entries
   verbatim.
3. A/AFem.v TOT_range 127008 (donor lines 128 and 206; override rows). TOT := length (ly_tr0 ly) + 1 + depot_frames S
   (A/AFem.v:99) with length (ly_tr0 ly) <= 31 (Reusable/YG0f.v:326 lo_tr0) and depot_frames <= 31 * length d (A/AFem.v:39-40
   depot_frames_bound), DEPOT_MAX = 4096 (Reusable/YG01.v:142): TOT <= 31 + 1 + 31 * 4096 = 127008, a count. The donor's
   127070 is that count moved by a code-address shift in an earlier relocation; port_core moves it as an address at
   A/AFem.v:206 and reports `FAIL value-role-conflict`; the override rows write 127008. The atom range `(aTOT, mkAF 2
   131072 0)` (A/AFek.v donor line 34) stays: 131072 is cgif's own slack range, and the memory cell at TFIB_STORE also holds
   the post-store value TOT + length tr + 1 <= 127008 + 30 + 1 = 127039 (tr_len A/AFem.v:122, store A/AFem.v:1247).

The relocation tool's reviewer's limits of every port_core run (02:43Z), on the run of record: L1 no override row moves an interval delta (the only
interval-shaped rows are the two TOT_range bounds, whose partner 2 is no address); L2 hypothesis lines with a trailing
comment in the 492 staged files: 0 (no Hypothesis / Hypotheses / Variable / Variables / Context line carries a comment),
so none to check by hand; L3 FAIL tot-bound rows: 0 (and interval-delta rows: 0); L4 `NO-FILE` rows in the run's
overrides.tsv: 0.

## Patches

Each applies with no offset or fuzz (the run's patches.log: `patching file` lines only, 14 patches). The first 6 and
afet-cost add no comment line; the G patches add 9 lines that hold a comment `(*` (g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q
1 each, g-AD1r 2, g-AD2f 2), each saying what the G hunk under it states, for example A/ACfn.v:30-31.

- zero-shadow-forallb.patch (A/AFex, AFf0, AFf3, AFf4, AFfl, AFjy): the case splits over grant's Tfib_zero_shadow ranges
  become one forallb check decided by vm_compute, so the proofs hold for the unit's own list; D9's patch re-cut against
  this run's stage-out.
- cell-lookup.patch (A/AFim, AFin): the const-cell lookup by index into grant's list becomes AF0x.cell_lookup_In decided
  by vm_compute; byte-equal to D9's (sha256 a4cff1a229c0).
- ad1q-shape.patch (A/AD1q): `GrantShape` / `grant_shape` become TransportShape / transport_shape.
- imgtop-alias.patch (A/AB1w, ACeg, AF0x, Reusable/YCbq, YCe5): the image bounds YImgTop computes are written as the
  numeral vm_compute gives, with `_eq` lemmas in ACeg and AF0x, so the donor's `unfold ...; lia` proofs see a number.
- dead-arm-ad1g.patch (A/AD1g, tfib_layout_ok, donor line 1069): removes the dead arm `|| (change 6316032 with (1482 *
  4096); apply Z_mod_mult)`. The term is kImgEnd - kImgLo = 0x616000 - 0x10000 = 6316032 = 1542 * 4096; the donor's
  1482 * 4096 = 6070272 can never match, and the arm before it closes the goal. Cut against the stage-out before
  port_core's item 95 recomputes the count, because port_core applies patches first.
- bss-zero-range.patch (A/AD1o, AD25): the zero-shadow pieces, item 2 above.
- g-ACfn, g-AD1w, g-AD1m, g-AD1p, g-AD1q, g-AD1r, g-AD2f: the G patches, section "G patches" above. g-AD1q applies on top
  of ad1q-shape.patch (both touch A/AD1q.v).
- afet-cost.patch (A/AFet.v, sha256 9f5dfea19198): a proof-script cost fix, no statement changed. Four blocks of A/AFet.v
  (FIN_a lines 294-295 and 302-303, DRPRE 483-484 and 491-492, each the sub-proof `assert (Hv : v = AV (ANum 0))`) split
  `In c (Tfib_const ly)` one cell at a time (`cbv ... in Hc. repeat (destruct Hc as [Hc|Hc]; ...)`), so time and memory
  grow with the square of the cell count, most of it in `Qed`. Each block now checks `forallb (...) (Tfib_const ly) = true`
  by `vm_compute; reflexivity` and takes v = AV (ANum 0) from it. Each block keeps two lines (no line moves), and the new
  lines hold no numeral. The reason is this unit's cell count (records/afet/AFET-COST.md, the lane report; build log
  line 51, removed from the shipped tree on 2026-11-04; internal record, in git history):

  | unit | cells of Tfib_const (sym + abs + shadow) | A/AFet.vo time / peak memory |
  |---|---|---|
  | fuzz_transport (before the fix) | 22 + 568 + 2490 = 3080 | 7936 s / 43.3 GB |
  | fuzz_transport (afet-cost.patch, MEM=24g) | 3080 | 8.48 s / 0.7 GB |
  | libdiginet fuzz_decode | 369 | 90.9 s / 1.67 GB |
  | fuzz_reply | 792 | 297-397 s / 3.6-4.2 GB |
  | fuzz_wire | 310 | 50-55 s / 1.25 GB |
  | fuzz_pcap | 330 | 55-70 s / 1.45 GB |

  The integration build (MEM=24g) had killed A/AFet.vo at 24 GB. A/AFet.v is the same text in transport, grant and decode
  except module paths and the Syms rename; what differs is Tfib_const in the start-up A/AF0m.v. The lane built the fixed
  file on the interim lib (work-rec2's 492 files); for the changed lines the run of record's lib gives the same input (AF0x.v and
  YG0f.v identical; AF0m.v differs only by the added cell `z8 (ANum 0x10338)`; the report's "Not run" section).

There is no ab1w-text-hi patch (D9 had one): 83f5203d2a2f writes each tfib section cell from the pin's section headers;
the section-cell check finds 22 of 22 equal (records/secbounds.txt).

## Header rule

Each staged file is the donor's text with module paths, the four renames (GrantB, GrantSyms, GrantB_syms, GrantB_ok ->
Transport*) and relocated values changed, plus port_core's one registered provenance line. `hdrcheck.py` checks the form;
then `reusable-local.py` (reac-repacer/fuzz_uci's core-B script, its bytes, sha256 f3b058010eab) makes the shared Zify
redefinitions of Reusable/YA09.v and YA0e.v `Local` and checks each file's code against fuzz_grant's released lib/B copy.

## Gates

Every gate and check ran on the run of record (WORK = work-rec5, LIB as above) through one command:

    P=<fuzz_transport images, result/bin/ + unstripped/> TIMG=<fuzz_transport pins, stripped/ + unstripped/>
    PG=<fuzz_grant images> DON=<fuzz_grant's released lib, normalised> HUB=<the hub repository>
    CKDIR=<port_addr_check directory> DONORS=<port_addr_check's donor tree> ALRELOC=<alreloc.py.frozen-a5c53bb2bed4ad03>
    MANIFEST_ELF=<fuzz_manifest.asan> CGIF_ELF=<cgif_file_fuzzer.asan>
    PINS=<this tree's projects/libdiginet/fuzz_transport/harness.yaml, sha256 31f9695f19a5>
    UNIT_FILES="<this tree's lib/A/TransportDrvG.v> <lib/A/TransportDriver.v>"
    checks/run-gates.sh WORK LIB OUT

records/run-gates.txt has each gate's own single command over WORK LIB OUT/<gate>, its exit status and wall time, and the
sha256 of every script. run-gates.sh takes EV (the run's inputs) as this directory and extracts the registry's tool
directories (start-up set 2026-10-30d, atable 1ce98fbad397, roundconst-gate 32b39f3b34e9, global_settings 439f8e3bd463,
yh03check fb3bfbc1eea8) from HUB at the tool registry's commit TOOLS_REF (its README.md, sha256 05596ed48d98; internal
record).

The scripts are the gate lanes' scripts of the dry runs (adapted from D9's), with these changes, each for a measured
reason: no script holds a host path (every input is a named variable); decval_hand.py no longer crashes on an address
outside the loaded image (A/AD25.v's donor 0x5fa000) and decval-A.sh, run-all.sh, compcheck-A.sh, gotwords-A.sh,
symoff-A.sh, hypvalues.sh and codeptr-A.sh exit non-zero when a step or a control fails (a crashed step had left an exit 0
with missing result lines); pac-A.sh and flag-gate-A.sh run port_addr_check 205a90fd19b8 (the version of record after
08:00Z; pac-A.sh checks the version's own SHA256SUMS, passes its own --cache, and names the triage outputs by the checker
sha); triage-A.py's K-CZONE rule takes this unit's CZONE derivation, and its new rules take the zero-shadow pieces
(P-BSSZR), the numerals of the G patches (P-GHUNK), the lines next to afet-cost.patch's hunks that the checker leaves
unpaired (P-LINEPAIR: paired by line and by symbol + offset) and the image span in A/AD1g.v static_img_chk that
205a90fd19b8's size-name slot rule flags (N-IMGSPAN); alreloc_decide.py's czone group also checks the upper limit
kLowShadowBeg + IMG_TOP / 8, and two groups take a donor line a patch rewrote (the rewritten line keeps the numeral) and a
comment line a patch added that names a target symbol next to its address; hypderive.py's KNOWN CZONE row names 0x800b9c00
with its derivation, its COUNT rule decides the start-up region counts (IMG_E, IMG_B, PM_tailL) against LIB/A/AD2j.v when
that file reads the pin (it said NEEDS-STARTUP for every LIB before), and its GPATCH rule takes a numeral below 0x10000 on
a line a G patch added; flag-gate-A.sh and triage-A.py list every patch; codeptr-notaddr.tsv no longer declares the
donor's TOT 0x1f05e (the run writes 127008); compcheck-decided.tsv holds the rows decided by hand; yh03-gate.py runs
yh03check fb3bfbc1eea8 (v6.4, the version of record; it refuses a run without --pinned) in place of ca63d81d7725 /
5e92f52b8caa, and reads by content the cells the registry says v6.4 does not judge (KNOWN LIMIT `not checked by any rule`,
KNOWN GAP NOSYM); v10-gate.py also reads the files the unit writes itself (UNIT_FILES); ghunks-A.sh is new (the G
patches). The dry-run results of the lanes (work2, work83b, work-rec2, work-rec4) stay in the lanes' own directories and
are not cited here. On 2026-10-31 the scripts' comments and printed text were rewritten so that no file names an actor
by its roster name or an unreleased commit (MANIFEST.md); every gate was then run again on the run of record, and
every result row is the same (measured against the run before: each record byte-equal but the edited text, the script
sha256, times and the overrides.tsv sha256). One script change came with it: compcheck.py names the example donor and
target quantities of an a2 row in sorted order (it took them in set order, which differs from run to run with the hash
seed), so records/compcheck-rows.tsv names other examples in its text column; its 4439 rows have the same part,
verdict, place and values. GATES.md has the results; records/ the outputs.
