# DECIMAL-VALUES-uci - by-value check of reac-repacer/fuzz_uci's relocated image-A core

role: check. rule 24: no function proved. Read-only: no file of the worktree was changed, nothing was staged or
committed. The tree read is a clean checkout of commit
`276afc86670b4ccfb478d7c75992f412bd227d74` (`git status` empty),
lib = `proofs/reac-repacer/fuzz_uci/lib`. The method is libreac/fuzz_decode's
(its DECIMAL-VALUES.md and its script `decval.py`, sha256 `43527d3edbc2`), adapted in `decval.py` here.

**Result: 0 DONOR-STALE.** The method's decision tree flags 7 rows; by image bytes, 6 of them are SHARED (the
same bytes are at the same address in both images) and 1 is a constant.

## What was checked

Every numeral, decimal or hex, of every RELOCATED core file, whose value lies in the donor image's address range
`[0x10000, 0x5f93b0)`:

| | image | sha256 | PT_LOAD top (page-up) | rw_lo | entry | builtin_tls / tp |
|---|---|---|---|---|---|---|
| donor | `fuzz_grant.asan` (the libreac build) | `c2c7559b29bd` | `0x5f93b0` (`0x5fa000`) | `0x9e000` | `0x307dc` | `0x5d7a08` / `0x5d7ad0` |
| target | `fuzz_uci.asan` (the reac-repacer build) | `6ea017c24525` | `0x5f3870` (`0x5f4000`) | `0x98000` | `0x2fbf0` | `0x5d1ec8` / `0x5d1f90` |

Symbols come from the unstripped twins. Bytes come from the stripped images of record. The PT_LOAD bounds of the
stripped and unstripped images are the same; the script asserts this.

| relocated core files | numerals in range |
|---|---|
| 569 = 363 `lib/A/*.v` + 206 `lib/Reusable/*.v` | 8519 (A: 8099, Reusable: 420) |

The file list:
* `lib/A`: the `A/` entries of `provenance/core-reloc/A/core-files-uci.txt`, minus
  `not-relocated-startup-layer.txt` (19 A files) and minus `taken-by-path.txt`. This gives 363 files. That is
  exactly the A part of `applied.txt` "copied", and each of these files is byte-identical to port_core's
  `work9/stage-out/A/` (363/363).
* `lib/Reusable`: the 206 `Reusable/` entries of `applied.txt` "copied" (the staged non-A files that the
  integrator copied in), minus the two exclude lists. `YI0a.v` and `YI17.v` (start-up layer) and `AllocSlots`,
  `PlaceCap`, `YO04` and `YImgTop` (taken by path) are not in it.
* Not in the set: `lib/A/RelimCut.v` (it is not in the core list), and the 24 trunk files in `lib/Reusable` that
  are in the core list but were not copied by this run (`YK02 YK0h YK0i YK0j YK0l YK0n YK0q YK0t YK0v YK10 YK11
  YK14 YK15 YK16 YK18 YK1a YK1b YK1c YK1d YK1e YK1g YK1i YM03 YZ00`).

Donor text: `don2/proofs/libreac/fuzz_grant/lib`, normalised as decode's lane A (Reusable moved to the
root). `A/x.v` aligns with `don2/.../lib/A/x.v`, and `Reusable/x.v` aligns with `don2/.../lib/x.v`. This text is
the text port_core staged: for all 363 A files, the sequence of numerals in `work9/stage/A/x.v` (with Require lines
removed) is the same as the sequence in `don2`.

Evidence, as in decode's run (stage 1, `decval.py`):
1. **Donor-file alignment.** Lines are aligned with difflib after every numeral is masked. A numeral is UNMOVED
   when the aligned donor token has the same value.
2. **Image bytes.** Every `Definition W_x` / `fetch_word .. (0xA : word) = Some W_x` pair is read out of
   `fuzz_uci.asan`: **329/329 match, 0 mismatches.**
3. **Symbol, section and segment values** of both unstripped images: `st_value`, `st_value+st_size`, section and
   PT_LOAD bounds and their page roundings, PT_PHDR, `__global_pointer$`, `builtin_tls` and `builtin_tls+200` = tp.

Stage 2 (`decval_extra.py`) adds image evidence for each row that stage 1 leaves to a look by hand. Stage 2 never
relaxes a stage-1 rule. It decides rows with these checks:
* every fetch lemma, in all six forms the core uses, is re-read from the target;
* every word definition is matched to a verified pair, or to a word list or run found exactly once in the target
  `.text`;
* every MOVED value is matched to its twin of the donor value in the target: the same symbol and offset, the same
  bytes, a derived quantity, the same string offset, a jump-table entry, or a memory word;
* every UNMOVED non-comment value that is neither a target nor a shared value gets a context category.

## 1. Control: a planted donor address is flagged

The control was run FIRST, on a scratch copy only (`decval/ctrlA/lib`, a copy of the worktree's lib;
`ctrlA/provenance` is a symlink to the worktree's provenance). In `lib/A/AB1w.v:606`,
`Definition tfib_at_x_memset : Z := 0x90754.` was changed to `0x95e30.`. `0x95e30` is `fuzz_grant.asan`'s
`memset` and is the value that the donor file holds on that line (donor `A/AB1w.v:605`, one header line earlier).
`fuzz_uci.asan`'s `memset` is `0x90754`.

```
A     (unmodified) classes: TARGET 3092  SHARED 615  OTHER 4805  DONOR-STALE 7
ctrlA (planted)    classes: TARGET 3091  SHARED 615  OTHER 4805  DONOR-STALE 8
DONOR-STALE  lib/A/AB1w.v:606  0x95e30  Definition tfib_at_x_memset : Z := 0x95e30.
```

`diff -r ctrlA/lib <worktree lib>` shows only that line. `diff <(cut -f1-7 A.tsv) <(cut -f1-7 ctrlA.tsv)` shows
one row: `lib/A/AB1w.v 606` changes from `TARGET (unmoved False)` to `DONOR-STALE ... unmoved True`. The planted
value is the only row that moves, and it moves from TARGET to DONOR-STALE. The 7 DONOR-STALE rows of the
unmodified tree are the same in both runs. Section 3 decides them.

## 2. Counts per class

"TARGET" is the class decode calls DECODE: the value is the target image's.

| class | stage 1 (decode's decision tree, unchanged) | final (after stage-2 image evidence) |
|---|---|---|
| TARGET | 3092 | 6791 |
| SHARED | 615 | 708 |
| OTHER | 4805 | 1020 |
| **DONOR-STALE** | **7** | **0** |
| total numerals in the donor range | 8519 | 8519 |

Stage 1, by the evidence that decided each row (decode's reason table):

| reason | rows |
|---|---|
| TARGET - target symbol / section / segment value | 2437 |
| TARGET - fetch/word pair (stage 2 re-verifies all of these rows, below) | 632 |
| TARGET - target value that is also a donor value, but the relocation moved it here | 23 |
| SHARED - same value in both images | 615 |
| OTHER - no address role (constant, count, label, instruction word) | 4532 |
| OTHER - decoded field of a verified instruction word | 117 |
| OTHER - comment numeral | 137 |
| OTHER - comment numeral that names the donor value by design | 19 |
| DONOR-STALE - address-role field, unmoved from the donor file, no target value | 7 |
| DONOR-STALE - donor image value, unmoved from the donor file | 0 |

Stage 2, how each class changed:

| stage-2 decision | rows | evidence |
|---|---|---|
| stage-1 TARGET stays TARGET | 3092 | fetch rows 476/476 re-read from the target; word rows 156/156 verified (see below); all 2812 moved rows (fetch, word and value) are the donor value's twin (same symbol and offset); the 15 unaligned rows (`AB1w.v:87`, `AE6x.v:477,479`, `AE7d.v:477,479`, `AF0l.v:13`) are target symbol values |
| stage-1 OTHER, moved -> TARGET | 3699 | its donor value's twin in the target: symbol+offset 3444; 16 bytes around the address are equal 182; derived quantity 33; same offset in the same string 30; jump-table entry 6; the target holds that word at the stated address 4 |
| stage-1 SHARED stays SHARED | 615 | the value has the same role in both images (list below) |
| stage-1 OTHER -> SHARED (bytes) | 80 | the address is in the byte-identical `.rodata` prefix `[0x102e0, 0x12368)` of the two images |
| stage-1 DONOR-STALE -> SHARED (bytes) | 6 | the same (section 3) |
| stage-1 OTHER (Coq bullet read as a comment) -> SHARED | 7 | `0x10000` / `65536`; the same value in both images |
| stage-1 DONOR-STALE -> OTHER | 1 | `kNodesBlockSize 0x100000`, a size (section 3) |
| stage-1 OTHER stays OTHER | 1019 | comment 142; decoded field 117; instruction-word literal handed to `icpt_ld8` 216; model label 42; mmap flag sums 33; allocator / trace sizes 62; constant / size / mask / bound 402; instruction word 3; line inside a multi-line comment 2 |

Stage-2 details:
* **Fetch rows, 476/476 verified.** This covers the 329 `W_x` pairs and every other lemma form:
  `(Z_to_bv 64 (BASE + off))` with BASE resolved from its `Definition` (`tfib_A_musl_memcpy 0x90350`,
  `tfib_A_musl_memchr 0x90254`, `tfib_A_musl_memcmp 0x90320`, `tfib_A_musl_memset 0x90754`, `A_ISL 0x62914`),
  `(0xA%bv : word)` and `(Z_to_bv 64 0xA)`.
* **Word rows, 156/156 verified.** 85 have a verified fetch pair. 27 are in the lists `imemcpy_words`,
  `imemset_words`, `istrncpy_words` and `memisz_words`; each list occurs exactly once in the target `.text`, at
  `0x62744`, `0x627c0`, `0x62bec` and `0x62cf0`, which are the `tfib_at_x_imemcpy/imemset/istrncpy/memiszero`
  values of `AB1w.v`. 38 are the dead `W_c96ec..` run of `Reusable/YB1o.v`, which no file uses; it occurs once in
  the target, at `0x50510` (`__sanitizer::Sort<ioctl_desc>`). 6 are `PW0..PW7` of `Reusable/YFk4.v` and
  `Reusable/YK0a.v`, which occur once in the target, at `0x35fdc` (= `tfib_at_x_popfree`, inside
  `PopulateFreeArray`).
* **Derived moved values (33)**, each derived from the same anchor in both images:
  * `x/8` of `img_top_up` (21). The image top is `0x5fa000` in grant and `0x5f4000` in uci.
  * `x/8` of `img_span` (4).
  * `x/8-1` of `img_top_up` (1).
  * `x/8` of `internal_alloc_placeholder` (2): `84904 -> 81984`; uci's placeholder is `0xa0200`.
  * `x/8` of `__asan::instance+0xa8` (1): `82608 -> 79688`.
  * `x/4` of `theDepot` (1): `400006 -> 394166`.
  * `x/8` of `__do_init.__object+0x10` (1).
  * `x/8` of `asan_globals` end (1).
  * `(img_top_up - __stop_asan_globals)/8` (1): `700788 -> 700638`.
* **String moved values (30)** are the same offset inside `"cli: read error on %s\n"`, which is at `0x1d7c5` in
  grant and `0x1d5fb` in uci.
* **Jump-table moved values (6)**: the addresses `0x218c8/0x218cc -> 0x21240/0x21244`. In both images, each
  entry's address plus the entry it holds lands at the same `sysconf` offset. All 8 entries of that table agree,
  and the 26 entries of `VSNPrintf`'s table (`0x20b9c -> 0x209bc`) agree too. The two entries the proofs read are
  `0x64ec8` at `0x21240` and `0x44f0c` at `0x20a1c` (the four "memory" rows), and they are in the target's bytes.
* **No moved row is left without a twin** (0 of 6511).
* **Unmoved values inside a donor symbol whose twin moved.** This would be a donor interior address that should
  have moved. The 666 rows of this kind are all non-addresses:
  * instruction words: in `decode_any` lemmas, the `icpt_ld8` literals `0x7b783`, `0x73703`, `0x83803`,
    `0x8b883` and `0x6b683`, and the `0x5c603` table lookup;
  * allocator constants: `262144` = `kUserMapSize`, `0x3fff8`, `0x3ffff`, `1048576`, `131072` =
    `kPtrArrayCommit`, `AMETA_SIZE 3727360`, `kFakeStackSize/8 1446400`;
  * the mmap flag sums `0x100022`, `0x100032`, `0x104022` and `0x104032`;
  * the kernel model's `mcheck` / `fail (FCheck pc)` / `spin` / `ISpin` labels: `201364`, `201376`, `202260`,
    `209280`, `210276`, `212388`, `213516`, `219184`, `221048`, `222820`, `391236`, `449860`, `460508` and
    `469488`. These are the same values that `lib/Reusable/YG00.v` holds, and the A files restate the YG00 body
    with them, so they have to stay equal to the kernel;
  * trace sizes in `YO0f` / `YO0i` (`200000`, `200020`, `200100`, `200704`, `400000`, `401408`);
  * bounds: `PID_MAX 4194304`, `280000`, `2240000`, `2239000` and `2107576`;
  * the stretch length `262728` (`AFfg.v`). It equals `0x40000 + 584`, which uci's own code computes:
    `lui x19,0x40` at `0x5cd68` and `addiw x12,x19,584` at `0x5cd98`, in `__sanitizer::internal_allocator`.
* No unmoved non-comment value equals a donor geometry quantity that changed in uci (segment page sizes, image
  span, image top / 8, and so on), except `0x20000`/`131072` (77 rows). Every one of those rows was read: they are
  allocator constants (`kPtrArrayCommit`, `2^17`, trace bounds), and none is segment 0's page size. Grant's segment
  0 page size is `0x20000` and uci's is `0x1f000`; the 4 rows that use that size (`AD1o.v:25`, `AE39.v:37`,
  `AE6x.v:95`, `AFia.v:133`) moved to `126976`.
* `tfib_A_` / `tfib_E_` table (`AB1w.v`): 1042 rows, **0 donor rows**. Stage 1 counts 1034 target values and 8
  "interior" rows (lines 72, 158, 172, 245). Those 8 are starts of duplicate-named local symbols
  (`__asan::MemToShadow` copies) and the next function's start. They are absent only because the method keys
  symbols by name. Counted against every target symbol, duplicates included, all 521 A rows are starts and all 521
  E rows are ends or next starts. Each of the 8 is also the twin of its donor row (`MemToShadow+0`,
  `InitializeFlags+0`, ...).

### SHARED: every value and why it is equal in both images

| value | rows | why it is the same in `fuzz_grant.asan` and `fuzz_uci.asan` |
|---|---|---|
| `0x10000` / `65536` | 603 + 7 | image low / PT_LOAD 0 base (both); also the 64 KiB constant (`kCtxMapSize`, page sizes) |
| `0x10040` | 1 | PT_PHDR vaddr (both): `AB1w.v:601 tfib_at_ph_addr_z` |
| `0x102e0` | 1 | `.rodata` start (both): `AB1w.v:11 tfib_rodata_lo` (`tfib_rodata_hi` moved to `0x22584`) |
| `0x10800` / `67584` | 8 | `__global_pointer$` (both): `AB1w.v:23 tfib_gp`; gp register in `AD23.v:306,308,309` and `AD2f.v:156,232,278` |
| `0x55c000` / `5619712` | 2 | `rw_len` = image top - rw_lo: `0x5fa000-0x9e000` in grant, `0x5f4000-0x98000` in uci. The length is the same from different bounds (`AB1w.v:600`, `AFia.v:133`) |
| `0x102e8 0x10308 0x10328 0x10350 0x10368 0x10370 0x10398 0x103a0 0x103b0 0x103d0 0x103d8 0x10420 0x10520 0x10560 0x10b54 0x117fe` | 86 | addresses in `[0x102e0, 0x12368)`, where `.rodata` is byte for byte the same in the two images (the first differing byte is at `0x12368`): the MurmurHash constants `D_consts`, `HIGHS 0x8080808080808080` and `ONES 0x0101010101010100`, `FF_mask` (`0xafffff00000fffff`), the CTZ tables, the `"-+   0X0x"` digits string (`68436`, the memcpy source in `AE3j`), `"<sealed>"` (`0x117fe`), and the `MC_LO/MC_HI` and assert-message bounds |

### Sweeps (every numeral of the 569 files, in any range)

| value | rows | where |
|---|---|---|
| fuzz_grant `builtin_tls 0x5d7a08` / tp `0x5d7ad0` (`6126088` / `6126288`) | **0** | - |
| fuzz_grant `0x5d7a48` / `0x5d7b10`, the values decode's DECIMAL-VALUES.md quotes for grant | **0** | - |
| fuzz_grant image top `0x5fa000` | 2 | `AD1g.v:4`, `AFjy.v:4`: the cgif -> grant history note in a comment |
| fuzz_grant rw_lo `0x9e000`, entry `0x307dc`, last PT_LOAD end `0x5f93b0` | **0** | - |
| cgif `builtin_tls 0x5d8ec8`, tp `0x5d8f90`, image top `0x5fb000`, entry `0x3030c` | **0** | - |
| cgif rw_lo `0x9f000` | 2 | `ACeg.v:24 A_uar_glob`, `AD2l.v:23 as_uar_cell`: this is uci's `__asan_option_detect_stack_use_after_return` (`0x9f000`, size 4; grant's is `0xa4b40`, which these lines held in the donor). It equals cgif's rw_lo only by chance |
| gp shifted as a data address, `67608` / `0x10818` (decode's TAGSCAN fault) | **0** | - |
| `__global_pointer$ 0x10800` (both) | 8 | listed under SHARED |
| fuzz_uci tp `0x5d1f90` / `6102928` | 17 | e.g. `AD2f.v:156,232`, `AD23.v:306-309`, `AD1j.v:114` |
| fuzz_uci image top `0x5f4000` | 100 | - |
| fuzz_uci rw_lo `0x98000`; entry `0x2fbf0` | 2; 4 | `AB1w.v:599`, `AFia.v:133`; `AB1w.v:12,23,24,598` |

gp-relative window `[gp-0x800, gp+0x800) = [0x10000, 0x11000)`: the values found are `0x10000`, `0x10040`,
`0x10800`, the rodata-prefix addresses above, and the constants `0x10002 0x10060 0x10101` (`65538`, `65632`,
`65793`). None of these has bytes that differ between the images.

Shadow window of the image (`>= 0x7fffa000`, outside the method's range; checked as decode did). 195 rows: 14
moved and 181 unmoved.
* The unmoved values are image-independent: `0x7fffa000` (shadow of `0x10000`), `MAX_RW_COUNT 0x7ffff000`,
  `0x7ffffff0`, `INT_MAX`, `0x80000000`, and the CZONE bound `0x80050000` (kept by `overrides.tsv`). There is also
  one comment, the grant history note of `AE35.v:5`.
* The 14 moved values are fuzz_uci's:
  * the `SH_LO/SH_HI` format-string windows of `AE2t/u/v/w` and `AE35` (for example `AE35.v:65`
    `0x7fffa8e8/0x7fffa8f0` = the window of `"cli: out of memory\n"` at `0x1474f`);
  * the shadow of `builtin_tls+0xeb8` and of the image top (`AFjm.v:328`, `AFjy.v:831,1565`, `AFk1.v:695`).

## 3. DONOR-STALE rows

### Final: none

### The 7 rows stage 1 flags, each decided

Stage 1 flags these rows by the rule "hex value in a `Definition _ : Z :=`, unmoved from the donor file, not a
target symbol / section value". None is a donor image value; the rule "donor image value, unmoved" has 0 rows.

| file:line | value | what it is in fuzz_grant.asan | in fuzz_uci.asan | decision |
|---|---|---|---|---|
| `lib/A/AB16.v:261` `tfib_sealed_src` | `0x117fe` | the string `"<sealed>"` (no symbol) | the same string at the same address | SHARED (bytes) |
| `lib/A/AB1w.v:569` `tfib_D_str_sealed` | `0x117fe` | the same | the same | SHARED (bytes) |
| `lib/A/AB1w.v:610` `tfib_at_x_sealed` | `0x117fe` | the same | the same | SHARED (bytes) |
| `lib/A/AE2k.v:37` `FF_mask` | `0x103a0` | 8 bytes `ff ff 0f 00 00 ff ff af` = `FF_mask_val 0xafffff00000fffff` (`$d`) | the same 8 bytes | SHARED (bytes) |
| `lib/A/AE3a.v:17` `tfib_D_const_HIGHS_0x8080808080808080` | `0x10350` | `0x8080808080808080` (`$d`) | the same | SHARED (bytes) |
| `lib/A/AE3a.v:18` `tfib_D_const_ONES_0x0101010101010100` | `0x10368` | `0x0101010101010100` (`$d`) | the same | SHARED (bytes) |
| `lib/Reusable/YG0f.v:34` `kNodesBlockSize` | `0x100000` | not an address: the 1 MiB block size of the StackDepot node map, next to `kStoreBlockSize 0x800000` and `kFakeStackSize 0xb09000` (port_core's `nonA.tsv` row `YG0f.v 33`) | - | OTHER (constant) |

These six addresses are SHARED for the same reason as decode's `0x102e8` / `0x10308`. The two images share the
first 8 KiB of `.rodata` byte for byte: the bytes are identical from `0x102e0` up to `0x12368`, where the first
difference is.

### Comment numerals that name a donor value (by design; not stale)

Eight comment numerals are fuzz_grant image values and not fuzz_uci values: `AB1w.v:5 0x3cda4`,
`AFem.v:4 0x186a18`, `AFfg.v:4 0xa5d40`, `AFfu.v:5 0xa5d40`, `AFg1.v:4 0xa5d40`, `AFj1.v:4 0x176a08`,
`AFjf.v:4 0x176a08` and `AFjr.v:5 660696`. Each is in the historical cgif -> fuzz_grant note, kept verbatim from
the donor. The file's last note says that the file was copied from fuzz_grant's lib and its addresses were moved to
fuzz_uci. The code values that those notes describe are fuzz_uci's:
* `IM8` witness `81984` = `0xa0200/8`;
* `BS3` quotient `79688` = `(637336+168)/8`, where `637336` is uci's `__asan::instance 0x9b998`;
* `TFIB_DEPOT/4` `394166`;
* the store bound `0x170ec8` and length `0x160ec8`;
* the jump-table entries `0x64ec8` at `0x21240` and `0x44f0c` at `0x20a1c`;
* the GOT bound `0x97cb0`;
* the decimal code address `220300` = `0x35c8c`;
* the cells `0x9bd0a` / `638218` and `0x9bc41/0x9bc42` / `638017/638018`;
* `637384`.

All of these are rows that moved and were twin-checked in stage 2.

## 4. Observations next to the value check (no numeral is wrong)

1. **decval's `role()` reads a Coq bullet as a comment.** A line that starts with `*` is classed as a comment. 14
   rows in this tree are bullets (code): `AD1d.v:208,210`, `AD1e.v:224,228,233,234,235`, `AD1f.v:198`,
   `AFj1.v:1092`, `AFjf.v:1086`, `AFjz.v:1079`. Stage 2 decides them as code: 3 moved to their uci twins
   (`0x5e4000`, `0x5c1650` x2), 7 are `0x10000` (SHARED), and 4 are constants. In a future run, a donor value on a
   bullet line would be hidden in "comment numeral". decode's run has the same blind spot.
2. **port_core's `--rename GrantSyms=UciSyms` changed the historical notes.** It rewrote the cgif -> fuzz_grant
   note in 159 files, which now reads "names TfibSyms -> UciSyms ... moved to libreac/fuzz_grant's ASan build". The
   donor note reads "TfibSyms -> GrantSyms". This changes no numeral.
3. **decode's DECIMAL-VALUES.md quotes fuzz_grant's `builtin_tls`/tp as `0x5d7a48`/`0x5d7b10`.** The `.symtab` of
   `fuzz_grant.asan`'s unstripped twin, `provenance/core-reloc/A/fuzz_grant.asan.syms.txt:1914` and the donor text
   (`TFIB_TP 0x5d7ad0`, `SLit 6126288`) all give `0x5d7a08`/`0x5d7ad0`. Both pairs were swept, with 0 hits.

## 5. Exact commands

```sh
# inputs (read-only)
git -C <checkout> rev-parse HEAD     # 276afc86670b4ccfb478d7c75992f412bd227d74
git -C <checkout> status --short     # (empty)
sha256sum "$P/bin/fuzz_uci/fuzz_uci.asan"         # 6ea017c24525e694...
sha256sum "$PG/bin/fuzz_grant/fuzz_grant.asan"    # c2c7559b29bdf39c...
export P PG CORE=<checkout>/proofs/reac-repacer/fuzz_uci DON=<the normalised grant lib, run.sh's DON>

cd <work dir>
# control FIRST, on a scratch copy
mkdir ctrlA && cp -r "$CORE/lib" ctrlA/lib
ln -s "$CORE/provenance" ctrlA/provenance
#   ctrlA/lib/A/AB1w.v:606  tfib_at_x_memset : Z := 0x90754.  ->  0x95e30.   (fuzz_grant.asan's memset)
python3 decval.py --core ctrlA --out ctrlA.tsv --review ctrlA.review.tsv > ctrlA.log 2>&1   # DONOR-STALE 8
# the real run
python3 decval.py --out A.tsv --review A.review.tsv > A.log 2>&1                            # DONOR-STALE 7
diff <(cut -f1-7 A.tsv) <(cut -f1-7 ctrlA.tsv)                                              # 1 row: AB1w.v:606
# stage 2: image evidence for every row stage 1 leaves to a look by hand
python3 decval_extra.py A.tsv --out A.extra.tsv > A.extra.log 2>&1                          # 0 unverified, 0 no-twin
```

Files kept beside this one in the work dir `decval/` (this directory holds the two scripts):
* `decval.py` (sha256 `d631969e632d` as run; `8e017bedf8ee` here, where only its inputs moved from fixed paths to
  the environment variables P / PG / CORE / DON) and `decval_extra.py` (sha256 `ea53687ce107`);
* `A.tsv` and `ctrlA.tsv`: one row per numeral, with file, line, token, value, class, reason, unmoved, donor token
  and source;
* `A.review.tsv`: stage 1's by-hand lists;
* `A.extra.tsv`: the final class and evidence per row;
* `A.log`, `ctrlA.log`, `A.extra.log`;
* `ctrlA/`: the scratch copy holding the planted value.

**fuzz_uci image-A core: 0 DONOR-STALE in 8519 numerals of 569 relocated files. Final classes: TARGET 6791 /
SHARED 708 / OTHER 1020.** Control: the one planted fuzz_grant `memset` is the only row that moves, to
DONOR-STALE.
