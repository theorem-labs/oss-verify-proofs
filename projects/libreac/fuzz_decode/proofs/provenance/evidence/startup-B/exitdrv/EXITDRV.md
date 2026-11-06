# EXITDRV: libreac/fuzz_decode exit certificate (AE23 / AD1y + B twins), relocated from cgif_file_fuzzer

OWNER_WORKER / LANE_1, 2026-10-29. Read-only on every git tree; nothing built, committed or pushed. rule 24:
no function proved — only numerals moved and module paths renamed. Owner of the decode files: OWNER_WORKER; porter:
PORTER_WORKER. Donor: `proofs/cgif/cgif_file_fuzzer` at `origin/ossv/recipes c8557374ad2e` (hub `HUB`).

## 0. Deliverables (all under WORKDIR/)

| file | from (cgif) | build | sha256 |
|---|---|---|---|
| `exitdrv.py` | — | — | ac06e6f2e25f03c343a5456c1b8e9ae57ff6f82fbac2c98d80ba200739ae3db7 |
| `AE23.v` | lib/A/AE23.v | decode.asan | a448ec42ab433eaf69088feedc37d1067eccd24a01c797ab0f4b30d52b05efc9 |
| `YE23.v` | lib/YE23.v | decode.asan-ubsan | 66092be4b040bddccbd60ffb1327cb631db5f6e1e5b046d2b28008c2f97032b6 |
| `AD1y.v` | lib/A/AD1y.v | decode.asan | 4cbe73cb871f616448bd908b3c718073c67e48d8acc468e6107d0980a404a5a4 |
| `YD1y.v` | lib/YD1y.v | decode.asan-ubsan | 93fd1d70a816cd79097696e18f21b847e39989a320c0baa9c206de383ae44b30 |

Revision 2 (LANE_2, 2026-10-29 10:4xZ), from the first build (log WORKDIR_LOG):
- `TfibSyms` -> `GrantSyms` (AF0m.v's record; owner PORTER_WORKER 10:02Z), was `DecodeSyms`.
- The 7 DECIMAL data literals of the donor AE23/YE23 are relocated by the same data rule (they were left as cgif
  addresses: AE23:488 failed on `Z_to_bv 64 6264480` = cgif STDOUT_BUFA); table rows `DEC` in §5.
- DRV_IVS keeps the donor's 4 windows (no split around the ODR bytes); §4 says why. AD1y:63 failed because the
  driver's main-entry region R_A5a [0x5d3410, 0x5d3cb4) writes over the ODR bytes and was in no split window.

Regenerate: `python3 WORKDIR/exitdrv.py` (prints the numeral table + CONTROLS, re-reads the donor from
git, rewrites the four `.v`). AE23.v is the asan file; its asan-ubsan twin in cgif is **lib/YE23.v** (not lib/A).
AD1y's twin is **lib/YD1y.v**. Both twins are in cgif `lib/` → decode `lib/Reusable/` (naming rule below).

## 1. Inputs and tools (what each number is read from)

- **Pins (image BYTES)** — the LANE_3 ORIGINALs, re-hashed here:
  - A `bin/fuzz_decode/fuzz_decode.asan`  sha256 `5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036`
  - B `bin/fuzz_decode/fuzz_decode.asan-ubsan` sha256 `5d05689fd5b196976890b91e68c113953d385775b9d811ef98c712b2cac7d4a9`
  Symlinked under `WORKDIR/`. **Every cell value and every ODR / shadow / segment fact is read
  from these pins**, never from the unstripped file.
- **Symbols** — the unstripped twins `WORKDIR/fuzz_decode.asan{,-ubsan}` `.symtab` only
  (sha256 `4cb0a852…` / `6744989b…`); used to NAME a decode address, never to read a value.
- **Code map** — `WORKDIR/binmatch.cgif.asan.json` (side A) and `…asan-ubsan.json` (side B): the
  identical cgif functions. A code pc moves by its function's delta (`decode = cgif − delta`). Side A moves AE23/AD1y
  (cgif-asan) addresses; side B moves YE23/YD1y (cgif-asan-ubsan) addresses, each with its own binmatch.
- **Data map (side A)** — `WORKDIR/map.cgif2decode.asan.json` (MAP_KIT `MAP_TOOL`, cgif-asan→decode-asan): a data
  address moves to `new_lo + (cgif − old_lo)`. The decode-asan address is then NAMED in the unstripped twin
  (enclosing `STT_OBJECT`, the `.fini_array`/`.got` section, or a `.got` slot by the pointer it holds).
- **Data map (side B)** — no cgif-asan-ubsan MAP_TOOL is needed: AE23 and YE23 (and AD1y/YD1y) are the SAME
  certificate, numeral position for numeral position (`exitdrv.py` asserts **0 pairing mismatches**, 238 tokens each
  for AE23/YE23, 34 for AD1y/YD1y). So each cell's decode-asan-ubsan address is the SAME object / section / `.got`
  slot in the asan-ubsan twin that side A found in the asan twin.
- **Shadow** — `shadow(a) = (a >> 3) + 0x7fff8000` of the decode global (or asan_globals section) the cgif shadow
  byte covers; globals read from each pin's `asan_globals` descriptors.
- **Segment bounds** — page-rounded PT_LOAD hull `[base & ~0xfff, ceil(base+memsz)]` of each pin.

### CONTROLS (same tool on cgif's own files reproduces cgif's values)
- Page-rounding cgif-asan's PT_LOADs gives `(0x10000,0x30000) (0x30000,0x9d000) (0x9d000,0x9f000) (0x9f000,0x5fb000)`
  — exactly cgif AD1y's `in_img` literals 0x10000 / 0x30000 / 0x9d000 / 0x9f000 / 0x5fb000. **PASS.**
- `shadow(0x20e00) = 0x7fffc1c0` = cgif AE23 XW2's first shadow bound; `shadow(0xa2870) = 0x8000c50e` = cgif AE23's
  metadata-shadow bound. **PASS** (same formula reproduces the donor's own numbers).
- binmatch reproduces the donor control: `pinned_bytes == twin: True`, 1243/1262 identical both sides; every exit
  function used (exit, __funcs_on_exit, libc_exit_fini, __cxa_finalize, asan.module_dtor, __do_fini, …) is
  `identical` (per `binmatch.cgif.stats.*`).
- Decode asan_globals ODR indicators read from the pins: A `0x5d3440/0x5d3441/0x5d3442`, B `0x5d39c0/0x5d39c1/0x5d39c2`
  (cgif's are all −1). This is exactly the donor-breaking fact (WORKDIR_NOTE_1 F1).

Word-boundary anchors were used for every symbol/module rewrite (`\bTfibSyms\b`, `\bTfibB\b`, exact module prefixes).

## 2. The ODR exit write (confirmed by disassembly of the PINS, capstone 5.0.7 RV64GC)

`UnregisterGlobal` is inlined in `__asan_unregister_globals` (A 0x3eeb4, B 0x3ef00). Per descriptor:
`ld a0,0x38(s4)` loads the ODR indicator; `addi a1,a0,1`; **`bgeu a1,s2,…`** (s2 = 2) branches to the write only when
`odr ∉ {0, −1}`; the write is **`sb zero, 0(a0)`** — 0 into the ODR byte.

| side | branch pc | **ODR write instruction pc** | instruction |
|---|---|---|---|
| A (asan) | 0x3f060 `bgeu a1,s2,0xc4` | **0x3f124** | `sb zero, 0(a0)` |
| B (asan-ubsan) | 0x3f0ac `bgeu a1,s2,0xc4` | **0x3f170** | `sb zero, 0(a0)` |

Exit path: `module_dtor` (X2_PC, A 0x812ac / B 0x815cc = `fini_array[0]`, read from the pin) →
`__asan_unregister_elf_globals` → `__asan_unregister_globals`; the `bgeu` is taken once per global, so the symbolic
x2 run hits 0x3f124 (A) / 0x3f170 (B) **three times**. In cgif the indicators are −1 so `a1 = 0 < 2` and the branch
is never taken — cgif's exit write set has no ODR bytes. This is why AE23's XW2 must gain them.

## 3. Exit write set (AE23 / YE23)

`XW1 = False` (unchanged). `XW3`: the single `___dso…`-adjacent flag — A `a = 0x9d750`, B `a = 0x9dcd0`.
`XW2` (ADD the 3 ODR bytes as the last disjunct):

- **A**: `(0x9d700 ≤ a < 0x9d708)` `___asan_globals_registered` ∨ `(0x9e670 ≤ a < 0x9e678)` `__asan::mu_for_globals`
  ∨ `(0x7fffc1a8,0x7fffc1ac) (0x7fffc1ac,0x7fffc1b0) (0x7fffc1b0,0x7fffc1b4)` shadow of the 3 globals
  ∨ `(0x8000bac2 ≤ a < 0x8000bada)` shadow of asan_globals (24 B) ∨ **`(0x5d3440 ≤ a < 0x5d3443)` the 3 ODR bytes**.
- **B**: `(0x9dc80,0x9dc88)` ∨ `(0x9ebf0,0x9ebf8)` ∨ `(0x7fffc1ac,0x7fffc1b0) (0x7fffc1b0,0x7fffc1b4) (0x7fffc1b4,0x7fffc1b8)`
  ∨ `(0x8000bb76,0x8000bb8e)` ∨ **`(0x5d39c0 ≤ a < 0x5d39c3)`**.

Other exit anchors (A | B): `A_exit` 0x88858 | 0x88e00 (`exit`); `X1_PC` 0x6f624 | 0x6f670 (`__sanitizer_cov_dump`),
`X1_RA` 0x886f4 | 0x88c9c (`__funcs_on_exit`+128); `X2_PC` 0x812ac | 0x815cc (`asan.module_dtor` = `fini_array[0]`,
**not** the MAP_TOOL value, cert F3); `X3_PC` 0x300c4 | 0x30110 (`__do_fini`); `X23_RA` 0x8883c | 0x88de4
(`libc_exit_fini`+48); `TFIB_TPX` 0x5d3d58 | 0x5d42d8 (`builtin_tls`+200); `F_STDIN` 0x9d4f0 | 0x9da98
(`__stdin_FILE`). `X3PRE`: A `0x98d10=0x8873c` (`.got`→`__cxa_finalize`), `0x98d18=0`; B `0x992b8=0x88ce4`, `0x992c0=0`.
`ex_consts`/`ex_consts1`/`ex_regions` cells are all relocated the same way (full table below).

## 4. Driver windows (AD1y / YD1y) — the donor's 4 windows, relocated, NOT split

Revision 1 split the 3rd window around the ODR bytes on the assumption that AF0m would make them runtime-owned. It
does not: `Tfib_owned_static` (AF0m run 4) lists no range over 0x5d3440..0x5d3442, and gen_ad2's AD2j carries the 3
bytes as `CVal 1` chunks of the driver region `R_A5a` [0x5d3410, 0x5d3cb4), whose write window is the whole region.
`smem_main_win_ok` (every write window of `smem_main` lies in DRV_IVS or the stack window) therefore needs them inside
DRV_IVS; with the split, `R_A5a` lay in no window (the only failing region of `smem_main`, computed from AD2i/AD2j).
Unsplit, no owned entry meets DRV_IVS (DRVW_not_owned holds: WORKDIR/drvivs.py, 0 overlaps), and XW2 still lists the
ODR bytes (the exit's module_dtor writes them; XW2 is a write set, not a window).

| | window 1 | window 2 | window 3 | window 4 |
|---|---|---|---|---|
| cgif.asan | (0xa2530,0xa2870) | (0xa2948,0xa2990) | (0x5d8650,0x5d8f38) | (0x5f8fe0,0x5f9200) |
| **decode.asan** | (0x9d2c8,0x9d610) | (0x9d708,0x9d750) | (0x5d3410,0x5d3d00) | (0x5f3da8,0x5f3fc8) |
| **decode.asan-ubsan** | (0x9d870,0x9dbb0) | (0x9dc88,0x9dcd0) | (0x5d3990,0x5d4280) | (0x5f4328,0x5f4548) |

`exitdrv.py` asserts the 3 ODR bytes lie inside window 3 on both sides. Window endpoints are named: oft_arg0 ..
asan_globals; __do_init.__initialized .. __do_fini.__finalized; target_run.initialized .. builtin_tls+112;
finished_atexit .. exit.exit_lock.

Segment bounds (both builds share the page hull): `0x9d000→0x98000` (rw lo), `0x9f000→0x9a000` (seg2/seg3 split),
`0x5fb000→0x5f6000` (hull hi), `0x30000`/`0x10000` unchanged — the 4 Asan segments are
`(0x10000,0x30000)(0x30000,0x98000)(0x98000,0x9a000)(0x9a000,0x5f6000)`.

## 5. Full numeral table (cgif-asan | cgif-asan-ubsan | kind | decode.asan | decode.asan-ubsan | source)

AE23 / YE23:

```
0x130        0x130        CONST  0x130       0x130       image-independent (region size 0x5f9110-0x5f8fe0)
0x30398      0x303c8      CODE   0x300c4     0x30110     binmatch __do_fini
0x6fa50      0x6fa80      CODE   0x6f624     0x6f670     binmatch __sanitizer_cov_dump
0x80418      0x80448      CODE   0x7ffec     0x80038     binmatch oft_exit_guard
0x813d4      0x80cc0      CODE   0x812ac     0x815cc     binmatch asan.module_dtor (= fini_array[0])
0x8d4a0      0x8d714      CODE   0x886f4     0x88c9c     binmatch __funcs_on_exit+128
0x8d4e8      0x8d75c      CODE   0x8873c     0x88ce4     binmatch __cxa_finalize
0x8d5b0      0x8d824      CODE   0x88804     0x88dac     binmatch call
0x8d5e8      0x8d85c      CODE   0x8883c     0x88de4     binmatch libc_exit_fini+48
0x8d604      0x8d878      CODE   0x88858     0x88e00     binmatch exit
0x9da20      0x9dc90      DATA   0x987c8     0x98d70     .fini_array[0]
0x9da28      0x9dc98      DATA   0x987d0     0x98d78     .fini_array[1] (__fini)
0x9da30      0x9dca0      DATA   0x987d8     0x98d80     _ZL7preinit
0x9df68      0x9e1d8      GOT    0x98d10     0x992b8     .got slot -> __cxa_finalize
0x9df70      0x9e1e0      GOT    0x98d18     0x992c0     .got slot -> __dso_handle (0)
0x9df78      0x9e1e8      GOT    0x98d20     0x992c8     .got cluster end (+0x10)
0x9ec68      0x9eed8      GOT    0x99a10     0x99fb8     .got slot -> preinit
0x9ec70      0x9eee0      GOT    0x99a18     0x99fc0     .got slot -> .fini_array
0x9ec78      0x9eee8      GOT    0x99a20     0x99fc8     .got cluster end (+0x10)
0xa2660      0xa28d0      DATA   0x9d3f8     0x9d9a0     __stderr_used
0xa2668      0xa28d8      DATA   0x9d400     0x9d9a8     __stderr_used+8 (= __stdout_FILE)
0xa2750      0xa29c0      DATA   0x9d4e8     0x9da90     __stdout_used
0xa2758      0xa29c8      DATA   0x9d4f0     0x9da98     __stdin_FILE (= F_STDIN)
0xa2840      0xa2ab0      DATA   0x9d5d8     0x9db80     __stdin_used
0xa2848      0xa2ab8      DATA   0x9d5e0     0x9db88     __stdin_used+8
0xa2940      0xa2bc0      DATA   0x9d700     0x9dc80     ___asan_globals_registered
0xa2948      0xa2bc8      DATA   0x9d708     0x9dc88     __do_init.__initialized (= reg+8)
0xa2990      0xa2c10      DATA   0x9d750     0x9dcd0     __do_fini.__finalized (XW3)
0xa38b0      0xa3b30      DATA   0x9e670     0x9ebf0     __asan::mu_for_globals
0xa38b8      0xa3b38      DATA   0x9e678     0x9ebf8     __asan::mu_for_globals+8
0x5d8654     0x5d88d4     DATA   0x5d3414    0x5d3994    oft_in_callback
0x5d8655     0x5d88d5     DATA   0x5d3415    0x5d3995    oft_in_callback+1 (cell end)
0x5d8f90     0x5d9210     DATA   0x5d3d58    0x5d42d8    builtin_tls+200 (TFIB_TPX)
0x5f8fe0     0x5f9260     DATA   0x5f3da8    0x5f4328    finished_atexit
0x5f8fe4     0x5f9264     DATA   0x5f3dac    0x5f432c    lock
0x5f8fe8     0x5f9268     DATA   0x5f3db0    0x5f4330    slot (atexit count = 2)
0x5f8ff0     0x5f9270     DATA   0x5f3db8    0x5f4338    head
0x5f8ff8     0x5f9278     DATA   0x5f3dc0    0x5f4340    builtin (__funcs_on_exit table)
0x5f9000     0x5f9280     DATA   0x5f3dc8    0x5f4348    builtin+8
0x5f9008     0x5f9288     DATA   0x5f3dd0    0x5f4350    builtin+16
0x5f9100     0x5f9380     DATA   0x5f3ec8    0x5f4448    builtin+264
0x5f9108     0x5f9388     DATA   0x5f3ed0    0x5f4450    builtin+272
0x5f9110     0x5f9390     DATA   0x5f3ed8    0x5f4458    builtin+280 (region end)
0x5f9200     0x5f9480     DATA   0x5f3fc8    0x5f4548    exit.exit_lock
0x5f9204     0x5f9484     DATA   0x5f3fcc    0x5f454c    exit.exit_lock+4
0x5f9223     0x5f94a3     DATA   0x5f3feb    0x5f456b    __libc+3
0x5f9224     0x5f94a4     DATA   0x5f3fec    0x5f456c    __libc+4
0x5f9680     0x5f9900     DATA   0x5f4448    0x5f49c8    ofl_lock
0x5f9688     0x5f9908     DATA   0x5f4450    0x5f49d0    ofl_head
0x5f9690     0x5f9910     DATA   0x5f4458    0x5f49d8    buf (region end)
0x7fffc1c0   0x7fffc1b8   SHADOW 0x7fffc1a8  0x7fffc1ac  shadow(global 0 beg)
0x7fffc1c4   0x7fffc1bc   SHADOW 0x7fffc1ac  0x7fffc1b0  shadow(global 0 slot end)
0x7fffc1cc   0x7fffc1c4   SHADOW 0x7fffc1ac  0x7fffc1b0  shadow(global 1 beg)
0x7fffc1d0   0x7fffc1c8   SHADOW 0x7fffc1b0  0x7fffc1b4  shadow(global 1 slot end)
0x7fffc1d4   0x7fffc1cc   SHADOW 0x7fffc1b0  0x7fffc1b4  shadow(global 2 beg)
0x7fffc1d8   0x7fffc1d0   SHADOW 0x7fffc1b4  0x7fffc1b8  shadow(global 2 slot end)
0x8000c50e   0x8000c55c   SHADOW 0x8000bac2  0x8000bb76  shadow(asan_globals beg)
0x8000c526   0x8000c574   SHADOW 0x8000bada  0x8000bb8e  shadow(asan_globals end, 24 B)
0xffffffff   0xffffffff   CONST  0xffffffff  0xffffffff  FILE sentinel (image-independent)
```

AD1y / YD1y (segment bounds + the 8 DRV_IVS endpoints; interval 3 then split around the ODR bytes):

```
0x10000      0x10000      SEG    0x10000     0x10000     Asan_segment_000 lo
0x30000      0x30000      SEG    0x30000     0x30000     seg0/seg1 split
0x9d000      0x9d000      SEG    0x98000     0x98000     rw lo (seg2)
0x9f000      0x9f000      SEG    0x9a000     0x9a000     seg2/seg3 split
0x5fb000     0x5fb000     SEG    0x5f6000    0x5f6000    hull hi
0xa2530      0xa27a0      DRV    0x9d2c8     0x9d870     oft_arg0        (win1 lo)
0xa2870      0xa2ae0      DRV    0x9d610     0x9dbb0     asan_globals    (win1 hi)
0xa2948      0xa2bc8      DRV    0x9d708     0x9dc88     __do_init.__initialized (win2 lo)
0xa2990      0xa2c10      DRV    0x9d750     0x9dcd0     __do_fini.__finalized   (win2 hi)
0x5d8650     0x5d88d0     DRV    0x5d3410    0x5d3990    target_run.initialized  (win3 lo)
0x5d8f38     0x5d91b8     DRV    0x5d3d00    0x5d4280    builtin_tls+112         (win3 hi)
0x5f8fe0     0x5f9260     DRV    0x5f3da8    0x5f4328    finished_atexit (win4 lo)
0x5f9200     0x5f9480     DRV    0x5f3fc8    0x5f4548    exit.exit_lock  (win4 hi)
```

## 6. Renames applied (WORKDIR_NOTE_2 §3)

`OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A` → `…libreac.fuzz_decode.lib.A`; any other `…cgif_file_fuzzer.lib`
→ `…libreac.fuzz_decode.lib.Reusable`; `OssFuzzTheorems.cgif.cgif_file_fuzzer.images` → `…libreac.fuzz_decode.images`
(leaf `Asan` / `AsanUbsan` kept); `TfibSyms` → `DecodeSyms`, `TfibB` → `DecodeB` (AE23/AD1y reference only the record
`TfibSyms`, never the instance). `tfibsegs`, `tfib_*`, field accessors `ts_owned`/`ts_errno`, `Tfib_owned_static`,
`asyms` are KEPT (they are the donor lib names carried into decode's ported `AB1v`/`AF0m`/`AD2l`).

## 7. Open items (what I could not fully settle here)

1. **Proof obligations of the enlarged XW2 / split DRV_IVS are NOT discharged here (rule 24).** AE23's `X2` is a
   `Hypothesis` (`xret_realizes_noar … X2_PC XW2 XTRUE`), proved in the `x2_ranges` file (AE3h/AE37, a different
   worker). With the 3 ODR bytes in XW2 that proof's symbolic x2 run must take the `sb zero,0(a0)` branch
   (0x3f124 A / 0x3f170 B) three times. The `GEO` (`unfold … XW2 …; lia`) tactics in AE23's body are robust to the
   extra disjunct; the `DRVW_*` tactics in AD1y are `repeat`-based and robust to 5 windows. Confirmation is the build.
2. **Record / field names depend on PORTER_WORKER's AF0m / AD2l.** I applied `TfibSyms → DecodeSyms` per WORKDIR_NOTE_2 §3
   but KEPT the field accessors `ts_owned` / `ts_errno`. If decode's `AF0m` names the record or its fields
   differently, a one-line `\b` rename in these files follows. Coordinate with PORTER_WORKER (porter of AF0m).
3. **`AF0m` must mark the 3 ODR bytes runtime-owned** (`Tfib_owned_static`/`Tfib_const`) now that AD1y removed them
   from the driver window (WORKDIR_NOTE_1 F2). That is AF0m's file, not mine.
4. Side-B data addresses come from the asan-ubsan twin's `.symtab` by the object identity side A established; the
   image-backed ones (GOT, `.fini_array`, `.data` pointers) were cross-checked by reading the side-B pin
   (e.g. decode.asan-ubsan `0x98d70 = 0x815cc` module_dtor, `0x992b8 = 0x88ce4` __cxa_finalize). The runtime-written
   driver cells (atexit tables, ODR) are not in the image on either side; their values are the relocated exit-state
   model, as in the donor.
