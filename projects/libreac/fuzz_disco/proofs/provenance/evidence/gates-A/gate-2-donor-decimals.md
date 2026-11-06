# Gate 2 — by-value donor-stale numeral check, image A (fuzz_disco.asan)

Kind: measurement; proves no function. A DECIMAL literal v (65536 ≤ v < 0x600000, outside comments, not part of an
identifier, not after `0x`) is a HIT when cgif's image has a symbol N covering v at offset o (v = N + o) and
fuzz_disco.asan does not place N + o at v. A hit is a donor (cgif) address left unmoved; a defect.

## Script of record (copied; new version with arguments)

`donordec/donor_decimals.py` sha256 `a7ec855ffb43c421a5cab3c96b2ca4c7be781ed2ad79fceac663ef12b3dbc1aa` and
`donordec/funnel.py` sha256 `9cc314dc24afe2dbc3a454d3932fbde3970728b1bf3df6f6cb75f7b7aa978284`. The earlier version
held host constants (a git dir, cgif's image path, the output root); this version takes every path as an argument
(`--git --kit --donors-from --cache --cgif-image BUILD=ELF --target-image BUILD=ELF:SYMS --tree --target --subdirs
--plant --out`; funnel adds `--cgif-lib REF:PATH`). cgif's symbols are recovered by the frozen `port_addr_check` kit
sha256 `5033540ba83bdad174e9b1aa3cc21ffeda3469736e4dd0390f58db9008890546` (with its `scan_literals.py`
`ae01d69b2ee4…` and `cfgpair.py` `bc9795900868…`), named by `--kit`.

### Same rows as the earlier version (cmp, byte for byte)

The earlier version (sha256 `e7d879e2ed9c…`, funnel `940cb11df71e…`) and this one give the same rows on the same
inputs, measured with a fresh recovery cache:

| input | rows | old = new |
|---|---|---|
| cgif against its own released lib (negative control) | 0 | sha256 `2a34bb11aff4…` |
| cgif's A/AE23.v:471 planted as a disco lib/A file (positive control) | 1 | sha256 `8e28535917180f…` |
| lib/A at the base | 2726 | sha256 `1c39bf917977…` |
| funnel over the lib/A scan | — | `21fddb48932f…` (old = new) |

## Controls

- **Negative** (`donordec/control-neg`): target cgif over its released lib → `# rows 0`.
- **Positive** (`donordec/control-pos`): cgif's `A/AE23.v:471` (`Z_to_bv 64 6264480`, cgif's stdout buffer `buf+0x8`)
  scanned as a disco lib/A file → `# rows 1` (a hit: cgif `buf+0x8`; disco's `buf+0x8` is 0x5fc760).

## Verdict (run.sh `donordec/scan-A` + `donordec/funnel-A`)

**0 defects.** The scan of lib/A at the base is 2726 rows; `funnel.py` sorts every row into an explained class and
prints the rest:

| class | rows | why it is not a donor address left unmoved |
|---|---|---|
| NOT-IN-DONOR | 1811 | the value is no literal anywhere in cgif's released lib: disco's own numeral inside a cgif object by chance |
| SIZE | 584 | a power of two (±64) or a multiple of 1000 / 1024: a shared size or geometry constant |
| ODD-IN-CODE | 281 | an odd value inside cgif code, so no instruction address (rv64g is 4-byte aligned) |
| LABEL | 19 | an argument of mcheck / FCheck / fail / spin / ISpin: an opaque check-site name (port_addr_check 5033540ba83b:82-83) |
| INSN-IMM | 1 | the operand of a decoded instruction (a pc-relative jump offset) |
| DISCO-POINTER | 1 | a value in a start-up state at a disco object (an asan_globals descriptor) |
| UNEXPLAINED | 29 | the 5 values below, by hand |

The 29 UNEXPLAINED rows hold 5 distinct values, all disco-own or sizes:

- **1446400** (0x161200), 22 rows in AB01 / AD1d / AD1f: the length of a shadow zero-fill (`kn_zero ch (…) … 1446400`).
  It coincides with cgif's `useCounts+0x29340`; disco has no object there.
- **678584 / 678592** (0xa5ab8 / 0xa5ac0), AB01 / AB03: an a_off inside disco's allocator `instance`, in collected
  start-up states; coincides with cgif's `ScopedInErrorReport::current_error_`.
- **2101549** (0x20112d), AB01 / AB03: a collected value inside disco's `theDepot`.
- **262728** (0x40248), AFfg: the length operand of `do_stretch`, next to hex pcs; coincides with cgif's
  `__asan_after_dynamic_init`.

These 5 values are the per-value table `donordec/unexplained-safe.tsv`; `donordec/triage_unexplained.py` checks that
every value the funnel leaves UNEXPLAINED is one of them (run.sh `donordec/unexplained`: `UNEXPLAINED 29 rows, 5 values;
all recorded disco-own: True`, exit 0). An unlisted UNEXPLAINED value would be a candidate donor-stale decimal, a
defect to report. Every row's enclosing declaration is in the scan's `decl` column. No real defect; nothing to fix.

## Planted control (must fire)

A copy of `lib/A/AE23.v` outside the branch with its stdout-buffer decimal `6276960` (disco `buf+0x8`) set to cgif's
`6264480`. Re-scan (`donordec/plant`): a hit row at `AE23.v:473 6264480` (cgif `buf+0x8`, which disco does not place at
6264480). A scan with 0 rows would be void. Recorded `FIRED` in run.sh.
