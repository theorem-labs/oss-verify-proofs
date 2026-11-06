# Symbol+offset sweep — libreac/fuzz_identity, A core

The limit this answers, stated by a lane at 19:51Z and recorded here in full: **a by-address move onto an unrelated
cell reads SAME** to every relocation tool and value gate. The check: derive each relocated numeral as
*target symbol + offset* from the *donor's symbol + offset*, and refuse when it lands in `.got`/`.got.plt` or
on a different symbol.

## Method

Reused a lane's gate rather than writing a third one: `symoff-check.py` from
`the frame B-core branch`, `proofs/libdiginet/fuzz_frame/provenance/evidence/core-B/b-core/gates/`.
One change, kept minimal: the file selection was hard-wired to `B/*.v`, so `SIDE` now names the side and the
`YImgTop.v` skip is by suffix. Nothing else was touched.

```
DONOR_ELF   <the relocation lane's workspace>/bin/cgif/cgif_file_fuzzer/cgif_file_fuzzer.asan
DONOR_TWIN  <redacted: see the internal record>bin/cgif-twins/cgif_file_fuzzer/cgif_file_fuzzer.asan   (sha256 488e39500746)
FRAME_ELF   <redacted: see the internal record>bin/pau-libreac-v190/libreac/bin/fuzz_identity/fuzz_identity.asan (c954b804786c = builds.asan)
FRAME_TWIN  <redacted: see the internal record>bin/libreac-v190/x/unstripped/fuzz_identity/fuzz_identity.asan
STAGE       the d9e0 --dry work dir's stage/ (the donor text of the relocated files)
CORE        the committed lib/ of this series branch
OUT         <this lane's workspace>/t5/symoff-identity-A.tsv
```

The donor image is stripped, so `DONOR_TWIN` must be cgif's unstripped twin; passing the stripped image gives
`AttributeError: 'NoneType' object has no attribute 'iter_symbols'`.

## Result

```
checked 8934 numerals
  EQUAL (target symbol + offset, as the rule requires)            7266
  GOT-EQUAL                                                          (in the EQUAL set above)
  DIFFER                                                          1159
  UNPAIRED-LINE                                                   2266   (1653 of them in slot files)
  NO-COUNTERPART 144 | AMBIGUOUS 90 | C_OTHER_SYMBOL 546 | GOT-* 42 | EMITTED-* 15
```

**The 1159 DIFFER rows split cleanly, and the large part is not a move at all:**

| | count | what it is |
| --- | --- | --- |
| committed value **equals the donor's** | **970** | the port kept the numeral; these are instruction words, not addresses — e.g. `0x0035f693`, `0x00050693` (RISC-V encodings) that happen to fall inside a symbol's address range |
| committed value **differs** | **189** | genuinely moved, but not to the donor symbol's counterpart |

Of the 189, **69 are in `A/AB01.v`** and more in `A/AB13.v`, `A/AD2j.v`, `A/AF0m.v` — all **generated slot**
files, whose values come from the start-up collector, not from symbol+offset relocation (see
`port_core-rerun-A.md`). The remainder, about a hundred rows in `A/ACej.v`, `A/AFhn.v`,
`A/AFkm.v`, `A/AFkz.v`, `A/AD1f.v`, `A/AD1g.v`, are the set still to classify.

## What is NOT claimed

The lane's second stage, `symoff-verdict.py`, assigns each non-EQUAL row `KEPT` / `ROLE <name>` / `CROSS` /
`OPEN`. It requires a `CROSS` table — the alreloc cross-check of the same core — which **identity's A core
does not have**, so it cannot be run here and no row is marked OPEN or explained on its authority.

So this record states what is measured: **7266 numerals satisfy the rule outright, 970 more are kept
verbatim and are not address moves, and 189 are moved otherwise, most of them in generated slot files.** It
does not claim "0 unexplained" — that sentence needs the cross-check table or a role check, and neither has
been run here.

Two blunt readings were tried first and are recorded so nobody repeats them: counting numerals that land in
`.got` gives **307**, and counting those whose line does not mention GOT gives **519**. Both are artefacts —
files such as `A/AFhy.v` and `A/AFii.v` model GOT entries deliberately, and `lit8 <addr> <word>` rows state
what the image holds at an address. Neither number is a finding.

## The hand role pass (a lane, 20:30Z: by hand, no alreloc table)

Scope as instructed: every moved, non-kept row in a file that is **not** a generated slot. The slot set is
the 11 files carrying a `regenerate from the start-up collector` row in the run's own `required.tsv` —
`AB01`, `AB03`, `AB05`, `AB12`, `AB1h`, `AB1k`, `AB1m`, `AB1v`, `AD1k`, `AD2i`, `AD2j` — read from the file,
not guessed from names. (An earlier pass guessed the set and classified 30 rows under the wrong heading.)

| verdict | rows | how it was measured |
| --- | --- | --- |
| `SYM+OFF`, same symbol and offset | 46 | the donor's containing symbol exists in the target twin at the same offset |
| `ROLE hull_len_page` | 36 | `(hull_hi − hull_lo)` page-rounded: donor `0x5eb000`, target `0x5ea000` |
| `ROLE hi/8_r256` | 21 | `hull_hi / 8` rounded to `0x100`: `0xbf600` → `0xbf400` (shadow length) |
| `ROLE seg1_len_page` | 8 | the executable PT_LOAD's length, page-rounded: `0x6d000` → `0x6a000` |
| `ROLE hull_len/8_r256` | 4 | `0xbd600` → `0xbd400` |
| `ROLE .preinit_array_hi` | 1 | the section bound |
| same symbol, different offset | 25 | code inside a function whose layout differs between the two units |
| start-up layer (ruled 20:34Z) | 19 | `ACej`, `AF0m`, `AE3i`, `AE37` — see below |
| memory-content cells, verified on the pin | 4 | `AFih`, `AFii`, `AFk1`, `AFk2` — see below |

**The 19 start-up rows.** Each file states its own source in its header, so this is from the record, not the
name: `ACej.v` *"generated for libreac/fuzz_identity image A by the start-up collector tools/startup/…"*; `AF0m.v`
*"regenerated for libreac/fuzz_identity image A from this image and the 50 c…"*; `AE3i.v` *"generated by
gen_ae3i.py for libreac/fuzz_identity image A"*; `AE37.v` *"the walk's globals array is fuzz_identity.asan's
50 descriptors at 0xa0c60"*. They are written from identity's own execution, so the donor-paired rule does
not apply to them.

**The 4 remaining rows are memory-content assertions, and the image settles them.** They read
`lit4 <addr> <word>` / `val_mem … <addr> <n> <word>` — *this image holds this word at this address* — so the
right test is the pin itself, not the symbol rule:

```
AFih.v:68   lit4 0x20d08 0x46044   pin [0x20d08:4] = 0x46044   MATCH
AFk2.v:597  val_mem … 0x20d08 4    pin [0x20d08:4] = 0x46044   MATCH
AFii.v:24   lit4 0x21ce4 0x686e4   pin [0x21ce4:4] = 0x686e4   MATCH
AFk1.v:659  val_mem … 0x21d48 2    pin [0x21d48:2] = 0xff04    MATCH
```

The donor's same cells hold `0x53190` and `0x6574726f` — different data, as they should be. The sweep flagged
these only because it resolved the stored *word* as if it were an address and found it inside a different
function; that is the sweep's limit on content cells, not a move onto an unrelated cell. An instruction-class
check would have been weaker still: on `AFii`/`AFk1` the opcode classes differ (`0x3` vs `0x13`) because the
words are jump-table data, not instructions.

**Result: 0 VALUE rows, 0 OPEN rows, nothing to commit for the A core.**
