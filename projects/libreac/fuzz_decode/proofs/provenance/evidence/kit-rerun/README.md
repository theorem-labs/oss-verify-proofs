This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

# provenance/evidence/kit-rerun: the comparison-kit re-run records of decode's alloc-reloc relocation

The records that a shipped line or row cites for decode's relocated code addresses, made on cmpkit 4bbd3a74be89, with the
exposure scans and hand traces that cmpkit 86da41d3ef68 requires. They lie here because the released tree ships only
provenance/evidence/; they were moved from provenance/alloc-reloc/ with their relative layout kept. Provenance only: no
file here proves a function.

- `A/kit-rerun-4bbd3a74be89/`: the image-A re-run, a token copy of another lane's record; `COPY.md` and `copycheck.py`
  prove the copy against the original's commit. `KIT-RERUN.md` is the file the funcpair citation names (sha256
  `ddcfcfa5e36bd456e579dde539a601d3b8d2948638a6f8453a68c5f1d7fc65d7`).
- `B/`: the image-B re-run, its 86da41d3ef68 scans and its lui hand trace.
- `cmpkit-4bbd3a74be89/`: the script of the B record, the settled rows with their measurements, and their scans.
- `cmpkit-86da41d3ef68/`: the scan script and its summary (`SCANS.md`); `failopen/` holds the hand pass of the kit's
  KNOWN FAIL-OPEN shapes (a)-(h) on every compared function, with its planted controls (`FAILOPEN-SHAPES.md`).

## Files

What each file is, where no other text of this slice says it (the file list with the sha256 of every file is in
`provenance/evidence/MANIFEST.md`):

- `A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log`: cmpkit 86da41d3ef68 scans of the A record (luiscan, ambiscan,
  strictcmp3 control), made by cmpkit-86da41d3ef68/run.sh
- `A/kit-rerun-4bbd3a74be89/KIT-RERUN.md`: the image-A re-run record on cmpkit 4bbd3a74be89: 7 pairs, 417 numerals, 495
  cited numerals
- `A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md`: the A record author's hand trace of every lui through every ALU op
- `A/kit-rerun-4bbd3a74be89/SCANS-86da41d3ef68.md`: the A record author's exposure scans of cmpkit 86da41d3ef68
- every other file of `A/kit-rerun-4bbd3a74be89/` but `COPY.md`, `COPY.diff`, `copy-edits.tsv` and `copycheck.py` (which
  `COPY.md` describes): a file of the A record as the original ships it (role in KIT-RERUN.md, SCANS-86da41d3ef68.md or
  LUI-HANDTRACE.md)
- `B/LUI-HANDTRACE-B.md`: the hand trace of every lui of the B record and of the settled rows through every ALU op
- `B/fncmp.cmpkit-4bbd3a74be89.log`: the image-B re-run record on cmpkit 4bbd3a74be89: 8 functions on S : E and T : E,
  kit and settled verdicts against the old bytecmp tables
- `B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log`: cmpkit 86da41d3ef68 scans of the B record, made by
  cmpkit-86da41d3ef68/run.sh
- `B/luitrace-TryMemCpy-86da41d3ef68.out`: every word of TryMemCpy in T and in E, and their word compare
- `B/luitrace-compare-86da41d3ef68.out`: the B lui trace against the A record's trace, and S : E against T : E
- `B/luitrace-pair-SE-86da41d3ef68.out`: luitrace pair output, symtwin S : decode B twin E (cmpkit-86da41d3ef68/run.sh)
- `B/luitrace-pair-TE-86da41d3ef68.out`: luitrace pair output, donor twin T : decode B twin E
  (cmpkit-86da41d3ef68/run.sh)
- `FAILOPEN-SHAPES.md`: the KNOWN FAIL-OPEN shapes (a)-(h) of cmpkit 86da41d3ef68 on every compared function of the four
  records, both sides: one line per record (DIFFERENT 0), per-function tables, the A author's trace cited per shape, the
  planted controls
- `LUI-COMBINED.md`: the KNOWN FAIL-OPEN check: two lui values combined into one load / store / jump base, one line per
  record
- `cmpkit-4bbd3a74be89/kitsum.py`: per row: kit verdict, settled verdict, old verdicts
- `cmpkit-4bbd3a74be89/pinback.py`: rebuilds the stripped donor pin from the symtwin, for drvcmp twins
- `cmpkit-4bbd3a74be89/run.sh`: makes B/fncmp.cmpkit-4bbd3a74be89.log, settled.tsv and twins.log on cmpkit 4bbd3a74be89
- `cmpkit-4bbd3a74be89/settle.py`: the named measurement of each kit difference (bounded-byte-table,
  got-value-zero-test)
- `cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log`: cmpkit 86da41d3ef68 scans of the settled rows, made by
  cmpkit-86da41d3ef68/run.sh
- `cmpkit-4bbd3a74be89/settled.tsv`: the settled rows: Allocate +0xdc (S:E, T:E), PoisonShadow +0x48c (S:E), each with
  its measurement
- `cmpkit-4bbd3a74be89/twins.log`: donor pin rebuild and twin proofs of the 4bbd3a74be89 run
- `cmpkit-86da41d3ef68/SCANS.md`: what the 86da41d3ef68 scans found on the three records, and the open-limit checks
- `cmpkit-86da41d3ef68/failopen/controls.out`: the 28 planted controls (14 shapes x diff / same) with their objdump
  words, planted site and CHECK line: PASS 28 of 28
- `cmpkit-86da41d3ef68/failopen/failopen-CA.out`: failopen.py over the A record's 7 pairs, donor twin C : decode A twin:
  every site, both targets, verdict
- `cmpkit-86da41d3ef68/failopen/failopen-SE.out`: failopen.py over the B record's 8 functions, symtwin S : decode B twin
  E (the settled rows' S : E functions)
- `cmpkit-86da41d3ef68/failopen/failopen-TE.out`: failopen.py over the B record's 8 functions, donor twin T : decode B
  twin E (the settled rows' T : E function)
- `cmpkit-86da41d3ef68/failopen/failopen.py`: the hand pass: a MAY dataflow per function over GNU objdump listings;
  every load / store / jalr / AMO site, its shapes (a)-(h) and its target on both sides
- `cmpkit-86da41d3ef68/failopen/plant.py`: writes the planted control copies, one per shape and variant, and checks
  their results
- `cmpkit-86da41d3ef68/failopen/run.sh`: runs failopen.py and plant.py in the toolchain image and makes every
  failopen/*.out
- `cmpkit-86da41d3ef68/diffcheck.py`: an old 4bbd3a74be89 record against a strictcmp3 run: verdict, counts, accepted and
  differing targets
- `cmpkit-86da41d3ef68/luicomb-86da41d3ef68.out`: luicomb.py over the 8 compared functions in the 4 images
- `cmpkit-86da41d3ef68/luicomb-control-86da41d3ef68.out`: the planted control and the same function of the image of
  record
- `cmpkit-86da41d3ef68/luicomb-run.sh`: runs luicomb.py over the records and the planted control
- `cmpkit-86da41d3ef68/luicomb.py`: finds every base that two or more lui values reach, with its address where the
  dataflow knows it
- `cmpkit-86da41d3ef68/luiconst-search.out`: every lui-const in the 86da41d3ef68 outputs of the three records, with the
  command (none)
- `cmpkit-86da41d3ef68/plantlui.py`: plants the fail-open shape in a copy of an image: the positive control of
  luicomb.py
- `cmpkit-86da41d3ef68/run.sh`: makes every *.scans-86da41d3ef68.log, the B lui trace outputs, twins.log and
  luiconst-search.out on cmpkit 86da41d3ef68
- `cmpkit-86da41d3ef68/twins.log`: twin proofs of the 86da41d3ef68 run
- `cmpkit-86da41d3ef68/window.py`: every word of one function in each image, and their word compare
