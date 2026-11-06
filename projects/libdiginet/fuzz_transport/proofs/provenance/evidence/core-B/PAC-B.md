# port_addr_check record of libdiginet/fuzz_transport's image-B core (run r17)

proves no function (kind: measurement). The address checker port_addr_check, run once on run r17 of record (the
stage/ donor text against the stage-out the tree applies), and the verdict on each row that is decided by hand: the
rows that an --override row of overrides-B.tsv writes and the checker cannot name, and the one changed bound read by
hand.

## The run

Checker: port_addr_check.py sha256 `45b78aaa48c332768dcd469c4da8658c573ba6f260d79642d1fe85bb99c92371` (the address
checker's release directory versions/45b78aaa48c3/, its SHA256SUMS checked; the checker of record from 2026-10-31
16:17Z). It replaces 205a90fd19b8 (`205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69`), which was run
on the same inputs as the baseline.

    python3 <CK> --src <WORK>/stage --dst <WORK>/stage-out \
      --src-image "B=<P>/bin/fuzz_decode/fuzz_decode.asan-ubsan:<P>/unstripped/fuzz_decode/fuzz_decode.asan-ubsan" \
      --dst-image "B=<T>/result/bin/fuzz_transport/fuzz_transport.asan-ubsan:<T>/result/unstripped/fuzz_transport/fuzz_transport.asan-ubsan" \
      --donors-from <DONORS> --paired-only --out rec.tsv --summary --cache <CACHE> --fail-on-flags

`<CK>` the checker, `<WORK>` run r17's directory, `<P>` / `<T>` the image trees of run.sh, `<DONORS>` the symbolised
donor image tree the checker reads, `<CACHE>` a new empty directory. Images: donor fuzz_decode.asan-ubsan 5d05689fd5b1
(twin 6744989bb2e6), target fuzz_transport.asan-ubsan 41113a03c82f (twin e217cb0a84f1). 388 files paired, 168131
numerals; named-symbol cells unmeasured 0 / 883; the checker's known-answer control ran and passed. Exit 4 (rows
flagged), as with every port_core run of this core.

## Flag counts

| class | 205a90fd19b8 on run r17 | 45b78aaa48c3 on run r17 |
|---|---|---|
| DIFFERENT-SYMBOL | 19 | 19 |
| GEOMETRY-CHANGED | 3 | 3 |
| KIND-CHANGED | 10 | 10 |
| NON-ADDRESS-CHANGED | 174 | 173 |
| SAME-VALUE-DIFFERENT-OBJECT | 11 | 13 |
| STALE-DONOR-CODE-POINTER | 3 | 3 |
| UNPAIRED-PORTED | 177 | 177 |
| UNPAIRED-SOURCE | 254 | 254 |
| UNRESOLVED | 18 | 18 |
| flagged | 669 | 670 |

`PAC-B.r17.flagged.tsv` (beside this file) lists the 670 rows 45b78aaa48c3 flags, with the checker's own columns
(verdict, files and lines, sentence, index, kind, both values, the class of the source value, what each value denotes,
the checker's note). Two rows are new against 205a90fd19b8 and one is gone; the other 668 are the rows 205a90fd19b8
flags on the same run (keyed by class, file, sentence, index and both values). This record does not classify those 668
one by one.

- New, SAME-VALUE-DIFFERENT-OBJECT: B/YE30.v:1395 and B/YE6k.v:1389 (`entD_ro`, sentence 15), 0x200000 in both texts.
  It is the bound of `fst (fst e) + snd (fst e) <= 0x200000` over the seven entries of B/YE2y.v's `icpt_rodata`, not
  an address (205a90fd19b8 classes it NON-ADDRESS-SAME: a size in a bound slot). The entries' largest end is 0xad378
  (the donor's 0xa2038), below 0x200000; the build proves the assertion entry by entry.
- Gone, NON-ADDRESS-CHANGED: B/YD1g.v:1279 (`static_img_chk`), 0x5e6000 -> 0x606000; 45b78aaa48c3 classes it
  SAME-GEOMETRY (the image span, each image its own).

## Rows decided by hand

The 7 UNRESOLVED rows of CZONE: B/YFix.v:284 and :288, B/YFjb.v:283 and :287, B/YFju.v:574 and :584, B/YFkm.v:1296
(donor line numbers, as overrides-B.tsv names them; each stage-out line is one more), 0x80050000 -> 0x800b9c00. The
checker reads both values as shadow bytes of .bss with no object at them. Each is an overrides-B.tsv row: CZONE =
kLowShadowBeg + IMG_TOP / 8 = 0x7fff7000 + 0x616000 / 8 = 0x800b9c00 (Reusable/YG0f.v:22; IMG_TOP 0x616000 of pin
41113a03c82f), as the image-A core (A/AFix.v:286); above the highest constant shadow cell of B/YF0m.v, 0x800b65cc,
which the donor's 0x80050000 is below.

The changed bound of B/YE7d.v:78, which the checker passes as SAME-SYMBOL (it reads each value as an end whose last
byte is `__sanitizer::useCounts + 0x1053f` in its own image), read by hand:

    B/YE7d.v:78 snl_rom_low X 0x143740 -> 0x14ea80: changed bound, SAME-SYMBOL, true for both values (ceiling above RO end 0xa3000), 0 readers: no change

`in_rom tfibsegs a` (Reusable/YG0d.v:381) holds for the addresses of the image's non-writable segments, which end at
0xa25a4 (the read-only and executable PT_LOAD of pin 41113a03c82f; 0xa3000 rounded up to a page), so `0 <= a < X`
holds for X = 0x143740 and for X = 0x14ea80. `git grep -nw snl_rom_low` over lib at 5fb903565376 finds its own
definition and image A's own lemma of the same name (A/AE7d.v:77), no reader.
