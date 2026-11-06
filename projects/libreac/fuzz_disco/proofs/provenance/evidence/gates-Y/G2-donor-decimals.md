# G2: decimal literals that are a cgif address and not the same object in fuzz_disco (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g2`).

## Scripts (shipped in donordec/) and the kit they import
- `donordec/donor_decimals.py` sha256 `a7ec855ffb43c421a5cab3c96b2ca4c7be781ed2ad79fceac663ef12b3dbc1aa` and
  `donordec/funnel.py` `9cc314dc24afe2dbc3a454d3932fbde3970728b1bf3df6f6cb75f7b7aa978284`: the new versions that take
  every path as an argument (the earlier version, donor_decimals.py of commit f718ed26820f, held the git directory,
  the cgif pins and the fuzz_disco pins as constants). Byte-identical to `gates-A/donordec/`. A literal v (decimal,
  0x10000 <= v < 0x600000, outside comments) is a row when cgif's image has a symbol N covering v at offset o and
  fuzz_disco's does not place N + o at v. funnel.py then classes each row (NOT-IN-DONOR, SIZE, ODD-IN-CODE, INSN-IMM,
  LABEL, DISCO-POINTER) and prints the rest as UNEXPLAINED.
- Imported kit (cited, not copied): the frozen port_addr_check 5033540ba83b directory of commit 088272ccecac:
  port_addr_check.py `5033540ba83bdad174e9b1aa3cc21ffeda3469736e4dd0390f58db9008890546`,
  scan_literals.py `ae01d69b2ee4af269258982bef0de35a38a44d2b8832b62ef217e58439cd5804`, cfgpair.py
  `bc9795900868df328eebcf4f90bc7c1cbf9abf5ab9efa95474a2871bf99c5cd4`; donor_decimals.py refuses another version.
  cgif symbols are recovered by the kit from the donors under `$DONORS` (56 donors; asan and asan-ubsan: 1247 functions,
  705 objects each); fuzz_disco symbols come from the unstripped twins.

## The new version gives the old version's rows (same inputs)
- donor_decimals.py, old (sha256 `e7d879e2ed9ce55d1f3b430abd72537ac6457f578fb062a82a212d19e844352b`, its own constants:
  cgif pins 7093581aab04 / 1c29845fe605, fuzz_disco pins with the `.debug` twins) and new (those same files as
  arguments), on the base, `--subdirs Reusable,Y,B`, the old run reading a copy of the new run's recovery cache: 2869 rows
  each, byte-identical (sha256 `9d5c38498fd28a679c888be2ec162b2715c29ef5accdd3f2d58236fc22daaed3`).
- funnel.py old (`940cb11df71e5f8a1774e2ec6d86a7a556ffb9475f4058d4f0aab77e3d846189`, which reads cgif's literal set from a
  moving released ref, here at commit 09c6822d8861) and new (`--cgif-lib 09c6822d8861:proofs/cgif/cgif_file_fuzzer/lib`, same images)
  on that scan: byte-identical (sha256 `ced836a759600d32cfec0ddd2ee8fa213b20af91417b34072cd1faadf6c4221f`), and equal to
  the record run's `--cgif-lib c8557374ad2e:...` output, the shipped funnel_Y.txt.
- The gates-A slice made the same comparison on lib/A and on both controls (equal byte for byte).

## Commands (run.sh g2; every path a variable)
```
COMMON=(--git "$GIT" --kit "$KIT5033" --donors-from "$DONORS" --cache "$WORK/g2/cache"
        --cgif-image asan="$CGIF_BIN/cgif_file_fuzzer.asan" --cgif-image asan-ubsan="$CGIF_BIN/cgif_file_fuzzer.asan-ubsan"
        --target-image asan="$PIN_DIR/fuzz_disco.asan:$TWIN_DIR/fuzz_disco.asan"
        --target-image asan-ubsan="$PIN_DIR/fuzz_disco.asan-ubsan:$TWIN_DIR/fuzz_disco.asan-ubsan")
donordec/donor_decimals.py "${COMMON[@]}" --target disco --subdirs Reusable,Y,B --tree base=b1afc3e80791 --out scan_Y.tsv
donordec/donor_decimals.py "${COMMON[@]}" --target cgif --subdirs '' \
    --tree cgif=c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib --out control_neg.tsv
donordec/donor_decimals.py "${COMMON[@]}" --target disco --subdirs A --tree none=b1afc3e80791@b1afc3e80791 \
    --plant plant_AE23.v --out control_pos_AE23.tsv          # plant_AE23.v = cgif lib/A/AE23.v line 471
donordec/donor_decimals.py "${COMMON[@]}" --git <a repository holding the planted YE23.v> --target disco \
    --subdirs Reusable --tree plant=HEAD --out control_pos_YE23.tsv
donordec/funnel.py "${COMMON[@]}" scan_Y.tsv --cgif-lib c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib > funnel_Y.txt
```
The record inputs (the hub's cgif pins, the v190 twins) give the same 2869 rows as the old inputs, byte for byte.

## Controls: both fired
- Negative: cgif as the target over its own lib at c8557374ad2e (2467 files): 0 rows (`control_neg.tsv`, sha256
  `2a34bb11aff4...`, = gates-A's).
- Positive, the brief's: cgif lib/A/AE23.v line 471 (`Z_to_bv 64 6264480`, cgif asan buf+0x8) planted as a fuzz_disco
  lib/A file: 1 row, `6264480 0x5f96a0 buf+0x8 ... target_same 0x5fc758` (`control_pos_AE23.tsv`, `8e2853591718...`,
  = gates-A's).
- Positive on image B: a copy of lib/Reusable/YE23.v with line 474's `6277920` (fuzz_disco buf+0x8) replaced by cgif's
  `6265120` (cgif asan-ubsan buf+0x8), in a one-commit repository outside the tree: the row `YE23.v 474 6265120
  0x5f9920 buf+0x8` is there (`control_pos_YE23.tsv`; the other 22 rows are YE23.v's own decimals, which the base scan
  carries too and the funnel classes).

## Result: 2869 rows, 0 defects
Rows by image and tree: asan-ubsan 2766 (lib/Reusable 2588, lib/Y 75, lib/B 103), asan 103 (lib/B: the script reads a
file outside A/, U/, Reusable/Y*, Y/ against both ASan images). funnel_Y.txt: NOT-IN-DONOR 1724 rows (491 values),
SIZE 705 (30), ODD-IN-CODE 326 (6), INSN-IMM 3 (2), LABEL 42 (14), DISCO-POINTER 13 (7), UNEXPLAINED 56 (12).

Every UNEXPLAINED row, triaged (the reading in image B is the twin's; none is a cgif address left in place):

| value | rows: where | what it is in fuzz_disco | why it is right |
|---|---|---|---|
| 1446400 | 26: YB01.v:15 (x17), :117, :121; YD1d.v:38, :281; YD1f.v:195; YG0t.v:58, :63 (x2), :692 | kFakeStackSize / 8, the ASan fake stack's shadow length (YG0t.v:58 `assert (E2 : kFakeStackSize / 8 = 1446400) by reflexivity`) | a length (kn_zero / KZero / KDisj), checked by the kernel; equal to cgif's |
| 2101549 | 2: YB01.v:15, YB03.v:13 | `KRange (EVar 9) 4397 2101549` = the V_HW range 0x112D .. 0x20112D | a value bound, the model constant G1 classes MODEL-CONST; equal to cgif's |
| 2107576 | 5: YK12.v:298; YK14.v:357, :360, :364, :395 | the `<=` bound of `struct_av_bound` (argv struct bytes) | a byte bound, not an address |
| 200020 | 6: YO0i.v:1037, :1038, :1043, :1049, :1055, :1061 | `KMmapRW 200020` in YO0i.hdr_script | an mmap size |
| 200100 | 3: YO0i.v:1054, :1056, :1057 | `Realloc 0 200100` | a realloc size |
| 400020 | 1: YO0i.v:1050 | `KMmapRW 400020` | an mmap size |
| 262728 | 1: YFfg.v:243 | the length operand of `do_stretch HS 42%nat 0xeb440 262728 0x5ea78` | a length beside two hex pcs |
| 683224, 683225, 683228, 683232, 683240 | 2 + 2 + 4 + 2 + 2: YB01.v:15 and YB03.v:13 | addresses inside fuzz_disco's own `__asan::asan_flags_dont_use_directly` (0xa6c78, 120 bytes: +96, +97, +100, +104, +112) in states collected from the image B run: KWord cells holding 1 (+96), 2 (+100), 81601 (+104), 65793 (+112), and the KImg range bound 683225 .. 683228 | image B addresses; they only coincide with cgif's AsanMappingProfile+0xa48.. |

The same 12 values, with the same readings, are the hand-explained rest of the earlier record of this scan.
