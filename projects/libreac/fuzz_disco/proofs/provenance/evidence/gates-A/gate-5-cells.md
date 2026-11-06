# Gate 5 — ASan cell / owned / shadow gates on AF0m, image A

Kind: measurement; proves no function. The file-backed const cells, the owned-static ranges, the start-up shadow cells
and the owned read-only pin count of `lib/A/AF0m.v`, each checked against fuzz_disco.asan.

IMG_TOP = 0x5fe000 — the pin's highest PT_LOAD end 0x5fd930 rounded up to a page (gate twin-check.txt; the earlier
record's "A top 0x5fd930"). Image A sha256 `5e39150dd810…`.

## Tools of record (cited by name + sha256, not copied)

- `cellcheck.py` sha256 `cc60c6705e6f4264ce9b15def8a3ef85225340c1b0f95c982b4183184e530e54` — every `zN (ANum A) V` cell
  whose address A is file-backed in the image: V must equal the image's N little-endian bytes at A. (The sibling set
  whose cellcheck exits 0 on a mismatch is NOT used.)
- `ownedcheck.py` sha256 `b663903ddda19527c05a72f47187888fdbc241cf911322ec751a13a66445cde8` (with its `termeval.py`
  `b64897421d5b…`) — every TFIB_CONST cell inside `Tfib_owned_static` or its shadow (too-narrow), and no owned byte in
  `.text` or a registered program object (too-wide), with `--elf` the pin; IMG_LO / IMG_TOP checked against the pin.
- `shadowcheck.py` sha256 `e04173f5a5a50913ad205152cde41f4759aff4c1ca0bd521ff32c9b3616abcb7` (with its `termeval.py`
  sha256 `85060f6c7558815c5eff2149aefeab395e8e6a34b89393b38fc03013c95fa829`, beside it; its own sha256 not recorded
  elsewhere, measured here) — every `Tfib_const_shadow` cell against the shadow the image's asan_globals descriptors
  imply, and no poisoned granule inside `Tfib_zero_shadow`.
- `ro_pins.py` (shipped, kind script): the owned read-only static bytes and those a const cell pins, with af0m.py's own
  `ro_segs` / `ro_counts` rule (af0m `f8201f503394`, imported from the start-up set); folded into this record.

## Commands (run.sh `cells`)

```
cellcheck.py <dir holding AF0m.v> $PIN_A
ownedcheck.py $A/AF0m.v --elf $PIN_A
shadowcheck.py $PIN_A $A/AF0m.v IMG_TOP=0x5fe000
ro_pins.py $SET $A/AF0m.v $PIN_A
```

## Verdict (all exit 0)

| gate | result | compared with the earlier record |
|---|---|---|
| cellcheck | `662 file-backed cells, 0 mismatch` | 662 / 0 (A) |
| ownedcheck | `owned ranges 84, const cells 1358, UNOWNED 0, OVERCLAIM 0, UNPARSED 0; image bounds OK` | owned-const coverage clean (the earlier 571/571 predates the 198 appended pin cells) |
| shadowcheck | `descriptors 49, 586 cells 0 wrong; Tfib_zero_shadow 25 ranges, 0 poisoned, 0 unparsed` | 586 cells 0 wrong, 25 ranges 0 poisoned 0 unparsed |
| ro_pins | `owned read-only ranges 59, owned read-only bytes 1452, pinned by a const cell 1452, unpinned 0` (af0m.ro_counts: 1452 bytes in 229 cells, from 59 ranges) | RO pins 1452 / 1452 |

ownedcheck reads the unit's `lib/Reusable/YImgTop.v` beside `lib/A/AF0m.v`, so IMG_LO 0x10000 / IMG_TOP 0x5fe000 are
checked against the pin's own PT_LOADs (`image bounds: OK`). Both cellcheck and shadowcheck give the same result against
the unstripped twin as against the pin (the data they read is byte-equal in PT_LOAD 4). **0 defects.**

## Planted controls (one per tool, each must fire)

- **cellcheck** (`plant-cellcheck`): AF0m.v with `z8 (ANum 0xa1200) 0x8` → `0x9` → `… 1 mismatch`, exit 1.
- **ownedcheck** (`plant-ownedcheck`): a const cell moved to `0x30eb0` (inside `.text`) → `UNOWNED 1`, exit 1.
- **shadowcheck** (`plant-shadowcheck`): a shadow cell `z1 (ANum 0x7fffc1f3) 0x6` → `0x7` → `Tfib_const_shadow: … 1
  wrong`, exit 1. Also `control-shadow-noimgtop`: the same AF0m.v without IMG_TOP leaves the named last range `1
  unparsed`, exit 1 (the earlier record's "no IMG_TOP → UNPARSED").
- **ro_pins** (`plant-ro_pins`): the pin cell `z8 (ANum 0x103b8)` moved to `0xa1208` so an owned read-only byte is left
  uncovered → `unpinned` ≥ 1, exit 1.

All recorded `FIRED` in run.sh.
