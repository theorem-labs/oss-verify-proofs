# G5: ASan cell, shadow, owned and coverage gates on lib/Reusable/YF0m.v (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g5`).

## Tools (cited, not copied)
| tool | sha256 | reads |
|---|---|---|
| cellcheck.py | `cc60c6705e6f4264ce9b15def8a3ef85225340c1b0f95c982b4183184e530e54` | every `zN (ANum A) V` cell whose A is file-backed in the ELF: V = the ELF's little-endian N bytes at A; exit 1 on a mismatch or when no file-backed cell is found (an earlier cellcheck copy exits 0 on a mismatch; not used) |
| ownedcheck.py | `b663903ddda19527c05a72f47187888fdbc241cf911322ec751a13a66445cde8` (with its termeval.py `b64897421d5b1dd634a7d49986ea9503538b035a9c356381592a1c3dea3749b0`) | every Tfib_const cell inside Tfib_owned_static or its shadow (UNOWNED), no owned byte in .text or in a registered global (OVERCLAIM), image-bound constants equal to the ELF |
| shadowcheck.py, the fixed version | `e04173f5a5a50913ad205152cde41f4759aff4c1ca0bd521ff32c9b3616abcb7` (with its termeval.py `85060f6c7558815c5eff2149aefeab395e8e6a34b89393b38fc03013c95fa829`) | every Tfib_const_shadow cell = the start-up shadow computed from the image's asan_globals descriptors; no poisoned granule inside a Tfib_zero_shadow range |
| covcheck.py | `595119b27d0c715a6e99b21688b110154aeb7d230d7d0a29d99717c7a3370c12` | every Tfib_const_abs cell, at its full width, inside one Tfib_owned_static range or its shadow |

covcheck is no frozen tool and lives on no git ref: this is the version found on the host, dated 2026-10-29 00:35Z,
whose output matches the regenerated YF0m's stated `covcheck 853 cells, 85 owned ranges, 0 uncovered`.

## Inputs
- `$Y` = the base's `proofs/libreac/fuzz_disco/lib/Reusable/YF0m.v`.
- `$PIN_B` = fuzz_disco.asan-ubsan, sha256 `cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146`.
- `$TWIN_B` = its unstripped twin, sha256 `ead714913acd1e81835e08e021456cebcb35c09af2f87f4e7e2b6891f1b92489` (shadowcheck
  and ownedcheck need its section table). PT_LOAD 2..4 of twin and pin are byte-equal (measured); the asan_globals
  section (0xa5160..0xa5da0, 49 descriptors) lies in PT_LOAD 4.
- IMG_TOP = 0x5fe000, measured from the pin's own PT_LOADs: the last ends at 0xa25a8 + 0x55b748 = 0x5fdcf0, page round-up
  0x5fe000 (run.sh computes it and stops if it differs). It is the value of YImgTop.IMG_TOP that Tfib_zero_shadow's last
  range names.

## Commands and results (all PASS, rc 0)
| command | result |
|---|---|
| `python3 cellcheck.py <dir holding only Reusable/YF0m.v> "$PIN_B"` | `# 743 file-backed cells, 0 mismatch` (earlier record: 743) |
| `python3 shadowcheck.py "$TWIN_B" "$Y" IMG_TOP=0x5fe000` | `descriptors 49, granules with nonzero start-up shadow: 586`; `Tfib_const_shadow: 586 cells, 0 wrong`; `Tfib_zero_shadow: 25 ranges, 0 poisoned granules inside, 0 unparsed` (earlier: 586 / 0, 25 / 0 / 0) |
| `python3 ownedcheck.py "$Y" IMG_TOP=0x5fe000 --elf "$TWIN_B"` | `owned ranges 85, const cells 1439, UNOWNED 0, OVERCLAIM 0, UNPARSED 0`; `image bounds: OK` (1439 = 853 abs + 586 shadow cells; the 22 sym cells are at symbolic addresses, not ANum) |
| `python3 covcheck.py "$Y" IMG_TOP=0x5fe000` | `Tfib_const_abs: 853 cells; Tfib_owned_static: 85 ranges; 0 uncovered` (earlier: 853) |

Without `IMG_TOP=` shadowcheck refuses the last zero range (`ZERO-RANGE UNPARSED (0xa5da0, YImgTop.IMG_TOP - 0xa5da0)`,
24 ranges, exit 1): the constant is required, not decorative.

## Planted controls: all fired (copies of YF0m.v outside the tree)
| gate | plant | result |
|---|---|---|
| cellcheck | line 882 `z8 (ANum 0xa2618) 0x99478` -> `0x99479` | rc 1, `Reusable/YF0m.v 882 0xa2618 8 0x99479 0x99478`, `# 743 file-backed cells, 1 mismatch` |
| shadowcheck | line 885 `z1 (ANum 0x7fffc1f4) 0xf9` -> `0xf8` | rc 1, `CELL WRONG shadow 0x7fffc1f4 (granule 0x20fa0): stated 0xf8, start-up 0xf9`, `586 cells, 1 wrong` |
| ownedcheck | line 30 `z8 (ANum 0x13afa8) 0x1` -> `z8 (ANum 0x40000) 0x1` (a cell moved into .text) | rc 1, `UNOWNED 1`, `UNOWNED Tfib_const_abs: cell 0x40000/8` |
| covcheck | the same plant | rc 1, `UNCOVERED const cell 0x40000 width 8`, `853 cells; 85 ranges; 1 uncovered` |
