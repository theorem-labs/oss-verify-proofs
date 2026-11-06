# Gate 3 — codeptr of record, image A start-up files

Kind: measurement; proves no function. Every hex literal and every decimal ≥ 0x10000 in the start-up files is resolved
against fuzz_disco.asan (its own image): a code address, a return pc, a data cell, a value at or above the image top, a
quantity by its type, or a donor address left unmoved (a finding). The donor side is cgif's own version of each file
(`--stale-dir`), so a value both images carry with the same meaning is not stale.

## Command (run.sh `codeptr`, through the frozen start-up set)

```
frozen-run.sh startup-set-2026-10-30d.tsv codeptr.py \
  --image $PIN_A --names $TWIN_A --stale-image $CGIF_BIN.asan \
  --stale-names $CTL/syms/cgif_file_fuzzer.asan.nm --stale-dir $CGIF_LIB \
  [declarations] $A/AB01.v $A/AB03.v $A/AB05.v $A/AB12.v $A/AD1k.v $A/AD2i.v $A/AD2j.v $A/AF0m.v $A/ACej.v
```

## Tool of record (cited by name + sha256, not copied)

`codeptr.py` sha256 `12348302dfd2e419748bc3ad20e67b246d21b576c9c6d7887a33854785e146dd` — the codeptr of record, run
through the start-up set of record `startup-set-2026-10-30d` (its 18 bundle lines verified `sha256sum -c SHA256SUMS`,
50 OK; `frozen-run.sh` sha256 `40cd8a4bf5bf355c4a8f506bcc1503e9c7ec4a1331831204bd36ef22a8915ab4`). The run self-tests
27 known answers before it reads a file. Symbols from the unstripped twin `$TWIN_A` (PT_LOAD 2..4 byte-equal to the pin,
gate twin-check.txt); cgif's from its symbol list `cgif_file_fuzzer.asan.nm` sha256
`bc0bee6320e6b74f4a2c0e7baa557a3abd07bc0ecc9727d697377c3681fa060f`.

## Control of record (known answers, run first)

`codeptr-controls.sh` sha256 `25c012a65b96fe16406ee979efb146b6bd266770739bbedfc3b57f5fd54e3c03` through the same set:
`codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)`, exit 0. (1) MUST FIND cgif's own
unrelocated AD1k / AD2i / AD2j (22 / 6 / 107 findings) and YD1k / YD2i / YD2j (22 / 6 / 107), each line naming its
paired donor file; (2) MUST NOT FLAG cgif's `YF0m.v:289` 0x8065e (a bucket index), listed as not an address.

## Verdict

- **Raw** (no declarations, `codeptr/raw`): 25 findings over the nine files — AB01 6, AB03 9, AD1k 2, AD2i 2, AD2j 2,
  AF0m 4 (AB05, AB12, ACej 0). Every finding is a value both images carry with the same meaning (a layout constant or a
  quantity), triaged below.
- **Declared** (`codeptr/final`): exit 0, **0 FINDINGS** on all nine files. Declarations (each checked against the pin):

  | value | kind | what it is |
  |---|---|---|
  | 0x10800 | --same | gp = `__global_pointer$` 0x10800 in fuzz_disco.asan (twin symtab) and in cgif asan: a layout constant both link the same |
  | 0x10310 / 0x103c0 | --same | region bounds of AD2j / AD1k (CImg 40 / 16) in fuzz_disco.asan .rodata (the region generator output from the pin) |
  | 0x103b8 | --same | AF0m const cell `z8 (ANum 0x103b8)` in .rodata; its value equals the pin bytes (cellcheck 0 mismatch) |
  | 0x10101 | --not-address | 65793 (flag bytes 01 01 01) stored in the collected states and AF0m cell 0xa6928 |
  | 0x1ffff / 0x20000 / 0x445c0 / 0x100000 / 0x100018 / 0x3fffff | --not-address | numeric bounds / sizes of the collected start-up states (2^17, 1 MiB, 2^22−1, …) |
  | 0x71c00 / 0x161200 / 0x38e000 | --not-address | byte lengths of a runtime mmap region or its shadow in the collected states |

Each declared value is also a flagged row of gate 1, triaged there; the two gates agree. No value is a donor address
left unmoved. **0 real defects.**

## Planted control (must fire)

A copy of `lib/A/ACej.v` outside the branch with the `CTX_target_alloc_init` return address `0x80c04` set to cgif's
value in the same slot, `0x80150` (a donor address copied unchanged). Re-run: `ACej.v … 1 FINDINGS: 0x80150 [… 1 STALE
(0x80150)]`, exit 1. A run with 0 findings would be void. Recorded `FIRED` in run.sh.
