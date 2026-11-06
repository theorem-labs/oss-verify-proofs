# kit-rerun/B: every lui of the B record and of the settled rows, hand-traced through all ALU ops

Why: the KIT LIMIT of cmpkit 86da41d3ef68. Rule 8 of strictcmp3 65688e94214a, and therefore luiscan 9ae61e4a0e01, carry
a lui value forward only through addi, load, store and jalr. They do not follow it through add, sub, the shNadd ops or
the other ALU ops. So the `memfed 0` that clears these two records in the scan logs is not proof:
- the B record (`B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log`);
- the settled rows (`cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log`).

The A record's own hand trace (`A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md`) covers 7 functions, donor twin : decode A.
This file covers the B record's 8 functions:
- donor twin T `cgif_file_fuzzer.asan-ubsan` (sha256 ce511d541cda), the twin the A record uses;
- symtwin S `cgif_file_fuzzer.asan-ubsan.symtwin` (3f110c1db582);
- against decode B twin E `fuzz_decode.asan-ubsan` (6744989bb2e6).

The settled rows lie in two of these functions. Provenance only: no .v file, no theorem, no function proved here.

## 1. Method and outputs

`cmpkit-86da41d3ef68/run.sh` runs the A record's own `luitrace.py` (`A/kit-rerun-4bbd3a74be89/luitrace.py`) in `pair`
mode on T : E and on S : E, over the 8 function names of the B record. It is the same tool on the same dataflow,
LUI-HANDTRACE.md section 1: a MAY forward dataflow over the whole CFG, through every ALU op and every copy, fail-closed.
It also prints every word of TryMemCpy in both images (`window.py`).

| file | what it holds |
|---|---|
| `luitrace-pair-TE-86da41d3ef68.out` | one ROW per lui, T : E, and both full traces |
| `luitrace-pair-SE-86da41d3ef68.out` | the same, S : E |
| `luitrace-compare-86da41d3ef68.out` | T : E against the A record's trace, and S : E against T : E |
| `luitrace-TryMemCpy-86da41d3ef68.out` | every word of TryMemCpy in T and in E, and their word compare |

Count check: each image has 19 lui, the luiscan `luis 19` per image of the B scan log:
- Allocator::Allocate 12, CombinedAllocator::Allocate 5, memset 1: the 18 of the A record;
- TryMemCpy 1: the B record's eighth function, which the A record does not compare.

TOTAL of the pair runs: `lui rows 19, class a 5, class b 14, unmatched none`.

## 2. The 18 rows the A record also has

- **Same rows as A.** The 18 ROW lines of T : E (all but TryMemCpy) are byte-identical to the ROW lines of the A record's
  `out/luitrace-pair-86da41d3ef68.out` (luitrace-compare: IDENTICAL). Each row matches in offset, register, value in
  both images, class, use kinds, number of uses, chain words, number of words equal, and in the differing words, which
  are `jal` words only.
- **S gives the same as T.** S : E gives exactly what T : E gives (luitrace-compare: IDENTICAL over every line that does
  not name an image). The symtwin carries the donor's bytes: `cmpkit-86da41d3ef68/twins.log` shows that S and T equal
  the donor pin outside the ELF header and the build id.
- **Decode B against decode A.** The A rows compare the same donor bytes against decode A. The decode B traces
  therefore have the same structure, and the same equal and differing word counts, as decode A's.

LUI-HANDTRACE.md sections 3 and 4 give the hand argument for these 18 rows. Its three mechanical facts, measured again
on decode B:
1. **No value lies in an allocated section.** luiscan `insec 0` holds for every function in S, T and E (the B scan log).
   0x10000 is the ELF header region, in no section (`inload`).
2. **No load, store or jump has a statically known lui-derived base.**
   - In `luitrace-pair-TE-86da41d3ef68.out` there are 166 MEMBASE / JUMPBASE use lines at 27 distinct sites, over both
     images. Every one of them has an unknown effective address (`ea=-`): its base is a runtime pointer. These are the
     same 166 lines at the same 27 sites as the A record's trace, measured with the same `awk` over the USE lines.
   - The known values that reach a call argument are 0xfff8, 0x0101010101010101, 0x10000 and 0x10001, in 22 CALLARG
     use lines out of 358, the same as in the A trace. They are sizes, masks and bounds, not in any section.
3. **The address is the same expression in both images.** strictcmp3 compares the 8 functions on S : E and T : E with
   0 real words and 0 unmeasured words (the B scan log, `control` section): every word is identical or differs in a
   pc-relative field only. Inside the traces, the differing words are the `jal` call words.

So in every class (b) row the lui value is a mask, a bound or an index added to a runtime pointer, as in the A record.

## 3. TryMemCpy +0x34, the 19th row (class a)

Words of `luitrace-TryMemCpy-86da41d3ef68.out`, the same in T and E:

```
+0x034  37b5aaaa  lui  a0, 0xaaaab
+0x038  930aa5aa  addi s5, a0, -0x556      s5 = 0xffffffffaaaaaaaa
+0x03c  23245101  sw   s5, 8(sp)
+0x040  23265101  sw   s5, 0xc(sp)
+0x044  13058100  addi a0, sp, 8           a0 written: the lui register is dead
+0x070  23225101  sw   s5, 4(sp)
```

- **The value is only stored, as 32-bit data.** Its uses are the three `sw` words: STOREDATA, the poison pattern
  0xaaaaaaaa written into the stack slots of the two pipe fds and of the status word. The base of each store is `sp`.
  `a0` is overwritten at +0x44. `s5` is read by no other word: it is callee-saved, and +0x13c restores it.
- **What reads the slots back.** The `lw a0, 8(sp)` / `lw a0, 0xc(sp)` words that read the slots back pass a 32-bit fd
  to the fd helpers. They are reached only after the internal_pipe call at +0x48 returned 0 (`bnez a0` at +0x4c leaves
  for the CheckFailed path otherwise). luitrace does not follow memory, so this part is read from the words above. None
  of these words is a base.
- **Not an address.** The value lies in no section of either image (luiscan `insec 0`).
- **The two images agree.** The word compare gives 100 offsets: 88 identical, 12 differing. The 12 are the `jal` at +0x48
  and the `auipc` / `addi` pairs at +0xe0..+0x184 that form the CheckFailed arguments, all pc-relative. Every word of
  this row's chain (+0x34, +0x38, +0x3c, +0x40, +0x70) is identical.

## 4. The settled rows

The three rows of `cmpkit-4bbd3a74be89/settled.tsv` lie in two functions:
- Allocator::Allocate: its 12 lui are rows of section 2.
- PoisonShadow: it holds no lui (luiscan `luis 0` in S, T and E).

Neither settled target is built by a lui:
- Allocate +0xdc is an `auipc` / `addi` table address.
- PoisonShadow +0x48c is an `auipc` / `ld` of a .got cell.

## 5. lui-const

No output of the A, B or settled records holds a `lui-const (dataflow)` row, and luiscan's `luiconst` column is 0
everywhere. The search command and its counts are in `cmpkit-86da41d3ef68/luiconst-search.out`. The registry notice's
fail-open class therefore has no row to bite on in these records.

## 6. Result

All 19 rows were hand-traced per pair: 5 (a), 14 (b), with no mismatch. No address of the B record or of the settled rows
depends on a lui value, and no lui-derived target differs between the layouts. The `exposure 0` of the B and settled
scan logs stands, now on this hand argument rather than on `memfed 0`. No verdict changes.
