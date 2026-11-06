# port_core d9e0589898fd dry re-run — libreac/fuzz_identity, A core

Ruling: a lane 19:1xZ — for a port_core output whose inputs are re-runnable, run `d9e0 --dry` on the SAME
inputs, diff the stage-out, classify every row provenance-only / patched / VALUE; a VALUE row is fixed in a
code commit before BASE with the measuring command as its record.

## Inputs, all verified re-runnable

| input | path | state |
| --- | --- | --- |
| donor text | `<the acceptance lane's workspace>/port/core/src/proofs/cgif/cgif_file_fuzzer/lib` | present |
| donor image | `<the relocation lane's workspace>/bin/cgif/cgif_file_fuzzer/cgif_file_fuzzer.asan` | present |
| target image | `<redacted: see the internal record>bin/pau-libreac-v190/libreac/bin/fuzz_identity/fuzz_identity.asan` | sha256 `c954b804786cb87f` = `builds.asan` of the unit's `harness.yaml` |
| target twin | `<redacted: see the internal record>bin/libreac-v190/x/unstripped/fuzz_identity/fuzz_identity.asan` | present |
| overrides | `<the acceptance lane's workspace>/port/core/work-libreac-fuzz_identity/overrides.tsv` | 37 rows |

The path the original run used for the target ELF no longer exists (its worktree was removed), but the pinned
copy is the same bytes by sha256 against the harness, so the inputs are re-runnable, not lost.

Command: `port_core.py --src-lib <donor lib> --old-elf <donor image> --target-lib <unit lib> --target-mod ...
--target-elf <pinned asan> --target-syms <twin asan> --files core-files.txt --override <overrides.tsv>
--work <work dir>` (no `--apply`: that is the dry run). Result `rc=3`, 17 min,
**symbol gate: explained 3093, info 67, review 143 — PASS**, 147 values with no rule.

**`--target-syms` is required for a faithful re-run.** Without it the same command gives 925 no-rule values and
`MISMATCH 5`, and produces 18 rows that look like defects in the shipped unit. They are artefacts of the
missing symbol table. That run is discarded; nothing in this record comes from it.

## The classified diff, against the SHIPPED tree

| class | count | disposition |
| --- | --- | --- |
| files agreeing definition-for-definition | 369 of 389 | — |
| files differing | 20 | below |
| `port_core_refused_*` markers | 9 definitions | d9e0 declines to decide; the shipped value stands |
| symbolic vs literal, same value | 52 definitions | `IMG_RO_LO := YImgTop.IMG_LO` vs `0x10000`; provenance-only |
| **REAL value differences** | **15 definitions** | **all REJECTED — see below** |

## Every REAL row, arbitrated against the pin and its twin

| file | definition | shipped | d9e0 | what the image says |
| --- | --- | --- | --- | --- |
| `A/AB12.v` | `TFIB_TEXT_LO` | `0x309b8` | `0x302dc` | shipped = the pin's `.text` **start** |
| `A/AB05.v` | `startup_plan_tfib_ranges` | `0x309b8` | `0x30000` | shipped = the pin's `.text` start |
| `A/AB1w.v` | `tfib_rodata_lo` / `_hi` | `0x102e0` / `0x2306c` | `0x102e0` / `0x2302c` | shipped `_hi` = the pin's `.rodata` **end** |
| `A/AE3i.v` | `IMG_RO_HI` | `0x2f9b8` | `0x2f888` | shipped = the pin's `.eh_frame` **end** |
| `A/AD2i.v` | `TFIB_MAIN` | `0x8026c` | `0x7fff0` | shipped = `main`; d9e0's address has **no symbol** |
| `A/AB1k.v` | `tfibst_text_start` | `0x651f8` | `0x64f7c` | shipped = `__sanitizer::GetMaxUserVirtualAddress`; d9e0's has none |
| `A/AB1v.v` | `tfibmusl_text_start` | `0x8a1b4` | `0x8c9bc` | shipped = `sysconf`; d9e0's has none |
| `A/AB1v.v` | `tfibguard_start` | `0x80694` | `0x80418` | shipped = `oft_exit_guard`; d9e0's has none |
| `A/AB13.v` | `TFIB_BSS` | `0xa18e0` | `0xa18e0` + extra | both = `__stop_asan_globals`; d9e0 adds a second element |
| `A/AB1k.v` | `SEALEDTOP_PC`, `SEALEDTOP_END` | `0x6522c`, `0x652e0` | `0x64fb0`, `0x65064` | neither carries a symbol; both shifted with `tfibst_text_start` |
| `A/AE37.v`, `A/AB1v.v`, `A/AB12.v`, `A/AD2j.v` | `x2_shbytes`, `tfibmusl_text_count`, `TFIB_TEXT_N`, `IMG_REGIONS` | — | — | counts derived from the addresses above |

**Verdict: all 15 rows REJECTED; no VALUE row goes into the series — and the reason is the tool's own stated
behaviour, not a defect.** Every one of these definitions lives in a file `d9e0` staged as a **generated
slot**, which the run says plainly:

```
generated slots applied (the staged files the relocation pass handled as slots): 12: A/AB01.v A/AB03.v
   A/AB05.v A/AB12.v A/AB1h.v A/AB1k.v ...
required.tsv, 15 rows of the form:
   A/AB12.v  0  -  regenerate from the start-up collector (the start-up collector)
                   (a per-image generated file: staged as a slot, not relocated)
```

So the values `d9e0` leaves in them are **cgif's own, by design** (`0x302dc` is cgif's `.text` start,
`0x7fff0` cgif's main region): the file is not relocated, it is handed to the start-up collector. The shipped
tree holds the regenerated values, which is exactly why each equals a section bound of this unit's pin or
lands on a named symbol of its twin, while the donor text does not.

An earlier version of this file called that *"a finding about d9e0 ... the tool's error"*. **That was wrong.**
It was wrong because the diff was read without the run's own `required.tsv` rows beside it; a lane named
the cause (20:21Z) and those rows had been in the output all along. Corrected rather than quietly deleted,
because the mistake is the useful part: **a relocation diff is not evidence of anything until the slot rows
are read.**

`tfib_rodata_hi` is a lane's 19:55Z donor defect, confirmed independently here: identity's `0x2306c` **is**
its own pin's `.rodata` end, so the released cell is right and the donor's value is the false one, exactly as
the ruling predicts for cgif-derived units.

One caveat for the tool's owner: this run exited **3**, not 4. A caller testing `rc == 4` for "slots were
staged, regenerate them" would not learn that 15 files need regenerating on an invocation that also has
cell-gate FAILs. Reported to a lane; not claimed as a defect here.

## The rc=3 cell-gate FAILs, explained rather than passed over

The run prints two FAILs and one PASS:

```
cell gate shadowcheck A/AF0m.v: FAIL: image bounds: OK
cell gate ownedcheck  A/AF0m.v: FAIL: image bounds: OK
cell gate cellcheck:  PASS: # 216 cells (70 file-backed), 0 mismatch
```

They are expected on a dry run, and the tool says so in its own source (`cell_gates`):

> *"AF0m's generated classes are slots until the unit puts its collector's rows in: before that, shadowcheck
> and ownedcheck report the donor's rows as wrong (expected); `--prepush` makes any failure fail the run."*

This invocation has no collector rows, so `AF0m.v` is donor text, and the two gates are reading cgif's rows
against identity's image. The third gate, `cellcheck`, is the one that reads the staged cells themselves, and
it **PASSES with 0 mismatch over 216 cells**.

**The shipped `A/AF0m.v` is right where it matters**: all 14 of its numeric cells resolve on this unit's own
pin, and 9 of them land exactly on a named symbol of its twin —

| cell | value | section of the pin | symbol |
| --- | --- | --- | --- |
| `TFIB_INST` | `0xa1958` | `.bss` | `__asan::instance` |
| `TFIB_DEPOT` | `0x186e98` | `.bss` | `__sanitizer::theDepot` |
| `TFIB_STORE` | `0x176e88` | `.bss` | `__sanitizer::stackStore` |
| `TFIB_TSD` | `0x5f92f8` | `.bss` | `__pthread_tsd_main` |
| `TFIB_IAL_LO` | `0xa61c0` | `.bss` | `__sanitizer::internal_alloc_placeholder` |
| `TFIB_IAL_FLAG` | `0x134a48` | `.bss` | `__sanitizer::internal_allocator_out_of_memory` |
| `TFIB_OOM` | `0x127220` | `.bss` | `__sanitizer::allocator_out_of_memory` |
| `TFIB_MAIN` | `0x8026c` | `.text` | `main` |
| `TFIB_GP` | `0x10800` | `.rodata` | `__global_pointer$` |

The remaining five (`TFIB_TP`, `TFIB_IAL_HI`, `TFIB_IAL_W`, `TFIB_MAIN_RA`, `TFIB_ERRNO`) are interior
addresses with no symbol of their own, each inside the expected section.
