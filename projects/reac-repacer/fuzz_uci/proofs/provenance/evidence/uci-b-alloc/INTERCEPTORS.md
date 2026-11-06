# Interceptor inventory: reac-repacer fuzz_uci, fuzz_egress, fuzz_wire, image B (asan-ubsan)

Read-only. For each image this lists every defined function symbol named `__interceptor_*`, `___interceptor_*` or
`__asan_*`, and marks the ones the program code calls directly. The full lists are in `inventory/inventory-{uci,egress,wire}.tsv`
(one row per symbol: address, size, binding, other names at the same address, direct call sites, calling trampoline);
`inventory/run.sh` repeats the run. The file names here are those of the committed slice: `inventory/` is what
`inventory/run.sh` writes to its `commit/`.

## Method

- **Images:** each unit's unstripped twin. Each twin's PT_LOAD bytes equal its pinned image's outside the ELF header
  and `.note.gnu.build-id` (the `twins.out` of the UCI-B-ALLOC, EGRESS-B-ALLOC and WIRE-B-ALLOC records). So the
  symbols name code that is in the pin. The raw outputs name the twins by the tokens `UCI_B_TWIN`, `EGRESS_B_TWIN` and
  `WIRE_B_TWIN`, which `inventory/images.sha256` defines by sha256 and index line.

| unit | pin (stripped) sha256 | index line | unstripped twin sha256 |
|---|---|---|---|
| fuzz_uci | `a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc` | index/binaries.tsv:7521 | `8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16` |
| fuzz_egress | `a4a151dbf92bc8641d13932865f9d51bf2fd95b0f98d0cc9aa173d87c52ab63e` | index/binaries.tsv:7513 | `5db4802c6137e4d3fff1651b098ff56f3b1a6fe11023ea06ca4fef8910c600c6` |
| fuzz_wire | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` | index/binaries.tsv:7525 | `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3` |

The index lines are the same at f47e2a8927b9 and at recipes 6d085644782c.

- **Tool:** `inventory/tools/inventory.py` (sha256 `c4e5592ab63d5d584fce9e0e188faa1e6c384fa51b544481492b87cbc02cfc64`,
  written for these records). It loads the same `drvcmp.py` (1b13206c79dd), bytecmp (0ac2ec8db277, from 1480ca2faea0)
  and repin_check (f268a01b33c5, from e5487165abb8) copies as the UCI-B-ALLOC record. `inventory/tools.sha256` lists
  them, and `inventory/tools/DIFFS.md` gives each copy's original, source and diff. The inventory uses only
  repin_check's `targets()`, which e5487165abb8 did not change. The previous run, with repin_check 9cbc3553c09e, is
  kept in `inventory/v9cbc3553c09e/` (outputs, its own `tools/` and `DIFFS.md`); its outputs are byte-identical to
  the version of record's.
- **Program code:** the DWARF subprograms of every CU that is not under /llvm-project and not musl. This is bsurvey.py's
  root rule (B-DONORS.md, "Method"). It gives 15 functions for uci, 21 for egress and 30 for wire.
- **Direct call:** a jal (any rd, so tail calls count) or auipc+jalr whose target `targets()` resolves (a `.got` cell is
  dereferenced) to the start of a function outside the caller. This is bsurvey.py's `callees()` rule.
- **Trampolines:** a directly called trampoline (`__interceptor_trampoline_X`, one `j`) marks its jump target
  (`___interceptor_X`, and the weak alias `__interceptor_X`) as reached "via trampoline".
- **Register-indirect calls:** the program code has none in any of the three units (0 register-indirect call sites).

## Summary

| | fuzz_uci B | fuzz_egress B | fuzz_wire B |
|---|---|---|---|
| inventory symbols | 180 | 184 | 185 |
| `__asan_*` / `___interceptor_*` / `__interceptor_*` (of which trampolines) | 61 / 40 / 79 (39) | 62 / 41 / 81 (40) | 63 / 41 / 81 (40) |
| called directly by the program code | 17 | 17 | 18 |
| reached via a directly called trampoline | 20 names (10 interceptors with their weak aliases) | 20 (10) | 20 (10) |
| neither | 143 | 147 | 147 |
| **`__asan_memset`** | **ABSENT** | **PRESENT** 0x50d48, 576 B; called at LLVMFuzzerTestOneInput+0x138 and rp_mute+0x7c | **ABSENT** |
| **`__asan_memcpy`** | **PRESENT** 0x50674, 1180 B; 4 call sites | **PRESENT** 0x508ac, 1180 B; 6 call sites | **PRESENT** 0x50c14, 1180 B; 4 call sites |
| `__asan_memmove` | ABSENT | ABSENT | PRESENT 0x510b0, 880 B; called at rp_copy_untag+0x64 |

- **wire B and `__asan_memset`:** wire B has no `__asan_memset`. This confirms the report that it is absent.
- **uci B and `__asan_memset`:** uci B has none either.
- **The memset-named functions in uci B and wire B** are only these: `__interceptor_trampoline_memset` / `__wrap_memset`,
  `___interceptor_memset` / `__interceptor_memset`, `__sanitizer_internal_memset` and musl's `memset`. The program
  code calls none of them directly (`inventory/summary-*.out`).
- **Across the three images**, the inventory sets differ only by these names:
  - `___interceptor_bcmp`, `__interceptor_bcmp`, `__interceptor_trampoline_bcmp`: egress and wire only;
  - `__asan_memset`: egress only;
  - `__asan_memmove`, `__asan_stack_malloc_0`: wire only.
  
  All 180 of uci's names are in all three images.

## Called directly by the program code (call sites; "-" = defined but not called directly; ABSENT = no such symbol)

| function | fuzz_uci B | fuzz_egress B | fuzz_wire B |
|---|---|---|---|
| `__asan_handle_no_return` | 3 | 5 | 9 |
| `__asan_memcpy` | 4 | 6 | 4 |
| `__asan_memmove` | ABSENT | ABSENT | 1 |
| `__asan_memset` | ABSENT | 2 | ABSENT |
| `__asan_report_load1` | 11 | 13 | 63 |
| `__asan_report_load4` | 14 | 4 | - |
| `__asan_report_store1` | 2 | 7 | - |
| `__asan_report_store2` | - | - | 1 |
| `__asan_report_store4` | 7 | - | 1 |
| `__asan_stack_malloc_0` | ABSENT | ABSENT | 1 |
| `__asan_stack_malloc_1` | 1 | 1 | 1 |
| `__interceptor_trampoline__exit` | 1 | 1 | 1 |
| `__interceptor_trampoline_bcmp` | ABSENT | 4 | 1 |
| `__interceptor_trampoline_fflush` | 1 | 1 | 1 |
| `__interceptor_trampoline_fprintf` | 2 | 2 | 2 |
| `__interceptor_trampoline_free` | 6 | 8 | 6 |
| `__interceptor_trampoline_fwrite` | 2 | 2 | 2 |
| `__interceptor_trampoline_malloc` | 6 | 9 | 6 |
| `__interceptor_trampoline_memchr` | 1 | - | - |
| `__interceptor_trampoline_memcpy` | 3 | 3 | 3 |
| `__interceptor_trampoline_read` | 1 | 1 | 1 |
| `__interceptor_trampoline_vprintf` | 1 | 1 | 1 |
| **total in the inventory** | **17** | **17** | **18** |

The interceptors reached through those trampolines are `___interceptor_{_exit, fflush, fprintf, free, fwrite, malloc,
memcpy, read, vprintf}` in all three units, plus `memchr` in uci and `bcmp` in egress and wire.

**Cross-check with B-DONORS.md's "Direct callees" tables:**

| | uci | egress | wire |
|---|---|---|---|
| table rows (lines) | 22 (lines 27-58) | 22 (lines 198-229) | 23 (lines 141-173) |
| inventory direct callees + musl callees (`abort`, `atexit`, `close`, `exit`, `open`) | 17 + 5 | 17 + 5 | 18 + 5 |

The names are exactly those of the tables, without the rows marked "(trampoline target)". Calls from one program
function to another are left out, as there.

## Files (the committed slice: `inventory/`, written by `inventory/run.sh` to its `commit/`)

- `inventory/tools/`: `inventory.py`, `drvcmp.py`, `bytecmp-1480ca2faea0.py`, `repin_check-e5487165abb8.py`,
  `scrub_out.py`, `mkdiffs.py` and `DIFFS.md`; `inventory/tools.sha256`. The previous run: `inventory/v9cbc3553c09e/`.
- `inventory/run.sh`. It needs an `env.sh` beside it that sets `UCI_U`, `EGRESS_U` and `WIRE_U` to the three twins;
  env.sh is not committed. Its last step, `tools/scrub_out.py`, writes `commit/`. It rewrites each twin path to its
  token and refuses its output if a host path, an internal branch prefix, a worker name or the tool registry's branch
  name is left.
- `inventory/images.sha256`, `inventory/inventory-{uci,egress,wire}.tsv`, `inventory/summary-{uci,egress,wire}.out`.
- **Checks (2026-10-30, after the move to repin_check e5487165abb8):**
  - Rows that changed: **none**. The version of record's raw outputs are byte-identical to the previous run's (6
    files: 1,835 numbers; only `tools.sha256` differs).
  - Replacing each token in `commit/` by its twin path gives back every raw output (14 files, both versions).
  - Run from a copy of `commit/` with an `env.sh`, `run.sh` wrote an identical `commit/`.
