# A/AB1w.v regenerated for libreac/fuzz_boxreg.asan (TFIB function-range table)

Output: `AB1w.v` in this directory (628 lines). It replaces
`A/AB1w.v` of the run-9 stage-out set (the relocation script's run-9 output, 616 lines; the set is not in the repository: 462 `.v` files, set sha256 `c5ea51aee5265490d7a8e0f76366a5fdf1d7068ed3f60b9aaa30d6d2bb74233c`, see Commands), which left 25 rows as
`port_core_refused_<cgif addr>` and kept cgif's merged rows whole.

## Sources

- cgif table (row names and row order): `proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v` (git blob
  `4dead8b1cff4cc7af784e200ee7644eb50002411`; 545 `tfib_A_*`/`tfib_E_*` rows, lines 20-564).
- Function pairing by address, code-verified: `fnstart.tsv` in this directory (sha256
  `e80f10f1e8af1501767ec52f68eb2c72eb51e6d807b7b5068152e0308903f084`; 545 rows, column `port_target` =
  `<boxreg symbol>@<addr>+<size>`; its `map_verdict` / `port_verdict` columns are the old masked compare, superseded by
  `RERUN-cmpkit-4bbd3a74be89.md` and not evidence), summarised in section 1 + appendix A of a working document,
  CORE-PREP.md (sha256 `fc8fd0affb5171c25268ec1bf5e4590e6e5040b1e87f62e4525c66b66cfaad58`, git blob
  `88a9a082dd2093b6c815352e2a0987585d85fab9`; not an input of any verdict, not in the release).
- Every emitted address: fuzz_boxreg.asan's symtab, read from `$PIPELINE_ROOT/unstripped/fuzz_boxreg/fuzz_boxreg.asan`
  (sha256 `4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3`; `PIPELINE_ROOT` is the pipeline's `libreac`
  directory, see Commands)
  with revcheck's `Elf` (`rc.Elf(path).syms`, tuples `(name, type, st_value, st_size)`); only `type == 2` (FUNC) used.
  `tfib_A_x = st_value`, `tfib_E_x = st_value + st_size`.
- Header lines 1-20 (copyright, `From Stdlib Require Import ZArith.`, section/img/entry constants) and the tail
  (`tfib_D_*`, `tfib_at_*`, line 616 `tfib_at_stops_more`) are carried verbatim from the run-9 stage-out file.
  One provenance comment was added as line 5. The section constants were re-checked against the ELF section table
  (`.rodata 0x102e0..0x2268c`, `.init_array 0x98920..0x98940`, `.fini_array 0x98940..0x98950`,
  `.preinit_array 0x98950..0x98958`, `.data.rel.ro 0x98958..0x98e58`, `.got 0x98e58..0x99bb0`,
  `.data 0x9abb0..0x9d770`, `asan_globals 0x9d770..0x9d8b0`, `.bss 0x9d8c0..0x5f57f0`, `.tbss 0x97920..0x97934`):
  all equal. `tfib_text_hi = 0x97920` is `.tbss`'s start, not `.text`'s end `0x9791c`; this is cgif's own convention
  (cgif `.text` ends `0x9c9fc`, cgif `tfib_text_hi = 0x9ca00 = .tbss` start).

## Counts

| | rows |
|---|---|
| cgif AB1w rows | 545 |
| kept (cgif row has a boxreg counterpart) | 518 |
| of these, emitted 1:1 under cgif's row name | 513 |
| of these, merged cgif rows split into 2 boxreg rows each | 5 -> 10 |
| new row (cgif class-1 stack_malloc has no twin; boxreg has class 3 only) | 1 |
| dropped, no counterpart in boxreg | 10 |
| dropped, cgif program functions (0x80490..0x86bcc) | 16 |
| **rows in the regenerated file** | **524** |

Code comparison of the 518 kept rows, re-run on the comparison kits (record: `RERUN-cmpkit-4bbd3a74be89.md` in this
directory; it replaces the `fnstart.tsv` `port_verdict` counts that stood here, a mnemonic + register compare with every
immediate masked, made with capstone by the pairing script itself, not a strict compare): every kept cgif row was
compared by address with its boxreg row as one byte range (a merged row with its two split rows; `start` and
`set_thread_area` over their row ranges). 518 compared, 0 not compared; the count holds compared rows only. On cmpkit
86da41d3ef68 (`strictcmp3`): `EQUAL` 141, `EQUAL-mod-pcrel` 335, `DIFFERENT-target` 42. The 42 rows hold 23 fail-closed
targets in 21 rows, each settled by a named measurement, and 39 `lui-in-section` targets in 23 rows; `strictcmp3` also
accepts 20 `lui` values in 18 rows only by its fail-open `lui-const (dataflow)` label (15 of those rows are outside the
42). All 59 `lui` values are traced in both images: 57 settle and 2 are NOT CERTIFIED: REAL 0 (`InitializeShadowMemory`,
`SizeClassAllocator64_PopulateFreeArray`); 0 REAL words. The 27 cgif rows with no boxreg row (below) are NOT COMPARED;
the record names each one, and each of the 34 rows the old pairing could not compare, with its reason.

Checks run on the generated file: 524 rows parsed; no duplicate row name; no duplicate address range; every row
inside `.text` (`0x2ff58 <= A < E <= 0x97920`); every `A` equals a FUNC `st_value` and every `E` equals
`st_value + st_size` of the same symbol (the two size-0 asm rows excepted, see below); 0 occurrences of
`port_core_refused`. Every 1:1 row has the same byte length as its cgif row (only `target_run` differs, because it
is split). Cross-check against the run-9 stage-out file: the 519 rows that file resolved agree with the
regenerated values, except `target_run` (stage-out `0x7fd7c..0x7ff04` = cgif's merged length; symtab says
`target_run` is `0x7fd7c+0x158`).

## Dropped rows and their users

No other stage-out file names any dropped row. The only `tfib_[AE]_*` names used outside `A/AB1w.v` in
the run-9 stage-out set (not in the repository; see Commands) are five, all kept:

| name | boxreg symbol | A | E |
|---|---|---|---|
| `tfib_A_musl_memchr` | `memchr` | 0x92088 | 0x92154 |
| `tfib_A_musl_memcmp` | `memcmp` | 0x92154 | 0x92184 |
| `tfib_A_musl_memcpy` | `memcpy` | 0x92184 | 0x92588 |
| `tfib_A_musl_memset` | `memset` | 0x92588 | 0x92680 |
| `tfib_A_musl_strnlen` | `strnlen` | 0x92a70 | 0x92ab4 |

(Command: `grep -rhoE 'tfib_[AE]_[A-Za-z0-9_]+' --include=*.v . --exclude=AB1w.v | sort -u` in
the run-9 stage-out set; 19 files, all under `A/`, all five names only.) In the cgif tree the same grep returns the
whole name list, because `lib/YB1w.v` is a second copy of the same table; that file is not in the stage-out set.
No `file:line` list is therefore owed for any dropped row.

Dropped, no counterpart in fuzz_boxreg.asan (10; each line is kept as a comment in the file at the row's place):

| cgif row | cgif range | reason |
|---|---|---|
| `asan_stack_malloc_B` | 0x3ca34+0x19c | class 2; boxreg has only `__asan_stack_malloc_3` |
| `fopen` | 0x41950+0x4 | trampoline; no fopen in boxreg |
| `fclose` | 0x41958+0x4 | trampoline; no fclose in boxreg |
| `icpt_fopen` | 0x462f0+0x46c | no fopen interceptor in boxreg |
| `icpt_fclose` | 0x46868+0x1ac | no fclose interceptor in boxreg (the map lands in `__interceptor_sem_post`, 107 vs 12 insns) |
| `fdopen` | 0x929c4+0x1d8 | musl `__fdopen` not linked |
| `musl_fclose` | 0x92ee4+0xcc | not linked |
| `musl_fopen` | 0x93540+0xdc | not linked |
| `fmodeflags` | 0x9361c+0xb4 | not linked |
| `ofl_add` | 0x93950+0x40 | not linked |

Dropped cgif program functions (16, cgif 0x80490..0x86bcc): `LLVMFuzzerTestOneInput`, `read_frameconfig`,
`cgif_newgif`, `cgif_writecb_or_freeCGIF`, `freeFrame_or_freeCGIF`, `cgif_addframe`, `cmpPixel`, `flushFrame`,
`freeFrame`, `cgif_close`, `cgif_raw_newgif`, `cgif_raw_addframe`, `LZW_GenerateStream`, `cgif_raw_close`,
`create_byte_list`, `create_byte_list_block`. fuzz_boxreg is a different program; the boxreg program lane is
listed below. Note `cgif`'s `main`, `target_alloc_init`, `target_alloc_count`, `target_run`, `emit_printf`,
`asan.module_ctor`, `asan.module_dtor` are harness code, not cgif program code: they pair and are kept.

## Replaced row: stack_malloc

cgif uses `__asan_stack_malloc` classes 1 (0x3c8a4+0x190, 100 insns, `slli a7,a7,7`) and 2 (0x3ca34+0x19c, 103
insns). fuzz_boxreg.asan has only `__asan_stack_malloc_3` 0x3c520+0x1ac (107 insns, `slli 9`), and no other
`__asan_stack_malloc_N` / `__asan_stack_free_N` symbol (CORE-PREP section 1(a)). Both cgif rows are therefore
dropped and one new row is emitted:

```
Definition tfib_A_asan_stack_malloc_3 : Z := 0x3c520.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3c6cc.
```

No `tfib_*_asan_stack_malloc_1` / `_2` row exists in the regenerated file.

## Split rows (merged cgif rows -> one row per boxreg symbol)

Each part gets its own name; no other core file used the merged row's `tfib_E_*` (see "Dropped rows and their
users"), so nothing has to be rewritten.

| cgif merged row (range) | boxreg symbol | new row | A | E |
|---|---|---|---|---|
| `MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser` (0x6e0b8+0x14c) | `_ZN11__sanitizer20ReservedAddressRange3MapEmmPKc` | `ReservedAddressRange_Map` | 0x6db74 | 0x6dbe8 |
| | `_ZN11__sanitizerL23SealedRepairReservationEmm` | `SealedRepairReservation` | 0x6dbe8 | 0x6dcc0 |
| `pthread_key_create_body_tsd_init` (0x99700+0x11c) | `__pthread_rwlock_wrlock` | `pthread_rwlock_wrlock` | 0x94650 | 0x94658 |
| | `__pthread_rwlock_timedwrlock` | `pthread_rwlock_timedwrlock` | 0x94658 | 0x9476c |
| `thunk_417cc` (0x41940+0x8) | `__interceptor_trampoline_strerror` | `thunk_trampoline_strerror` | 0x41440 | 0x41444 |
| | `__interceptor_trampoline__exit` | `thunk_trampoline_exit` | 0x41444 | 0x41448 |
| `thunk_96f9c` (0x998b4+0x8) | `__pthread_testcancel` | `thunk_pthread_testcancel` | 0x94804 | 0x94808 |
| | `__testcancel` | `thunk_testcancel` | 0x94808 | 0x9480c |
| `target_run` (0x802c0+0x188) | `target_run` | `target_run` (name kept) | 0x7fd7c | 0x7fed4 |
| | `oft_exit_guard` | `oft_exit_guard` | 0x7fed4 | 0x7ff04 |

Each pair's two sizes add up to the cgif row's size (e.g. 0x74 + 0xd8 = 0x14c; 0x158 + 0x30 = 0x188), which is the
check that the split is the right one. The `target_run` / `oft_exit_guard` boundary was re-checked here with
elfdis: cgif `--addr 0x80418 0x30` vs boxreg `oft_exit_guard` is 12/12 mnemonic + register equal.
(elfdis is fail-open; on cmpkit 86da41d3ef68 the same ranges are `EQUAL-mod-pcrel` with 0 target differences, by address
and by name: `RERUN-cmpkit-4bbd3a74be89.md`, section "Line 127 (split boundary) and line 228 (16 `j` stubs) ...".)

`InitializeCommonInterceptors` is **not** split: it is a mislabelled, not a merged, row. boxreg's single symbol
`_ZL16ioctl_table_fillv` 0x4825c+0x8cd8 covers it (9014/9014 insns, 4 immediate-only diffs; CORE-PREP appendix A
row 125). cgif's row name is kept, since the row pairs 1:1.

The `start` and `set_thread_area` rows keep cgif's names and come from size-0 asm symbols, so `E` is the next FUNC
boundary, not `st_value + st_size`:
`_start` 0x2ff58, size 0, next FUNC `_start_c` 0x2ff74+0x2c -> `tfib_E_start = 0x2ffa0` ( = `__do_init`'s start,
and 0x48 = cgif's row length, 18/18 insns equal);
`__set_thread_area` 0x9480c, size 0, next FUNC `__unmapself` 0x94818 -> `tfib_E_set_thread_area = 0x94818`
( = 0xc = cgif's row length, 3/3 insns equal).

## boxreg program lane (not in the table)

fuzz_boxreg's own program functions, from the symtab; rows were added for none of them, because no stage-out file
cites them (`A_LLVMF*` names belong to other files). Ranges, for whoever writes the program lane:

| symbol | A | E | size |
|---|---|---|---|
| `main` | 0x7faac | 0x7fd70 | 0x2c4 |
| `target_alloc_init` | 0x7fd70 | 0x7fd74 | 0x4 |
| `target_alloc_count` | 0x7fd74 | 0x7fd7c | 0x8 |
| `target_run` | 0x7fd7c | 0x7fed4 | 0x158 |
| `oft_exit_guard` | 0x7fed4 | 0x7ff04 | 0x30 |
| `emit_printf` | 0x7ff04 | 0x7ff4c | 0x48 |
| `LLVMFuzzerTestOneInput` | 0x7ff4c | 0x80ff0 | 0x10a4 |
| `check` | 0x80ff0 | 0x812b0 | 0x2c0 |
| `read_name` | 0x812b0 | 0x81430 | 0x180 |
| `range_free` | 0x81430 | 0x81524 | 0xf4 |
| `lowest_free` | 0x81524 | 0x815b4 | 0x90 |
| `asan.module_ctor` | 0x815b4 | 0x815ec | 0x38 |
| `asan.module_dtor` | 0x815ec | 0x8161c | 0x30 |
| `reac_boxreg_init` | 0x8161c | 0x816a0 | 0x84 |
| `reac_boxreg_find` | 0x816a0 | 0x817a0 | 0x100 |
| `reac_boxreg_declare` | 0x817a0 | 0x81a54 | 0x2b4 |
| `lowest_free_base` | 0x81a54 | 0x81ba8 | 0x154 |
| `reac_boxreg_add` | 0x81ba8 | 0x81ea4 | 0x2fc |
| `reac_boxreg_set_name` | 0x81ea4 | 0x81f34 | 0x90 |
| `__wrap_getenv` | 0x81f34 | 0x81f3c | 0x8 |
| `__wrap_getpid` | 0x81f3c | 0x81f44 | 0x8 |

`main`, `target_alloc_init`, `target_alloc_count`, `target_run`, `oft_exit_guard`, `emit_printf`,
`asan.module_ctor` and `asan.module_dtor` are already table rows (harness code shared with cgif); the other 13 are
boxreg-only and have no row.

## Commands

Run from the repository root. `PIPELINE_ROOT` is the pipeline's `libreac` directory and `CGIF_ASAN` the cgif image
(sha256 `7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0`); neither has a default. revcheck is
`002698d25b7653ae4f5ef9096c4f8a3da4dac534:frame/revcheck.py` (sha256
`06fc9cefdb2080f7c4c577f572114f544a1c47330d7837661a532a608953653d`); elfdis is
`217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py` (sha256
`ed45f6bea2e54eff8a6fa9bed0bd4fec353f7c6887c0ce3472a53725f41ccab2`), which is fail-open, so the split-boundary spot check
below is superseded by `RERUN-cmpkit-4bbd3a74be89.md` (section "Line 127 (split boundary) and line 228 ...").

```bash
R=${PIPELINE_ROOT:?set PIPELINE_ROOT to the pipeline libreac root (bin/, unstripped/)}
C=${CGIF_ASAN:?set CGIF_ASAN to the cgif_file_fuzzer.asan image}
D=proofs/libreac/fuzz_boxreg/provenance/core-reloc/ab1w
# names any other core file uses: the committed A core
git grep -h -o -E 'tfib_[AE]_[A-Za-z0-9_]+' 0ee62147ab179f61706aebcd20ab24d7c9420360 \
  -- 'proofs/libreac/fuzz_boxreg/lib/A/*.v' ':!*/AB1w.v' | sort -u

# pairing table (by cgif address)
awk -F'\t' 'NR>1' "$D/fnstart.tsv"

# the tools, fetched by commit into a throwaway repository
G=$(mktemp -d); X=$(mktemp -d)
git -C "$G" init -q
git -C "$G" remote add origin "$(git remote get-url origin)"
git -C "$G" fetch --depth=1 --filter=blob:none origin 002698d25b7653ae4f5ef9096c4f8a3da4dac534 \
  217c0af79e0d8be29b6aa5f568b03cfe250712ab
git -C "$G" show 002698d25b7653ae4f5ef9096c4f8a3da4dac534:frame/revcheck.py > "$X/revcheck.py"
git -C "$G" show 217c0af79e0d8be29b6aa5f568b03cfe250712ab:audit-tools/elfdis.py > "$X/elfdis.py"

# boxreg symtab (every emitted value)
python3 - "$X" "$R" <<'PY'
import sys; sys.path.insert(0, sys.argv[1]); import revcheck as rc
e = rc.Elf(sys.argv[2] + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan')
for nm,typ,val,sz in e.syms:
    if typ == 2 and nm: print(nm, hex(val), hex(sz))
PY

# split-boundary spot check (elfdis, fail-open; superseded, see above)
python3 "$X/elfdis.py" "$C" --addr 0x80418 0x30
python3 "$X/elfdis.py" "$R/unstripped/fuzz_boxreg/fuzz_boxreg.asan" oft_exit_guard
```

The names grep over the committed A core (`proofs/libreac/fuzz_boxreg/lib/A`, 659 `.v` files at
`0ee62147ab179f61706aebcd20ab24d7c9420360`) prints the five names `tfib_A_musl_memchr`, `tfib_A_musl_memcmp`,
`tfib_A_musl_memcpy`, `tfib_A_musl_memset`, `tfib_A_musl_strnlen`, used by 25 files; all five rows are kept. The run of
record ran the same grep over the run-9 stage-out set, which is not in the repository (462 `.v` files; their set sha256,
the sha256 of the `sha256sum` output of the files listed by `find . -name '*.v' | LC_ALL=C sort` in the set's root, is
`c5ea51aee5265490d7a8e0f76366a5fdf1d7068ed3f60b9aaa30d6d2bb74233c`; 19 of the 462 files are in no commit): the same five
names, used by 19 files. The re-check before renaming (below) ran over the assembled core of that time, which is not
in the repository either (462 `.v` files, set sha256 `a876704e2b843598120987a1d057b57b8aadd8944df1cdd31e140b6bcce908dd`
computed the same way; 31 of its files are in no commit); the same grep with `--exclude=YB1w.v` over the committed
A core (no `YB1w.v` there) prints the same five names.

## Follow-up: the 37 port_addr_check flags (checker 6fe6a891e21e; the flag list of that run is `../flags/ab1w.tsv`, in this directory tree; not in the release: sha256 `a06731dd1f26b98eb7d493fe35db6ab802d1d3489c8d6b8b27762bbaafe3de2e`, git blob `d5fff3b451479086cbd17d287b63fafd33516907`)

**All 33 code-pointer flags are artifacts of the checker's line pairing, except one that is the intended split.**
The checker pairs cgif's row with mine by LINE. My file is not line-aligned with cgif's: it carries 27 comment
lines where cgif rows were dropped and 5 extra rows from the splits, so from line 96 on it compares cgif's row N
with my row N+k. Every flagged row's own note already carries the right answer ("the target has it at
`<symbol>@<addr>`"), and in all 16 flagged `tfib_A_*` rows that address is exactly what my row holds:

| flagged row (cgif name) | cgif A | checker's "target has it at" | my row (A, E) | verdict |
|---|---|---|---|---|
| `thunk_417cc` | 0x41940 | `__interceptor_trampoline_strerror@0x41440` | 0x41440, 0x41444 (split row) | artifact |
| `thunk_417dc` | 0x41954 | `__interceptor_trampoline_fflush@0x41450` | 0x41450, 0x41454 | artifact |
| `thunk_417e4` | 0x4195c | `__interceptor_trampoline_sem_init@0x41454` | 0x41454, 0x41458 | artifact |
| `thunk_417e8` | 0x41960 | `__interceptor_trampoline_sem_destroy@0x41458` | 0x41458, 0x4145c | artifact |
| `thunk_417ec` | 0x41964 | `__interceptor_trampoline_sem_wait@0x4145c` | 0x4145c, 0x41460 | artifact |
| `thunk_417f0` | 0x41968 | `__interceptor_trampoline_sem_trywait@0x41460` | 0x41460, 0x41464 | artifact |
| `thunk_417f8` | 0x41970 | `__interceptor_trampoline_sem_post@0x41468` | 0x41468, 0x4146c | artifact |
| `thunk_4180c` | 0x41984 | `__interceptor_trampoline_sigaction@0x4147c` | 0x4147c, 0x41480 | artifact |
| `thunk_59674` | 0x59854 | `__asan_set_death_callback@0x59310` | 0x59310, 0x59314 | artifact |
| `thunk_653ec` | 0x655d4 | `__sanitizer::InitializePlatformEarly@0x65090` | 0x65090, 0x65094 | artifact |
| `thunk_66008` | 0x661f0 | `__sanitizer::CloseFile@0x65cac` | 0x65cac, 0x65cb0 | artifact |
| `thunk_6d37c` | 0x6d564 | `__sanitizer::GetThreadSelf@0x6d020` | 0x6d020, 0x6d024 | artifact |
| `thunk_762d8` | 0x765fc | `__sanitizer::SymbolizerProcess::GetEnvP@0x760b8` | 0x760b8, 0x760bc | artifact |
| `thunk_77ab0` | 0x77dd4 | `__sanitizer::InternalSymbolizer::Flush@0x77890` | 0x77890, 0x77894 | artifact |
| `thunk_7b6f8` | 0x7ba28 | `__lsan::DoRecoverableLeakCheckVoid@0x7b4e4` | 0x7b4e4, 0x7b4e8 | artifact |
| `thunk_931e0` | 0x8dd54 | `__lctrans@0x890bc` | 0x890bc, 0x890c0 | artifact |

The 13 `tfib_E_*` flags of the same rows (DIFFERENT-SYMBOL / SLID-TO-NEIGHBOUR) are the same shift one field later;
each end equals its own row's `st_value + st_size`.

Code evidence, independent of the checker (these are all 1-insn `j` stubs, so they pair by jump target; elfdis
`--addr <a> 4` on each image, jump target resolved in boxreg's symtab):
strerror stub -> `__interceptor_strerror`; fflush -> `__interceptor_fflush`; sem_init / sem_destroy / sem_wait /
sem_trywait / sem_post -> the matching `__interceptor_sem_*`; sigaction -> `__interceptor_sigaction`;
`__asan_set_death_callback` -> `__sanitizer::SetUserDieCallback`; `InitializePlatformEarly` -> `InitTlsSize`;
`CloseFile` -> `internal_close`; `GetThreadSelf` -> `pthread_self`; `SymbolizerProcess::GetEnvP` -> `GetEnviron`.
Each is the callee the donor row's trampoline has. The last three (`InternalSymbolizer::Flush`, 
`DoRecoverableLeakCheckVoid`, `__lctrans`) disassemble to the same 1-insn stub in both images (`j .` / `j .+4`);
they are in the 19 identical-stub tiebreaks resolve_code reports, and the code is byte-identical.
(elfdis is fail-open; on cmpkit 86da41d3ef68 all 16 stubs are `EQUAL` / `EQUAL-mod-pcrel` with 0 target differences,
by address and by name, each with the same jump target: `RERUN-cmpkit-4bbd3a74be89.md`, section "Line 127 (split
boundary) and line 228 (16 `j` stubs) ...".)

The remaining 4 flags:

| flag | verdict |
|---|---|
| `tfib_E_target_run` 0x80448 -> 0x7fed4, DIFFERENT-SYMBOL, "expected 0x7ff04" | **by design, no fix.** cgif's row is merged; 0x7ff04 is where `oft_exit_guard` ends. The split gives `target_run` 0x7fd7c..0x7fed4 and `oft_exit_guard` 0x7fed4..0x7ff04, both from the symtab. |
| `tfib_rodata_hi` UNRESOLVED | no fix. Source side is unnamed in cgif; my value 0x2268c is `.rodata`'s end in boxreg's section table. |
| `tfib_E_HaveStackTraceBasedSuppressions` UNRESOLVED | no fix. Source side unnamed; 0x5aecc = `__asan::HaveStackTraceBasedSuppressions`'s `st_value + st_size`, and the checker itself resolves it to `__asan::IsODRViolationSuppressed+0x0`. |
| `tfib_E_set_thread_area` UNRESOLVED (both sides unnamed) | no fix. `__set_thread_area` is a size-0 asm symbol; 0x94818 is the next FUNC (`__unmapself`), and the length 0xc equals cgif's row (3/3 insns equal). |
| `tfib_at_ph_addr_z` UNRESOLVED, "value unchanged (a copied literal?)" | no fix. 0x10040 is `img_lo + e_phoff` (0x10000 + 0x40) in **both** images, so the literal is right, not stale. |

### Names fixed (23 rows)

Applied rule: where the row's cgif label names something other than its code, the row takes boxreg's own symbol.
No other core file uses these names (only the five `musl_*` rows are cited elsewhere), so nothing else changes.
Addresses were not touched by the rename; the file still has 524 rows and the same 524 address pairs.

- The 21 `thunk_<hex>` rows: those labels are cgif addresses that match nothing (`thunk_417cc`'s row is at cgif
  0x41940, not 0x417cc), so each is now named after boxreg's symbol:
  `interceptor_trampoline_snprintf` 0x41430, `interceptor_trampoline_strerror` 0x41440,
  `interceptor_trampoline__exit` 0x41444, `interceptor_trampoline_fflush` 0x41450,
  `interceptor_trampoline_sem_init` 0x41454, `interceptor_trampoline_sem_destroy` 0x41458,
  `interceptor_trampoline_sem_wait` 0x4145c, `interceptor_trampoline_sem_trywait` 0x41460,
  `interceptor_trampoline_sem_post` 0x41468, `interceptor_trampoline_sigaction` 0x4147c,
  `asan_set_death_callback` 0x59310, `InitializePlatformEarly` 0x65090, `CloseFile` 0x65cac,
  `GetThreadSelf` 0x6d020, `SymbolizerProcess_GetEnvP` 0x760b8, `InternalSymbolizer_Flush` 0x77890,
  `DoRecoverableLeakCheckVoid` 0x7b4e4, `lctrans` 0x890bc, `bcmp` 0x92084, `pthread_testcancel` 0x94804,
  `testcancel` 0x94808. (`thunk_417bc` 0x41430 and `thunk_95368` 0x92084 were not flagged -- the line shift hid
  them -- but they are the same defect, so they are fixed too; the four names from the two split thunk rows are
  normalised to the same form.)
- The swapped pair: cgif's `AsanCheckIncompatibleRT` sits on boxreg's `_ZN6__asan25AsanCheckDynamicRTPrereqsEv`
  0x5227c+0x4 and cgif's `AsanCheckDynamicRTPrereqs` on `_ZN6__asan23AsanCheckIncompatibleRTEv` 0x52280+0x168:
  the two labels are interchanged in cgif. The rows keep their addresses and swap names, so each row now carries
  boxreg's symbol.

### Second pass: 45 more rows renamed to boxreg's symbol (the stream lead, 2026-10-28)

The same defect class covered 49 further rows (the ASan contract owner's survey: "about 100 wrong AB1w labels per image"): the address is
right (code-verified by the pairing table) but the cgif label names a different function. Four of them were false
positives of the survey test ("no token of length >= 4 of the row name occurs in the symbol"): `Die`
(`__sanitizer::Die`), `pop_arg`, `pad`, `fmt_fp` all carry boxreg's own name already and were left alone. The
other 45 now take boxreg's symbol, sanitized the same way (leading underscores and the `__sanitizer` / `__asan` /
`__lsan` namespace dropped, `::` -> `_`, template argument kept only where two rows would otherwise collide).
Addresses were not touched.

Before renaming, every old name was re-checked against the assembled core in
its working directory of that time (not in the repository; 462 .v files, set sha256 `a876704e2b843598120987a1d057b57b8aadd8944df1cdd31e140b6bcce908dd`; see Commands):
`grep -rhoE 'tfib_[AE]_[A-Za-z0-9_]+' --include=*.v . --exclude=AB1w.v --exclude=YB1w.v | sort -u` returns only
`tfib_A_musl_memchr`, `musl_memcmp`, `musl_memcpy`, `musl_memset`, `musl_strnlen`. None of the 45 is cited, so no
other file changes; the five `musl_*` rows keep their names.

| old row name (cgif label) | A | E | boxreg symbol at A | new row name |
|---|---|---|---|---|
| `QuarantineCache_MergeBatches_Transfer` | 0x32d48 | 0x32f2c | `_ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_` | `Quarantine_Recycle` |
| `Allocator_ComputeRZLog` | 0x364f8 | 0x36610 | `_ZN6__asanL10RZSize2LogEj` | `RZSize2Log` |
| `FakeStack_SetShadow` | 0x3c6cc | 0x3c808 | `_ZN6__asanL11MemToShadowEm` | `MemToShadow_3c6cc` |
| `memcmp_2` | 0x41404 | 0x41408 | `__wrap_bcmp` | `interceptor_trampoline_bcmp` |
| `vfprintf_2` | 0x4142c | 0x41430 | `__wrap_fprintf` | `interceptor_trampoline_fprintf` |
| `icpt_vfprintf_2` | 0x451e8 | 0x452c0 | `__interceptor_fprintf` | `interceptor_fprintf` |
| `icpt_diouxXn` | 0x47518 | 0x476b0 | `_ZL21format_get_value_sizecPKcb` | `format_get_value_size` |
| `InitializeCommonInterceptors` | 0x4825c | 0x50f34 | `_ZL16ioctl_table_fillv` | `ioctl_table_fill` |
| `InitializeSignalInterceptors_or_syscall_hooks` | 0x50f34 | 0x51090 | `_ZN11__sanitizer4SortI10ioctl_desc18ioctl_desc_compareEEvPT_mT0_` | `Sort_ioctl_desc` |
| `icpt_cfree_or_DlsymFree` | 0x5271c | 0x527e8 | `_ZN11__sanitizer14DlSymAllocatorI10DlsymAllocE8AllocateEmm` | `DlSymAllocator_Allocate` |
| `DlsymAlloc_PointerIsMine_internal_allocator_From` | 0x527ec | 0x528ec | `_ZNK11__sanitizer11TwoLevelMapIhLy32768ELy4096ENS_21LocalAddressSpaceViewEE6CreateEm` | `TwoLevelMap_u8_Create` |
| `ScopedInErrorReport_ReportError_helper` | 0x54cd0 | 0x54edc | `_ZN6__asan18ReportDeadlySignalERKN11__sanitizer13SignalContextE` | `ReportDeadlySignal` |
| `IsStackTraceSuppressed` | 0x5af34 | 0x5b080 | `_ZN6__asan16IsAddrSuppressedEPKcPN11__sanitizer10SymbolizerEm` | `IsAddrSuppressed` |
| `weak_default_hook_ret` | 0x5d484 | 0x5d488 | `_ZN11__sanitizer17ThreadContextBase9OnStartedEPv` | `ThreadContextBase_OnStarted` |
| `InternalAlloc_RawInternalAlloc` | 0x5d490 | 0x5d6d0 | `_ZN6__asanL20GetAsanThreadContextEj` | `GetAsanThreadContext` |
| `InternalFree_LowLevelAllocator_free_to_freelist` | 0x5d924 | 0x5da7c | `_ZN11__sanitizer18internal_allocatorEv` | `internal_allocator` |
| `AllocatorMayReturnNull` | 0x5de60 | 0x5de70 | `_ZN11__sanitizer18IsRssLimitExceededEv` | `IsRssLimitExceeded` |
| `IncreaseTotalMmap` | 0x5fb4c | 0x5fb70 | `_ZN11__sanitizer17DecreaseTotalMmapEm` | `DecreaseTotalMmap` |
| `ReportFile_SetReportPath` | 0x60d7c | 0x60ec0 | `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | `CommonFlags_SetDefaults` |
| `FlagParser_PrintFlagDescriptions_gate_Verbosity` | 0x624b4 | 0x624d8 | `_ZN11__sanitizer21InitializeCommonFlagsEPNS_11CommonFlagsE` | `InitializeCommonFlags` |
| `GetNamedMappingFd_ReadProcess_openat_getdents64` | 0x644d0 | 0x648cc | `_ZN11__sanitizer12ThreadLister11ListThreadsEPNS_18InternalMmapVectorIyEE` | `ThreadLister_ListThreads` |
| `GetPageSizeCached` | 0x64b50 | 0x64b58 | `_ZN11__sanitizer11GetPageSizeEv` | `GetPageSize` |
| `internal_sigaction_syscall_wrapper_selector` | 0x64e6c | 0x64ec8 | `_ZN11__sanitizer19GetHandleSignalModeEi` | `GetHandleSignalMode` |
| `internal_errno_mapping_helper` | 0x652e8 | 0x652f4 | `_ZN11__sanitizer10ErrorIsOOMEi` | `ErrorIsOOM` |
| `MmapFixedNoAccess_3_insn_arg_shim_0x65c98` | 0x65930 | 0x6593c | `_ZN11__sanitizer14MmapFixedOrDieEmmPKc` | `MmapFixedOrDie` |
| `InternalAllocatorLock_Unlock_or_stats_add_17_ins` | 0x69558 | 0x6959c | `_ZN11__sanitizer17ThreadContextBaseC2Ej` | `ThreadContextBase_ctor` |
| `weak_default_hook_ret_2` | 0x6c020 | 0x6c024 | `_ZN11__sanitizer11InitTlsSizeEv` | `InitTlsSize` |
| `GetThreadStackAndTls` | 0x6c024 | 0x6c414 | `_ZN11__sanitizerL6GetTlsEPmS0_` | `GetTls` |
| `GetThreadStackTopAndBottom_caller_ClearShadowFor` | 0x6c414 | 0x6c4e4 | `_ZN11__sanitizer20GetThreadStackAndTlsEbPmS0_S0_S0_` | `GetThreadStackAndTls` |
| `weak_default_hook_ret_3` | 0x6cb90 | 0x6cb94 | `_ZN11__sanitizer29InitializePlatformCommonFlagsEPNS_11CommonFlagsE` | `InitializePlatformCommonFlags` |
| `InternalMmapVector_push_back` | 0x6cb94 | 0x6cca0 | `_ZN11__sanitizerL22CollectStaticTlsBlocksEP12dl_phdr_infomPv` | `CollectStaticTlsBlocks` |
| `internal_pthread_weak_stub_ret` | 0x6d1d4 | 0x6d1d8 | `_ZN11__sanitizer6AtexitEPFvvE` | `Atexit` |
| `MmapFixedNoReserve` | 0x6da14 | 0x6da74 | `_ZN11__sanitizer23MmapFixedSuperNoReserveEmmPKc` | `MmapFixedSuperNoReserve` |
| `MprotectNoAccess` | 0x6db54 | 0x6db74 | `_ZN11__sanitizer12MmapNoAccessEm` | `MmapNoAccess` |
| `MmapFixedOrDie` | 0x6dcc0 | 0x6dcd0 | `_ZN11__sanitizer20ReservedAddressRange8MapOrDieEmmPKc` | `ReservedAddressRange_MapOrDie` |
| `MaybeStartBackgroudThread` | 0x6f4c8 | 0x6f50c | `_ZN11__sanitizer18InitializeCoverageEbPKc` | `InitializeCoverage` |
| `Atexit_internal_exit_hook_runner_12_insns_execut` | 0x6f50c | 0x6f53c | `__sanitizer_cov_dump` | `sanitizer_cov_dump` |
| `StackDepotBase_Get` | 0x72210 | 0x72320 | `_ZN11__sanitizer13StackDepotGetEj` | `StackDepotGet` |
| `StackDepotBase_lock_bucket_spin_lock` | 0x72790 | 0x72890 | `_ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm` | `TwoLevelMap_StackDepotNode_Create` |
| `asan_malloc_hook_RunMallocHooks_target_sanitizer` | 0x7f46c | 0x7f484 | `_ZN6__lsan20DisabledInThisThreadEv` | `DisabledInThisThread` |
| `fini_stub_ret` | 0x88850 | 0x88854 | `__cxa_finalize` | `cxa_finalize` |
| `libc_exit_fini_array_walker_stub` | 0x88918 | 0x8891c | `call` | `call` |
| `musl_exit_helper_stub` | 0x8891c | 0x88920 | `dummy` | `fini` |
| `fprintf` | 0x8e00c | 0x8e070 | `dprintf` | `dprintf` |
| `syscall_cp_c_tail_sccp_9_insns` | 0x92dd8 | 0x92dfc | `__tls_get_addr` | `tls_get_addr` |

Two names needed a disambiguator, because the symbol occurs more than once:
`MemToShadow_3c6cc` (boxreg has five `__asan::MemToShadow` instances; the other three rows already carried
distinct `MemToShadow_*` labels and are unchanged), and `TwoLevelMap_u8_Create` / `TwoLevelMap_StackDepotNode_Create`
(`TwoLevelMap<u8,32768,4096>::Create` at 0x527ec and `TwoLevelMap<StackDepotNode,32768,65536>::Create` at 0x72790).
Three renames are order-dependent and land where an old label used to sit: `MmapFixedOrDie` now means 0x65930
(the old `MmapFixedOrDie` row, 0x6dcc0, became `ReservedAddressRange_MapOrDie`), and `GetThreadStackAndTls` now
means 0x6c414 (the old row of that name, 0x6c024, became `GetTls`).

After this pass: 628 lines, 524 rows, 524 distinct names, 0 `port_core_refused`, every `A` = a FUNC `st_value` and
every `E` = `st_value + st_size` of the same symbol (the two size-0 asm rows excepted), and the set of 524 address
pairs is unchanged from the first pass.

Nothing was committed, pushed or built.
