# gen-states: the generated files of the port_core check, plugin-hostd/fuzz_command

Scope: every row that the value gate port_addr_check 3d2eee813cce flags in eight generated files. The runs are RA
(the donor's lib/A to our lib/A, image key A) and RB (the donor's root Y files to our lib/B, key B). The files are
lib/A/AB01.v, AB03.v, AB1w.v, ACej.v and their B twins lib/B/YB01.v, YB03.v, YB1w.v, YCej.v. The input rows are the
rows that the first mechanical triage routed to its generated-file tables.

Result: 18,295 flagged rows. 18,295 are OK, 0 are OPEN, and there is 0 FINDING. No STOP-rule event.

| file | rows | gate verdicts | reasons (triage-rows.tsv column `reason`) |
|---|---|---|---|
| lib/A/AB01.v | 7,384 | UNPAIRED-PORTED 5,864, NON-ADDRESS-CHANGED 1,272, DIFFERENT-SYMBOL 173, KIND-CHANGED 27, UNPAIRED-SOURCE 22, GEOMETRY-CHANGED 16, UNRESOLVED 8, IMAGE-EXTENT-CHANGED 1, SLID-TO-NEIGHBOUR 1 | GEN-SEVERAL-ROLES 4,206; GEN-EVAR-FRESH 1,068; GEN-SHADOW-GLOBALS 646; GEN-REL-MAP 420; GEN-SEG-BOUND 402; GEN-VAL-DATA 184; GEN-KIMG-HULL 101; GEN-TOTSZ / ABYTES / EAGER / NEXT-FRESH 50 each; GEN-LEN 33; NO-PORTED-VALUE 22; GEN-DONOR-SAME-RANGE 19; GEN-VAL-OUTSIDE 13; GEN-ADDR-IMG-RW 10; GEN-SCALE 10; GEN-DONOR-SAME-RELCELL 9; GEN-DONOR-SAME-CELL 8; GEN-VAL-SMALL 7; GEN-BASE-LIT 6; GEN-MASK 5; GEN-WIDTH 5; GEN-REL-SHADOWMAP 3; GEN-DONOR-SAME-STRING / -VALUE, GEN-RANGE-BOUND 2 each; GEN-RANGE-IMGTOP 1 |
| lib/A/AB03.v | 53 | DIFFERENT-SYMBOL 34, KIND-CHANGED 10, NON-ADDRESS-CHANGED 7, UNPAIRED-SOURCE 2 | GEN-SEVERAL-ROLES 19; GEN-KIMG-HULL 16; GEN-LEN 9; GEN-DONOR-SAME-STRING 2; GEN-RANGE-BOUND 2; NO-PORTED-VALUE 2; GEN-TOTSZ / ABYTES / RANGE-IMGTOP 1 each |
| lib/A/AB1w.v | 97 | UNPAIRED-SOURCE 66, UNPAIRED-PORTED 24, DIFFERENT-SYMBOL 2, STALE-DONOR-CODE-POINTER 2, UNRESOLVED 2, KIND-CHANGED 1 | DONOR-ROW-DROPPED 52; ROW-FUNC 28; DONOR-ROW-RENAMED 14; SECTION 2; PHDR 1 |
| lib/A/ACej.v | 1,595 | UNPAIRED-SOURCE 1,595 | DONOR-TRACE-NOT-PORTED 1,595 |
| lib/B/YB01.v | 7,366 | UNPAIRED-PORTED 5,864, NON-ADDRESS-CHANGED 1,272, DIFFERENT-SYMBOL 174, UNPAIRED-SOURCE 22, GEOMETRY-CHANGED 16, KIND-CHANGED 8, UNRESOLVED 8, IMAGE-EXTENT-CHANGED 1, SLID-TO-NEIGHBOUR 1 | as AB01; GEN-SHADOW-GLOBALS 647, GEN-LEN 13, GEN-DONOR-SAME-CELL 9 |
| lib/B/YB03.v | 43 | DIFFERENT-SYMBOL 33, NON-ADDRESS-CHANGED 7, UNPAIRED-SOURCE 2, KIND-CHANGED 1 | GEN-SEVERAL-ROLES 19; GEN-KIMG-HULL 15; GEN-DONOR-SAME-STRING 2; GEN-RANGE-BOUND 2; NO-PORTED-VALUE 2; GEN-TOTSZ / ABYTES / RANGE-IMGTOP 1 each |
| lib/B/YB1w.v | 93 | UNPAIRED-SOURCE 64, UNPAIRED-PORTED 24, DIFFERENT-SYMBOL 2, STALE-DONOR-CODE-POINTER 2, UNRESOLVED 1 | DONOR-ROW-DROPPED 50; ROW-FUNC 28; DONOR-ROW-RENAMED 14; PHDR 1 |
| lib/B/YCej.v | 1,664 | UNPAIRED-SOURCE 1,664 | DONOR-TRACE-NOT-PORTED 1,664 |

The gate pairs each generated file with the donor's text by position. A generated state of our image and the donor's
state of the donor image share no positions, so these verdicts are pairing artefacts. Each row is therefore settled by
what our own numeral measures in our own image. The donor's file is used only by name (the same symbol, section or
cell in the donor's own image), never by a numeric delta.

## Images and tools

| role | pin (sha256 12) | twin |
|---|---|---|
| ours A, fuzz_command.asan | c0661b96b5bd | 68db792d5fa7 |
| ours B, fuzz_command.asan-ubsan | bbe55d24d096 | 658cefbe806b |
| donor A, cgif_file_fuzzer.asan | 7093581aab04 | 488e39500746 |
| donor B, cgif_file_fuzzer.asan-ubsan | 1c29845fe605 | ce511d541cda |

Bytes and headers are read from the pin. Only the symbol table is read from the twin. Each script stops when the
PT_LOAD headers of the pin and the twin differ (they do not).

Tools: pyelftools 0.33; rvelf.py, sha256 23152d9ca11cb6287ab13e27265103520e7fb9c3816093c893f68a23f5c7dd5b, a vendored
stdlib ELF64 reader and RV64GC decoder (linear decode of .text); the scripts import it from the directory given as
`--kit` (`kit/` beside them in the runs); that copy is not shipped in this slice, its internal record entry is in
`../internal-texts.md`. The unit's gen_traces.py 59966c883510 with resolve_code.py 503295fdfa6c. Scripts as run
(sha256 12): imgfacts.py 8da4ed9d6a3e, vterm.py 9347a5b0c938, rule_states.py 111879f542dc, rule_ab1w.py a51bb156d6cc,
rule_acej.py 1dbc1347a7ec, merge.py 8645fea284ba, run_states.sh e01689494825, run_light.sh 2d31312b17c0; the shipped
imgfacts.py and run_light.sh differ from those copies only in comment and docstring text (`../internal-texts.md`).

## What was run

ROOT is the check's input directory: tree/cmd (ours, series head plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record)), tree/cgif (the donor, c8557374ad2e),
img/ (the images above) and triage/ (the gate's generated-file rows).

```
sh run_states.sh ROOT states                    # AB01 AB03 YB01 YB03 in parallel; minutes (heavy: run on a build VM)
sh run_light.sh ROOT gen_traces.py light        # gen_traces on both images, ACej YCej AB1w YB1w; seconds
python3 merge.py --gen ROOT/triage/RA.gen.tsv ROOT/triage/RB.gen.tsv --states states --light light \
    --out-rows triage-rows.tsv --out-ctl controls.tsv
```

merge.py checks that every flagged row appears once, in input order, with its 16 input columns unchanged. It also
checks that no table text names a host path.

## The rules, per file

### Start-up states: A/AB01.v, A/AB03.v, B/YB01.v, B/YB03.v (rule_states.py)

vterm.py parses each file into the constructors of Reusable/YK0c.v and YK09.v. It gives EVERY numeral its role:
s_pc, s_next, an EVar index, a register value, a cell address (`a_off`), a KWord width or value, a KImg / KRange bound,
a `seg` index, an map base or length, a total. The kn lists are evaluated (`seg L i n` = firstn n (skipn i L)), and
each numeral is judged in every state that contains it. The rules (full text in the script's header):

- Exact, whole-state: TOTSZ (a_totsz = image hull size + sum(am_len) + sum(ghost lengths)), ABYTES and EAGER (each
  value minus its image-dependent part equals the residue of the donor's same-index state, computed from the donor
  image), NEXT-FRESH (s_next = 1 + the largest EVar of the state), PC-INSN plus DONOR-SAME-SYM on s_pc (A: all 50
  hand-off pcs are main+0 = 0x86044; B 0x86090; AB03/YB03: LowLevelAllocator::Allocate+0xb8, the same symbol + offset
  as the donor's).
- Shadow content: SHADOW-GLOBALS. Every absolute KFill / KZero / KWord in the shadow of the image hull holds exactly the
  bytes that the registration of the image's globals writes. The measure is the 180 `__asan_global` descriptors of the
  pin's asan_globals section: 0xf9 on the redzone granules, size % 8 on a partial last granule, 0xf9 on the descriptor
  array itself, and 0 elsewhere. The donor's released A/AB01.v fills its own asan_globals section the same way. The
  shadow offset is the value that the file stores at the twin's __asan_shadow_memory_dynamic_address (0x7fff8000).
  The rule is applied in the hand-off states (s_pc = main) only. The join state of AB03 is earlier than the
  registration of the globals.
- Name-keyed against the donor's same-index state: DONOR-SAME-SYM / -SECOFF / -STRING / -VALUE (registers and KWord
  values; `-SECOFF` also needs the same 8 bytes), DONOR-SAME-CELL (an absolute cell at the same symbol + offset, also
  for the address a shadow cell covers), DONOR-SAME-RELCELL (the same symbolic base and offset), DONOR-SAME-RANGE /
  RANGE-IMGTOP (a KRange bound equals the donor's bound for the same expression, or differs from it only by the two
  top pages: our 1542 = 0x606000 / 4096 against the donor's 1531).
- Image geometry: KIMG-HULL (a KImg range lies in the hull, and each bound is a PT_LOAD, section or symbol bound,
  the end / start of an absolute write of the same state, or the donor's KImg bound at the same symbol + offset),
  RANGE-BOUND (the same for absolute KWr / KZero / KFill ranges), ADDR-IMG-RW (an absolute cell lies in one writable
  PT_LOAD), ADDR-SHADOW, ADDR-LITMAP, ADDR-HULL, VIS-HULL (the a_vis entry (0x10000, 0x5f6000) is the hull),
  MAP-PAGE, YLO.
- Mappings and stack: REL-MAP / REL-SHADOWMAP (an offset lies within the length of the state's map / ghost / vis /
  brk region with that base, or within its shadow), REL-STACK / REL-STACKSHADOW (within 8 MiB + 64 KiB of the entry
  sp, or its shadow).
- Structure: SEG-BOUND (a `seg` piece lies inside the evaluated list and between its neighbouring pieces),
  EVAR-FRESH, WIDTH (1..8), SCALE (a power of two below the image base), MASK, LEN, RANGE, BYTE, EXT, BLOB.
- Descriptive (what a literal is in our image): VAL-SMALL, VAL-NEG, VAL-OUTSIDE, VAL-SHADOW, VAL-LITMAP, VAL-HULL,
  VAL-DATA, VAL-CODE (VAL-CODE fails a .text value that is not an instruction start in a FUNC symbol).

All 52,722 numerals of the four files pass their rules, not only the flagged ones: AB01 and YB01 have 23,477 each,
AB03 and YB03 have 2,884 each. The per-numeral table is states/<file>.nums.tsv.gz.

A row is matched to the numerals at its (dst_line, |dst_value|). The gate prints a negative numeral without its sign.
On the long kn and acs lines one value fills several roles. The reason is then GEN-SEVERAL-ROLES, and the
measurement lists the roles; each occurrence holds its rule. Rows with an empty dst_value (UNPAIRED-SOURCE) are
NO-PORTED-VALUE: the file holds no numeral there.

### Function-row table: A/AB1w.v, B/YB1w.v (rule_ab1w.py)

- ROW-FUNC: tfib_A_X / tfib_E_X are the st_value and st_value + st_size of one FUNC symbol of the twin. The label is
  checked as a run of the symbol name. This settles the 24 rows the port added (__asan_stack_malloc_0/_3/_4/_5/_7,
  IsAddrSuppressed, IsRssLimitExceeded, DecreaseTotalMmap, GetTls, MmapFixedSuperNoReserve, MmapNoAccess,
  ReservedAddressRange::MapOrDie). It also settles the internal_strcmp / internal_strncmp rows, where the donor's
  labels name another function.
- DONOR-ROW-DROPPED / DONOR-ROW-RENAMED: a donor row with no ported value is resolved in the donor image. The 52 (A) /
  50 (B) dropped rows name a FUNC that our twin does not have: cgif's program, fopen/fclose, __asan_stack_malloc_2.
  For each of the 14 renamed rows, our twin has the FUNC that the donor value points at, and our row of the right name
  covers it (rule ROW-FUNC).
- SECTION, PHDR: tfib_rodata_hi 0x246a4 and tfib_text_hi 0xa46fc are the .rodata and .text sh_addr + sh_size of the A
  pin. tfib_at_ph_addr_z 0x10040 is PT_PHDR p_vaddr.
- Every other definition also passes (light/*.defs.tsv: 1,126 definitions + 12 stops_more entries per file). The rules
  are SECTION, HULL, ENTRY, GP, PHDR (e_phnum 11, e_phentsize 56), NLOAD (4 PT_LOADs), RW-PAGES (the last writable
  PT_LOAD page-rounded: A 0xa8000 + 0x55e000, B 0xa7000 + 0x55f000), SHADOW-OFF, GOT-WORD (the 8 pin bytes of each
  tfib_D_GOT_X hold the address of X), DATA-SYM, INSN-IN, and, for the 7 rows (14 definitions) that span several
  functions or start at a symbol of size 0 and for 7 other definitions, ROW-DONOR-COVER / DONOR-SAME-* (the same FUNC names at the same offsets, or the same
  symbol, GOT target, string or section offset, as the donor's row of that name in the donor image).

### Trace universe: A/ACej.v, B/YCej.v (rule_acej.py)

gen_traces.py was run again on each pinned image and its twin. The `--ipc` values are measured: they are the return
address of the second GetCurrentPc call in ___interceptor_malloc / ___interceptor_free (the Unwind branch of
GET_STACK_TRACE_MALLOC). This gives A 0x58c20 / 0x58ac0 and B 0x58c6c / 0x58b0c. The donor's file uses the same call
(0x52bcc / 0x52a6c). Checks, all OK:
- IPC: the two singletons of Tfib_universe are those return addresses.
- TRACES-GEN: TRACES_main (4 traces) and TRACES_target_run (2 traces) are equal to gen_traces' lists.
- NO-FP: main and target_run never set s0 from sp, so each trace ends after the call site.
- UNIVERSE: Tfib_universe is the prefix closure of the 6 kept traces (8 traces).

All 3,259 flagged rows are donor numerals with no ported value (DONOR-TRACE-NOT-PORTED). Each row names the donor FUNC
+ offset and what our image has for that function.

## Known-answer controls (controls.tsv)

Each judged numeral of a flagged row is judged again with value + 4, and with the donor's value (the row's
src_value). The table counts how many of those values each rule refuses (level `numeral`). A row-level summary is also
given (`row`: refused / refused-some / accepted / descriptive / n/a). Totals over the eight files:

| rule | + 4 refused / judged | donor value refused / judged |
|---|---|---|
| TOTSZ, ABYTES, EAGER, NEXT-FRESH | 404 / 404 | 404 / 404 |
| DONOR-SAME-SYM / -STRING / -VALUE | 348 / 348 | 394 / 394 |
| DONOR-SAME-CELL / -RELCELL | 1,651 / 1,693 | 250 / 250 |
| DONOR-SAME-RANGE / RANGE-IMGTOP | 108 / 108 | 130 / 134 |
| MAP-PAGE, REL-SHADOWMAP, ADDR-HULL | 1,982 / 1,982 | - |
| SCALE | 7,072 / 7,140 | 154 / 308 |
| KIMG-HULL | 397 / 443 | 434 / 435 |
| SHADOW-GLOBALS | 1,915 / 2,238 | 1,160 / 1,338 |
| SEG-BOUND | 708 / 804 | 508 / 716 |
| RANGE-BOUND | 547 / 1,286 | 645 / 982 |
| ROW-FUNC, SECTION, PHDR (AB1w, YB1w) | 60 / 60 | 10 / 10 |
| ACej / YCej file checks (14 numerals each) | 28 / 28 | 28 / 28 |
| EVAR-FRESH | 400 / 5,520 | 186 / 2,248 |
| REL-MAP | 736 / 2,104 | 26 / 60 |
| ADDR-IMG-RW, ADDR-SHADOW, REL-STACK(SHADOW) | 4 / 1,342 | 8 / 242 |

The rules in the upper rows discriminate. EVAR-FRESH, REL-MAP, ADDR-*, REL-STACK and the descriptive VAL-* rules do
not discriminate, and this is expected. They settle numerals by role: the index of a symbolic variable, an offset
inside a symbolic mapping, a cell inside a writable segment, or a non-address constant. Such a numeral holds no image
address, so the defect classes of this check (a .got cell on the wrong word, an address-like model constant that
moved, a kept donor image-derived count) cannot occur in it. The image-derived quantities of these states (sizes,
totals, the top page, the shadow bytes, the registers, the cells at named places) are held by the rules that
discriminate.
In AB01 / YB01, 1,860 / 1,861 rows are still accepted under + 4. Each such row is settled only by a role rule of
that kind.

## Supporting evidence, cited (the results above do not depend on it)

- The bodies (line 4 to the end) of our AB01, AB03, YB01 and YB03 are byte-equal to the start-up collector's gate
  snapshot (snapshot sha256 of AB01 bd63ca75b817 and of YB01 e16c712bf87f, as its SHA256SUMS lists). Only the
  provenance comment of line 3 differs.
- The collector's state check over all 50 hand-off states, A and B: 0 failing rows (both result tables hold only their
  header).
- ifchk bc48411567d7 / f5cde600cc18 over AB01 / YB01 with AF0m: 5,015 cells x 50 states, 0 different, 0 undetermined,
  A and B. Two later independent audits repeat 250,750 / 0 / 0.
- kimg_overlap acfd7418176d sweep: lib/A/AB01.v (sha256 bd63ca75b817; internal record; the same body) PASS, with 144 rows, 50 states,
  0 stale-cgif, 0 contradicting, 0 aliases and 0 duplicates; lib/A/AB03.v (sha256 10c88da39e5a; internal record) PASS. Our files
  (plugin-hostd/fuzz_command lib/A/AB01.v (file sha256 b1fb12113419; released), plugin-hostd/fuzz_command lib/A/AB03.v (file sha256 05b30df44ce5; released)) differ only in the line-3 comment.

## Observations (no FINDING)

1. tfib_text_hi (A/AB1w.v:9) and tfib_rodata_hi (:8). Ours are the section ends of the A pin. The donor's own values
   follow no single rule. Donor B's YB1w gives .rodata end 0x2278c and .text end 0x9cc70 (= its .tbss start). Donor
   A's AB1w gives rodata_hi 0x2278c, which is donor B's .rodata end, not donor A's (0x227cc). It gives text_hi
   0x9ca00, which is donor A's .tbss start and not its .text end 0x9c9fc. Under a ".tbss start" reading, our A value
   would be 0xa4700 instead of 0xa46fc. No statement or definition in lib/ other than the two definitions names either
   identifier (by-use grep), so no proof reads them. They are recorded here and do not change any claim.
2. ACej / YCej keep only the traces of main and target_run. gen_traces finds 39 traces from 20 calling functions in A
   and 35 traces from 19 functions in B (light/*.check.tsv lists them). The file's own header gives the reason (the
   trace store admits every other trace against an allocator event, C5). This is a design choice of the proof, not a
   numeral defect.
3. YCej.v:4 repeats the ASan build's call sites (0x86094 ..., 0x58c20 / 0x58ac0). The line says that they are the
   ASan build's. Line 5 records the move to the ASan+UBSan build. The text is accurate.

## Files

- triage-rows.tsv: one row per flagged row, the 16 input columns + reason, measurement, result, finding_kind,
  new_value, read_by.
- controls.tsv: the known-answer controls (see above).
- states/: per state file the triage rows, the numeral table (.nums.tsv.gz), the per-row (.ctl) and per-rule
  (.ctlrules) controls and the run summary.
- light/: the AB1w / YB1w definition checks, the ACej / YCej file checks, the controls, and gen_traces' output on our
  two images.
- The part's work directory also held working material (earlier runs, copies of working notes). It is not part of the record.
