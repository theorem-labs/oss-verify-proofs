# APPROVE — 0 rejected rows, 3 doubtful rows

Reviewed: `proofs/libreac/fuzz_decode/provenance/alloc-reloc/B/fncmp-cmpkit-86da41d3ef68/` (RECORD.md sections 0-11,
`tools/`, `out/`, `scans/`, `controls/`), the decode image-B Allocate relocation addendum on cmpkit 86da41d3ef68 over its
whole compare set.

Images, by sha256, as the record names them:

- X / C = `<cgif-B-twin>` = `<cgif-B-twin>`
  sha256 `ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7`
- Y / D = `<decode-B-twin>` = `<decode-B-twin>`
  sha256 `6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4`

Both hashes re-computed here. The kit (`git archive 98e50c029045 tools/cmpkit/86da41d3ef68`) checks out: `sha256sum -c
SHA256SUMS` 9 of 9 OK, and sha256(SHA256SUMS) = `86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60`, which
is also the content of the record's `kit/SHA256SUMS`.

No row is rejected: I found no settlement whose class is wrong, no citation whose quoted text is absent from the pinned
source, no use the record's trace drops, and no count I could not reproduce. The three doubtful rows below are two
documentation defects and one unpinned citation.

## Doubtful rows

### D1. RECORD.md section 9: "8 planted controls, each refused" — there are 7 refusals

`tools/plant_ctz.py` makes TWO file copies: `untouched` (byte-identical to the cgif-B twin) and `planted` (one byte of
the De Bruijn table flipped). `out/plant_ctz.out` lines 5 and 7 show the untouched copy settling **EQUAL** and the
planted copy **DIFFERS**. The untouched copy is a positive control, not a refusal. The distinct plants are:

| plant | tool | verdict |
|---|---|---|
| ctz (table byte 0x10439 0x11 -> 0xee) | plant_ctz.py | DIFFERS |
| (a) lui value made a STORE BASE through `add` | plant_lui.py via plant_luiclass.py | NOT CERTIFIED |
| (b) lui value passed as `void *addr` | plant_lui.py via plant_luiclass.py | NOT CERTIFIED |
| (c) displacement lui 0x40 -> 0x41 | plant_luilui.py | DIFFERS |
| (d) PackedCounterArray table byte 0x104ed flipped | plant_luilui.py | DIFFERS |
| (e) the same lui 0x40 -> 0x41 | plant_constbase.py | DIFFERS |
| (f) Refill +0x60 `addi a3, zero, 0x20` -> 0x21 | plant_constbase.py | DIFFERS |

That is 7 plants, each refused, plus 1 untouched baseline that is accepted. The sentence's own enumeration also lists 7
items, so the number 8 contradicts the list beside it. Nothing measured changes; the count in section 9 should read 7
refusals and 1 untouched baseline.

### D2. `tools/contracts.py` REAL_ARITY: the fflush and fclose line numbers are off by one

At the pinned commit (compiler-rt = llvm-project 87f0227cb60147a26a1eeb4fb06e3b505e9c7261), fetched and read here:

| cited | the record says | the pinned file holds |
|---|---|---|
| `sanitizer_common_interceptors.inc:6407` | `INTERCEPTOR(int, fflush, __sanitizer_FILE *fp)` | line 6407 is `#if SANITIZER_INTERCEPT_FFLUSH`; the INTERCEPTOR line is **6408** |
| `...inc:6412` | `REAL(fflush)(fp)` | line 6412 is `unpoison_file(fp);`; `int res = REAL(fflush)(fp);` is **6413** |
| `...inc:6426` | `INTERCEPTOR(int, fclose, __sanitizer_FILE *fp)` | line 6426 is `#if SANITIZER_INTERCEPT_FCLOSE`; the INTERCEPTOR line is **6427** |
| `...inc:6433` | `REAL(fclose)(fp)` | line 6433 is `unpoison_file(fp);`; `int res = REAL(fclose)(fp);` is **6434** |

The quoted code is real and the arity (1) it supports is right; only the line numbers are wrong. The citation is in use:
`scans/luiclass.tsv` carries it in at least one `lui-in-section` row's classed uses ("the indirect callee cannot read it
(a2 is beyond the 1 argument(s) of the function pointer: ...inc:6407 `INTERCEPTOR(int, fflush, ...)`"). Every other
citation I checked is exact (list below), so this is a transcription slip, not a pattern.

### D3. The RISC-V psABI citation carries no commit pin

`contracts.py` PSABI and RECORD.md section 5 (e) cite "RISC-V psABI riscv-cc.adoc lines 21-25, 178-179". Every
compiler-rt and musl citation in the same file names a commit; this one names none. I fetched
`riscv-non-isa/riscv-elf-psabi-doc` master: lines 21-25 are the `t0 - t2 / s0 - s1 / a0 - a7 / s2 - s11 / t3 - t6` rows
of the register table and lines 178-179 are "The base integer calling convention provides eight argument registers,
a0-a7", so the citation is correct today. It is the one load-bearing citation a future upstream edit can silently
invalidate. Class (e) at indirect calls rests on it (31 NOT CERTIFIED rows are the cases where it does not reach).

## Checks I ran

### 1. The 8 CLAIM functions, re-run on the pristine kit

I ran, from a fresh `git archive` of the kit, not from the record's copy:

```
python3 strictcmp3.py cmp <the 8 names of out/FNLIST8.txt> C=<cgif-B-twin> D=<decode-B-twin> C:D
```

My output is byte-identical to `out/strictcmp3-cmp.out` except the two header lines whose image paths the record's
publication scrub replaced by `<cgif-B-twin>` / `<decode-B-twin>` (declared in RECORD.md "Publication scrub"). Every
field of every row:

| function | X | Y | size | verdict | pcrel/real/unmeas | accepted | target-differ |
|---|---|---|---|---|---|---|---|
| Allocator::Allocate | 0x31550 | 0x31298 | 2440 | DIFFERENT-target | 81/0/0 | (2, 0, 20) | **1: +0xdc** |
| CombinedAllocator::Allocate | 0x359e4 | 0x3580c | 728 | EQUAL-mod-pcrel | 16/0/0 | (0, 0, 8) | 0 |
| SizeClassAllocator64LocalCache::Refill | 0x36134 | 0x35f5c | 256 | EQUAL | 0/0/0 | (0, 0, 0) | 0 |
| memset | 0x9790c | 0x92a1c | 248 | EQUAL | 0/0/0 | (0, 0, 0) | 0 |
| internal_mmap | 0x64198 | 0x63d88 | 12 | EQUAL | 0/0/0 | (0, 0, 0) | 0 |
| StackDepotPut | 0x724e0 | 0x720d0 | 32 | EQUAL-mod-pcrel | 2/0/0 | (0, 0, 0) | 0 |
| PoisonShadow | 0x53800 | 0x5308c | 1276 | EQUAL-mod-pcrel | 61/0/0 | (0, 1, 11) | 0 |
| TryMemCpy | 0x6dcc8 | 0x6d8b8 | 400 | EQUAL-mod-pcrel | 12/0/0 | (0, 0, 6) | 0 |

Allocate's only differing target is +0xdc and the other 7 have none. 45 CSTR rows, as section 1 states.

**+0xdc re-derived from the bytes, my own capstone decode, both images.** Both read identically:

```
+0xc0 auipc a2, 0xfffdf      +0xc4 ld a2, lo(a2)     (X -0x258 -> 0x103b8 | Y +0x78 -> 0x103d0)
+0xc8 neg a3, a1             +0xcc and a1, a1, a3    +0xd0 mul a1, a1, a2
+0xd4 auipc a2, 0xfffdf      +0xd8 srli a1, a1, 0x3a +0xdc addi a2, a2, lo12
+0xe0 add a1, a2, a1         +0xe4 lbu a1, 0(a1)
```

- the table base computes to 0x10428 in X and 0x10440 in Y (auipc at 0x31624 / 0x3136c, -0x21000, then -0x1fc / +0xd4) —
  the two addresses the kit reports;
- `srli 58` leaves 6 bits, so 0 <= index <= 63, and the only read is one `lbu` at base + index: the read extent is
  exactly [base, base+64);
- those 64 bytes are equal: `00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a`
  in both (the next 64 bytes are equal too);
- the multiplier the `.got` cell holds is `bf5d3dcd92a31802` at 0x103b8 and at 0x10440's counterpart cell 0x103d0 —
  equal, which is the `full+0xc4` acceptance.

### 2. Kit verdict stated first and verbatim

Section 1 is the first verdict in the record and every cell of it matches my re-run (table above), including the word
`DIFFERENT-target` and the `data-differs` kind. Section 1 also states, correctly, that strictcmp3 prints
`DIFFERENT-target` where strictcmp2 printed `EQUAL-mod-pcrel` for the same difference.

One nuance, not a defect: section 0 runs before section 1 and already asserts "+0xdc: the same table ... and the same
bytes as the re-run's bounded-byte-table settlement". The kit's own verdict is not altered or softened anywhere; a
reader meets a settlement claim one screen before the verdict that motivates it.

### 3. The lui rows — all 70 settled rows re-derived, not a sample of 30

I wrote an independent RISC-V tracer (capstone, my own ELF/symbol reader; it does not import the record's tools) that
follows the lui-defined register over both arms of every branch through mv / sext / add / addw / sub / subw / sh\*add /
add.uw / and / or / xor / andi / ori / xori / shifts / mul / div / rem, stops a derived value at a compare
(slt/sltu/slti/sltiu/seqz/snez/sltz/sgtz and branches), records BASE / STORE-DATA / ARG / TAILARG / RET / SYSCALL /
JUMPBASE / SPILL / RELOAD, and clobbers a0-a7 / t0-t6 / ra at calls. I ran it on **all 70 settled rows in both images**
and compared my in-function use offsets with the offsets the record cites in the same member.

- **70 of 70 rows: the record cites every use I find**, after accounting for two places where the record goes deeper
  than my tracer and so cites different offsets:
  - a `jr` jump-table dispatch (`__strftime_fmt_1` +0x64 / +0x480 / +0x508, `sysconf` +0xf4): my tracer stops at the
    dispatch, the record follows into the measured cases and cites the uses there (+0x514, +0x614, +0x1d4, +0xc0, ...);
  - a call through a thunk (`InitializeShadowMemory` +0x1c0 `jal 0x11d88`): the record resolves the callee to
    `__sanitizer::ProtectGap` and classes the uses inside it (+0x44, +0x68, +0xb0) instead of classing the argument
    register at the call site.
  In both cases the record's handling is the stricter one.
- The record's traces are the same in both images for every settled row (my own X/Y use-shape comparison agrees).
- **Class against the bytes.** For every cited use of every settled row I decoded the instruction at the cited offset
  and checked it against the class: (c) must be a compare or branch, (i)/(i-b) a call, (ii) a `ret`, (iii) a load /
  store / AMO / pointer-pass, (iv) a store or AMO, (e) a call or return. 998 citations resolve to one symbol
  unambiguously (c 310, e 554, iii 80, i 32, ii 14, i-b 2, iv 6): **0 mismatches**. The remaining 208 citations name a
  function truncated to 60 characters that matches several symbols; for every one of those at least one candidate's
  instruction fits the class.
- **Hand-derived rows across the classes** (bytes read directly):
  - (c) alone, `StackStore::Store` +0xb0 V=0x100000: the only use is `xor a0, a0, a1` at +0xc4 followed by `seqz a0, a0`
    at +0xcc; the record cites +0xcc "compare operand". The xor+seqz pair is an equality test and the result is a
    predicate, so ending the value there is right, and the cited offset is the precise one.
  - (e), `Quarantine::Recycle` +0x74: the derived value is in a4 at the call at +0xa4 to
    `QuarantineCache::MergeBatches`, whose first three instructions are `addi sp,sp,-0x10 ; sd ra,8(sp) ; ld a4,8(a0)` —
    a4 is written before any read on every path. Dead-at-call holds.
  - (iii) OFFSET-SAME-SYMBOL, `StackDepotGet` +0x30 and +0xc8: the auipc pair resolves to `__sanitizer::theDepot` in
    both images (X 0x727a4 + 0x116000 - 0x64c = 0x188158; Y 0x72394 + 0x111000 - 0x17c = 0x183218, both the symbol's
    value), and the lui+addiw adds 0x400010 / 0x400008, so the full address is `theDepot+0x400010` / `theDepot+0x400008`
    in both: the same symbol and the same offset, which is what class (iii) demands.
  - (ii), `__month_to_secs` +0x2c: the value is handed back to `__tm_to_secs`, where the return at +0x100 carries the
    musl `__tm_to_secs.c:3` / line 19 citation. The citation lives with the return, not with the hand-back.
  - (iv) and the private-spill rule, `AsanDeactivate` +0x8c V=0x100010: the store is `sw a0, 8(sp)` at +0x90 and the
    frame pointer leaves the function six bytes later (`mv a0, sp ; jal ReInitializeAllocator`). The slot is therefore
    **not** private, the record refuses to treat the store as a spill, and classes it (iv) with
    `asan_allocator.h:34-38 AllocatorOptions`. The 32-bit store at +8 writes `min_redzone = max_redzone = 16`, which is
    exactly V = 0x00100010. This is the rule working as the owner stated it.
- **Citations fetched and read at the pinned commits** (compiler-rt = llvm-project 87f0227cb601, musl = f21a96538f78;
  I fetched each file and printed the cited lines). Exact: `sanitizer_common.h` 90, 103, 113-114, 186, 187, 354,
  781-783; `sanitizer_posix.h` 30, 40-41; `asan_poisoning.h` 26-27; `sanitizer_termination.cpp` 20, 50-56, 67-72;
  `sanitizer_mutex.h` 35-36, 48, 253-263, 327, 357-358; `sanitizer_allocator_primary64.h` 671-677, 753, 806, 807, 845,
  846; `sanitizer_allocator_primary32.h` 281-282, 305; `sanitizer_allocator_stats.h` 18-19, 47-49; `asan_stats.h` 24-37
  (mmaped is the 11th uptr, so +0x50, as cited); `asan_allocator.h` 34-38; `asan_activation.cpp` 115-119;
  `sanitizer_linux.cpp` 582-586; `sanitizer_common.cpp` 334, 343-346; `sanitizer_thread_registry.h` 121;
  `sanitizer_stack_store.h` 21, 88-91; `sanitizer_stack_store.cpp` 374-376; `sanitizer_libc.h` 35-36;
  `interception.h` 255-262; `sanitizer_common_interceptors.inc` 414, 423, 1004, 2225;
  `asan_interceptors_memintrinsics.cpp` 28-39, 43-50; musl `open.c:5`, `socket.c:6`, `sysconf.c:28` and 190-193,
  `__tm_to_secs.c:3` and 19, `__year_to_secs.c:1`, 10, 46, `__map_file.c:10`, `alltypes.h.in` 56 and 74. The only
  defects are D2 (fflush, fclose) and D3 (unpinned psABI).
- **No class (i) settles an address.** Every (i) citation in the settled rows is a count, size, length, flags, mode,
  alignment or `u32 count`: internal_mmap a3 int flags (8), internal_open a1 int flags (2), ReservedAddressRange::Map /
  MapOrDie a2 uptr size (2+2), MmapAlignedOrDieOnFatalError a0 uptr size and a1 uptr alignment (2+2), MmapOrDie a0 uptr
  size (4), Semaphore::Post a1 u32 count (8), PoisonShadow a1 uptr size (2), `__sanitizer_internal_memset` a2 uptr n
  (4), open a1 / openat a2 int flags (1+2), socket a1 int type (2), CheckFailed a3/a4 (i-b, 4+2). No pointer-typed
  parameter is used to settle anything.
- **Internal arithmetic of section 5 checks out**: the per-class row table in `scans/luiclass-summary.md` sums to the
  record's "(c) 27, (e) 40, (i) 17, (i-b) 3, (ii) 7, (iii) 28, (iv) 5, (d) 0"; 12 settled lui-const + 58 settled
  lui-in-section = 70; 23 + 16 = 39 NOT CERTIFIED, each listed by member, word, V and reason;
  `scans/lui-targets.tsv` has 74 rows and `scans/luiconst-targets.tsv` 35, which is the 109 rows of
  `scans/luiclass.tsv`. Exposure: 41 of 786 EXPOSED, 745 zero, as `scans/exposure.out` prints.
- **The tool matches its description.** `luitrace.py` extends `luiflow.ALU` with `sh1add / sh2add / sh3add /
  sh*add.uw / add.uw`, so the record's op list is the list the trace uses. (`luiflow.py`, the earlier tool, lacks them;
  it is not what section 5 cites, and no `sh*add` instruction exists in either image, so nothing turns on it.)
  `luitrace.py` treats `lr` as a load and `sc` / `amo*` as stores, and takes the stored register of a 3-operand
  `amoadd` / `sc` as STORE-DATA, so the 290 `lr.d.aqrl` / 287 `sc.d.rl` pairs in the images are not a silent drop.

### 4. constbase: the fail-opens (a)-(h)

Reproduced independently from the images, not read from the record:

| claim (RECORD section 6) | my own measurement |
|---|---|
| closure 786 members | 786 (closure over direct `jal` / `j` from the 8 roots, each image) |
| every instruction 4 bytes, 70,756 in the closure, e_flags 0x4, RVC clear — so (g) c.lui cannot occur | 70,756 instructions, every size 4, `e_flags` 0x4 in both images; no `c.*` mnemonic anywhere in either image |
| 558 lui and 4226 `addi rd, zero, imm` tracked | X 558 / 4226, Y 558 / 4226 |
| (d) 0 fmv and 0 csr instructions in the closure | X 0 / 0, Y 0 / 0 (both exist elsewhere in the images, not in the closure) |
| (e) 13 switch `jr` plus 32 `jr t1` through a loaded pointer | 45 `jr` in the closure: exactly 32 are `jr t1` and every one of those is preceded within 3 instructions by a load; the other 13 are the switch dispatches |
| (a) 413 / (f) 2106 / (h) 2036 sites, 88 reloads per image | `scans/constbase.out` line 3 prints `{'(a) immediate': 413, '(f) passed / returned': 2106, '(h) without lui': 2036}; tracked values spilled and reloaded: X 88 / Y 88` |
| 2934 sites, 287 functions, 2787 EQUAL + 24 NUMBER + 21 NOT CERTIFIED + 102 REVIEW | sums check (2787+24+21+102 = 2934); the per-function table lists 21 REVIEW functions and 8 NOT-CERTIFIED-only functions, and the REVIEW sites sum to 102, the NOT CERTIFIED sites to 21 |

**Allocator::Allocate, 71 sites, read one by one.** 70 of the 71 site strings are byte-identical between X and Y. The
single difference is site 47, the De Bruijn read: `TABLE 0x10428` vs `TABLE 0x10440`, `indexed by srli(mul(0x200, (a
load of the image constant bf5d3dcd92a31802)), 0x3a) (index <= 0x3f)` — the same table, settled by the 64 equal bytes I
checked in section 1, and the bound the scan prints (index <= 0x3f) is the same bound I derived from `srli 58`.

Shape (a), the load / store immediate, verified against the bytes: the constant at +0x78 is `addi s0, zero, 8` (shape
(h): a constant with no lui at all), and the sites fold the instruction immediate into it — `lbu a0, -0xf(s4)` at +0x2c8
and `lbu a1, 1(s5)` at +0x6e4 are recorded as constant -0xf, `sh a1, -0xe(s4)` at +0x2e4 as -0xe, `sw s1, -0xc(s4)` at
+0x2e8 as -0xc, `sd a0, 8(s5)` at +0x3b8 as -0x8. Each of those instructions is identical in the two images. Shapes (b)
and (c) appear in the same rows as folded `addi` / `addiw` chains and `or(xori(slli(srli(mul(...` trees; shape (f) as
`the value passed: ... => EQUAL PASSED-OBJECT / PASSED-CONST / PASSED-LUIADDR` rows at `jal` and `jalr` sites, including
the indirect call at +0x6dc.

### 5. The 21 lui+lui sites

- "functions with 2 or more lui in either image: 101" — I counted the closure members myself: **101**.
- 21 sites, 19 OBJECT and 2 TABLE. Comparing the X and Y site strings one by one: **all 21 identical** once the table
  address is normalised, i.e. the same base object, the same constant part and the same index expression.
- The 2 TABLE sites: X 0x104e8 / Y 0x10500 and X 0x20a5e / Y 0x209fa. I read 64 bytes at each: equal in both pairs, and
  both are the same De Bruijn table (`00010207030d0813...`). Both lie in `.rodata` in both images.
- Controls (c) and (d) re-run below.

### 6. The planted controls

I re-ran all four plant scripts myself, from the record's `tools/` against the real images, with `PLANTDIR` outside the
record:

| script | my output vs the record's |
|---|---|
| `plant_ctz.py` -> `out/plant_ctz.out` | byte-identical |
| `plant_luiclass.py` -> `scans/plant_luiclass.out` | byte-identical |
| `plant_luilui.py` -> `scans/plant_luilui.out` | byte-identical |
| `plant_constbase.py` -> `scans/plant_constbase.out` | byte-identical |

So every plant is refused on a re-run: ctz DIFFERS, (a) NOT CERTIFIED (luitrace REVIEW, `ABSOLUTE V-derived`), (b) NOT
CERTIFIED (internal_mmap's syscall a0 has no contract), (c) DIFFERS, (d) DIFFERS, (e) DIFFERS, (f) DIFFERS. The count is
7, not 8 — finding D1. `plant_lui.py`, which no line of `run.sh` names, is not dead: `plant_luiclass.py` runs it as a
subprocess to build the two planted copies.

### 7. Reproduction

Three steps re-run from the pristine kit and compared with the record's files:

| step | result |
|---|---|
| `strictcmp3.py cmp <8> C=.. D=.. C:D` | identical apart from the two scrubbed path lines |
| `closure_strict3.py <X> <Y> <8>` (20,726 lines) | `diff` against `out/closure_strict3.out`: **0 lines** |
| `jtcheck.py <X> <Y> <the 100 reported>` | `diff` against `out/jtcheck.out`: **0 lines** |

Plus the four plant scripts above, which run the record's own tools end to end and also reproduce byte for byte. The
closure header line reproduces section 3's counts directly (784 functions from the 8 roots, EQUAL 162, EQUAL-mod-pcrel
522, other 100, 426 members with acceptances).

Limit of this check: I did not re-run the two 51-minute end-to-end `run.sh` copies that section 10 reports, so the
"`diff -r` of the two copies: 0 lines" claim and the hash-seed determinism story are unverified here; what I verified is
that four separate steps, two of them the kit's own, reproduce exactly from the inputs.

Tallies I re-added from the files rather than from the prose: `out/fulldiff.tsv` has 164 rows, kit kinds data-differs 90
+ lui-in-section 74 = 164; `out/certify.tsv` has 164 rows and its settlement counts sum to 164 (67 + 6 + 1 + 1 + 1 + 12
+ 2 + 58 + 16); the 14 rows `fulldiff.py` leaves DIFFERS are exactly the 12 `tables.py` measures plus the 2
`switchbound.py` bounds (VSNPrintf +0x1c0 and parseFDEInstructions +0x140); section 9's "123 NOT CERTIFIED" is 21 + 102
and "2811 equal or settled" is 2787 + 24. I also recomputed four of the jump tables entry by entry
(`Decorator::ShadowByte` 83, `ErrorGeneric::ErrorGeneric` 82, `__strftime_fmt_1` 86, `sysconf` 13): every
function-relative target is equal in the two images and inside the function. One CSTR-EMPTY row checked at the bytes
(0x13ed0 / 0x13ef3): NUL in both, and exactly 533 equal bytes past it, the number `out/escape.out` reports as the min
and the max for all 67 rows. `out/nameonly.out`: 0 NAME-ONLY acceptances.

### 8. Relation to the other lane's re-run

RECORD.md section 0 says how the two relate: this directory supersedes the 4bbd3a74be89 run as the current version, the
earlier record stays beside it unchanged, and the 8-function re-run of record is
`alloc-reloc/B/fncmp.cmpkit-4bbd3a74be89.log` with `alloc-reloc/cmpkit-4bbd3a74be89/settled.tsv`. It states that this
record's C:D is the same image pair as that re-run's T:E. I verified the two files' hashes against
`out/rerun8cmp.out`'s header: log `eff9ccb831d8`, settled.tsv `41d7ccff1f7f` — both match.

I then did my own field-by-field comparison, parsing the other lane's log myself and using my own kit re-run of the 8
functions (not the record's file), over verdict / pcrel / real / unmeasured / accepted targets / differing-target words:

- **T:E: no disagreement** in any field of any of the 8 functions, except the verdict word of Allocate.
- **S:E: exactly the two the record names** — PoisonShadow accepted targets (0, 1, 11) here against (0, 0, 11) there,
  and PoisonShadow target differences 0 here against 0x48c there.
- The Allocate verdict word, `DIFFERENT-target` here against `EQUAL-mod-pcrel` there, is the kit-version change
  described in section 1. `rerun8cmp.py` is explicit about it: it compares strictcmp3's *word* verdict (its last column)
  with strictcmp2's verdict and prints the combined verdict on its own row, which is why `out/rerun8cmp.out` shows
  "combined verdict (this kit) DIFFERENT-target" separately from the compared rows. The normalisation is disclosed in
  the tool's docstring and in RECORD.md section 1, so the 2-disagreement table is complete for what it compares.

The record also checks the two settled differences against the bytes here: the +0xdc table (0x10428 / 0x10440, 64
bytes) and the PoisonShadow `.got` cells (0x9e248 / 0x99328, both `0100000000000000`) are reported IDENTICAL to the
re-run's recorded bytes, which is consistent with my own reads of both.

## What I did not check

- The two end-to-end `run.sh` copies and the hash-seed determinism of section 10 (see check 7).
- The kit's own 40-plant suite and `negctl.py` of section 11: I read `controls/compare.out` and the three
  evidence-truncation rows it explains (Q1, V1, V2 under paircl-NEW, whose raw outputs are identical), but I did not
  re-run `suite.py` or `negctl.py`.
- The 39 NOT CERTIFIED lui rows and the 123 NOT CERTIFIED constbase sites are not settlements and I did not re-derive
  them; I checked only that each carries a reason and that none is a measured difference (every differing target in
  `out/certify.tsv` is either measured equal or marked NOT CERTIFIED: REAL 0).
