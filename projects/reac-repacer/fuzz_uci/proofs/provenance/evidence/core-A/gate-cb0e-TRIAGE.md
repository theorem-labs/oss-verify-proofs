# Triage of the cb0e symbol-gate rows: reac-repacer/fuzz_uci image-A core relocation

role: check. rule 24: no function proved. Read-only triage. Nothing outside this directory was changed.

## Result

- Gate run: `run.log` (port_addr_check cb0e067e3bae `--fail-on-flags`; its summary lines are `gate-cb0e-flagged.txt` in this directory). Last line: `FLAGGED 368 rows in 10 classes: DIFFERENT-SYMBOL=1 GEOMETRY-CHANGED=9 KIND-CHANGED=9 NO-COUNTERPART=1 NON-ADDRESS-CHANGED=174 SAME-VALUE-DIFFERENT-OBJECT=20 STALE-DONOR-CODE-POINTER=1 UNPAIRED-PORTED=40 UNPAIRED-SOURCE=105 UNRESOLVED=8`. FLAG-CLASSES 575d398c6022.
- Every one of the 368 flagged rows of `raw.tsv` has a measured reason below. The count per class matches the FLAGGED line (table below).
- **DEFECTS: none.** No flagged row has a wrong dst value. Each dst value is either fuzz_uci's own value of the quantity that the src value names in grant's image, or a value with no address role that is correct for fuzz_uci.
- One row per line, with reason id and measurement: `gate-cb0e-triage-rows.tsv` in this directory (column `raw_line` = the row's line number in `raw.tsv`).

| class | FLAGGED | triaged | reasons (rows) |
|---|---:|---:|---|
| DIFFERENT-SYMBOL | 1 | 1 | FMTWIN (1) |
| GEOMETRY-CHANGED | 9 | 9 | G-6128 (9) |
| KIND-CHANGED | 9 | 9 | FMTWIN (5), K-TLS (2), K-ABSENT0 (2) |
| NO-COUNTERPART | 1 | 1 | THUNK (1) |
| NON-ADDRESS-CHANGED | 174 | 174 | N-FMTPTR (113), N-REGCNT (44), N-RA3 (3), N-RANGES (3), N-IAL (2), N-CELLPATCH (2), FMTWIN (2), N-AD1o-BSS20 (1), N-AD1o-TOP (1), N-AD1o-ZLEN (1), N-DEPOT (1), N-INST (1) |
| SAME-VALUE-DIFFERENT-OBJECT | 20 | 20 | SV-MMAP (18), SV-HWCAP (2) |
| STALE-DONOR-CODE-POINTER | 1 | 1 | THUNK (1) |
| UNPAIRED-PORTED | 40 | 40 | PATCH-ZS (30), P-UCIPROG (10) |
| UNPAIRED-SOURCE | 105 | 105 | S-GRANTPROG (44), PATCH-ZS (39), S-ABSENTRT (12), S-AF0L (6), THUNK (4) |
| UNRESOLVED | 8 | 8 | U-TLSSH (2), FMTWIN (2), U-JT (1), U-UNMAP (1), U-PHDR (1), U-STDIN (1) |
| total | 368 | 368 | |

## What was measured, and how

- Images: src `fuzz_grant.asan` sha256 c2c7559b29bd, dst `fuzz_uci.asan` sha256 6ea017c24525. Symbols on both sides come from the unstripped twins' `.symtab` (`unstripped/fuzz_grant/fuzz_grant.asan`, pin 57c26f993615; `unstripped/fuzz_uci/fuzz_uci.asan`, pin 56822e263d76). Every allocated section of each twin is byte-identical to its stripped image, except `.note.gnu.build-id`. The gate named the src side by donor recovery (run.log line 4). That is why it called some src values unnamed (see U-UNMAP).
- Image bytes, PT_LOAD / PT_TLS / PT_PHDR and section bounds were read from the stripped images with pyelftools.
- Text: src = `work10/stage`, dst = `work10/stage-out`. Each row's src line and dst line were read. A dst line is the src line + 1 (the added `copied from` header line), unless a patch or a removed row moves it.
- Start-up layer (not staged): the dst lib in a clean checkout of commit 276afc86670b (the committed lib), and grant's released lib (`git show 25e3d17bdb50:proofs/libreac/fuzz_grant/lib/...`): AD2j (IMG_REGIONS, R_A3), AF0m (TFIB_DEPOT, TFIB_INST, TFIB_IAL_LO), AB13 (TFIB_BSS).
- The run's decisions: `work10/check.tsv`, `fixed.tsv`, `decimals.tsv`, `review.tsv`, `overrides.tsv`, `patches.log`; and `overrides.tsv`, `zero-shadow-forallb.patch`, `cell-lookup.patch` in this directory, and `provenance/core-reloc/A/README.md`.
- Override cross-check: 14 flagged rows carry an override row (same file, donor line, old value). For all 14, the dst value equals the override's new value: AD1o:94, AD1o:99, AD28:293, AD28:294, AD2d:131, AF0l:13, AF0l:14, AD2f:147, AE2t:63 (x2), AE2u:63 (x2), AE2v:63 (x2).
- `Equal modulo relocation immediates` in code comparisons means: the immediates of jal / auipc / lui and the 12-bit immediates of I-type and S-type words are masked; opcode, registers and funct3 must be equal.

### The image-B explanations, checked for image A

- AB1w thunk row after the dropped bcmp row = name-wildcard pairing: **true for image A** (reason THUNK; the n-th-wildcard count is measured).
- 0x104022 etc. = mmap flag sums: **true for image A** (SV-MMAP). The YA01:715 / YA02:741 value 0x20112D is not a flag sum: it is the AT_HWCAP range (SV-HWCAP).
- AE3h 0x5c603 = an instruction word: not flagged in this run. cb0e classes raw rows AE3h:1660 (idx 0, 3) and AE3h:1661 (idx 1) INSN-SAME (`insn 0x0005c603` on both sides).
- AFk1 BCELLS / AFk2 DCELLS = relative jump-table entries: not flagged in this run. cb0e classes AFk1:659 idx 11 and AFk2:597 idx 14 SAME-SYMBOL, note `the same jump-table entry (label - base) in the target` (sysconf+0x208 - sysconf+0xdc; __sanitizer::VSNPrintf+0x350 - VSNPrintf+0x1c0).

## Reasons

- **FMTWIN** (10 rows; DIFFERENT-SYMBOL, KIND-CHANGED, NON-ADDRESS-CHANGED, UNRESOLVED): driver format-string shadow window [SH_LO, SH_HI) for the vfprintf/vprintf interceptor's read of the format: SH_LO = floor8(0x7fff8000 + fmt/8), SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8, each side from its own image's string address (found by its bytes in .rodata). The same rule reproduces every src value and every dst value. The gate flags these because it names a shadow address only where an object starts in the 8 bytes it covers, and the floor8 cut lands on other objects / near-2^31 bounds.
- **G-6128** (9 rows; GEOMETRY-CHANGED): 6128 = kPage 4096 + secondary redzone 2048 - kChunkHeaderSize 16 (AFfc hdr_facts: hdr = MAP + 6128; YG00 kPage/kChunkHeaderSize). It is an offset from the runtime mmap base aMAP, not an image quantity. The gate's donor reading (.got.lo 0x9c810 -> load2.memhi 0x9e000 = 0x17f0) is a coincidence; its expected 0x1040 is the same distance in fuzz_uci and has no role here.
- **K-ABSENT0** (2 rows; KIND-CHANGED): override (knock's precedent): fuzz_uci.asan symtab has no __asan_memset and no __interceptor_trampoline_bcmp / bcmp; absent entry = 0 (no code at 0, image starts 0x10000).
- **K-TLS** (2 rows; KIND-CHANGED): tls.lo = PT_TLS p_vaddr: src 0x9b168 (.text.hi 0x9b164 + 4 bytes pad), dst 0x95a88. In dst .text.hi = tls.lo = load1.memhi = 0x95a88, so the gate reads it as an image extent. review.tsv bound-name-mismatch: the released value is tls.lo, and the port wrote dst tls.lo.
- **THUNK** (6 rows; NO-COUNTERPART, STALE-DONOR-CODE-POINTER, UNPAIRED-SOURCE): tfib_[AE]_thunk_<hex> names carry a hex wildcard, so the gate pairs the n-th tfib_A_thunk_* (and tfib_E_thunk_*) of each file. src AB1w has 19 thunk rows (18th = thunk_95368 at line 540 = bcmp, 19th = thunk_96f9c at line 563); dst has 18, because fuzz_uci.asan has no bcmp and the port blanked the row (dst line 541). So src 540 is judged against dst 564 (the dst thunk_96f9c), and src 563 has no partner. Measured by role: src 563 [0x9804c, 0x98054) = __pthread_testcancel+0x0 .. end of __testcancel (= __set_thread_area); dst 564 [0x92970, 0x92978) = __pthread_testcancel+0x0 .. end of __testcancel (= __set_thread_area); __pthread_testcancel/__testcancel bytes equal modulo relocation immediates. The thunk_96f9c name hex is an IDENT (cgif-era name), not an address.
- **N-AD1o-BSS20** (1 row; NON-ADDRESS-CHANGED): override `0x9b960 / 8`: 79660 = 0x9b960/8; 0x9b960 = .bss.lo 0x9b940 + 0x20 = __do_init.__object+0x10 (src 0xa14a0/8 = 82580, same role).
- **N-AD1o-TOP** (1 row; NON-ADDRESS-CHANGED): (IMG_TOP - 1)/8: (0x5f4000 - 1)/8 = 780287 (src (0x5fa000 - 1)/8 = 783359). IMG_TOP 0x5f4000 = page-up of fuzz_uci's last PT_LOAD end 0x5f3870.
- **N-AD1o-ZLEN** (1 row; NON-ADDRESS-CHANGED): override `(0x5f4000 - 0x9b910) / 8` = 700638 (src (0x5fa000 - 0xa1460)/8 = 700788); 0x9b910 = __stop_asan_globals = TFIB_BSS.lo.
- **N-CELLPATCH** (2 rows; NON-ADDRESS-CHANGED): cell-lookup.patch: `apply (nth_error_In _ 60)` (60 = list index) is replaced by `apply (AF0x.cell_lookup_In _ (ANum (TFIB_OOM + 1)))`; the gate pairs the index 60 with the byte offset 1. Neither is an address.
- **N-DEPOT** (1 row; NON-ADDRESS-CHANGED): S2 = TFIB_DEPOT + 4*bkt, witness TFIB_DEPOT/4: dst AF0m TFIB_DEPOT 0x180ed8 = __sanitizer::theDepot+0 (symtab), /4 = 394166; src 0x186a18 = theDepot+0, /4 = 400006. decimals.tsv `derived`.
- **N-FMTPTR** (113 rows; NON-ADDRESS-CHANGED): decimal pointer into a driver format string (a position of the vfprintf walk). Same string, same offset in both images; the string start is verified from the image bytes (NUL before it, bytes equal). The gate classes a decimal that is not a symbol start as non-address, so every moved one is flagged.
- **N-IAL** (2 rows; NON-ADDRESS-CHANGED): witness of (P + 8k) mod 8 = 0 with P = internal_alloc_placeholder (TFIB_IAL_LO): dst 655872 = 0xa0200, /8 = 81984; src 0xa5d40/8 = 84904. decimals.tsv `derived`.
- **N-INST** (1 row; NON-ADDRESS-CHANGED): (TFIB_INST + 168)/8 with TFIB_INST = __asan::instance: dst (0x9b998 + 168)/8 = 79688, src (0xa14d8 + 168)/8 = 82608. The 637336 in the same dst sentence is the dst TFIB_INST (0x9b998), so `637336 + 168 + 8 * LGv = (79688 + LGv) * 8` holds exactly. decimals.tsv first `mapped` it as a string pointer (0x141b0); review.tsv replaced it with this quotient.
- **N-RA3** (3 rows; NON-ADDRESS-CHANGED): override `R_A3 length`: dst AD2j R_A3 = mkRegion 636296..637136, CImg 840 = (__stderr_FILE 0x9b5d0 - 0x48) .. __start_asan_globals 0x9b8d0; grant 658912..659744, CImg 832.
- **N-RANGES** (3 rows; NON-ADDRESS-CHANGED): instruction-word count of an interceptor code range (icpt_ranges entry (start, n%nat)). fuzz_uci lacks three functions inside grant's ranges, so the counts shrink by exactly their size; the remaining words are equal to grant's modulo relocation immediates (jal/auipc/lui and I/S-type 12-bit immediates).
- **N-REGCNT** (44 rows; NON-ADDRESS-CHANGED): count or index in a region list. fuzz_uci's IMG_REGIONS (lib A/AD2j.v:150, generated start-up layer) has 31 regions; grant's (25e3d17bdb50 A/AD2j.v:165) has 33 (R_A1l, R_A1m are not in fuzz_uci's list). Every count, and every index after list position 11, drops by 2.
- **SV-HWCAP** (2 rows; SAME-VALUE-DIFFERENT-OBJECT): KRange (EVar V_HW) 0x112D 0x20112D: the range of the AT_HWCAP value hw (YA02 hw_facts_ok proves it from hwcap_rv64gc / hwcap_rv64gcv). 0x112D = ISA bits a,c,d,f,i,m; 0x20112D adds bit 21 (v). Not an address.
- **SV-MMAP** (18 rows; SAME-VALUE-DIFFERENT-OBJECT): mmap flags word, argument of `match prot, flags` (YA01 node_mmap2g), mmap_noreserve_b, ff_class and noreplace_core (YA09): MAP_PRIVATE 2 + MAP_ANON 32 [+ MAP_FIXED 16] [+ MAP_NORESERVE 16384] + 0x100000, the bit that YA09 `noreplace_core` names (MAP_FIXED_NOREPLACE). MAP_PRIVATE / MAP_FIXED / MAP_ANON / MAP_NORESERVE values as defined in other units' Spec/Malloc.v (git grep at 276afc86670b). Each value decomposes into these bits with remainder 0. ABI constants; they never relocate. The Reusable files are text-identical on both sides apart from the added header line.
- **P-UCIPROG** (10 rows; UNPAIRED-PORTED): fuzz_uci's own program functions check_no_overread, check_value, check_clamp, rp_hot_clamp, rp_uci_int, written on dst line 87 (A and E rows). Each A value is the symbol's start and each E value its start+size in fuzz_uci's symtab; with the kept rows (main .. LLVMFuzzerTestOneInput, asan.module_ctor/dtor) they cover every function of fuzz_uci's program range except oft_exit_guard, which grant's table also omits.
- **PATCH-ZS** (69 rows; UNPAIRED-PORTED, UNPAIRED-SOURCE): zero-shadow-forallb.patch (decode's, re-cut): the Tfib_zero_shadow case split (15 ranges in grant) becomes a forallb check (fuzz_uci has 3 ranges). Lines the patch deletes (src) or adds (dst) carry literal 8s (shadow granule) and 0 (mod remainder); the patch also adds sentences, so the identical lines after it in the same lemma get a new sentence index and the gate cannot pair their 8s. Every row is a literal 8 or 0, a non-address, and each 'same text' row has an identical line on the other side.
- **S-ABSENTRT** (12 rows; UNPAIRED-SOURCE): runtime functions that grant links and fuzz_uci does not: __asan_stack_malloc_0/2/4, __interceptor_trampoline_bcmp, ___interceptor_bcmp, __asan_memset (README.md file-list notes; measured on both symtabs). In dst the rows are gone: lines 68, 70, 71, 122, 151 are blank and line 87 now holds fuzz_uci's program rows (P-UCIPROG). No file of work10/stage and no file of the dst lib (276afc86670b) uses these names (grep).
- **S-AF0L** (6 rows; UNPAIRED-SOURCE): AF0l Tfib_code pc_stack_malloc: grant has classes 0, 1, 2, 4; fuzz_uci.asan has only __asan_stack_malloc_1 (0x3c1b8).
- **S-GRANTPROG** (44 rows; UNPAIRED-SOURCE): fuzz_grant's own program functions (AB1w program table, lines 441 and 444-464). fuzz_uci.asan has none of them (measured on both unstripped symtabs); the port blanked these rows (dst lines 442, 445-465) and wrote fuzz_uci's own program functions on dst line 87 (UNPAIRED-PORTED P-UCIPROG). No file of work10/stage and no file of the dst lib (276afc86670b) uses these names (grep).
- **U-JT** (1 row; UNRESOLVED): src 0x22c0c = cell +0x118 (entry 70) of the 86-entry jump table of __strftime_fmt_1 at 0x22af4..0x22c4c (= .rodata.hi - 0x40); dst 0x22584 = the same cell of the same table at 0x2246c..0x225c4 (= .rodata.hi - 0x40). All 86 entries target the same offset in __strftime_fmt_1 in both images (entry delta constant 0x5054). review.tsv: bound-released-elsewhere. No file of work10/stage or of the dst lib uses tfib_rodata_hi.
- **U-PHDR** (1 row; UNRESOLVED): AT_PHDR value: PT_PHDR p_vaddr = 0x10040 (e_phoff 64 + base 0x10000) in both images.
- **U-STDIN** (1 row; UNRESOLVED): override `__stdin_FILE.buf (FILE+88)`. Measured: word at __stdin_FILE+88 = src 0x5f85e8, dst 0x5f2aa8 (= stdin buf+8). SOBUF_LO (stderr FILE.buf) = dst 0x5f2698, same layout.
- **U-TLSSH** (2 rows; UNRESOLVED): 0x7fff8000 + a/8 with a = builtin_tls+0xeb8 in both (src 0x5d88c0, dst 0x5d2d80; builtin_tls size 0x200d0 both). It is a lower bound on SMv under mb >= IMG_TOP; it stays below shadow(IMG_TOP) (src 0x800b7400, dst 0x800b6800). The two uses (AFjm map_zoneN, AFk1 sm_bounds) moved together in each tree.
- **U-UNMAP** (1 row; UNRESOLVED): __unmapself+0x0 in both unstripped symtabs (src 0x98060, dst 0x92984) = end of the 12-byte asm stub __set_thread_area (symtab size 0); stub bytes 130205001305000067800000 identical. The gate called the src side unnamed because its src symbols are donor-recovered, not the unstripped twin's.

## Rows per class

### DIFFERENT-SYMBOL (1 row; FLAGGED says 1)

Reasons: FMTWIN (1).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 238 | A/AE2u.v:63 | 64 | Definition SH_LO (0) | hex | 0x7fffbaf8 | 0x7fffbab8 | FMTWIN | format "cli: read error on %s\n" (len 22) src @0x1d7c5, dst @0x1d5fb: SH_LO = floor8(0x7fff8000 + fmt/8) = src 0x7fffbaf8, dst 0x7fffbab8; override row |

### GEOMETRY-CHANGED (9 rows; FLAGGED says 9)

Reasons: G-6128 (9).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 145 | A/AFfc.v:100 | 101 | Lemma hdr_facts (0) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 171 | A/AFjq.v:713 | 714 | Lemma segUe / sentence 43 (0) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 172 | A/AFjq.v:715 | 716 | Lemma segUe / sentence 52 (2) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 173 | A/AFjq.v:716 | 717 | Lemma segUe / sentence 53 (0) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 380 | A/AFig.v:41 | 42 | Definition st_end (2) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 381 | A/AFig.v:41 | 42 | Definition st_end (5) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 382 | A/AFjq.v:838 | 839 | Lemma segUo / sentence 200 (0) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 383 | A/AFjq.v:840 | 841 | Lemma segUo / sentence 209 (2) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |
| 384 | A/AFjq.v:841 | 842 | Lemma segUo / sentence 210 (0) | dec | 0x17f0 | 0x17f0 | G-6128 | SOff aMAP 6128 / hdr = MAP + 6128; value unchanged |

### KIND-CHANGED (9 rows; FLAGGED says 9)

Reasons: FMTWIN (5), K-TLS (2), K-ABSENT0 (2).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 236 | A/AE2t.v:63 | 64 | Definition SH_LO (0) | hex | 0x7fffbaf0 | 0x7fffbab8 | FMTWIN | format "cli: cannot open %s\n" (len 20) src @0x1d7b0, dst @0x1d5e6: SH_LO = floor8(0x7fff8000 + fmt/8) = src 0x7fffbaf0, dst 0x7fffbab8; override row |
| 239 | A/AE2u.v:63 | 64 | Definition SH_HI (0) | hex | 0x7fffbb00 | 0x7fffbac8 | FMTWIN | format "cli: read error on %s\n" (len 22) src @0x1d7c5, dst @0x1d5fb: SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8 = src 0x7fffbb00, dst 0x7fffbac8; override row |
| 240 | A/AE2v.v:63 | 64 | Definition SH_LO (0) | hex | 0x7fffb2e8 | 0x7fffb2c0 | FMTWIN | format "cli: input >= %u bytes, refused\n" (len 32) src @0x1976d, dst @0x19614: SH_LO = floor8(0x7fff8000 + fmt/8) = src 0x7fffb2e8, dst 0x7fffb2c0; override row |
| 242 | A/AE2w.v:63 | 64 | Definition SH_LO (0) | hex | 0x7fffab20 | 0x7fffaaf8 | FMTWIN | format "usage: %s INPUT\n" (len 16) src @0x15905, dst @0x157cd: SH_LO = floor8(0x7fff8000 + fmt/8) = src 0x7fffab20, dst 0x7fffaaf8; no override row: written by port_core's review rule `shadow-window SH_LO/SH_HI (target string at ...)` (review.tsv), which corrected check.tsv's granule shift |
| 243 | A/AE2w.v:63 | 64 | Definition SH_HI (0) | hex | 0x7fffab28 | 0x7fffab00 | FMTWIN | format "usage: %s INPUT\n" (len 16) src @0x15905, dst @0x157cd: SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8 = src 0x7fffab28, dst 0x7fffab00; no override row: written by port_core's review rule `shadow-window SH_LO/SH_HI (target string at ...)` (review.tsv), which corrected check.tsv's granule shift |
| 114 | A/AF0l.v:13 | 14 | Definition Tfib_code (10) | hex | 0x51c98 | 0x0 | K-ABSENT0 | absent entry = 0; override |
| 115 | A/AF0l.v:14 | 15 | Definition Tfib_code (14) | hex | 0x42144 | 0x0 | K-ABSENT0 | absent entry = 0; override |
| 24 | A/AB1w.v:11 | 12 | Definition tfib_text_hi (0) | hex | 0x9b168 | 0x95a88 | K-TLS | tls.lo (both) |
| 25 | A/AB1w.v:20 | 21 | Definition tfib_tbss_lo (0) | hex | 0x9b168 | 0x95a88 | K-TLS | tls.lo (both) |

### NO-COUNTERPART (1 row; FLAGGED says 1)

Reasons: THUNK (1).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 83 | A/AB1w.v:540 | 564 | Definition tfib_E_thunk_95368 (1) | hex | 0x95930 | 0x92978 | THUNK | src memchr+0x0 (bcmp row, absent in fuzz_uci) judged against dst line 564 __set_thread_area+0x0 / __set_thread_area+0x0 = dst's own thunk_96f9c row |

### NON-ADDRESS-CHANGED (174 rows; FLAGGED says 174)

Reasons: N-FMTPTR (113), N-REGCNT (44), N-RA3 (3), N-RANGES (3), N-IAL (2), N-CELLPATCH (2), FMTWIN (2), N-AD1o-BSS20 (1), N-AD1o-TOP (1), N-AD1o-ZLEN (1), N-DEPOT (1), N-INST (1).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 237 | A/AE2t.v:63 | 64 | Definition SH_HI (0) | hex | 0x7fffbb00 | 0x7fffbac0 | FMTWIN | format "cli: cannot open %s\n" (len 20) src @0x1d7b0, dst @0x1d5e6: SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8 = src 0x7fffbb00, dst 0x7fffbac0; override row |
| 248 | A/AE35.v:64 | 65 | Definition SH_HI (0) | hex | 0x7fffa910 | 0x7fffa8f0 | FMTWIN | format "%d\n" (len 3) src @0x14863, dst @0x14763: SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8 = src 0x7fffa910, dst 0x7fffa8f0; no override row: written by port_core's review rule `shadow-window SH_LO/SH_HI (target string at ...)` (review.tsv), which corrected check.tsv's granule shift |
| 100 | A/AD1o.v:94 | 95 | Lemma bss_shadow_facts / sentence 12 (2) | dec | 0x14294 | 0x1372c | N-AD1o-BSS20 | 0x9b960/8; override |
| 101 | A/AD1o.v:94 | 95 | Lemma bss_shadow_facts / sentence 13 (3) | dec | 0xbf3ff | 0xbe7ff | N-AD1o-TOP | (0x5f4000-1)/8 |
| 102 | A/AD1o.v:99 | 100 | Lemma bss_shadow_facts / sentence 22 (3) | dec | 0xab174 | 0xab0de | N-AD1o-ZLEN | (0x5f4000-0x9b910)/8; override |
| 168 | A/AFim.v:500 | 501 | Lemma HSN / sentence 30 (0) | dec | 0x3c | 0x1 | N-CELLPATCH | index 60 vs offset +1 (cell-lookup.patch) |
| 169 | A/AFin.v:490 | 491 | Lemma HSN / sentence 30 (0) | dec | 0x3c | 0x1 | N-CELLPATCH | index 60 vs offset +1 (cell-lookup.patch) |
| 119 | A/AFem.v:412 | 413 | Lemma FACTS_fixed / sentence 32 (0) | dec | 0x61a86 | 0x603b6 | N-DEPOT | TFIB_DEPOT/4 |
| 249 | A/AE3j.v:253 | 254 | Theorem tfib_vfprintf_open_A1 / sentence 97 (0) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 250 | A/AE3j.v:254 | 255 | Theorem tfib_vfprintf_open_A1 / sentence 98 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 251 | A/AE3j.v:256 | 257 | Theorem tfib_vfprintf_open_A1 / sentence 99 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 252 | A/AE3j.v:256 | 257 | Theorem tfib_vfprintf_open_A1 / sentence 99 (3) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 253 | A/AE3j.v:506 | 507 | Theorem tfib_vfprintf_open_A1 / sentence 403 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 254 | A/AE3j.v:507 | 508 | Theorem tfib_vfprintf_open_A1 / sentence 405 (0) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 255 | A/AE3j.v:507 | 508 | Theorem tfib_vfprintf_open_A1 / sentence 405 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 256 | A/AE3j.v:509 | 510 | Theorem tfib_vfprintf_open_A1 / sentence 407 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 257 | A/AE3j.v:513 | 514 | Theorem tfib_vfprintf_open_A1 / sentence 408 (7) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 258 | A/AE3j.v:513 | 514 | Theorem tfib_vfprintf_open_A1 / sentence 408 (10) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 259 | A/AE3j.v:525 | 526 | Theorem tfib_vfprintf_open_A1 / sentence 408 (12) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 260 | A/AE3j.v:525 | 526 | Theorem tfib_vfprintf_open_A1 / sentence 408 (13) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 261 | A/AE3j.v:525 | 526 | Theorem tfib_vfprintf_open_A1 / sentence 408 (14) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 262 | A/AE3j.v:826 | 827 | Theorem tfib_vfprintf_open_A2 / sentence 97 (0) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 263 | A/AE3j.v:827 | 828 | Theorem tfib_vfprintf_open_A2 / sentence 98 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 264 | A/AE3j.v:829 | 830 | Theorem tfib_vfprintf_open_A2 / sentence 99 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 265 | A/AE3j.v:829 | 830 | Theorem tfib_vfprintf_open_A2 / sentence 99 (3) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 266 | A/AE3j.v:1085 | 1086 | Theorem tfib_vfprintf_open_A2 / sentence 409 (0) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 267 | A/AE3j.v:1087 | 1088 | Theorem tfib_vfprintf_open_A2 / sentence 410 (9) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 268 | A/AE3j.v:1118 | 1119 | Theorem tfib_vfprintf_open_A2 / sentence 473 (0) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 269 | A/AE3j.v:1118 | 1119 | Theorem tfib_vfprintf_open_A2 / sentence 473 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 270 | A/AE3j.v:1119 | 1120 | Theorem tfib_vfprintf_open_A2 / sentence 477 (0) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 271 | A/AE3j.v:1119 | 1120 | Theorem tfib_vfprintf_open_A2 / sentence 477 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 272 | A/AE3j.v:1350 | 1351 | Theorem tfib_vfprintf_open_A3 / sentence 97 (0) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 273 | A/AE3j.v:1351 | 1352 | Theorem tfib_vfprintf_open_A3 / sentence 98 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 274 | A/AE3j.v:1353 | 1354 | Theorem tfib_vfprintf_open_A3 / sentence 99 (2) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 275 | A/AE3j.v:1353 | 1354 | Theorem tfib_vfprintf_open_A3 / sentence 99 (3) | dec | 0x1d7c1 | 0x1d5f7 | N-FMTPTR | "cli: cannot open %s\n"+17 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 276 | A/AE3j.v:1600 | 1601 | Theorem tfib_vfprintf_open_A3 / sentence 429 (1) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 277 | A/AE3j.v:1603 | 1604 | Theorem tfib_vfprintf_open_A3 / sentence 430 (2) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 278 | A/AE3j.v:1603 | 1604 | Theorem tfib_vfprintf_open_A3 / sentence 430 (3) | dec | 0x1d7c3 | 0x1d5f9 | N-FMTPTR | "cli: cannot open %s\n"+19 (string @0x1d7b0 src, @0x1d5e6 dst; bytes equal) |
| 279 | A/AE3k.v:253 | 254 | Theorem tfib_vfprintf_rderr_A1 / sentence 97 (0) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 280 | A/AE3k.v:254 | 255 | Theorem tfib_vfprintf_rderr_A1 / sentence 98 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 281 | A/AE3k.v:256 | 257 | Theorem tfib_vfprintf_rderr_A1 / sentence 99 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 282 | A/AE3k.v:256 | 257 | Theorem tfib_vfprintf_rderr_A1 / sentence 99 (3) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 283 | A/AE3k.v:506 | 507 | Theorem tfib_vfprintf_rderr_A1 / sentence 403 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 284 | A/AE3k.v:507 | 508 | Theorem tfib_vfprintf_rderr_A1 / sentence 405 (0) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 285 | A/AE3k.v:507 | 508 | Theorem tfib_vfprintf_rderr_A1 / sentence 405 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 286 | A/AE3k.v:509 | 510 | Theorem tfib_vfprintf_rderr_A1 / sentence 407 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 287 | A/AE3k.v:513 | 514 | Theorem tfib_vfprintf_rderr_A1 / sentence 408 (7) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 288 | A/AE3k.v:513 | 514 | Theorem tfib_vfprintf_rderr_A1 / sentence 408 (10) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 289 | A/AE3k.v:525 | 526 | Theorem tfib_vfprintf_rderr_A1 / sentence 408 (12) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 290 | A/AE3k.v:525 | 526 | Theorem tfib_vfprintf_rderr_A1 / sentence 408 (13) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 291 | A/AE3k.v:525 | 526 | Theorem tfib_vfprintf_rderr_A1 / sentence 408 (14) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 292 | A/AE3k.v:826 | 827 | Theorem tfib_vfprintf_rderr_A2 / sentence 97 (0) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 293 | A/AE3k.v:827 | 828 | Theorem tfib_vfprintf_rderr_A2 / sentence 98 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 294 | A/AE3k.v:829 | 830 | Theorem tfib_vfprintf_rderr_A2 / sentence 99 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 295 | A/AE3k.v:829 | 830 | Theorem tfib_vfprintf_rderr_A2 / sentence 99 (3) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 296 | A/AE3k.v:1085 | 1086 | Theorem tfib_vfprintf_rderr_A2 / sentence 409 (0) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 297 | A/AE3k.v:1087 | 1088 | Theorem tfib_vfprintf_rderr_A2 / sentence 410 (9) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 298 | A/AE3k.v:1118 | 1119 | Theorem tfib_vfprintf_rderr_A2 / sentence 473 (0) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 299 | A/AE3k.v:1118 | 1119 | Theorem tfib_vfprintf_rderr_A2 / sentence 473 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 300 | A/AE3k.v:1119 | 1120 | Theorem tfib_vfprintf_rderr_A2 / sentence 477 (0) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 301 | A/AE3k.v:1119 | 1120 | Theorem tfib_vfprintf_rderr_A2 / sentence 477 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 302 | A/AE3k.v:1350 | 1351 | Theorem tfib_vfprintf_rderr_A3 / sentence 97 (0) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 303 | A/AE3k.v:1351 | 1352 | Theorem tfib_vfprintf_rderr_A3 / sentence 98 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 304 | A/AE3k.v:1353 | 1354 | Theorem tfib_vfprintf_rderr_A3 / sentence 99 (2) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 305 | A/AE3k.v:1353 | 1354 | Theorem tfib_vfprintf_rderr_A3 / sentence 99 (3) | dec | 0x1d7d8 | 0x1d60e | N-FMTPTR | "cli: read error on %s\n"+19 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 306 | A/AE3k.v:1600 | 1601 | Theorem tfib_vfprintf_rderr_A3 / sentence 429 (1) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 307 | A/AE3k.v:1603 | 1604 | Theorem tfib_vfprintf_rderr_A3 / sentence 430 (2) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 308 | A/AE3k.v:1603 | 1604 | Theorem tfib_vfprintf_rderr_A3 / sentence 430 (3) | dec | 0x1d7da | 0x1d610 | N-FMTPTR | "cli: read error on %s\n"+21 (string @0x1d7c5 src, @0x1d5fb dst; bytes equal) |
| 309 | A/AE3l.v:178 | 179 | Theorem tfib_vfprintf_refused / sentence 92 (1) | dec | 0x1977b | 0x19622 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+14 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 310 | A/AE3l.v:181 | 182 | Theorem tfib_vfprintf_refused / sentence 93 (2) | dec | 0x1977b | 0x19622 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+14 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 311 | A/AE3l.v:181 | 182 | Theorem tfib_vfprintf_refused / sentence 93 (3) | dec | 0x1977b | 0x19622 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+14 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 312 | A/AE3l.v:310 | 311 | Theorem tfib_vfprintf_refused / sentence 228 (1) | dec | 0x1977d | 0x19624 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+16 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 313 | A/AE3l.v:313 | 314 | Theorem tfib_vfprintf_refused / sentence 229 (2) | dec | 0x1977d | 0x19624 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+16 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 314 | A/AE3l.v:313 | 314 | Theorem tfib_vfprintf_refused / sentence 229 (3) | dec | 0x1977d | 0x19624 | N-FMTPTR | "cli: input >= %u bytes, refused\n"+16 (string @0x1976d src, @0x19614 dst; bytes equal) |
| 315 | A/AE3m.v:885 | 886 | Theorem tfib_vfprintf_stdout_first / sentence 346 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 316 | A/AE3m.v:888 | 889 | Theorem tfib_vfprintf_stdout_first / sentence 348 (6) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 317 | A/AE3m.v:913 | 914 | Theorem tfib_vfprintf_stdout_first / sentence 407 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 318 | A/AE3m.v:913 | 914 | Theorem tfib_vfprintf_stdout_first / sentence 407 (1) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 319 | A/AE3m.v:914 | 915 | Theorem tfib_vfprintf_stdout_first / sentence 411 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 320 | A/AE3m.v:914 | 915 | Theorem tfib_vfprintf_stdout_first / sentence 411 (1) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 321 | A/AE3m.v:951 | 952 | Theorem tfib_vfprintf_stdout_first / sentence 473 (0) | dec | 0x14866 | 0x14766 | N-FMTPTR | "%d\n"+3 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 322 | A/AE3m.v:952 | 953 | Theorem tfib_vfprintf_stdout_first / sentence 474 (2) | dec | 0x14866 | 0x14766 | N-FMTPTR | "%d\n"+3 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 323 | A/AE3m.v:955 | 956 | Theorem tfib_vfprintf_stdout_first / sentence 475 (1) | dec | 0x14866 | 0x14766 | N-FMTPTR | "%d\n"+3 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 324 | A/AE3m.v:1434 | 1435 | Theorem tfib_vfprintf_stdout_next / sentence 421 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 325 | A/AE3m.v:1435 | 1436 | Theorem tfib_vfprintf_stdout_next / sentence 422 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 326 | A/AE3m.v:1435 | 1436 | Theorem tfib_vfprintf_stdout_next / sentence 422 (1) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 327 | A/AE3m.v:1436 | 1437 | Theorem tfib_vfprintf_stdout_next / sentence 423 (0) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 328 | A/AE3m.v:1436 | 1437 | Theorem tfib_vfprintf_stdout_next / sentence 423 (1) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 329 | A/AE3m.v:1438 | 1439 | Theorem tfib_vfprintf_stdout_next / sentence 425 (2) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 330 | A/AE3m.v:1444 | 1445 | Theorem tfib_vfprintf_stdout_next / sentence 427 (3) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 331 | A/AE3m.v:1459 | 1460 | Theorem tfib_vfprintf_stdout_next / sentence 427 (10) | dec | 0x14865 | 0x14765 | N-FMTPTR | "%d\n"+2 (string @0x14863 src, @0x14763 dst; bytes equal) |
| 332 | A/AE3n.v:256 | 257 | Theorem tfib_vfprintf_usage_A1 / sentence 97 (0) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 333 | A/AE3n.v:257 | 258 | Theorem tfib_vfprintf_usage_A1 / sentence 98 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 334 | A/AE3n.v:259 | 260 | Theorem tfib_vfprintf_usage_A1 / sentence 99 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 335 | A/AE3n.v:259 | 260 | Theorem tfib_vfprintf_usage_A1 / sentence 99 (3) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 336 | A/AE3n.v:509 | 510 | Theorem tfib_vfprintf_usage_A1 / sentence 403 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 337 | A/AE3n.v:510 | 511 | Theorem tfib_vfprintf_usage_A1 / sentence 405 (0) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 338 | A/AE3n.v:510 | 511 | Theorem tfib_vfprintf_usage_A1 / sentence 405 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 339 | A/AE3n.v:512 | 513 | Theorem tfib_vfprintf_usage_A1 / sentence 407 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 340 | A/AE3n.v:516 | 517 | Theorem tfib_vfprintf_usage_A1 / sentence 408 (7) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 341 | A/AE3n.v:516 | 517 | Theorem tfib_vfprintf_usage_A1 / sentence 408 (10) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 342 | A/AE3n.v:528 | 529 | Theorem tfib_vfprintf_usage_A1 / sentence 408 (12) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 343 | A/AE3n.v:528 | 529 | Theorem tfib_vfprintf_usage_A1 / sentence 408 (13) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 344 | A/AE3n.v:528 | 529 | Theorem tfib_vfprintf_usage_A1 / sentence 408 (14) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 345 | A/AE3n.v:829 | 830 | Theorem tfib_vfprintf_usage_A2 / sentence 97 (0) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 346 | A/AE3n.v:830 | 831 | Theorem tfib_vfprintf_usage_A2 / sentence 98 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 347 | A/AE3n.v:832 | 833 | Theorem tfib_vfprintf_usage_A2 / sentence 99 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 348 | A/AE3n.v:832 | 833 | Theorem tfib_vfprintf_usage_A2 / sentence 99 (3) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 349 | A/AE3n.v:1106 | 1107 | Theorem tfib_vfprintf_usage_A2 / sentence 444 (0) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 350 | A/AE3n.v:1108 | 1109 | Theorem tfib_vfprintf_usage_A2 / sentence 445 (9) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 351 | A/AE3n.v:1139 | 1140 | Theorem tfib_vfprintf_usage_A2 / sentence 508 (0) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 352 | A/AE3n.v:1139 | 1140 | Theorem tfib_vfprintf_usage_A2 / sentence 508 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 353 | A/AE3n.v:1140 | 1141 | Theorem tfib_vfprintf_usage_A2 / sentence 512 (0) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 354 | A/AE3n.v:1140 | 1141 | Theorem tfib_vfprintf_usage_A2 / sentence 512 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 355 | A/AE3n.v:1371 | 1372 | Theorem tfib_vfprintf_usage_A3 / sentence 97 (0) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 356 | A/AE3n.v:1372 | 1373 | Theorem tfib_vfprintf_usage_A3 / sentence 98 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 357 | A/AE3n.v:1374 | 1375 | Theorem tfib_vfprintf_usage_A3 / sentence 99 (2) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 358 | A/AE3n.v:1374 | 1375 | Theorem tfib_vfprintf_usage_A3 / sentence 99 (3) | dec | 0x1590c | 0x157d4 | N-FMTPTR | "usage: %s INPUT\n"+7 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 359 | A/AE3n.v:1621 | 1622 | Theorem tfib_vfprintf_usage_A3 / sentence 429 (1) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 360 | A/AE3n.v:1624 | 1625 | Theorem tfib_vfprintf_usage_A3 / sentence 430 (2) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 361 | A/AE3n.v:1624 | 1625 | Theorem tfib_vfprintf_usage_A3 / sentence 430 (3) | dec | 0x1590e | 0x157d6 | N-FMTPTR | "usage: %s INPUT\n"+9 (string @0x15905 src, @0x157cd dst; bytes equal) |
| 166 | A/AFfu.v:409 | 410 | Lemma p_facts / sentence 38 (0) | dec | 0x14ba8 | 0x14040 | N-IAL | internal_alloc_placeholder/8 |
| 167 | A/AFg1.v:297 | 298 | Lemma p_facts / sentence 38 (0) | dec | 0x14ba8 | 0x14040 | N-IAL | internal_alloc_placeholder/8 |
| 174 | A/AFjr.v:627 | 628 | Lemma FS2_ok / sentence 48 (3) | dec | 0x142b0 | 0x13748 | N-INST | (TFIB_INST+168)/8 |
| 107 | A/AD28.v:293 | 294 | Lemma imgs_of_R / sentence 5 (2) | dec | 0x340 | 0x348 | N-RA3 | 832 -> 840 |
| 108 | A/AD28.v:294 | 295 | Lemma imgs_of_R / sentence 6 (1) | dec | 0x340 | 0x348 | N-RA3 | 832 -> 840 |
| 209 | A/AD2d.v:131 | 132 | Lemma img_facts_of / sentence 6 (1) | dec | 0x340 | 0x348 | N-RA3 | 832 -> 840 |
| 244 | A/AE34.v:26 | 27 | Definition icpt_ranges (1) | dec | 0x26 | 0x25 | N-RANGES | (0x42130, 38) -> (0x41068, 37): 38 trampoline/stub words from __interceptor_trampoline_strlen minus the 1-word __interceptor_trampoline_bcmp (absent); the 37 dst words equal the 37 src words modulo jal/auipc/I-type immediates; review.tsv `range-split` |
| 245 | A/AE34.v:26 | 27 | Definition icpt_ranges (7) | dec | 0x5e | 0x2f | N-RANGES | (0x43794, 94) -> (0x426c8, 47): ___interceptor_memcmp (0xbc) + ___interceptor_bcmp (0xbc) = 94 words; dst has only ___interceptor_memcmp (0xbc) = 47 words, equal modulo relocation immediates; review.tsv `range-split` |
| 246 | A/AE34.v:28 | 29 | Definition icpt_ranges (23) | dec | 0x3f1 | 0x361 | N-RANGES | (0x517f4, 1009) -> (0x5066c, 865): trampolines memset/memcpy + __asan_memcpy + __asan_memset (0x240 = 144 words) + ___interceptor_memset + ___interceptor_memcpy; dst lacks __asan_memset: 1009 - 144 = 865 words, equal modulo relocation immediates; dst range ends at ___interceptor_memcpy end 0x513f0; review.tsv `range-split` |
| 103 | A/AD27.v:69 | 70 | Lemma img_sub_COf / sentence 2 (1) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 104 | A/AD27.v:74 | 75 | Lemma img_sub_US / sentence 2 (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 105 | A/AD27.v:94 | 95 | Lemma img_sub_FW / sentence 3 (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 106 | A/AD27.v:96 | 97 | Lemma img_sub_FW / sentence 6 (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 109 | A/AD2h.v:64 | 65 | Lemma img_sub_SHORT / sentence 2 (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 110 | A/AD2h.v:69 | 70 | Lemma img_sub_OVR / sentence 2 (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 196 | A/AD1x.v:25 | 26 | Lemma IMG_X_wf (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 197 | A/AD1x.v:26 | 27 | Lemma IMG_X_wf (2) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 198 | A/AD22.v:20 | 21 | Lemma skipn3_dir (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 199 | A/AD22.v:20 | 21 | Lemma skipn3_dir (2) | dec | 0x27 | 0x25 | N-REGCNT | 39 -> 37 |
| 200 | A/AD27.v:87 | 88 | Lemma FW_facts (31) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 201 | A/AD28.v:105 | 106 | Lemma S_COf_mem (6) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 202 | A/AD28.v:106 | 107 | Lemma S_COf_mem (7) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 203 | A/AD28.v:106 | 107 | Lemma S_COf_mem (8) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 204 | A/AD28.v:106 | 107 | Lemma S_COf_mem (10) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 205 | A/AD28.v:107 | 108 | Lemma S_COf_mem (12) | dec | 0x26 | 0x24 | N-REGCNT | 38 -> 36 |
| 206 | A/AD28.v:109 | 110 | Lemma S_US_mem (6) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 207 | A/AD2d.v:24 | 25 | Definition B0_r5 (0) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 208 | A/AD2d.v:25 | 26 | Definition B1_r5 (0) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 210 | A/AD2e.v:63 | 64 | Definition PM_tailL (0) | dec | 0x23 | 0x21 | N-REGCNT | 35 -> 33 |
| 211 | A/AD2e.v:68 | 69 | Lemma PM_pieces_eq (0) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 212 | A/AD2e.v:68 | 69 | Lemma PM_pieces_eq (2) | dec | 0x25 | 0x23 | N-REGCNT | 37 -> 35 |
| 213 | A/AD2e.v:192 | 193 | Lemma rs_PM_sub / sentence 8 (0) | dec | 0x23 | 0x21 | N-REGCNT | 35 -> 33 |
| 214 | A/AD2f.v:58 | 59 | Definition IMG_E (0) | dec | 0x21 | 0x1f | N-REGCNT | 33 -> 31 |
| 215 | A/AD2f.v:67 | 68 | Lemma S_Pm_layout (0) | dec | 0x27 | 0x25 | N-REGCNT | 39 -> 37 |
| 216 | A/AD2f.v:67 | 68 | Lemma S_Pm_layout (1) | dec | 0x21 | 0x1f | N-REGCNT | 33 -> 31 |
| 217 | A/AD2f.v:67 | 68 | Lemma S_Pm_layout (3) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 218 | A/AD2f.v:85 | 86 | Lemma sPE0_facts (13) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 219 | A/AD2f.v:94 | 95 | Lemma sPE1_facts (12) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 221 | A/AD2f.v:148 | 149 | Definition IMG_B (0) | dec | 0x21 | 0x1f | N-REGCNT | 33 -> 31 |
| 222 | A/AD2f.v:167 | 168 | Lemma L_mem_wf (0) | dec | 0x23 | 0x21 | N-REGCNT | 35 -> 33 |
| 223 | A/AD2f.v:169 | 170 | Lemma IMG_LC_len (0) | dec | 0x23 | 0x21 | N-REGCNT | 35 -> 33 |
| 224 | A/AD2f.v:184 | 185 | Lemma sPE_mem (1) | dec | 0x24 | 0x22 | N-REGCNT | 36 -> 34 |
| 225 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (0) | dec | 0x18 | 0x16 | N-REGCNT | 24 -> 22 |
| 226 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (1) | dec | 0x18 | 0x16 | N-REGCNT | 24 -> 22 |
| 227 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (3) | dec | 0x19 | 0x17 | N-REGCNT | 25 -> 23 |
| 228 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (6) | dec | 0x1d | 0x1b | N-REGCNT | 29 -> 27 |
| 229 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (7) | dec | 0x1d | 0x1b | N-REGCNT | 29 -> 27 |
| 230 | A/AD2f.v:196 | 197 | Lemma IMG_B_eq (8) | dec | 0x21 | 0x1f | N-REGCNT | 33 -> 31 |
| 231 | A/AD2f.v:197 | 198 | Lemma IMG_B_eq (9) | dec | 0x18 | 0x16 | N-REGCNT | 24 -> 22 |
| 232 | A/AD2f.v:197 | 198 | Lemma IMG_B_eq (10) | dec | 0x18 | 0x16 | N-REGCNT | 24 -> 22 |
| 233 | A/AD2f.v:197 | 198 | Lemma IMG_B_eq (11) | dec | 0x19 | 0x17 | N-REGCNT | 25 -> 23 |
| 234 | A/AD2f.v:197 | 198 | Lemma IMG_B_eq (12) | dec | 0x19 | 0x17 | N-REGCNT | 25 -> 23 |
| 235 | A/AD2f.v:197 | 198 | Lemma IMG_B_eq (13) | dec | 0x21 | 0x1f | N-REGCNT | 33 -> 31 |

### SAME-VALUE-DIFFERENT-OBJECT (20 rows; FLAGGED says 20)

Reasons: SV-MMAP (18), SV-HWCAP (2).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 190 | Reusable/YA01.v:715 | 716 | Definition init_kn_g (3) | hex | 0x20112d | 0x20112d | SV-HWCAP | hwcap range [0x112D, 0x20112D]; value unchanged |
| 191 | Reusable/YA02.v:741 | 742 | Lemma hw_facts_ok (1) | hex | 0x20112d | 0x20112d | SV-HWCAP | hwcap range [0x112D, 0x20112D]; value unchanged |
| 182 | Reusable/YA01.v:299 | 300 | Definition node_mmap2g (11) | hex | 0x104022 | 0x104022 | SV-MMAP | 0x104022 = MAP_PRIVATE + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 183 | Reusable/YA01.v:299 | 300 | Definition node_mmap2g (13) | hex | 0x104032 | 0x104032 | SV-MMAP | 0x104032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 184 | Reusable/YA01.v:300 | 301 | Definition node_mmap2g (17) | hex | 0x100022 | 0x100022 | SV-MMAP | 0x100022 = MAP_PRIVATE + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 185 | Reusable/YA01.v:300 | 301 | Definition node_mmap2g (19) | hex | 0x100032 | 0x100032 | SV-MMAP | 0x100032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 186 | Reusable/YA01.v:301 | 302 | Definition node_mmap2g (23) | hex | 0x104022 | 0x104022 | SV-MMAP | 0x104022 = MAP_PRIVATE + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 187 | Reusable/YA01.v:301 | 302 | Definition node_mmap2g (25) | hex | 0x104032 | 0x104032 | SV-MMAP | 0x104032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 188 | Reusable/YA01.v:302 | 303 | Definition node_mmap2g (29) | hex | 0x100022 | 0x100022 | SV-MMAP | 0x100022 = MAP_PRIVATE + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 189 | Reusable/YA01.v:302 | 303 | Definition node_mmap2g (31) | hex | 0x100032 | 0x100032 | SV-MMAP | 0x100032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 192 | Reusable/YA09.v:1271 | 1272 | Lemma ff_class_100022 (1) | hex | 0x100022 | 0x100022 | SV-MMAP | 0x100022 = MAP_PRIVATE + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 193 | Reusable/YA09.v:1272 | 1273 | Lemma ff_class_100032 (1) | hex | 0x100032 | 0x100032 | SV-MMAP | 0x100032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 194 | Reusable/YA09.v:1273 | 1274 | Lemma ff_class_104022 (1) | hex | 0x104022 | 0x104022 | SV-MMAP | 0x104022 = MAP_PRIVATE + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 195 | Reusable/YA09.v:1274 | 1275 | Lemma ff_class_104032 (1) | hex | 0x104032 | 0x104032 | SV-MMAP | 0x104032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 385 | Reusable/YA09.v:402 | 403 | Lemma mmap_noreserve_b_100022 (2) | hex | 0x100022 | 0x100022 | SV-MMAP | 0x100022 = MAP_PRIVATE + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 386 | Reusable/YA09.v:403 | 404 | Lemma mmap_noreserve_b_100032 (2) | hex | 0x100032 | 0x100032 | SV-MMAP | 0x100032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 387 | Reusable/YA09.v:404 | 405 | Lemma mmap_noreserve_b_104022 (2) | hex | 0x104022 | 0x104022 | SV-MMAP | 0x104022 = MAP_PRIVATE + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 388 | Reusable/YA09.v:405 | 406 | Lemma mmap_noreserve_b_104032 (2) | hex | 0x104032 | 0x104032 | SV-MMAP | 0x104032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + MAP_NORESERVE + 0x100000 (noreplace); value unchanged |
| 389 | Reusable/YA09.v:430 | 431 | Definition noreplace_core (0) | hex | 0x100022 | 0x100022 | SV-MMAP | 0x100022 = MAP_PRIVATE + MAP_ANON + 0x100000 (noreplace); value unchanged |
| 390 | Reusable/YA09.v:430 | 431 | Definition noreplace_core (1) | hex | 0x100032 | 0x100032 | SV-MMAP | 0x100032 = MAP_PRIVATE + MAP_FIXED + MAP_ANON + 0x100000 (noreplace); value unchanged |

### STALE-DONOR-CODE-POINTER (1 row; FLAGGED says 1)

Reasons: THUNK (1).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 82 | A/AB1w.v:540 | 564 | Definition tfib_A_thunk_95368 (1) | hex | 0x9592c | 0x92970 | THUNK | src bcmp+0x0 (bcmp row, absent in fuzz_uci) judged against dst line 564 pthread_testcancel+0x0 / __pthread_testcancel+0x0 = dst's own thunk_96f9c row |

### UNPAIRED-PORTED (40 rows; FLAGGED says 40)

Reasons: PATCH-ZS (30), P-UCIPROG (10).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 90 | A/AB1w.v:- | 87 | Definition tfib_A_check_no_overread (-) | hex | - | 0x7f4fc | P-UCIPROG | dst check_no_overread+0x0 (size 0x130); src symtab has no check_no_overread |
| 91 | A/AB1w.v:- | 87 | Definition tfib_E_check_no_overread (-) | hex | - | 0x7f62c | P-UCIPROG | dst check_no_overread ends here (check_value+0x0); src symtab has no check_no_overread |
| 92 | A/AB1w.v:- | 87 | Definition tfib_A_check_value (-) | hex | - | 0x7f62c | P-UCIPROG | dst check_value+0x0 (size 0x25c); src symtab has no check_value |
| 93 | A/AB1w.v:- | 87 | Definition tfib_E_check_value (-) | hex | - | 0x7f888 | P-UCIPROG | dst check_value ends here (check_clamp+0x0); src symtab has no check_value |
| 94 | A/AB1w.v:- | 87 | Definition tfib_A_check_clamp (-) | hex | - | 0x7f888 | P-UCIPROG | dst check_clamp+0x0 (size 0x374); src symtab has no check_clamp |
| 95 | A/AB1w.v:- | 87 | Definition tfib_E_check_clamp (-) | hex | - | 0x7fbfc | P-UCIPROG | dst check_clamp ends here (asan.module_ctor+0x0); src symtab has no check_clamp |
| 96 | A/AB1w.v:- | 87 | Definition tfib_A_rp_hot_clamp (-) | hex | - | 0x7fc64 | P-UCIPROG | dst rp_hot_clamp+0x0 (size 0x28c); src symtab has no rp_hot_clamp |
| 97 | A/AB1w.v:- | 87 | Definition tfib_E_rp_hot_clamp (-) | hex | - | 0x7fef0 | P-UCIPROG | dst rp_hot_clamp ends here (rp_uci_int+0x0); src symtab has no rp_hot_clamp |
| 98 | A/AB1w.v:- | 87 | Definition tfib_A_rp_uci_int (-) | hex | - | 0x7fef0 | P-UCIPROG | dst rp_uci_int+0x0 (size 0x214); src symtab has no rp_uci_int |
| 99 | A/AB1w.v:- | 87 | Definition tfib_E_rp_uci_int (-) | hex | - | 0x80104 | P-UCIPROG | dst rp_uci_int ends here (__wrap_getenv+0x0); src symtab has no rp_uci_int |
| 129 | A/AFex.v:- | 939 | Lemma zshadow' / sentence 35 (-) | dec | - | 0x8 | PATCH-ZS | dst line 939 = src line 938 (same text, sentence index shifted); literal 8 |
| 130 | A/AFex.v:- | 939 | Lemma zshadow' / sentence 35 (-) | dec | - | 0x0 | PATCH-ZS | dst line 939 = src line 938 (same text, sentence index shifted); literal 0 |
| 131 | A/AFex.v:- | 945 | Lemma zshadow' / sentence 50 (-) | dec | - | 0x8 | PATCH-ZS | dst line 945 = src line 942 (same text, sentence index shifted); literal 8 |
| 132 | A/AFex.v:- | 946 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 946 = src line 943 (same text, sentence index shifted); literal 8 |
| 133 | A/AFex.v:- | 946 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 946 = src line 943 (same text, sentence index shifted); literal 8 |
| 134 | A/AFex.v:- | 946 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 946 = src line 943 (same text, sentence index shifted); literal 8 |
| 135 | A/AFex.v:- | 947 | Lemma zshadow' / sentence 57 (-) | dec | - | 0x8 | PATCH-ZS | dst line 947 = src line 944 (same text, sentence index shifted); literal 8 |
| 136 | A/AFex.v:- | 949 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 949 = src line 946 (same text, sentence index shifted); literal 8 |
| 137 | A/AFex.v:- | 949 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 949 = src line 946 (same text, sentence index shifted); literal 8 |
| 138 | A/AFex.v:- | 949 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 949 = src line 946 (same text, sentence index shifted); literal 8 |
| 139 | A/AFex.v:- | 949 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 949 = src line 946 (same text, sentence index shifted); literal 8 |
| 140 | A/AFf0.v:- | 470 | Lemma zshadow' / sentence 28 (-) | dec | - | 0x8 | PATCH-ZS | dst line 470 added by the patch; literal 8 |
| 141 | A/AFf3.v:- | 647 | Lemma zshadow' / sentence 39 (-) | dec | - | 0x8 | PATCH-ZS | dst line 647 added by the patch; literal 8 |
| 142 | A/AFf4.v:- | 897 | Lemma zshadow' / sentence 32 (-) | dec | - | 0x8 | PATCH-ZS | dst line 897 added by the patch; literal 8 |
| 143 | A/AFf4.v:- | 897 | Lemma zshadow' / sentence 32 (-) | dec | - | 0x8 | PATCH-ZS | dst line 897 added by the patch; literal 8 |
| 144 | A/AFf4.v:- | 897 | Lemma zshadow' / sentence 32 (-) | dec | - | 0x8 | PATCH-ZS | dst line 897 added by the patch; literal 8 |
| 155 | A/AFfl.v:- | 829 | Lemma zshadow' / sentence 35 (-) | dec | - | 0x8 | PATCH-ZS | dst line 829 = src line 828 (same text, sentence index shifted); literal 8 |
| 156 | A/AFfl.v:- | 829 | Lemma zshadow' / sentence 35 (-) | dec | - | 0x0 | PATCH-ZS | dst line 829 = src line 828 (same text, sentence index shifted); literal 0 |
| 157 | A/AFfl.v:- | 835 | Lemma zshadow' / sentence 50 (-) | dec | - | 0x8 | PATCH-ZS | dst line 835 = src line 832 (same text, sentence index shifted); literal 8 |
| 158 | A/AFfl.v:- | 836 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 836 = src line 833 (same text, sentence index shifted); literal 8 |
| 159 | A/AFfl.v:- | 836 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 836 = src line 833 (same text, sentence index shifted); literal 8 |
| 160 | A/AFfl.v:- | 836 | Lemma zshadow' / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 836 = src line 833 (same text, sentence index shifted); literal 8 |
| 161 | A/AFfl.v:- | 837 | Lemma zshadow' / sentence 57 (-) | dec | - | 0x8 | PATCH-ZS | dst line 837 = src line 834 (same text, sentence index shifted); literal 8 |
| 162 | A/AFfl.v:- | 839 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 839 = src line 836 (same text, sentence index shifted); literal 8 |
| 163 | A/AFfl.v:- | 839 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 839 = src line 836 (same text, sentence index shifted); literal 8 |
| 164 | A/AFfl.v:- | 839 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 839 = src line 836 (same text, sentence index shifted); literal 8 |
| 165 | A/AFfl.v:- | 839 | Lemma zshadow' / sentence 60 (-) | dec | - | 0x8 | PATCH-ZS | dst line 839 = src line 836 (same text, sentence index shifted); literal 8 |
| 178 | A/AFjy.v:- | 1600 | Lemma zshadow_final / sentence 51 (-) | dec | - | 0x8 | PATCH-ZS | dst line 1600 = src line 1597 (same text, sentence index shifted); literal 8 |
| 179 | A/AFjy.v:- | 1600 | Lemma zshadow_final / sentence 52 (-) | dec | - | 0x8 | PATCH-ZS | dst line 1600 = src line 1597 (same text, sentence index shifted); literal 8 |
| 180 | A/AFjy.v:- | 1600 | Lemma zshadow_final / sentence 53 (-) | dec | - | 0x8 | PATCH-ZS | dst line 1600 = src line 1597 (same text, sentence index shifted); literal 8 |

### UNPAIRED-SOURCE (105 rows; FLAGGED says 105)

Reasons: S-GRANTPROG (44), PATCH-ZS (39), S-ABSENTRT (12), S-AF0L (6), THUNK (4).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 120 | A/AFex.v:942 | - | Lemma zshadow' / sentence 42 (-) | dec | 0x8 | - | PATCH-ZS | src line 942 = dst line 945 (same text, sentence index shifted); literal 8 |
| 121 | A/AFex.v:943 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 943 = dst line 946 (same text, sentence index shifted); literal 8 |
| 122 | A/AFex.v:943 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 943 = dst line 946 (same text, sentence index shifted); literal 8 |
| 123 | A/AFex.v:943 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 943 = dst line 946 (same text, sentence index shifted); literal 8 |
| 124 | A/AFex.v:944 | - | Lemma zshadow' / sentence 49 (-) | dec | 0x8 | - | PATCH-ZS | src line 944 = dst line 947 (same text, sentence index shifted); literal 8 |
| 125 | A/AFex.v:946 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 946 = dst line 949 (same text, sentence index shifted); literal 8 |
| 126 | A/AFex.v:946 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 946 = dst line 949 (same text, sentence index shifted); literal 8 |
| 127 | A/AFex.v:946 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 946 = dst line 949 (same text, sentence index shifted); literal 8 |
| 128 | A/AFex.v:946 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 946 = dst line 949 (same text, sentence index shifted); literal 8 |
| 146 | A/AFfl.v:832 | - | Lemma zshadow' / sentence 42 (-) | dec | 0x8 | - | PATCH-ZS | src line 832 = dst line 835 (same text, sentence index shifted); literal 8 |
| 147 | A/AFfl.v:833 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 833 = dst line 836 (same text, sentence index shifted); literal 8 |
| 148 | A/AFfl.v:833 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 833 = dst line 836 (same text, sentence index shifted); literal 8 |
| 149 | A/AFfl.v:833 | - | Lemma zshadow' / sentence 45 (-) | dec | 0x8 | - | PATCH-ZS | src line 833 = dst line 836 (same text, sentence index shifted); literal 8 |
| 150 | A/AFfl.v:834 | - | Lemma zshadow' / sentence 49 (-) | dec | 0x8 | - | PATCH-ZS | src line 834 = dst line 837 (same text, sentence index shifted); literal 8 |
| 151 | A/AFfl.v:836 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 836 = dst line 839 (same text, sentence index shifted); literal 8 |
| 152 | A/AFfl.v:836 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 836 = dst line 839 (same text, sentence index shifted); literal 8 |
| 153 | A/AFfl.v:836 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 836 = dst line 839 (same text, sentence index shifted); literal 8 |
| 154 | A/AFfl.v:836 | - | Lemma zshadow' / sentence 52 (-) | dec | 0x8 | - | PATCH-ZS | src line 836 = dst line 839 (same text, sentence index shifted); literal 8 |
| 175 | A/AFjy.v:1597 | - | Lemma zshadow_final / sentence 47 (-) | dec | 0x8 | - | PATCH-ZS | src line 1597 = dst line 1600 (same text, sentence index shifted); literal 8 |
| 176 | A/AFjy.v:1597 | - | Lemma zshadow_final / sentence 48 (-) | dec | 0x8 | - | PATCH-ZS | src line 1597 = dst line 1600 (same text, sentence index shifted); literal 8 |
| 177 | A/AFjy.v:1597 | - | Lemma zshadow_final / sentence 49 (-) | dec | 0x8 | - | PATCH-ZS | src line 1597 = dst line 1600 (same text, sentence index shifted); literal 8 |
| 362 | A/AFf0.v:471 | - | Lemma zshadow' / sentence 32 (-) | dec | 0x8 | - | PATCH-ZS | src line 471 deleted by the patch; literal 8 |
| 363 | A/AFf0.v:471 | - | Lemma zshadow' / sentence 32 (-) | dec | 0x8 | - | PATCH-ZS | src line 471 deleted by the patch; literal 8 |
| 364 | A/AFf0.v:471 | - | Lemma zshadow' / sentence 32 (-) | dec | 0x8 | - | PATCH-ZS | src line 471 deleted by the patch; literal 8 |
| 365 | A/AFf0.v:472 | - | Lemma zshadow' / sentence 33 (-) | dec | 0x8 | - | PATCH-ZS | src line 472 deleted by the patch; literal 8 |
| 366 | A/AFf0.v:472 | - | Lemma zshadow' / sentence 33 (-) | dec | 0x8 | - | PATCH-ZS | src line 472 deleted by the patch; literal 8 |
| 367 | A/AFf0.v:472 | - | Lemma zshadow' / sentence 33 (-) | dec | 0x8 | - | PATCH-ZS | src line 472 deleted by the patch; literal 8 |
| 368 | A/AFf3.v:648 | - | Lemma zshadow' / sentence 43 (-) | dec | 0x8 | - | PATCH-ZS | src line 648 deleted by the patch; literal 8 |
| 369 | A/AFf3.v:648 | - | Lemma zshadow' / sentence 43 (-) | dec | 0x8 | - | PATCH-ZS | src line 648 deleted by the patch; literal 8 |
| 370 | A/AFf3.v:648 | - | Lemma zshadow' / sentence 43 (-) | dec | 0x8 | - | PATCH-ZS | src line 648 deleted by the patch; literal 8 |
| 371 | A/AFf3.v:649 | - | Lemma zshadow' / sentence 44 (-) | dec | 0x8 | - | PATCH-ZS | src line 649 deleted by the patch; literal 8 |
| 372 | A/AFf3.v:649 | - | Lemma zshadow' / sentence 44 (-) | dec | 0x8 | - | PATCH-ZS | src line 649 deleted by the patch; literal 8 |
| 373 | A/AFf3.v:649 | - | Lemma zshadow' / sentence 44 (-) | dec | 0x8 | - | PATCH-ZS | src line 649 deleted by the patch; literal 8 |
| 374 | A/AFf4.v:898 | - | Lemma zshadow' / sentence 34 (-) | dec | 0x8 | - | PATCH-ZS | src line 898 deleted by the patch; literal 8 |
| 375 | A/AFf4.v:898 | - | Lemma zshadow' / sentence 34 (-) | dec | 0x8 | - | PATCH-ZS | src line 898 deleted by the patch; literal 8 |
| 376 | A/AFf4.v:898 | - | Lemma zshadow' / sentence 34 (-) | dec | 0x8 | - | PATCH-ZS | src line 898 deleted by the patch; literal 8 |
| 377 | A/AFf4.v:899 | - | Lemma zshadow' / sentence 35 (-) | dec | 0x8 | - | PATCH-ZS | src line 899 deleted by the patch; literal 8 |
| 378 | A/AFf4.v:899 | - | Lemma zshadow' / sentence 35 (-) | dec | 0x8 | - | PATCH-ZS | src line 899 deleted by the patch; literal 8 |
| 379 | A/AFf4.v:899 | - | Lemma zshadow' / sentence 35 (-) | dec | 0x8 | - | PATCH-ZS | src line 899 deleted by the patch; literal 8 |
| 26 | A/AB1w.v:67 | - | Definition tfib_A_asan_stack_malloc_0 (-) | hex | 0x3cda4 | - | S-ABSENTRT | src __asan_stack_malloc_0+0x0 (size 0x174); dst symtab has no __asan_stack_malloc_0 |
| 27 | A/AB1w.v:67 | - | Definition tfib_E_asan_stack_malloc_0 (-) | hex | 0x3cf18 | - | S-ABSENTRT | src __asan_stack_malloc_0 ends here (__asan_stack_malloc_1+0x0); dst symtab has no __asan_stack_malloc_0 |
| 28 | A/AB1w.v:69 | - | Definition tfib_A_asan_stack_malloc_2 (-) | hex | 0x3d0a8 | - | S-ABSENTRT | src __asan_stack_malloc_2+0x0 (size 0x19c); dst symtab has no __asan_stack_malloc_2 |
| 29 | A/AB1w.v:69 | - | Definition tfib_E_asan_stack_malloc_2 (-) | hex | 0x3d244 | - | S-ABSENTRT | src __asan_stack_malloc_2 ends here (__asan_stack_malloc_4+0x0); dst symtab has no __asan_stack_malloc_2 |
| 30 | A/AB1w.v:70 | - | Definition tfib_A_asan_stack_malloc_4 (-) | hex | 0x3d244 | - | S-ABSENTRT | src __asan_stack_malloc_4+0x0 (size 0x1cc); dst symtab has no __asan_stack_malloc_4 |
| 31 | A/AB1w.v:70 | - | Definition tfib_E_asan_stack_malloc_4 (-) | hex | 0x3d410 | - | S-ABSENTRT | src __asan_stack_malloc_4 ends here (_ZN6__asanL11MemToShadowEm+0x0); dst symtab has no __asan_stack_malloc_4 |
| 32 | A/AB1w.v:86 | - | Definition tfib_A_memcmp_2 (-) | hex | 0x42144 | - | S-ABSENTRT | src __interceptor_trampoline_bcmp+0x0 (size 0x4); dst symtab has no __interceptor_trampoline_bcmp |
| 33 | A/AB1w.v:86 | - | Definition tfib_E_memcmp_2 (-) | hex | 0x42148 | - | S-ABSENTRT | src __interceptor_trampoline_bcmp ends here (__wrap_memchr+0x0 / __interceptor_trampoline_memchr+0x0); dst symtab has no __interceptor_trampoline_bcmp |
| 34 | A/AB1w.v:121 | - | Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m (-) | hex | 0x43850 | - | S-ABSENTRT | src ___interceptor_bcmp+0x0 (size 0xbc); dst symtab has no ___interceptor_bcmp |
| 35 | A/AB1w.v:121 | - | Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m (-) | hex | 0x4390c | - | S-ABSENTRT | src ___interceptor_bcmp ends here (__interceptor_memchr+0x0 / ___interceptor_memchr+0x0); dst symtab has no ___interceptor_bcmp |
| 36 | A/AB1w.v:150 | - | Definition tfib_A_asan_memset (-) | hex | 0x51c98 | - | S-ABSENTRT | src __asan_memset+0x0 (size 0x240); dst symtab has no __asan_memset |
| 37 | A/AB1w.v:150 | - | Definition tfib_E_asan_memset (-) | hex | 0x51ed8 | - | S-ABSENTRT | src __asan_memset ends here (__interceptor_memset+0x0 / ___interceptor_memset+0x0); dst symtab has no __asan_memset |
| 111 | A/AF0l.v:12 | - | Definition Tfib_code (-) | hex | 0x3cda4 | - | S-AF0L | arm `cid =? k then 0x3cda4`: src __asan_stack_malloc_0+0x0; dst symtab has no __asan_stack_malloc_0. port_core removed the arm (review.tsv code-no-counterpart; kept-refused-definition Tfib_code); dst keeps only `if cid =? 1 then 0x3c1b8` (= __asan_stack_malloc_1, the only __asan_stack_malloc_* in fuzz_uci) |
| 112 | A/AF0l.v:12 | - | Definition Tfib_code (-) | hex | 0x3d0a8 | - | S-AF0L | arm `cid =? k then 0x3d0a8`: src __asan_stack_malloc_2+0x0; dst symtab has no __asan_stack_malloc_2. port_core removed the arm (review.tsv code-no-counterpart; kept-refused-definition Tfib_code); dst keeps only `if cid =? 1 then 0x3c1b8` (= __asan_stack_malloc_1, the only __asan_stack_malloc_* in fuzz_uci) |
| 113 | A/AF0l.v:12 | - | Definition Tfib_code (-) | hex | 0x3d244 | - | S-AF0L | arm `cid =? k then 0x3d244`: src __asan_stack_malloc_4+0x0; dst symtab has no __asan_stack_malloc_4. port_core removed the arm (review.tsv code-no-counterpart; kept-refused-definition Tfib_code); dst keeps only `if cid =? 1 then 0x3c1b8` (= __asan_stack_malloc_1, the only __asan_stack_malloc_* in fuzz_uci) |
| 116 | A/AF0l.v:12 | - | Definition Tfib_code (-) | dec | 0x0 | - | S-AF0L | the class key 0 of a removed arm (`cid =? 0`); not an address |
| 117 | A/AF0l.v:12 | - | Definition Tfib_code (-) | dec | 0x2 | - | S-AF0L | the class key 2 of a removed arm (`cid =? 2`); not an address |
| 118 | A/AF0l.v:12 | - | Definition Tfib_code (-) | dec | 0x4 | - | S-AF0L | the class key 4 of a removed arm (`cid =? 4`); not an address |
| 38 | A/AB1w.v:441 | - | Definition tfib_A_check_groupa (-) | hex | 0x81b70 | - | S-GRANTPROG | src check_groupa+0x0 (size 0x3b4); dst symtab has no check_groupa |
| 39 | A/AB1w.v:441 | - | Definition tfib_E_check_groupa (-) | hex | 0x81f24 | - | S-GRANTPROG | src check_groupa ends here (asan.module_ctor+0x0); dst symtab has no check_groupa |
| 40 | A/AB1w.v:444 | - | Definition tfib_A_reac_ctrl_checksum_verify (-) | hex | 0x81f8c | - | S-GRANTPROG | src reac_ctrl_checksum_verify+0x0 (size 0x74); dst symtab has no reac_ctrl_checksum_verify |
| 41 | A/AB1w.v:444 | - | Definition tfib_E_reac_ctrl_checksum_verify (-) | hex | 0x82000 | - | S-GRANTPROG | src reac_ctrl_checksum_verify ends here (reac_ctrl_parse+0x0); dst symtab has no reac_ctrl_checksum_verify |
| 42 | A/AB1w.v:445 | - | Definition tfib_A_reac_ctrl_parse (-) | hex | 0x82000 | - | S-GRANTPROG | src reac_ctrl_parse+0x0 (size 0x9a0); dst symtab has no reac_ctrl_parse |
| 43 | A/AB1w.v:445 | - | Definition tfib_E_reac_ctrl_parse (-) | hex | 0x829a0 | - | S-GRANTPROG | src reac_ctrl_parse ends here (kind_of_link1+0x0); dst symtab has no reac_ctrl_parse |
| 44 | A/AB1w.v:446 | - | Definition tfib_A_kind_of_link1 (-) | hex | 0x829a0 | - | S-GRANTPROG | src kind_of_link1+0x0 (size 0x74); dst symtab has no kind_of_link1 |
| 45 | A/AB1w.v:446 | - | Definition tfib_E_kind_of_link1 (-) | hex | 0x82a14 | - | S-GRANTPROG | src kind_of_link1 ends here (reac_ctrl_stamp_headamp+0x0); dst symtab has no kind_of_link1 |
| 46 | A/AB1w.v:447 | - | Definition tfib_A_reac_ctrl_stamp_headamp (-) | hex | 0x82a14 | - | S-GRANTPROG | src reac_ctrl_stamp_headamp+0x0 (size 0x24c); dst symtab has no reac_ctrl_stamp_headamp |
| 47 | A/AB1w.v:447 | - | Definition tfib_E_reac_ctrl_stamp_headamp (-) | hex | 0x82c60 | - | S-GRANTPROG | src reac_ctrl_stamp_headamp ends here (reac_ctrl_headamp_record_verify+0x0); dst symtab has no reac_ctrl_stamp_headamp |
| 48 | A/AB1w.v:448 | - | Definition tfib_A_reac_ctrl_headamp_record_verify (-) | hex | 0x82c60 | - | S-GRANTPROG | src reac_ctrl_headamp_record_verify+0x0 (size 0xdc); dst symtab has no reac_ctrl_headamp_record_verify |
| 49 | A/AB1w.v:448 | - | Definition tfib_E_reac_ctrl_headamp_record_verify (-) | hex | 0x82d3c | - | S-GRANTPROG | src reac_ctrl_headamp_record_verify ends here (reac_ctrl_identity_poll_block+0x0); dst symtab has no reac_ctrl_headamp_record_verify |
| 50 | A/AB1w.v:449 | - | Definition tfib_A_reac_ctrl_identity_poll_block (-) | hex | 0x82d3c | - | S-GRANTPROG | src reac_ctrl_identity_poll_block+0x0 (size 0x50); dst symtab has no reac_ctrl_identity_poll_block |
| 51 | A/AB1w.v:449 | - | Definition tfib_E_reac_ctrl_identity_poll_block (-) | hex | 0x82d8c | - | S-GRANTPROG | src reac_ctrl_identity_poll_block ends here (reac_ctrl_build_grant_sweep+0x0); dst symtab has no reac_ctrl_identity_poll_block |
| 52 | A/AB1w.v:450 | - | Definition tfib_A_reac_ctrl_build_grant_sweep (-) | hex | 0x82d8c | - | S-GRANTPROG | src reac_ctrl_build_grant_sweep+0x0 (size 0x270); dst symtab has no reac_ctrl_build_grant_sweep |
| 53 | A/AB1w.v:450 | - | Definition tfib_E_reac_ctrl_build_grant_sweep (-) | hex | 0x82ffc | - | S-GRANTPROG | src reac_ctrl_build_grant_sweep ends here (ctrl_lay_block+0x0); dst symtab has no reac_ctrl_build_grant_sweep |
| 54 | A/AB1w.v:451 | - | Definition tfib_A_ctrl_lay_block (-) | hex | 0x82ffc | - | S-GRANTPROG | src ctrl_lay_block+0x0 (size 0x3a0); dst symtab has no ctrl_lay_block |
| 55 | A/AB1w.v:451 | - | Definition tfib_E_ctrl_lay_block (-) | hex | 0x8339c | - | S-GRANTPROG | src ctrl_lay_block ends here (ctrl_finish+0x0); dst symtab has no ctrl_lay_block |
| 56 | A/AB1w.v:452 | - | Definition tfib_A_ctrl_finish (-) | hex | 0x8339c | - | S-GRANTPROG | src ctrl_finish+0x0 (size 0x1b0); dst symtab has no ctrl_finish |
| 57 | A/AB1w.v:452 | - | Definition tfib_E_ctrl_finish (-) | hex | 0x8354c | - | S-GRANTPROG | src ctrl_finish ends here (reac_box_model_block+0x0); dst symtab has no ctrl_finish |
| 58 | A/AB1w.v:453 | - | Definition tfib_A_reac_box_model_block (-) | hex | 0x8354c | - | S-GRANTPROG | src reac_box_model_block+0x0 (size 0xe80); dst symtab has no reac_box_model_block |
| 59 | A/AB1w.v:453 | - | Definition tfib_E_reac_box_model_block (-) | hex | 0x843cc | - | S-GRANTPROG | src reac_box_model_block ends here (build_dt1_single+0x0); dst symtab has no reac_box_model_block |
| 60 | A/AB1w.v:454 | - | Definition tfib_A_build_dt1_single (-) | hex | 0x843cc | - | S-GRANTPROG | src build_dt1_single+0x0 (size 0x470); dst symtab has no build_dt1_single |
| 61 | A/AB1w.v:454 | - | Definition tfib_E_build_dt1_single (-) | hex | 0x8483c | - | S-GRANTPROG | src build_dt1_single ends here (reac_grant_alloc_fits+0x0); dst symtab has no build_dt1_single |
| 62 | A/AB1w.v:455 | - | Definition tfib_A_reac_grant_alloc_fits (-) | hex | 0x8483c | - | S-GRANTPROG | src reac_grant_alloc_fits+0x0 (size 0x24); dst symtab has no reac_grant_alloc_fits |
| 63 | A/AB1w.v:455 | - | Definition tfib_E_reac_grant_alloc_fits (-) | hex | 0x84860 | - | S-GRANTPROG | src reac_grant_alloc_fits ends here (reac_grant_allocate+0x0); dst symtab has no reac_grant_alloc_fits |
| 64 | A/AB1w.v:456 | - | Definition tfib_A_reac_grant_allocate (-) | hex | 0x84860 | - | S-GRANTPROG | src reac_grant_allocate+0x0 (size 0x90); dst symtab has no reac_grant_allocate |
| 65 | A/AB1w.v:456 | - | Definition tfib_E_reac_grant_allocate (-) | hex | 0x848f0 | - | S-GRANTPROG | src reac_grant_allocate ends here (reac_grant_build_sweep+0x0); dst symtab has no reac_grant_allocate |
| 66 | A/AB1w.v:457 | - | Definition tfib_A_reac_grant_build_sweep (-) | hex | 0x848f0 | - | S-GRANTPROG | src reac_grant_build_sweep+0x0 (size 0x42c); dst symtab has no reac_grant_build_sweep |
| 67 | A/AB1w.v:457 | - | Definition tfib_E_reac_grant_build_sweep (-) | hex | 0x84d1c | - | S-GRANTPROG | src reac_grant_build_sweep ends here (reac_headamp_tx_init+0x0); dst symtab has no reac_grant_build_sweep |
| 68 | A/AB1w.v:458 | - | Definition tfib_A_reac_headamp_tx_init (-) | hex | 0x84d1c | - | S-GRANTPROG | src reac_headamp_tx_init+0x0 (size 0x20); dst symtab has no reac_headamp_tx_init |
| 69 | A/AB1w.v:458 | - | Definition tfib_E_reac_headamp_tx_init (-) | hex | 0x84d3c | - | S-GRANTPROG | src reac_headamp_tx_init ends here (reac_headamp_tx_set+0x0); dst symtab has no reac_headamp_tx_init |
| 70 | A/AB1w.v:459 | - | Definition tfib_A_reac_headamp_tx_set (-) | hex | 0x84d3c | - | S-GRANTPROG | src reac_headamp_tx_set+0x0 (size 0x118); dst symtab has no reac_headamp_tx_set |
| 71 | A/AB1w.v:459 | - | Definition tfib_E_reac_headamp_tx_set (-) | hex | 0x84e54 | - | S-GRANTPROG | src reac_headamp_tx_set ends here (reac_headamp_default+0x0); dst symtab has no reac_headamp_tx_set |
| 72 | A/AB1w.v:460 | - | Definition tfib_A_reac_headamp_default (-) | hex | 0x84e54 | - | S-GRANTPROG | src reac_headamp_default+0x0 (size 0x10); dst symtab has no reac_headamp_default |
| 73 | A/AB1w.v:460 | - | Definition tfib_E_reac_headamp_default (-) | hex | 0x84e64 | - | S-GRANTPROG | src reac_headamp_default ends here (reac_headamp_tx_effective+0x0); dst symtab has no reac_headamp_default |
| 74 | A/AB1w.v:461 | - | Definition tfib_A_reac_headamp_tx_effective (-) | hex | 0x84e64 | - | S-GRANTPROG | src reac_headamp_tx_effective+0x0 (size 0xb8); dst symtab has no reac_headamp_tx_effective |
| 75 | A/AB1w.v:461 | - | Definition tfib_E_reac_headamp_tx_effective (-) | hex | 0x84f1c | - | S-GRANTPROG | src reac_headamp_tx_effective ends here (reac_headamp_tx_arm_scene+0x0); dst symtab has no reac_headamp_tx_effective |
| 76 | A/AB1w.v:462 | - | Definition tfib_A_reac_headamp_tx_arm_scene (-) | hex | 0x84f1c | - | S-GRANTPROG | src reac_headamp_tx_arm_scene+0x0 (size 0x13c); dst symtab has no reac_headamp_tx_arm_scene |
| 77 | A/AB1w.v:462 | - | Definition tfib_E_reac_headamp_tx_arm_scene (-) | hex | 0x85058 | - | S-GRANTPROG | src reac_headamp_tx_arm_scene ends here (reac_headamp_tx_set_resweep+0x0); dst symtab has no reac_headamp_tx_arm_scene |
| 78 | A/AB1w.v:463 | - | Definition tfib_A_reac_headamp_tx_set_resweep (-) | hex | 0x85058 | - | S-GRANTPROG | src reac_headamp_tx_set_resweep+0x0 (size 0x74); dst symtab has no reac_headamp_tx_set_resweep |
| 79 | A/AB1w.v:463 | - | Definition tfib_E_reac_headamp_tx_set_resweep (-) | hex | 0x850cc | - | S-GRANTPROG | src reac_headamp_tx_set_resweep ends here (reac_headamp_tx_next+0x0); dst symtab has no reac_headamp_tx_set_resweep |
| 80 | A/AB1w.v:464 | - | Definition tfib_A_reac_headamp_tx_next (-) | hex | 0x850cc | - | S-GRANTPROG | src reac_headamp_tx_next+0x0 (size 0x710); dst symtab has no reac_headamp_tx_next |
| 81 | A/AB1w.v:464 | - | Definition tfib_E_reac_headamp_tx_next (-) | hex | 0x857dc | - | S-GRANTPROG | src reac_headamp_tx_next ends here (__wrap_getenv+0x0); dst symtab has no reac_headamp_tx_next |
| 85 | A/AB1w.v:563 | - | Definition tfib_A_thunk_96f9c (-) | ident | 0x96f9c | - | THUNK | name hex 0x96f9c (IDENT, not an address); the dst keeps the same name at dst line 564 |
| 86 | A/AB1w.v:563 | - | Definition tfib_A_thunk_96f9c (-) | hex | 0x9804c | - | THUNK | src pthread_testcancel+0x0 / __pthread_testcancel+0x0; its dst twin is dst line 564 = pthread_testcancel+0x0 / __pthread_testcancel+0x0 |
| 87 | A/AB1w.v:563 | - | Definition tfib_E_thunk_96f9c (-) | ident | 0x96f9c | - | THUNK | name hex 0x96f9c (IDENT, not an address); the dst keeps the same name at dst line 564 |
| 88 | A/AB1w.v:563 | - | Definition tfib_E_thunk_96f9c (-) | hex | 0x98054 | - | THUNK | src __set_thread_area+0x0 / __set_thread_area+0x0; its dst twin is dst line 564 = __set_thread_area+0x0 / __set_thread_area+0x0 |

### UNRESOLVED (8 rows; FLAGGED says 8)

Reasons: U-TLSSH (2), FMTWIN (2), U-JT (1), U-UNMAP (1), U-PHDR (1), U-STDIN (1).

| raw line | src file:line | dst line | sentence (idx) | kind | src value | dst value | reason | measurement |
|---:|---|---:|---|---|---|---|---|---|
| 241 | A/AE2v.v:63 | 64 | Definition SH_HI (0) | hex | 0x7fffb2f8 | 0x7fffb2c8 | FMTWIN | format "cli: input >= %u bytes, refused\n" (len 32) src @0x1976d, dst @0x19614: SH_HI = floor8(0x7fff8000 + (fmt+len)/8) + 8 = src 0x7fffb2f8, dst 0x7fffb2c8; override row |
| 247 | A/AE35.v:64 | 65 | Definition SH_LO (0) | hex | 0x7fffa908 | 0x7fffa8e8 | FMTWIN | format "%d\n" (len 3) src @0x14863, dst @0x14763: SH_LO = floor8(0x7fff8000 + fmt/8) = src 0x7fffa908, dst 0x7fffa8e8; no override row: written by port_core's review rule `shadow-window SH_LO/SH_HI (target string at ...)` (review.tsv), which corrected check.tsv's granule shift |
| 23 | A/AB1w.v:10 | 11 | Definition tfib_rodata_hi (0) | hex | 0x22c0c | 0x22584 | U-JT | JT cell +0x118 = .rodata.hi - 0x40 (both) |
| 89 | A/AB1w.v:600 | 601 | Definition tfib_at_ph_addr_z (0) | hex | 0x10040 | 0x10040 | U-PHDR | PT_PHDR p_vaddr (both) |
| 220 | A/AD2f.v:147 | 148 | Definition SOBUF_HI (0) | hex | 0x5f85e8 | 0x5f2aa8 | U-STDIN | __stdin_FILE.buf (both); override |
| 170 | A/AFjm.v:327 | 328 | Lemma map_zoneN (2) | dec | 0x800b3118 | 0x800b25b0 | U-TLSSH | shadow(builtin_tls+0xeb8) (both) |
| 181 | A/AFk1.v:694 | 695 | Lemma sm_bounds (0) | dec | 0x800b3118 | 0x800b25b0 | U-TLSSH | shadow(builtin_tls+0xeb8) (both) |
| 84 | A/AB1w.v:562 | 563 | Definition tfib_E_set_thread_area (0) | hex | 0x98060 | 0x92984 | U-UNMAP | __unmapself+0x0 (both) |

## DEFECTS

None. No flagged row has a dst value that is wrong for fuzz_uci.asan.

Observations that are not defects:
- The fuzz_uci program rows are on AB1w dst line 87 (the line of the removed bcmp-trampoline row), not where grant's program rows were (dst lines 442 and 445-465 are blank). The values are correct; only the position in the file differs.
- No file of work10/stage and no file of the dst lib uses tfib_rodata_hi, tfib_text_hi, tfib_tbss_lo, tfib_E_set_thread_area or tfib_at_ph_addr_z: a grep finds only their definitions in AB1w.
- U-TLSSH: the bound keeps its role (shadow of builtin_tls+0xeb8). Its margin below shadow(IMG_TOP) is 0x4250 in fuzz_uci (0x42e8 in grant), so `2148214192 <= SMv` still follows from `6242304 <= mb`.


## GENERATOR-FILL (6 rows; REPORTED, not counted by --fail-on-flags; triaged per the unit owner's rule)

The gate calls each a positional duplicate: the ported value repeats another ported value of its sentence. In every row the
donor sentence has the same duplicate at the same two positions, and the ported value is fuzz_uci's, measured:

| src file:line | dst line | idx | src | dst | reason (measured) |
|---|---|---|---|---|---|
| A/AD2e.v:69 | 70 | 3 | 37 | 35 | `length PM_piecesCM = N /\ length (...) = N`, N twice in the donor too; fuzz_uci's IMG_REGIONS has 31 regions, grant's 33 (A/AD2j.v IMG_REGIONS, counted), so every region count is -2 |
| A/AD2e.v:69 | 70 | 5 | 37 | 35 | the same sentence, second position |
| A/AD2f.v:184 | 185 | 3 | 36 | 34 | `skipn N (ss_mem sB0)` and `skipn N (ss_mem sB1)`, N twice in the donor too; regions -2 |
| A/AD2f.v:196 | 197 | 5 | 25 | 23 | IMG_B_eq's region indices 24/25/29/33 -> 22/23/27/31, regions -2 |
| A/AE3m.v:955 | 956 | 3 | 84070 | 83814 | `(SLit 84070) ... (84070)`, the same literal twice in the donor; "%d\n" is at 0x14863 in fuzz_grant.asan and 0x14763 in fuzz_uci.asan (bytes `%d\n\0` read from both images); +3 = 0x14766 = 83814 |
| A/AE3m.v:1444 | 1445 | 6 | 84069 | 83813 | the same string, +2 = 0x14765 = 83813 |

No defect. FLAGGED 368 rows in 10 classes (FLAG-CLASSES 575d398c6022); GENERATOR-FILL 6 (all triaged above).
