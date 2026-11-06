# fuzz_wire __asan_memmove: the donor comparison on cmpkit 86da41d3ef68 (kit86 = comparison kit version 86da41d3ef68, tool registry cmpkit/86da41d3ef68/)

This record replaces, as the comparison of record, `memmove-kit3/` (the same comparison on cmpkit 4bbd3a74be89, which
86da41d3ef68 supersedes). The old record stays as it is. Nothing here proves a function: it is a measurement of two
binaries.

It is a FULL re-run of the kit over the WHOLE compare set, not only the functions rule 8 exposes: **785 closure members
per image** (`closure_strict3.py` from `__asan_memmove`, every member compared against the pcap twin) and **944 paired
functions per image** (`paircl.py` against the released pcap PIN, `--full`, every differing target in the targets TSV).
Every member and every pair the kit does not certify is settled here target by target from the kit's FULL list, or
listed NOT CERTIFIED.

This version carries the fixes three read-only audits of the earlier versions asked for (findings F1-F6, G1, G2,
R1-R5, and the four of the check of 2f38af68638) and applies the pool owner's rulings O1 and O3 throughout. Every
change in the last round only removed settlements: no row, target or member settles here that was not settled before.

**No ABI assumption is made at calls or at returns.** At a call, every register that holds the value goes into the
callee (a0-a7 as arguments, every other register too), and the value survives the call unless that callee is shown to
write the register on every path back. At a `ret`, every register that still holds the value goes to the callers, not
only a0 / a1; it is settled only by the complete-caller test of ruling O3: the function's address is formed nowhere
but in its direct call sites (no loadable data word, no code sequence), and every caller is traced to the
register's next write (a caller that keeps the register to its own `ret`, or reaches the function by a tail call, is
tested one level up; so is a caller that hands the value on in a TAIL call whose callee may return it intact). A path
that ends at an unresolvable indirect call or jump with the value live, or at the depth bound (8 calls, 4 tail
callers), leaves the row NOT CERTIFIED, and so does a call that is the function's last word (a return would fall past
its end) or a tail call, unless the callee writes the register on every path. A store of the register into a
callee's own stack frame is not a use ONLY when that callee forms no sp-derived pointer (no `va_list`, no address of
a local) and no load reads the stored bytes back, except the restore of a save / restore pair; every other frame
store is a read (so an argument register `Printf` or `Report` saves into the varargs area its `va_list` points at
counts as read, and so does an s-register that `SharedPrintfCode` or `StackTrace::Print` saves in a frame whose local
buffer it passes on). The pool owner's O3 ruling
makes `compare`, dead-at-call, callee-analysed `compare-only`, (i) / (ii) / (iii), a store into an integer field and
`dead-at-ret` settled classes; a row with mixed uses settles only when EVERY use on every path is in one of them, with
the class named per use.

## Images and kit

| role | file | sha256 (12) |
|---|---|---|
| X unit | fuzz_wire.asan (pin) | `2f8f8697cd4f` |
| X unit | fuzz_wire.asan.unstripped (twin, image A) | `d2f662a22962` |
| X unit | fuzz_wire.asan-ubsan (pin) | `af4534831a45` |
| X unit | fuzz_wire.asan-ubsan.unstripped (twin, image B) | `51eb4bef2425` |
| Y donor | fuzz_pcap.asan (released pin, A) | `b7a91d9b1fb0` |
| Y donor | fuzz_pcap.asan (unstripped twin, A) | `36da3052c383` |
| Y donor | fuzz_pcap.asan-ubsan (released pin, B) | `9e66f771f22a` |
| Y donor | fuzz_pcap.asan-ubsan (unstripped twin, B) | `c969d83cdd59` |

Kit: cmpkit **86da41d3ef68** (sha256 of `records/cmpkit-SHA256SUMS`; `sha256sum -c` of its nine members: 9 x OK), run
from a fresh copy of the kit directory. `drvcmp.py twins` on each pcap pin and twin and on each wire pin and twin: the
PT_LOAD layout is equal and the loadable bytes differ only in the ELF header `[0x10000,0x10040)` and
`.note.gnu.build-id` `[0x102a8,0x102cc)` (24 bytes pcap, 25 bytes wire; `records/twins-*.txt`).
`__asan_memmove` roots: X A `0x51310` / B `0x510b0`, Y A `0x51bf0` / B `0x51c40`. No ambiguous name was given to any
tool: closure_strict3 compares one member per X ADDRESS and paircl pairs by call target, so the five
`_ZN6__asanL11MemToShadowEm` copies are reached by address; the kit refused nothing (no AMBIGUOUS line, rc 0).

## Result: 0 REAL on both images

No differing instruction word, no differing named target, no table entry and no full address whose symbol + offset
differs, on either image. The verdict is NOT "the closure is equal": the kit certifies part of it, the measurements
below settle more, and the rest is listed NOT CERTIFIED (REAL 0) with its count.

Both images give the same counts (image A and image B rows are identical throughout: same keys, same uses with the
same offset, role, register and class, same verdicts; only image-specific addresses in the citations differ):

| run | functions | kit-certified | settled here | NOT CERTIFIED (REAL 0) |
|---|---|---|---|---|
| closure (`closure_strict3`, X twin vs Y twin) | 785 | 657 | 53 (48 reported + 5 kit-EQUAL with a `lui-const` acceptance) | 75 (52 + 23) |
| paircl (`paircl --full`, X twin vs Y PIN) | 944 | 798 | 56 (50 + 6) | 90 (57 + 33) |

"kit-certified" is EQUAL or EQUAL-mod-pcrel with no differing target AND no `lui-const` acceptance: a `lui-const
(dataflow)` row is listed by the kit, not measured, so this record traces it like any other lui row (the XOR plant
below is exactly that row shape, and it hides a real difference).

Targets of the non-certified members / pairs, settled by these measurements only (per image; closure + paircl):

| measurement | closure | paircl | what it is |
|---|---|---|---|
| CSTR | 37 | 39 | an unnamed read-only target whose bytes up to and including the NUL are equal, with EVERY use of its address settled: a consumer the table names as reading only to the NUL, a register the callee reads on no path, or a register the complete-caller test clears at a `ret`. A row settles only when every use does; a hand line may name the class of one use (the field a store writes, the byte a load reads), never the whole row. All of them are the EMPTY string (X `0x13e67` / Y `0x13e7d`, 1 byte): under rule 3 an empty string takes the full-region rule, so the kit reports `data-differs`; the settlement is the consumer, not the region |
| CSTR NOT CERTIFIED | 30 | 33 | the same string, but one use of the address is not settled: most often it is still in a register at a call into a function that may read it (the callee, or a function it calls, saves the register into a frame it passes a pointer into), or at a `ret` whose callers the test cannot clear |
| TABLE | 7 | 7 | an index-to-load dataflow with the bound in the code: the six 64-entry De Bruijn ctz tables (`srli 58`, 64 x 1 byte equal) and OpenFile +0x60 (`addi a1,zero,2; bltu a1,s1`, 3 x 4 bytes equal) |
| JTCHECK | 13 | 13 | jtcheck 8b0ea3862423 (a kit member) ACCEPTs a table / initializer at that offset under its table rule |
| BYHAND-JT32-rel | 3 | 3 | a relative 32-bit jump table jtcheck refuses, read entry by entry as a function offset, with its bound checked from the code |
| LUI | 29 | 31 | a rule-8 row (a `lui-in-section` target or a `lui-const` acceptance) settled by the hand trace below |
| LUI NOT CERTIFIED | 80 | 92 | a rule-8 row no class settles: NOT CERTIFIED, REAL 0 |
| unmeasured | 0 | 3 | `I/S-type word on an auipc register, not a compared target`: no named measurement applies, NOT CERTIFIED, REAL 0. The three words are byte-equal in X and Y |

`records/settle-<image>-targets.tsv` has one row per target with its measurement, verdict and detail;
`records/settle-<image>-members.tsv` the per-member status; `records/settle-<image>-summary.txt` the counts. The tool
re-runs the kit's own `strictcmp3.tcmp` on every non-certified pair and stops unless its full differing-target list
matches the kit's printed list offset for offset and kind for kind (it matched everywhere).

## The three classes the scans miss

1. **jtcheck table refusals** — three rows, each settled by hand entry by entry, with the bound checked by the tool
   (the compare word, and that the ONLY definition of the bound register reaching it is `addi rK, zero, K` with
   K + 1 = the entry count, by a MAY reaching-definitions walk):
   `VSNPrintf +0x1c0` 33 entries (bound `+0x1b4 bltu s0, a7`, s0 from `+0x68 addi s0, zero, 0x20`),
   `CFI_Parser::parseCIE +0x23c` 47 (bound `+0x258`, s5 from `+0x234 addi s5, zero, 0x2e`),
   `CFI_Parser::parseFDEInstructions +0x140` 48 (bound `+0x134`, s1 from `+0xd0 addi s1, zero, 0x2f`; jtcheck refuses
   it because the bound is reloaded from the stack elsewhere, and the definition that REACHES the compare is the
   constant). Every entry gives the same function offset in X and Y, on both images.
2. **Empty-string data targets** — all CSTR rows are the empty string; each use of the address is traced from its
   `addi` to every read (`records/settle-<image>-cstr-consumers.txt`) and settled by a consumer the table in
   `tools/luiclass.tsv` names as reading only to the NUL (Printf / AppendF `%s`, `InternalScopedString::Append`,
   `internal_strncpy`, `internal_strcmp` / `internal_strncmp`, `FlagParser::ParseString`, `fstatat`'s path,
   PrintMemoryByte's `before` / `after`, `PrintAddressDescription`'s `bug_type`, `__lctrans`), by a `const char *`
   flag field, by a return value whose consumer is cited, or as not a use (a register the callee reads on no path,
   or one the complete-caller test clears at a `ret`). 30 + 33 rows per image are NOT CERTIFIED (above).
3. **NAME-ONLY acceptances** — none, on either image, in closure, paircl or jtcheck.

## The lui rows (rule 8), hand-traced

Every rule-8 row is traced with `tools/luitrace.py`: the value is followed through EVERY word up to the next write of
each register (and frame slot) that holds it, on every path of the kit's own control-flow graph, through
addi / addiw / add / sub / sh1add / sh2add / sh3add / and / or / xor / andi / ori / xori / shifts / mul / div, through
`mv`, and through stack spills and their reloads. A call to a function that never returns (CheckFailed, Die) has no
fall-through edge. Each USE is printed with its role and, where the value's leaves are lui / auipc / immediates, the
FULL ADDRESS computed on BOTH images from that image's own words and named by the kit's naming.
`records/settle-<image>-luitrace.txt` holds every trace.

Per image: **115 distinct lui rows** (68 `lui-in-section` targets, 47 `lui-const` acceptances) — **30 SETTLED, 85 NOT
CERTIFIED (REAL 0)**. The 742 uses in them (more than before: every register at every `ret` and every non-argument
register at every call is now a use):

| class | uses | what settles it |
|---|---|---|
| FULL-ADDRESS-EQUAL | 9 | the value reaches a base (or is passed / stored / returned) and its full address is the same symbol + offset on both images |
| FULL-ADDRESS-TERM-EQUAL | 2 | an object address plus a runtime term: the constant part is the same symbol + offset on both images and the term is a runtime index (`StackDepotGet +0x3c / +0x48`: `theDepot+0x400010` + 8 * (id >> 16)) |
| iii-disp | 30 | a displacement on an object-pointer base. The tool checks the base: at least one runtime leaf must be a real object pointer (an argument the function's pinned signature makes a pointer, a loaded value, or the a0 of a call whose callee returns a pointer); an integer argument, an atomic result or a value a call left in a2-a7 may appear only as an index term beside it; an auipc-built value settles only by full address |
| i | 37 | a call argument the pinned source's contract makes a byte count / length / count / size / flags / mode / prot / alignment |
| b | 5 | `CheckFailed`'s `u64 v1` / `v2`, which CheckFailed only formats (`Printf("%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n", ...)`, sanitizer_termination.cpp:74-76) |
| ii | 6 | an integer return (GetStats's two uptr counters, `sysconf`'s `long`, `__tm_to_secs` / `__year_to_secs`) |
| dead-at-call | 118 | an argument register beyond the callee's integer-register arguments (signature cited) that the callee reads on no path to its return; where the callee may leave it intact, the trace goes on in the caller to the register's next write |
| not-read-by-callee | 123 | a non-argument register (t0-t6, s0-s11, ra) holding the value at a call into a function that reads it on no path to its return, in X and Y; the trace goes on in the caller past the call |
| dead-at-ret | 21 | a register (other than a returned a0 / a1) that still holds the value at a `ret`, cleared by the complete-caller test of ruling O3 |
| compare-only | 7 | every use of the value, on every path up to its next write, is a branch / compare operand |
| compare | 5 | a branch / compare operand in a row whose other uses are all settled |
| NONE | 379 | nothing above applies: the row is NOT CERTIFIED (REAL 0) |

The 379 unsettled uses are: 93 a compare in a row whose other uses are not settled, 88 a read in a callee or a
caller (86 of them a register saved into a frame that a pointer leaves: 64 an s-register prologue save in a function
that forms an sp-derived pointer, the address of a local (`SharedPrintfCodeNoBuffer` 28, `VSNPrintf` 17,
`SharedPrintfCode` 2, and 17 in allocator, mmap and file functions; 61 of the 64 pass that address to a call, and
`SizeClassAllocator32::PopulateFreeList`'s 3 only form it, for its local `shuffle_array`, as `PopulateBatches` is
inlined), 22 an argument register saved into the varargs area that a `va_list` points at
(`Report` 15, `Printf` 5, `InternalScopedString::AppendF` 2)), 75
on a path that ends at an unresolved (indirect) call with the value live (`Die`'s die callbacks, the interceptors'
REAL() calls, `sysconf`'s jump table), 30 at the depth bound, 26 a memory base whose pointer leaf has no cited object,
18 an argument whose parameter is address-typed or not a count, 13 a store whose destination field is not cited, 11 a
caller list that cannot be shown complete, 8 a syscall argument, 6 a callee with no signature in the table, 5 a tail
call or a last-word call the callee may return from, 3 a register-indirect call or an ecall, 2 refused by the
object-pointer test, and 1 other. By role: 131 a non-argument register at a call, 59 a register at a `ret`, 93 a
compare, 55 an argument, 28 a base, 13 a store. The 85 NOT CERTIFIED rows hold REAL 0: the lui word of all 115 rows is
byte-equal in X and Y on both images (90 distinct functions have a NOT CERTIFIED member or pair).

**Against the reviewers' estimates.** The settled lui set is exactly the 30 rows the check of 2f38af68638 confirmed:
the 33 settled there minus `StackDepotBase::find +0x1c` (a2 reaches `Printf`'s varargs save through `Put`,
`StackDepotPut`, `LeakReport::AddLeakedChunks` and `CheckForLeaks +0x364`), `__lsan_unregister_root_region +0x238` (a4
leaves `___interceptor_free` in its tail call into `InternalFree`, which may return it intact, and goes on to callers
that reach `Die` / `__interceptor_read`), and `sysconf +0x214` (the call to `__stack_chk_fail` is sysconf's last word;
the tool has no model of a callee that never returns other than one without a `ret`). That estimate was lui 30 / 85,
CSTR settled 44 / 47, closure 657 / 56 / 72, paircl 798 / 60 / 86. The lui count matches. The CSTR and member counts
are lower because the frame-store rule, applied everywhere as stated, also refuses CSTR rows whose string sits in an
s-register at a call that reaches `SharedPrintfCode` or `StackTrace::Print`. `SharedPrintfCode` saves s1 / s2 in its
prologue (`+0xc sd s1, 0x198(sp)`, `+0x10 sd s2, 0x190(sp)`) and `StackTrace::Print` saves s1 (`+0xc sd s1, 0x18(sp)`).
Each then passes the address of a local buffer (`mv a0, sp` at `+0x20`), so the save counts as a read. This is not a
`va_list`: `Printf` and `Report` save only ra and their varargs registers, and it is that varargs save, read through
the `va_list`, that refuses `find +0x1c`. The CSTR rows this
refuses beyond the two the check named (`InitializeFlags +0x104`, `RegisterCommonFlags +0x1218`) are in
`ReportDeadlySignal`, `ErrorGeneric::Print`, `ErrorOutOfMemory::Print`, `ErrorODRViolation::Print`,
`ErrorRssLimitExceeded::Print`, `StackAddressDescription::Print` and `__lsan::PrintResults`. That makes 3 more NOT
CERTIFIED closure members (the three `Error*::Print`) and 4 more paircl members (the same three and `PrintResults`).
`__nl_langinfo_l +0xf8`, which a CSTR hand line used to settle as a whole row, now settles use by use: its byte-0 load
at `+0x100` reads the string's NUL, named by its own consumer line.

## What the audits changed (F1-F6, G1, G2, R1-R5, O1-O3)

| finding | what it was | what it is now |
|---|---|---|
| F1 `StackDepotGet` lui +0x24, bases +0x3c / +0x48 | `iii-disp` with the base called a loaded pointer; the base is the static `theDepot`, reached by auipc | settled by FULL ADDRESS: constant part `theDepot+0x400010` on XA / YA and XB / YB, plus the runtime index term `8 * (id >> 16)` |
| F2 / R1 `StackDepotGet` lui +0xc4, argument a0 at +0xd0 | `iii-disp`, then a mixed class whose "pointer part" came from the call at +0xc0 | the call at +0xc0 is `CheckFailed`, which never returns, so the edge +0xc0 -> +0xc4 is on no path (the tool drops the fall-through edge of every call to a function that never returns); the only value is `theDepot+0x400008`: **FULL-ADDRESS-EQUAL** on both images |
| F3 `StackDepotBase::Put` lui +0xc0, a3 at +0x168 / +0x17c | `iii-disp` granted to a raw constant by a wildcard ARG line | both uses settle as dead-at-call; the a0 uses keep class (iii) through register-qualified lines. The row is NOT CERTIFIED under G2 (s4 / s8 into `TwoLevelMap::Create`, `find` and `CheckFailed`, whose callees reach an indirect call) |
| F4 `StackDepotBase::find` lui +0x1c, a2 at +0x74 | same defect | dead-at-call (Create writes a2 at +0x1c). The row is NOT CERTIFIED: a2 at `ret +0xb0` goes up the caller chain to `Printf`'s varargs save (2a) |
| F5 dead-at-call citation | claimed the callee writes the register, which the tool did not check | checked (`callee_kills`, a tail call counted as a return point); the citation says what was checked |
| F6 / R4 plant outputs | made with older tools | the planted images were re-made and both plants re-run with exactly the committed tools; `records/plant-settle-*` carry no stale mark |
| G1 registers live at `ret` | only a0 / a1 were read at a `ret` | every register still holding the value at a `ret` goes to the callers and is settled only by the complete-caller test (data AND code references checked, each caller traced to the register's next write, chains followed) |
| G2 non-argument registers at calls | the callee-saved convention was assumed | every register holding the value at a call goes into the callee; it settles only if the callee reads it on no path (a stack save / restore is not a read); a path that ends at an indirect transfer or at the depth bound with the value live leaves the row NOT CERTIFIED |
| R2 the object-pointer test | any runtime leaf passed | at least one leaf must be a real object pointer (by the pinned signature, a load, or a pointer-returning call's a0); integer arguments, atomic results and a2-a7 after a call may only be index terms |
| R3 wildcard ARG lines | 7 left (they granted iii-disp to byte masks and shift counts) | removed; `tools/luiclass.tsv` holds per-register lines only (`<offset>@<register>`), and none with `*` for an argument use |
| R5 the CSTR "not a use" sentence | said the callee writes the register | says what is checked: the callee reads it on no path (for `internal_memset` and `StaticSpinMutex::LockSlow`, which do not write a6, the trace then goes on past the call) |
| 2a frame stores | every store of the register into a callee's frame was skipped | skipped only when the callee forms no sp-derived pointer and nothing reads the stored bytes back (except the restore of a save / restore pair); refuses `find +0x1c` |
| 2b tail calls in a caller | a value leaving a caller in a tail call was not followed | followed one level up when the tail callee may return it intact; refuses `__lsan_unregister_root_region +0x238` |
| extra: CSTR hand override | a CSTR hand line settled a whole row whatever its other uses showed | a row settles only when every use does; a hand line names the class of the store use(s) it cites; refuses `InitializeFlags +0x104`, `RegisterCommonFlags +0x1218` |
| 3 (check of 7047c7c1a9d) first event in `reads_after_call` | the caller test stopped at the first event in word order, so a `ret` or tail call that hands the value back could hide a real read at a later word on another path | every live word on every path is examined, and a real read anywhere wins over `RET-LIVE` (tested one level up). No verdict changed (every lui row with its per-use classes, every target and every member is identical on both images). The masked caller contexts are recorded as now examined in `records/reads-after-call-masked-asan.txt`: walking every caller chain from every `ret` use of image A in full (no stop at the first refusal), 2743 contexts, of which 90 (45 on X, 45 on Y) changed from `RET-LIVE` to a real read. This covers the reviewer's 25, among them `InternalAlloc +0x3c` a4, `LeakSuppressionContext::Suppress +0x100` a5 and `fflush +0xf0` a2, and the 8 contexts settle3's own runs query |
| 4 (check of 7047c7c1a9d) the printer mechanism | named `Printf` / `Report` / `VSNPrintf` and a `va_list` | corrected: the s-register saves are in `SharedPrintfCode` / `StackTrace::Print` (and `SharedPrintfCodeNoBuffer`, `VSNPrintf`), each passing the address of a local; `Printf` / `Report` save only ra and their varargs registers |
| 1 `sysconf +0x214` | settled with no reason given | NOT CERTIFIED: a call at a function's last word, or a tail call, whose callee may return without writing the register leaves the trace with nowhere to go |
| O1 psABI | relied on at calls and returns | not relied on anywhere (above) |
| O3 `dead-at-ret`, mixed `compare` | | settled classes; `dead-at-ret` only by the complete-caller test |

## The kit's fail-open #3: two lui values in one base

`tools/luipair.py` over the WHOLE compare set, **1729 function pairs per image** (785 closure + 944 paircl), 217 of
them with two or more lui words: **lui+lui->base: 10 sites, all a displacement on a runtime pointer, none an absolute
address**. The 10 are in `StackDepotBase<StackDepotNode,1,20>::Put` at +0x134, +0x150 and +0x154 (5 in the closure run
and the same 5 in the paircl run): the base is `this` or a loaded pointer plus `lui 0x400000 + 0x10` and a masked
index. 62 further bases hold two lui values only through a widened node (4 of them an auipc base: the De Bruijn ctz
table loads). In **0 of the 1729 pairs** does any lui word differ between X and Y, so no lui-built constant can
differ.

## The kit's known fail-opens: every base shape (a)-(h)

`tools/baseshapes.py` scans EVERY memory / jump base of EVERY compared function pair — 1729 pairs, of which 1727 are
analysed (**43 587 bases per image**) and 2 (one function, `parseFDEInstructions`, in both runs) are NOT CERTIFIED:
REAL 0 because the dataflow did not settle (below) — says which shapes built each base, and names the combined target
on both images:

| shape | bases | |
|---|---|---|
| (a) the load / store IMMEDIATE (V + imm as one address) | 31 865 | covered: the immediate is added before naming |
| (b) addi / addiw chains | 26 824 | covered |
| (c) ori / xori / slli (and the other logical / shift ops) | 3 669 | covered |
| (d) a stack spill (followed), an FP move or a CSR round trip | spills followed; 0 bases hold an FP or CSR leaf | an FP / CSR leaf would make the base RUNTIME here (never settled) |
| (e) a jump-table arm no decoded edge reaches | 386 | analysed with every value live at the function's indirect jumps, as the kit's own lui_scan does |
| (f) a call this scan cannot resolve to a sized FUNC (an in-function callee, a register-indirect call) | 2 314 | such a value is RUNTIME here, never settled |
| (g) c.lui / 2-byte parcels | 0 functions, 0 c.lui words | no compared function holds a 2-byte parcel |
| (h) an address built WITHOUT lui (auipc or arithmetic only) | 8 009 | covered |
| (none: a plain lo12 pair or a pointer) | 6 010 | |

Verdicts over those 43 587 bases, identical on A and B: **ADDRESS-EQUAL 3 435** (every leaf known: the full address is
the same symbol + offset on both images), **TERM-EQUAL 2 042** (an object address plus a runtime term: its constant
part is the same symbol + offset), **OFFSET-ON-POINTER 21 731** (a struct offset on a runtime pointer: no address to
name — the lui rows above settle those offsets), **RUNTIME 13 828** (a pointer from an argument, a load or a call),
**UNNAMED 2 551** (an address in a section that neither image names at that point: 2 071 are `.got` cells, which the
kit compares by what they hold, and 480 are unnamed read-only data, which the kit compares by bytes), and **0
DIFFERS**. **One function was not analysed** by this scan: `libunwind::CFI_Parser<LocalAddressSpace>::parseFDEInstructions`
(`_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE`,
5380 bytes, X A `0x83b84`), flagged once in the closure run and once in the paircl run (the 2 `NOT-ANALYSED` rows of
`records/baseshapes-<image>.txt`): its 1345-word body with a 48-way jump table did not let the expression dataflow
settle inside its step budget. Its bases are therefore **NOT CERTIFIED: REAL 0 by this scan** and counted so in the
totals below. Separately, the member itself is SETTLED: its only differing target, the +0x140 jump table, is read
entry by entry (BYHAND-JT32-rel, 48 entries equal on both images), which does not need this dataflow.

## The two planted controls, both refused

`tools/plant.py` writes the SAME three words into a copy of one X function and of its Y counterpart, so every word of
the pair stays equal and only the two layouts make the address they build name two different objects. Planted
function: `_ZN6__asan9Allocator22FindHeapChunkByAddressEm` at +0x10 (X `0x30954` / Y `0x30948`); the load base is
`0x98288` = `_ZTVN11__sanitizer11FlagHandlerIiEE+0x0` in X and `read+0x28` in Y.

| plant | words | what the kit does | what this record's settlement does |
|---|---|---|---|
| ADD | `lui a0,0x98 ; add a0,a0,zero ; ld a0,0x288(a0)` | reports the value as a `lui-in-section` target (both values `0x98000`) and leaves it to a hand argument | **REFUSED**: the trace carries it through the `add` into the load base and names `0x98288` as two different objects -> REAL |
| XOR | `lui a0,0x98 ; xor a0,a0,zero ; ld a0,0x288(a0)` | xor is a logical read and no pair is memory-fed, so the kit settles the value as `lui-const (dataflow)` and never compares the address (the fail-open) | **REFUSED**: the same trace through the `xor` -> REAL |

Both runs are the full pipeline (closure_strict3, paircl, jtcheck, settle3) on the planted images, made and run with
the tools in `tools/`: `records/plant-settle-add-summary.txt`, `records/plant-settle-xor-summary.txt` (each `REAL 2`:
the row in the closure run and in the paircl run), the rows in `records/plant-settle-*-targets.tsv`, the kit's own
view in `records/plant-closure-*.txt` / `records/plant-paircl-*.txt` (extracts: the header and every line naming the
planted function) and the planted images' sha256s in `records/plant-images.txt`. The extracts are the fail-open
itself: on the XOR-planted pair the closure run counts the same `other` total as the unplanted run and prints
`ACCEPT ... lui-const+0x10[0x98000|0x98000]` for the planted function, while on the ADD-planted pair it is reported.

## What a reader may and may not take from this

- May: on both images, every word of wire's `__asan_memmove` closure that the kit compares is equal up to pc-relative
  and lui-built fields; every pc-relative target the kit judges names the same thing on both sides; every target the
  kit leaves unsettled is measured here or listed; every memory base of every compared function was read for the
  eight shapes above; and no measurement found a difference (REAL 0).
- May not: that the 85 NOT CERTIFIED lui rows per image, the 30 + 33 NOT CERTIFIED CSTR rows or the 3 `unmeasured`
  words are equal in meaning. They are not measured; their words are equal, nothing more.
- The base-shape scan leaves the bases of one function, `parseFDEInstructions`, NOT CERTIFIED (above); its member
  verdict rests on the by-hand jump-table reading.
- The kit's OPEN KNOWN LIMITS 2, 3, 6 and 7 apply unchanged.

## Sources cited by the settlement

The parameter contracts, struct layouts and consumers cited in `tools/luiclass.tsv` are the PINNED source of these
images: LLVM at llvmorg-20.1.8 (87f0227cb60147a26a1eeb4fb06e3b505e9c7261) with theorem-labs/static-asan b0506135's
`patches/compiler-rt` applied, and musl at v1.2.6-20-gf21a9653 with its `patches/musl` applied — the bases
static-asan b0506135's `toolchain/Dockerfile` pins (MUSL_BASE f21a9653, LLVM_BASE 87f0227cb); the licence evidence of
`provenance/PROVENANCE.yaml` names the same LLVM tag.

## Commands (a fresh copy of the kit in ./kit, these tools in ./tools, the kit outputs in ./rec)

    sha256sum -c kit/SHA256SUMS
    python3 kit/drvcmp.py twins <pcap pin> <pcap twin>
    python3 kit/closure_strict3.py <wire twin> <pcap twin> __asan_memmove
    python3 kit/paircl.py <wire twin> <pcap pin> __asan_memmove <0x51bf0 A / 0x51c40 B> <pcap twin> --full --targets-out <TSV>
    python3 kit/jtcheck.py <wire twin> <pcap twin> <the non-certified function names, comma-separated>
    WIRE=<dir> PCAPU=<dir> PCAPP=<dir> tools/run-settle.sh          # settle3 on both images
    python3 tools/luipair.py kit <wire twin> <pcap pin> <pcap twin> rec/closure-<image>.txt rec/paircl-targets-<image>.tsv out
    python3 tools/baseshapes.py kit <wire twin> <pcap pin> <pcap twin> <0x51bf0 A / 0x51c40 B> out
    python3 tools/plant.py kit <wire twin> <pcap twin> <pcap pin> out/plants _ZN6__asan9Allocator22FindHeapChunkByAddressEm
    tools/run-plants.sh                                             # the full pipeline on the planted images
