# WIRE-B-ALLOC bytecmp record: fuzz_wire image B malloc / free chain against fuzz_grant image B

Read-only on every input. Version of record: **bytecmp 1480ca2faea0 + repin_check e5487165abb8, with the same
fail-closed target rule in `jtcheck.py` and `paircl.py`**. The rule: two different named targets, or a name on one side
only, are a target difference, and their contents are never compared. repin_check e5487165abb8 supersedes
9cbc3553c09e, whose target pass broke this rule. jtcheck.py 2e2f9c2126b2 and paircl.py 16e1466be22d broke it too; see
"The target-name rule" for all three. The earlier run (repin_check 9cbc3553c09e, jtcheck.py and paircl.py unchanged) is
kept in `v9cbc3553c09e/`. Apart from that, the method and tools are those of the UCI-B-ALLOC record; only the unit
changes. `./run.sh` repeats every measurement, for either version. The committed slice is `commit/` plus this file
(section "The committed slice"); the file names below are those in `commit/`.

**Verdict (bytecmp 1480ca2faea0 + repin_check e5487165abb8, fail-closed jtcheck and paircl): SAME CODE up to relocation. fuzz_wire B's malloc / free interceptor chain is equal to fuzz_grant B's (pinned fde52226dc48). Details: the 4 roots are EQUAL or EQUAL-mod-pcrel with target-differ 0; 825 closure functions pair one-to-one with 0 conflicts, 0 real and 0 unmeasured words; all 16 table rows are settled; the three planted changes (a word, a re-pointed call, a re-pointed .rodata address) were caught. Every measurement output is byte-identical to the earlier run's.**

## Method

This is the method of the image-B donor survey (repacer/B-DONORS.md): its "Method" section (lines 5-18) and its
fuzz_wire `__asan_memmove` section (lines 254-280). bytecmp is switched to 1480ca2faea0 as in the UCI-B-MEMCPY record
(commit 7af39d3f61c, `proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/RECORD.md`).

- **Roots:** compared with `drvcmp.py cmp`: bytecmp `cmp` plus the repin_check e5487165abb8 target pass. Two
  different named targets, or a name on one side only, are a target difference. A root counts as equal when it is
  EQUAL, or EQUAL-mod-pcrel with target-differ 0.
- **Target-paired closure (`paircl.py`, through `pairtable.py`):** wire B unstripped against the grant B **stripped
  pin**, starting at grant's address; every pairing must be one-to-one. Each target pair is also named, on X and on
  grant's unstripped twin, under the target rule.
- **By-name closure (`closure.py`):** against grant B's unstripped twin.
- **Table members:** checked with `jtcheck.py`, under the target rule; `cietable.py` covers the one row jtcheck
  cannot settle.
- **Stripped vs unstripped:** `drvcmp.py twins`.

## Tools (`tools/`, `tools.sha256`, `tools/DIFFS.md`)

All scripts are committed and run from the slice: their inputs are arguments, and `run.sh` takes the image paths from
an `env.sh` that is not committed (variables `UNIT X_S X_U GR_S GR_U ID_S ID_U`). `tools/DIFFS.md`, written by
`tools/mkdiffs.py`, gives each copy's sha256, its original's sha256 and source, and the unified diff original → copy.

| script | copy sha256 | original sha256 | source |
|---|---|---|---|
| `bytecmp-1480ca2faea0.py` | `145447a50bb2…` | `1480ca2faea0…` | tool registry commit 797e8971d27d, `tools/bytecmp/1480ca2faea0/bytecmp.py` (it carries insnflow a36c2b82eb44, lines 39-151) |
| `repin_check-e5487165abb8.py` | `7a69dadf5169…` | `e5487165abb8…` | tool registry commit f69e6d74ebe, `tools/repin_check/e5487165abb8/repin_check.py` (supersedes 9cbc3553c09e) |
| `drvcmp.py` | `1b13206c79dd…` | `27f7a0e92bb9…` | commit 7af39d3f61c, `…/evidence/uci-b-memcpy/drvcmp.py`: the image-B donor survey's drvcmp.py with bytecmp switched to 1480ca2faea0 |
| `jtcheck.py` | `f95cc8e243d1…` | `2e2f9c2126b2…` | image-B donor survey scripts, with the one-line fail-closed patch |
| `paircl.py` | `a88c2822a0f2…` | the same | tool registry commit b73d10eb732, `tools/paircl/a88c2822a0f2/paircl.py` (supersedes 16e1466be22d, the image-B donor survey's paircl.py) |
| `closure.py` | `b50998fb3bd3…` | the same | image-B donor survey scripts |
| `pairtable.py` | `f5760dd50c20…` | - | written for these records; it now passes Y's unstripped twin to paircl.py |
| `cietable.py` | `c82414f4b6d7…` | - | written for these records |
| `syms.py` | `ebf764d5cdf2…` | - | written for these records |
| `scrub_out.py` | `421e40db2b09…` | - | written for these records: the writer of `commit/` |
| `mkdiffs.py` | `6b1b976d4004…` | - | written for these records: the writer of `tools/DIFFS.md` |

**How the four changed copies differ from their originals, and what paircl a88c2822a0f2 changes:**
- **bytecmp and repin_check:** only in comments (agent, lane and branch names removed) and in their host-path
  constants, which they now read from the environment (default: empty). These records never run the code that reads
  those constants; the UCI-B-ALLOC record gives the details. In repin_check e5487165abb8, class `Img` is still at
  lines 31-59, and `sx` .. `w_off` is at lines 188-247 (it was 188-237 in 9cbc3553c09e).
- **drvcmp.py:** besides its docstring, two code lines. It now loads `repin_check-e5487165abb8.py` and takes `sx` ..
  `w_off` from lines 188-247 instead of 188-237.
- **jtcheck.py:** one code line, after `same_target`'s same-name test (`jtcheck.py:79`). A pair with two different
  names, or a name on one side only, returns a difference before any string, 8-byte or table compare. Its docstring
  states the rule.
- **paircl.py** is the registered a88c2822a0f2, byte for byte, so `tools/DIFFS.md` lists it as unchanged. Against
  16e1466be22d it adds two things. It takes a fifth argument, Y's unstripped twin (`paircl.py:39`). And it names every
  target pair before any pairing or content compare (`paircl.py:68-72`; a `.got` cell by the symbol it holds). Two
  different names, or a name on one side only, is a target difference (the function's row becomes "other"), with no
  content compare and no pairing. Its docstring states the rule.

**Earlier run, in `v9cbc3553c09e/tools/`** (its own `DIFFS.md`): the tools of the run before the fixes. It holds
`repin_check-9cbc3553c09e.py` (copy `a406b7c1b76e…` of `9cbc3553c09e…`, tool registry commit 797e8971d27d), the
drvcmp.py that loads it (`a4c8056e896a…`), the unchanged `jtcheck.py` (`2e2f9c2126b2…`) and `paircl.py`
(`16e1466be22d…`), and pairtable.py `1429e829dbe6…`. The other four measurement scripts are the same as above.

## Images (`images.sha256`, `twins.out`)

The raw outputs name each image by a token. `images.sha256` defines each token by sha256 and index line.

| token | file | sha256 | pin / twin check |
|---|---|---|---|
| `WIRE_B_PIN` | `fuzz_wire.asan-ubsan` | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` | index/binaries.tsv:7525 and `projects/reac-repacer/fuzz_wire/harness.yaml:64` @ f47e2a8927b9 and @ recipes 6d085644782c |
| `WIRE_B_TWIN` | `fuzz_wire.asan-ubsan`, unstripped | `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3` | PT_LOAD equal to the pin: 25 bytes differ, all in the ELF header / `.note.gnu.build-id`. Measured here; B-DONORS.md:7 had not checked it. |
| `GRANT_B_PIN` | `fuzz_grant.asan-ubsan` | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | index/binaries.tsv:5591 @ 4f87de75d67 (released) and @ 6d085644782c |
| `GRANT_B_TWIN` | `fuzz_grant.asan-ubsan`, unstripped | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | PT_LOAD equal to the pin |
| `IDENT_B_PIN` (control) | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | index/binaries.tsv:5595 @ f47e2a8927b9 and @ 6d085644782c |
| `IDENT_B_TWIN` (control) | `fuzz_identity.asan-ubsan`, unstripped | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` | PT_LOAD equal to the pin |
| `GRANT_B_{PIN,TWIN}_PLANTED_{ROOT,CALL,RODATA}` | the planted copies | see "Controls" | written by `run.sh`; not committed |

## Roots (`roots-syms.out`, `roots.tsv`)

The wire addresses of B-DONORS.md:157-162 are confirmed by wire's own symbol table. Grant's addresses are those
of the UCI-B-ALLOC record (grant `lib/B/YF0l.v:11-12` @ 4f87de75d67).

| root | wire B | grant B | size | verdict | pcrel | real | unmeasured | target-differ |
|---|---|---|---|---|---|---|---|---|
| `__interceptor_trampoline_malloc` | 0x52098 | 0x52edc | 4 | EQUAL | 0 | 0 | 0 | 0 |
| `___interceptor_malloc` | 0x5226c | 0x530b0 | 348 | EQUAL-mod-pcrel | 3 | 0 | 0 | 0 |
| `__interceptor_trampoline_free` | 0x52094 | 0x52ed8 | 4 | EQUAL | 0 | 0 | 0 | 0 |
| `___interceptor_free` | 0x5209c | 0x52ee0 | 464 | EQUAL-mod-pcrel | 3 | 0 | 0 | 0 |

## Closure

### Target-paired against the grant B pin (`paircl-*-grant.out`, `pairs-*-grant.tsv`)

| root | paired | EQUAL | EQUAL-mod-pcrel (targets paired) | other | pairing conflicts | real words | unmeasured words | name / size = grant symbol |
|---|---|---|---|---|---|---|---|---|
| `___interceptor_malloc` @ 0x530b0 | 825 | 212 | 599 | 14 | 0 | 0 | 0 | 825 / 825 |
| `___interceptor_free` @ 0x52ee0 | 825 | 212 | 599 | 14 | 0 | 0 | 0 | 825 / 825 |
| `__interceptor_trampoline_malloc` @ 0x52edc | 825 | 212 | 599 | 14 | 0 | 0 | 0 | 825 / 825 |
| `__interceptor_trampoline_free` @ 0x52ed8 | 825 | 212 | 599 | 14 | 0 | 0 | 0 | 825 / 825 |

- The four pair maps are identical.
- Over the 825 pairs, bytecmp gives EQUAL 212, EQUAL-mod-pcrel 613 and UNMEASURED 0, with pc-relative words 12455,
  **real 0** and unmeasured 0.
- The 14 "other" rows are all EQUAL-mod-pcrel with real 0: functions whose pc-relative target is a jump table or a
  constant pool longer than 8 bytes. They are the same 14 names as for uci B, as the identity control below and as
  B-DONORS.md's known-equal pcap control (line 265).
- The symbolic `tcmp` flags 3 functions: GetHandleSignalMode, SignalContext::Describe and `__synccall`. All 3 are in
  the jtcheck set.
- `__asan_memcpy` (0x50c14) and `__asan_memmove` (0x510b0) are not in this closure; `__asan_memset` is not in wire
  B's image at all (the UCI-B-ALLOC record's `INTERCEPTORS.md`).

### By name against grant B's twin (`closure-grant.out`)

- **Each of the 4 roots:** 784 functions (97 register-indirect call sites inside), EQUAL 200, EQUAL-mod-pcrel with
  all targets equal 581, other 3.
- **The 3 "other" rows** are the target-differ rows GetHandleSignalMode +0x24, SignalContext::Describe +0x1c and
  `__synccall` +0x54. They are the same 3 as for uci B.
- **Subset:** the 784 are a subset of the 825 target-paired functions. The 41 extra are address-taken functions.

### Table members (`jtcheck-members.txt`, `jtcheck-grant.out`, `cietable.out`)

The members checked are the same 16 functions as for uci B: the union of both passes' "other" rows.

- **15 of 16:** `target differs 0`, `unpaired differing words 0`.
- **parseCIE:** `target differs 1` at +0x23c. This is jtcheck's `bound()` limit; the UCI-B-ALLOC record explains it.
  `cietable.py` reads wire's table directly:
  - its base is 0x20c94;
  - the dispatch words +0x234 / +0x254 / +0x258 are the same as in uci B (47 entries);
  - all 47 entries point into parseCIE at the same function-relative offsets as in grant B and identity B.

**Real differences in the closure: 0.**

## Controls

**(a) Known-equal, identity B** (`roots.tsv` U:I rows, `closure-identity.out`, `ctl-pairtable-*-identity.out`, `ctl-pairs-*-identity.tsv`, `ctl-jtcheck-identity.out`):

- **Roots:** the wire-vs-identity-B rows reproduce B-DONORS.md exactly:
  - `__interceptor_trampoline_free` EQUAL 0 (line 157);
  - `___interceptor_free` EQUAL-mod-pcrel 3 (line 158);
  - `__interceptor_trampoline_malloc` EQUAL 0 (line 161);
  - `___interceptor_malloc` EQUAL-mod-pcrel 3 (line 162).
- **By-name closure:** 784 / 200 / 581 / other 3.
- **paircl against the identity pin** at 0x52de8 and 0x52c18:
  - 825 paired, 212 EQUAL, 599 EQUAL-mod-pcrel, other 14 (the same names), 0 conflicts;
  - real 0, unmeasured 0;
  - 825 / 825 name matches.
- **jtcheck:** the 11 wire rows of the donor survey's jtcheck run (repacer/B-DONORS.md line 14) come back
  0 / 0. parseCIE shows the same `bound()` row as against grant.

**(b) Planted changes** (`planted/planted.sha256`, `planted/planted.cmp`). Each pair of copies of grant B (stripped
copy for paircl, unstripped copy for the symbolic tools) has one changed word, at the same file offset in both.

| copy | word changed | stripped / unstripped sha256 |
|---|---|---|
| root | `___interceptor_malloc` 0x530b0+0x28 (file 0x420d8): `00008913` `addi s2,ra,0` → `00108913` | d7f2e10f4c3c / f6ef385ce8a5 (the same copies as in the UCI-B-ALLOC record) |
| call | `___interceptor_malloc` 0x530b0+0x130 (file 0x421e0): `98dde0ef` `jal __asan::asan_malloc` (0x31b6c, 92 bytes) → `cd9df0ef` `jal __sanitizer_get_allocated_begin` (0x32eb8, 92 bytes) | 1c85bde94bdb / 4aabaada3a62 |
| rodata | `__intscan` 0x95c04+0x4c8 (file 0x850cc): `79858a93` `addi s5,a1,1944` → `46058a93` `addi s5,a1,1120`, which re-points the address of `table` (0x22860, 257 bytes) to `all_mask` (0x22528, 8 bytes) | d4c374587adc / 7a86001f9ee0 |

The call and rodata copies each re-point one reference in the `___interceptor_malloc` closure to a different named
object whose compared bytes are the same:
- **call:** both functions are 92 bytes, and both begin with the same bytes up to the first NUL (`addi sp,sp,-16;
  sd ra,8(sp)` = `13 01 01 ff 23 34 11`).
- **rodata:** both objects begin with the same 8 bytes (`ff` × 8). `table` is not a string, so the original paircl
  compares only these 8 bytes.

The bytecmp verdict of every changed word stays EQUAL-mod-pcrel, so only a target pass can see these changes.

**Root copy:** caught under both versions. drvcmp gives `___interceptor_malloc DIFFERENT pcrel 3 real 1`, with the
other 3 roots unchanged. paircl gives other 15, 0 conflicts, and the new row is `___interceptor_malloc DIFFERENT
(pcrel 3 real 1)`.

**Call copy:**

| check | version of record (fail-closed tools) | earlier run (`v9cbc3553c09e/`) |
|---|---|---|
| drvcmp roots (`ctl-planted-call-roots.tsv`) | `___interceptor_malloc` target-differ 1 at +0x130 (`__asan::asan_malloc+0x0` vs `__sanitizer_get_allocated_begin+0x0`). **CAUGHT** | target-differ 0; the pair is counted `rodata-str-eq`. NOT CAUGHT |
| closure.py (`ctl-planted-call-closure.out`) | other 3 → 4 (`___interceptor_malloc`). **CAUGHT** | other 3. NOT CAUGHT |
| paircl (`ctl-planted-call-pairtable.out`, `-pairs.tsv`) | other 15, 0 conflicts; the new row is `___interceptor_malloc` with `named target differs` at +0x130. **CAUGHT** | other 15, 1 pairing conflict; `__asan::asan_malloc` paired with `__sanitizer_get_allocated_begin`, DIFFERENT real 19. **CAUGHT**, by the byte compare of the paired functions |
| jtcheck `___interceptor_malloc` (`ctl-planted-call-jtcheck.out`) | target differs 0, unpaired 0. **NOT CAUGHT**: jtcheck pairs only lo12 words (`tools/jtcheck.py:27`, `:162`), so it never looks at a `jal` target | the same. NOT CAUGHT |

jtcheck's job here is the jump-table and constant-table members, whose targets are lo12 pairs. A re-pointed `jal` is
outside what it compares. drvcmp, closure.py and paircl catch the call copy.

**Rodata copy:**

| check | version of record (fail-closed tools) | earlier run (`v9cbc3553c09e/`) |
|---|---|---|
| drvcmp `__intscan` (`ctl-planted-rodata-intscan.tsv`) | target-differ 1 at +0x4c8 (`table+0x0` vs `all_mask+0x0`). **CAUGHT** | target-differ 0; the pair is counted `const-eq`. NOT CAUGHT |
| jtcheck `__intscan` (`ctl-planted-rodata-jtcheck.out`) | target differs 1, `DIFF +0x4c8 table+0x0 \| all_mask+0x0`. **CAUGHT** | target differs 1, `DIFF +0x4c8 table rel4-str 10 entries`. **CAUGHT**, but only because it reads the target as a table and the table compare fails, not by name |
| closure.py (`ctl-planted-rodata-closure.out`) | other 3 → 4 (`__intscan`). **CAUGHT** | other 3. NOT CAUGHT |
| paircl (`ctl-planted-rodata-pairtable.out`, `-pairs.tsv`) | 825 paired, other 14 → 15, 0 conflicts; the new row is `__intscan` with `named target differs` at +0x4c8. **CAUGHT** | 825 paired, other 14, 0 conflicts; `__intscan` row `ok`. **NOT CAUGHT** |

## The target-name rule: repin_check, jtcheck and paircl

The rule is the one repin_check e5487165abb8 introduced: two different named targets, or a name on one side only, are
a target difference, and their contents are never compared. Before the fixes, three comparers broke it:
- **repin_check 9cbc3553c09e `tcmp`:** it compared two named targets by the bytes up to the first NUL, a jump table or 8
  bytes. Fixed in e5487165abb8. The call and rodata copies above show the miss.
- **jtcheck.py 2e2f9c2126b2 `same_target`** (`v9cbc3553c09e/tools/jtcheck.py:77-85`): after the same-name test (:77),
  a named pair falls through to a table read (:78-79), the NUL-cut string (:80-81), a memcpy initializer (:82-83) and
  the 8 bytes (:84-85).
  - Fixed by the one-line patch (`tools/jtcheck.py:79`).
  - The patch's known-answer control, on `fuzz_boxreg.asan` (sha256 4532568b621d), uses `kInterceptorName` (0x20910)
    and `kInterceptorViaFunction` (0x20921), two named .rodata objects whose first 8 bytes are both `interceptor`'s
    first 8 letters.
  - Result: the unpatched copy returns `(True, 'const 696e746572636570')` and the patched copy returns `False`. This
    holds both for the control's own copies and for this record's two copies.
- **paircl.py 16e1466be22d:** Y is the stripped image (`Raw`, `v9cbc3553c09e/tools/paircl.py:19-33`: no symbols), so
  paircl never sees a name on Y's side. It reads target pairs in three ways:
  - a target that starts an X function is paired by position only (`:64-70`), and the pair's bytes are compared later;
  - a `.rodata` target is compared by content only, the NUL-cut string or else the first 8 bytes (`:71-76`);
  - a `.got`, `.data` or `.data.rel.ro` target is not compared at all (`:77-78`).

  So two different named .rodata objects with the same compared bytes count as equal. The rodata copy shows it. The
  fix is paircl a88c2822a0f2, registered at tool registry commit b73d10eb732 (`tools/paircl.py:39, 68-72`). It takes
  Y's unstripped twin and names every target pair first (a `.got` cell by the symbol it holds). A name difference
  becomes a target difference with no content compare and no pairing.

**Residual gap, not changed:** a target pair with no symbol on either side still gets only the content compare in
each tool. In paircl (`tools/paircl.py:86-87`), unnamed `.data` and `.data.rel.ro` cells get no compare at all. In this
record such pairs are covered by drvcmp's `tcmp`: the 3 `(section)` rows in the "Closure" section, each settled by
jtcheck.

## Rows that changed

**None.** `v9cbc3553c09e/` is the same `run.sh` with the earlier tools (`./run.sh v9cbc3553c09e/tools v9cbc3553c09e`).
- **Version of record vs earlier run:** apart from the planted-call and planted-rodata controls, every file of the two
  runs is byte-identical (27 files). Only the 9 planted-control outputs in the tables above differ, plus
  `tools.sha256`. So every count of this record is the same under both versions: no root or closure row moved.
- **No hidden name difference:** none of the fixed tools reports a target difference that the earlier tools did not.
  So no real target pair of wire B has two different names, or a name on one side only.
  - This covers drvcmp / closure.py, jtcheck (`jtcheck-grant.out`, `ctl-jtcheck-identity.out`: unchanged) and paircl
    (`paircl-*-grant.out`, `pairs-*-grant.tsv`, the identity controls: unchanged).
- **The earlier run is reproducible:** re-run with the same tools, its measurement outputs are byte-identical to the
  record's previous committed run (26 files).

## Limits

- **Code only.** The 97 register-indirect call sites in the closure, and the `.got` / `.data` / `.data.rel.ro` cells,
  are not covered by a code comparison (B-DONORS.md line 251).
- **Not a proof of context.** "Same code" does not say that grant's released walks prove the chain in wire B's call
  contexts (B-DONORS.md line 18).

## Files (all in `commit/`)

- **Version of record:**
  - inputs and pins: `images.sha256`, `twins.out`, `roots-syms.out`, `tools.sha256`, `tools/` (with `DIFFS.md`);
  - roots: `roots.tsv`;
  - closure: `paircl-{malloc,free,tmalloc,tfree}-grant.out`, `pairtable-*-grant.out`, `pairs-*-grant.tsv`,
    `closure-grant.out`, `jtcheck-members.txt`, `jtcheck-grant.out`, `cietable.out`;
  - controls: `closure-identity.out`, `ctl-*` (with `ctl-planted-call-*` and `ctl-planted-rodata-*`),
    `planted/planted.sha256`, `planted/planted.cmp`.
- **Earlier run:** `v9cbc3553c09e/`, the same file names, with its own `tools/` (and `DIFFS.md`) and `tools.sha256`.
- **Re-run:** `run.sh` (`./run.sh` for the version of record; `./run.sh v9cbc3553c09e/tools v9cbc3553c09e` for the
  earlier run).
  - It needs an `env.sh` beside it that sets `UNIT=fuzz_wire` and `X_S X_U GR_S GR_U ID_S ID_U` to the six images of
    the table above.
  - It writes the planted copies `planted/grantB-{S,U}-{root,call,rodata}.elf` (tokens
    `GRANT_B_{PIN,TWIN}_PLANTED_{ROOT,CALL,RODATA}`; not committed), and their sha256 in `planted/planted.sha256`.
  - Its last step writes `commit/`.

## The committed slice

`commit/` holds everything committed except this file and MANIFEST.md. Its last writer is `tools/scrub_out.py`, the
last step of `run.sh`, as in the UCI-B-ALLOC record:
- in the raw outputs, each image path becomes its token;
- the tool scripts and `run.sh` are copied byte for byte;
- it refuses its own output if a host path, an internal branch prefix, a worker name or the tool registry's branch
  name is left.

**Checks (2026-10-30, after the fail-closed jtcheck and paircl):**
- **Only tokens rewritten:** replacing each token in `commit/` by its image path gives back every raw output of both
  runs byte for byte (78 files).
- **Same numbers as before the fixes:** the version of record's measurement files are byte-identical to those of the
  record's previous run (repin_check 9cbc3553c09e, jtcheck.py and paircl.py unchanged; 29 files, 85,457 numbers). The
  numbers diff is empty.
- **Runnable from the slice:** `run.sh` (both versions), run from a copy of `commit/` with an `env.sh` beside it, wrote
  a `commit/` identical to this one (`diff -r`: no difference).
- **Scanner of record:** run over this slice at its repository path (`commit/` plus this file), it reported 0 files
  with an uncleared flag-tier hit.
