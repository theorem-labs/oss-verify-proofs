# UCI-B-ALLOC bytecmp record: fuzz_uci image B malloc / free chain against fuzz_grant image B

Read-only on every input. Version of record: **bytecmp 1480ca2faea0 + repin_check e5487165abb8, with the same
fail-closed target rule in `jtcheck.py` and `paircl.py`**. The rule: two different named targets, or a name on one side
only, are a target difference, and their contents are never compared (section "The two tool defects"). Two earlier
versions are kept, each in its own directory:
- `v9cbc3553c09e/`: the previous version of record (bytecmp 1480ca2faea0 + repin_check 9cbc3553c09e, jtcheck.py and
  paircl.py unchanged);
- `v7daa0e2a03d9/`: the first run (bytecmp 7daa0e2a03d9), given as a second column below.

`./run.sh` repeats every measurement, for each version. The committed slice is `commit/` plus this file (section "The
committed slice"); the file names below are those in `commit/`.

**Verdict (bytecmp 1480ca2faea0 + repin_check e5487165abb8, fail-closed jtcheck and paircl): SAME CODE up to relocation. fuzz_uci B's malloc / free interceptor chain is equal to fuzz_grant B's (pinned fde52226dc48), the donor of uci B's lib/B/YF0w.v / YF0q.v. Details: the 4 roots are EQUAL or EQUAL-mod-pcrel with target-differ 0; 825 closure functions pair one-to-one with 0 conflicts, 0 real and 0 unmeasured words; all 16 table rows are settled; all four planted changes were caught. No row changed against the previous version of record, and bytecmp 7daa0e2a03d9 gives the same verdict.**

## The theorems

Image B's malloc / free contracts are already CLOSED in the base `f47e2a8927b9` (the image-B core, relocated from
fuzz_grant's released lib/B, recipes `4f87de75d67`):
- `lib/B/YF0w.v:45` `tfib_amalloc_realizes : forall fx rc B, UciSyms B -> (forall t, as_dhash B t = tfib_dhash t) ->
  amalloc_realizes tfibsegs B`;
- `lib/B/YF0q.v:11` `afree_realizes_closed : forall fx rc B, UciSyms B -> (forall t, ...) -> afree_realizes tfibsegs B`.

The one new file `lib/B/UciBRtAlloc.v` applies them at the runtime record `UciB` (the twin of grant's released
`lib/B/GrantBCloseInst.v:189-193`, grantB_MALLOC / grantB_FREE). The premises are discharged by `UciB_syms`
(`lib/B/YD2l.v:75`) and by `eq_refl` (`YD2l.v:35`, `as_dhash := tfib_dhash`):
- `:16` `uciB_MALLOC : forall fx rc, @amalloc_realizes fx rc tfibsegs UciB`;
- `:19` `uciB_FREE : forall fx rc, @afree_realizes fx rc tfibsegs UciB`.

No contract text is restated: the composition takes the landed predicates verbatim.

**Build:** `cb build` (dune), FACTS `25e3d17bdb50`, targets `lib/B/UciBRtAlloc.vo` plus a scratch `Check` / `Print
Assumptions` probe (not committed). Result: rc=0, 2 targets compiled, 0 failed, `4 PINNED, 0 MISMATCH, 0 MISSING,
0 UNPINNED, 0 ABSENT`. A probe of `tfib_amalloc_realizes` / `afree_realizes_closed` on the bare base also gave rc=0.

**Print Assumptions:**
- `uciB_MALLOC`: the Rocq primitives (PrimInt63 / PrimString / PrimArray) and `functional_extensionality_dep`;
- `uciB_FREE`: the same plus `Classical_Prop.classic`.

All of these are on `toolchain/allowed-axioms.txt`.

## Method

This is the method of the image-B donor survey (repacer/B-DONORS.md): its "Method" section (lines 5-18) and its
fuzz_wire `__asan_memmove` section (lines 254-280). bytecmp is switched to 1480ca2faea0 the same way as in the
UCI-B-MEMCPY record (commit 7af39d3f61c, `proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/RECORD.md`,
"Donor byte compare"): only `drvcmp.py`'s bytecmp file changes, and every tool that loads drvcmp.py follows it.

- **Roots:** the four entries the donor files name, by symbol in each unstripped twin. Each root pair is compared with
  bytecmp `cmp` plus the repin_check e5487165abb8 `targets()` / `tcmp` target pass (`drvcmp.py cmp`). Two different
  named targets, or a name on one side only, are a target difference. A root counts as equal when it is EQUAL, or
  EQUAL-mod-pcrel with target-differ 0.
- **Closure, target-paired (`paircl.py`):** X = uci B unstripped, Y = grant B **stripped pin**, starting at grant's
  address. The i-th pc-relative target of X is paired with the i-th of Y, and every pairing must be one-to-one. Each
  target pair is also named, on X and on grant's unstripped twin, under the target rule.
  `pairtable.py` runs paircl.py through `runpy` and writes one TSV row per pair with:
  - the bytecmp counts;
  - the grant symbol at the paired address, read from grant's unstripped twin;
  - the symbolic `tcmp` target-differ count.
- **Closure, by name (`closure.py`):** the direct-call closure in uci B (jal / auipc+jalr / .got; register-indirect
  calls are counted, not followed). Each member is compared by name and size with grant B's twin (`tcmp`).
- **Table members:** every closure member that either pass leaves as "other" is checked with `jtcheck.py`, under the
  target rule. The single row jtcheck cannot settle is read directly with `cietable.py`.
- **Stripped vs unstripped:** `drvcmp.py twins`. The PT_LOAD bytes are equal outside the ELF header and the build id,
  so a symbolic result on a twin holds for its pinned image.

## Tools (`tools/`, `tools.sha256`, `tools/DIFFS.md`)

Every script these records ran is committed in `tools/` and runs from the slice: its inputs are arguments, and
`run.sh` takes the image paths from an `env.sh` that is not committed (variables `UCI_S UCI_U GR_S GR_U ID_S ID_U`).
`tools/DIFFS.md`, written by `tools/mkdiffs.py`, gives each copy's sha256, its original's sha256 and source, and the
unified diff original → copy.

| script | copy sha256 | original sha256 | source |
|---|---|---|---|
| `bytecmp-1480ca2faea0.py` | `0ac2ec8db277…` | `1480ca2faea0…` | tool registry commit 797e8971d27d, `tools/bytecmp/1480ca2faea0/bytecmp.py`; its lines 39-151 are insnflow a36c2b82eb44 (`tools/insnflow/a36c2b82eb44/insnflow.py`, same commit), which it carries instead of importing |
| `repin_check-e5487165abb8.py` | `f268a01b33c5…` | `e5487165abb8…` | tool registry commit f69e6d74ebe, `tools/repin_check/e5487165abb8/repin_check.py` (supersedes 9cbc3553c09e) |
| `drvcmp.py` | `1b13206c79dd…` | `27f7a0e92bb9…` | commit 7af39d3f61c, `…/evidence/uci-b-memcpy/drvcmp.py`: the image-B donor survey's drvcmp.py with bytecmp switched to 1480ca2faea0 |
| `jtcheck.py` | `f95cc8e243d1…` | `2e2f9c2126b2…` | image-B donor survey scripts, with the one-line fail-closed patch |
| `paircl.py` | `a88c2822a0f2…` | the same | tool registry commit b73d10eb732, `tools/paircl/a88c2822a0f2/paircl.py` (supersedes 16e1466be22d, the image-B donor survey's paircl.py) |
| `closure.py` | `b50998fb3bd3…` | the same | image-B donor survey scripts (also the UCI-B-MEMCPY copy) |
| `pairtable.py` | `f5760dd50c20…` | - | written for these records: runs paircl.py (with grant's unstripped twin), one TSV row per pair |
| `cietable.py` | `c82414f4b6d7…` | - | written for these records: reads parseCIE's jump table |
| `syms.py` | `ebf764d5cdf2…` | - | written for these records: symbol lookup |
| `scrub_out.py` | `4ee202522d78…` | - | written for these records: the writer of `commit/` |
| `mkdiffs.py` | `bd50962aa1a6…` | - | written for these records: the writer of `tools/DIFFS.md` |

These are the same 11 scripts, with the same sha256s, as the EGRESS-B-ALLOC and WIRE-B-ALLOC records' `tools/`.

**How the four changed copies differ from their originals, and what paircl a88c2822a0f2 changes:**
- **bytecmp and repin_check:** only in comments (agent, lane and branch names removed) and in their host-path
  constants. These constants are now read from the environment, default empty: bytecmp's `base` (`BYTECMP_BASE_A` /
  `_B`, with the `os` import this needs) and repin_check's `IMG` / `PIN` (`REPIN_IMG_*` / `REPIN_PIN_*`). These
  records never run the `main` of bytecmp or repin_check, which are the only code that reads those constants. In
  repin_check e5487165abb8, class `Img` is still at lines 31-59, and `sx` .. `w_off` is at lines 188-247 (188-237 in
  9cbc3553c09e).
- **drvcmp.py:** besides its docstring, two code lines. It loads `repin_check-e5487165abb8.py` and takes `sx` ..
  `w_off` from lines 188-247.
- **jtcheck.py:** one code line after `same_target`'s same-name test (`jtcheck.py:79`). It returns a difference for two
  different names, or a name on one side only, before any string, 8-byte or table compare. Its docstring states the
  rule.
- **paircl.py** is the registered a88c2822a0f2, byte for byte, so `tools/DIFFS.md` lists it as unchanged. Against
  16e1466be22d it adds two things. It takes a fifth argument, Y's unstripped twin (`paircl.py:39`). And it names every
  target pair before any pairing or content compare (`paircl.py:68-72`; a `.got` cell by the symbol it holds).

**Previous version of record, in `v9cbc3553c09e/tools/`** (its own `DIFFS.md`): `repin_check-9cbc3553c09e.py`
(copy `15045c02875c…` of `9cbc3553c09e…`, tool registry commit 797e8971d27d), the drvcmp.py that loads it
(`a4c8056e896a…`), the unchanged `jtcheck.py` (`2e2f9c2126b2…`) and `paircl.py` (`16e1466be22d…`), and pairtable.py
`1429e829dbe6…`. The other four measurement scripts are the same as above.

**First run, in `v7daa0e2a03d9/tools/`** (its own `DIFFS.md`): as `v9cbc3553c09e/tools/`, except three scripts:

| script | copy sha256 | original sha256 | source |
|---|---|---|---|
| `bytecmp-7daa0e2a03d9.py` | `d8c4befbf695…` | `7daa0e2a03d9…` | tool registry commit 797e8971d27d, `tools/bytecmp/7daa0e2a03d9/bytecmp.py` |
| `drvcmp.py` | `4c3feca0363d…` | `fbbdb144ddfc…` | image-B donor survey scripts (it loads bytecmp 7daa0e2a03d9) |
| `pairtable.py` | `c3f983a0289c…` | - | written for these records. The same code as `1429e829dbe6`; its docstring names bytecmp 7daa0e2a03d9 |

**What differs between the two bytecmp versions.** 1480ca2faea0 uses insnflow's `flow_states`. A word reached only
through an indirect jump (a jump-table case) starts a block where every register is UNKNOWN, so an auipc inside the case
pairs with its consumer. 7daa0e2a03d9 gave such words no state, so their differing lo12 words read as UNMEASURED.

## Images (`images.sha256`, `twins.out`)

The raw outputs name each image by a token. `images.sha256` defines each token by sha256 and index line.

| token | file | sha256 | pin / twin check |
|---|---|---|---|
| `UCI_B_PIN` | `fuzz_uci.asan-ubsan` | `a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc` | index/binaries.tsv:7521 and `proofs/reac-repacer/fuzz_uci/provenance/PROVENANCE.yaml:83` @ f47e2a8927b9 |
| `UCI_B_TWIN` | `fuzz_uci.asan-ubsan`, unstripped | `8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16` | PT_LOAD equal to the pin: 25 bytes differ, all in the ELF header / `.note.gnu.build-id` |
| `GRANT_B_PIN` | `fuzz_grant.asan-ubsan` | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | index/binaries.tsv:5591 @ 4f87de75d67 (released) and @ f47e2a8927b9; `proofs/libreac/fuzz_grant/provenance/PROVENANCE.yaml:81` @ 4f87de75d67 |
| `GRANT_B_TWIN` | `fuzz_grant.asan-ubsan`, unstripped | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | PT_LOAD equal to the pin (the same 25 header / build-id bytes) |
| `IDENT_B_PIN` (control) | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | index/binaries.tsv:5595 @ f47e2a8927b9 |
| `IDENT_B_TWIN` (control) | `fuzz_identity.asan-ubsan`, unstripped | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` | PT_LOAD equal to the pin |
| `GRANT_B_{PIN,TWIN}_PLANTED_{DEEP,ROOT,CALL,RODATA}` | the planted copies | see "Controls" | written by `run.sh`; not committed |

## Roots (`roots-syms.out`, `roots.tsv`)

Grant B's addresses are confirmed from grant's own symbol table. They are also the ones the released donor names:
grant `lib/B/YF0l.v:11-12` @ 4f87de75d67 gives `pc_malloc := 0x530b0; pc_wrap_malloc := 0x52edc; pc_malloc_ra0 := 0x53178`
and `pc_free := 0x52ee0; pc_wrap_free := 0x52ed8; pc_free_ra0 := 0x53018`. Uci's `lib/B/YF0l.v:12-13` @ f47e2a8927b9
gives 0x5195c / 0x51788 / 0x51a24 and 0x5178c / 0x51784 / 0x518c4. The return-address offsets agree: malloc +0xc8,
free +0x138.

| root | uci B | grant B | size | verdict | pcrel | real | unmeasured | target-differ |
|---|---|---|---|---|---|---|---|---|
| `__interceptor_trampoline_malloc` | 0x51788 | 0x52edc | 4 | EQUAL | 0 | 0 | 0 | 0 |
| `___interceptor_malloc` | 0x5195c | 0x530b0 | 348 | EQUAL-mod-pcrel | 3 | 0 | 0 | 0 |
| `__interceptor_trampoline_free` | 0x51784 | 0x52ed8 | 4 | EQUAL | 0 | 0 | 0 | 0 |
| `___interceptor_free` | 0x5178c | 0x52ee0 | 464 | EQUAL-mod-pcrel | 3 | 0 | 0 | 0 |

bytecmp 7daa0e2a03d9 gives the same rows: `v7daa0e2a03d9/roots.tsv` is byte-identical.

## Closure

### Target-paired against the grant B pin (`paircl-*-grant.out`, `pairs-*-grant.tsv`)

| root | paired | EQUAL | EQUAL-mod-pcrel (targets paired) | other | pairing conflicts | real words | unmeasured words | name / size = grant symbol |
|---|---|---|---|---|---|---|---|---|
| `___interceptor_malloc` @ 0x530b0 | 825 | 184 | 627 | 14 | 0 | 0 | 0 | 825 / 825 |
| `___interceptor_free` @ 0x52ee0 | 825 | 184 | 627 | 14 | 0 | 0 | 0 | 825 / 825 |
| `__interceptor_trampoline_malloc` @ 0x52edc | 825 | 184 | 627 | 14 | 0 | 0 | 0 | 825 / 825 |
| `__interceptor_trampoline_free` @ 0x52ed8 | 825 | 184 | 627 | 14 | 0 | 0 | 0 | 825 / 825 |

The four pair maps are identical, because asan's allocator start-up pulls in the whole runtime. bytecmp counts over the
825 pairs, per version:

| over the 825 pairs | 1480ca2faea0 | 7daa0e2a03d9 |
|---|---|---|
| EQUAL / EQUAL-mod-pcrel / UNMEASURED functions | 184 / 641 / 0 | 184 / 633 / 8 |
| pc-relative / real / unmeasured words | 12982 / **0** / 0 | 12823 / 0 / 159 |
| paircl other / pairing conflicts | 14 / 0 | 14 / 0 (the same 14 names, the same pair map) |
| functions with symbolic `tcmp` target-differ | 3 | 3 |

- **Effect of the version change:** under 1480ca2faea0, all 159 words that 7daa0e2a03d9 left unmeasured are
  pc-relative (12823 + 159 = 12982), and its 8 UNMEASURED functions become EQUAL-mod-pcrel. Nothing else changes.
- **The 14 "other" rows** are all real 0 and all EQUAL-mod-pcrel under 1480ca2faea0. Each is a function whose
  pc-relative target is a jump table or a constant pool longer than 8 bytes, which paircl cannot pair without symbols.
  They are the same 14 names as the known-equal pcap control of the image-B donor survey (repacer/B-DONORS.md line
  265) and as the identity control below.
- **The symbolic `tcmp`** flags 3 functions: GetHandleSignalMode +0x24, SignalContext::Describe +0x1c and
  `__synccall` +0x54. All 3 are in the jtcheck set.

### By name against grant B's twin (`closure-uci-grant.out`)

| each of the 4 roots | 1480ca2faea0 | 7daa0e2a03d9 |
|---|---|---|
| closure (register-indirect call sites inside) | 784 (97) | 784 (97) |
| EQUAL / EQUAL-mod-pcrel with all targets equal / other | 172 / 609 / 3 | 172 / 601 / 11 |

- **The 3 "other" rows (1480ca2faea0)** are the target-differ rows GetHandleSignalMode, SignalContext::Describe and
  `__synccall`. These are the same 3 that the UCI-B-MEMCPY record found and resolved in the same image pair.
- **7daa0e2a03d9's 11** are these 3 plus 8 UNMEASURED members. They are the 11 jump/constant-table members that
  B-DONORS.md lists for uci against identity B (its line 14, and the table rows of lines 61-73).
- **Subset:** the 784 by-name members are a subset of the 825 target-paired ones. The 41 extra are address-taken
  functions that paircl follows and closure.py does not (for example `__lsan::LockAllocator`, `__asan::AsanDie`,
  `asan_atexit`).

### Table members: jtcheck, uci B vs grant B's twin (`jtcheck-uci-grant.out`, `cietable.out`)

The members checked are the union of the "other" rows of both passes: 16 functions (`jtcheck-members.txt`), the same set
under both versions. The jtcheck and cietable outputs are byte-identical under both versions.

- **15 of 16:** `target differs 0`, `unpaired differing words 0`. This includes the 3 symbolic rows:
  - GetHandleSignalMode: an 8-entry pointer table;
  - SignalContext::Describe: an 8-entry pointer table and a string table;
  - `__synccall`: 5 lo12 pairs, all with the same target.
- **The 16th is `libunwind::CFI_Parser::parseCIE`**, with `target differs 1` at +0x23c. This is a limit of jtcheck,
  not a code difference. `cietable.py` measures it:
  - +0x23c loads a rel4 jump-table base into s6. Its dispatch comes after the auipc: `addi s5,zero,46` (+0x234),
    `addi a1,a0,-76` (+0x254), `bltu s5,a1` (+0x258), then `slli; add s6; lw; add s6; jr` (+0x25c-+0x26c). That makes
    47 entries.
  - jtcheck's `bound()` looks only before the auipc. It takes the unrelated `addi a1,zero,255` + `bgeu` at
    +0x210/+0x214 and asks for 255 entries. So `table()` fails at entry 47 and falls back to an 8-byte compare.
  - Read directly, all 47 entries point into parseCIE at the **same function-relative offsets** in uci B, grant B and
    identity B.
  - The same row appears against identity B.

**Real differences in the closure: 0.** No unpaired differing word, no target difference that is not settled, no
unmeasured word.

## Controls (results with the version of record; 7daa0e2a03d9 in brackets where it differs)

**(a) Known-equal, identity B** (`roots.tsv` U:I rows, `closure-uci-identity.out`, `ctl-pairtable-*-identity.out`, `ctl-pairs-*-identity.tsv`, `ctl-jtcheck-uci-identity.out`):

- **Roots:** the uci-vs-identity-B rows reproduce B-DONORS.md exactly:
  - `__interceptor_trampoline_free` EQUAL 0 (line 40);
  - `___interceptor_free` EQUAL-mod-pcrel 3 (line 41);
  - `__interceptor_trampoline_malloc` EQUAL 0 (line 44);
  - `___interceptor_malloc` EQUAL-mod-pcrel 3 (line 45).
- **By-name closure:** 784 / 172 / 609 / other 3 [601 / 11], the same rows as against grant.
- **paircl against the identity pin** at 0x52de8 and 0x52c18:
  - 825 paired, 184 EQUAL, 627 EQUAL-mod-pcrel, other 14 (the same 14 names), 0 conflicts;
  - real 0, unmeasured 0 [159];
  - 825 / 825 name matches.
- **jtcheck:** the 11 uci rows of the donor survey's jtcheck run (repacer/B-DONORS.md line 14) come back 0 / 0.
  parseCIE shows the same `bound()` row as against grant.
- **Conclusion:** against grant B the method gives the same result as against a donor already known to be equal.

**(b) Planted changes** (`planted/planted.sha256`, `planted/planted.cmp`). Each copy of grant B has one changed word.
The change is made at the same file offset in a stripped copy (for paircl) and an unstripped copy (for the symbolic
tools).

| copy | word changed | stripped / unstripped sha256 | result |
|---|---|---|---|
| deep | `__asan::Allocator::Allocate` 0x31bc8+0x38 (file 0x20c00): `00078493` `addi s1,a5,0` → `00178493` | bb1b46859e27 / a397151cd84d | paircl from `___interceptor_malloc`: 825 paired, other **15**, 0 conflicts. The only new row is `Allocator::Allocate 0x30e34 0x31bc8 DIFFERENT (pcrel 92 real 1 unmeasured 0)`; TSV total real 0 → 1. closure.py: other 4 [12] = the 3 [11] + `Allocate DIFFERENT`; EQUAL-mod-pcrel 609 → 608 [601 → 600]. **CAUGHT** (all versions) |
| root | `___interceptor_malloc` 0x530b0+0x28 (file 0x420d8): `00008913` `addi s2,ra,0` → `00108913` | d7f2e10f4c3c / f6ef385ce8a5 | drvcmp: `___interceptor_malloc DIFFERENT pcrel 3 real 1`; the other 3 roots are unchanged. paircl: other 15, the new row is `___interceptor_malloc DIFFERENT (pcrel 3 real 1 unmeasured 0)`. **CAUGHT** (all versions) |
| call | `___interceptor_malloc` 0x530b0+0x130 (file 0x421e0): `98dde0ef` `jal __asan::asan_malloc` (0x31b6c, 92 bytes) → `cd9df0ef` `jal __sanitizer_get_allocated_begin` (0x32eb8, 92 bytes) | 1c85bde94bdb / 4aabaada3a62 | see the table below |
| rodata | `__intscan` 0x95c04+0x4c8 (file 0x850cc): `79858a93` `addi s5,a1,1944` → `46058a93` `addi s5,a1,1120`, which re-points the address of `table` (0x22860, 257 bytes) to `all_mask` (0x22528, 8 bytes) | d4c374587adc / 7a86001f9ee0 | see the table below |

In the deep and root copies, `diff` against the unplanted outputs shows only the planted function's row, the totals
and the image line.

The call and rodata copies each re-point one reference in the `___interceptor_malloc` closure to a different named
object whose compared bytes are the same:
- **call:** both functions are 92 bytes and begin with the same bytes up to the first NUL (`13 01 01 ff 23 34 11`);
- **rodata:** both objects begin with the same 8 bytes (`ff` × 8).

The bytecmp verdict of the changed word stays EQUAL-mod-pcrel, so only a target pass can see these changes. They are
the same copies as in the EGRESS-B-ALLOC and WIRE-B-ALLOC records.

| copy | check | version of record (fail-closed tools) | previous version (`v9cbc3553c09e/`) |
|---|---|---|---|
| call | drvcmp roots (`ctl-planted-call-roots.tsv`) | `___interceptor_malloc` target-differ 1 at +0x130 (`__asan::asan_malloc+0x0` vs `__sanitizer_get_allocated_begin+0x0`). **CAUGHT** | target-differ 0; the pair is counted `rodata-str-eq`. NOT CAUGHT |
| call | closure.py (`ctl-planted-call-closure.out`) | other 3 → 4 (`___interceptor_malloc`). **CAUGHT** | other 3. NOT CAUGHT |
| call | paircl (`ctl-planted-call-pairtable.out`, `-pairs.tsv`) | 812 paired, other 15, 0 conflicts; the new row is `___interceptor_malloc` with `named target differs` at +0x130. **CAUGHT** | other 15, 1 pairing conflict; `__asan::asan_malloc` paired with `__sanitizer_get_allocated_begin`, DIFFERENT real 19. **CAUGHT**, by the byte compare of the paired functions |
| call | jtcheck `___interceptor_malloc` (`ctl-planted-call-jtcheck.out`) | target differs 0. **NOT CAUGHT**: jtcheck pairs only lo12 words (`tools/jtcheck.py:27`, `:162`), so it never looks at a `jal` target | the same. NOT CAUGHT |
| rodata | drvcmp `__intscan` (`ctl-planted-rodata-intscan.tsv`) | target-differ 1 at +0x4c8 (`table+0x0` vs `all_mask+0x0`). **CAUGHT** | target-differ 0; the pair is counted `const-eq`. NOT CAUGHT |
| rodata | jtcheck `__intscan` (`ctl-planted-rodata-jtcheck.out`) | target differs 1, `DIFF +0x4c8 table+0x0 \| all_mask+0x0`. **CAUGHT** | target differs 1, `table rel4-str 10 entries`. Caught only because the table compare fails, not by name |
| rodata | closure.py (`ctl-planted-rodata-closure.out`) | other 3 → 4 (`__intscan`). **CAUGHT** | other 3. NOT CAUGHT |
| rodata | paircl (`ctl-planted-rodata-pairtable.out`, `-pairs.tsv`) | 825 paired, other 14 → 15, 0 conflicts; the new row is `__intscan` with `named target differs` at +0x4c8. **CAUGHT** | other 14, `__intscan` row `ok`. **NOT CAUGHT** |

The `v7daa0e2a03d9/` run gives the same plant results as `v9cbc3553c09e/` (the same repin_check, jtcheck and paircl).

## The two tool defects

Both broke the rule that repin_check e5487165abb8 introduced: two different named targets, or a name on one side
only, are a target difference, and their contents are never compared. (repin_check 9cbc3553c09e's own `tcmp` broke it
too, and e5487165abb8 fixed it; the call and rodata rows above show the miss.)
- **jtcheck.py 2e2f9c2126b2 `same_target`** (`v9cbc3553c09e/tools/jtcheck.py:77-85`): after the same-name test (:77),
  a named pair falls through to a table read (:78-79), the NUL-cut string (:80-81), a memcpy initializer (:82-83) and
  the 8 bytes (:84-85). Fixed by the one-line patch (`tools/jtcheck.py:79`).
  - The patch's known-answer control, on `fuzz_boxreg.asan` (sha256 4532568b621d): `kInterceptorName` and
    `kInterceptorViaFunction` share their first 8 bytes.
  - Result: the unpatched copy returns `(True, 'const 696e746572636570')`, and the patched copy returns `False`.
- **paircl.py 16e1466be22d:** Y is the stripped image (`Raw`, `v9cbc3553c09e/tools/paircl.py:19-33`: no symbols), so
  paircl never sees a name on Y's side.
  - A function-start target is paired by position only (`:64-70`).
  - A `.rodata` target is compared by content only, the NUL-cut string or else the first 8 bytes (`:71-76`).
  - `.got`, `.data` and `.data.rel.ro` targets are not compared at all (`:77-78`).

  The rodata copy shows the miss. The fix is paircl a88c2822a0f2, registered at tool registry commit b73d10eb732
  (`tools/paircl.py:39, 68-72`). It takes Y's unstripped twin and names every target pair first.

**Limit of jtcheck, not changed:** jtcheck compares only lo12 pairs, so a re-pointed `jal` is outside what it checks.
drvcmp, closure.py and paircl catch the call copy.

**Residual gap, not changed:** a target pair with no symbol on either side still gets only the content compare. In
paircl (`tools/paircl.py:86-87`), unnamed `.data` and `.data.rel.ro` cells get no compare at all. In this record such
pairs are covered by drvcmp's `tcmp`: the 3 `(section)` rows in the "Closure" section, each settled by jtcheck.

## Rows that changed

**None.** The version of record against the previous version of record (`v9cbc3553c09e/`, re-run with its own tools):
- **Byte-identical:** every file of the two runs is byte-identical (30 files), except the 9 planted-call and
  planted-rodata outputs in the table above and `tools.sha256`. No root or closure row moved.
- **No hidden name difference:** none of the fixed tools reports a target difference that the earlier tools did not.
  So no real target pair of uci B has two different names, or a name on one side only.
- **Reproducible:** the re-runs of the two earlier versions are byte-identical to their committed outputs
  (`v9cbc3553c09e/`: 32 files; `v7daa0e2a03d9/`: 30 files). The only exceptions are `tools.sha256`, and the new plant
  outputs that the extended `run.sh` adds.
- **The first run:** `v7daa0e2a03d9/` differs from the version of record only where it did before, in the UNMEASURED
  words (section "Closure").

## Limits

- **Code only.** The 97 register-indirect call sites in the closure take their targets from data, and paircl skips
  `.got` / `.data` / `.data.rel.ro` cells. Neither is covered by a code comparison (B-DONORS.md line 251).
- **Not a proof of context.** "Same code" does not say that grant's released walks prove the chain in the call
  contexts uci B needs (B-DONORS.md line 18).

## Files (all in `commit/`)

- **Version of record:**
  - inputs and pins: `images.sha256`, `twins.out`, `roots-syms.out`, `tools.sha256`, `tools/` (with `DIFFS.md`);
  - roots: `roots.tsv`;
  - closure: `paircl-{malloc,free,tmalloc,tfree}-grant.out`, `pairtable-*-grant.out`, `pairs-*-grant.tsv`,
    `closure-uci-grant.out`, `jtcheck-members.txt`, `jtcheck-uci-grant.out`, `cietable.out`;
  - controls: `closure-uci-identity.out`, `ctl-*` (with `ctl-planted-call-*` and `ctl-planted-rodata-*`),
    `planted/planted.sha256`, `planted/planted.cmp`.
- **Earlier versions:** `v9cbc3553c09e/` and `v7daa0e2a03d9/`, the same file names, each with its own `tools/` (and
  `DIFFS.md`) and `tools.sha256`.
- **Re-run:** `run.sh` (`./run.sh` for the version of record; `./run.sh v9cbc3553c09e/tools v9cbc3553c09e` and
  `./run.sh v7daa0e2a03d9/tools v7daa0e2a03d9` for the earlier versions).
  - It needs an `env.sh` beside it that sets `UCI_S UCI_U GR_S GR_U ID_S ID_U` to the six images of the table above.
  - It writes the planted copies `planted/grantB-{S,U}-{deep,root,call,rodata}.elf` (tokens
    `GRANT_B_{PIN,TWIN}_PLANTED_{DEEP,ROOT,CALL,RODATA}`; not committed), and their sha256 in `planted/planted.sha256`.
  - Its last step writes `commit/`.

## The committed slice

`commit/` holds everything committed except this file and MANIFEST.md. Its last writer is `tools/scrub_out.py`, the
last step of `run.sh`:
- In the raw outputs, each image path becomes the token that `images.sha256` defines by sha256 and index line.
- The tool scripts and `run.sh` are copied byte for byte, with their modes.
- It refuses its own output (exit 1, `commit/` left as it was) if any file or file name in it still holds a host
  path, an internal branch prefix, a worker name or the tool registry's branch name.
  - Control: an untokenized image path, a planted worker name and a planted branch prefix each gave exit 1.

**Checks (2026-10-30, after the move to repin_check e5487165abb8 and the fail-closed jtcheck and paircl):**
- **Only tokens rewritten:** replacing each token in `commit/` by its image path gives back every raw output of the
  three versions byte for byte (124 files).
- **Same numbers as the previous version of record:** the version of record's measurement files are byte-identical
  to the committed previous run (32 files, 97,541 numbers). The numbers diff is empty.
- **Runnable from the slice:** `run.sh` (all three versions), run from a copy of `commit/` with an `env.sh` beside it,
  wrote a `commit/` identical to this one (`diff -r`: no difference).
- **Scanner of record:** run over this slice at its repository path (`commit/` plus this file, with `inventory/` and
  `INTERCEPTORS.md`), it reported 0 files with an uncleared flag-tier hit.
