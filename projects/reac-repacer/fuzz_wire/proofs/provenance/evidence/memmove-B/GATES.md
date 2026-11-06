# fuzz_wire image-B __asan_memmove contract: gate record

The files: lib/B/Rt/MemmoveDef.v, MemmoveIm.v, MemmoveK.v, MemmovePaths.v and Memmove.v (blobs 668220844de9,
cc3350446beb, 979e71ad47a0, d296430180c4, f478ad8cd578), relocated from libreac/fuzz_pcap's released lib/B/Rt/ files of
the same names (recipes 5098883da0b; blobs f576a34ecead, 8fa41ef7b88d, c26066d543f1, dd1e48d0d17f, 9382b504bfae) by
`provenance/evidence/memmove-reloc/run.sh B`: alreloc frozen a5c53bb2bed4ad03 with the 60 measured resolutions of
`asan-resolve-B.txt`, then `adapt_memmove.py B`. Target fuzz_wire.asan-ubsan (sha256 af4534831a45, unstripped twin
51eb4bef2425); donor fuzz_pcap.asan-ubsan (sha256 9e66f771f22a, unstripped twin c969d83cdd59). The image-B core
(lib/B, lib/Reusable) is not under check here. `gates/run-gates.sh` runs every gate below with its controls;
`gates/records-mm.py` writes records/. The method is fuzz_uci's image-B class-1 stack_malloc record
(proofs/reac-repacer/fuzz_uci/provenance/evidence/stackmalloc1-B/); only the unit, the image, the donor, the five file
names, the tool versions and the planted values are changed.

The statement, in `OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.B.Rt.Memmove`:

    Theorem asan_memmove_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> amemmove_realizes tfibsegs B 0x510b0.

(Memmove.v:148: fuzz_pcap's Memmove.v:147 with PcapSyms renamed WireSyms and the entry moved from fuzz_pcap's
__asan_memmove 0x51c40 to fuzz_wire's 0x510b0.)

| gate | result | counts | control |
|---|---|---|---|
| 0 bytecmp | done by the relocation (cited) | root EQUAL-mod-pcrel; closure 785, 11 jump-table members 0 / 0; paircl 826, 0 conflicts | comparator controls DIFFERENT |
| 1 port_addr_check efa19b81e92b | PASS | 8868 numerals, FLAGGED 0, GENERATOR-FILL 0; the 60 resolved rows in their expected classes | 2 plants, each STALE-DONOR-CODE-POINTER 1, rc 4 |
| 2a codeptr 12348302dfd2 | PASS | 5 findings, all non-addresses, declared; 0 with the declarations | plant: 1 STALE finding, also under the declarations |
| 2b atable | N/A | no atable field, no YB12, no keyed table | - |
| 2c by-value | PASS | 170 numerals: TARGET 13, OTHER 157, SHARED 0, DONOR-STALE 0 | plant: DONOR-STALE 1 |
| 3 v10 439f8e3bd463 | PASS | ESCAPES 0 = fuzz_pcap's counterparts' 0 | plant: ESCAPES 1 |
| 4 yh03check | N/A | no start-up layer | - |

## 0. Bytecmp (done by the relocation; cited, not re-run)

The relocation's measurement records, cited by sha256 of each record file:

- root compare `root-B.txt` (ea5b2923e580; comparator `fncmp.py` f8b778b1103a): __asan_memmove fuzz_wire 0x510b0
  against fuzz_pcap 0x51c40, 880 B: instructions 220 / 220, real differences 0, external pairs 10 (among them
  0x538c0 -> 0x54450 __asan_region_is_poisoned and 0x63078 -> 0x63c08 __sanitizer_internal_memmove), conflicts 0,
  VERDICT EQUAL-mod-pcrel. The comparator's controls were first measured with the same `fncmp.py` on image A:
  fuzz_wire A's memmove against its memcpy gives 209 real differences (DIFFERENT), and one planted bit in the A root
  (`addi s4, s0, -0x7ff` for `-0x800`) gives 1 difference (DIFFERENT).
- image-B root controls (gates/root-controls.sh, same `fncmp.py`; records/root-control-plant.out, root-control-memcpy.out): a copy of fuzz_wire.asan-ubsan with one bit flipped at 0x510f0 (__asan_memmove + 0x40, `addi s4, s0, -0x800` -> `-0x7ff`; the copy deleted after) against fuzz_pcap 0x51c40, 880 B: real differences 1 (+0x40), VERDICT DIFFERENT; fuzz_wire's __asan_memmove 0x510b0 against its __asan_memcpy 0x50c14, 880 B: real differences 209, conflicts 8, VERDICT DIFFERENT.
- `closure-asan-ubsan.txt` (c346f2d04ac6): the closure of __asan_memmove is 785 functions: EQUAL 171,
  EQUAL-mod-pcrel 603, other 11.
- `jtcheck-asan-ubsan.txt` (a613c47d67e4): those 11 jump-table members: target differs 0 and unpaired differing
  words 0 in each.
- `paircl-B.txt` (f4749fd0b664): 826 functions paired, EQUAL 183, EQUAL-mod-pcrel 629, other 14, pairing conflicts 0.

## 1. Flag gate: port_addr_check efa19b81e92b --fail-on-flags (records/flag-gate.txt, records/flag-triage.tsv)

Command (run-gates.sh `pac`, core-B/gates/pac-B.sh's flags with this row's images):
`port_addr_check.py --src DON --dst FIN --src-image B=<fuzz_pcap pin>:<twin> --dst-image B=<fuzz_wire pin>:<twin>
--donors-from DONORS --paired-only --summary --fail-on-flags`, checker sha256 efa19b81e92b. Both images are keyed B,
the build letter of asan-ubsan (an efa19b81e92b run keyed by another name leaves the named-symbol rule unmeasured).
Donor DON = the five released files with their module paths renamed (`libreac.fuzz_pcap` ->
`reac_repacer.fuzz_wire`, the only change; alreloc writes into the tree and keeps no stage); ported FIN = the
committed files.

Result: 5 files paired, 8868 numerals: SAME-SYMBOL 111, SAME-GEOMETRY 12, ROUND-CONSTANT-SAME 1, INSN-SAME 22,
NON-ADDRESS-SAME 8722. `FLAG-CLASSES 575d398c6022`; `FLAGGED 0 rows in 0 classes`; no GENERATOR-FILL row; named-symbol
cells unmeasured 0; rc 0. `triage-mm.py`: 0 flagged rows, so no row needs a reason.

The 111 SAME-SYMBOL rows are every address of the walk, each the same symbol + offset in both images: the entry
__asan_memmove+0x0 (Memmove.v, MemmoveK.v MM_ENTRY: 0x51c40 -> 0x510b0), MM_MID +0x94 (0x51144), the ld pcs
+0x88 / +0x8c (0x51138 / 0x5113c, 18 each) and +0xd4 / +0xd8 (0x51184 / 0x51188, 18 each), MM_RA +0xe4 (0x51194),
__sanitizer_internal_memmove+0x0 (MemmoveIm.v, MemmoveK.v MM_REAL: 0x63c08 -> 0x63078), and the return address
__asan_region_is_poisoned+0x174 (0x545c4 -> 0x53a34: MemmoveK.v MZ_RA, 32 rows of MemmovePaths.v).

The expected classes. The relocation decided 60 numerals by hand (`provenance/evidence/memmove-reloc/asan-resolve-B.why.txt`).
`triage-mm.py` finds each of them in the run and checks its verdict; all 60 are in the class their measured reason
predicts, none flagged (records/flag-triage.tsv):

| rows | value | verdict | measured reason (records/measure.out) |
|---|---|---|---|
| 24 | 345540 -> 342580 | SAME-SYMBOL, both sides `decimal return site: __asan_region_is_poisoned+0x174` | the return address of ret_ok_lit: fuzz_pcap 0x54450 + 0x174 = 0x545c4 = 345540, fuzz_wire 0x538c0 + 0x174 = 0x53a34 = 342580; the call word before it is jal 0x3d10f0ef in both images |
| 18 | 538627 (kept) | NON-ADDRESS-SAME | the icpt_ld8 instruction word ld x16, 0(x16) = 0x83803, read at __asan_memmove + 0x84 and + 0xd0 in both images |
| 18 | 571523 (kept) | NON-ADDRESS-SAME | the icpt_ld8 instruction word ld x17, 0(x17) = 0x8b883, read at __asan_memmove + 0x88 and + 0xd4 in both images |

Controls (records/flag-gate.txt), each a copy of the five files with one value planted:

- MemmoveK.v `MM_ENTRY` planted as the donor's __asan_memmove 0x51c40: `FLAGGED 1 rows in 1 classes:
  STALE-DONOR-CODE-POINTER=1` (MemmoveK.v:39: "donor function start __asan_memmove; the port value is
  ___interceptor_memcpy+0x530; the target has it at __asan_memmove@0x510b0"), rc 4.
- MemmoveK.v `MM_REAL` planted as fuzz_wire's LLVMFuzzerTestOneInput 0x7fbf8 (a wrong function):
  `STALE-DONOR-CODE-POINTER=1` (MemmoveK.v:42: the donor's __sanitizer_internal_memmove 0x63c08 against
  LLVMFuzzerTestOneInput+0x0; the target has it at 0x63078), rc 4.

`triage-mm.py` leaves each planted row UNEXPLAINED and exits 1. Both planted pointers are caught.

## 2. codeptr, atable, and the by-value check

### 2a. codeptr 12348302dfd2 (start-up set bundle 453349f98b04 at tool-registry commit 5aa27b4282c, frozen-run.sh; records/codeptr.txt)

On fuzz_wire.asan-ubsan with its twin, stale against fuzz_pcap.asan-ubsan with its twin and each file's donor text
(`--stale-file`): 5 findings, each also a literal of the donor file, each a number that is not an address. They are
declared in gates/codeptr-notaddr-mm.tsv; every occurrence is in records/codeptr-occurrences.tsv (one each):

| value | where | measured reason (records/measure.out) |
|---|---|---|
| 0x168693 | MemmoveIm.v:35 `W_mm18 : bv 32` | instruction word addi a3, a3, 1, at __sanitizer_internal_memmove + 0x18 in both images (0x63090 / 0x63c20) |
| 0x158593 | MemmoveIm.v:37 `W_mm1c : bv 32` | addi a1, a1, 1, at + 0x1c (0x63094 / 0x63c24) |
| 0x100613 | MemmoveIm.v:49 `W_mm34 : bv 32` | addi a2, zero, 1, at + 0x34 (0x630ac / 0x63c3c) |
| 0x168813 | MemmoveIm.v:57 `W_mm44 : bv 32` | addi a6, a3, 1, at + 0x44 (0x630bc / 0x63c4c) |
| 0x200000 | MemmoveK.v:1040 entD_ro `Hrange` | the bound lo + len <= 0x200000 of every icpt_rodata row, proved by lia over the rows; largest row end fuzz_wire 0xa14f8 (lib/B/YE2y.v), fuzz_pcap 0xa24b8; the flag gate reads it ROUND-CONSTANT-SAME |

With the declarations: 0 findings (rc 2: MemmoveDef.v holds no address literal in range, UNMEASURED, as in the
baseline). Controls: the donor text on its own image gives 0 findings (the baseline; rc 2 for the same MemmoveDef.v);
MemmoveK.v `MM_ENTRY` planted as the donor's 0x51c40 gives that finding (STALE against fuzz_pcap.asan-ubsan), with the
5 above when undeclared and exactly 1 finding under the declarations (rc 1).

### 2b. atable: N/A (records/atable.txt)

atable.py 6a35bb77e745 only emits the per-image atable file (YB12.v for asan-ubsan, the `atable` record of YK09). The
five files state no atable field and Require no YB12: a scan for YB12, atable*, AB12, stops_more, pc_stack_malloc,
pc_asan_*, Tfib_*_shadow and IMG_REGIONS finds 0 names in each file, and keyset 38b229c6ad08 `check` over the five
files finds no keyed table (a NOTE per file, rc 2, nothing measured). There is no table to check, so there is no
control.

### 2c. The by-value check (gates/decval-mm.py = stackmalloc1-B's decval-sm1.py with this row's inputs; records/byvalue.txt)

170 numerals in [0x10000, donor top 0x5f6070): TARGET 13, OTHER 157, SHARED 0, DONOR-STALE 0; no declaration. The
review rows (records/byvalue-review.tsv), each measured:

- 7 `word-without-verified-pair`: MemmoveIm.v W_mm0c, W_mm10, W_mm18, W_mm1c, W_mm34, W_mm3c, W_mm44 (the words in
  range). These files state no fetch_word lemma; their 22 words are checked in the build by `tfib_immove_code`
  (`code_at AsanUbsan.M.loaded_segments 0x63078 0 immove_words`, code_at_vm), and measure-mm.py reads each of the 22
  from both images at __sanitizer_internal_memmove + offset: all equal.
- 37 `donor-interior-unmoved`: 0x200000 (MemmoveK.v:1040, the bound above; inside the donor's theDepot), and the two
  kept instruction words 538627 (18 rows, inside a donor libunwind function) and 571523 (18 rows, inside the donor's
  __addtf3): the words read at __asan_memmove + 0x84 / + 0xd0 and + 0x88 / + 0xd4 in both images.

The walk's interior pcs (0x51138, 0x5113c, 0x51144, 0x51184, 0x51188, 0x51194, 342580) start no symbol, so this
check classes them OTHER; the flag gate checks each as SAME-SYMBOL (section 1). Control: MemmoveK.v `MM_ENTRY`
planted as the donor's 0x51c40 gives DONOR-STALE 1 (that row; TARGET 13 -> 12) and nothing else changes.

records/byvalue.txt (lines 6 and 17) lists the core table's interior rows as the gate read them at the time; two of
them, `tfib_A_FakeStack_SetShadow` and `tfib_E_FakeStack_SetShadow`, were removed from lib/B/YB1w.v in cd94f90a43f
(unread cells). No file of this row reads them, and the record stays as it was measured.

## 3. v10: global_settings 439f8e3bd463 (records/settings-count.txt)

The five files: ESCAPES 0, PLAIN 8, UNMEASURED 0, KERNEL 0 (TACTIC 8: `Unset Lia Cache.` / `Unset Nia Cache.` in
MemmoveIm, MemmoveK, MemmovePaths and Memmove). fuzz_pcap's released counterparts (lib/B/Rt/ at 5098883da0b): ESCAPES 0,
PLAIN 8, UNMEASURED 0, KERNEL 0: equal. The Zify flag line of MemmoveIm, MemmoveK, MemmovePaths and Memmove is `Local`
in each, as in the donor. Control: Memmove.v's line made global gives ESCAPES 1 (Memmove.v:31).

## 4. yh03check

N/A: these files have no start-up layer (no `src0_A_` / `src0_E_` / `src0_D_` definition).

The `cb` build with 4 PINNED is run by the row owner and is not part of this record.

## Edits to recorded output

records/flag-gate.txt lines 16, 45 and 76 are the checker's own printed text. Each ended with a pointer to a
documentation file of the checker that the release tree does not carry; the pointer is removed, so each line now ends
at "... with one image on both sides". Nothing else in the file changed. sha256 as the checker wrote it: 4ee3d34f5ebf0d9c4114f96174b8f470e2fc541871e78c3711a37ceb381b5103; as
committed: c65e218b02f4edbedf749e51e0edfcad2eb57f5b1cbbf8897c8c4c01d08b9578.
