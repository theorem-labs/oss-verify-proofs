# fuzz_wire image-A __asan_memmove contract: gate record

The files: lib/A/Rt/MemmoveDef.v, MemmoveIm.v, MemmoveK.v, MemmovePaths.v and Memmove.v (blobs 71b483627f30,
1c0011e111a0, e50a6822820d, 00eab34ae3b0, 53570a3cdeb6), relocated from libreac/fuzz_pcap's released lib/A/Rt/ files of
the same names (recipes 5098883da0b; blobs 7f72addf7a2a, 3476ea79d91d, 0c435d181bef, 275ded8e8c5c, 3a8554c369c6) by
`provenance/evidence/memmove-reloc/run.sh A`: alreloc frozen a5c53bb2bed4ad03 with the 60 measured resolutions of
`asan-resolve-A.txt`, then `adapt_memmove.py A`. Target fuzz_wire.asan (sha256 2f8f8697cd4f, unstripped twin
d2f662a22962); donor fuzz_pcap.asan (sha256 b7a91d9b1fb0, unstripped twin 36da3052c383). The image-A core (lib/A,
lib/Reusable) is not under check here. `gates/run-gates.sh` runs every gate below with its controls;
`gates/records-mm.py` writes records/. The method is the image-B record's (../memmove-B/, itself fuzz_uci's
stackmalloc1-B method) with only the image changed: lib/A, the asan images, images keyed A, the planted values.

The statement, in `OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.A.Rt.Memmove`:

    Theorem asan_memmove_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> amemmove_realizes tfibsegs B 0x51310.

(Memmove.v:148: fuzz_pcap's lib/A/Rt/Memmove.v:147 with PcapSyms renamed WireSyms and the entry moved from fuzz_pcap
A's __asan_memmove 0x51bf0 to fuzz_wire A's 0x51310.)

| gate | result | counts | control |
|---|---|---|---|
| 0 bytecmp | done by the relocation (cited) | root EQUAL-mod-pcrel; closure 785, 11 jump-table members 0 / 0; paircl 826, 0 conflicts | comparator controls DIFFERENT |
| 1 port_addr_check efa19b81e92b | PASS | 8875 numerals, FLAGGED 0, GENERATOR-FILL 0; the 60 resolved rows in their expected classes | 2 plants, each STALE-DONOR-CODE-POINTER 1, rc 4 |
| 2a codeptr 12348302dfd2 | PASS | 5 findings, all non-addresses, declared; 0 with the declarations | plant: 1 STALE finding, also under the declarations |
| 2b atable | N/A | no atable field, no AB12, no keyed table | - |
| 2c by-value | PASS | 179 numerals: TARGET 17, OTHER 162, SHARED 0, DONOR-STALE 0 | plant: DONOR-STALE 1 |
| 3 v10 439f8e3bd463 | PASS | ESCAPES 0 = fuzz_pcap's counterparts' 0 | plant: ESCAPES 1 |
| 4 yh03check | N/A | no start-up layer | - |

## 0. Bytecmp (done by the relocation; cited, not re-run)

The relocation's measurement records, cited by sha256 of each record file:

- root compare `root-A.txt` (cb606a287a93; comparator `fncmp.py` f8b778b1103a): __asan_memmove fuzz_wire A 0x51310
  against fuzz_pcap A 0x51bf0, 880 B: instructions 220 / 220, real differences 0, external pairs 10 (among them
  0x53b20 -> 0x54400 __asan_region_is_poisoned and 0x632d8 -> 0x63bb8 __sanitizer_internal_memmove), conflicts 0,
  VERDICT EQUAL-mod-pcrel.
- the comparator's controls on image A, with the same `fncmp.py` (the relocation's measurement note, sha256
  968f4a33dd47, section 2): fuzz_wire A's __asan_memmove against its __asan_memcpy, 880 B: 220 / 220 instructions,
  209 real differences, 11 external pairs, 8 conflicts, DIFFERENT; fuzz_wire A with one planted bit at 0x51350
  (__asan_memmove + 0x40, `addi s4, s0, -0x7ff` for `-0x800`) against fuzz_pcap A: 1 real difference, DIFFERENT.
- `closure-asan.txt` (b8f934d98938): the closure of __asan_memmove is 785 functions: EQUAL 173, EQUAL-mod-pcrel 601,
  other 11.
- `jtcheck-asan.txt` (eb2a7786f3ba): those 11 jump-table members: target differs 0 and unpaired differing words 0 in
  each.
- `paircl-A.txt` (4dff04646040): fuzz_wire A (twin d2f662a22962) against fuzz_pcap A (b7a91d9b1fb0), root 0x51310 /
  0x51bf0: 826 functions paired, EQUAL 185, EQUAL-mod-pcrel 627, other 14, pairing conflicts 0.

## 1. Flag gate: port_addr_check efa19b81e92b --fail-on-flags (records/flag-gate.txt, records/flag-triage.tsv)

Command (run-gates.sh `pac`, core-B/gates/pac-B.sh's flags with this row's images):
`port_addr_check.py --src DON --dst FIN --src-image A=<fuzz_pcap.asan pin>:<twin> --dst-image A=<fuzz_wire.asan
pin>:<twin> --donors-from DONORS --paired-only --summary --fail-on-flags`, checker sha256 efa19b81e92b. Both images
are keyed A, the build letter of asan (an efa19b81e92b run keyed by another name leaves the named-symbol rule
unmeasured). Donor DON = the five released lib/A/Rt files with their module paths renamed (`libreac.fuzz_pcap` ->
`reac_repacer.fuzz_wire`, the only change; alreloc writes into the tree and keeps no stage); ported FIN = the
committed files.

Result: 5 files paired, 8875 numerals: SAME-SYMBOL 115, SAME-GEOMETRY 12, ROUND-CONSTANT-SAME 1, INSN-SAME 25,
NON-ADDRESS-SAME 8722. `FLAG-CLASSES 575d398c6022`; `FLAGGED 0 rows in 0 classes`; no GENERATOR-FILL row; named-symbol
cells unmeasured 0; rc 0. `triage-mm.py`: 0 flagged rows, so no row needs a reason.

The 115 SAME-SYMBOL rows are every address of the walk, each the same symbol + offset in both images: the entry
__asan_memmove+0x0 (Memmove.v 1, MemmoveK.v 2: 0x51bf0 -> 0x51310), the ld pcs +0x88 / +0x8c (0x51398 / 0x5139c, 18
each) and +0xd4 / +0xd8 (0x513e4 / 0x513e8, 18 each), MM_MID +0x94 (0x513a4), +0xe0 (0x513f0), MM_RA +0xe4 (0x513f4),
+0x36c (0x5167c), __sanitizer_internal_memmove+0x0 (MemmoveIm.v 1, MemmoveK.v 2: 0x63bb8 -> 0x632d8), and the return
address __asan_region_is_poisoned+0x174 (0x54574 -> 0x53c94: MemmoveK.v MZ_RA, 32 rows of MemmovePaths.v). The 25
INSN-SAME rows are MemmoveIm.v's 22 words and MemmoveK.v's three `clookup tbl_icpt` words 0x81010113 (+0x0),
0x6e9110ef (+0xe0) and 0xd75ff06f (+0x36c), each read at that offset of __asan_memmove in both images
(records/measure.out section 5).

The expected classes. The relocation decided 60 numerals by hand (`provenance/evidence/memmove-reloc/asan-resolve-A.why.txt`).
`triage-mm.py` finds each of them in the run and checks its verdict; all 60 are in the class their measured reason
predicts, none flagged (records/flag-triage.tsv):

| rows | value | verdict | measured reason (records/measure.out) |
|---|---|---|---|
| 24 | 345460 -> 343188 | SAME-SYMBOL, both sides `decimal return site: __asan_region_is_poisoned+0x174` | the return address of ret_ok_lit: fuzz_pcap A 0x54400 + 0x174 = 0x54574 = 345460, fuzz_wire A 0x53b20 + 0x174 = 0x53c94 = 343188; the call word before it is jal 0x3d10f0ef in both images |
| 18 | 538627 (kept) | NON-ADDRESS-SAME | the icpt_ld8 instruction word ld x16, 0(x16) = 0x83803, read at __asan_memmove + 0x84 and + 0xd0 in both images |
| 18 | 571523 (kept) | NON-ADDRESS-SAME | the icpt_ld8 instruction word ld x17, 0(x17) = 0x8b883, read at __asan_memmove + 0x88 and + 0xd4 in both images |

Controls (records/flag-gate.txt), each a copy of the five files with one value planted:

- MemmoveK.v `MM_ENTRY` planted as the donor's __asan_memmove 0x51bf0: `FLAGGED 1 rows in 1 classes:
  STALE-DONOR-CODE-POINTER=1` (MemmoveK.v:39: "donor function start __asan_memmove; the port value is
  ___interceptor_memcpy+0x280; the target has it at __asan_memmove@0x51310"), rc 4.
- MemmoveK.v `MM_REAL` planted as fuzz_wire A's LLVMFuzzerTestOneInput 0x7fe58 (a wrong function):
  `STALE-DONOR-CODE-POINTER=1` (MemmoveK.v:42: the donor's __sanitizer_internal_memmove 0x63bb8 against
  LLVMFuzzerTestOneInput+0x0; the target has it at 0x632d8), rc 4.

`triage-mm.py` leaves each planted row UNEXPLAINED and exits 1. Both planted pointers are caught.

## 2. codeptr, atable, and the by-value check

### 2a. codeptr 12348302dfd2 (start-up set bundle 453349f98b04 at tool-registry commit 5aa27b4282c, frozen-run.sh; records/codeptr.txt)

On fuzz_wire.asan with its twin, stale against fuzz_pcap.asan with its twin and each file's donor text
(`--stale-file`): 5 findings, each also a literal of the donor file, each a number that is not an address. They are
declared in gates/codeptr-notaddr-mm.tsv; every occurrence is in records/codeptr-occurrences.tsv (one each):

| value | where | measured reason (records/measure.out) |
|---|---|---|
| 0x168693 | MemmoveIm.v:35 `W_mm18 : bv 32` | instruction word addi a3, a3, 1, at __sanitizer_internal_memmove + 0x18 in both images (0x632f0 / 0x63bd0) |
| 0x158593 | MemmoveIm.v:37 `W_mm1c : bv 32` | addi a1, a1, 1, at + 0x1c (0x632f4 / 0x63bd4) |
| 0x100613 | MemmoveIm.v:49 `W_mm34 : bv 32` | addi a2, zero, 1, at + 0x34 (0x6330c / 0x63bec) |
| 0x168813 | MemmoveIm.v:57 `W_mm44 : bv 32` | addi a6, a3, 1, at + 0x44 (0x6331c / 0x63bfc) |
| 0x200000 | MemmoveK.v:1048 entD_ro `Hrange` | the bound lo + len <= 0x200000 of every icpt_rodata row, proved by lia over the rows; largest row end fuzz_wire A 0xa1478 (lib/A/AE2y.v), fuzz_pcap A 0xa25b8; the flag gate reads it ROUND-CONSTANT-SAME |

With the declarations: 0 findings (rc 2: MemmoveDef.v holds no address literal in range, UNMEASURED, as in the
baseline). Controls: the donor text on its own image gives 0 findings (the baseline; rc 2 for the same MemmoveDef.v);
MemmoveK.v `MM_ENTRY` planted as the donor's 0x51bf0 gives that finding (STALE against fuzz_pcap.asan), with the 5
above when undeclared and exactly 1 finding under the declarations (rc 1).

### 2b. atable: N/A (records/atable.txt)

atable.py 6a35bb77e745 only emits the per-image atable file (AB12.v for asan, the `atable` record of YK09). The five
files state no atable field and Require no AB12: a scan for YB12, atable*, AB12, stops_more, pc_stack_malloc,
pc_asan_*, Tfib_*_shadow and IMG_REGIONS finds 0 names in each file, and keyset 38b229c6ad08 `check` over the five
files finds no keyed table (a NOTE per file, rc 2, nothing measured). There is no table to check, so there is no
control.

### 2c. The by-value check (gates/decval-mm.py = the image-B record's decval-mm.py with image A's inputs; records/byvalue.txt)

179 numerals in [0x10000, donor top 0x5f6170): TARGET 17, OTHER 162, SHARED 0, DONOR-STALE 0; no declaration. The
review rows (records/byvalue-review.tsv), each measured:

- 7 `word-without-verified-pair`: MemmoveIm.v W_mm0c, W_mm10, W_mm18, W_mm1c, W_mm34, W_mm3c, W_mm44 (the words in
  range). These files state no fetch_word lemma; their 22 words are checked in the build by `tfib_immove_code`
  (code_at at 0x632d8, code_at_vm), and measure-mm.py reads each of the 22 from both images at
  __sanitizer_internal_memmove + offset: all equal.
- 37 `donor-interior-unmoved`: 0x200000 (MemmoveK.v:1048, the bound above; inside the donor's theDepot), and the two
  kept instruction words 538627 (18 rows, inside a donor libunwind function) and 571523 (18 rows, inside the donor's
  __addtf3): the words read at __asan_memmove + 0x84 / + 0xd0 and + 0x88 / + 0xd4 in both images.

The walk's interior pcs (0x51398, 0x5139c, 0x513a4, 0x513e4, 0x513e8, 0x513f0, 0x513f4, 0x5167c, 343188) start no
symbol, so this check classes them OTHER; the flag gate checks each as SAME-SYMBOL (section 1). Control: MemmoveK.v
`MM_ENTRY` planted as the donor's 0x51bf0 gives DONOR-STALE 1 (that row; TARGET 17 -> 16) and nothing else changes.

records/byvalue.txt (lines 6 and 17) lists the core table's interior rows as the gate read them at the time; two of
them, `tfib_A_FakeStack_SetShadow` and `tfib_E_FakeStack_SetShadow`, were removed from lib/A/AB1w.v in e06a69e09264
(unread cells). No file of this row reads them, and the record stays as it was measured.

## 3. v10: global_settings 439f8e3bd463 (records/settings-count.txt)

The five files: ESCAPES 0, PLAIN 8, UNMEASURED 0, KERNEL 0 (TACTIC 8: `Unset Lia Cache.` / `Unset Nia Cache.` in
MemmoveIm, MemmoveK, MemmovePaths and Memmove). fuzz_pcap's released counterparts (lib/A/Rt/ at 5098883da0b): ESCAPES 0,
PLAIN 8, UNMEASURED 0, KERNEL 0: equal. The Zify flag line of MemmoveIm, MemmoveK, MemmovePaths and Memmove is `Local`
in each, as in the donor. Control: Memmove.v's line made global gives ESCAPES 1 (Memmove.v:31).

## 4. yh03check

N/A: these files have no start-up layer (no `src0_A_` / `src0_E_` / `src0_D_` definition).

The `cb` build with 4 PINNED is run by the row owner and is not part of this record.

## Edits to recorded output

records/flag-gate.txt lines 16, 45 and 76 are the checker's own printed text. Each ended with a pointer to a
documentation file of the checker that the release tree does not carry; the pointer is removed, so each line now ends
at "... with one image on both sides". Nothing else in the file changed. sha256 as the checker wrote it: 8a5c43c45540aabf7618bfebe7a6af5178c9013711e6774f6f28e3bf725b9331; as
committed: ec83a195a7ec21e1127389ce18ca2fa792e1294f6896780bef1ed5d4d31dfd0e.
