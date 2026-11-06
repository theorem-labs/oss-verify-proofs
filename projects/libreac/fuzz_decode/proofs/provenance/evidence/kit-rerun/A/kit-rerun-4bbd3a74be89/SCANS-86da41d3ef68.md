# libreac/fuzz_decode, image A alloc-reloc: the two exposure scans of cmpkit 86da41d3ef68 on this record

Why: the kit re-run beside this file (KIT-RERUN.md, DATE, WORKER) was made on cmpkit 4bbd3a74be89, which
cmpkit 86da41d3ef68 SUPERSEDES. 86da41d3ef68's README:92-98 ("For lanes that compared on 4bbd3a74be89 (or older):
what needs a re-run") names two scans that decide, without re-running the compare, whether the new kit's rules can
change what the old run concluded: `luiscan.py` (rule 8, lui-built absolute values) and `ambiscan.py` (a by-name
compare that took the wrong copy of a duplicated name). Both were run here, on the same 7 function pairs and the same
inputs as the re-run. This file changes no .v file and no theorem; it is provenance only. No function is proved here.

## 1. The kit, checked

| what | sha256 (12) | where |
| cmpkit (kit id = first 12 of sha256(SHA256SUMS)) | 86da41d3ef68 | hub HUB, commit 98e50c029045 (BRANCH), tools/cmpkit/86da41d3ef68/ |
| SHA256SUMS | 86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60 | sha256(SHA256SUMS)[:12] = 86da41d3ef68, the kit id |
| luiscan.py | 9ae61e4a0e01 | kit member (full: 9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad) |
| ambiscan.py | 9f61b4cee422 | kit member (full: 9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d) |
| strictcmp3.py (both scans load it from the same directory) | 65688e94214a | kit member |

Extracted with `git -C HUB archive 98e50c029045 tools/cmpkit/86da41d3ef68/` into one directory
holding exactly the kit's files; `sha256sum -c SHA256SUMS` = 9 x OK (out/scans-kitsha.out).

## 2. Inputs: the same images and the same 7 pairs as the re-run

| side | file | sha256 (12) |
| donor twin, C (cgif asan-ubsan; pin 1c29845fe605) | DONOR_TWIN | ce511d541cda |
| decode A twin, A (pin 5973b76807d8) | DECODE_A_TWIN | 4cb0a852e826 |

The 7 names are the cmp rows of out/run-strictcmp2.out (field 1 of each line whose field 2 is `C:A`), i.e. the 7 pairs
of KIT-RERUN.md 4.1: Allocator::Allocate 0x31550->0x3124c, CombinedAllocator::Allocate 0x359e4->0x357c0,
SizeClassAllocator64LocalCache::Refill 0x36134->0x35f10, PoisonShadow 0x53800->0x53040, internal_mmap
0x64198->0x63d3c, StackDepotPut 0x724e0->0x72084, memset 0x9790c->0x92474. ambiscan was given the record's whole
out/ directory (15 files), not a hand-picked subset.

## 3. Commands

```
cd <kit copy> && sha256sum -c SHA256SUMS                                       > out/scans-kitsha.out
C=DONOR_TWIN
A=DECODE_A_TWIN
FNS=$(awk -F'\t' '$2=="C:A" && $1!="fn"{printf "%s%s",(NR>5?",":""),$1}' out/run-strictcmp2.out | sed 's/^,//')
python3 <kit>/luiscan.py --all --fns "$FNS" $C $A                              > out/luiscan-86da41d3ef68.out
python3 <kit>/ambiscan.py $C $A out                                            > out/ambiscan-86da41d3ef68.out
```

## 4. luiscan 9ae61e4a0e01 (rule 8 exposure), full output

```
ROW	image	function	addr	size	luis	insec	inload	memfed	memfed_out	luiconst	unmeasured	exposure
# image DONOR_TWIN sha256 ce511d541cda
ROW	cgif_file_fuzzer.asan-ubsan	_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb	0x31550	2440	12	0	3	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm	0x359e4	728	5	0	1	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m	0x36134	256	0	0	0	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	_ZN6__asan12PoisonShadowEmmh	0x53800	1276	0	0	0	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	_ZN11__sanitizer13internal_mmapEPvmiiiy	0x64198	12	0	0	0	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	_ZN11__sanitizer13StackDepotPutENS_10StackTraceE	0x724e0	32	0	0	0	0	0	0	0	0
ROW	cgif_file_fuzzer.asan-ubsan	memset	0x9790c	248	1	0	0	0	0	0	0	0
TOTAL	cgif_file_fuzzer.asan-ubsan	functions 7	with-lui 3	with-exposure 0	luis 18	insec 0	inload 4	memfed 0	memfed_out 0	luiconst 0	unmeasured 0	exposure 0
# image DECODE_A_TWIN sha256 4cb0a852e826
ROW	fuzz_decode.asan	_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb	0x3124c	2440	12	0	3	0	0	0	0	0
ROW	fuzz_decode.asan	_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm	0x357c0	728	5	0	1	0	0	0	0	0
ROW	fuzz_decode.asan	_ZN11__sanitizer30SizeClassAllocator64LocalCacheINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEEEE6RefillEPNS7_8PerClassEPS6_m	0x35f10	256	0	0	0	0	0	0	0	0
ROW	fuzz_decode.asan	_ZN6__asan12PoisonShadowEmmh	0x53040	1276	0	0	0	0	0	0	0	0
ROW	fuzz_decode.asan	_ZN11__sanitizer13internal_mmapEPvmiiiy	0x63d3c	12	0	0	0	0	0	0	0	0
ROW	fuzz_decode.asan	_ZN11__sanitizer13StackDepotPutENS_10StackTraceE	0x72084	32	0	0	0	0	0	0	0	0
ROW	fuzz_decode.asan	memset	0x92474	248	1	0	0	0	0	0	0	0
TOTAL	fuzz_decode.asan	functions 7	with-lui 3	with-exposure 0	luis 18	insec 0	inload 4	memfed 0	memfed_out 0	luiconst 0	unmeasured 0	exposure 0
TOTAL	all	functions 14	with-lui 6	with-exposure 0	luis 36	insec 0	inload 8	memfed 0	memfed_out 0	luiconst 0	unmeasured 0	exposure 0
```

Reading (luiscan.py:7-22): `exposure` 0 for a function in BOTH images = rule 8 leaves its strictcmp2 verdict
unchanged. Every one of the 7 is 0 in both images, so there is no `lui-in-section` row, no memory-fed lui target and
no 2-byte-parcel `unmeasured` word in this record — the class of OPEN LIMIT 1 (README:63-70), which costs other lanes
36 paircl / 39 closure functions, does not touch these 7. 36 lui words exist over the 14 rows (12 + 5 + 1 per image);
`insec` is 0 on both sides, so strictcmp3 forms no lui ADDRESS target at all here, and every one of those words stays
a raw bytecmp constant, exactly as strictcmp2 compared it. The 4 `inload` values per image (3 in Allocator::Allocate,
1 in CombinedAllocator::Allocate) are the difference between AGENT TIME's literal PT_LOAD wording and the
section test AGENT confirmed at TIME (strictcmp3 rule 8, README:52): they lie inside a PT_LOAD but in no
section (the ELF header / inter-section padding), so they name no object and the kit does not treat them as
addresses. Under either wording nothing in these 7 becomes a difference: an in-load, no-section value is
`writable-unnamed` only when memory-fed, and `memfed` is 0 in both images.

**luiscan: CLEAR, exposure 0 in both images for all 7 pairs.**

## 5. ambiscan 9f61b4cee422 (duplicated names), full output

```
# X = DONOR_TWIN sha256 ce511d541cda
# Y = DECODE_A_TWIN sha256 4cb0a852e826
# AMBIG	file	line	name	image	copies	addr/size/STT_FILE/qname ; ...	Img.fsym takes	how the line was read
TOTAL	files read 15	by-name compares seen (distinct names) 7	ambiguous hits 0	distinct ambiguous names 0	lines with a function token 66	resolved items NAME{FILE}/0xADDR (distinct) 0	files skipped 0
```

Reading (ambiscan.py:40-45): TOTAL with 0 ambiguous hits means no by-name compare in those files hit a duplicated
name, in X or in Y. All 15 files of the record's out/ were read (0 skipped), and the by-name compares they contain
are exactly 7 distinct names — the 7 pairs, no eighth name. This re-measures, with the kit's own tool, what
KIT-RERUN.md section 5 measured by hand ("FUNCPAIR NAME CHECK: unique 7 / duplicated 0"): each of the 7 carries one
sized STT_FUNC symbol per image, so the lowest-address lookup of the old tools could not have taken another copy.

The two duplicated names of these images, `_ZN6__asanL11MemToShadowEm` (5 copies each side) and `dummy` (5 in decode
A, 6 in the donor), appear in this record only on the `#` listing lines of out/dupzone.out and out/dupnames.out,
which report them; no compare of this record is rooted at either name. The decode-owner's note that a MemToShadow
compared by name is now REFUSED by strictcmp3 (README:57-58, plant AMB / K1) therefore has nothing to bite on here:
there is no MemToShadow row to re-cite by address.

**ambiscan: CLEAR, 0 ambiguous hits over 15 files and 7 distinct compared names.**

## 6. What the two scans do and do not settle

- They settle that the two NEW members of 86da41d3ef68 (rule 8 exposure, duplicated-name selection) cannot change any
  verdict of this record: 0 exposure in both images, 0 ambiguous hits.
- They are not a re-run of the compare. README:97-98: strictcmp3's other changes (the string-label NAME-ONLY rule,
  ESC in C strings, the combined verdict column, jtcheck's table rule) need a re-run with the kit, and every old cmp
  verdict column must be read with its target-differ column. KIT-RERUN.md 4.1 already reports both columns per pair
  (the target pass column), and its 4.2 settles the single reported row by hand, so its verdicts are already combined
  verdicts, not word-only ones.
- The classes the new kit leaves open do not arise in this record: no `lui-in-section` row (section 4), so OPEN
  LIMIT 1 needs no hand argument here; no jump / string table and no base-relative switch decode is claimed by this
  record, so OPEN LIMIT 4's fail-closed class is not relied on anywhere in it; the one by-hand acceptance the record
  does make, Allocator::Allocate +0xdc, is OPEN LIMIT 5's named class (an unnamed .rodata target read through a
  bounded index, compared on its whole region) and is settled there with its own measurement (out/probe_tbl.out) and
  an independent audit, never as a kit EQUAL. Rule 8 does not touch it: that target is built by `auipc`/`addi`, not
  by a `lui`.

## 7. Verdict

No row is EXPOSED, so no row was re-run on 86da41d3ef68 and no verdict of KIT-RERUN.md changes.

VERDICT CHANGED: no

SCANS CLEAR
