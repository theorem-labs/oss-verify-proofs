## Table

| slice | image pair (X : Y, sha12) | functions scanned | luiscan result | ambiscan result | lui hand trace (kit limits 6d8ff128a01 / 797c750bbb0) | verdict |
|---|---|---|---|---|---|---|
| stackmalloc1-A (pack f75c58498e6; records on 4bbd3a74be89, writer's own 86da41d3ef68 scans beside: records/cmpkit-86da41d3ef68-luiscan.out (exposure 0), -ambiscan.out (0 hits), -lui-trace.md (20 rows, sha256 fee89d36be8b)) | fuzz_grant.asan 57c26f993615 : fuzz_uci.asan 56822e263d76 | 13 (13 per image; MemToShadow by NAME{asan_fake_stack.cpp} = the copy the record compared by address); no lui rows: 8 | exposure 0 in both images for all 13 (10 lui words per image; same as the writer's scan) | TOTAL 0 (files 21: the 4bbd3a74be89 and bytecmp.py outputs, 12 by-name compares) | 10 lui in 5 functions: EQUAL 6, NO-BASE-USE 4, DIFFERENT 0; agrees row by row with the writer's hand trace | scans clear |
| stackmalloc1-B (pack f75c58498e6 = 2801e78cc4d; record already re-run on 86da41d3ef68: records/strictcmp3-bodies.out, luiscan.out, ambiscan.out by its writer) | fuzz_grant.asan-ubsan 5a5ee7c02b4e : fuzz_uci.asan-ubsan 8d07ffcf5948 | 13 (17 rows per image: all 5 MemToShadow copies scanned); no lui rows: 8 | exposure 0 in both images for all 17 rows (10 lui words per image) | old records/strictcmp2-bodies.out: 6 AMBIG rows (lines 215-217, `_ZN6__asanL11MemToShadowEm`, X and Y, 5 copies each; Img.fsym took copy 1/5 asan_errors.cpp, X 0x3b890 / Y 0x3aafc; the bytecmp.py rows compared the asan_fake_stack.cpp copy by call target); TOTAL ambiguous hits 6 over 7 files. The 86da41d3ef68 re-run records/strictcmp3-bodies.out: TOTAL 0 (MemToShadow given as NAME{asan_fake_stack.cpp}) | 10 lui in 5 functions: EQUAL 6, NO-BASE-USE 4, DIFFERENT 0 | EXPOSED: ambiscan 6 AMBIG rows (the old strictcmp2 MemToShadow row took copy 1/5); already superseded inside the record by its own 86da41d3ef68 re-run (strictcmp3 on `MemToShadow{asan_fake_stack.cpp}`, EQUAL-mod-pcrel 15; its ambiscan.out lists the same 6 rows), whose ambiscan is TOTAL 0 |
| memchr-A | fuzz_uci.asan 56822e263d76 : fuzz_boxreg.asan 4532568b621d | 787 (closure of ___interceptor_memchr 785 + chain 4 + jtcheck 62, union); no lui rows: 580 | EXPOSED 41 functions, exposure equal in X and Y for each (sum 74 per image); list in section E | TOTAL 0 (files 13: tables/ of the bytecmp 7daa0e2a03d9 + repin_check 9cbc3553c09e run and tables/cmpkit-4bbd3a74be89/; 435 by-name compares, 4 NAME{FILE} items) | 556 lui in 207 functions: EQUAL 125, NO-BASE-USE 431, DIFFERENT 0 | EXPOSED: luiscan 41 functions (lui-in-section class, kit OPEN LIMIT 1); the record's claim is narrowed to the 4 chain functions, none of them exposed; the hand trace finds no lui-built address that differs |
| memchr-B | fuzz_uci.asan-ubsan 8d07ffcf5948 : fuzz_boxreg.asan-ubsan 1d548458eac3 | 787 (closure of ___interceptor_memchr 785 + chain 4 + jtcheck 62, union); no lui rows: 580 | EXPOSED 41 functions, exposure equal in X and Y for each (sum 74 per image); list in section E | TOTAL 0 (files 13: tables/ of the bytecmp 7daa0e2a03d9 + repin_check 9cbc3553c09e run and tables/cmpkit-4bbd3a74be89/; 435 by-name compares, 4 NAME{FILE} items) | 556 lui in 207 functions: EQUAL 125, NO-BASE-USE 431, DIFFERENT 0 | EXPOSED: luiscan 41 functions (lui-in-section class, kit OPEN LIMIT 1); the record's claim is narrowed to the 4 chain functions, none of them exposed; the hand trace finds no lui-built address that differs |
| strlen-A | fuzz_uci.asan 56822e263d76 : fuzz_identity.asan 5b0cbe573036 | 788 (closures of ___interceptor_strlen 784 and ___interceptor_memchr 785 + chain 8 + jtcheck 62, union); no lui rows: 581 | EXPOSED 41 functions, exposure equal in X and Y for each (sum 74 per image); list in section E | TOTAL 0 (files 9: tables/; 437 by-name compares) | 556 lui in 207 functions: EQUAL 121, NO-BASE-USE 431, 4 settled by hand EQUAL (PackedCounterArray: same unnamed 64-byte table, index 0..63), DIFFERENT 0 | EXPOSED: luiscan 41 functions (lui-in-section class, kit OPEN LIMIT 1); the claim is narrowed to the 8 chain functions, none of them exposed; the hand trace finds no lui-built address that differs |
| uci-b-alloc (donor pair) | fuzz_uci.asan-ubsan 8d07ffcf5948 : fuzz_grant.asan-ubsan 5a5ee7c02b4e (paircl against the pin fde52226dc48, names from the twin) | 943 (closure_strict2 of the 4 roots 784 + paircl of the 4 roots 943 pairs + roots 4 + jtcheck 16 + earlier/ pairtable 825, union); no lui rows: 698 | EXPOSED 43 functions, exposure equal in X and Y for each (sum 76 per image); list in section E | current 4bbd3a74be89 outputs: 96 AMBIG rows, 1 name (`_ZN6__asanL11MemToShadowEm`), all CSTR rows of the 6 paircl outputs (8 per file, X and Y; paircl pairs by call-target address, the closure_strict2 outputs name the copies NAME{FILE}: 5 resolved items, 0 hits); earlier/ (va88c2822a0f2, v7daa0e2a03d9, v9cbc3553c09e: 119 files): 300 AMBIG rows, 2 names (MemToShadow 5 copies, `dummy` 5 copies), all in pairtable pairs-*.tsv rows (bare name + both addresses); section A | 633 lui in 245 functions: EQUAL 123, NO-BASE-USE 506, 4 settled by hand EQUAL (PackedCounterArray: same unnamed 64-byte table, index 0..63), DIFFERENT 0 | EXPOSED: luiscan 43 functions (lui-in-section class, kit OPEN LIMIT 1) + ambiscan 96 + 300 AMBIG rows; the hand trace finds no lui-built address that differs |
| uci-b-alloc (identity control pair) | fuzz_uci.asan-ubsan 8d07ffcf5948 : fuzz_identity.asan-ubsan 43b44d50be8a | 825 (closure_strict2 of the 4 roots 784 + roots 4 + jtcheck 16 + earlier/ ctl pairtable 825, union); no lui rows: 608 | EXPOSED 42 functions, exposure equal in X and Y for each (sum 75 per image); list in section E | current (closure-uci-identity.out, ctl-jtcheck-uci-identity.out, roots.tsv): TOTAL 0; earlier/ identity files: 60 AMBIG rows (MemToShadow, dummy) in ctl-pairs-*-identity.tsv rows (bare name + both addresses) | 570 lui in 217 functions: EQUAL 122, NO-BASE-USE 444, 4 settled by hand EQUAL (PackedCounterArray: same unnamed 64-byte table, index 0..63), DIFFERENT 0 | EXPOSED: luiscan 42 functions (lui-in-section class, kit OPEN LIMIT 1) + ambiscan 60 AMBIG rows (earlier/); the hand trace finds no lui-built address that differs |
| uci-b-memcpy | fuzz_uci.asan-ubsan 8d07ffcf5948 : fuzz_grant.asan-ubsan 5a5ee7c02b4e | 785 (closure of __asan_memcpy 785 + jtcheck 62 (settle.py 49 inside it), union); no lui rows: 578 | EXPOSED 41 functions, exposure equal in X and Y for each (sum 74 per image); list in section E | TOTAL 0 (files 7; 431 by-name compares, 4 NAME{FILE} items) | 556 lui in 207 functions: EQUAL 121, NO-BASE-USE 431, 4 settled by hand EQUAL (PackedCounterArray: same unnamed 64-byte table, index 0..63), DIFFERENT 0 | EXPOSED: luiscan 41 functions (lui-in-section class, kit OPEN LIMIT 1); the hand trace finds no lui-built address that differs |
| cmpkit-audit (memchr-A part) | fuzz_uci.asan 56822e263d76 : fuzz_boxreg.asan 4532568b621d | 53 (the 49 functions of memchr-A acceptances.tsv the reviewer ran tcmp on + the chain); no lui rows: 40 | EXPOSED 2 functions: SizeClassAllocator64::MaybeReleaseToOS 1 / 1, __strftime_fmt_1 7 / 7 | TOTAL 0, but ambiscan read 0 function tokens: AUDIT.md is prose and tables, the reviewer's raw tcmp outputs are not in the pack (no evidence either way from this scan) | 48 lui in 13 functions: EQUAL 11, NO-BASE-USE 37, DIFFERENT 0 | EXPOSED: luiscan 2 functions (also in the memchr-A row); hand trace: no differing address |
| cmpkit-audit (memchr-B part) | fuzz_uci.asan-ubsan 8d07ffcf5948 : fuzz_boxreg.asan-ubsan 1d548458eac3 | 53 (the 49 functions of memchr-B acceptances.tsv the reviewer ran tcmp on + the chain); no lui rows: 40 | EXPOSED 2 functions: SizeClassAllocator64::MaybeReleaseToOS 1 / 1, __strftime_fmt_1 7 / 7 | TOTAL 0, but ambiscan read 0 function tokens: AUDIT.md is prose and tables, the reviewer's raw tcmp outputs are not in the pack (no evidence either way from this scan) | 48 lui in 13 functions: EQUAL 11, NO-BASE-USE 37, DIFFERENT 0 | EXPOSED: luiscan 2 functions (also in the memchr-B row); hand trace: no differing address |
| cmpkit-audit (strlen-A part) | fuzz_uci.asan 56822e263d76 : fuzz_identity.asan 5b0cbe573036 | 57 (the 49 functions of strlen-A acceptances.tsv the reviewer ran tcmp on + the chain); no lui rows: 44 | EXPOSED 2 functions: SizeClassAllocator64::MaybeReleaseToOS 1 / 1, __strftime_fmt_1 7 / 7 | TOTAL 0, but ambiscan read 0 function tokens: AUDIT.md is prose and tables, the reviewer's raw tcmp outputs are not in the pack (no evidence either way from this scan) | 48 lui in 13 functions: EQUAL 7, NO-BASE-USE 37, 4 settled by hand EQUAL (PackedCounterArray: same unnamed 64-byte table, index 0..63), DIFFERENT 0 | EXPOSED: luiscan 2 functions (also in the strlen-A row); hand trace: no differing address |

## Section E: the functions luiscan exposes (the same function has the same exposure in X and Y in every pair)

Records: mA memchr-A, mB memchr-B, sA strlen-A, bA uci-b-alloc (grant), bI uci-b-alloc (identity), bM uci-b-memcpy,
cA / cB / cS cmpkit-audit parts. luiscan's TOTAL lines count some addresses twice (alias names at one address); the sums
above count each function pair once. Every one of these lui values is a size, mask or displacement: in the hand trace it
reaches no base by itself (no "absolute address built from the lui alone" row in any trace); where it is added to a base, the
base is a runtime pointer (same displacement both sides) or a symbol (same symbol + offset both sides, e.g.
StackDepotGet +0x3c: _ZN11__sanitizerL8theDepotE+0x400010 + 8*index in both images).

| function | exposure (X / Y, every pair) | lui trace verdicts (per lui) | records |
|---|---|---|---|
| `_ZN6__asan9Allocator10PrintStatsEv` | 1 / 1 | NO-BASE-USE 2 | mA mB sA bA bI bM |
| `_ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm` | 1 / 1 | NO-BASE-USE 4 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb` | 1 / 1 | NO-BASE-USE 1 | cA cB cS mA mB sA bA bI bM |
| `_ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm` | 2 / 2 | EQUAL 4, NO-BASE-USE 3 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm` | 1 / 1 | EQUAL 2, NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN6__asan14AsanDeactivateEv` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN6__asan26InitializeAsanInterceptorsEv` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7acquireEPNS2_6HandleE` | 1 / 1 | EQUAL 1, NO-BASE-USE 2 | mA mB sA bA bI bM |
| `_ZN11__sanitizer11AddrHashMapI25CommonInterceptorMetadataLm31051EE7releaseEPNS2_6HandleE` | 1 / 1 | NO-BASE-USE 3 | mA mB sA bA bI bM |
| `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE24GetActuallyAllocatedSizeEPv` | 1 / 1 | EQUAL 1 | mA mB sA bA bI bM |
| `_ZN6__asan19SealedReserveShadowEv` | 2 / 2 | NO-BASE-USE 4 | mA mB sA bA bI bM |
| `_ZN6__asan22InitializeShadowMemoryEv` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer18internal_allocatorEv` | 7 / 7 | EQUAL 1, NO-BASE-USE 3 | mA mB sA bA bI bM |
| `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE8AllocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEmm` | 2 / 2 | EQUAL 5, NO-BASE-USE 3 | mA mB sA bA bI bM |
| `_ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm` | 2 / 2 | EQUAL 6, NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE13AllocateBatchEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEm` | 1 / 1 | EQUAL 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE16PopulateFreeListEPNS_14AllocatorStatsEPNS_30SizeClassAllocator32LocalCacheIS2_EEPNS2_13SizeClassInfoEm` | 5 / 5 | EQUAL 5, NO-BASE-USE 6 | mA mB sA bA bI bM |
| `_ZN11__sanitizer20SizeClassAllocator32INS_4AP32EE15DeallocateBatchEPNS_14AllocatorStatsEmPNS2_13TransferBatchE` | 1 / 1 | EQUAL 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE10DeallocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEPv` | 2 / 2 | NO-BASE-USE 2 | mA mB sA bA bI bM |
| `_ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE10DeallocateEPNS_14AllocatorStatsEPv` | 1 / 1 | EQUAL 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer15internal_usleepEy` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer19ReadLongProcessNameEPcm` | 1 / 1 | NO-BASE-USE 2 | mA mB sA bA bI bM |
| `_ZN11__sanitizerL22ReadNullSepFileToArrayEPKcPPPci` | 1 / 1 | NO-BASE-USE 2 | mA mB sA bA bI bM |
| `_ZN11__sanitizer17GetNamedMappingFdEPKcmPi` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizerL23SealedRepairReservationEmm` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer12StopTheWorldEPFvRKNS_20SuspendedThreadsListEPvES3_` | 1 / 1 | NO-BASE-USE 5 | bA |
| `_ZN11__sanitizer10StackStore5AllocEmPmS1_` | 2 / 2 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer10StackStore9BlockInfo11GetOrUnpackEPS0_` | 1 / 1 | NO-BASE-USE 9 | mA mB sA bA bI bM |
| `_ZN11__sanitizer10StackStore9BlockInfo4PackENS0_11CompressionEPS0_` | 1 / 1 | EQUAL 1, NO-BASE-USE 11 | mA mB sA bA bI bM |
| `_ZNK11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE8GetStatsEv` | 4 / 4 | EQUAL 1, NO-BASE-USE 4 | mA mB sA bA bI bM |
| `_ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb` | 3 / 3 | EQUAL 4 | mA mB sA bA bI bM |
| `_ZN11__sanitizer13StackDepotGetEj` | 2 / 2 | EQUAL 1, NO-BASE-USE 1 | mA mB sA bA bI bM |
| `_ZN11__sanitizer25StackDepotUnlockAfterForkEb` | 1 / 1 | EQUAL 1 | bA bI |
| `_ZNK11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE4findEjNS_10StackTraceEy` | 2 / 2 | EQUAL 1 | mA mB sA bA bI bM |
| `_ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `sysconf` | 3 / 3 | NO-BASE-USE 4 | mA mB sA bA bI bM |
| `__vsyslog` | 2 / 2 | NO-BASE-USE 2 | mA mB sA bA bI bM |
| `__map_file` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |
| `__year_to_secs` | 2 / 2 | NO-BASE-USE 6 | mA mB sA bA bI bM |
| `__tm_to_secs` | 1 / 1 | NO-BASE-USE 3 | mA mB sA bA bI bM |
| `__strftime_fmt_1` | 7 / 7 | NO-BASE-USE 14 | cA cB cS mA mB sA bA bI bM |
| `__strftime_l` | 1 / 1 | NO-BASE-USE 1 | mA mB sA bA bI bM |

## Section A: uci-b-alloc AMBIG rows (raw: uci-b-alloc/ambiscan*.out)

- Current outputs (cmpkit 4bbd3a74be89 run): 96 rows, all `cstr` lines of paircl-{malloc,free,tmalloc,tfree}-grant.out and
  ctl-planted-{call,rodata}-paircl.out naming `_ZN6__asanL11MemToShadowEm` (8 per file, X and Y). paircl pairs functions by
  call-target address (paircl.py docstring), so these are not by-name lookups; the record's dupcheck.tsv states the by-address
  verdict equals the by-name verdict for MemToShadow and dummy.
- earlier/ (superseded versions kept in the pack): 300 rows (grant run) / 60 rows (identity run), all in pairtable
  pairs-*.tsv / ctl-pairs-*-identity.tsv rows, each row giving the bare name with both addresses.
- Settled by address (uci-b-alloc/ambig-settle.tsv, ambig-settle.md): each of the 96 current rows is attributed to its
  function pair by re-running paircl's loop (its CSTR lines equal the record's line for line); X copy and Y copy carry the
  same STT_FILE and are called by the paired callers at the same offset: 96 MATCH, 0 MISMATCH. The 300 + 60 earlier/ rows:
  no earlier/ file is cited by RECORD.md, ACCEPTANCES.tsv or settle.tsv (0 hits); MANIFEST.md only lists them as files.
- By ambiscan's own rule (TOTAL 0 = no hit) these rows are hits, so the table marks the row EXPOSED as printed; the reading
  above (address-paired tools, bare name printed beside the addresses) is mine.

## Slices not scanned

- close-B, core-A, core-B, gate, k2: no RECORD / BYTECMP / GATES file and no other file cites a compare (strictcmp2,
  closure_strict2, paircl, jtcheck, repin_check, bytecmp, cmpkit, drvcmp).
- startup-B: cites binmatch.py (the identical-function map cgif_file_fuzzer -> fuzz_uci that gen_exitB.py uses to move code
  numerals; binmatch json not in the pack). Not one of the kit compares, so not scanned here; named so the release check can
  decide.
- uci-b-alloc/inventory/ (a one-image symbol inventory) and uci-b-memcpy callsites-*.out (one-image call-site lists): not
  compares, not scanned.

