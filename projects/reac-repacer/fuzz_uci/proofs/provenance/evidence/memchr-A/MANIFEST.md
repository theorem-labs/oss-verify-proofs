# provenance/evidence/memchr-A: fuzz_uci image A memchr interceptor chain = fuzz_boxreg's released one

Written by scripts/mk_evidence_memchr.py; not edited by hand. What a reader needs to re-derive why lib/A/Rt/Memchr.v may port fuzz_boxreg's released walk (proofs/libreac/fuzz_boxreg/lib/A/Rt/Memchr.v:562 memchr_icpt_realizesM, recipes 88154566652a): the code of fuzz_uci's chain equals the donor's up to relocation. Tools cited, not shipped: the tools of record (commit 8cd71d3a4bb) tools/bytecmp/7daa0e2a03d9/bytecmp.py and tools/repin_check/9cbc3553c09e/repin_check.py. Generation logs are not here.

## Verdict

- chain (__interceptor_trampoline_memchr, ___interceptor_memchr, memchr, _ZN11__sanitizer15internal_memchrEPKvim): EQUAL or EQUAL-mod-pcrel, real 0, target-differ 0
- planted control: caught (DIFFERENT)
- jump / constant table members of the closure: target differs 0, unpaired differing words 0
- the walk's `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` redefinitions, global in the donor, are `Local` in lib/{A,B}/Rt/{Memchr,MemchrChk}.v, so no importer inherits them: 0 global (memchr-local.py --check). With them Local, settings check global_settings v10 (439f8e3bd463) reports 0 ESCAPES over the ten memchr files; with them global it reported 4.

## Files

| file | kind | role |
|---|---|---|
| `scripts/env.example.sh` | config | every variable name the builder reads, without values |
| `scripts/run.sh` | script | the run of record: builds memchr-A and memchr-B |
| `scripts/mk_evidence_memchr.py` | script | this builder |
| `scripts/drvcmp.py` | script | per-function compare (bytecmp cmp + repin_check target pass) and the twins check |
| `scripts/closure.py` | script | direct-call closure compare |
| `scripts/jtcheck.py` | script | jump-table / constant-table members of the closure |
| `scripts/memchr-local.py` | script | makes the walk's global Zify redefinitions Local (only that word changes); --check verifies none is global |
| `tables/twins.txt` | table | unstripped twin = pin, PT_LOAD bytes, both units |
| `tables/chain.tsv` | table | the four chain functions, fuzz_uci : fuzz_boxreg, and the planted control |
| `tables/closure.txt` | table | the interceptor's closure, and the planted control |
| `tables/jtcheck.tsv` | table | the 11 table-carrying closure members |
| `tables/local.txt` | table | memchr-local.py --check on the committed lib |

## Re-run on the comparison kit cmpkit 4bbd3a74be89

Written by scripts/mk_evidence_memchr_kit.py; not edited by hand. The sections above and the tables directly under tables/ were made with bytecmp 7daa0e2a03d9 + repin_check 9cbc3553c09e. This section and `tables/cmpkit-4bbd3a74be89/` re-run the same comparisons with the comparison kit of record, cmpkit 4bbd3a74be89 (commit 3c3e62ee278, tools/cmpkit/4bbd3a74be89/; sha256 of its SHA256SUMS 4bbd3a74be8994d014875952efdb79ef6516680988de43e95a3e217194f0ec33), its seven files run from one directory that holds only them. Tools cited, not shipped. Each verdict is the kit's first; where the kit fails closed, the settled verdict follows it, from a named measurement of this builder (`acceptances.tsv`), or "not certified".

Images (file name, sha256):

- U: fuzz_uci.asan, unstripped twin, `56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb`
- R: fuzz_boxreg.asan, unstripped twin, `4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3`
- pin: fuzz_uci.asan, pinned image, `6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d`
- pin: fuzz_boxreg.asan, pinned image, `eacfa20547ad7dc0d24164010513fcc8af4ba5e557ff3f391a07559e3e34a6df`
- P1: PLANT1(fuzz_boxreg copy, ___interceptor_memchr+0x10 2338217d -> 2338217c), `143a1cfaada0950ee8fce5b654874e0c0c079006c6fb6005b9667b85b84ec723`
- P2: PLANT2(fuzz_boxreg copy, ___interceptor_memchr+0x114 jal _ZN11__sanitizer15internal_memchrEPKvim -> jal __interceptor_trampoline_bcmp, 6f004209 -> 6fe08f94), `6b35c7e65db3d6baef73450cb09b021898440f1e21a0bedbe0db0be762caa0a7`

### Verdict

- CLAIM: NARROWED to the chain: the four chain functions (`__interceptor_trampoline_memchr`, `___interceptor_memchr`, `memchr`, `_ZN11__sanitizer15internal_memchrEPKvim`) equal the donor's up to relocation on the kit, every target equal. The closure of `___interceptor_memchr` is not certified as a whole: 6 reported members are listed below as not certified.
- twins (each pin = its unstripped twin, PT_LOAD bytes; `twins.txt`): equal outside the ELF header and build-id note (unchanged)
- chain, U : R (`chain.tsv`), kit verdict (old verdict):
  - `__interceptor_trampoline_memchr`: EQUAL-mod-pcrel (old: EQUAL-mod-pcrel)
  - `___interceptor_memchr`: EQUAL-mod-pcrel (old: EQUAL-mod-pcrel)
  - `memchr`: EQUAL-mod-pcrel (old: EQUAL-mod-pcrel)
  - `_ZN11__sanitizer15internal_memchrEPKvim`: EQUAL (old: EQUAL)
- closure of `___interceptor_memchr` (`closure.txt`): kit: 785 functions, EQUAL 172, EQUAL-mod-pcrel with all targets equal 551, reported 62 (old: 785 functions, EQUAL 172, EQUAL-mod-pcrel 602, other 11). Of the 62 reported: settled by the kit's jtcheck 13; settled by measurement 43; not certified 6; REAL 0.
- jtcheck over 62 functions, the 11 of the old record and every reported closure member (`jtcheck.tsv`): kit: settled 13, not settled 49 (old: 11 run, settled 11). Its 141 unsettled targets, measured (`acceptances.tsv`): C string with non-printable bytes 69, empty string 57, not certified 6, unnamed table 9.
- planted control (`control.txt`): P1 caught (chain row DIFFERENT; closure reports `___interceptor_memchr` only; jtcheck: REAL difference yes); P2 caught (chain row EQUAL-mod-pcrel target-differ 1 at +0x114; closure reports it; jtcheck DIFF at +0x114: yes)

Settled verdicts (this builder's measurement on file bytes, read with the kit's Img / frd / region / qres; never a kit EQUAL): "empty string", "C string with non-printable bytes", "C string" = an unnamed target whose address every path that uses it passes on as a call argument or a return value, equal through its NUL in both images (the kit fails closed: its C-string rule needs printable bytes, and the region to the next symbol differs). "unnamed table" = an indexed unnamed .rodata table, equal entry by entry over every index its bound allows: a jump table as function+offset, a relative pointer table as symbol+offset (an unnamed entry target as a C string through its NUL), a value table over the bytes its index can reach; the bounding instructions are named in `acceptances.tsv`. "not certified" = the measurement did not settle it (its consumer or bound was not followed). "REAL" = bytes the code reads differ.

### Changed verdicts against the old tables

| table | function | pair | old verdict | kit verdict | kit line | settled verdict |
|---|---|---|---|---|---|---|
| closure | `___interceptor_memchr` | U:R | closure 785 functions, EQUAL 172, EQUAL-mod-pcrel 602, other 11 | closure 785 functions, EQUAL 172, EQUAL-mod-pcrel 551, other 62 | `closure.txt:1` | - |
| closure | `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE` | U:R @0x30b20 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:2` | settled by measurement: unnamed table |
| closure | `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb` | U:R @0x30e34 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:3` | settled by measurement: unnamed table |
| closure | `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb` | U:R @0x33c64 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:4` | settled by measurement: unnamed table |
| closure | `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE21ReleaseFreeMemoryToOSINS_12MemoryMapperIS5_EEEEvPjmmmPT_m` | U:R @0x33e50 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:5` | settled by measurement: unnamed table |
| closure | `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_` | U:R @0x343fc | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:6` | settled by measurement: unnamed table |
| closure | `_ZN6__asanL10RZSize2LogEj` | U:R @0x36190 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:7` | settled by measurement: unnamed table |
| closure | `_ZNK6__asan22HeapAddressDescription5PrintEv` | U:R @0x37828 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:8` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZNK6__asan23StackAddressDescription5PrintEv` | U:R @0x37d84 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:9` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZNK6__asan24GlobalAddressDescription5PrintEPKc` | U:R @0x3826c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:10` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan15ErrorDoubleFree5PrintEv` | U:R @0x38c10 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:11` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan26ErrorNewDeleteTypeMismatch5PrintEv` | U:R @0x38d70 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:12` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan20ErrorFreeNotMalloced5PrintEv` | U:R @0x3909c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:13` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZNK6__asan18AddressDescription5PrintEPKc` | U:R @0x39240 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:14` | settled by the kit (jtcheck) |
| closure | `_ZN6__asan22ErrorAllocTypeMismatch5PrintEv` | U:R @0x392b8 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:15` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan29ErrorMallocUsableSizeNotOwned5PrintEv` | U:R @0x394c0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:16` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan38ErrorSanitizerGetAllocatedSizeNotOwned5PrintEv` | U:R @0x395a0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:17` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan19ErrorCallocOverflow5PrintEv` | U:R @0x39680 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:18` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan25ErrorReallocArrayOverflow5PrintEv` | U:R @0x3975c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:19` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan20ErrorPvallocOverflow5PrintEv` | U:R @0x39838 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:20` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan31ErrorInvalidAllocationAlignment5PrintEv` | U:R @0x39928 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:21` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan33ErrorInvalidAlignedAllocAlignment5PrintEv` | U:R @0x399f4 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:22` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan34ErrorInvalidPosixMemalignAlignment5PrintEv` | U:R @0x39ad0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:23` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan25ErrorAllocationSizeTooBig5PrintEv` | U:R @0x39ba0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:24` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan21ErrorRssLimitExceeded5PrintEv` | U:R @0x39c8c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:25` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan16ErrorOutOfMemory5PrintEv` | U:R @0x39d40 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:26` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan38ErrorStringFunctionMemoryRangesOverlap5PrintEv` | U:R @0x39df8 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:27` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan31ErrorStringFunctionSizeOverflow5PrintEv` | U:R @0x39f7c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:28` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan17ErrorODRViolation5PrintEv` | U:R @0x3a160 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:29` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan23ErrorInvalidPointerPair5PrintEv` | U:R @0x3a478 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:30` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan12ErrorGenericC1Ejmmmmbm` | U:R @0x3a5f4 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:31` | settled by the kit (jtcheck) |
| closure | `_ZN6__asan12ErrorGeneric5PrintEv` | U:R @0x3ac38 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:32` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan15InitializeFlagsEv` | U:R @0x3c484 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:33` | not certified |
| closure | `_ZN6__asan15PrintMemoryByteEPN11__sanitizer20InternalScopedStringEPKchbS4_` | U:R @0x53ce0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:34` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__asan9Decorator10ShadowByteEh` | U:R @0x53dc8 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:35` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `__asan_describe_address` | U:R @0x56fe8 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:36` | settled by measurement: empty string |
| closure | `_ZN6__asan16ErrorDescription5PrintEv` | U:R @0x57248 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:37` | settled by the kit (jtcheck) |
| closure | `_ZN6__asanL23force_interface_symbolsEv` | U:R @0x589ac | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:38` | settled by the kit (jtcheck) |
| closure | `__asan_default_suppressions` | U:R @0x5a0f0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:39` | settled by measurement: empty string |
| closure | `_ZN11__sanitizer12LoadedModule15addAddressRangeEmmbbPKc` | U:R @0x5ed84 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:40` | settled by the kit (jtcheck) |
| closure | `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | U:R @0x60118 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:41` | not certified |
| closure | `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | U:R @0x605ac | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:42` | not certified |
| closure | `_ZN11__sanitizer10FlagParser21PrintFlagDescriptionsEv` | U:R @0x61c08 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:43` | settled by measurement: empty string |
| closure | `_ZN11__sanitizer8OpenFileEPKcNS_14FileAccessModeEPi` | U:R @0x64e9c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:45` | settled by measurement: unnamed table |
| closure | `_ZN11__sanitizer9VSNPrintfEPciPKcPv` | U:R @0x65578 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:47` | settled by the kit (jtcheck) |
| closure | `_ZN11__sanitizer10Symbolizer12PlatformInitEv` | U:R @0x763d0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:48` | settled by the kit (jtcheck) |
| closure | `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_` | U:R @0x774a4 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:49` | settled by measurement: C string with non-printable bytes + empty string |
| closure | `_ZN6__lsan5Flags11SetDefaultsEv` | U:R @0x78d8c | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:50` | not certified |
| closure | `__lsan_default_options` | U:R @0x7bc44 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:51` | settled by measurement: empty string |
| closure | `_ZN7__ubsan5Flags11SetDefaultsEv` | U:R @0x7ecd0 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:52` | not certified |
| closure | `__ubsan_default_options` | U:R @0x7ee30 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:53` | settled by measurement: empty string |
| closure | `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE` | U:R @0x80c34 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:54` | settled by measurement: unnamed table |
| closure | `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE` | U:R @0x823c4 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:55` | settled by the kit (jtcheck) |
| closure | `_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm` | U:R @0x83d1c | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:56` | settled by the kit (jtcheck) |
| closure | `_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh` | U:R @0x8561c | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:57` | settled by the kit (jtcheck) |
| closure | `sysconf` | U:R @0x85ef4 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:58` | settled by the kit (jtcheck) |
| closure | `__fstat` | U:R @0x8bc00 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:59` | settled by measurement: empty string |
| closure | `__nl_langinfo_l` | U:R @0x93188 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:61` | not certified |
| closure | `__tm_to_tzname` | U:R @0x93a90 | settled (EQUAL / EQUAL-mod-pcrel, all targets equal) | EQUAL-mod-pcrel target-differ | `closure.txt:62` | settled by measurement: empty string |
| closure | `__strftime_fmt_1` | U:R @0x94d24 | UNMEASURED | EQUAL-mod-pcrel target-differ | `closure.txt:63` | settled by measurement: empty string |
| jtcheck | `_ZN6__asan9Decorator10ShadowByteEh` | U:R | settled | not settled: target differs 2, target unmeasured 4, unpaired 0 | `jtcheck.tsv:24` | settled by measurement: C string with non-printable bytes + empty string |
| jtcheck | `_ZNK11__sanitizer13SignalContext8DescribeEv` | U:R | settled | not settled: target differs 0, target unmeasured 1, unpaired 0 | `jtcheck.tsv:41` | settled by measurement: unnamed table |
| jtcheck | `__strftime_fmt_1` | U:R | settled | not settled: target differs 0, target unmeasured 2, unpaired 0 | `jtcheck.tsv:178` | settled by measurement: empty string |

Each row's detail and the kit's full line are in `tables/cmpkit-4bbd3a74be89/changed.tsv`.

### Not certified

| function | X address | kit verdict | unsettled targets (`acceptances.tsv`) |
|---|---|---|---|
| `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | 0x60118 | EQUAL-mod-pcrel target-differ | +0x48 not certified |
| `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | 0x605ac | EQUAL-mod-pcrel target-differ | +0x1218 not certified |
| `_ZN6__asan15InitializeFlagsEv` | 0x3c484 | EQUAL-mod-pcrel target-differ | +0x104 not certified |
| `_ZN6__lsan5Flags11SetDefaultsEv` | 0x78d8c | EQUAL-mod-pcrel target-differ | +0xc not certified |
| `_ZN7__ubsan5Flags11SetDefaultsEv` | 0x7ecd0 | EQUAL-mod-pcrel target-differ | +0x4 not certified |
| `__nl_langinfo_l` | 0x93188 | EQUAL-mod-pcrel target-differ | +0x5c empty string; +0xf8 not certified |

### Acceptances (settled by measurement, not by the kit; a fresh reviewer audits them)

Grouped by target and measured bytes; one row per use is in `tables/cmpkit-4bbd3a74be89/acceptances.tsv`, with the consumer (the call or return that passes the address on) or the table bound of each use.

| settled verdict | measurement | uses |
|---|---|---|
| C string with non-printable bytes | b'\x1b[1m\x1b[0m\x00' equal through its NUL at 0x18da2 \| 0x18dc7 | 33: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1f0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6b0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xd0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xe4`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[31m\x00' equal through its NUL at 0x17764 \| 0x17799 | 23: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1ec`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xcc`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xe0`, `_ZN6__asan12ErrorGeneric5PrintEv+0x5c`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[35m\x00' equal through its NUL at 0x1d709 \| 0x1d728 | 5: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6b8`, `_ZN6__asan15PrintMemoryByteEPN11__sanitizer20InternalScopedStringEPKchbS4_+0x94`, `_ZN6__asan9Decorator10ShadowByteEh+0x48`, `_ZNK6__asan22HeapAddressDescription5PrintEv+0x2d4`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[32m\x00' equal through its NUL at 0x176fa \| 0x1772f | 4: `_ZNK6__asan22HeapAddressDescription5PrintEv+0xbc`, `_ZNK6__asan23StackAddressDescription5PrintEv+0x3d4`, `_ZNK6__asan23StackAddressDescription5PrintEv+0x58`, `_ZNK6__asan24GlobalAddressDescription5PrintEPKc+0x88` |
| C string with non-printable bytes | b'\x1b[1m\x1b[34m\x00' equal through its NUL at 0x1f9aa \| 0x1f9de | 2: `_ZN6__asan12ErrorGeneric5PrintEv+0xd0`, `_ZN6__asan9Decorator10ShadowByteEh+0x34` |
| C string with non-printable bytes | b'\x1b[1m\x1b[33m\x00' equal through its NUL at 0x20198 \| 0x201cc | 1: `_ZN6__asan9Decorator10ShadowByteEh+0x5c` |
| C string with non-printable bytes | b'\x1b[1m\x1b[36m\x00' equal through its NUL at 0x10903 \| 0x10903 | 1: `_ZN6__asan9Decorator10ShadowByteEh+0x70` |
| empty string | b'\x00' equal through its NUL at 0x13e5f \| 0x13e6c | 57: `_ZN11__sanitizer10FlagParser21PrintFlagDescriptionsEv+0x70`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x15c`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1d8`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6c0`, ... |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x103e0 \| 0x103e0 | 1: `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE+0x20c` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10420 \| 0x10420 | 1: `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb+0xdc` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10460 \| 0x10460 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb+0x140` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x104a0 \| 0x104a0 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE21ReleaseFreeMemoryToOSINS_12MemoryMapperIS5_EEEEvPjmmmPT_m+0x128` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x104e0 \| 0x104e0 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_+0x190` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10520 \| 0x10520 | 1: `_ZN6__asanL10RZSize2LogEj+0x44` |
| unnamed table | value table, 3 entries of 4 bytes (stride 4): the 12 bytes its index can reach are equal at 0x20990 \| 0x209c4 | 1: `_ZN11__sanitizer8OpenFileEPKcNS_14FileAccessModeEPi+0x60` |
| unnamed table | relative pointer table, 8 entries, each the same symbol+offset or (unnamed) the same C string through its NUL (b'ILL\x00', b'TRAP\x00', b'ABRT\x00', b'BUS\x00', b'FPE\x00', b'UNKNOWN SIGNAL\x00', b'UNKNOWN SIGNAL\x00', b'SEGV\x00') at 0x2099c \| 0x209d0 | 1: `_ZNK11__sanitizer13SignalContext8DescribeEv+0x1c` |
| unnamed table | relative jump table, 47 entries: every entry the same function+offset (6 distinct cases) at 0x20cd0 \| 0x20d94 | 1: `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE+0x23c` |

### Files

| file | kind | role |
|---|---|---|
| `scripts/mk_evidence_memchr_kit.py` | script | this re-run's builder |
| `tables/cmpkit-4bbd3a74be89/twins.txt` | table | drvcmp.py twins: each pin = its unstripped twin |
| `tables/cmpkit-4bbd3a74be89/chain.tsv` | table | strictcmp2.py cmp: the four chain functions, U : R |
| `tables/cmpkit-4bbd3a74be89/closure.txt` | table | closure_strict2.py: the closure of `___interceptor_memchr`, U : R |
| `tables/cmpkit-4bbd3a74be89/jtcheck.tsv` | table | jtcheck.py: the old 11 and every reported closure member |
| `tables/cmpkit-4bbd3a74be89/control.txt` | table | the planted copies P1, P2 against R, under strictcmp2, closure_strict2, jtcheck |
| `tables/cmpkit-4bbd3a74be89/acceptances.tsv` | table | each target jtcheck leaves unsettled: kit verdict, settled verdict, measurement |
| `tables/cmpkit-4bbd3a74be89/changed.tsv` | table | every changed verdict, the kit's line, and the settled verdict |

## Not-certified rows settled by measurement

Two of the six not-certified closure rows are settled by scripts/settle2.py (run by scripts/run_settle2.py) on U = fuzz_uci.asan (sha256 56822e263d76) and R = fuzz_boxreg.asan (sha256 4532568b621d): 32 checks, all PASS (tables/cmpkit-4bbd3a74be89/settled2.tsv). Control: the same run on a copy of R with the empty string's first byte changed fails exactly the two string checks (tables/cmpkit-4bbd3a74be89/settled2-control.tsv).

- `__nl_langinfo_l+0xf8`: SETTLED. The string is empty (NUL) in both images; the code reads that one byte (`lbu` +0x100) and returns the address (`bnez` +0xfc / `beqz` +0x104 -> `ret` +0x118); its returned value has the consumers of the accepted row `__nl_langinfo_l+0x5c`.
- `RegisterCommonFlags+0x1218`: SETTLED. The empty string is stored (+0x1228, +0x1274) into the field +0x18 of two objects whose vtable is __sanitizer::FlagHandlerInclude's (+0x121c, +0x1268). Of that vtable's two methods Parse only writes the field and Format reads it once and passes it to internal_snprintf with the format "%s". [Limit: that no code outside the class reads the field is a property of the class, not measured.]
- `CommonFlags::SetDefaults+0x48`, `InitializeFlags+0x104`, `__lsan::Flags::SetDefaults+0xc`, `__ubsan::Flags::SetDefaults+0x4`: NOT CERTIFIED: reader list of flag fields needed. The claim of this slice is the chain, which does not depend on them.
