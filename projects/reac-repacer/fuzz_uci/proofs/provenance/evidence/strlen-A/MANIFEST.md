# provenance/evidence/strlen-A: fuzz_uci image A strlen and memchr chains = fuzz_identity's released ones (cmpkit 4bbd3a74be89)

Written by scripts/mk_evidence_strlen_kit.py; not edited by hand. What a reader needs to re-derive why fuzz_uci's lib/A strlen and memchr walks may port fuzz_identity's released ones: the code of fuzz_uci image A's strlen and memchr chains equals the donor's up to relocation. Donor: fuzz_identity, recipes 70952e1c8c9 (PR #399): proofs/libreac/fuzz_identity/lib/A/Rt/StrlenDef.v:36 `astrlen_realizes`, proved as proofs/libreac/fuzz_identity/lib/A/Rt/Strlen.v:26 `strlen_icpt_contract`; proofs/libreac/fuzz_identity/lib/A/Rt/MemchrDef.v:25 `amemchr_realizes`, proved as proofs/libreac/fuzz_identity/lib/A/Rt/Memchr.v:574 `memchr_icpt_contract`; the pinned image below is the one projects/libreac/fuzz_identity/harness.yaml pins at that commit. Tools cited, not shipped: the comparison kit of record, cmpkit 4bbd3a74be89 (commit 3c3e62ee278, tools/cmpkit/4bbd3a74be89/; sha256 of its SHA256SUMS 4bbd3a74be8994d014875952efdb79ef6516680988de43e95a3e217194f0ec33), its seven files run from one directory that holds only them. Each verdict is the kit's first; where the kit fails closed, the settled verdict follows it, from a named measurement of this builder (`tables/acceptances.tsv`), or "not certified". Generation logs are not here.

Images (file name, sha256):

- U: fuzz_uci.asan, unstripped twin, `56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb`
- R: fuzz_identity.asan, unstripped twin, `5b0cbe57303630895c71979f5c3209f1d343f0f42aad36e87c9f5193408da124`
- pin: fuzz_uci.asan, pinned image, `6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d`
- pin: fuzz_identity.asan, pinned image, `c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b`
- P1: P1(fuzz_identity copy, ___interceptor_strlen+0x48 00090513 -> 00048513), `67ec8c7bb7018c0b76bae49a00ffdce15dfd007dda637d36def47505ebe00df0`
- P2: P2(fuzz_identity copy, ___interceptor_strlen+0x30 jal _ZN6__asan10AsanInitedEv -> jal __interceptor_trampoline_strnlen, 70c160ef -> f45ff0ef), `d645ff968e7cae8c5f03ba2a3cfe4dda2385a5f4213fb0e0407a67201c0b7114`
- P3: P3(fuzz_identity copy, memchr+0x18 00100813 -> 00200813), `22a717d7941cc7378952768546f78461fd12793816012a71328fec66bef633b7`
- P4: P4(fuzz_identity copy, __asan_region_is_poisoned+0x0 fc010113 -> fc810113), `eea2ff3d49d65162e5b7b475d7a47b4e7974cdb74df1739ea008ad2aa76877ce`
- P5: P5(fuzz_identity copy, sysconf jump-table entry 1 at 0x21cdc: 000686f0 -> 000686f4), `e2b24355b37bd967e2ae3d6955cb60385a9fc762a4731cbe43576408c9f69b59`

## Verdict

- CLAIM: NARROWED to the chain: the eight chain functions (`__interceptor_trampoline_strlen`, `___interceptor_strlen`, `strlen`, `_ZN11__sanitizer15internal_strlenEPKc`, `__interceptor_trampoline_memchr`, `___interceptor_memchr`, `memchr`, `_ZN11__sanitizer15internal_memchrEPKvim`) equal the donor's up to relocation on the kit, every target equal. The closures of `___interceptor_strlen` and `___interceptor_memchr` are not certified as a whole: 6 reported members are listed below as not certified.
- twins (each pin = its unstripped twin, PT_LOAD bytes; `tables/twins.txt`): equal outside the ELF header and build-id note
- chain, U : R (`tables/chain.tsv`), kit verdict (pc-relative words; real, unmeasured, target-differ):
  - `__interceptor_trampoline_strlen`: EQUAL-mod-pcrel (1; 0, 0, 0) `chain.tsv:5`
  - `___interceptor_strlen`: EQUAL-mod-pcrel (24; 0, 0, 0) `chain.tsv:6`
  - `strlen`: EQUAL-mod-pcrel (4; 0, 0, 0) `chain.tsv:8`
  - `_ZN11__sanitizer15internal_strlenEPKc`: EQUAL (0; 0, 0, 0) `chain.tsv:9`
  - `__interceptor_trampoline_memchr`: EQUAL-mod-pcrel (1; 0, 0, 0) `chain.tsv:10`
  - `___interceptor_memchr`: EQUAL-mod-pcrel (26; 0, 0, 0) `chain.tsv:11`
  - `memchr`: EQUAL-mod-pcrel (4; 0, 0, 0) `chain.tsv:13`
  - `_ZN11__sanitizer15internal_memchrEPKvim`: EQUAL (0; 0, 0, 0) `chain.tsv:14`
- the kit's own acceptances inside the chain verdicts (value / full-bytes, and C-string; also the CSTR rows of `chain.tsv`): `___interceptor_strlen`: full+0x260[0x103d0\|0x103d8]=8; `___interceptor_strlen`: 0x1e0@0x16981\|0x16b1f=b'strlen\x00'; `strlen`: full+0x44[0x10368\|0x10368]=8 full+0x48[0x10350\|0x10350]=8; `___interceptor_memchr`: full+0x29c[0x103d0\|0x103d8]=8; `___interceptor_memchr`: 0x204@0x19fc9\|0x1a1d1=b'memchr\x00'; `memchr`: full+0x5c[0x10368\|0x10368]=8 full+0x64[0x10350\|0x10350]=8
- closures (`tables/closure.txt`): `___interceptor_strlen`: 784 functions, EQUAL 172, EQUAL-mod-pcrel with all targets equal 550, reported 62; `___interceptor_memchr`: 785 functions, EQUAL 172, EQUAL-mod-pcrel with all targets equal 551, reported 62. The reported members, 62 distinct functions over both roots (`tables/members.tsv`): settled by the kit's jtcheck 13; settled by measurement 43; not certified 6; REAL 0.
- jtcheck over 62 functions, the 11 table members of the earlier record and every reported closure member (`tables/jtcheck.tsv`): kit: settled 13, not settled 49. Its 141 unsettled targets, measured (`tables/acceptances.tsv`): C string with non-printable bytes 69, empty string 57, not certified 6, unnamed table 9.
- planted controls (`tables/control.txt`): P1 caught, P2 caught, P3 caught, P4 caught, P5 caught

Settled verdicts (this builder's measurement on file bytes, read with the kit's Img / frd / region / qres; never a kit EQUAL): "empty string", "C string with non-printable bytes", "C string" = an unnamed target whose address every path that uses it passes on as a call argument or a return value, equal through its NUL in both images (the kit fails closed: its C-string rule needs printable bytes, and the region to the next symbol differs). "unnamed table" = an indexed unnamed .rodata table, equal entry by entry over every index its bound allows: a jump table as function+offset, a relative pointer table as symbol+offset (an unnamed entry target as a C string through its NUL), a value table over the bytes its index can reach; the bounding instructions are named in `tables/acceptances.tsv`. "not certified" = the measurement did not settle it (its consumer or bound was not followed). "REAL" = bytes the code reads differ.

## Reported closure members (the kit's verdict, then the settled verdict)

| function | X address | reported under | kit verdict | kit line | jtcheck | settled verdict |
|---|---|---|---|---|---|---|
| `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE` | 0x30b20 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:2`, `closure.txt:3339` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:862`) | settled by measurement: unnamed table |
| `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb` | 0x30e34 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:3`, `closure.txt:3340` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:867`) | settled by measurement: unnamed table |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb` | 0x33c64 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:4`, `closure.txt:3341` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:463`) | settled by measurement: unnamed table |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE21ReleaseFreeMemoryToOSINS_12MemoryMapperIS5_EEEEvPjmmmPT_m` | 0x33e50 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:5`, `closure.txt:3342` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:480`) | settled by measurement: unnamed table |
| `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_` | 0x343fc | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:6`, `closure.txt:3343` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:467`) | settled by measurement: unnamed table |
| `_ZN6__asanL10RZSize2LogEj` | 0x36190 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:7`, `closure.txt:3344` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:891`) | settled by measurement: unnamed table |
| `_ZNK6__asan22HeapAddressDescription5PrintEv` | 0x37828 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:8`, `closure.txt:3345` | not settled: target differs 0, target unmeasured 12, unpaired 0 (`jtcheck.tsv:924`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZNK6__asan23StackAddressDescription5PrintEv` | 0x37d84 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:9`, `closure.txt:3346` | not settled: target differs 0, target unmeasured 9, unpaired 0 (`jtcheck.tsv:971`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZNK6__asan24GlobalAddressDescription5PrintEPKc` | 0x3826c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:10`, `closure.txt:3347` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:1009`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan15ErrorDoubleFree5PrintEv` | 0x38c10 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:11`, `closure.txt:3348` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:566`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan26ErrorNewDeleteTypeMismatch5PrintEv` | 0x38d70 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:12`, `closure.txt:3349` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:788`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan20ErrorFreeNotMalloced5PrintEv` | 0x3909c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:13`, `closure.txt:3350` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:721`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZNK6__asan18AddressDescription5PrintEPKc` | 0x39240 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:14`, `closure.txt:3351` | settled (`jtcheck.tsv:920`) | settled by the kit (jtcheck) |
| `_ZN6__asan22ErrorAllocTypeMismatch5PrintEv` | 0x392b8 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:15`, `closure.txt:3352` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:748`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan29ErrorMallocUsableSizeNotOwned5PrintEv` | 0x394c0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:16`, `closure.txt:3353` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:803`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan38ErrorSanitizerGetAllocatedSizeNotOwned5PrintEv` | 0x395a0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:17`, `closure.txt:3354` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:838`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan19ErrorCallocOverflow5PrintEv` | 0x39680 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:18`, `closure.txt:3355` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:715`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan25ErrorReallocArrayOverflow5PrintEv` | 0x3975c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:19`, `closure.txt:3356` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:782`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan20ErrorPvallocOverflow5PrintEv` | 0x39838 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:20`, `closure.txt:3357` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:734`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan31ErrorInvalidAllocationAlignment5PrintEv` | 0x39928 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:21`, `closure.txt:3358` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:813`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan33ErrorInvalidAlignedAllocAlignment5PrintEv` | 0x399f4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:22`, `closure.txt:3359` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:826`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan34ErrorInvalidPosixMemalignAlignment5PrintEv` | 0x39ad0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:23`, `closure.txt:3360` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:832`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan25ErrorAllocationSizeTooBig5PrintEv` | 0x39ba0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:24`, `closure.txt:3361` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:776`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan21ErrorRssLimitExceeded5PrintEv` | 0x39c8c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:25`, `closure.txt:3362` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:742`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan16ErrorOutOfMemory5PrintEv` | 0x39d40 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:26`, `closure.txt:3363` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:696`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan38ErrorStringFunctionMemoryRangesOverlap5PrintEv` | 0x39df8 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:27`, `closure.txt:3364` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:848`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan31ErrorStringFunctionSizeOverflow5PrintEv` | 0x39f7c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:28`, `closure.txt:3365` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:819`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan17ErrorODRViolation5PrintEv` | 0x3a160 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:29`, `closure.txt:3366` | not settled: target differs 0, target unmeasured 3, unpaired 0 (`jtcheck.tsv:702`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan23ErrorInvalidPointerPair5PrintEv` | 0x3a478 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:30`, `closure.txt:3367` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:764`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan12ErrorGenericC1Ejmmmmbm` | 0x3a5f4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:31`, `closure.txt:3368` | settled (`jtcheck.tsv:1`) | settled by the kit (jtcheck) |
| `_ZN6__asan12ErrorGeneric5PrintEv` | 0x3ac38 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:32`, `closure.txt:3369` | not settled: target differs 0, target unmeasured 7, unpaired 0 (`jtcheck.tsv:515`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan15InitializeFlagsEv` | 0x3c484 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:33`, `closure.txt:3370` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:573`) | not certified |
| `_ZN6__asan15PrintMemoryByteEPN11__sanitizer20InternalScopedStringEPKchbS4_` | 0x53ce0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:34`, `closure.txt:3371` | not settled: target differs 0, target unmeasured 4, unpaired 0 (`jtcheck.tsv:690`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__asan9Decorator10ShadowByteEh` | 0x53dc8 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:35`, `closure.txt:3372` | not settled: target differs 0, target unmeasured 6, unpaired 0 (`jtcheck.tsv:24`) | settled by measurement: C string with non-printable bytes + empty string |
| `__asan_describe_address` | 0x56fe8 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:36`, `closure.txt:3373` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1023`) | settled by measurement: empty string |
| `_ZN6__asan16ErrorDescription5PrintEv` | 0x57248 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:37`, `closure.txt:3374` | settled (`jtcheck.tsv:33`) | settled by the kit (jtcheck) |
| `_ZN6__asanL23force_interface_symbolsEv` | 0x589ac | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:38`, `closure.txt:3375` | settled (`jtcheck.tsv:904`) | settled by the kit (jtcheck) |
| `__asan_default_suppressions` | 0x5a0f0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:39`, `closure.txt:3376` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1021`) | settled by measurement: empty string |
| `_ZN11__sanitizer12LoadedModule15addAddressRangeEmmbbPKc` | 0x5ed84 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:40`, `closure.txt:3377` | settled (`jtcheck.tsv:239`) | settled by the kit (jtcheck) |
| `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | 0x60118 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:41`, `closure.txt:3378` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:233`) | not certified |
| `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | 0x605ac | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:42`, `closure.txt:3379` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:283`) | not certified |
| `_ZN11__sanitizer10FlagParser21PrintFlagDescriptionsEv` | 0x61c08 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:43`, `closure.txt:3380` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:202`) | settled by measurement: empty string |
| `_ZN11__sanitizer19GetHandleSignalModeEi` | 0x64208 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:44`, `closure.txt:3381` | settled (`jtcheck.tsv:39`) | settled by the kit (jtcheck) |
| `_ZN11__sanitizer8OpenFileEPKcNS_14FileAccessModeEPi` | 0x64e9c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:45`, `closure.txt:3382` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:492`) | settled by measurement: unnamed table |
| `_ZNK11__sanitizer13SignalContext8DescribeEv` | 0x65330 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:46`, `closure.txt:3383` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:41`) | settled by measurement: unnamed table |
| `_ZN11__sanitizer9VSNPrintfEPciPKcPv` | 0x65578 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:47`, `closure.txt:3384` | settled (`jtcheck.tsv:495`) | settled by the kit (jtcheck) |
| `_ZN11__sanitizer10Symbolizer12PlatformInitEv` | 0x763d0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:48`, `closure.txt:3385` | settled (`jtcheck.tsv:209`) | settled by the kit (jtcheck) |
| `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_` | 0x774a4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:49`, `closure.txt:3386` | not settled: target differs 0, target unmeasured 13, unpaired 0 (`jtcheck.tsv:241`) | settled by measurement: C string with non-printable bytes + empty string |
| `_ZN6__lsan5Flags11SetDefaultsEv` | 0x78d8c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:50`, `closure.txt:3387` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:906`) | not certified |
| `__lsan_default_options` | 0x7bc44 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:51`, `closure.txt:3388` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1028`) | settled by measurement: empty string |
| `_ZN7__ubsan5Flags11SetDefaultsEv` | 0x7ecd0 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:52`, `closure.txt:3389` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:908`) | not certified |
| `__ubsan_default_options` | 0x7ee30 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:53`, `closure.txt:3390` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1038`) | settled by measurement: empty string |
| `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE` | 0x80c34 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:54`, `closure.txt:3391` | not settled: target differs 1, target unmeasured 0, unpaired 0 (`jtcheck.tsv:910`) | settled by measurement: unnamed table |
| `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE` | 0x823c4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:55`, `closure.txt:3392` | settled (`jtcheck.tsv:44`) | settled by the kit (jtcheck) |
| `_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm` | 0x83d1c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:56`, `closure.txt:3393` | settled (`jtcheck.tsv:142`) | settled by the kit (jtcheck) |
| `_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh` | 0x8561c | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:57`, `closure.txt:3394` | settled (`jtcheck.tsv:166`) | settled by the kit (jtcheck) |
| `sysconf` | 0x85ef4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:58`, `closure.txt:3395` | settled (`jtcheck.tsv:174`) | settled by the kit (jtcheck) |
| `__fstat` | 0x8bc00 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:59`, `closure.txt:3396` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1026`) | settled by measurement: empty string |
| `__synccall` | 0x92cb4 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:60`, `closure.txt:3397` | settled (`jtcheck.tsv:176`) | settled by the kit (jtcheck) |
| `__nl_langinfo_l` | 0x93188 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:61`, `closure.txt:3398` | not settled: target differs 0, target unmeasured 2, unpaired 0 (`jtcheck.tsv:1030`) | not certified |
| `__tm_to_tzname` | 0x93a90 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:62`, `closure.txt:3399` | not settled: target differs 0, target unmeasured 1, unpaired 0 (`jtcheck.tsv:1036`) | settled by measurement: empty string |
| `__strftime_fmt_1` | 0x94d24 | strlen, memchr | EQUAL-mod-pcrel target-differ | `closure.txt:63`, `closure.txt:3400` | not settled: target differs 0, target unmeasured 2, unpaired 0 (`jtcheck.tsv:178`) | settled by measurement: empty string |

## Not certified

| function | X address | kit verdict | unsettled targets (`tables/acceptances.tsv`) |
|---|---|---|---|
| `_ZN6__asan15InitializeFlagsEv` | 0x3c484 | EQUAL-mod-pcrel target-differ | +0x104 not certified |
| `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | 0x60118 | EQUAL-mod-pcrel target-differ | +0x48 not certified |
| `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | 0x605ac | EQUAL-mod-pcrel target-differ | +0x1218 not certified |
| `_ZN6__lsan5Flags11SetDefaultsEv` | 0x78d8c | EQUAL-mod-pcrel target-differ | +0xc not certified |
| `_ZN7__ubsan5Flags11SetDefaultsEv` | 0x7ecd0 | EQUAL-mod-pcrel target-differ | +0x4 not certified |
| `__nl_langinfo_l` | 0x93188 | EQUAL-mod-pcrel target-differ | +0x5c empty string; +0xf8 not certified |

## Acceptances (settled by measurement, not by the kit; a fresh reviewer audits them)

Grouped by target and measured bytes; one row per use is in `tables/acceptances.tsv`, with the kit's verdict, and the consumer (the call or return that passes the address on) or the table bound of each use.

| settled verdict | measurement | uses |
|---|---|---|
| C string with non-printable bytes | b'\x1b[1m\x1b[0m\x00' equal through its NUL at 0x18da2 \| 0x18f92 | 33: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1f0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6b0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xd0`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xe4`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[31m\x00' equal through its NUL at 0x17764 \| 0x17945 | 23: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1ec`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xcc`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0xe0`, `_ZN6__asan12ErrorGeneric5PrintEv+0x5c`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[35m\x00' equal through its NUL at 0x1d709 \| 0x1d9af | 5: `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6b8`, `_ZN6__asan15PrintMemoryByteEPN11__sanitizer20InternalScopedStringEPKchbS4_+0x94`, `_ZN6__asan9Decorator10ShadowByteEh+0x48`, `_ZNK6__asan22HeapAddressDescription5PrintEv+0x2d4`, ... |
| C string with non-printable bytes | b'\x1b[1m\x1b[32m\x00' equal through its NUL at 0x176fa \| 0x178db | 4: `_ZNK6__asan22HeapAddressDescription5PrintEv+0xbc`, `_ZNK6__asan23StackAddressDescription5PrintEv+0x3d4`, `_ZNK6__asan23StackAddressDescription5PrintEv+0x58`, `_ZNK6__asan24GlobalAddressDescription5PrintEPKc+0x88` |
| C string with non-printable bytes | b'\x1b[1m\x1b[34m\x00' equal through its NUL at 0x1f9aa \| 0x1fc5f | 2: `_ZN6__asan12ErrorGeneric5PrintEv+0xd0`, `_ZN6__asan9Decorator10ShadowByteEh+0x34` |
| C string with non-printable bytes | b'\x1b[1m\x1b[33m\x00' equal through its NUL at 0x20198 \| 0x20455 | 1: `_ZN6__asan9Decorator10ShadowByteEh+0x5c` |
| C string with non-printable bytes | b'\x1b[1m\x1b[36m\x00' equal through its NUL at 0x10903 \| 0x1090b | 1: `_ZN6__asan9Decorator10ShadowByteEh+0x70` |
| empty string | b'\x00' equal through its NUL at 0x13e5f \| 0x13fb2 | 57: `_ZN11__sanitizer10FlagParser21PrintFlagDescriptionsEv+0x70`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x15c`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x1d8`, `_ZN11__sanitizer18ReportDeadlySignalERKNS_13SignalContextEjPFvS2_PKvPNS_18BufferedStackTraceEES4_+0x6c0`, ... |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x103e0 \| 0x103e8 | 1: `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE+0x20c` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10420 \| 0x10428 | 1: `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb+0xdc` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10460 \| 0x10468 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb+0x140` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x104a0 \| 0x104a8 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE21ReleaseFreeMemoryToOSINS_12MemoryMapperIS5_EEEEvPjmmmPT_m+0x128` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x104e0 \| 0x104e8 | 1: `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_+0x190` |
| unnamed table | value table, 64 entries of 1 bytes (stride 1): the 64 bytes its index can reach are equal at 0x10520 \| 0x10528 | 1: `_ZN6__asanL10RZSize2LogEj+0x44` |
| unnamed table | value table, 3 entries of 4 bytes (stride 4): the 12 bytes its index can reach are equal at 0x20990 \| 0x20c7c | 1: `_ZN11__sanitizer8OpenFileEPKcNS_14FileAccessModeEPi+0x60` |
| unnamed table | relative pointer table, 8 entries, each the same symbol+offset or (unnamed) the same C string through its NUL (b'ILL\x00', b'TRAP\x00', b'ABRT\x00', b'BUS\x00', b'FPE\x00', b'UNKNOWN SIGNAL\x00', b'UNKNOWN SIGNAL\x00', b'SEGV\x00') at 0x2099c \| 0x20c88 | 1: `_ZNK11__sanitizer13SignalContext8DescribeEv+0x1c` |
| unnamed table | relative jump table, 47 entries: every entry the same function+offset (6 distinct cases) at 0x20cd0 \| 0x21774 | 1: `_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE8parseCIEERS1_mPNS2_8CIE_InfoE+0x23c` |

## Planted controls (`tables/control.txt`)

Each a FILE copy of R with one 4-byte word changed, compared as U : Pn (the claim's pair with the donor planted); the expected report, and no other row changes against U : R.

| plant | sha256 | expected report | caught |
|---|---|---|---|
| P1(fuzz_identity copy, ___interceptor_strlen+0x48 00090513 -> 00048513) | `67ec8c7bb7018c0b76bae49a00ffdce15dfd007dda637d36def47505ebe00df0` | strictcmp2: `___interceptor_strlen` DIFFERENT; closure_strict2: `___interceptor_strlen` DIFFERENT under both roots, nothing else added | yes |
| P2(fuzz_identity copy, ___interceptor_strlen+0x30 jal _ZN6__asan10AsanInitedEv -> jal __interceptor_trampoline_strnlen, 70c160ef -> f45ff0ef) | `d645ff968e7cae8c5f03ba2a3cfe4dda2385a5f4213fb0e0407a67201c0b7114` | strictcmp2: `___interceptor_strlen` target-differ at +0x30, `names`, `__interceptor_trampoline_strnlen` | yes |
| P3(fuzz_identity copy, memchr+0x18 00100813 -> 00200813) | `22a717d7941cc7378952768546f78461fd12793816012a71328fec66bef633b7` | strictcmp2: `memchr` DIFFERENT | yes |
| P4(fuzz_identity copy, __asan_region_is_poisoned+0x0 fc010113 -> fc810113) | `eea2ff3d49d65162e5b7b475d7a47b4e7974cdb74df1739ea008ad2aa76877ce` | closure_strict2: `__asan_region_is_poisoned` DIFFERENT under both roots, nothing else added | yes |
| P5(fuzz_identity copy, sysconf jump-table entry 1 at 0x21cdc: 000686f0 -> 000686f4) | `e2b24355b37bd967e2ae3d6955cb60385a9fc762a4731cbe43576408c9f69b59` | jtcheck: `sysconf` target differs 1, DIFF +0xdc (settled against R) | yes |

## Files

| file | kind | role |
|---|---|---|
| `scripts/env.example.sh` | config | every variable name the builder reads, without values |
| `scripts/run.sh` | script | the run of record |
| `scripts/mk_evidence_strlen_kit.py` | script | this builder: checks and copies the kit, runs it, measures, writes the tables and this file |
| `tables/twins.txt` | table | drvcmp.py twins: each pin = its unstripped twin |
| `tables/chain.tsv` | table | strictcmp2.py cmp: the eight chain functions, U : R |
| `tables/closure.txt` | table | closure_strict2.py: the closures of `___interceptor_strlen` and `___interceptor_memchr`, U : R |
| `tables/jtcheck.tsv` | table | jtcheck.py: the 11 table members of the earlier record and every reported closure member |
| `tables/members.tsv` | table | every reported closure member: the kit's verdict next to the settled verdict |
| `tables/acceptances.tsv` | table | each target jtcheck leaves unsettled: the kit's verdict, the settled verdict, the measurement |
| `tables/control.txt` | table | the planted copies P1-P5, as U : Pn, under strictcmp2, closure_strict2, jtcheck |

## Not-certified rows settled by measurement

Two of the six not-certified closure rows are settled by scripts/settle2.py (run by scripts/run_settle2.py) on U = fuzz_uci.asan (sha256 56822e263d76) and R = fuzz_identity.asan (sha256 5b0cbe573036): 32 checks, all PASS (tables/settled2.tsv). Control: the same run on a copy of R with the empty string's first byte changed fails exactly the two string checks (tables/settled2-control.tsv).

- `__nl_langinfo_l+0xf8`: SETTLED. The string is empty (NUL) in both images; the code reads that one byte (`lbu` +0x100) and returns the address (`bnez` +0xfc / `beqz` +0x104 -> `ret` +0x118); its returned value has the consumers of the accepted row `__nl_langinfo_l+0x5c`.
- `RegisterCommonFlags+0x1218`: SETTLED. The empty string is stored (+0x1228, +0x1274) into the field +0x18 of two objects whose vtable is __sanitizer::FlagHandlerInclude's (+0x121c, +0x1268). Of that vtable's two methods Parse only writes the field and Format reads it once and passes it to internal_snprintf with the format "%s". [Limit: that no code outside the class reads the field is a property of the class, not measured.]
- `CommonFlags::SetDefaults+0x48`, `InitializeFlags+0x104`, `__lsan::Flags::SetDefaults+0xc`, `__ubsan::Flags::SetDefaults+0x4`: NOT CERTIFIED: reader list of flag fields needed. The claim of this slice is the chain, which does not depend on them.
