# lib/B/AB1w.v code comparison, re-run on the comparison kit cmpkit 4bbd3a74be89

This record re-runs the code comparison of `NOTES.md` ("Code comparison", line 19, and the verdict table, lines 45-65):
the 524 row pairs of `lib/A/AB1w.v` (fuzz_boxreg.asan) and `lib/B/AB1w.v` (fuzz_boxreg.asan-ubsan). That comparison
was a mnemonic + register compare of a disassembly with every immediate masked. Such a compare also masks the
pc-relative fields, so it cannot see a re-pointed target. Here every pair is compared on the comparison kit, and every
target the kit leaves open (its fail-closed classes) is settled by a named measurement. `NOTES.md` is unchanged except
for the SHAPE explanation (lines 51 and 53-58), which now points here.

## Result

| NOTES.md verdict | rows | kit verdict (strictcmp2 `tcmp`, by address) | settled verdict |
|---|---|---|---|
| `SAME` | 186 | `EQUAL`, 0 target differences: 186 | same code |
| `IMM` | 335 | `EQUAL-mod-pcrel`, 0 target differences: 315; `EQUAL-mod-pcrel` with fail-closed target differences: 20 | same code past pc-relative fields (the 20 settled below) |
| `SHAPE` | 3 | `EQUAL-mod-pcrel`, 0 target differences: 2; `EQUAL-mod-pcrel` with 1 fail-closed target difference: 1 | same code past pc-relative fields; **not** a code difference |

All 524 pairs on 4bbd3a74be89: 503 certified by the kit (0 target differences, 0 REAL words, 0 unmeasured words), 21 settled
by a named measurement (23 target differences, every one listed below), 0 real differences, 0 unmeasured. No pair has
a REAL (non-pc-relative) word difference and no pair differs in length.

On the successor kit cmpkit 86da41d3ef68 (section "cmpkit 86da41d3ef68" below) the same pairs carry 55 `lui` values the
kit does not certify by itself (35 `lui-in-section` targets in 21 rows, and 20 values it accepts only by its
fail-open `lui-const (dataflow)` label, in 18 rows). Each is traced by hand and classed under the settlement rules: 53
certified, 2 NOT CERTIFIED: REAL 0 (no real difference is shown; the value is the same number with the same uses in both
images): `InitializeShadowMemory` +0x1b0, `SizeClassAllocator64_PopulateFreeArray` +0xb0. No verdict moves toward a real difference.

**Changed verdict: the three SHAPE rows.** `NOTES.md` said they are "UBSan's own code differences inside otherwise equal
functions". They are not. Each word the disassembler counted as unequal (1, 9 and 1 words) is `addi rd,rs,lo12` in one
image and `addi rd,rs,0` in the other: the low part of a pc-relative address that is 0 in one layout. The disassembler
prints `addi rd,rs,0` as its alias `mv rd,rs`, so the mnemonics differ although the registers are the same. The kit
pairs each of these words with its `auipc` and finds the same target on both sides. `ioctl_table_fill` and
`AsanThread_AsyncSignalSafeLazyInitFakeStack` are `EQUAL-mod-pcrel` with 0 target differences; `asan_InitializeFlags`
is `EQUAL-mod-pcrel` with one fail-closed target (an empty string), settled below.

## Inputs

| image | pin (stripped, released) sha256 | twin with `.symtab` and DWARF (read here) sha256 |
|---|---|---|
| fuzz_boxreg.asan | `eacfa20547ad7dc0d24164010513fcc8af4ba5e557ff3f391a07559e3e34a6df` | `4532568b621d62be2c79a1e2cf52cd1393008542eeb32e465d50b90d68e8f7a3` |
| fuzz_boxreg.asan-ubsan | `7620eb05e0adf5cb5ea350a6fe814d02d6ddb2685ec03477d0d4a85d249b0d85` | `1d548458eac37ae17f9e8dfb06a5dfef3c606ec9e03eca8ef291d5fec9dce495` |

Twin proof (`drvcmp.py twins`, kit member): for both pairs the PT_LOAD layout is equal and the only differing loadable
bytes (25) are in the ELF header [0x10000,0x10040) and `.note.gnu.build-id` [0x102a8,0x102cc).

Row pairs: `lib/A/AB1w.v` (git blob `68d907a2306868af462cff22e74fb9e3b9c467c2`) and `lib/B/AB1w.v` (git blob
`426222576f90821d236a6f486e44aa22f0a0a2f3`) of this tree: 524 rows each, the same names in the same order. A row is
the range [tfib_A_x, tfib_E_x) in each image.

Tools, by sha256 (the measurement scripts are the ones that produced every value in this record):

| tool | sha256 |
|---|---|
| cmpkit 4bbd3a74be89 (sha256 of its `SHA256SUMS`) | `4bbd3a74be8994d014875952efdb79ef6516680988de43e95a3e217194f0ec33` |
| kit member `strictcmp2.py` | `16982e3ef42b8773ae979f587eebc32ad365a4012e874047f194779412d1a57c` |
| kit member `drvcmp.py` | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` |
| kit member `repin_check-4c05cadaeba3.py` | `4c05cadaeba3b2ca013e56c056a39afe0f840d6662c6150ed1394e869d3b4353` |
| kit member `bytecmp-1480ca2faea0.py` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` |
| kit member `jtcheck.py` | `824905e2621161bc7e85cd99db6e724f496e493ee3dae0868d10854b6d8be4c2` |
| kit member `paircl.py` | `e6df5ed4dd8b1a2b934b36b05b345442e5552935e65912c16b221f8e36305d4a` |
| kit member `closure_strict2.py` | `387ac56b542550b4f0b3ead93eeceee2ed7c75248926caaa925301012c6bc999` |
| `rvdis.py`: independent RV64GC decoder over pyelftools 0.33 (not the kit, not capstone) | `dc4e137a1a22b4307d370543b8991b68dd4adc77c1743421e12a950978e3d565` |
| `luitrace.py`: lui value tracer (dataflow over the CFG, both images) | `12eda0ad0e63f06c2e7943eb953f6f4931063d6c90249606f5592fc606baa0d3` |
| `rootcheck.py`: pointer-root check of load / store bases | `3fdb7676cbace31308006e7843317fd55ca039c79ae22203c05b5996d52c30a4` |
| `dwarfcite.py`: DWARF call-site declarations and .debug_line rows of the images | `4c25390bc1b8089dabfbfbceb85b42c5ee06bfd647747890e40553ae20b3159e` |
| `tables.py`: jump / pointer tables entry by entry | `e85f3165d110167566488b96e2aec64a2ed1dcd8f7eb8c15c845a76d4ec97d02` |
| `cstraudit.py`: audit of the kit's C-string and full-data acceptances | `3f5d2f51391cad5ed62b94604429d8d90ccc6450f562e64096e19f131b7c515a` |
| `settle.py`: named measurements of the 23 fail-closed targets | `ec1daa7d89ca40d347a10e50e6c545bdfda526603136d82832172ba8ca522139` |
| `samecode.py`: kit calls by address and by name, plants | `d0d308cef431255b723023a331a255f0050d370850056bd909d1d0a8092a68db` |
| `lui_classes.py`: class and citation of every lui value | `003df38d0948d645ad0fd03ad5d38d02a6fa2a762e8d950decde858a9a22c097` |

## Runtime source of record

The AddressSanitizer runtime in both images comes from the toolchain image
`ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b`.
The image has no `org.opencontainers.image.revision`; its label `oft.asan_static_commit` = `385966a2672b4be07efec847baee1dd5e497b25f` names the source:
the toolchain's private source repository at that commit, whose `toolchain/Dockerfile:518-520` applies
`patches/compiler-rt/0001..0023` with `patch -p1 --fuzz=0` onto llvm-project `87f0227cb60147a26a1eeb4fb06e3b505e9c7261`
(= `llvmorg-20.1.8`; `toolchain/Dockerfile:293-294` pins it and musl `f21a9653`, v1.2.6-20-gf21a9653). The image's
compiler is clang 20.1.8 (`.comment` of both images). `oss-fuzz-theorems-build` `toolchain/asan-rv64g.patch` is not the
source: it was deleted in that repository's `700355c4f36f` and never held the Sealed* code.

In the citations below: **P** `file:line` = the file as the 23-patch series leaves it (the file is changed by the series;
patched line numbers); **U** `file:line` = `llvmorg-20.1.8`, for a file the series does not change (so patched = upstream);
**M** `file:line` = musl `f21a9653` (the two musl patches change only `src/env/__init_tls.c`). Every cited line was read
in a tree rebuilt here from llvm-project `87f0227cb601` plus the 23 patches, applied as the Dockerfile does (23 of 23
applied, no fuzz); the rebuilt tree reproduces the sha256 of the six patched files the source record lists (6 of 6).

Binary confirmations: the images' `.debug_line` has rows in `sanitizer_allocator_primary64.h` at lines 751 (2), 852 (3),
854 (2) and none at 746, 847, 849, and its highest line there is 906: the series adds 5 lines (one insertion at upstream
line 185), so patched 751 / 852 / 854 = upstream 746 / 847 / 849. `SealedReserveShadow` (patched `asan_shadow_setup.cpp:111`,
declared `asan_internal.h:83`) and `SealedRepairReservation` (patched `sanitizer_posix_libcdep.cpp:475`) are not upstream
(patches 0019 and 0022).

| patch | sha256 |
|---|---|
| `0001-static-interception.patch` | `7432e113ed2cfcc8404ba56348b87934f299e21e7402448d9ebe905cd20520b5` |
| `0002-wrap-list.patch` | `63feea6b5c41a5bf8994488aa1630f2d8e2e6885291a56b97d90fc29745f1167` |
| `0003-musl-tls-bounds.patch` | `789ed31c4ae142fe81f0fdf7207be0c00f26d3d533f4029f76698a53392b6c3a` |
| `0004-musl-msghdr-layout.patch` | `52d030134904daba2833988043c66ebbed849d2840c8b1ece1aa73b042bbb754` |
| `0005-musl-interceptor-names.patch` | `1310b6f99a4b55be06d2d4d9833fefeaecfd9a532798d068c99294829808d1a8` |
| `0006-musl-interceptor-gates.patch` | `32849a11ea3e75109ed56f92367c998f9e90800aa95f250dbf16b6bba5b46620` |
| `0007-gethostbyaddr-socklen.patch` | `72a046febac9723d4bc2150946e122fa8bcc68aa82ee10435eff82032d357d6c` |
| `0008-musl-time-types.patch` | `4a86cd1bde3da9a0b7d39976e6a80ab3e7598baa86ab62cdc7588e51a94233cb` |
| `0009-musl-shmid-ds-layout.patch` | `243fb5ed9ec44c186417aca5e985d4181919bbeece9f3d9d68c099cf6986c9c2` |
| `0010-musl-internal-stat.patch` | `c7b83645072ab9d7ee88ba0238eebc372b4b42787f9060187abb6863606ebed1` |
| `0011-musl-mktime-time-t.patch` | `682b371b6432fc8f17d073abf7d1f078b477f38d3d66b9e0d602f9bc12b62654` |
| `0012-sealed-init.patch` | `638f9146e2392b9d8dfdf67c739f5326d8dde77b5a0271d13301d870ffd841ce` |
| `0013-riscv64-mmap-range.patch` | `ffc6cf502a568bd3b049474648c4e3ddc133269b002f65c4183de2486be8e8f5` |
| `0014-silent-reports.patch` | `384ea58a115a4fa803cfe7e6f450ea47ce8369c2b56bc75772134b46dacb8c4f` |
| `0015-sealed-allocation-failure.patch` | `f12239df60ece576a988fdd664d5043e7b5ee03358ffa1f3982110a59f302d0e` |
| `0016-sealed-refusal-sites.patch` | `5e1980d3ea697c913677215787736b6dcc1a9aedc72df2e2566cd4e3ad790ded` |
| `0017-sealed-raw-mmap-returns.patch` | `626f0d22fb4ab74bfffa475fca4a2b9bff3dddcd87a577241983d98bd52c43b6` |
| `0018-trampoline-sections.patch` | `d4c42d900d733026696b56c1c040e0249eb6f8727fef0b2f9966382b10535ec1` |
| `0019-sealed-shadow-first.patch` | `2521085e73e858350b7683a00d87d0df158ecf724d506502d1a40d1eeb0521d9` |
| `0020-sealed-madvise-dontneed.patch` | `1f82b2ae9eaea1ea97f5afececa8c32a2997f16aba8dc2637e4f58a1e961618d` |
| `0021-static-interception-extract-real.patch` | `36c45ccd8fbc508a94007009e839682c9fdb6d84a05d21416afa97068cc0a156` |
| `0022-sealed-commit-refusal-reservation.patch` | `e38fb11d14a67b5c22fc0d5012fa4198add08c8c5e339dbcc515249c46886c32` |
| `0023-sealed-new-throws-bad-alloc.patch` | `d9355ec14008d4a2851977557d6c15413878ae80f33981650a1a52b73e00d8d9` |

## Method

- Every pair by address: the kit's `strictcmp2.tcmp(asan, A_asan, asan-ubsan, A_asan-ubsan, E - A)`, called directly.
  `tcmp` returns the full list of differing targets (no print limit applies to it); N below is its length.
- Every name at the row's address also by name, as `strictcmp2.py cmp` does it (`Img.fsym`, the lowest-address FUNC
  copy of the name), and the copies of every name are counted in both images (all `.symtab` entries of that name).
- Every target difference is settled by the measurement its fail-closed class needs: a string up to and including its
  NUL when its consumer reads only to the NUL; a table entry by entry as function + offset, measured with the
  independent decoder (the guarding bound, the base, the dispatch, every entry on both images); data on the extent the
  code reads; a `.got` value that is a section-bound symbol by its name when every symbol at that address is listed, its
  consumer uses it only as a bound, and the enclosed array is equal.
- Consumers are read with the independent decoder. A consumer scan tracks the values that `auipc` pairs and `.got`
  loads put in registers through straight-line code, and lists every load of the field it finds.

## The three SHAPE rows: every word with a different mnemonic

| row | offset | fuzz_boxreg.asan word | fuzz_boxreg.asan-ubsan word | registers | kit target of the word (both images) |
|---|---|---|---|---|---|
| `asan_InitializeFlags` | +0x84c | `06068693` `addi a3,a3,96` | `00068693` `mv a3,a3` = `addi a3,a3,0` | equal (rd a3, rs a3) | 0x180ac / 0x180ac = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0xa00 | `c2080813` `addi a6,a6,-992` | `00080813` `mv a6,a6` = `addi a6,a6,0` | equal (rd a6, rs a6) | 0x9e878 / 0x9ecb8 = _ZL11ioctl_table+0x0, same |
| `ioctl_table_fill` | +0x1620 | `00080813` `mv a6,a6` = `addi a6,a6,0` | `3e080813` `addi a6,a6,992` | equal (rd a6, rs a6) | 0x9e878 / 0x9ecb8 = _ZL11ioctl_table+0x0, same |
| `ioctl_table_fill` | +0x58b4 | `06078793` `addi a5,a5,96` | `00078793` `mv a5,a5` = `addi a5,a5,0` | equal (rd a5, rs a5) | 0x1bb68 / 0x1bb68 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x6804 | `06058613` `addi a2,a1,96` | `00058613` `mv a2,a1` = `addi a2,a1,0` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x6864 | `00058613` `mv a2,a1` = `addi a2,a1,0` | `fa058613` `addi a2,a1,-96` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x7804 | `06058613` `addi a2,a1,96` | `00058613` `mv a2,a1` = `addi a2,a1,0` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x7864 | `00058613` `mv a2,a1` = `addi a2,a1,0` | `fa058613` `addi a2,a1,-96` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x8804 | `06058613` `addi a2,a1,96` | `00058613` `mv a2,a1` = `addi a2,a1,0` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `ioctl_table_fill` | +0x8864 | `00058613` `mv a2,a1` = `addi a2,a1,0` | `fa058613` `addi a2,a1,-96` | equal (rd a2, rs a1) | 0x1bab8 / 0x1bab8 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |
| `AsanThread_AsyncSignalSafeLazyInitFakeStack` | +0x21c | `06050513` `addi a0,a0,96` | `00050513` `mv a0,a0` = `addi a0,a0,0` | equal (rd a0, rs a0) | 0x1dd90 / 0x1dd90 = unnamed .rodata, accepted as the same C string on both images (`cstr`), same |

The other words of the three functions are equal or differ only in pc-relative fields (kit: 0 REAL, 0 unmeasured).
`(.rodata)` targets are unnamed; the kit accepted them by its C-string rule on both images (`full` or `cstr`).

## The rows the kit does not certify: kit verdict and settled verdict

21 rows, 23 target differences. All are fail-closed kit classes; none is a REAL word.

| row | function | word | kit target kind | kit verdict (by address) | settled verdict |
|---|---|---|---|---|---|
| `asan_InitializeFlags` | `_ZN6__asan15InitializeFlagsEv` | +0x104 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `asan_suppression_kinds_getter_3_insns` | `__asan_default_suppressions` | +0x4 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `CommonFlags_SetDefaults` | `_ZN11__sanitizer11CommonFlags11SetDefaultsEv` | +0x48 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `FlagParser_ParseString_parse_flags` | `_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE` | +0x1218 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `lsan_flags_init_helper` | `_ZN6__lsan5Flags11SetDefaultsEv` | +0xc | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `lsan_ubsan_default_options_weak_stub` | `__lsan_default_options` | +0x4 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `ubsan_MaybeCallUbsanDefaultOptions` | `_ZN7__ubsan5Flags11SetDefaultsEv` | +0x4 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `ubsan_default_options_weak_returns` | `__ubsan_default_options` | +0x4 | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `init_libc` | `__init_libc` | +0xcc | data-differs (unnamed empty string "") | `EQUAL-mod-pcrel` N=1 | equal "" (NUL on both images, consumer reads only to the NUL) |
| `Allocator_Deallocate` | `_ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE` | +0x20c | data-differs (unnamed .rodata table read through a bounded index) | `EQUAL-mod-pcrel` N=1 | equal on the read extent (64 bytes) |
| `Allocator_Allocate` | `_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb` | +0xdc | data-differs (unnamed .rodata table read through a bounded index) | `EQUAL-mod-pcrel` N=1 | equal on the read extent (64 bytes) |
| `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` | `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE18PackedCounterArrayC2INS_12MemoryMapperIS5_EEEEyyPT_` | +0x190 | data-differs (unnamed .rodata table read through a bounded index) | `EQUAL-mod-pcrel` N=1 | equal on the read extent (64 bytes) |
| `RZSize2Log` | `_ZN6__asanL10RZSize2LogEj` | +0x44 | data-differs (unnamed .rodata table read through a bounded index) | `EQUAL-mod-pcrel` N=1 | equal on the read extent (64 bytes) |
| `force_interface_symbols_dead_volatile_switch` | `_ZN6__asanL23force_interface_symbolsEv` | +0x20 | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=1 | every entry the same function + offset (measured below) |
| `GetHandleSignalMode` | `_ZN11__sanitizer19GetHandleSignalModeEi` | +0x24 | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=1 | every entry the same function + offset (measured below) |
| `sysconf` | `sysconf` | +0xdc | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=1 | every entry the same function + offset (measured below) |
| `pop_arg` | `pop_arg` | +0x14 | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=1 | every entry the same function + offset (measured below) |
| `printf_core` | `printf_core` | +0x534 | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=3 | every entry the same function + offset (measured below) |
| `printf_core` | `printf_core` | +0x6ac | data-differs (jump / pointer table) | `EQUAL-mod-pcrel` N=3 | every entry the same function + offset (measured below) |
| `asan_module_ctor` | `asan.module_ctor` | +0x1c | got-value (cell holds a section-end address) | `EQUAL-mod-pcrel` N=1 | name-only equal (__stop_asan_globals), bound only, enclosed array equal |
| `asan_module_dtor` | `asan.module_dtor` | +0x14 | got-value (cell holds a section-end address) | `EQUAL-mod-pcrel` N=1 | name-only equal (__stop_asan_globals), bound only, enclosed array equal |
| `printf_core` | `printf_core` | +0x890 | unmeasured (I/S-type word on an auipc register) | `EQUAL-mod-pcrel` N=3 | the address it forms is the same .rodata place and the same bytes on both images |
| `start` | `_start` | +0x10 | writable-unnamed (both targets address 0) | `EQUAL-mod-pcrel` N=1 | equal value 0 on both images, never read |

### The measurements

**data-differs (unnamed empty string "")**

- `asan_InitializeFlags` +0x104: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi t5 (+0x104), then two stores: sd t5,288(sp) (+0x108), whose only other 288(sp) access is ld a1,288(sp) at +0xc94 -> jal FlagParser::ParseString (+0xc9c); and sd t5,104(s3) (+0x220), s3 = __asan::asan_flags_dont_use_directly (set at +0xe8), so the asan `suppressions` flag (Flags +104); consumer: FlagParser::ParseString: lbu a2,0(s) (+0x5c); byte 0 is no whitespace (mask 0x400100100002600 bit 0 = 0); beqz a2 (+0x88) -> exit (+0xb0) without parse_flag: reads s[0] only; asan::InitializeSuppressions +0x40 ld a1,104(a0) (a0 = the flags object, from its .got cell) -> jal SuppressionContext::ParseFromFile (+0x4c): lbu a1,0(a1) (+0x1c), beqz -> return: reads byte 0 only
- `asan_suppression_kinds_getter_3_insns` +0x4: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; returns a0 = ""; only caller asan::InitializeSuppressions jal at +0x50, mv a1,a0, tail j SuppressionContext::Parse (+0x6c); consumer: SuppressionContext::Parse: lbu str[0] (+0xcc), not 32 / 9; internal_strchr(str,10) (C string) = 0; internal_strlen(str) = 0 -> end == str (+0xfc); lbu end[0] (+0xac) beqz -> exit: reads to the NUL only
- `CommonFlags_SetDefaults` +0x48: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi a4 (+0x48) -> sd a4 to CommonFlags +24 / +200 / +208 = strip_path_prefix / cov_8bit_counters_out / cov_pcs_out (RegisterCommonFlags handlers +0x104 / +0x9a4 / +0x9d8); consumer: readers found (value-tracking scan): strip_path_prefix: ProcessAddressFrames +0xbc / ReportErrorSummary +0xc4 load it into a7, the strip_path_prefix argument of the virtual RenderFrame; StripPathPrefix (callers: FormattedStackTracePrinter::RenderFrame x2, RenderSourceLocation, RenderModuleLocation, RenderData) reads it only through internal_strstr and internal_strlen (C string); cov_8bit_counters_out / cov_pcs_out: no reader found; FlagHandler<const char*>::Format (0x37204): ld *t_, internal_snprintf "%s" (C string)
- `FlagParser_ParseString_parse_flags` +0x1218: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi s2 (+0x1218), then two stores sd s2,24(a2) (+0x1228 and +0x1274): the original_path field of the two FlagHandlerInclude objects, `include` and `include_if_exists`, each from LowLevelAllocator::Allocate(32) (vtable +0, parser +8, ignore_missing +16, path +24); consumer: FlagHandlerInclude::Format (0x62594): ld a3,24(a0) -> internal_snprintf(buf, size, "%s", path) (C string); FlagHandlerInclude::Parse (0x624d8) first does sd a1,24(a0) (overwrites the field, never reads the old value); both objects use these two methods
- `lsan_flags_init_helper` +0xc: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi a3 (+0xc) -> sd a3,32(a0): lsan Flags +32 = suppressions (RegisterLsanFlags handler +0x378); consumer: reader: LeakSuppressionContext::Suppress +0x44 ld a1,96(s5) (= lsan_flags+32) -> SuppressionContext::ParseFromFile: lbu a1,0(a1) (+0x1c), beqz -> return: reads byte 0 only; FlagHandler<const char*>::Format "%s"
- `lsan_ubsan_default_options_weak_stub` +0x4: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; returns a0 = ""; only caller asan::InitializeFlags jal +0xcc8, mv a1,a0 -> jal FlagParser::ParseString +0xcd8; consumer: FlagParser::ParseString (as for InitializeFlags +0x104): reads s[0] only
- `ubsan_MaybeCallUbsanDefaultOptions` +0x4: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi a1 (+0x4) -> sd a1,8(a0): ubsan Flags +8 = suppressions (RegisterUbsanFlags handler +0xc4); consumer: reader: ubsan::InitializeSuppressions +0x40 ld a1,8(a0) -> tail j SuppressionContext::ParseFromFile: lbu a1,0(a1), beqz -> return: byte 0 only; FlagHandler<const char*>::Format "%s"
- `ubsan_default_options_weak_returns` +0x4: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; returns a0 = ""; only caller asan::InitializeFlags jal +0xcb4, mv a1,a0 -> jal FlagParser::ParseString +0xcc4; consumer: FlagParser::ParseString: reads s[0] only
- `init_libc` +0xcc: target asan 0x13e6c / asan-ubsan 0x13e6c (.rodata); byte 0 = 00 / 00 (NUL); the two images agree on 50856 bytes from there; addi s0 (+0xcc) when argv[0] is NULL -> sd s0 to __progname_full and __progname (GOT cells 0x99b50 / 0x99b58 in asan); consumer: in-function scan for "/": lbu a3,-1(a1) from pn[0] (+0xfc), bnez continue -> stops at the NUL; no other reader of __progname / __progname_full found by the value-tracking scan

**data-differs (unnamed .rodata table read through a bounded index)**

- `Allocator_Deallocate` +0x20c: index = (x & -x) * C >> 58 (neg, mul, srli 0x3a at 0x31090, lbu at 0x3109c) is 0..63, so the code reads 64 bytes from the table; table at 0x103e0 in asan and 0x103e0 in asan-ubsan: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C: 0x103b0=0x0218a392cd3d5dbf in asan, 0x103b0=0x0218a392cd3d5dbf in asan-ubsan; the two images agree on 65844 bytes from the table
- `Allocator_Allocate` +0xdc: index = (x & -x) * C >> 58 (neg, mul, srli 0x3a at 0x31274, lbu at 0x31280) is 0..63, so the code reads 64 bytes from the table; table at 0x10420 in asan and 0x10420 in asan-ubsan: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C: 0x103b0=0x0218a392cd3d5dbf in asan, 0x103b0=0x0218a392cd3d5dbf in asan-ubsan; the two images agree on 65780 bytes from the table
- `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` +0x190: index = (x & -x) * C >> 58 (neg, mul, srli 0x3a at 0x348f8, lbu at 0x34900) is 0..63, so the code reads 64 bytes from the table; table at 0x104e0 in asan and 0x104e0 in asan-ubsan: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C: 0x103b0=0x0218a392cd3d5dbf in asan, 0x103b0=0x0218a392cd3d5dbf in asan-ubsan; the two images agree on 65588 bytes from the table
- `RZSize2Log` +0x44: index = (x & -x) * C >> 58 (neg, mul, srli 0x3a at 0x36544, lbu at 0x3654c) is 0..63, so the code reads 64 bytes from the table; table at 0x10520 in asan and 0x10520 in asan-ubsan: the 64 bytes are equal (00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a); multiplier C: 0x103b0=0x0218a392cd3d5dbf in asan, 0x103b0=0x0218a392cd3d5dbf in asan-ubsan; the two images agree on 65524 bytes from the table

**data-differs (jump / pointer table)**

- `force_interface_symbols_dead_volatile_switch` +0x20: relative jump table: `li 51; bltu` bound -> 52 entries, base 0x20840 (.rodata) in both images, `slli 2; add; lw; add; jr`; every entry the same function + offset in both images and on an instruction boundary of _ZN6__asanL23force_interface_symbolsEv
- `GetHandleSignalMode` +0x24: pointer table: `li 7; bltu` and the mask `li 159; srl; andi 1; beqz` before `ld; lw`; 8 entries at 0x98a78 / 0x98e98 (.data.rel.ro); entries 0-4 and 7 the same symbol + offset (common_flags_dont_use+0x58 ... +0x6c) in both images, entries 5 and 6 are 0 in both and never read (bits 5 and 6 of 0x9f are 0)
- `sysconf` +0xdc: relative jump table: `li 12; bltu` bound -> 13 entries, base 0x212f8 (.rodata) in both images, `slli 2; add; lw; add; jr`; every entry the same function + offset in both images and on an instruction boundary of sysconf
- `pop_arg` +0x14: relative jump table: `li 17; bltu` bound -> 18 entries, base 0x22038 (.rodata) in both images, `slli 2; add; lw; add; jr`; every entry the same function + offset in both images and on an instruction boundary of pop_arg
- `printf_core` +0x534: relative jump table: `li 55; bltu` bound -> 56 entries, base 0x21f38 (.rodata) in both images, `slli 2; add; lw; add; jr`; every entry the same function + offset in both images and on an instruction boundary of printf_core. (The kit's jtcheck also lists 10 "C-string acceptances" for printf_core: those are its C-string targets, not table entries.)
- `printf_core` +0x6ac: relative jump table: `li 7; bltu` bound -> 8 entries, base 0x22018 (.rodata) in both images, `slli 2; add; lw; add; jr`; every entry the same function + offset in both images and on an instruction boundary of printf_core. (The kit's jtcheck also lists 10 "C-string acceptances" for printf_core: those are its C-string targets, not table entries.)

**got-value (cell holds a section-end address)**

- `asan_module_ctor` +0x1c: .got cell 0x99b38 holds 0x9d8b0 (asan) and 0x99f58 holds 0x9dcd0 (asan-ubsan); every symbol at that value: __stop_asan_globals (asan), __stop_asan_globals (asan-ubsan), the end of asan_globals (0x9d770+0x140, 0x9db90+0x140); consumer __asan_register_elf_globals: a2 (stop) is used only in beq a1,a2 and sub a2,a2,a1 -> count (a bound); enclosed array asan_globals, 5 entries of 64 bytes, entry by entry equal: yes
- `asan_module_dtor` +0x14: .got cell 0x99b38 holds 0x9d8b0 (asan) and 0x99f58 holds 0x9dcd0 (asan-ubsan); every symbol at that value: __stop_asan_globals (asan), __stop_asan_globals (asan-ubsan), the end of asan_globals (0x9d770+0x140, 0x9db90+0x140); consumer __asan_unregister_elf_globals: a2 (stop) is used only in beq a1,a2 and sub a2,a2,a1 -> count (a bound); enclosed array asan_globals, 5 entries of 64 bytes, entry by entry equal: yes

**unmeasured (I/S-type word on an auipc register)**

- `printf_core` +0x890: word 00158893 (addi a7,a1,1) on both images; CFG with every table target as a successor of every jr; the value of a1 there, through its definition chain: asan 0x8f118 addi a1,a1,-1468 <- [0x8f110 auipc] / asan-ubsan 0x8f53c addi a1,a1,1568 <- [0x8f534 auipc]; a1 = 0x10b54/0x10b54 ((.rodata)/(.rodata)) -> the word forms a7 = 0x10b55/0x10b55, C string b'+   0X0x\x00'/b'+   0X0x\x00'; the two images agree on 63935 bytes from there

**writable-unnamed (both targets address 0)**

- `start` +0x10: auipc a1 / addi a1 at +0xc / +0x10 form 0x0 (asan) and 0x0 (asan-ubsan), address 0 (`.symtab` holds an undefined `_DYNAMIC`: _DYNAMIC STB_LOCAL); a1 is then dead: _start ends `j _start_c`, and _start_c +0 is `lw a1,0(a0)` (asan) / `lw a1,0(a0)` (asan-ubsan), which overwrites a1 before any read

### Names with more than one copy

| row | name | copies (asan / asan-ubsan) | by address | by name (`fsym`: lowest-address copy) |
|---|---|---|---|---|
| `MemToShadow_3c6cc` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | EQUAL-mod-pcrel N=0 (A 0x3c6cc B 0x3c72c) | 0x3ae64 0x3aec4 EQUAL-mod-pcrel N=0 |
| `MemToShadow_CHECK_AddrIsInMem_instance` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | EQUAL-mod-pcrel N=0 (A 0x52140 B 0x521a0) | 0x3ae64 0x3aec4 EQUAL-mod-pcrel N=0 |
| `MemToShadow_checked` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | EQUAL-mod-pcrel N=0 (A 0x53788 B 0x537e8) | 0x3ae64 0x3aec4 EQUAL-mod-pcrel N=0 |
| `MemToShadow_checked_instance_3` | `_ZN6__asanL11MemToShadowEm` | 5 / 5 | EQUAL-mod-pcrel N=0 (A 0x5c674 B 0x5c6d4) | 0x3ae64 0x3aec4 EQUAL-mod-pcrel N=0 |
| `init` | `dummy` | 5 / 5 | EQUAL N=0 (A 0x87f4c B 0x88370) | 0x87f4c 0x88370 EQUAL N=0 |
| `fini` | `dummy` | 5 / 5 | EQUAL N=0 (A 0x8891c B 0x88d40) | 0x87f4c 0x88370 EQUAL N=0 |
| `aio_close_stub_j_ret_used_by_close_stdio_close` | `dummy` | 5 / 5 | EQUAL N=0 (A 0x8dd2c B 0x8e150) | 0x87f4c 0x88370 EQUAL N=0 |
| `testcancel` | `dummy` | 5 / 5 | EQUAL N=0 (A 0x94808 B 0x94c2c) | 0x87f4c 0x88370 EQUAL N=0 |

For the MemToShadow rows the by-name compare compares copy 1 with copy 1, not the row's copy, so the by-address verdict
is the one that covers the row; both are equal. Control P3 below shows that the by-name compare cannot see a change in
the row's copy.

## Controls

Plants are file copies of fuzz_boxreg.asan-ubsan with one instruction word changed; each is compared with
fuzz_boxreg.asan the same way as the pairs above, and its unplanted baseline is compared too.

| plant | change | planted result | baseline |
|---|---|---|---|
| Pab1wB-ioctl-lo12 | ioctl_table_fill asan-ubsan 0x48cbc word 00080813 -> 00880813 (addi a6,a6,0 -> addi a6,a6,8) | CAUGHT: N=1 [('0xa00', '_ZL11ioctl_table+0x0', '_ZL11ioctl_table+0x8', 'names', None)] | CLEAN (N=0) |
| Pab1wB-rge-jal | ReportGenericError asan-ubsan 0x5780c jal 0x789f4 (_ZN11__sanitizer21ScopedErrorReportLock4LockEv+0x0) -> 0x78af0 (_ZN11__sanitizer21ScopedErrorReportLock6UnlockEv+0x0) | CAUGHT: N=1 [('0x65c', '_ZN11__sanitizer21ScopedErrorReportLock4LockEv+0x0', '_ZN11__sanitizer21ScopedErrorReportLock6UnlockEv+0x0', 'names', None)] | CLEAN (N=0) |
| Pab1wB-m2s3-jal | MemToShadow copy 3/5 asan-ubsan 0x522d8 jal 0x6b18c (_ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0) -> 0x6b244 (_ZN11__sanitizer16BackgroundThreadEPv+0x0); copies of the name: asan 5, asan-ubsan 5 | CAUGHT: by address N=1 [('0x138', '_ZN11__sanitizer11CheckFailedEPKciS1_yy+0x0', '_ZN11__sanitizer16BackgroundThreadEPv+0x0', 'names', None)]; by name (copy 1 vs copy 1) N=0: the by-name compare does not see the plant | CLEAN (N=0) |

## Limits measured

- 4bbd3a74be89 compares a `lui`-built absolute address as a raw word. In the 524 pairs (both images, independent
  decoder) there are 920 `lui` words and none of their values is used directly as a load, store or `jalr` base; the
  kit's luiscan agrees (memory-fed 0, next section), and 86da41d3ef68, which compares them, is run below.
- C-string and data acceptances (cmpkit 86da41d3ef68 README, OPEN KNOWN LIMIT 6). `.rodata` has the same range in
  both images and is byte-identical except 1500 bytes in 909 runs inside the windows [[0x20514, 0x2066d), [0x20690, 0x2090d), [0x209f0, 0x20be9), [0x20c00, 0x20c2e), [0x20d94, 0x2132a), [0x21f38, 0x2207e), [0x22534, 0x2268a)] (the jump-table
  area). Over the 524 pairs strictcmp3 accepts 2057 targets by its C-string rule and 124 by full-data compare; every
  one (2181 of 2181) is at the same address in both images and byte-identical through the accepted NUL (or the full
  extent), 0 lie inside or touch a differing window, and the two images agree for at least 16 bytes from every
  accepted address. One acceptance is right for another reason: sysconf +0x214 is `lui a0,0x20` (0x20000, the
  returned ARG_MAX 131072 in both images), which the kit accepts as the C string "S" at .rodata 0x20000.

## cmpkit 86da41d3ef68: exposure scans and re-run

cmpkit 86da41d3ef68 supersedes 4bbd3a74be89. It adds rule 8 (a `lui`-built absolute value is a target), refuses a
function name that several copies carry, and prints a combined verdict. Its README tells a record made on 4bbd3a74be89
to run two exposure scans. Both scans were run on this re-run. They expose rows, so every pair was also re-run on
86da41d3ef68. The 4bbd3a74be89 verdicts above stay as they were measured; the 86da41d3ef68 verdicts are given beside
them in the appendix.

| tool | sha256 |
|---|---|
| cmpkit 86da41d3ef68 (sha256 of its `SHA256SUMS`) | `86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60` |
| kit member `strictcmp3.py` | `65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7` |
| kit member `jtcheck.py` | `8b0ea3862423e3941fd9d70ccc9bcb89cfd89b824fa348140e168880c9745fb7` |
| kit member `luiscan.py` | `9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad` |
| kit member `ambiscan.py` | `9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d` |
| kit member `drvcmp.py` | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` |
| kit member `bytecmp-1480ca2faea0.py` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` |
| kit member `repin_check.py` | `e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66` |
| kit member `paircl.py` | `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1` |
| kit member `closure_strict3.py` | `a98d2b3e88574d09d4aee478ba4fed060a3c1577e2229f47affb116c3ccded4e` |

Commands (the kit directory; `A` = fuzz_boxreg.asan twin, `B` = fuzz_boxreg.asan-ubsan twin; the item lists are the 524
row starts of each image plus `_start_c`, because `_start` is a size-0 symbol):

```
python3 luiscan.py --all --fns <row starts in A> A
python3 luiscan.py --all --fns <row starts in B> B
python3 ambiscan.py A B <the by-name compares of this re-run, one cmp-format row each> <the jtcheck output above>
```

- luiscan, each image: functions 629, with a `lui` 152, with exposure > 0 24; `lui` words 485, in-section values 60,
  memory-fed 0, memory-fed outside every section 0, dataflow constants 20, unmeasured 0, exposure 40 (the same
  numbers in both images: yes). Exposed functions: `_ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_`, `_ZN11__sanitizer10StackStore5AllocEmPmS1_`, `_ZN11__sanitizer13StackDepotGetEj`, `_ZN11__sanitizer14StackDepotBaseINS_14StackDepotNodeELi1ELi20EE3PutENS_10StackTraceEPb`, `_ZN11__sanitizer15internal_usleepEy`, `_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator32INS_4AP32EEENS_32LargeMmapAllocatorPtrArrayStaticEE8AllocateEPNS_30SizeClassAllocator32LocalCacheIS3_EEmm`, `_ZN11__sanitizer17GetNamedMappingFdEPKcmPi`, `_ZN11__sanitizer18LargeMmapAllocatorIN6__asan20AsanMapUnmapCallbackENS_33LargeMmapAllocatorPtrArrayDynamicENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`, `_ZN11__sanitizer18LargeMmapAllocatorINS_20NoOpMapUnmapCallbackENS_32LargeMmapAllocatorPtrArrayStaticENS_21LocalAddressSpaceViewEE8AllocateEPNS_14AllocatorStatsEmm`, `_ZN11__sanitizer18internal_allocatorEv`, `_ZN11__sanitizer19ReadLongProcessNameEPcm`, `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm`, `_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE20EnsureFreeArraySpaceEPNS5_10RegionInfoEmm`, `_ZN11__sanitizerL23SealedRepairReservationEmm`, `_ZN6__asan14AsanDeactivateEv`, `_ZN6__asan19SealedReserveShadowEv`, `_ZN6__asan22InitializeShadowMemoryEv`, `_ZN6__asan26InitializeAsanInterceptorsEv`, `_ZNK11__sanitizer11TwoLevelMapINS_14StackDepotNodeELy32768ELy65536ENS_21LocalAddressSpaceViewEE6CreateEm`, `__init_tls`, `fmt_fp`, `printf_core`, `static_init_tls`, `sysconf`.
- luiscan prints `ABSENT` for 2 items, the two size-0 symbols among the row starts: `_start` (0x2ff58, whose body the item
  `_start_c` covers) and `__set_thread_area` (0x9480c / 0x94c30). `__set_thread_area` is 3 words, `mv tp,a0; li a0,0; ret`, with
  no `lui`; its pair is `EQUAL` on 86da41d3ef68.
- ambiscan: by-name compares seen (distinct names) 622, ambiguous hits 16, distinct ambiguous names 2: `_ZN6__asanL11MemToShadowEm` (8 hits), `dummy` (8 hits). These are the by-name compares of the 8 rows
  listed in "Names with more than one copy"; their verdicts of record are by address.
- Re-run of all 524 pairs on 86da41d3ef68 (`strictcmp3.tcmp` by address, full target list, combined verdict):
  `EQUAL` 186, `EQUAL-mod-pcrel` 297, `DIFFERENT-target` 41. The `DIFFERENT-target` rows are: the same 21 rows and 23
  targets as on 4bbd3a74be89, settled above (86da41d3ef68's `jtcheck.py` gives the same table acceptances), and 35
  `lui-in-section` targets in 21 rows (OPEN LIMIT 1 of the kit README). No REAL word, no memory-fed `lui` value, no new
  target of any other kind. strictcmp3 also accepts 20 `lui` values in 18 rows by its `lui-const (dataflow)` label, which
  is fail-open when a value passes logical ops before it forms an address (a kit limit registered at commit `797c750bbb0`), so
  those values are traced too. The next section settles all 55 values.
- The 8 rows with a duplicated name, by qualified name on 86da41d3ef68 (`strictcmp3.py cmp` with `NAME{FILE}`, the
  form the kit asks for): the 4 MemToShadow copies (asan_fake_stack.cpp, asan_linux.cpp, asan_poisoning.cpp,
  asan_thread.cpp) are `EQUAL-mod-pcrel` with 0 target differences, at the row addresses; `_init`, `_fini`,
  `__aio_close` and `__testcancel` are `EQUAL`. The bare name `_ZN6__asanL11MemToShadowEm` is refused (5 copies).
- Controls on 86da41d3ef68: the three plants above are `DIFFERENT-target` (N=1, the planted word); their baselines are
  `EQUAL-mod-pcrel`.

## The 55 lui values: trace, class and citation

Ops the tracer follows (luitrace.py): every RV64GC integer instruction the decoder knows (lui, auipc, li, mv, addi(w), add(w), sub(w), sh1add, sh2add, sh3add, and, or, xor, andi, ori, xori, sll(i)(w), srl(i)(w), sra(i)(w), mul(w), mulh*, div(u)(w), rem(u)(w), slt(i)(u), seqz, snez, sign / zero extension, the Zbb ops), loads and stores (a stack slot at a known sp offset carries the value to its reload), and the A-extension lr / sc / amo* as bases and as data, from the value's word to each register's or slot's next write, over every path of the function's control-flow graph.

The tracer starts at the word the kit names and records, for that value, every use and whether the value enters it
linearly (through addi / add / sub / sh*add as the added operand / mv, or folded exactly) or non-linearly (through any
other op with a runtime operand). A use at a load / store / amo / jump base names the base: an auipc address (compared
as symbol + offset in both images), an incoming register, a load, or the stack. A register live at a call is matched
to the callee's parameter list (from its mangled name and the declaration the image's DWARF call site names); a
register beyond the list is not passed. Each value has the same number and the same uses in both images (55 of 55).

Settlement rules applied (the classes, as ruled): (i) a call argument whose parameter the source contract states is a
byte count / length / count / size / flags / mode / prot / alignment (an address parameter never settles); (ii) a
returned integer that is not an address; (iii) an offset added to an object pointer that comes from a load, an argument
or an allocator return, or, when the base is an auipc address, the absolute address compared by symbol + offset in both
images; store: into an integer, non-address field; (c) CheckFailed v1 / v2, when CheckFailed formats them only with a
numeric conversion and uses them nowhere else on any path;
(d) a value whose every use on every path up to its next write is a branch / compare operand; (e) a frame base: the
base's only pointer root is sp on every path; integer constants added to it, including a lui-built frame offset, are
offsets, not pointers; no auipc / lui / section-built pointer (a value naming a static address) appears anywhere in the
base chain. Anything else: NOT CERTIFIED: REAL 0.

Counts (values): (c) 1, (d) 20, (e)+(ii)+(i) 1, (i) 9, (i)+(store)+(c) 1, (ii) 2, (iii) 14, (store) 4, (store)+(c) 1, NOT CERTIFIED 2; total 53 certified, 2 NOT CERTIFIED: REAL 0, of 55. By kind: `lui-in-section` 33 certified of 35;
`lui-const (dataflow)` 20 certified of 20. Rows: 37 rows carry these values; 2 are NOT CERTIFIED: REAL 0 (`InitializeShadowMemory`, `SizeClassAllocator64_PopulateFreeArray`), the
others are certified.

**NOT CERTIFIED: REAL 0** (no real difference is shown; not settled under the rules):

- `InitializeShadowMemory` +0x1b0: an address parameter (`uptr zero_base_max_shadow_start`) never settles
- `SizeClassAllocator64_PopulateFreeArray` +0xb0: the value enters the store base at +0x1d0 non-linearly (its CheckFailed `v1` use alone would settle by (c))

| row | word | value (both images) | kind | class | what it is | binary evidence | source of record |
|---|---|---|---|---|---|---|---|
| `Quarantine_Recycle` | +0x74 | 0x190000 | lui-in-section | CERTIFIED (d) compare only | every use on every path is a compare operand (ruling (d)) | binary: the only use is `mul a4,a6,a4` (+0x7c); the product's only use is `bgeu a5,a4` (+0x84); a4 is live at `jal MergeBatches` (+0xa4) but MergeBatches takes this, from (a0, a1: `MergeBatchesEPS3_`), so it is not passed; next write of a4 ends the chain | U sanitizer_quarantine.h:163-166 (`overhead_size * (100 + kOverheadThresholdPercents) > cache_size * kOverheadThresholdPercents`) |
| `SizeClassAllocator64_EnsureFreeArraySpace` | +0x2c | 0x3ffff | lui-in-section | CERTIFIED (i) call argument + CERTIFIED (store) + CERTIFIED (c) CheckFailed v1 / v2 | Map `size` and PoisonShadow `size` (uptr, used only as lengths, ruling (b)), stores into `uptr mmaped` and `uptr mapped_free_array`, CheckFailed v1 (ruling (c)) | binary: a2 of `jal ReservedAddressRange::Map` (+0x9c; `MapEmmPKc`, 3rd incl. this = unsigned long), a1 of `jal PoisonShadow` (+0xb8; DWARF asan_poisoning.h:27), `sd` at +0xd4 (.debug_line asan_allocator.cpp:296) and +0xdc (.debug_line sanitizer_allocator_primary64.h:758), a3 of `jal CheckFailed` (+0x120; DWARF sanitizer_common.h:333). binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | P sanitizer_allocator_primary64.h:750-751 `RoundUpTo(needed_space, kFreeArrayMapSize)`, `CHECK_LE(new_mapped_free_array, kFreeArraySize)` (llvmorg-20.1.8: 745-746), :758, :679 `uptr mapped_free_array`; P sanitizer_posix_libcdep.cpp:492-499 (Map: size goes only to MmapFixedOrDieOnFatalError(fixed_addr, size, name) and SealedRepairReservation(fixed_addr, size)); P asan_poisoning.cpp:37-51 (size only in addr + size bounds and FastPoisonShadow(addr, size, value)); P asan_allocator.cpp:296 `thread_stats.mmaped += size`, U asan_stats.h:37 `uptr mmaped` |
| `LargeMmapAllocator_Allocate` | +0x430 | 0x100000 | lui-in-section | CERTIFIED (c) CheckFailed v1 / v2 | CheckFailed v2 = kMaxNumChunks (ruling (c)) | binary: a4 of `jal CheckFailed` (+0x434; DWARF sanitizer_common.h:333); .debug_line at the word: sanitizer_allocator_secondary.h:42. binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | U sanitizer_allocator_secondary.h:42 `CHECK_LT(n, kMaxNumChunks)` |
| `SizeClassAllocator64_PopulateFreeArray` | +0xb0 | 0x40000 | lui-in-section | NOT CERTIFIED: REAL 0 | the value enters the store base at +0x1d0 non-linearly (its CheckFailed `v1` use alone would settle by (c)) | binary: store base at +0x1d0 (.debug_line sanitizer_allocator_primary64.h:843) takes the value through non-linear ops; CheckFailed a3 = v1 (+0x2ac); .debug_line at the word: sanitizer_common.h:471 (RoundUpTo) | P sanitizer_allocator_primary64.h:843, :852 (llvmorg-20.1.8: 838, 847); U sanitizer_common.h:471 |
| `AsanDeactivate_activation_CHECK_helper` | +0x8c | 0x100010 | lui-in-section | CERTIFIED (store) | store into integer fields u16 min_redzone, u16 max_redzone of a local AllocatorOptions | binary: `sw a0,8(sp)` (+0x90) of 0x00100010 = two u16 values 16; .debug_line +0x90: asan_activation.cpp:115; then `mv a0,sp; jal ReInitializeAllocator` (+0x98/+0x9c; `ReInitializeAllocatorERKNS_16AllocatorOptionsE`, a const reference; DWARF call site asan_allocator.h:48) | U asan_allocator.h:34-38 (`u32 quarantine_size_mb; u32 thread_local_quarantine_size_kb; u16 min_redzone; u16 max_redzone;` -> +8, +10); U asan_activation.cpp:115-116, :119 |
| `InitializeAsanInterceptors` | +0x44 | 0x38db28 | lui-in-section | CERTIFIED (i) call argument | MmapOrDie `size` (uptr), used only as a length (ruling (b)) | binary: a0 of `jal MmapOrDie` (+0x4c; `MmapOrDieEmPKcb`, 1st = unsigned long; DWARF call site sanitizer_common.h:90); .debug_line at the word: sanitizer_addrhashmap.h:200 | U sanitizer_common.h:90 `void *MmapOrDie(uptr size, const char *mem_type, bool raw_report = false)`; P sanitizer_posix.cpp:48-56 (size only in RoundUpTo, MmapNamed(nullptr, size, ...), ReportMmapFailureAndDie(size, ...), IncreaseTotalMmap(size)); U sanitizer_addrhashmap.h:200 `MmapOrDie(kSize * sizeof(table_[0]), "AddrHashMap")` |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | +0x74 | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int) | binary: a3 of `jal internal_mmap` (+0x88; `internal_mmapEPvmiiiy`, 4th = int; DWARF call site sanitizer_posix.h:40); .debug_line at the word: asan_shadow_setup.cpp:70 | U sanitizer_posix.h:40-41 `uptr internal_mmap(void *addr, uptr length, int prot, int flags, int fd, u64 offset)`; P asan_shadow_setup.cpp:68-72 (SealedReserveRange, patch 0019, not upstream) `MAP_PRIVATE \| MAP_ANONYMOUS \| MAP_NORESERVE \| MAP_FIXED_NOREPLACE` = 0x104022 |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | +0xfc | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int), two calls | binary: a3 of `jal internal_mmap` (+0x118, +0x164; DWARF call site sanitizer_posix.h:40); .debug_line at the word: asan_shadow_setup.cpp:69 | U sanitizer_posix.h:40-41; P asan_shadow_setup.cpp:68-72 (patch 0019) |
| `InitializeShadowMemory` | +0x1b0 | 0x40000 | lui-in-section | NOT CERTIFIED: REAL 0 | an address parameter (`uptr zero_base_max_shadow_start`) never settles | binary: a3 of `jal ProtectGap` (+0x1c0; `ProtectGapEmmmm`, 4th = unsigned long; DWARF call site sanitizer_common.h:160); .debug_line at the word: asan_shadow_setup.cpp:49 | U sanitizer_common.h:160-161 `void ProtectGap(uptr addr, uptr size, uptr zero_base_shadow_start, uptr zero_base_max_shadow_start)`; P asan_shadow_setup.cpp:49-50 (`kZeroBaseMaxShadowStart`) |
| `internal_allocator` | +0x88 | 0x81008 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x81008 | binary: a0 of `jal __sanitizer_internal_memset` (+0x98; DWARF call site sanitizer_libc.h:35) = auipc base + the value: internal_alloc_placeholder+0x81008 in both images | P sanitizer_allocator.cpp:29 `static char internal_alloc_placeholder[sizeof(InternalAllocator)]`, :36-47 |
| `internal_allocator` | +0xa4 | 0x40000 | lui-in-section | CERTIFIED (i) call argument | memset `n` (uptr): a byte count (ruling (a)) | binary: a2 of `jal __sanitizer_internal_memset` (+0xb0; DWARF call site sanitizer_libc.h:35); .debug_line at the word: sanitizer_libc.h:52 | U sanitizer_libc.h:35-36 `void *__sanitizer_internal_memset(void *s, int c, uptr n)`, :51 `internal_memset(void *s, int c, uptr n)`; contract: M include/string.h:29 `void *memset (void *, int, size_t);` (C memset: n is the byte count) |
| `internal_allocator` | +0xb4 | 0x40040 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x40040 | binary: a0 of `jal __sanitizer_internal_memset` (+0xc8) = internal_alloc_placeholder+0x40040 in both images | P sanitizer_allocator.cpp:29 |
| `internal_allocator` | +0xcc | 0x41000 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s`, two store bases and one stored address, all internal_alloc_placeholder + an offset | binary: memset a0 (+0xe0) = placeholder+0x40dc0; `sd` bases (+0x10c, +0x110; .debug_line sanitizer_allocator_secondary.h:76-77) = placeholder+0x40dc0, +0x40dc8; stored datum (+0x110) = placeholder+0x40dd0; the same in both images. a1 at `ret` (+0x144) is not a return value: internal_allocator returns one pointer, in a0 | P sanitizer_allocator.cpp:29, :36 `InternalAllocator *internal_allocator()`; U sanitizer_allocator_secondary.h:75-77 |
| `internal_allocator` | +0xd0 | 0x40dc0 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | memset `s` = internal_alloc_placeholder+0x40dc0 | binary: a0 of `jal __sanitizer_internal_memset` (+0xe0) = placeholder+0x40dc0 in both images | P sanitizer_allocator.cpp:29 |
| `internal_allocator` | +0xd8 | 0x40248 | lui-in-section | CERTIFIED (i) call argument | memset `n` (uptr): a byte count (ruling (a)) | binary: a2 of `jal __sanitizer_internal_memset` (+0xe0; DWARF call site sanitizer_libc.h:35); .debug_line at the word: sanitizer_libc.h:52 | U sanitizer_libc.h:35-36 `void *__sanitizer_internal_memset(void *s, int c, uptr n)`, :51 `internal_memset(void *s, int c, uptr n)`; contract: M include/string.h:29 `void *memset (void *, int, size_t);` (C memset: n is the byte count) |
| `internal_allocator` | +0x100 | 0x40dd0 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | stored datum internal_alloc_placeholder+0x40dd0 | binary: stored by `sd a2,-568(a1)` (+0x110) at placeholder+0x40dc8 (.debug_line sanitizer_allocator_secondary.h:77); the same in both images | P sanitizer_allocator.cpp:29; U sanitizer_allocator_secondary.h:77 `chunks_ = reinterpret_cast<Header**>(ptr_array_.Init())` |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0xa8 | 0x40dc0 | lui-in-section | CERTIFIED (iii) offset from an argument base | `this` of LargeMmapAllocator::Allocate = incoming a0 (CombinedAllocator `this`, an argument) + 0x40dc0 = &secondary_ | binary: a0 of `jal ...LargeMmapAllocator...8AllocateEPNS_14AllocatorStatsEmm` (+0xc0) = incoming a0 + 0x40dc0 in both images; a4 is live but not a parameter | U sanitizer_allocator_combined.h:71 `secondary_.Allocate(&stats_, original_size, alignment)`, :196-198; U sanitizer_allocator_secondary.h:85 |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0xac | 0x81008 | lui-in-section | CERTIFIED (iii) offset from an argument base | `AllocatorStats *stat` = incoming a0 + 0x81008 = &stats_ | binary: a1 of the same call (+0xc0; 2nd parameter `PNS_14AllocatorStatsE`) = incoming a0 + 0x81008 in both images; a5 is live but not a parameter | U sanitizer_allocator_combined.h:71, :198; U sanitizer_allocator_secondary.h:85 `void *Allocate(AllocatorStats *stat, const uptr size, uptr alignment)` |
| `InternalAllocator_LargeMmapAllocator_Allocate` | +0x118 | 0x40010 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offsets from `this` (incoming a0): +0x40010 (n_chunks_, chunks_sorted_, stats.*), +0x40240 (mutex_) | binary: 13 load / store bases = incoming a0 + 0x40010 (.debug_line sanitizer_allocator_secondary.h:119-127), `lr.w.aq` / `sc.w` bases (+0x12c, +0x140) and a0 of `jal StaticSpinMutex::LockSlow` (+0x390) = incoming a0 + 0x40240, in both images | U sanitizer_allocator_secondary.h:313-321 (page_size_, chunks_, n_chunks_, chunks_sorted_, struct Stats, mutex_), :118-127 |
| `InternalAllocator_LargeMmapAllocator_Allocate` | +0x24c | 0x40000 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offset +0x40000 from `this` + a runtime index: stats.by_size_log[size_log] | binary: `ld` / `sd` bases (+0x258, +0x268; .debug_line sanitizer_allocator_secondary.h:127) = incoming a0 + index + 0x40000 in both images | U sanitizer_allocator_secondary.h:127 `stats.by_size_log[size_log]++`, :319 |
| `internal_usleep_internal_sleep_nanosleep` | +0x14 | 0xf4240 | lui-in-section | CERTIFIED (store) | store into the integer field `long tv_nsec` of a local timespec | binary: `sd a0,8(sp)` (+0x38; .debug_line sanitizer_linux.cpp:641) of (us - q*1000000)*1000; then a0 = a1 = sp, a7 = 101 (nanosleep), `ecall` | P sanitizer_linux.cpp:638-642 `ts.tv_nsec = (useconds % 1000000) * 1000`; M include/alltypes.h.in:44 `struct timespec { time_t tv_sec; ...; long tv_nsec; ... }` |
| `ReadLongProcessName_proc_self_cmdline` | +0x40 | 0x100000 | lui-in-section | CERTIFIED (i) call argument | ReadFileToBuffer `max_len` (uptr), used only as a length (ruling (b)) | binary: a4 of `jal ReadFileToBuffer` (+0x48; `ReadFileToBufferEPKcPPcPmS4_mPi`, 5th = unsigned long; DWARF call site sanitizer_common.h:781); .debug_line at the word: sanitizer_linux.cpp:1397 | U sanitizer_common.h:781-783 `bool ReadFileToBuffer(const char *file_name, char **buff, uptr *buff_size, uptr *read_len, uptr max_len = ..., error_t *errno_p = nullptr)`; P sanitizer_file.cpp:140, :143, :146, :167 (max_len only in `!max_len`, `Min(PageSize, max_len)`, `Min(size * 2, max_len)`, `*read_len == max_len`); P sanitizer_linux.cpp:1397-1398 (`1024 * 1024`) |
| `GetNamedMappingFd_MmapNamed` | +0x90 | 0x80242 | lui-in-section | CERTIFIED (i) call argument | internal_open `flags` (int) | binary: a1 of `jal internal_open` (+0x98; `internal_openEPKcij`, 2nd = int; DWARF call site sanitizer_posix.h:30); .debug_line at the word: sanitizer_posix.cpp:397 | U sanitizer_posix.h:30 `uptr internal_open(const char *filename, int flags, u32 mode)`; P sanitizer_posix.cpp:397 `O_RDWR \| O_CREAT \| O_TRUNC \| o_cloexec` = 0x2 \| 0x40 \| 0x200 \| 0x80000 = 0x80242 |
| `SealedRepairReservation` | +0x78 | 0x104022 | lui-in-section | CERTIFIED (i) call argument | internal_mmap `flags` (int) | binary: a3 of `jal internal_mmap` (+0x90; DWARF call site sanitizer_posix.h:40) | U sanitizer_posix.h:40-41; P sanitizer_posix_libcdep.cpp:475-484 (SealedRepairReservation, patch 0022, not upstream) `MAP_PRIVATE \| MAP_ANON \| MAP_NORESERVE \| MAP_FIXED_NOREPLACE` |
| `StackStore_Alloc` | +0x78 | 0x100000 | lui-in-section | CERTIFIED (store) + CERTIFIED (c) CheckFailed v1 / v2 | amo add into `atomic_uint32_t stored_`, `*pack` (uptr), and CheckFailed v2 = kBlockSizeFrames (ruling (c)) | binary: `amoadd.w.rl` data (+0x9c, +0xd0) and `sd` into *pack (+0xcc, +0xf0) as for +0x84; a4 of `jal CheckFailed` (+0x130; DWARF call site sanitizer_common.h:333) = 0x100000 = v2. binary: CheckFailed (0x6b12c asan / 0x6b18c asan-ubsan) moves v1 (a3) to s2 and v2 (a4) to s1; on every path the only other reads of s2 / s1 are `mv a5,s2` and `mv a6,s1` for `jal Printf`, whose format at .rodata 0x1a204 (same bytes in both images) is "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a5 / a6 are the two numeric conversions "(0x%zx, 0x%zx)"; the paths after Printf (lr / sc on first_tid, the callback, Die, SleepForSeconds, the trap) do not read s2 / s1. P sanitizer_termination.cpp:71-76 (the toolchain's private source repository at the commit of record: `(uptr)v1, (uptr)v2` passed only to that Printf), :77-91 | U sanitizer_stack_store.cpp:91 `CHECK_LE(count, kBlockSizeFrames)`, :92-96, :374-376; U sanitizer_stack_store.h:21 `kBlockSizeFrames = 0x100000`, :91 |
| `StackStore_Alloc` | +0x84 | 0xfffff | lui-in-section | CERTIFIED (store) | stores into integers: amo add into `atomic_uint32_t stored_`, and `*pack` (uptr) | binary: `amoadd.w.rl` data (+0x9c, +0xd0; .debug_line sanitizer_atomic_clang.h:58, inside Stored()) into blocks_[i] + 8; `sd` into *pack (+0xcc, +0xf0; .debug_line sanitizer_stack_store.cpp:95-96; pack = 3rd parameter of `AllocEmPmS1_`, unsigned long*); a7 at `jal BlockInfo::Create` is not a parameter | U sanitizer_stack_store.h:88-91 (`atomic_uintptr_t data_; ...; atomic_uint32_t stored_;`), :76; U sanitizer_stack_store.cpp:92-96, :374-376 |
| `StackDepotBase_Put` | +0x104 | 0x400010 | lui-in-section | CERTIFIED (iii) offset from an argument base | member offset +0x400010 (nodes.map1_) from `this` (incoming a0) + a runtime index | binary: `ld` bases (+0x134, +0x1e0; .debug_line sanitizer_atomic_clang.h:43, atomic_load) = incoming a0 + index + 0x400010 in both images | U sanitizer_stackdepotbase.h:73 `TwoLevelMap<Node, kNodesSize1, kNodesSize2> nodes`; U sanitizer_flat_map.h:121-124, :155 `atomic_uintptr_t map1_[kSize1]` |
| `StackDepotBase_Put` | +0x114 | 0x400008 | lui-in-section | CERTIFIED (iii) offset from an argument base | `this` of TwoLevelMap::Create = incoming a0 + 0x400008 = &nodes | binary: a0 of `jal ...TwoLevelMap...6CreateEm` (+0x168, +0x27c) = incoming a0 + 0x400008 in both images; a3 at `jal lock` (+0x17c) is not a parameter (static `lock(atomic_uint32_t *p)`) | U sanitizer_stackdepotbase.h:67, :73; U sanitizer_flat_map.h:143 |
| `StackDepotBase_Put` | +0x1b0 | 0x400000 | lui-in-section | CERTIFIED (iii) offset from an argument base | amo base = incoming a0 + 0x400000 = &n_uniq_ids | binary: `amoadd.w a0,a1,(a0)` (+0x1bc; .debug_line sanitizer_atomic_clang.h:58) base = incoming a0 + 0x400000 in both images | U sanitizer_stackdepotbase.h:71 `atomic_uint32_t n_uniq_ids`, :139 |
| `StackDepotGet` | +0x30 | 0x400010 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | load base theDepot+0x400010 + a runtime index (nodes.map1_[i]) | binary: `ld` bases (+0x3c, +0x48) = auipc theDepot + 0x400010 + index in both images | U sanitizer_stackdepot.cpp:58 `static StackDepot theDepot`, :214-215 |
| `StackDepotGet` | +0xc8 | 0x400008 | lui-in-section | CERTIFIED (iii) absolute address, same symbol + offset in both images | `this` of TwoLevelMap::Create = theDepot+0x400008 | binary: a0 of `jal ...TwoLevelMap...6CreateEm` (+0xd0) = theDepot+0x400008 in both images | U sanitizer_stackdepot.cpp:58; U sanitizer_flat_map.h:143 |
| `TwoLevelMap_StackDepotNode_Create` | +0x84 | 0xfffff | lui-in-section | CERTIFIED (i) call argument | MmapOrDie `size` (uptr), used only as a length (ruling (b)) | binary: a0 of `jal MmapOrDie` (+0xa0; DWARF call site sanitizer_common.h:90); the value is the round-up mask of RoundUpTo | U sanitizer_common.h:90; P sanitizer_posix.cpp:48-56 (as InitializeAsanInterceptors +0x44); U sanitizer_flat_map.h:117-118, :147 `MmapOrDie(MmapSize(), "TwoLevelMap")` |
| `sysconf` | +0xe8 | 0x31000 | lui-in-section | CERTIFIED (ii) return value | returned by `long sysconf(int)`: 200809, an integer, not an address | binary: `addiw a0,a2,105` -> a0 = 0x31069, then the jump table (0x212f8, 13 entries) reaches `ret` (+0xc0) with it; a2 at `jal getauxval` / `jal sysinfo` is not a parameter; DWARF: the call site of sysconf in the runtime declares it in the toolchain image's musl sysroot (usr/include/unistd.h:133) | M include/unistd.h:133 `long sysconf(int);`, :217 `#define _POSIX_VERSION 200809L`; M src/conf/sysconf.c:190-191 `case VER & 255: return _POSIX_VERSION;` |
| `sysconf` | +0xf0 | 0x31069 | lui-in-section | CERTIFIED (ii) return value | as +0xe8 (this word builds the returned 0x31069) | binary: as +0xe8 | M as +0xe8 |
| `fmt_fp` | +0x670 | 0x24000 | lui-in-section | CERTIFIED (e) frame base + CERTIFIED (ii) return value + CERTIFIED (i) call argument | the 9 load / store bases it enters are frame bases (ruling (e): the base's only pointer root is sp on every path; integer constants added to it, including a lui-built frame offset, are offsets, not pointers; no auipc / lui / section-built pointer appears anywhere in the base chain); also the returned int, memset `n`, __fwritex `l` and pad `w` (lengths) | binary: rootcheck.py (fmt_fp prototype: a1-a7 integers) finds that every value reaching the bases at +0xa90, +0xb04, +0xde0, +0xe0c, +0xe30, +0xe38, +0xe44, +0xec4, +0xf24 has the single pointer root sp, on every path, in both images (the VLA: `sub s6,sp,a0` at +0x94, stack probe, `mv sp,s6`); the integer constants in the chains (frame offsets from sp, e.g. -0x25c ... -0x1f0c, and the index from this 0x24000 after its division by 9) are offsets; the lui values of fmt_fp that lie in a section (0x24000; 0x12000 at +0x398 / +0xa20 / +0x10f8) never reach a base as a pointer, and no auipc pointer does (no `saddr` / `pc` root, no `mix`). Other uses: a0 at `ret` (+0x474, int), a2 of `jal memset` (+0x1138, +0x11f0, +0x1660), a1 of `jal __fwritex` (+0x1194 ... +0x16b0), a2 of `jal pad` (+0x14e0, +0x1624); spills to its own frame (reloads traced); registers live at __floatsitf(int) / __stack_chk_fail(void) beyond their parameters | M src/stdio/vfprintf.c:181 `static int fmt_fp(FILE *f, long double y, int w, int p, int fl, int t, int ps)`, :190 `uint32_t big[bufsize]`, :314-315 `((j+9*LDBL_MAX_EXP)/9 - LDBL_MAX_EXP)`, `j += 9*LDBL_MAX_EXP` (0x24000 = 9 * 16384); :138-146 pad (w only in `l >= w`, `l = w - l`); M src/internal/stdio_impl.h:78 `size_t __fwritex(const unsigned char *, size_t, FILE *)`; M include/string.h:29 memset |
| `SizeClassAllocator64_GetFromAllocator` | +0x1b4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `asan_register_globals_impl_RegisterGlobal_loop` | +0xb2c | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `asan_unregister_globals_impl` | +0x3fc | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `asan_UnpoisonBeforeMain_ctor` | +0x134 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `asan_before_dynamic_init_asan_after_dynamic_init` | +0x1d4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `AsanStats_Clear_ctor` | +0x170 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `GetAsanThreadContext` | +0x150 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `InternalAllocator_CombinedAllocator_Allocate_int` | +0x80 | 0x20000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use is `bltu` (a size limit) | binary: uses listed below | - |
| `ThreadRegistry_CreateThread` | +0x21c | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `ThreadRegistry_StartThread` | +0x1a4 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `StackStore_Store_BlockInfo_helper` | +0xb0 | 0x100000 | lui-const (dataflow) | CERTIFIED (store) | store into the integer `*pack` (uptr) | binary: `xor` with 0x100000, `seqz`, `add` to *pack, `sd a0,0(s0)` (+0xd4; .debug_line sanitizer_stack_store.cpp:52; pack = 2nd parameter of `StoreERKNS_10StackTraceEPm`, unsigned long*) | U sanitizer_stack_store.cpp:40, :52 `*pack += blocks_[GetBlockIdx(idx)].Stored(h.size + 1)`, :374-376 |
| `lsan_register_root_region` | +0x1dc | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `lsan_unregister_root_region` | +0x248 | 0xfffff | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare: `slli 40`, `and`, then `beq` / `bne` only; registers live at Semaphore::Post(this, count), Printf("UnpoisonBeforeMain\n") (no conversion) or __asan_after_dynamic_init(void) are beyond the parameters, so not passed | binary: `addi a1,a1,-1` after `lui a1,0x100` = 0xfffff; uses listed below | - |
| `open` | +0x48 | 0x410000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - |
| `libc_malloc_impl` | +0x64 | 0x1ffec | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - |
| `printf_core` | +0x994 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`); it is also spilled to its own frame slot, and every reload is used only by compares | binary: uses listed below | - |
| `pad` | +0x30 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - |
| `fmt_fp` | +0x398 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - |
| `fmt_fp` | +0xa20 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`) | binary: uses listed below | - |
| `fmt_fp` | +0x10f8 | 0x12000 | lui-const (dataflow) | CERTIFIED (d) compare only | every use on every path is a compare (`and`, then `beq` / `bne` / `bltu`); it is also spilled to its own frame slot, and every reload is used only by compares | binary: uses listed below | - |

### Every use of every value (both images identical)

One line per use site (function offset, instruction, role, linear / non-linear); value variants of one site are merged.
A register live at a call is marked with the parameter it is, or "not a parameter".

**`Quarantine_Recycle` +0x74** (lui-in-section; word lui a4,0x190):

- +0x7c `mul a4,a6,a4` alu mul [linear]
- +0x84 `bgeu a5,a4,0x32e04` branch [non-linear]
- +0xa4 `jal 0x32f2c` live-in-a4-at-call [non-linear]: QuarantineCache::MergeBatches, not a parameter

**`SizeClassAllocator64_EnsureFreeArraySpace` +0x2c** (lui-in-section; word addiw a3,a3,-1):

- +0x30 `add a3,a5,a3` add [linear]
- +0x38 `and s0,a3,s0` alu and [linear]
- +0x44 `bgeu s0,a3,0x33f50` branch [non-linear]
- +0x6c `add a2,s0,a2` add [non-linear]
- +0x7c `bgeu a0,a2,0x33f28` branch [non-linear]
- +0x88 `sub s2,s0,a4` sub [non-linear]
- +0x9c `jal 0x6db74` live-in-a2-at-call [non-linear]: ReservedAddressRange::Map, parameter `size`
- +0xb8 `jal 0x5328c` live-in-a1-at-call [non-linear]: PoisonShadow, parameter `size`
- +0xc8 `add a1,a1,s2` add [non-linear]
- +0xd4 `sd a1,80(a0)` store-data [non-linear]
- +0xdc `sd s0,24(a1)` store-data [non-linear]
- +0x120 `jal 0x6b12c` live-in-a3-at-call [non-linear]: CheckFailed, parameter `v1`

**`LargeMmapAllocator_Allocate` +0x430** (lui-in-section; word lui a4,0x100):

- +0x434 `jal 0x6b12c` live-in-a4-at-call [linear]: CheckFailed, parameter `v2`

**`SizeClassAllocator64_PopulateFreeArray` +0xb0** (lui-in-section; word lui s3,0x40):

- +0xbc `add s3,a1,s3` add [linear]
- +0xcc `add a3,a3,s3` add [linear]
- +0xd4 `bgeu a3,a1,0x36410` branch [linear]
- +0xf0 `add s4,s4,s3` add [linear]
- +0x100 `bgeu a2,s4,0x362e4` branch [linear]
- +0x11c `jal 0x6db74` live-in-a2-at-call [linear]: ReservedAddressRange::Map, parameter `size`
- +0x138 `jal 0x5328c` live-in-a1-at-call [linear]: PoisonShadow, parameter `size`
- +0x14c `add a2,a2,s3` add [linear]
- +0x154 `sd a2,80(a0)` store-data [linear]
- +0x160 `amoadd.d zero,s3,(s1)` amo-data(amoadd.d) [linear]
- +0x16c `add s4,s4,s3` add [linear]
- +0x170 `sd s4,48(s0)` store-data [linear]
- +0x178 `sub s4,s4,a3` sub [linear]
- +0x17c `divu s3,s4,s5` alu divu [linear]
- +0x180 `add s1,s1,s3` add [non-linear]
- +0x190 `jal 0x33e4c` live-in-a3-at-call [non-linear]: EnsureFreeArraySpace, parameter `num_freed_chunks`
- +0x19c `bltu s4,s5,0x36364` branch [linear]
- +0x1b0 `slli s1,s1,0x2` alu slli [non-linear]
- +0x1b4 `add a1,a1,s1` add [non-linear]
- +0x1cc `add a5,a1,a5` add [non-linear]
- +0x1d0 `sw a4,0(a5)` BASE [non-linear]: base reached non-linearly
- +0x1d8 `bltu a0,s3,0x36344` branch [non-linear]
- +0x1e0 `mul a1,s3,s5` alu mul [non-linear]
- +0x1e8 `add a3,a3,a1` add [non-linear]
- +0x1ec `add a0,a0,s3` add [non-linear]
- +0x1f0 `sd a0,16(s0)` store-data [non-linear]
- +0x1f4 `sd a3,32(s0)` store-data [non-linear]
- +0x1f8 `bltu a4,a3,0x36420` branch [non-linear]
- +0x2ac `jal 0x6b12c` live-in-a3-at-call [non-linear]: CheckFailed, parameter `v1`
- +0x2ac `jal 0x6b12c` live-in-a5-at-call [non-linear]: CheckFailed, not a parameter
- +0x2c4 `jal 0x6b12c` live-in-a5-at-call [non-linear]: CheckFailed, not a parameter
- +0x2e8 `jal 0x667a4` live-in-a3-at-call [linear]: Printf, Printf variadic slot 3

**`AsanDeactivate_activation_CHECK_helper` +0x8c** (lui-in-section; word addi a0,a0,16):

- +0x90 `sw a0,8(sp)` spill to sp-40 [linear]

**`InitializeAsanInterceptors` +0x44** (lui-in-section; word addiw a0,a2,-1240):

- +0x4c `jal 0x652f4` live-in-a0-at-call [linear]: MmapOrDie, parameter `size`

**`ReserveShadowMemoryRanges_sealed_early_shadow_re` +0x74** (lui-in-section; word addiw a3,a0,34):

- +0x88 `jal 0x63c24` live-in-a3-at-call [linear]: internal_mmap, parameter `flags`

**`ReserveShadowMemoryRanges_sealed_early_shadow_re` +0xfc** (lui-in-section; word addiw s0,a0,34):

- +0x118 `jal 0x63c24` live-in-a3-at-call [linear]: internal_mmap, parameter `flags`
- +0x164 `jal 0x63c24` live-in-a3-at-call [linear]: internal_mmap, parameter `flags`

**`InitializeShadowMemory` +0x1b0** (lui-in-section; word lui a3,0x40):

- +0x1c0 `jal 0x6ba60` live-in-a3-at-call [linear]: ProtectGap, parameter `zero_base_max_shadow_start`

**`internal_allocator` +0x88** (lui-in-section; word addiw a0,a1,8):

- +0x8c `add a0,s1,a0` add [linear]
- +0x98 `jal 0x63424` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`internal_allocator` +0xa4** (lui-in-section; word lui a2,0x40):

- +0xb0 `jal 0x63424` live-in-a2-at-call [linear]: __sanitizer_internal_memset, parameter `n`

**`internal_allocator` +0xb4** (lui-in-section; word addiw a0,s3,64):

- +0xb8 `add a0,s1,a0` add [linear]
- +0xc8 `jal 0x63424` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`internal_allocator` +0xcc** (lui-in-section; word lui s2,0x41):

- +0xd0 `addiw a0,s2,-576` alu addiw [linear]
- +0xd4 `add a0,s1,a0` add [linear]
- +0xe0 `jal 0x63424` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`
- +0xfc `add a1,s1,s2` add [linear]
- +0x100 `addiw a2,s2,-560` alu addiw [linear]
- +0x104 `add a2,s1,a2` add [linear]
- +0x10c `sd a0,-576(a1)` BASE [linear]: absolute: abs:_ZN11__sanitizerL26internal_alloc_placeholderE+0x40dc0
- +0x110 `sd a2,-568(a1)` BASE [linear]: absolute: abs:_ZN11__sanitizerL26internal_alloc_placeholderE+0x40dc8
- +0x110 `sd a2,-568(a1)` store-data [linear]
- +0x144 `ret` return a1 [linear]

**`internal_allocator` +0xd0** (lui-in-section; word addiw a0,s2,-576):

- +0xd4 `add a0,s1,a0` add [linear]
- +0xe0 `jal 0x63424` live-in-a0-at-call [linear]: __sanitizer_internal_memset, parameter `s`

**`internal_allocator` +0xd8** (lui-in-section; word addiw a2,s3,584):

- +0xe0 `jal 0x63424` live-in-a2-at-call [linear]: __sanitizer_internal_memset, parameter `n`

**`internal_allocator` +0x100** (lui-in-section; word addiw a2,s2,-560):

- +0x104 `add a2,s1,a2` add [linear]
- +0x110 `sd a2,-568(a1)` store-data [linear]

**`InternalAllocator_CombinedAllocator_Allocate_int` +0xa8** (lui-in-section; word addiw a1,a1,-576):

- +0xb0 `add a4,a0,a1` add [linear]
- +0xc0 `jal 0x5e148` live-in-a0-at-call [linear]: LargeMmapAllocator::Allocate, parameter `this`
- +0xc0 `jal 0x5e148` live-in-a4-at-call [linear]: LargeMmapAllocator::Allocate, not a parameter

**`InternalAllocator_CombinedAllocator_Allocate_int` +0xac** (lui-in-section; word addiw a5,a4,8):

- +0xb4 `add a1,a0,a5` add [linear]
- +0xc0 `jal 0x5e148` live-in-a1-at-call [linear]: LargeMmapAllocator::Allocate, parameter `stat`
- +0xc0 `jal 0x5e148` live-in-a5-at-call [linear]: LargeMmapAllocator::Allocate, not a parameter

**`InternalAllocator_LargeMmapAllocator_Allocate` +0x118** (lui-in-section; word addiw a1,a1,16):

- +0x11c `add s3,s1,a1` add [linear]
- +0x120 `addi a1,s3,560` addi [linear]
- +0x124 `andi a3,a1,-4` align andi -4 [linear]
- +0x12c `lr.w.aq a5,zero,(a3)` BASE(lr.w.aq) [linear]: object base in:a0, offset 0x40240
- +0x140 `sc.w a6,a6,(a3)` BASE(sc.w) [linear]: object base in:a0, offset 0x40240
- +0x150 `ld a3,0(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x160 `ld a4,16(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x164 `ld a5,32(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x168 `ld a1,40(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x230 `sd a7,0(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x234 `sb zero,8(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x238 `sd a4,16(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x23c `sd a3,32(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x264 `sd a1,40(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x27c `sb zero,560(s3)` BASE [linear]: object base in:a0, offset 0x40010
- +0x390 `jal 0x651a0` live-in-a0-at-call [linear]: StaticSpinMutex::LockSlow, parameter `this`
- +0x390 `jal 0x651a0` live-in-a1-at-call [linear]: StaticSpinMutex::LockSlow, not a parameter
- +0x390 `jal 0x651a0` live-in-a3-at-call [linear]: StaticSpinMutex::LockSlow, not a parameter
- +0x398 `ld a3,0(s3)` BASE [linear]: object base in:a0, offset 0x40010

**`InternalAllocator_LargeMmapAllocator_Allocate` +0x24c** (lui-in-section; word lui a3,0x40):

- +0x250 `add a3,s1,a3` add [linear]
- +0x254 `add a2,a3,a2` add [linear]
- +0x258 `ld a3,64(a2)` BASE [linear]: object base in:a0+op:+0x248, offset 0x40000
- +0x268 `sd a3,64(a2)` BASE [linear]: object base in:a0+op:+0x248, offset 0x40000

**`internal_usleep_internal_sleep_nanosleep` +0x14** (lui-in-section; word addiw a2,a2,576):

- +0x20 `mul a1,a4,a2` alu mul [linear]
- +0x24 `sub a0,a0,a1` sub [non-linear]
- +0x2c `mul a0,a0,a3` alu mul [non-linear]
- +0x38 `sd a0,8(sp)` spill to sp-8 [non-linear]

**`ReadLongProcessName_proc_self_cmdline` +0x40** (lui-in-section; word lui a4,0x100):

- +0x48 `jal 0x60768` live-in-a4-at-call [linear]: ReadFileToBuffer, parameter `max_len`

**`GetNamedMappingFd_MmapNamed` +0x90** (lui-in-section; word addiw a1,a1,578):

- +0x98 `jal 0x63c84` live-in-a1-at-call [linear]: internal_open, parameter `flags`

**`SealedRepairReservation` +0x78** (lui-in-section; word addiw a3,a0,34):

- +0x90 `jal 0x63c24` live-in-a3-at-call [linear]: internal_mmap, parameter `flags`

**`StackStore_Alloc` +0x78** (lui-in-section; word lui a4,0x100):

- +0x7c `bltu a4,a5,0x6fbac` branch [linear]
- +0x84 `addiw a7,a4,-1` alu addiw [linear]
- +0x88 `and t2,s0,a7` alu and [linear]
- +0x90 `sub t2,a4,t2` sub [non-linear]
- +0x90 `sub t2,a4,t2` sub [linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [non-linear]
- +0xa8 `sub t3,a5,t2` sub [linear]
- +0xa8 `sub t3,a5,t2` sub [non-linear]
- +0xb4 `add t0,t2,t0` add [linear]
- +0xb4 `add t0,t2,t0` add [non-linear]
- +0xc0 `xor t0,t0,a4` alu xor [linear]
- +0xc0 `xor t0,t0,a4` alu xor [non-linear]
- +0xc4 `seqz t0,t0` alu seqz [non-linear]
- +0xc8 `add t0,t2,t0` add [non-linear]
- +0xcc `sd t0,0(a3)` store-data [non-linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [non-linear]
- +0xe0 `add t0,t3,t0` add [linear]
- +0xe0 `add t0,t3,t0` add [non-linear]
- +0xe4 `xor t0,t0,a4` alu xor [linear]
- +0xe4 `xor t0,t0,a4` alu xor [non-linear]
- +0xe8 `seqz t0,t0` alu seqz [non-linear]
- +0xec `add t0,t1,t0` add [non-linear]
- +0xf0 `sd t0,0(a3)` store-data [non-linear]
- +0x110 `jal 0x7047c` live-in-a4-at-call [linear]: StackStore::BlockInfo::Create, not a parameter
- +0x110 `jal 0x7047c` live-in-a7-at-call [linear]: StackStore::BlockInfo::Create, not a parameter
- +0x130 `jal 0x6b12c` live-in-a4-at-call [linear]: CheckFailed, parameter `v2`

**`StackStore_Alloc` +0x84** (lui-in-section; word addiw a7,a4,-1):

- +0x88 `and t2,s0,a7` alu and [linear]
- +0x90 `sub t2,a4,t2` sub [non-linear]
- +0x9c `amoadd.w.rl t0,t2,(t0)` amo-data(amoadd.w.rl) [non-linear]
- +0xa8 `sub t3,a5,t2` sub [non-linear]
- +0xb4 `add t0,t2,t0` add [non-linear]
- +0xc0 `xor t0,t0,a4` alu xor [non-linear]
- +0xc4 `seqz t0,t0` alu seqz [non-linear]
- +0xc8 `add t0,t2,t0` add [non-linear]
- +0xcc `sd t0,0(a3)` store-data [non-linear]
- +0xd0 `amoadd.w.rl t0,t3,(t1)` amo-data(amoadd.w.rl) [non-linear]
- +0xe0 `add t0,t3,t0` add [non-linear]
- +0xe4 `xor t0,t0,a4` alu xor [non-linear]
- +0xe8 `seqz t0,t0` alu seqz [non-linear]
- +0xec `add t0,t1,t0` add [non-linear]
- +0xf0 `sd t0,0(a3)` store-data [non-linear]
- +0x110 `jal 0x7047c` live-in-a7-at-call [linear]: StackStore::BlockInfo::Create, not a parameter

**`StackDepotBase_Put` +0x104** (lui-in-section; word addiw s8,a3,16):

- +0x108 `add s8,s1,s8` add [linear]
- +0x130 `add a2,s8,a2` add [linear]
- +0x134 `ld a2,0(a2)` BASE [linear]: object base in:a0+op:+0x12c, offset 0x400010
- +0x1dc `add a0,s8,a0` add [linear]
- +0x1e0 `ld a0,0(a0)` BASE [linear]: object base in:a0+op:+0x1d8, offset 0x400010

**`StackDepotBase_Put` +0x114** (lui-in-section; word addiw a3,a3,8):

- +0x118 `add s4,s1,a3` add [linear]
- +0x168 `jal 0x72790` live-in-a0-at-call [linear]: TwoLevelMap::Create, parameter `this`
- +0x168 `jal 0x72790` live-in-a3-at-call [linear]: TwoLevelMap::Create, not a parameter
- +0x17c `jal 0x72700` live-in-a3-at-call [linear]: StackDepotBase::lock, not a parameter
- +0x27c `jal 0x72790` live-in-a0-at-call [linear]: TwoLevelMap::Create, parameter `this`

**`StackDepotBase_Put` +0x1b0** (lui-in-section; word lui a0,0x400):

- +0x1b4 `add a0,s1,a0` add [linear]
- +0x1bc `amoadd.w a0,a1,(a0)` BASE(amoadd.w) [linear]: object base in:a0, offset 0x400000

**`StackDepotGet` +0x30** (lui-in-section; word addiw a3,a3,16):

- +0x34 `add a0,a2,a3` add [linear]
- +0x38 `add a0,a0,a4` add [linear]
- +0x3c `ld a3,0(a0)` BASE [linear]: absolute: abs:_ZN11__sanitizerL8theDepotE+0x400010 + runtime op:+0x28
- +0x48 `ld a0,0(a0)` BASE [linear]: absolute: abs:_ZN11__sanitizerL8theDepotE+0x400010 + runtime op:+0x28

**`StackDepotGet` +0xc8** (lui-in-section; word addiw a0,a0,8):

- +0xcc `add a0,a2,a0` add [linear]
- +0xd0 `jal 0x72790` live-in-a0-at-call [linear]: TwoLevelMap::Create, parameter `this`

**`TwoLevelMap_StackDepotNode_Create` +0x84** (lui-in-section; word addiw a1,a1,-1):

- +0x88 `add a1,a0,a1` add [linear]
- +0x90 `and a0,a1,a0` alu and [linear]
- +0xa0 `jal 0x652f4` live-in-a0-at-call [non-linear]: MmapOrDie, parameter `size`

**`sysconf` +0xe8** (lui-in-section; word lui a2,0x31):

- +0xc0 `ret` return a0 [non-linear]
- +0xc0 `ret` return a0 [linear]
- +0xf0 `addiw a0,a2,105` alu addiw [linear]
- +0x108 `jal 0x8ca54` live-in-a2-at-call [linear]: __getauxval, not a parameter
- +0x13c `jal 0x89098` live-in-a2-at-call [linear]: __lsysinfo, not a parameter
- +0x224 `jal 0x88658` live-in-a0-at-call [non-linear]: __stack_chk_fail, not a parameter
- +0x224 `jal 0x88658` live-in-a0-at-call [linear]: __stack_chk_fail, not a parameter

**`sysconf` +0xf0** (lui-in-section; word addiw a0,a2,105):

- +0xc0 `ret` return a0 [non-linear]
- +0xc0 `ret` return a0 [linear]
- +0x224 `jal 0x88658` live-in-a0-at-call [non-linear]: __stack_chk_fail, not a parameter
- +0x224 `jal 0x88658` live-in-a0-at-call [linear]: __stack_chk_fail, not a parameter

**`fmt_fp` +0x670** (lui-in-section; word lui a1,0x24):

- +0x474 `ret` return a0 [non-linear]; +0x67c `addw a0,a0,a1` alu addw [linear]; +0x688 `mul a1,a0,a1` alu mul [non-linear]; +0x68c `srli a2,a1,0x3f` alu srli [non-linear]; +0x690 `srai a1,a1,0x21` alu srai [non-linear]; +0x694 `add a1,a1,a2` add [non-linear]; +0x698 `slli a2,a1,0x2` alu slli [non-linear]; +0x69c `slli a3,a1,0x3` alu slli [non-linear]; +0x6a0 `add a4,s6,a2` add [non-linear]; +0x6a4 `add a1,a3,a1` add [non-linear]; +0x6a8 `addi s2,a4,4` addi [non-linear]; +0x6ac `subw a0,a0,a1` alu subw [non-linear]; +0x6b4 `add a2,a4,s10` add [non-linear]; +0x6b8 `blt a1,a0,0x90630` branch [non-linear]; +0x6bc `addi a0,a0,-8` addi [non-linear]; +0x6c8 `addiw a0,a0,1` alu addiw [non-linear]; +0x6d0 `bnez a0,0x90270` branch [non-linear]; +0xa8c `sd a2,-504(s0)` spill to sp-504 [non-linear]; +0xa90 `lw s8,0(a2)` BASE [non-linear]: base reached non-linearly; +0xaa0 `add s10,s2,s10` add [non-linear]; +0xaa8 `bne s10,s11,0x90664` branch [non-linear]; +0xabc `sd a4,-520(s0)` spill to sp-520 [non-linear]; +0xac4 `jal 0x8bf08` live-in-a2-at-call [non-linear]: __floatsitf, not a parameter; +0xac4 `jal 0x8bf08` live-in-a3-at-call [non-linear]: __floatsitf, not a parameter; +0xac4 `jal 0x8bf08` live-in-a4-at-call [non-linear]: __floatsitf, not a parameter; +0xaf8 `bgeu s1,a0,0x906dc` branch [non-linear]; +0xb00 `add a0,s2,a0` add [non-linear]; +0xb04 `lbu a0,-4(a0)` BASE [non-linear]: base reached non-linearly; +0xd48 `bne s10,s11,0x90900` branch [non-linear]; +0xde0 `sw s2,0(s7)` BASE [non-linear]: base reached non-linearly; +0xe0c `sw a0,0(s7)` BASE [non-linear]: base reached non-linearly; +0xe1c `add a0,a2,a0` add [non-linear]; +0xe30 `lw a2,0(a0)` BASE [non-linear]: base reached non-linearly; +0xe38 `sw a2,0(a0)` BASE [non-linear]: base reached non-linearly; +0xe3c `addi a0,a0,-4` addi [non-linear]; +0xe44 `sw zero,4(a0)` BASE [non-linear]: base reached non-linearly; +0xe48 `bgeu a0,s1,0x909d8` branch [non-linear]; +0xe74 `addi s7,a0,4` addi [non-linear]; +0xea4 `addi a0,s7,4` addi [non-linear]; +0xea8 `bltu a0,s11,0x90a58` branch [non-linear]; ... (106 more sites of the same kinds: frame bases, lengths, non-parameters)

**`SizeClassAllocator64_GetFromAllocator` +0x1b4** (lui-const (dataflow); word addi a1,a1,-1):

- +0x1c0 `slli a6,a1,0x28` alu slli [linear]
- +0x1f8 `and a1,a2,a6` alu and [linear]
- +0x1fc `beqz a1,0x360a0` branch [non-linear]
- +0x25c `jal 0x652b0` live-in-a6-at-call [linear]: Semaphore::Post, not a parameter

**`asan_register_globals_impl_RegisterGlobal_loop` +0xb2c** (lui-const (dataflow); word addi a1,a1,-1):

- +0xb38 `slli a5,a1,0x28` alu slli [linear]
- +0xb6c `and a1,a0,a5` alu and [linear]
- +0xb70 `beqz a1,0x3ead4` branch [non-linear]
- +0xbdc `jal 0x652b0` live-in-a5-at-call [linear]: Semaphore::Post, not a parameter

**`asan_unregister_globals_impl` +0x3fc** (lui-const (dataflow); word addi a1,a1,-1):

- +0x408 `slli a5,a1,0x28` alu slli [linear]
- +0x43c `and a1,a0,a5` alu and [linear]
- +0x440 `beqz a1,0x3f1c0` branch [non-linear]
- +0x510 `j 0x652b0` live-in-a5-at-tailcall [linear]: Semaphore::Post, not a parameter

**`asan_UnpoisonBeforeMain_ctor` +0x134** (lui-const (dataflow); word addi a1,a1,-1):

- +0x140 `slli a6,a1,0x28` alu slli [linear]
- +0x178 `and a1,a2,a6` alu and [linear]
- +0x17c `beqz a1,0x3fc1c` branch [non-linear]
- +0x208 `jal 0x652b0` live-in-a6-at-call [linear]: Semaphore::Post, not a parameter
- +0x22c `jal 0x667a4` live-in-a6-at-call [linear]: Printf, Printf variadic slot 6
- +0x25c `j 0x3fcec` live-in-a6-at-tailcall [linear]: __asan_after_dynamic_init, not a parameter
- +0x264 `jal 0x652b0` live-in-a6-at-call [linear]: Semaphore::Post, not a parameter

**`asan_before_dynamic_init_asan_after_dynamic_init` +0x1d4** (lui-const (dataflow); word addi a1,a1,-1):

- +0x1e0 `slli a5,a1,0x28` alu slli [linear]
- +0x218 `and a1,a0,a5` alu and [linear]
- +0x21c `beqz a1,0x3ff2c` branch [non-linear]
- +0x2dc `j 0x652b0` live-in-a5-at-tailcall [linear]: Semaphore::Post, not a parameter

**`AsanStats_Clear_ctor` +0x170** (lui-const (dataflow); word addi a1,a1,-1):

- +0x17c `slli a5,a1,0x28` alu slli [linear]
- +0x1b4 `and a1,a0,a5` alu and [linear]
- +0x1b8 `beqz a1,0x5a54c` branch [non-linear]
- +0x278 `j 0x652b0` live-in-a5-at-tailcall [linear]: Semaphore::Post, not a parameter

**`GetAsanThreadContext` +0x150** (lui-const (dataflow); word addi a3,a3,-1):

- +0x15c `slli a3,a3,0x28` alu slli [linear]
- +0x19c `and a1,a7,a3` alu and [linear]
- +0x1a0 `beqz a1,0x5d654` branch [non-linear]
- +0x204 `jal 0x652b0` live-in-a3-at-call [linear]: Semaphore::Post, not a parameter

**`InternalAllocator_CombinedAllocator_Allocate_int` +0x80** (lui-const (dataflow); word lui a5,0x20):

- +0x84 `bltu a5,a3,0x5df1c` branch [linear]
- +0x88 `bltu a5,a4,0x5df1c` branch [linear]

**`ThreadRegistry_CreateThread` +0x21c** (lui-const (dataflow); word addi a1,a1,-1):

- +0x228 `slli a5,a1,0x28` alu slli [linear]
- +0x25c `and a1,a0,a5` alu and [linear]
- +0x260 `beqz a1,0x69880` branch [non-linear]
- +0x2c4 `jal 0x652b0` live-in-a5-at-call [linear]: Semaphore::Post, not a parameter

**`ThreadRegistry_StartThread` +0x1a4** (lui-const (dataflow); word addi a1,a1,-1):

- +0x1b0 `slli a5,a1,0x28` alu slli [linear]
- +0x1e4 `and a1,a0,a5` alu and [linear]
- +0x1e8 `beqz a1,0x6a540` branch [non-linear]
- +0x2b8 `j 0x652b0` live-in-a5-at-tailcall [linear]: Semaphore::Post, not a parameter

**`StackStore_Store_BlockInfo_helper` +0xb0** (lui-const (dataflow); word lui a1,0x100):

- +0xc4 `xor a0,a0,a1` alu xor [linear]
- +0xcc `seqz a0,a0` alu seqz [non-linear]
- +0xd0 `add a0,a2,a0` add [non-linear]
- +0xd4 `sd a0,0(s0)` store-data [non-linear]

**`lsan_register_root_region` +0x1dc** (lui-const (dataflow); word addi a1,a1,-1):

- +0x1e8 `slli a4,a1,0x28` alu slli [linear]
- +0x220 `and a1,a5,a4` alu and [linear]
- +0x224 `beqz a1,0x7c338` branch [non-linear]
- +0x288 `jal 0x652b0` live-in-a4-at-call [linear]: Semaphore::Post, not a parameter

**`lsan_unregister_root_region` +0x248** (lui-const (dataflow); word addi a1,a1,-1):

- +0x250 `slli a4,a1,0x28` alu slli [linear]
- +0x290 `and a1,t0,a4` alu and [linear]
- +0x294 `beqz a1,0x7c6d8` branch [non-linear]
- +0x364 `j 0x652b0` live-in-a4-at-tailcall [linear]: Semaphore::Post, not a parameter

**`open` +0x48** (lui-const (dataflow); word lui a0,0x410):

- +0x4c `and a1,s0,a0` alu and [linear]
- +0x50 `beq a1,a0,0x88c3c` branch [non-linear]
- +0x50 `beq a1,a0,0x88c3c` branch [linear]

**`libc_malloc_impl` +0x64** (lui-const (dataflow); word addiw a0,a0,-20):

- +0x70 `bltu s0,a0,0x8a00c` branch [linear]

**`printf_core` +0x994** (lui-const (dataflow); word lui a0,0x12):

- +0x998 `and s2,s8,a0` alu and [linear]
- +0x99c `sd s2,8(sp)` spill to sp-536 [non-linear]
- +0x99c `sd s2,8(sp)` spill to sp-536 [linear]
- +0x9a0 `bnez s2,0x8f594` branch [non-linear]
- +0x9a0 `bnez s2,0x8f594` branch [linear]
- +0xa44 `bne s2,a0,0x8f638` branch [non-linear]
- +0xa44 `bne s2,a0,0x8f638` branch [linear]
- +0xb6c `bne s2,a0,0x8ec20` branch [non-linear]
- +0xb6c `bne s2,a0,0x8ec20` branch [linear]

**`pad` +0x30** (lui-const (dataflow); word lui a0,0x12):

- +0x34 `and a0,a4,a0` alu and [linear]
- +0x38 `bnez a0,0x8fb7c` branch [non-linear]

**`fmt_fp` +0x398** (lui-const (dataflow); word lui a0,0x12):

- +0x39c `and a0,s11,a0` alu and [linear]
- +0x3a4 `bne a0,a1,0x8ffc4` branch [non-linear]

**`fmt_fp` +0xa20** (lui-const (dataflow); word lui a0,0x12):

- +0xa24 `and s7,a1,a0` alu and [linear]
- +0xa2c `bnez s7,0x90710` branch [non-linear]
- +0xb88 `bne s7,a0,0x907a8` branch [non-linear]
- +0xcbc `bne s7,a0,0x908dc` branch [non-linear]

**`fmt_fp` +0x10f8** (lui-const (dataflow); word lui a0,0x12):

- +0x10fc `and a0,t3,a0` alu and [linear]
- +0x1104 `sd a0,-472(s0)` spill to sp-472 [non-linear]
- +0x1108 `bnez a0,0x90d40` branch [non-linear]
- +0x11c0 `bne a1,a0,0x90df8` branch [non-linear]
- +0x163c `bne a1,a0,0x9125c` branch [non-linear]

### fmt_fp +0x670: the frame-base check

    # incoming registers typed as integers by the prototype: ['a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7']
    fuzz_boxreg.asan fmt_fp: lui words whose value lies in an image section (static-address candidates): +0x398 lui 0x12000 (.rodata), +0x670 lui 0x24000 (.eh_frame_hdr), +0xa20 lui 0x12000 (.rodata), +0x10f8 lui 0x12000 (.rodata)
    fuzz_boxreg.asan fmt_fp +0xa90 `lw s8,0(a2)`: base a2 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xb04 `lbu a0,-4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xde0 `sw s2,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe0c `sw a0,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe30 `lw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe38 `sw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xe44 `sw zero,4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xec4 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    fuzz_boxreg.asan fmt_fp +0xf24 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp: lui words whose value lies in an image section (static-address candidates): +0x398 lui 0x12000 (.rodata), +0x670 lui 0x24000 (.eh_frame_hdr), +0xa20 lui 0x12000 (.rodata), +0x10f8 lui 0x12000 (.rodata)
    fuzz_boxreg.asan-ubsan fmt_fp +0xa90 `lw s8,0(a2)`: base a2 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xb04 `lbu a0,-4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xde0 `sw s2,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xe0c `sw a0,0(s7)`: base s7 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xe30 `lw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xe38 `sw a2,0(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xe44 `sw zero,4(a0)`: base a0 pointer roots ['sp'], offsets from sp unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xec4 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    fuzz_boxreg.asan-ubsan fmt_fp +0xf24 `lw a2,-4(s7)`: base s7 pointer roots ['sp'], offsets from sp -0x1f04, -0x1f08, -0x1f0c, -0x254, -0x258, -0x25c, -0x41c, unknown (an index added) -> frame base
    # every value reaching every base has root sp, in both images: True

### Controls for the tracer and the rules

Plants are file copies of the images (out of tree); each is traced like the rows above.

| plant | change | tracer / rules |
|---|---|---|
| Plui-or-store | both images: internal_allocator +0xfc `add a1,s1,s2` -> `or a1,s1,s2` (012485b3 -> 0124e5b3); asan-ubsan also `lui s2,0x41` -> `lui s2,0x42` | REFUSED: the value enters the `sd` bases at +0x10c / +0x110 non-linearly (through `or`) |
| Plui-or-store-samelui | as Plui-or-store, with the `lui` unchanged in asan-ubsan | REFUSED: the same, although the two values are equal |
| Plui-store | asan-ubsan internal_allocator `lui s2,0x41` -> `lui s2,0x42`: the lui offset added to an auipc base, used as a store base | REFUSED: the absolute store addresses differ, internal_alloc_placeholder+0x40dc0 / +0x41dc0 |
| Plui-uptr | asan-ubsan InitializeShadowMemory `lui a3,0x40` -> `lui a3,0x41`: a lui value passed as a uptr address parameter (ProtectGap `zero_base_max_shadow_start`) | REFUSED: an address parameter never settles; the values also differ |
| Plui-amo | asan-ubsan StackDepotBase::Put `lui a0,0x400` -> `lui a0,0x401`: an amo base offset | REFUSED: offsets 0x400000 / 0x401000 differ |

On 86da41d3ef68, Plui-or-store gives `DIFFERENT` (the changed `lui` word is a REAL difference) and Plui-or-store-samelui
gives `DIFFERENT-target` for 6 of internal_allocator's 7 `lui-in-section` targets and accepts the planted +0xcc value as
`lui-const (dataflow)`: the kit does not see the `or`.

## Appendix: all 524 pairs

86da41d3ef68 settled column: "same" = 0 target differences and no `lui` value; "same (settled)" = only the fail-closed
targets settled above; "same (lui certified)" = every `lui` value of the row certified (with "settled;" when the row also has
fail-closed targets settled above); "NOT CERTIFIED: REAL 0" = a
`lui` value of the row is not certified.

| row | asan A | asan-ubsan A | size | NOTES.md verdict | 4bbd3a74be89 verdict (by address) | N | 86da41d3ef68 verdict (by address) | N | settled verdict |
|---|---|---|---|---|---|---|---|---|---|
| `start` | 0x2ff58 | 0x2ffb8 | 0x48 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `do_init` | 0x2ffa0 | 0x30000 | 0x74 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `do_fini` | 0x30014 | 0x30074 | 0x90 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AllocatorOptions_SetFrom` | 0x300a4 | 0x30104 | 0x3c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `InitializeAllocator` | 0x30250 | 0x302b0 | 0x18 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_InitLinkerInitialized` | 0x30268 | 0x302c8 | 0x16c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_FindHeapChunkByAddress_helper` | 0x30930 | 0x30990 | 0x15c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_free` | 0x30e60 | 0x30ec0 | 0x28 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_Deallocate` | 0x30e88 | 0x30ee8 | 0x2b8 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_malloc` | 0x31140 | 0x311a0 | 0x5c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_Allocate` | 0x3119c | 0x311fc | 0x988 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `AsanChunkView_GetAsanChunk_ptr_helper` | 0x3225c | 0x322bc | 0x144 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_get_allocated_begin_size_style_query` | 0x3248c | 0x324ec | 0x5c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_Init` | 0x324e8 | 0x32548 | 0x250 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_MapWithCallbackOrDie` | 0x32738 | 0x32798 | 0xf4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_SharedInitCode` | 0x3282c | 0x3288c | 0xe8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Quarantine_Recycle` | 0x32d48 | 0x32da8 | 0x1e4 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `QuarantineCache_DequeueBatch` | 0x32f2c | 0x32f8c | 0x184 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `QuarantineCallback_Recycle` | 0x331e8 | 0x33248 | 0x284 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_GetBlockBegin` | 0x3346c | 0x334cc | 0x180 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64LocalCache_Deallocate` | 0x335ec | 0x3364c | 0x1c8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_Deallocate` | 0x337b4 | 0x33814 | 0x1cc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_ReturnToAllocator_helper` | 0x33980 | 0x339e0 | 0xa0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalMmapVector_Realloc` | 0x33a20 | 0x33a80 | 0x104 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_EnsureFreeArraySpace` | 0x33e4c | 0x33eac | 0x148 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `DieOnMapFailure_sealed` | 0x33f94 | 0x33ff4 | 0x38 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe` | 0x34764 | 0x347c4 | 0x2e8 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `Allocator_QuarantineChunk` | 0x35124 | 0x35184 | 0x178 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Allocator_QuarantineChunk_tail_quarantine_Put` | 0x3529c | 0x352fc | 0x1b0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `QuarantineCache_Enqueue` | 0x3544c | 0x354ac | 0x1e4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CombinedAllocator_Allocate` | 0x35630 | 0x35690 | 0x2d8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LargeMmapAllocator_Allocate` | 0x35908 | 0x35968 | 0x478 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `SizeClassAllocator64LocalCache_Refill` | 0x35d80 | 0x35de0 | 0x100 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SizeClassAllocator64_GetFromAllocator` | 0x35e80 | 0x35ee0 | 0x308 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `SizeClassAllocator64_PopulateFreeArray` | 0x36188 | 0x361e8 | 0x370 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | NOT CERTIFIED: REAL 0 |
| `RZSize2Log` | 0x364f8 | 0x36558 | 0x118 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `LargeMmapAllocator_EnsureSortedChunks` | 0x36918 | 0x36978 | 0xfc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanDeactivate_activation_CHECK_helper` | 0x36a14 | 0x36a74 | 0xe8 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `AsanActivate` | 0x36afc | 0x36b5c | 0xdc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_activation_flag_parse_helper_0_no` | 0x370b4 | 0x37114 | 0xe8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_AddrIsInFakeStack` | 0x3bc54 | 0x3bcb4 | 0xd8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_Create` | 0x3bd2c | 0x3bd8c | 0xec | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FakeStack_Allocate` | 0x3c0d4 | 0x3c134 | 0x2e8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetTLSFakeStack` | 0x3c4f0 | 0x3c550 | 0x30 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_stack_malloc_3` | 0x3c520 | 0x3c580 | 0x1ac | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_3c6cc` | 0x3c6cc | 0x3c72c | 0x13c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_InitializeFlags` | 0x3c808 | 0x3c868 | 0x102c | SHAPE | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_register_globals_impl_RegisterGlobal_loop` | 0x3df40 | 0x3dfa0 | 0xe1c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_unregister_globals_impl` | 0x3ed5c | 0x3edbc | 0x5cc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_register_globals` | 0x3f328 | 0x3f388 | 0x6c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_unregister_globals` | 0x3f394 | 0x3f3f4 | 0x68 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_UnpoisonBeforeMain_ctor` | 0x3fa7c | 0x3fadc | 0x270 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `asan_before_dynamic_init_asan_after_dynamic_init` | 0x3fcec | 0x3fd4c | 0x308 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `RoundUpTo_size_CHECK_helper_sanitizer_common_h_C` | 0x40768 | 0x407c8 | 0x150 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_globals_RegisterGlobal_vector_push_back` | 0x412d4 | 0x41334 | 0x118 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `strlen` | 0x413ec | 0x4144c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `strnlen` | 0x413f0 | 0x41450 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `strcmp` | 0x413f4 | 0x41454 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `strchr` | 0x413fc | 0x4145c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `memcmp` | 0x41400 | 0x41460 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_bcmp` | 0x41404 | 0x41464 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `memchr` | 0x41408 | 0x41468 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `frexpl` | 0x4140c | 0x4146c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `read` | 0x41410 | 0x41470 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fwrite` | 0x41414 | 0x41474 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `time` | 0x41418 | 0x41478 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `gmtime_r` | 0x4141c | 0x4147c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `vprintf` | 0x41420 | 0x41480 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `vfprintf` | 0x41424 | 0x41484 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `vsnprintf` | 0x41428 | 0x41488 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_fprintf` | 0x4142c | 0x4148c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_snprintf` | 0x41430 | 0x41490 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `clock_gettime` | 0x41434 | 0x41494 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `wcrtomb` | 0x41438 | 0x41498 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `wctomb` | 0x4143c | 0x4149c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_strerror` | 0x41440 | 0x414a0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline__exit` | 0x41444 | 0x414a4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_attr_getstack` | 0x41448 | 0x414a8 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `tls_get_addr_thunk` | 0x4144c | 0x414ac | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_fflush` | 0x41450 | 0x414b0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sem_init` | 0x41454 | 0x414b4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sem_destroy` | 0x41458 | 0x414b8 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sem_wait` | 0x4145c | 0x414bc | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sem_trywait` | 0x41460 | 0x414c0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sem_timedwait` | 0x41464 | 0x414c4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sem_post` | 0x41468 | 0x414c8 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_setcancelstate` | 0x4146c | 0x414cc | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `send` | 0x41470 | 0x414d0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sendto` | 0x41474 | 0x414d4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sigaltstack` | 0x41478 | 0x414d8 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `interceptor_trampoline_sigaction` | 0x4147c | 0x414dc | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `icpt_strlen` | 0x41480 | 0x414e0 | 0x294 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strnlen` | 0x41714 | 0x41774 | 0x294 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strcmp` | 0x419ac | 0x41a0c | 0x530 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_strchr` | 0x424b8 | 0x42518 | 0x2e0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcmp` | 0x43030 | 0x43090 | 0xbc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m` | 0x430ec | 0x4314c | 0xbc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memchr` | 0x431a8 | 0x43208 | 0x2d0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_frexpl` | 0x43478 | 0x434d8 | 0x278 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_read` | 0x436f0 | 0x43750 | 0x270 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_fwrite` | 0x43960 | 0x439c0 | 0x274 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_time` | 0x43bd4 | 0x43c34 | 0x29c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_gmtime_r` | 0x44078 | 0x440d8 | 0x240 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vprintf` | 0x442b8 | 0x44318 | 0x9c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `printf_common_format_interceptor` | 0x44354 | 0x443b4 | 0xac8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vfprintf` | 0x44e1c | 0x44e7c | 0xb4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_vsnprintf` | 0x44ed0 | 0x44f30 | 0x318 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `interceptor_fprintf` | 0x451e8 | 0x45248 | 0xd8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_clock_gettime` | 0x45364 | 0x453c4 | 0x258 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_wcrtomb` | 0x455bc | 0x4561c | 0x570 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_wctomb` | 0x45b2c | 0x45b8c | 0x35c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_pthread_attr_getstack` | 0x45f54 | 0x45fb4 | 0x3e8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_tls_get_addr_DTLS_on_tls_get_addr_hook` | 0x46348 | 0x463a8 | 0x7c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sem_timedwait` | 0x465d0 | 0x46630 | 0x298 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_pthread_setcancelstate` | 0x46898 | 0x468f8 | 0x228 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_send` | 0x46ac0 | 0x46b20 | 0x2b4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sendto` | 0x46d74 | 0x46dd4 | 0x2c4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_sigaltstack` | 0x47038 | 0x47098 | 0x25c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeAsanInterceptors` | 0x47368 | 0x473c8 | 0x1b0 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `format_get_value_size` | 0x47518 | 0x47578 | 0x198 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ioctl_table_fill` | 0x4825c | 0x482bc | 0x8cd8 | SHAPE | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Sort_ioctl_desc` | 0x50f34 | 0x50f94 | 0x15c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `memset` | 0x51090 | 0x510f0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `memcpy` | 0x51094 | 0x510f4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `asan_memcpy` | 0x51098 | 0x510f8 | 0x49c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_memset` | 0x51534 | 0x51594 | 0x240 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memset` | 0x51774 | 0x517d4 | 0x2f0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_memcpy` | 0x51a64 | 0x51ac4 | 0x5f0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeMemintrinsicInterceptors_tail_CHECK` | 0x52054 | 0x520b4 | 0x38 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializePlatformInterceptors` | 0x5208c | 0x520ec | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `InitializePlatformExceptionHandlers` | 0x52090 | 0x520f0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `asan_linux_PlatformShadowSetup_helper_CheckForEx` | 0x52094 | 0x520f4 | 0x60 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_CHECK_AddrIsInMem_instance` | 0x52140 | 0x521a0 | 0x13c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanCheckDynamicRTPrereqs` | 0x5227c | 0x522dc | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanCheckIncompatibleRT` | 0x52280 | 0x522e0 | 0x168 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `free` | 0x523e8 | 0x52448 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `malloc` | 0x523ec | 0x5244c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `icpt_free` | 0x523f0 | 0x52450 | 0x1d0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `icpt_malloc` | 0x525c0 | 0x52620 | 0x15c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `DlSymAllocator_Allocate` | 0x5271c | 0x5277c | 0xcc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReplaceSystemMalloc` | 0x527e8 | 0x52848 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `TwoLevelMap_u8_Create` | 0x527ec | 0x5284c | 0x100 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `HeapProfile_Insert_asan_memory_profile` | 0x52c14 | 0x52c74 | 0x16c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCanPoisonMemory` | 0x53268 | 0x532c8 | 0x10 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CanPoisonMemory` | 0x53278 | 0x532d8 | 0x14 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PoisonShadow` | 0x5328c | 0x532ec | 0x4fc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_checked` | 0x53788 | 0x537e8 | 0x13c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_poison_stack_memory_PoisonAlignedStackMemor` | 0x538c4 | 0x53924 | 0x1a0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_unpoison_stack_memory` | 0x53a64 | 0x53ac4 | 0x180 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_region_is_poisoned` | 0x53c14 | 0x53c74 | 0x344 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDInit` | 0x54378 | 0x543d8 | 0x7c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDGet` | 0x543f4 | 0x54454 | 0x40 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanTSDSet` | 0x54434 | 0x54494 | 0x40 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PlatformTSDDtor` | 0x54474 | 0x544d4 | 0x84 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallAtForkHandler` | 0x544f8 | 0x54558 | 0x1c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallAtExitCheckLeaks` | 0x54574 | 0x545d4 | 0x44 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportDeadlySignal` | 0x54cd0 | 0x54d30 | 0x20c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportDoubleFree` | 0x555e4 | 0x55644 | 0x290 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportGenericError` | 0x57150 | 0x571b0 | 0x8bc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInited` | 0x58198 | 0x581f8 | 0x18 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load1` | 0x581b0 | 0x58210 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load1` | 0x58200 | 0x58260 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load2` | 0x58250 | 0x582b0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load2` | 0x582a0 | 0x58300 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load4` | 0x582f0 | 0x58350 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load4` | 0x58340 | 0x583a0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load8` | 0x58390 | 0x583f0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load8` | 0x583e0 | 0x58440 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load16` | 0x58430 | 0x58490 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load16` | 0x58480 | 0x584e0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store1` | 0x584d0 | 0x58530 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store1` | 0x58520 | 0x58580 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store2` | 0x58570 | 0x585d0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store2` | 0x585c0 | 0x58620 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store4` | 0x58610 | 0x58670 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store4` | 0x58660 | 0x586c0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store8` | 0x586b0 | 0x58710 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store8` | 0x58700 | 0x58760 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store16` | 0x58750 | 0x587b0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store16` | 0x587a0 | 0x58800 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_load_n` | 0x587f0 | 0x58850 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_load_n` | 0x58840 | 0x588a0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_store_n` | 0x58890 | 0x588f0 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_report_exp_store_n` | 0x588e0 | 0x58940 | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializeHighMemEnd` | 0x58930 | 0x58990 | 0x80 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PrintAddressSpaceLayout` | 0x589b0 | 0x58a10 | 0x3b4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInitInternal` | 0x58df4 | 0x58e54 | 0x2b4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanInitFromRtl_ENSURE_ASAN_INITED` | 0x590a8 | 0x59108 | 0xa0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_set_death_callback` | 0x59310 | 0x59370 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `asan_init` | 0x59314 | 0x59374 | 0x94 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_version_mismatch_check_v8` | 0x593a8 | 0x59408 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SealedTopOfMemory_check` | 0x593ac | 0x5940c | 0x64 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_handle_no_return_tiny_rtl_stub_2_insns` | 0x59584 | 0x595e4 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `force_interface_symbols_dead_volatile_switch` | 0x59610 | 0x59670 | 0x328 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `ReserveShadowMemoryRanges_sealed_early_shadow_re` | 0x59938 | 0x59998 | 0x1e0 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `InitializeShadowMemory` | 0x59b18 | 0x59b78 | 0x308 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | NOT CERTIFIED: REAL 0 |
| `SetMallocContextSize` | 0x59e20 | 0x59e80 | 0x10 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetMallocContextSize` | 0x59e30 | 0x59e90 | 0x10 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `BufferedStackTrace_UnwindImpl_asan` | 0x59e40 | 0x59ea0 | 0x150 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanStats_Clear_ctor` | 0x5a370 | 0x5a3d0 | 0x2a0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `GetCurrentThreadStats` | 0x5aa74 | 0x5aad4 | 0x38 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_suppression_kinds_getter_3_insns` | 0x5ad54 | 0x5adb4 | 0xc | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_InitializeSuppressions` | 0x5ad60 | 0x5adc0 | 0x8c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsInterceptorSuppressed` | 0x5adec | 0x5ae4c | 0x68 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `HaveStackTraceBasedSuppressions` | 0x5ae54 | 0x5aeb4 | 0x78 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsODRViolationSuppressed` | 0x5aecc | 0x5af2c | 0x68 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsAddrSuppressed` | 0x5af34 | 0x5af94 | 0x14c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_thread_tiny_getter_3_insns` | 0x5b30c | 0x5b36c | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_Create` | 0x5b498 | 0x5b4f8 | 0x19c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_Destroy_TSDDtor` | 0x5b690 | 0x5b6f0 | 0x218 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetCurrentThread` | 0x5b8a8 | 0x5b908 | 0x20 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_SetThreadStackAndTls` | 0x5b8c8 | 0x5b928 | 0x1a4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_stack_top` | 0x5ba6c | 0x5bacc | 0x58 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_stack_bottom` | 0x5bac4 | 0x5bb24 | 0x58 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `AsanThread_AsyncSignalSafeLazyInitFakeStack` | 0x5bb1c | 0x5bb7c | 0x230 | SHAPE | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_Init` | 0x5bd4c | 0x5bdac | 0x3f4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AsanThread_ClearShadowForThreadStackAndTLS` | 0x5c140 | 0x5c1a0 | 0x10c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CreateMainThread` | 0x5c280 | 0x5c2e0 | 0x110 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCurrentThread` | 0x5c390 | 0x5c3f0 | 0xe0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MemToShadow_checked_instance_3` | 0x5c674 | 0x5c6d4 | 0x13c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ThreadContextBase_OnStarted` | 0x5d484 | 0x5d4e4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetAsanThreadContext` | 0x5d490 | 0x5d4f0 | 0x240 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `internal_allocator` | 0x5d924 | 0x5d984 | 0x158 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 7 | same (lui certified) |
| `internal_allocator_getter` | 0x5dc68 | 0x5dcc8 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `LowLevelAllocator_InternalAlloc_bump_allocator` | 0x5dc74 | 0x5dcd4 | 0x14c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetLowLevelAllocateMinAlignment` | 0x5ddc0 | 0x5de20 | 0x4c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetLowLevelAllocateCallback` | 0x5de0c | 0x5de6c | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetAllocatorMayReturnNull` | 0x5de48 | 0x5dea8 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `PrintHintAllocatorCannotReturnNull` | 0x5de54 | 0x5deb4 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsRssLimitExceeded` | 0x5de60 | 0x5dec0 | 0x10 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalAllocator_CombinedAllocator_Allocate_int` | 0x5de7c | 0x5dedc | 0x2cc | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `InternalAllocator_LargeMmapAllocator_Allocate` | 0x5e148 | 0x5e1a8 | 0x3c0 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `SetSealedStartFrame_sealed_patch` | 0x5f464 | 0x5f4c4 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportMmapFailureAndDie` | 0x5f470 | 0x5f4d0 | 0xd8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportMunmapFailureAndDie` | 0x5f548 | 0x5f5a8 | 0x9c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check` | 0x5fb08 | 0x5fb68 | 0x44 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `DecreaseTotalMmap` | 0x5fb4c | 0x5fbac | 0x24 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadBinaryNameCached_CacheBinaryName_body` | 0x5fdc4 | 0x5fe24 | 0x114 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `RunMallocHooks` | 0x6007c | 0x600dc | 0xb8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_malloc_hook_weak_default_ret` | 0x60134 | 0x60194 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `RunFreeHooks` | 0x60138 | 0x60198 | 0xac | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_free_hook_weak_default` | 0x601e4 | 0x60244 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sanitizer_ignore_free_hook_weak_default_ret_0` | 0x601ec | 0x6024c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SleepForSeconds_WaitForDebugger` | 0x60218 | 0x60278 | 0x4c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReportFile_SetReportPath_body_stderr_stdout_keyw` | 0x60528 | 0x60588 | 0x240 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_set_report_path` | 0x60d64 | 0x60dc4 | 0x18 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CommonFlags_SetDefaults` | 0x60d7c | 0x60ddc | 0x144 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `OverrideCommonFlags_no_op_flag_hook_2_insns` | 0x60ec0 | 0x60f20 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `FlagParser_ParseString_parse_flags` | 0x61210 | 0x61270 | 0x12a4 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `InitializeCommonFlags` | 0x624b4 | 0x62514 | 0x24 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_parse_flag_ParseString_core` | 0x6298c | 0x629ec | 0x310 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_ParseStringFromEnv` | 0x62c9c | 0x62cfc | 0x144 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_ParseString` | 0x62de0 | 0x62e40 | 0xf4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `RegisterFlag_T_FlagParser_RegisterHandler` | 0x63068 | 0x630c8 | 0x60 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FlagParser_alloc_helper_LowLevelAlloc` | 0x630c8 | 0x63128 | 0x40 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_atoll` | 0x63108 | 0x63168 | 0xec | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_simple_strtoll` | 0x631f4 | 0x63254 | 0x15c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_memchr` | 0x63350 | 0x633b0 | 0x20 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memcmp` | 0x63370 | 0x633d0 | 0x38 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memcpy` | 0x633a8 | 0x63408 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memmove` | 0x633cc | 0x6342c | 0x58 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_memset` | 0x63424 | 0x63484 | 0x60 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strcspn` | 0x63484 | 0x634e4 | 0x54 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strcmp` | 0x634d8 | 0x63538 | 0x34 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strdup` | 0x6350c | 0x6356c | 0x6c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strlen` | 0x63578 | 0x635d8 | 0x1c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strncmp` | 0x63594 | 0x635f4 | 0x44 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strchr` | 0x635d8 | 0x63638 | 0x4c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strchrnul` | 0x63624 | 0x63684 | 0x48 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strrchr` | 0x6366c | 0x636cc | 0x40 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strnlen` | 0x637dc | 0x6383c | 0x30 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strncpy` | 0x63850 | 0x638b0 | 0x70 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_strstr` | 0x638c0 | 0x63920 | 0x94 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `mem_is_zero` | 0x63954 | 0x639b4 | 0xb4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_sigprocmask_raw_rt_sigprocmask` | 0x63a08 | 0x63a68 | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `BlockSignals_ScopedBlockSignals_ctor_CHECK_inter` | 0x63a18 | 0x63a78 | 0x1e0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_iserror` | 0x63c04 | 0x63c64 | 0x20 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_mmap` | 0x63c24 | 0x63c84 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_munmap` | 0x63c30 | 0x63c90 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_mprotect` | 0x63c3c | 0x63c9c | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_madvise` | 0x63c4c | 0x63cac | 0x2c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `internal_close` | 0x63c78 | 0x63cd8 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_open_openat_AT_FDCWD` | 0x63c84 | 0x63ce4 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_read` | 0x63ca8 | 0x63d08 | 0x38 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_write` | 0x63ce0 | 0x63d40 | 0x38 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_ftruncate` | 0x63d18 | 0x63d78 | 0x38 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_dup` | 0x63d50 | 0x63db0 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_dup2_dup3` | 0x63d5c | 0x63dbc | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_unlink_unlinkat` | 0x63d6c | 0x63dcc | 0x18 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sched_yield` | 0x63d84 | 0x63de4 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_usleep_internal_sleep_nanosleep` | 0x63d90 | 0x63df0 | 0x4c | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `internal_execve` | 0x63ddc | 0x63e3c | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_exit_exit_group` | 0x63de8 | 0x63e48 | 0x14 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `FileExists_newfstatat` | 0x63dfc | 0x63e5c | 0x80 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `DirExists_newfstatat` | 0x63e7c | 0x63edc | 0x64 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetTid_gettid` | 0x63ee0 | 0x63f40 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetEnv` | 0x63eec | 0x63f4c | 0x130 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `FutexWait` | 0x64120 | 0x64180 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `FutexWake` | 0x64144 | 0x641a4 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_ptrace` | 0x64168 | 0x641c8 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_waitpid_wait4` | 0x64174 | 0x641d4 | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_getpid` | 0x64184 | 0x641e4 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_getppid` | 0x64190 | 0x641f0 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_prctl` | 0x6419c | 0x641fc | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sigaltstack` | 0x641a8 | 0x64208 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_fork_clone` | 0x641b4 | 0x64214 | 0x18 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `internal_sigaction_norestorer_rt_sigaction` | 0x641cc | 0x6422c | 0x12c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ThreadLister_ListThreads` | 0x644d0 | 0x64530 | 0x3fc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetMaxUserVirtualAddress_sealed_from_the_start_f` | 0x64a38 | 0x64a98 | 0x118 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetPageSize` | 0x64b50 | 0x64bb0 | 0x8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadBinaryName_readlinkat_proc_self_exe` | 0x64b58 | 0x64bb8 | 0xac | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReadLongProcessName_proc_self_cmdline` | 0x64c04 | 0x64c64 | 0x120 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `internal_clone_CHECK_child_stack_16` | 0x64dec | 0x64e4c | 0x80 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetHandleSignalMode` | 0x64e6c | 0x64ecc | 0x5c | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `internal_start_thread_BlockSignals_variant_rt_si` | 0x64ec8 | 0x64f28 | 0xcc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializePlatformEarly` | 0x65090 | 0x650f0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `CheckASLR` | 0x65094 | 0x650f4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetMmapGranularity_thunk` | 0x652e4 | 0x65344 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `ErrorIsOOM` | 0x652e8 | 0x65348 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `MmapOrDie` | 0x652f4 | 0x65354 | 0x10c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNamed_internal_mmap_name_helper` | 0x65400 | 0x65460 | 0x74 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `UnmapOrDie` | 0x65474 | 0x654d4 | 0x7c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `MmapOrDieOnFatalError` | 0x654f0 | 0x65550 | 0x110 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNoReserveOrDie` | 0x6582c | 0x6588c | 0x104 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedOrDie` | 0x65930 | 0x65990 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `MmapFixed_named_may_die_core_MmapNamed_IncreaseT` | 0x6593c | 0x6599c | 0x178 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co` | 0x65ab4 | 0x65b14 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `CloseFile` | 0x65cac | 0x65d0c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetNamedMappingFd_MmapNamed` | 0x65fd0 | 0x66030 | 0x20c | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `SetPrintfAndReportCallback` | 0x66794 | 0x667f4 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Printf` | 0x667a4 | 0x66804 | 0x4c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SharedPrintfCode` | 0x667f0 | 0x66850 | 0x5c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `Report` | 0x6684c | 0x668ac | 0x4c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SuppressionContext_ctor` | 0x68390 | 0x683f0 | 0x5c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SuppressionContext_ParseFromFile` | 0x683ec | 0x6844c | 0x23c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SuppressionContext_Parse` | 0x68628 | 0x68688 | 0x324 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob` | 0x68eec | 0x68f4c | 0xd0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a` | 0x68fbc | 0x6901c | 0x350 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `DTLS_Destroy_ForEachDVT_no_op_4_insns` | 0x6930c | 0x6936c | 0x10 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ThreadContextBase_ctor` | 0x69558 | 0x695b8 | 0x44 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ThreadContextBase_ctor_ThreadRegistry_init_helpe` | 0x6959c | 0x695fc | 0x60 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `ThreadRegistry_CreateThread` | 0x695fc | 0x6965c | 0x478 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `ThreadRegistry_StartThread` | 0x6a334 | 0x6a394 | 0x324 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `ThreadRegistry_ThreadArgRetval_vector_growth` | 0x6a660 | 0x6a6c0 | 0x104 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AddDieCallback` | 0x6af14 | 0x6af74 | 0x88 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Die` | 0x6b060 | 0x6b0c0 | 0xc0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetCheckUnwindCallback` | 0x6b120 | 0x6b180 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `CheckFailed` | 0x6b12c | 0x6b18c | 0xb8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReservedAddressRange_InitAligned` | 0x6b83c | 0x6b89c | 0xf8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ReserveShadowMemoryRange` | 0x6b934 | 0x6b994 | 0x12c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_common_libcdep_static_ctor_background` | 0x6bc88 | 0x6bce8 | 0x7c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetThreadStackTopAndBottom` | 0x6bd38 | 0x6bd98 | 0x2e8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitTlsSize` | 0x6c020 | 0x6c080 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `GetTls` | 0x6c024 | 0x6c084 | 0x3f0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetThreadStackAndTls` | 0x6c414 | 0x6c474 | 0xd0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `AndroidLogInit` | 0x6c8c8 | 0x6c928 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `MonotonicNanoTime_NanoTime` | 0x6c8fc | 0x6c95c | 0x48 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MapDynamicShadow_MmapAlignedOrDieOnFatalError` | 0x6c944 | 0x6c9a4 | 0x24c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InitializePlatformCommonFlags` | 0x6cb90 | 0x6cbf0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `CollectStaticTlsBlocks` | 0x6cb94 | 0x6cbf4 | 0x10c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InternalMmapVector_Realloc_2` | 0x6cca0 | 0x6cd00 | 0x104 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `GetThreadSelf` | 0x6d020 | 0x6d080 | 0x4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetShadowRegionHugePageMode_DontDumpShadow_madvi` | 0x6d0c8 | 0x6d128 | 0x20 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `DisableCoreDumperIfNecessary` | 0x6d0e8 | 0x6d148 | 0xa0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Atexit` | 0x6d1d4 | 0x6d234 | 0x4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `SetAlternateSignalStack` | 0x6d214 | 0x6d274 | 0xc4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `UnsetAlternateSignalStack` | 0x6d2d8 | 0x6d338 | 0x88 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `InstallDeadlySignalHandlers` | 0x6d360 | 0x6d3c0 | 0x78 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MaybeInstallSigaction` | 0x6d3d8 | 0x6d438 | 0xe4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `IsAccessibleMemoryRange` | 0x6d578 | 0x6d5d8 | 0x134 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve` | 0x6d8e4 | 0x6d944 | 0x130 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapFixedSuperNoReserve` | 0x6da14 | 0x6da74 | 0x60 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNoAccess_ReservedAddressRange_Init` | 0x6da74 | 0x6dad4 | 0xcc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `MmapNoAccess` | 0x6db54 | 0x6dbb4 | 0x20 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `ReservedAddressRange_Map` | 0x6db74 | 0x6dbd4 | 0x74 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SealedRepairReservation` | 0x6dbe8 | 0x6dc48 | 0xd8 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `ReservedAddressRange_MapOrDie` | 0x6dcc0 | 0x6dd20 | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `InitializeCoverage` | 0x6f4c8 | 0x6f528 | 0x44 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sanitizer_cov_dump` | 0x6f50c | 0x6f56c | 0x30 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackStore_Store_BlockInfo_helper` | 0x6f970 | 0x6f9d0 | 0x124 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `StackStore_Alloc` | 0x6fa94 | 0x6faf4 | 0x134 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `StackStore_BlockInfo_Create_Map` | 0x7047c | 0x704dc | 0xb4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotNode_store_hash_helper` | 0x71c84 | 0x71ce4 | 0x5c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotPut` | 0x71f6c | 0x71fcc | 0x20 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackDepotBase_Put` | 0x71f8c | 0x71fec | 0x284 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 3 | same (lui certified) |
| `StackDepotGet` | 0x72210 | 0x72270 | 0x110 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 2 | same (lui certified) |
| `StackDepotBase_find_bucket_chain_walk` | 0x72700 | 0x72760 | 0x90 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `TwoLevelMap_StackDepotNode_Create` | 0x72790 | 0x727f0 | 0x100 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `StackTrace_GetCurrentPc` | 0x728f0 | 0x72950 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `BufferedStackTrace_Init_UnwindFast_frame_pointer` | 0x728f8 | 0x72958 | 0x160 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `StackTrace_PopStackFrames` | 0x72a58 | 0x72ab8 | 0x74 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `BufferedStackTrace_Unwind_FAST_frame_pointer_wal` | 0x72f54 | 0x72fb4 | 0x118 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `SymbolizerProcess_GetEnvP` | 0x760b8 | 0x76118 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `InternalSymbolizer_Flush` | 0x77890 | 0x778f0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `BufferedStackTrace_UnwindSlow` | 0x792bc | 0x7931c | 0xbc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Unwind_Trace_callback` | 0x79378 | 0x793d8 | 0xd8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Unwind_GetIP_slow_unwind_helper` | 0x79450 | 0x794b0 | 0x274 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lsan_flags_init_helper` | 0x799f0 | 0x79a50 | 0x44 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re` | 0x79a34 | 0x79a94 | 0x3d0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lsan_InitCommonLsan` | 0x7a0d4 | 0x7a134 | 0xb8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `DoRecoverableLeakCheckVoid` | 0x7b4e4 | 0x7b544 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `lsan_register_root_region` | 0x7c0f0 | 0x7c150 | 0x330 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `lsan_unregister_root_region` | 0x7c420 | 0x7c480 | 0x488 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `lsan_ubsan_default_options_weak_stub` | 0x7c8a8 | 0x7c908 | 0xc | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `DisabledInThisThread` | 0x7f46c | 0x7f4cc | 0x18 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_InitializeSuppressions` | 0x7f808 | 0x7f868 | 0x7c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_InitAsPlugin` | 0x7f884 | 0x7f8e4 | 0xb0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_MaybeCallUbsanDefaultOptions` | 0x7f934 | 0x7f994 | 0x18 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `ubsan_RegisterUbsanFlags_InitializeFlags_part` | 0x7f94c | 0x7f9ac | 0x148 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ubsan_default_options_weak_returns` | 0x7fa94 | 0x7faf4 | 0xc | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_default_options_cli_c` | 0x7faa0 | 0x7fb00 | 0xc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `main` | 0x7faac | 0x7fb0c | 0x2c4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `target_alloc_init` | 0x7fd70 | 0x7fdd0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `target_alloc_count` | 0x7fd74 | 0x7fdd4 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `target_run` | 0x7fd7c | 0x7fddc | 0x158 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `oft_exit_guard` | 0x7fed4 | 0x7ff34 | 0x30 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `emit_printf` | 0x7ff04 | 0x7ff64 | 0x48 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `asan_module_ctor` | 0x815b4 | 0x8182c | 0x38 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `asan_module_dtor` | 0x815ec | 0x81864 | 0x30 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `extenddftf2` | 0x81f44 | 0x82368 | 0x190 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sysconf` | 0x87d24 | 0x88148 | 0x228 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 3 | same (settled; lui certified) |
| `init` | 0x87f4c | 0x88370 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `init_libc` | 0x87f50 | 0x88374 | 0x22c | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `libc_start_init` | 0x8817c | 0x885a0 | 0x4c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_start_main` | 0x881c8 | 0x885ec | 0x60 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `libc_start_main_stage2` | 0x88228 | 0x8864c | 0x48 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `init_tls` | 0x88348 | 0x8876c | 0x2b0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `init_ssp` | 0x885f8 | 0x88a1c | 0x60 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stack_chk_fail` | 0x88658 | 0x88a7c | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_sigaction_abort_area_fn_rt_sigaction_tkill` | 0x886a8 | 0x88acc | 0x94 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `Exit` | 0x8873c | 0x88b60 | 0x1c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `funcs_on_exit` | 0x88788 | 0x88bac | 0xc8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `cxa_finalize` | 0x88850 | 0x88c74 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `cxa_atexit_atexit` | 0x88854 | 0x88c78 | 0xc4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `call` | 0x88918 | 0x88d3c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fini` | 0x8891c | 0x88d40 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `libc_exit_fini` | 0x88920 | 0x88d44 | 0x4c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `exit` | 0x8896c | 0x88d90 | 0x74 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `open` | 0x88be0 | 0x89004 | 0xe4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `syscall_ret` | 0x88cc4 | 0x890e8 | 0x38 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_dl_iterate_phdr_static` | 0x88cfc | 0x89120 | 0x1a8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `calloc` | 0x89468 | 0x8988c | 0x138 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_malloc_j_libc_malloc_impl` | 0x895a0 | 0x899c4 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `libc_free` | 0x895a4 | 0x899c8 | 0x1cc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `get_meta` | 0x89770 | 0x89b94 | 0x110 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `alloc_meta` | 0x89c58 | 0x8a07c | 0x2d8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `libc_malloc_impl` | 0x89f30 | 0x8a354 | 0x370 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `alloc_slot` | 0x8a2a0 | 0x8a6c4 | 0x8a4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `enframe` | 0x8ab44 | 0x8af68 | 0x150 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `malloc_allzerop` | 0x8ac94 | 0x8b0b8 | 0x178 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `getrlimit` | 0x8cabc | 0x8cee0 | 0xf8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `getrusage` | 0x8cbb4 | 0x8cfd8 | 0x28 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `setrlimit` | 0x8cbdc | 0x8d000 | 0xc8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `mmap` | 0x8d0cc | 0x8d4f0 | 0xec | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `mprotect` | 0x8d1b8 | 0x8d5dc | 0x48 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `munmap` | 0x8d2d4 | 0x8d6f8 | 0x48 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `sched_yield` | 0x8d5e0 | 0x8da04 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `raise_tkill_path` | 0x8d660 | 0x8da84 | 0x78 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `sigaction_libc_sigaction` | 0x8d6d8 | 0x8dafc | 0x1d4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_sigaltstack` | 0x8d9a4 | 0x8ddc8 | 0x8c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `dprintf` | 0x8e00c | 0x8e430 | 0x64 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lockfile` | 0x8e070 | 0x8e494 | 0xfc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `unlockfile` | 0x8e16c | 0x8e590 | 0x60 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_read` | 0x8dd5c | 0x8e180 | 0x118 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stdio_write` | 0x8de7c | 0x8e2a0 | 0x190 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `aio_close_stub_j_ret_used_by_close_stdio_close` | 0x8dd2c | 0x8e150 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_close` | 0x8dd30 | 0x8e154 | 0x2c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fwritex` | 0x8e600 | 0x8ea24 | 0x138 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_fwrite` | 0x8e738 | 0x8eb5c | 0xb8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `towrite` | 0x8e7f0 | 0x8ec14 | 0x54 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `stdio_exit` | 0x8e45c | 0x8e880 | 0x1a4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `ofl_lock` | 0x8e844 | 0x8ec68 | 0x30 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_vfprintf` | 0x8e9c0 | 0x8ede4 | 0x1b0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `printf_core` | 0x8eb70 | 0x8ef94 | 0xe30 | IMM | EQUAL-mod-pcrel | 3 | DIFFERENT-target | 3 | same (settled; lui certified) |
| `pop_arg` | 0x8f9a0 | 0x8fdc4 | 0x134 | IMM | EQUAL-mod-pcrel | 1 | DIFFERENT-target | 1 | same (settled) |
| `pad` | 0x8fad4 | 0x8fef8 | 0xd4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same (lui certified) |
| `fmt_fp` | 0x8fba8 | 0x8ffcc | 0x16c8 | IMM | EQUAL-mod-pcrel | 0 | DIFFERENT-target | 1 | same (lui certified) |
| `lctrans` | 0x890bc | 0x894e0 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_wctomb` | 0x8d448 | 0x8d86c | 0x24 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_wcrtomb` | 0x8d31c | 0x8d740 | 0x12c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fpclassifyl` | 0x8b6ac | 0x8bad0 | 0x44 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `letf2` | 0x8aee4 | 0x8b308 | 0xc8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `multf3` | 0x8afac | 0x8b3d0 | 0x700 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `floatsitf` | 0x8bf08 | 0x8c32c | 0x108 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `scalbn` | 0x8c914 | 0x8cd38 | 0x98 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `subtf3` | 0x8bef8 | 0x8c31c | 0x10 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `addtf3` | 0x8b6f0 | 0x8bb14 | 0x7cc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fe_getround` | 0x8bebc | 0x8c2e0 | 0x30 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `fixunstfsi` | 0x91278 | 0x9169c | 0x94 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `floatunsitf` | 0x9130c | 0x91730 | 0xec | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `fixtfsi` | 0x8c9ac | 0x8cdd0 | 0xa8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `divtf3` | 0x8c010 | 0x8c434 | 0x904 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_vprintf` | 0x91ad0 | 0x91ef4 | 0x1c | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `stdout_write` | 0x8e880 | 0x8eca4 | 0xa0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `bcmp` | 0x92084 | 0x924a8 | 0x4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_memcmp` | 0x92154 | 0x92578 | 0x30 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_memcpy` | 0x92184 | 0x925a8 | 0x404 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_memset` | 0x92588 | 0x929ac | 0xf8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_strchr` | 0x92680 | 0x92aa4 | 0x3c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `strchrnul` | 0x926bc | 0x92ae0 | 0xe0 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_strlen` | 0x927d4 | 0x92bf8 | 0x90 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_strnlen` | 0x92a70 | 0x92e94 | 0x44 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `musl_memchr` | 0x92088 | 0x924ac | 0xcc | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lock` | 0x92ab4 | 0x92ed8 | 0x288 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `unlock` | 0x92d3c | 0x93160 | 0x74 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `syscall_cp_c` | 0x92db0 | 0x931d4 | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `syscall_cp_sccp` | 0x92dd4 | 0x931f8 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `tls_get_addr` | 0x92dd8 | 0x931fc | 0x24 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_atfork` | 0x92e14 | 0x93238 | 0xa4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `mremap` | 0x8d200 | 0x8d624 | 0xd4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `pthread_getspecific_tss_get` | 0x93e8c | 0x942b0 | 0x1c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_key_create` | 0x94234 | 0x94658 | 0xd4 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `lock_unlock_pair_user_futex` | 0x945ac | 0x949d0 | 0xa4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_rwlock_wrlock` | 0x94650 | 0x94a74 | 0x8 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_rwlock_timedwrlock` | 0x94658 | 0x94a7c | 0x114 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_key_atfork_tsd_table_init_11_insns` | 0x9476c | 0x94b90 | 0x2c | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_setspecific` | 0x947d0 | 0x94bf4 | 0x34 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `set_thread_area` | 0x9480c | 0x94c30 | 0xc | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `pthread_testcancel` | 0x94804 | 0x94c28 | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `testcancel` | 0x94808 | 0x94c2c | 0x4 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `clock_gettime_113_vdso_fallback_169_gettimeofday` | 0x95138 | 0x9555c | 0xb8 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
| `close` | 0x97808 | 0x97c2c | 0x54 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `musl_read` | 0x978e8 | 0x97d0c | 0x34 | SAME | EQUAL | 0 | EQUAL | 0 | same |
| `vm_wait` | 0x94e48 | 0x9526c | 0x50 | IMM | EQUAL-mod-pcrel | 0 | EQUAL-mod-pcrel | 0 | same |
