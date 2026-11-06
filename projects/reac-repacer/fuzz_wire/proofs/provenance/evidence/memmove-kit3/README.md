# fuzz_wire __asan_memmove: the donor comparison on cmpkit 4bbd3a74be89 (kit3 = the third donor comparison of this record, on comparison kit version 4bbd3a74be89, tool registry cmpkit/4bbd3a74be89/)

This record replaces, as the comparison of record, the donor comparisons that memmove-A/ (GATES.md section 0),
memmove-B/ (GATES.md section 0) and memmove-kit2/ cite. Those were made with comparison tools that are now known to
call some differently named or unnamed targets equal (repin_check 9cbc3553c09e / e5487165abb8, jtcheck 2e2f9c2126b2,
paircl 16e1466be22d / a88c2822a0f2). The old records stay as they were. This is the same comparison on the comparison
kit of record, cmpkit 4bbd3a74be89 (the seven files of records/cmpkit-SHA256SUMS). Every target that the kit does not
settle is given a separate measurement, taken from the kit's FULL target list.

Images (sha256 prefixes): fuzz_wire.asan 2f8f8697cd4f (unstripped twin d2f662a22962), fuzz_wire.asan-ubsan
af4534831a45 (twin 51eb4bef2425); the donor libreac/fuzz_pcap's released pins fuzz_pcap.asan b7a91d9b1fb0 (twin
36da3052c383) and fuzz_pcap.asan-ubsan 9e66f771f22a (twin c969d83cdd59). `drvcmp.py twins`: each pcap pin and its twin
have the same PT_LOAD layout and differ only in the ELF header and .note.gnu.build-id (records/twins-pcap-*.txt).

## Result

The verdict is UNCHANGED, but it is not 'closure 785 EQUAL' as the old GATES records state: the kit certifies part of
the closure, and the rest is settled by named measurements, with 0 REAL:

- **closure (785 functions per image):** 734 kit-certified. Of these, `closure_strict2` certifies 723 as EQUAL /
  EQUAL-mod-pcrel (A 173 + 550, B 171 + 552). The kit's own jtcheck 824905e26211 settles 11 more in full (target differs
  0, unmeasured 0, unpaired 0; records/jtcheck-open-*), and the reviewer measured each of their tables. The other 51 are
  settled by the named measurements below. The per-function list is records/closure-settlement-*.txt: KIT-JTCHECK 11
  and MEASURED 51, each MEASURED function with its count per class.
  The central re-run of the comparison-kit records (commit bdc037d1af2a, its row M2 for this record) counts
  736 / 49: its jtcheck also accepts Symbolizer::PlatformInit and LoadedModule::addAddressRange. Both differ from this
  count at one target, the empty string X 0x13e67 / Y 0x13e7d (PlatformInit +0x18c; addAddressRange +0x70, A 0x5f8f4, B
  0x5f694). The reviewer found that jtcheck's acceptance of each is a misreading by its heuristics (AUDIT.md, 'Re-check
  of v2', G2). It took a verbosity test (`addi a1,zero,2; bgeu`) for a 2-entry table bound, and `internal_strncpy(dst,
  "", 16)` for a 16-byte initializer, where strncpy reads only up to the NUL. The bytes it compared include the NUL and
  are equal, so no difference is hidden. The correct reading of both is the CSTR row, so this record counts both as
  measured.
- **paircl (944 pairs per image):** 877 kit-certified (A 214 + 663, B 212 + 665), 0 pairing conflicts. The other 67,
  which include the 62 closure rows, are settled by the same measurements.
- **0 REAL:** no differing instruction word, no differing named target, and no table entry with a different
  symbol + offset.

On both images, wire's __asan_memmove and every function it can reach are pcap's code up to pc-relative fields, and
every pc-relative target names the same thing on both sides. Every target the kit leaves unsettled is one of two
things: a read-only DATA target that the kit compares over its whole region to the next symbol, or an `unmeasured`
integer word. The kit README describes both as fail-closed classes. Each one is settled below.

| image | closure_strict2 (against the twin) | paircl (against the stripped pin) |
|---|---|---|
| A | 785 functions: EQUAL 173, EQUAL-mod-pcrel 550, other 62 | 944 paired: EQUAL 214, EQUAL-mod-pcrel 663, other 67, 0 conflicts |
| B | 785 functions: EQUAL 171, EQUAL-mod-pcrel 552, other 62 | 944 paired: EQUAL 212, EQUAL-mod-pcrel 665, other 67, 0 conflicts |

Every 'other' row is `EQUAL-mod-pcrel target-differ`: the code is equal, and some targets are not settled by the kit.
The kit PRINTS only the first two differing targets of a function (closure_strict2.py:88, paircl.py:67). So
tools/settle2.py runs the kit's own compare, strictcmp2.tcmp, again on each of the 67 function pairs (the 62 closure
rows are a subset of the 67 paircl rows) and settles every target in its full list (records/settle2-*):

| class (settle2) | targets per image (A = B) | measurement |
|---|---|---|
| TABLE | 7 | the target register is added to an index register and a load of the sum reads it; the index is bounded (srli 58: 64 entries; `addi a1,zero,2; bltu a1,s1`: 3 entries); the k*w bytes are equal: the 64-entry De Bruijn ctz tables of Allocator::Allocate +0xdc, Deallocate +0x20c, RZSize2Log +0x44 and three SizeClassAllocator64 functions, and OpenFile +0x60's three int32 `open` flag words `0, 0x241, 0x42` |
| CSTR | 152 | no such index, and the bytes up to the first NUL are equal on both sides, NUL included: the merged empty string at X 0x13e67 / Y 0x13e7d and the ANSI colour strings (`\x1b[1m\x1b[3Nm`, `\x1b[1m\x1b[0m`) of the report printers, flag defaults and the libc string paths |
| WORD-EQUAL | 3 | paircl's `unmeasured` words (an I/S-type word on an auipc register): CheckForLeaksCallback +0x484 `addi a1,a3,1`, +0x48c `slli a3,a3,3` and __sanitizer_dump_coverage +0x118 `addi a0,a0,-1`. Each word is equal in X and Y, and each is an integer operation that only a branch reaches (a `j` sits just before each), not a pc-relative use |
| OPEN | 16 | jump / pointer / string tables, settled below |

The 16 OPEN targets are in 15 functions (records/jtcheck-open-*, records/byhand-*):
- **jtcheck 824905e26211 SETTLES these 11 functions** (target differs 0, unmeasured 0, unpaired 0), covering 12 targets:
  GetHandleSignalMode, VSNPrintf, ErrorGeneric's constructor, ErrorDescription::Print, force_interface_symbols,
  CFI_Parser::parseFDEInstructions, EHHeaderParser::getTableEntrySize, LocalAddressSpace::getEncodedP (2 targets),
  AddressDescription::Print, __synccall, sysconf.
- **Decorator::ShadowByte +0x14 and __strftime_fmt_1 +0x44**: jtcheck gives `target differs 0`. The jump table each
  dispatches on is settled. Its `unmeasured` items are string targets (ShadowByte's six colour strings, strftime's two
  empty strings), and each of those is a CSTR row above.
- **CFI_Parser::parseCIE +0x23c** (jtcheck `target differs 1`): a relative 32-bit jump table (the switch on the CIE
  augmentation character). Its 47 entries give the same function offset on both sides, and the consumer's bound
  constant 46 gives exactly 47 entries. Entry 47 lies outside the function on both sides (records/byhand-*, JT32-rel).
- **SignalContext::Describe +0x1c** (jtcheck unmeasured 1): a table of 8 relative 32-bit entries (bound constant 7)
  pointing to signal names. All 8 strings are equal on both sides, NUL included: ILL, TRAP, ABRT, BUS, FPE, UNKNOWN
  SIGNAL, UNKNOWN SIGNAL, SEGV (records/byhand-*, STRTAB32-rel).

So every target of every reported function is settled, on both runs and both images, and none is a difference. The
acceptances are the kit README's 'listed by-hand acceptances with a separate measurement, never a kit EQUAL'.

## Audit

A fresh read-only reviewer audited the first version of this record (AUDIT.md). Its findings and their fixes:
- **F1:** the first version settled only the printed (first two) targets per function. Fixed: settle2.py works on the
  full tcmp list (178 targets per image). The reviewer had measured all 78 extra targets per image: each is an equal
  colour string or `""`, used as a C string. settle2.py reproduces that.
- **F2:** the 3 unmeasured words were not settled. Fixed: the WORD-EQUAL class.
- **F3:** three rows were classed as tables from an unrelated `srli` / `andi`. They are C strings. Fixed: a table now
  needs the index-to-load dataflow.
- **F4, F6:** wrong descriptions of the ShadowByte evidence and of the strings. Fixed in this text. The colour strings
  are returned to PrintMemoryByte, which prints them with `%s`.
- **F5:** the Describe claim had no measurement in the records. Fixed: byhand.py's STRTAB32-rel reading.

The reviewer read the consumer of every C-string target that the first version listed (71), and of the 78 targets
that version did not see. Each is used as a C string: a `%s` argument, `Append`, a `const char*` flag field, a
`strncpy` / `strcmp` / `fstatat` path, or a returned `char*`. No byte after the NUL is read. It also ran its use check
over the kit's own 3533 printable C-string acceptances per image, and read the 6 it flagged: each is used as a C string.

## Commands (in the kit directory, with tools/ beside it)

    python3 drvcmp.py twins <pcap pin> <pcap twin>
    python3 closure_strict2.py <wire twin> <pcap twin> __asan_memmove
    python3 paircl.py <wire twin> <pcap pin> __asan_memmove <pcap entry: 51bf0 A / 51c40 B> <pcap twin>
    python3 jtcheck.py <wire twin> <pcap twin> <the 15 functions above, comma-separated>
    python3 tools/settle2.py <kit> <wire twin> <pcap twin> <closure output> <paircl output>
    python3 tools/byhand.py <kit> <wire twin> <pcap twin> <FUNC+OFF ...>
